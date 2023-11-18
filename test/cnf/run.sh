#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/cnf/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/cnf/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/cnf ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "CNF testing in '$CADICALBUILD'" 
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

make -C $CADICALBUILD
res=$?
[ $res = 0 ] || exit $res

#--------------------------------------------------------------------------#

coresolver="$CADICALBUILD/cadical"
simpsolver="$CADICALBUILD/../scripts/run-simplifier-and-extend-solution.sh"
dratchecker=$CADICALBUILD/drat-trim
lratchecker=$CADICALBUILD/lrat-trim
solutionchecker=$CADICALBUILD/precochk
makefile=$CADICALBUILD/makefile

if [ ! -f $solutionchecker -o ! -f $dratchecker -o ! -f $lratchecker ]
then

  if [ ! -f $solutionchecker -o ../test/cnf/precochk.c -nt $solutionchecker ]
  then
    cmd="cc -O -o $solutionchecker ../test/cnf/precochk.c -lz"
    cecho "$cmd"
    if $cmd 2>/dev/null
    then
      msg "external solution checking with '$solutionchecker'"
    else
      msg "no external solution checking " \
          "(compiling '../test/cnf/preochk.c' failed)"
      solutionchecker=none
    fi
  fi

  if [ ! -f $dratchecker -o ../test/cnf/drat-trim.c -nt $dratchecker ]
  then
    cmd="cc -O -o $dratchecker ../test/cnf/drat-trim.c"
    if $cmd 2>/dev/null
    then
      msg "external proof checking with '$dratchecker'"
    else
      msg "no external proof checking " \
          "(compiling '../test/cnf/drat-trim.c' failed)"
      dratchecker=none
    fi
  fi

  if [ ! -f $lratchecker -o ../test/cnf/lrat-trim.c -nt $lratchecker ]
  then
    cmd="cc -O -o $lratchecker ../test/cnf/lrat-trim.c"
    if $cmd 2>/dev/null
    then
      msg "external proof checking with '$lratchecker'"
    else
      msg "no external proof checking " \
          "(compiling '../test/cnf/lrat-trim.c' failed)"
      lratchecker=none
    fi
  fi
else
  msg "external solution checking with '$solutionchecker'"
  msg "external DRAT checking with '$dratchecker'"
  msg "external LRAT checking with '$lratchecker'"
fi


#--------------------------------------------------------------------------#

ok=0
failed=0

core () {
  msg "running CNF test core ${HILITE}'$1'${NORMAL}"
  prefix=$CADICALBUILD/test-cnf-core
  cnf=../test/cnf/$1.cnf
  log=$prefix-$1.log
  err=$prefix-$1.err
  chk=$prefix-$1.chk
  prf=$prefix-$1.prf
  proofchecker=$3
  if [ -f cnf/$1.sol ]
  then
    solopts=" -r ../test/cnf/$1.sol"
  else
    solopts=""
  fi
  case $proofchecker in
    *drat*) proofopts=" $prf"; expectedcheckerstatus=0;;
    *lrat*) proofopts=" --lrat $prf"; expectedcheckerstatus=20;;
    *) proofopts="";;
  esac
  opts="$cnf --check$solopts$proofopts"
  cecho "$coresolver \\"
  cecho "$opts"
  cecho -n "# $2 ..."
  "$coresolver" $opts 1>$log 2>$err
  res=$?
  if [ ! $res = $2 ] 
  then
    cecho " ${BAD}FAILED${NORMAL} (actual exit code $res)"
    failed=`expr $failed + 1`
  elif [ $res = 10 ]
  then
    if [ "$solopts" = "" ]
    then
      cecho " ${GOOD}ok${NORMAL} (without solution file)"
    else
      cecho " ${GOOD}ok${NORMAL} (solution file checked after parsing)"
    fi
    if [ x"$solutionchecker" = xnone ]
    then
	ok=`expr $ok + 1`
    else
      cecho "$solutionchecker \\"
      cecho "$cnf $log"
      cecho -n "# 0 ..."
      if $solutionchecker $cnf $log 1>&2 >$chk
      then
        cecho " ${GOOD}ok${NORMAL} (solution checked externally too)"
	ok=`expr $ok + 1`
      else
	cecho " ${BAD}FAILED${NORMAL} (incorrect solution)"
	failed=`expr $failed + 1`
      fi
    fi
  elif [ $res = 20 ]
  then
    cecho " ${GOOD}ok${NORMAL} (exit code as expected)"
    if [ ! x"$proofchecker" = xnone ]
    then
      cecho "$proofchecker \\"
      cecho "$cnf $prf"
      cecho -n "# 0 ..."
      $proofchecker $cnf $prf 1>&2 >$chk
      status=$?
      if [ $status = $expectedcheckerstatus ]
      then
	cecho " ${GOOD}ok${NORMAL} (proof checked)"
	ok=`expr $ok + 1`
      else
	cecho " ${BAD}FAILED${NORMAL} (proof check '$proofchecker $cnf $prf' failed)"
	failed=`expr $failed + 1`
      fi
    fi
  else 
    cecho " ${BAD}FAILED${NORMAL} (unsupported exit code $res)"
    failed=`expr $failed + 1`
  fi
}

simp () {
  msg "running CNF test simp ${HILITE}'$1'${NORMAL}"
  prefix=$CADICALBUILD/test-cnf-simp
  cnf=../test/cnf/$1.cnf
  log=$prefix-$1.log
  err=$prefix-$1.err
  chk=$prefix-$1.chk
  opts="$cnf"
  cecho "$simpsolver \\"
  cecho "$opts"
  cecho -n "# $2 ..."
  "$simpsolver" $opts 1>$log 2>$err
  res=$?
  if [ ! $res = $2 ] 
  then
    cecho " ${BAD}FAILED${NORMAL} (actual exit code $res)"
    failed=`expr $failed + 1`
  elif [ $res = 10 ]
  then
    cecho " ${GOOD}ok${NORMAL}"
    if [ x"$solutionchecker" = xnone ]
    then
	ok=`expr $ok + 1`
    else
      cecho "$solutionchecker \\"
      cecho "$cnf $log"
      cecho -n "# 0 ..."
      if $solutionchecker $cnf $log 1>&2 >$chk
      then
        cecho " ${GOOD}ok${NORMAL} (solution checked externally)"
	ok=`expr $ok + 1`
      else
	cecho " ${BAD}FAILED${NORMAL} (incorrect solution)"
	failed=`expr $failed + 1`
      fi
    fi
  fi
}

run () {
  core $* none
  core $* $dratchecker
  core $* $lratchecker
  simp $*
}

run empty 10
run false 20

run unit0 10
run unit1 10
run unit2 10
run unit3 10
run unit4 20
run unit5 20
run unit6 20
run unit7 20

run sub0 10

run sat0 20
run sat1 10
run sat2 10
run sat3 10
run sat4 10
run sat5 20
run sat6 10
run sat7 10
run sat8 10
run sat9 10
run sat10 10
run sat11 10
run sat12 10
run sat13 10

run full1 20
run full2 20
run full3 20
run full4 20
run full5 20
run full6 20
run full7 20

run regr000 10
run elimclash 20
run elimredundant 10

run block0 10

run prime4 10
run prime9 10
run prime25 10
run prime49 10
run prime121 10
run prime169 10
run prime361 10
run prime289 10
run prime529 10
run prime841 10
run prime961 10
run prime1369 10
run prime1681 10
run prime1849 10
run prime2209 10

run factor2708413neg 10
run factor2708413pos 10

run sqrt2809 10
run sqrt3481 10
run sqrt3721 10
run sqrt4489 10
run sqrt5041 10
run sqrt5329 10
run sqrt6241 10
run sqrt6889 10
run sqrt7921 10
run sqrt9409 10
run sqrt10201 10
run sqrt10609 10
run sqrt11449 10
run sqrt11881 10
run sqrt12769 10
run sqrt16129 10
run sqrt63001 10
run sqrt259081 10
run sqrt1042441 10

run ph2 20
run ph3 20
run ph4 20
run ph5 20
run ph6 20

run add4 20
run add8 20
run add16 20
run add32 20
run add64 20
run add128 20

run prime65537 20

#--------------------------------------------------------------------------#

[ $ok -gt 0 ] && OK="$GOOD"
[ $failed -gt 0 ] && FAILED="$BAD"

msg "${HILITE}CNF testing results:${NORMAL} ${OK}$ok ok${NORMAL}, ${FAILED}$failed failed${NORMAL}"

exit $failed
