#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  echo "*** run-regression.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[run-regression.sh] $*"
}

#--------------------------------------------------------------------------#

cd `dirname $0`

[ x"$CADICALBUILD" = x ] && \
  CADICALBUILD="`pwd|xargs dirname`/build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

msg "regression testing '$CADICALBUILD/cadical'" 

#--------------------------------------------------------------------------#

binary="$CADICALBUILD/cadical"

checker=none
for d in `echo $PATH | tr : \ `
do
  if [ -x "$d/drabt" ]
  then 
    checker="$d/drabt -v"
    break 
  elif [ -x "$d/drat-trim" ]
  then
    checker="$d/drat-trim"
    break
  fi
done

if [ x"$checker" = xnone ]
then
  msg "no proof checking (neither 'drabt' nor 'drat-trim' found)"
else
  msg "checking DRAT proofs with '$checker'"
fi

ok=0
failed=0

run () {
  if [ -f cnfs/$1.sol ]
  then
    solopts=" -s ../test/cnfs/$1.sol"
  else
    solopts=""
  fi
  if [ ! $2 = 20 -o x"$checker" = xnone ]
  then
    proofopts=""
  else
    proofopts=" ../test/cnfs/$1.proof"
  fi
  opts="../test/cnfs/$1.cnf$solopts$proofopts"
  printf "$binary $opts # $2 ..."
  "$binary" $opts 1>cnfs/$1.log 2>cnfs/$1.err
  res=$?
  if [ $res = $2 ]
  then 
    if [ $res = 10 ]
    then
      echo " ok"
      ok=`expr $ok + 1`
    elif [ x"$checker" = xnone ]
    then
      echo " ok"
      ok=`expr $ok + 1`
    else
      $checker cnfs/$1.cnf cnfs/$1.proof 1>&2 >cnfs/$1.check
      if test $?
      then
	echo " ok (proof checked)"
	ok=`expr $ok + 1`
      else
	echo " failed (proof check '$checker cnfs/$1.cnf cnfs/$1.proof' failed)"
	failed=`expr $failed + 1`
      fi
    fi
  else 
    echo " failed (exit code $res)"
    failed=`expr $failed + 1`
  fi
}

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

msg "regression results: $ok ok, $failed failed"
exit $failed
