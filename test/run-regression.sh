#!/bin/sh

cd `dirname $0`

die () {
  echo "*** run-regression.sh: $*" 1>&2
  exit 1
}

binary=../build/cadical

[ -x $binary ] || die "make 'cadical' first"

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
  echo "no proof checking (neither 'drabt' nor 'drat-trim' found)"
else
  echo "checking DRAT proofs with '$checker'"
fi

ok=0
failed=0

run () {
  if [ -f cnfs/$1.sol ]
  then
    solopts=" -s cnfs/$1.sol"
  else
    solopts=""
  fi
  if [ $2 = 20 -a x"$checker" = xnone ]
  then
    proofopts=""
  else
    proofopts=" cnfs/$1.proof"
  fi
  opts="cnfs/$1.cnf$solopts$proofopts"
  echo -n "$binary $opts # $2 ..."
  $binary $opts 1>cnfs/$1.log 2>cnfs/$1.err
  res=$?
  if [ $res = $2 ]
  then 
    if [ $res = 10 ]
    then
      echo " ok"
      ok=`expr $ok + 1`
    elif [ x"$checker" = x ]
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

echo "regression results: $ok ok, $failed failed"
