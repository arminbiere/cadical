#!/bin/sh

cd `dirname $0`

if [ ! -x ../cadical ]
then
  echo "*** run-regression.sh: make 'cadical' first" 1>&2
  exit 1
fi

ok=0
failed=0

run () {
  echo -n $program $*
  ../cadical cnfs/$1.cnf 1>cnfs/$1.log 2>cnfs/$2.err
  res=$?
  if [ $res = $2 ]
  then 
    echo " ok"
    ok=`expr $ok + 1`
  else 
    echo " failed (incorrect exit code $res)"
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
