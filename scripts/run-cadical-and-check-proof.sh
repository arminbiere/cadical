#!/bin/sh
prefix=/tmp/run-cadical-and-check-proof
`dirname $0`/../build/cadical $1 $prefix.proof > $prefix.log
res=$?
cat $prefix.log
case $res in
  10) precochk $1 $prefix.log; res=$?;;
  20) drabt -v $1 $prefix.proof || exit 1;;
esac
exit $res
