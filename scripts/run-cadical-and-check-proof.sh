#!/bin/sh
prefix=/tmp/run-cadical-and-check-proof-$$
trap "rm -f $prefix*" 2 9 15
`dirname $0`/../build/cadical $1 $prefix.proof > $prefix.log
res=$?
cat $prefix.log
case $res in
  10) 
    precochk $1 $prefix.log | sed -e 's,^,c ,'
    case $? in
      0|10) res=10;;
      20) res=20;;
      *) res=1;;
    esac
    ;;
  20) drabt -v $1 $prefix.proof || exit 1;;
esac
rm -f $prefix*
exit $res
