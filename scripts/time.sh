#!/bin/sh
file=`echo "$*"|awk '{print $NF}'`
tmp=/tmp/cadical-scripts-time.sh-$$
trap "rm -f $tmp*" 2 9 15
LC_ALL=C
export LC_ALL
if [ x"`uname`" = xDarwin ]
then
  /usr/bin/time -o $tmp $*
  time=`awk '{print $1}' $tmp`
else 
  /usr/bin/time -f "%e" --output-file=$tmp
  time=`cat $tmp`
fi
echo "  compiling $file took $time seconds"
rm -f $tmp*
