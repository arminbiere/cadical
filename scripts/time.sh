#!/bin/sh
tmp=/tmp/cadical-scripts-time.sh-$$
trap "rm -f $tmp*" 2 9 15
LC_ALL=C
export LC_ALL
if [ x"$1" = xar -a x"$2" = xrc ]
then
  action=archiving
  target="$3"
elif [ x"`echo $*|grep -- -o`" = x ]
then
  action=compiling
  target=`echo "$*" | awk '{print $NF}'`
else
  action=linking
  target=`echo "$*" | sed -e 's,.* -o \([^ ]*\).*,\1,'`
fi
if [ x"`uname`" = xDarwin ]
then
  /usr/bin/time -o $tmp $*
  time=`awk '{print $1}' $tmp`
else 
  /usr/bin/time -f "%e" --output-file=$tmp $*
  time=`cat $tmp`
fi
echo "  $action $target took $time seconds"
rm -f $tmp*
