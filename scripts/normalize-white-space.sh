#!/bin/sh
cd `dirname $0`/../src
for i in *.cpp *.hpp
do
  cp $i $i~ || exit 1
  expand $i~ |sed -e 's,  *$,,'|uniq > $i
  rm -f $i~
done
