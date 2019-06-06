#!/bin/sh

echo `dirname $0`
cd `dirname $0`

pwd

. ./colors.sh

new=/tmp/cadical.hpp
old=../src/cadical.hpp
example=../test/api/example.cpp

rm -f $new
sed -e '/solver = new CaDiCaL::Solver/,$d' $old >> $new
sed -e '/solver = new CaDiCaL::Solver/,/delete solver/!d' $example | \
expand | sed -e 's,^,//  ,' >> $new
sed -e '1,/delete solver/d' $old >> $new

echo "${HILITE}diff $old $new${NORMAL}"
if diff $old $new
then
  echo "${GOOD}no need to update '$old'${NORMAL}"
else
  echo "${BAD}cp $new $old${NORMAL}"
  cp $new $old
fi
rm -f $new
