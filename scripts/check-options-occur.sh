#!/bin/sh
sed \
  -e '/^[OLQ[A-Z]*(/!d' \
  -e 's,^[OLQ[A-Z]*(,,' \
  -e 's/,.*//' \
  ../src/options.hpp | \
while read option
do
  grep -q opts.$option ../src/*.hpp ../src/*.cpp && continue
  echo "option '$option' not found"
done
