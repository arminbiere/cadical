#!/bin/sh
cd `dirname $0`
egrep '^(OPTION|BCEOPT|SHROPT)\( ' ../src/options.hpp | \
grep -v '\<double,' | \
sed -e 's,^[^(]*(,,' \
    -e 's/\<int,//' \
    -e 's/\<bool,//' \
    -e 's,".*,,' \
    -e 's/,[^,]*$//' \
    -e 's,/\*[^\*]*\*/,,' \
    -e 's/,/ /g' | \
awk '{printf "%s %d %d %d\n", $1, $2, $3, $4}' | \
grep -v 'check' | \
grep -v 'clim' | \
grep -v 'dlim' | \
grep -v 'extend' | \
grep -v 'learn' | \
grep -v 'witness'
