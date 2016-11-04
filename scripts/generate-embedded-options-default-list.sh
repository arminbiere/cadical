#!/bin/sh
cd `dirname $0`
grep '^OPTION' ../src/options.hpp | \
grep '\<int,' | \
sed -e 's,^OPTION(,,' \
    -e 's/\<int,//' \
    -e 's/,/ /' \
    -e 's/,.*//g' | \
awk '{printf "c --%s=%d\n", $1, $2}' | \
grep -v 'check' | \
grep -v 'clim' | \
grep -v 'dlim' | \
grep -v 'witness'
