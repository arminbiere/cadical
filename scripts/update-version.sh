#!/bin/sh
cd `dirname $0`
NEW="`cat ../VERSION`"
OLD="`awk '/define VERSION/{print \$4}' ../src/version.cpp|sed -e 's,\",,g'`"
if [ x"$OLD" = x"$NEW" ]
then
  echo "same version '$NEW' in 'VERSION' and '../src/version.cpp'"
else
  echo "found new version '$NEW' in '../VERSION'"
  echo "updating old version '$OLD' in '../src/version.cpp'"
  sed -i -e '/define VERSION/s,".*",'\""$NEW"\", ../src/version.cpp
fi
