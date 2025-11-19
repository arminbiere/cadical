#!/bin/sh

script=`basename $0`

die () {
  echo "$script: error: $*" 1>&2
  exit 1
}

cd `dirname $0`

NEW="`cat ../VERSION`"
OLD="`awk '/define VERSION/{print \$4}' ../src/version.cpp|sed -e 's,\",,g'`"

if [ x"$OLD" = x"$NEW" ]
then
  echo "same version '$NEW' in 'VERSION' and '../src/version.cpp'"
else
  echo "found new version '$NEW' in '../VERSION'"
  echo "updating old version '$OLD' in '../src/version.cpp'"
  sed -i -e '/define VERSION/s,".*",'\""$NEW"\", ../src/version.cpp || \
  die "patching 'version.hpp' failed"
fi

MAJOR=`echo $NEW|sed -e 's,^\([0-9][0-9]*\)\..*,\1,'`
MINOR=`echo $NEW|sed -e 's,^[^\.]*\.\([0-9][0-9]*\)\..*,\1,'`
PATCH=`echo $NEW|sed -e 's,^[^\.]*\.[^\.]*\.\([0-9][0-9]*\).*,\1,'`

test "$MAJOR" = "" && die "could extract major version"
test "$MINOR" = "" && die "could extract minor version"
test "$PATCH" = "" && die "could extract patch version"

echo "semantic numeric version '$MAJOR.$MINOR.$PATCH'"

sed -i \
  -e "s,^#define CADICAL_MAJOR .*//,#define CADICAL_MAJOR $MAJOR //," \
  -e "s,^#define CADICAL_MINOR .*//,#define CADICAL_MINOR $MINOR //," \
  -e "s,^#define CADICAL_PATCH .*//,#define CADICAL_PATCH $PATCH //," \
../src/cadical.hpp || die "patching 'cadical.hpp' failed"
