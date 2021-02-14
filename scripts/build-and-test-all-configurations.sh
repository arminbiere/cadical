#!/bin/sh

. `dirname $0`/colors.sh || exit 1

############################################################################

die () {
  echo "build-and-test-all-configurations.sh: ${BAD}error${NORMAL}: $*" 1>&2
  exit 1
}

############################################################################

if [ -f configure ]
then
  configure="./configure"
  makeoptions=""
elif [ -f ../configure ]
then
  configure="../configure"
  makeoptions=" -C .."
else
  die "Can not find 'configure'."
fi

if [ "$CXX" = "" ]
then
  environment=""
else
  environment="CXX=$CXX "
fi

if [ ! "$CXXFLAGS" = "" ]
then
  [ "$environment" = "" ] || environment="$environment "
  environment="${environment}CXXFLAGS=\"$CXXFLAGS\" "
fi

############################################################################

ok=0

run () {
  if [ "$*" = "" ]
  then
    configureoptions=""
    description="<empty>"
  else
    configureoptions=" $*"
    description="$*"
  fi
  echo "$environment$configure$configureoptions && make$makeoptions test"
  $configure$configureoptions $* >/dev/null 2>&1 && \
  make$makeoptions test >/dev/null 2>&1
  test $? = 0 || die "Configuration \`$description' failed."
  make$makeoptions clean >/dev/null 2>&1
  test $? = 0 || die "Cleaning up for \`$description' failed."
  ok=`expr $ok + 1`
}

############################################################################

# start with these two for fast fail

run		# default configuration (depends on 'MAKEFLAGS'!)
run -p		# then check default pedantic first

run -q		# library users might want to disable messages
run -q -p	# also check '--quiet' pedantically

# now start with the five single options

run -a		# actually enables all the four next options below
run -c
run -g
run -l

# all five single options pedantically

run -a -p
run -c -p
run -g -p
run -l -p

# all legal pairs of single options
# ('-a' can not be combined with any of the other options)
# ('-g' can not be combined '-c')

run -c -l
run -c -q
run -g -l
run -g -q

# the same pairs but now with pedantic compilation

run -c -l -p
run -c -q -p
run -g -l -p
run -g -q -p

# finally check that these also work to some extend

run -m32 -q
run -m32 -a -p

run --no-unlocked -q
run --no-unlocked -a -p

run --no-contracts -q
run --no-contracts -a -p

run --no-tracing -q
run --no-tracing -a -p

echo "successfully compiled and tested ${GOOD}${ok}${NORMAL} configurations"
