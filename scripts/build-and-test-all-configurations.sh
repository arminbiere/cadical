#!/bin/sh

scriptname=`basename $0`

. `dirname $0`/colors.sh || exit 1

############################################################################

usage() {
cat <<EOF
usage: $scriptname [ <option> ]

where '<option>' is one of the following:

-h                 print this command line option summary
-j[ ]<n>           number '<n>' of parallel threads (passed to 'makefile')
-s[ ]<n>           number '<n>' of starting configuration
-m | -m32          include 32 bit tests
-u | --undefined   also run '-fsanitize=undefined'
EOF
exit 0
}

die () {
  cecho "$scriptname: ${BAD}${BOLD}error${NORMAL}: $*" 1>&2
  exit 1
}

fatal () {
  cecho "$scriptname: ${BAD}${BOLD}fatal internal error${NORMAL}: $*" 1>&2
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
skipped=0
running="unknown"

skip() {
  while [ $# -gt 0 ]
  do
    case x"$1" in
      x"-m32") test $m32 = no && return 0;;
      x"-fsanitize=undefined") test $undefined = no && return 0;;
    esac
    shift
  done
  return 1
}

run () {
  if [ "$*" = "" ]
  then
    configureoptions=""
  else
    configureoptions=" $*"
  fi
  if skip $*
  then
    cecho "[$running] $environment$configure$configureoptions # skipped"
    skipped=`expr $skipped + 1`
  else
    cecho "[$running] $environment$configure$configureoptions && make$makeoptions$makeflags && make$makeoptions$makeflags test && make$makeoptions$makeflags clean"
    $configure$configureoptions $* >/dev/null 2>&1
    test $? = 0 || die "configuration $running failed (run '$configure$configureoptions $*' to investigate)"
    make$makeoptions$makeflags >/dev/null 2>&1
    test $? = 0 || die "building configuration $running failed (run 'make' to investigate)"
    make$makeoptions$makeflags test >/dev/null 2>&1
    test $? = 0 || die "testing configuration $running failed (run 'make test' to investigate)"
    make$makeoptions$makeflags clean >/dev/null 2>&1
    test $? = 0 || die "cleaning configuration $running failed (run 'make clean' to investigate)"
    ok=`expr $ok + 1`
  fi
}


runExtraMobical () {
  if [ "$*" = "" ]
  then
    configureoptions=""
  else
    configureoptions=" $*"
  fi
  if skip $*
  then
    cecho "[$running] $environment$configure$configureoptions # skipped"
    skipped=`expr $skipped + 1`
  else
    cecho "[$running] $environment$configure$configureoptions && make$makeoptions$makeflags && ./build/mobical 42 --medium -L 1000 --do-not-fork && make$makeoptions$makeflags test && make$makeoptions$makeflags clean"
    $configure$configureoptions $* >/dev/null 2>&1
    test $? = 0 || die "configuration $running failed (run '$configure$configureoptions $*' to investigate)"
    make$makeoptions$makeflags >/dev/null 2>&1
    test $? = 0 || die "building configuration $running failed (run 'make' to investigate)"
    make$makeoptions$makeflags test >/dev/null 2>&1
    test $? = 0 || die "testing configuration $running failed (run 'make test' to investigate)"
    ./build/mobical 42 --medium -L 1000 --do-not-fork
 >/dev/null 2>&1
    test $? = 0 || die "./build/mobical 42 -L 10000 $running failed (run 'make test' to investigate)"

    make$makeoptions$makeflags clean >/dev/null 2>&1
    test $? = 0 || die "cleaning configuration $running failed (run 'make clean' to investigate)"
    ok=`expr $ok + 1`
  fi
}

############################################################################

begin=0
end=36

m32=no
undefined=no

while [ $# -gt 0 ]
do
  case "$1" in
    -h) usage;;
    -j[1-9]|-j[1-9][0-9]*)
       makeflags=" -j`echo @$1 |sed -e 's,@-j,,'`"
       ;;
    -j)
        shift
	test $# = 0 && die "argument to '-j' missing'"
	case "$1" in
	  [0-9]|[1-9][0-9]) makeflags="$1" ;;
	  *) die "invalid argument in '-j $1'" ;;
	esac
	;;
    -m|-m32) m32=yes;;
    -u|-undefined|--undefined) undefined=yes;;
    -s[0-9]|-s[1-9][0-9])
       begin=`echo "@$1" |sed -e 's,@-s,,'`
       test $begin -gt $end && \
         die "invalid start configuration '$1' (above end '$end')"
       ;;
    -s)
        shift
	test $# = 0 && die "argument to '-s' missing'"
	case "$1" in
	  [0-9]|[1-9][0-9]*) begin="$1" ;;
	  *) die "invalid argument in '-s $1'" ;;
	esac
	 test $begin -gt $end && \
	   die "invalid start configuration '-s $1' (above end '$end')"
	;;
    *)
      die "invalid option '$1' (try '-h')"
      ;;
  esac
  shift
done

############################################################################

map_and_run () {

  running="$1" # such that 'run' knows the configuration number

  case $1 in

    0) run ;;	# run default configuration first
    1) run -p;;	# then check default pedantic next

    2) run -q;;	# library users might want to disable messages
    3) run -q -p;;	# also check '--quiet' pedantically

    # now start with the five single options

    4) run -a;;	# actually enables all the four next options below
    5) run -c;;
    6) run -g;;
    7) run -l;;

    # all five single options pedantically

    8) run -a -p;;
    9) run -c -p;;
    10) run -g -p;;
    11) run -l -p;;

    # all legal pairs of single options
    # ('-a' can not be combined with any of the other options)
    # ('-g' can not be combined '-c')

    12) run -c -l;;
    13) run -c -q;;
    14) run -g -l;;
    15) run -g -q;;

    # the same pairs but now with pedantic compilation

    16) run -c -l -p;;
    17) run -c -q -p;;
    18) run -g -l -p;;
    19) run -g -q -p;;

    # finally check that these also work to some extend

    20) run --no-unlocked -q;;
    21) run --no-unlocked -a -p;;

    22) run --no-contracts -q;;
    23) run --no-contracts -a -p;;

    24) run --no-tracing -q;;
    25) run --no-tracing -a -p;;

    26) run -m32 -q;;
    27) run -m32 -a -p;;

    # Shared library builds

    28) run -shared;;
    29) run -shared -p;;
    30) run -shared -p -m32;;

    # Sanitizer configurations

    31) run -a -fsanitize=address;;
    32) run -a -p -fsanitize=address;;
    33) run -a -fsanitize=undefined;;
    34) run -a -p -fsanitize=undefined;;
    35) run -a -Wswitch-enum -p -Wextra -Wall -Wextra -Wformat=2 -Wswitch-enum -Wpointer-arith -Winline -Wundef -Wcast-qual -Wwrite-strings -Wunreachable-code -Wstrict-aliasing -fno-common -fstrict-aliasing -Wno-format-nonliteral;;

    # memory fuzzing
    36) runExtraMobical -a -p --memory-fuzzing

      executed_last_configuration=yes # Keep this as part of last configuration!

      ;;

    *) fatal "iterating over invalid configuration '$1'";;
  esac
}

############################################################################


built_and_tested=0;
configurations=`expr $end + 1`
executed_last_configuration=no

cecho "building and testing ${BOLD}$configurations${NORMAL} configurations 0..$end"

if [ $begin = 0 ]
then
  cecho "starting with default configuration $begin"
else
  cecho "starting with non-default configuration $begin (and then wrapping around)"
fi

i=$begin
while [ $built_and_tested -lt $configurations ]
do
  map_and_run $i
  built_and_tested=`expr $built_and_tested + 1`
  i=`expr $i + 1`
  [ $i -gt $end ] && i=0
done

############################################################################

test $executed_last_configuration = no && \
  fatal "last configuration not executed"

if [ $skipped = 0 ]
then
  cecho "successfully built and tested ${GOOD}${ok}${NORMAL} configurations (none skipped)"
else
  cecho "successfully built and tested ${GOOD}${ok}${NORMAL} configurations ($skipped skipped)"
fi
