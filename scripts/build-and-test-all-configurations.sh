#!/bin/bash

. `dirname $0`/colors.sh || exit 1

startConfiguration=0

############################################################################

die () {
  echo "build-and-test-all-configurations.sh [-j N] [-s StartConfiguration]: ${BAD}error${NORMAL}: $*" 1>&2
  echo "You can pass the configuration number to start directly from one configuration"
  echo "The argument to -j is not optional. It only refers to makefile arguments, the compilation is not run in parallel."
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
  echo "$environment$configure$configureoptions && make$makeoptions$makeflags test"
  $configure$configureoptions $* >/dev/null 2>&1 && \
  make$makeoptions$makeflags test >/dev/null 2>&1
  test $? = 0 || die "Configuration \`$description' failed."
  make$makeoptions$makeflags clean >/dev/null 2>&1
  test $? = 0 || die "Cleaning up for \`$description' failed."
  ok=`expr $ok + 1`
}

############################################################################

END=31

while getopts "j:s:h" arg; do
  case $arg in
    h)
      die ""
      ;;
    j)
      strength=$OPTARG
      makeflags=" -j${OPTARG}"
      ;;
    s)
      startConfiguration=$OPTARG
      ;;
  esac
done

foundLast=0

run_configuration () {
    case $1 in		# default configuration (depends on 'MAKEFLAGS'!)
        0) run -p;;		# then check default pedantic first

        1) run -q;;		# library users might want to disable messages
        2) run -q -p;;	# also check '--quiet' pedantically

        # now start with the five single options

        3) run -a;;		# actually enables all the four next options below
        4) run -c;;
        5) run -g;;
        6) run -l;;

        # all five single options pedantically

        7) run -a -p;;
        8) run -c -p;;
        9) run -g -p;;
        10) run -l -p;;

        # all legal pairs of single options
        # ('-a' can not be combined with any of the other options)
        # ('-g' can not be combined '-c')

        11) run -c -l;;
        12) run -c -q;;
        13) run -g -l;;
        14) run -g -q;;

        # the same pairs but now with pedantic compilation

        15) run -c -l -p;;
        16) run -c -q -p;;
        17) run -g -l -p;;
        18) run -g -q -p;;

        # finally check that these also work to some extend

        19) run --no-unlocked -q;;
        20) run --no-unlocked -a -p;;

        21) run --no-contracts -q;;
        22) run --no-contracts -a -p;;

        23) run --no-tracing -q;;
        24) run --no-tracing -a -p;;

        25) run -m32 -q;;
        26) run -m32 -a -p;;

        # Shared library builds

        27) run -shared;;
        28) run -shared -p;;
        29) run -shared -p -m32;;

        # sanitizer configurations
        30) run -a -fsanitize=address -fsanitize=undefined;;
        31) run -a -p -fsanitize=address -fsanitize=undefined;
        # this checks that we found the last configuration
        foundLast=1;
        # the next line is a hint if you add configurations
        [ $END -eq 31 ] || die "invalid number of configuration";;
    esac
}


for i in $(seq 0 $(($END - 1))); do
    v=$(($i + $startConfiguration))
    if [ $v -gt $END ]; then
       v=$(( $v - $END ));
    fi
    echo "running configuration $v"
    run_configuration $v
done

if [ $foundLast -ne 1 ];
then
  die "END does not correspond to the number of tested configuration, please fix it!"
fi;


echo "successfully compiled and tested ${GOOD}${ok}${NORMAL} configurations"
