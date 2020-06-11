#!/bin/sh

#--------------------------------------------------------------------------#

die () {
  cecho "${HIDE}test/mbt/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/mbt/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/mbt ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "Model-Based Testing in '$CADICALBUILD'" 
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

make -C $CADICALBUILD
res=$?
[ $res = 0 ] || exit $res

#--------------------------------------------------------------------------#

tests=1000

msg "generating and running $tests randomly generated tests"
msg "changing to build directory '$CADICALBUILD' and running"
cd $CADICALBUILD

cmd="./mobical 42 --medium -L $tests --do-not-fork"
cecho "${HILITE}$cmd${NORMAL}"
$cmd
res=$?

if [ $res = 0 ]
then
  msg "${GOOD}all tests succeeded${NORMAL}"
else
  msg "${GOOD}some tests failed${NORMAL}"
fi

msg "consider to run 'mobical' for longer (without argument)"

exit $res
