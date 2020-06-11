#!/bin/sh

die () {
  cecho "${HIDE}test/trace/run.sh:${NORMAL} ${BAD}error:${NORMAL} $*"
  exit 1
}

msg () {
  cecho "${HIDE}test/trace/run.sh:${NORMAL} $*"
}

for dir in . .. ../..
do
  [ -f $dir/scripts/colors.sh ] || continue
  . $dir/scripts/colors.sh || exit 1
  break
done

#--------------------------------------------------------------------------#

[ -d ../test -a -d ../test/trace ] || \
die "needs to be called from a top-level sub-directory of CaDiCaL"

[ x"$CADICALBUILD" = x ] && CADICALBUILD="../build"

[ -x "$CADICALBUILD/cadical" ] || \
  die "can not find '$CADICALBUILD/cadical' (run 'make' first)"

cecho -n "$HILITE"
cecho "---------------------------------------------------------"
cecho "Regression Testing API traces in '$CADICALBUILD'" 
cecho "---------------------------------------------------------"
cecho -n "$NORMAL"

cd $CADICALBUILD || exit 1
make
res=$?
[ $res = 0 ] || exit $res


#--------------------------------------------------------------------------#

ok=0
failed=0
executed=0

run () {
  msg "running ${HILITE}'$1'${NORMAL}"
  trace=../test/trace/$1.trace
  executed=`expr $executed + 1`
  cecho "$CADICALBUILD/mobical $trace"
  $CADICALBUILD/mobical $trace 2>/dev/null 1>/dev/null
  res=$?
  cecho $res
  if [ $res = 0 ]
  then
    cecho "# ... ${GOOD}ok${NORMAL}"
    ok=`expr $ok + 1`
  else
    cecho "# ... ${BAD}failed${NORMAL}"
    failed=`expr $failed + 1`
  fi
}

#--------------------------------------------------------------------------#

traces="`ls ../test/trace/*.trace|sed -e 's,.*/,,' -e 's,\.trace$,,'`"
numtraces="`echo $traces|wc -w`"
msg "found $numtraces traces"

for trace in $traces ignore
do
  [ $trace = ignore ] && continue
  run $trace
done

#--------------------------------------------------------------------------#

if [ $failed -gt 0 ]
then
  OK=""
  FAILED=$BAD
elif [ $ok -gt 0 ]
then
  OK=$GOOD
  FAILED=""
else
  OK=""
  FAILED=""
fi

msg "executed $executed traces," \
    "${OK}$ok ok${NORMAL}," \
    "${FAILED}$failed failed$NORMAL"

exit $failed
