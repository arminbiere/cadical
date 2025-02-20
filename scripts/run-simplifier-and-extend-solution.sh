#!/bin/sh
scriptsdir=`dirname $0`
bindir=$scriptsdir/../build
solver=$bindir/cadical
colors=$scriptsdir/colors.sh
extend=$scriptsdir/extend-solution.sh
name=run-simplifier-and-extend-solution.sh
if [ -f $colors ]
then
  . $colors
else
  BAD=""
  BOLD=""
  HIDE=""
  NORMAL=""
fi
die () {
  echo "${BOLD}$name:${NORMAL} ${BAD}error:${NORMAL} $*" 1>&2
  exit 1
}
msg () {
  echo "${HIDE}c [$name] $*${NORMAL}"
}
input=""
options=""
while [ $# -gt 0 ]
do
  case $1 in
    -t) options="$1 $2"; shift;;
    *)
      if [ -f $1 ]
      then
        [ "$input" ] && die "too many inputs"
        input="$1"
      else
	die "invalid option '$1'"
      fi
      ;;
  esac
  shift
done
msg "input '$input'"
msg "options '$options'"
[ "$input" ] || die "expected at least one input argument"
[ -f $solver ] || \
die "can not find '$solver' (build solver first)"
msg "found '$solver'"
[ -f $extend ] || \
die "can not find '$extend'"
prefix=/tmp/run-simplifier-and-extend-solution-$$
trap "rm -f $prefix*" 2 9 15
out=$prefix.out
ext=$prefix.ext
log=$prefix.log
msg "$solver $options -n -O1 -c 0 -o $out -e $ext $input > $log"
$solver $options -n -O1 -c 0 -o $out -e $ext $input > $log
res=$?
msg "simplifier exit code '$res'"
msg "sed -e 's,^[vs],c,' -e 's,^c,c [simplifier],' $log"
sed -e 's,^[vs],c,' -e 's,^c,c [simplifier],' $log
msg "$solver $options $out > $log"
$solver $options $out > $log
res=$?
msg "solver exit code '$res'"
msg "sed -e 's,^[vs],c,' -e 's,^c,c [solver],' $log"
sed -e 's,^[vs],c,' -e 's,^c,c [solver],' $log
case $res in
  0|10|20) ;;
  *) die "unexpected solver exit code '$res'";;
esac
if [ $res = 10 ]
then
  msg "$extend $log $ext"
  $extend $log $ext
  res=$?
  msg "extender exit code $res"
elif [ $res = 20 ]
then
  echo "s UNSATISFIABLE"
fi
msg "rm -f $prefix*"
rm -f $prefix*
msg "exit $res"
exit $res
