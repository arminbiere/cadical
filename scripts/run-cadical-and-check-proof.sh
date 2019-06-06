#!/bin/sh
scriptsdir=`dirname $0`
bindir=$scriptsdir/../build
solver=$bindir/cadical
solutionchecker=$bindir/precochk
proofchecker=$bindir/drat-trim
name=run-cadical-and-check-proof.sh
colors=$scriptsdir/colors.sh
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
  echo "$name: error: $*" 1>&2
  exit 1
}
msg () {
  echo "${HIDE}c [$name] $*${NORMAL}"
}
[ $# -eq 1 ] || \
die "expected exactly one argument"
msg "input '$1'"
[ -f $solver ] || \
die "can not find '$solver' (build solver first)"
msg "found '$solver'"
[ -f $solutionchecker ] || \
die "can not find '$solutionchecker' (run cnf tests to compile it first)"
msg "found '$solutionchecker'"
[ -f $proofchecker ] || \
die "can not find '$proofchecker' (run cnf tests to compile it first)"
msg "found '$proofchecker'"
prefix=/tmp/run-cadical-and-check-proof-$$
trap "rm -f $prefix*" 2 9 15
msg "$solver $1 $prefix.proof > $prefix.log"
$solver $1 $prefix.proof > $prefix.log
res=$?
msg "solver exit code '$res'"
msg "cat $prefix.log"
cat $prefix.log
case $res in
  10) 
    msg "$solutionchecker $1 $prefix.log"
    $solutionchecker $1 $prefix.log || exit 1
    ;;
  20)
    msg "$proofchecker $1 $prefix.proof"
    $proofchecker $1 $prefix.proof || exit 1
    ;;
esac
msg "rm -f $prefix*"
rm -f $prefix*
msg "exit $res"
exit $res
