#!/bin/sh
usage () {
cat <<EOF 2>&1
usage: generate-cubes.sh [-h] <input> [ <output> [ <march_cu option> ... ] ]
EOF
exit 0
}
[ "$1" = -h ] && usage
die () {
  echo "generate-cubes.sh: error: $*" 1>&2
  exit 1
}
[ $# -lt 1 ] && die "expected DIMACS file argument"
output=""
options=""
[ -f "$1" ] || die "first argument is not a DIMACS file"
input="$1"
shift
while [ $# -gt 0 ]
do
  case "$1" in
    -*) options="$options $1";;
    *) exec 1>"$1";;
  esac
  shift
done
prefix=/tmp/generate-cubes-$$
cleanup () {
  rm -f $prefix*
}
trap "cleanup" 2 11
cubes=$prefix.cubes
march_cu $input -o $cubes $options 1>&2 || exit 1
sed -e 's,^p cnf.*,p inccnf,' $input
cat $cubes
cleanup
exit 0
