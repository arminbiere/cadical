#!/bin/sh
name=extend-solution.sh
scriptsdir=`dirname $0`
colors=$scriptsdir/colors.sh
if [ -f $colors ]
then
  . $colors
else
  BAD=""
  BOLD=""
  NORMAL=""
fi
die () {
  echo "${BOLD}$name:${NORMAL} ${BAD}error:${NORMAL} $*" 1>&2
  exit 1
}
[ $# -eq 2 ] || \
die "expected exactly two arguments"
[ -f $1 ] || \
die "argument '$1' not a file"
[ -f $2 ] || \
die "argument '$2' not a file"
status="`grep '^s' $1|head -1`"
case x"$status" in
  x"s SATISFIABLE") ;;
  x"s UNSATISFIABLE") echo "s UNSATISFIABLE"; exit 20;;
  *) die "not valid 's ...' line found in '$1'";;
esac
( 
  grep '^v' $1;
  awk '{
    printf "c"
    for (i = 1; $i; i++)
      printf " %d", $i
    printf "\nw";
    for (i++; $i; i++)
      printf " %d", $i
    printf "\n"
  }' $2
) | \
awk '
function abs (i) { return i < 0 ? -i : i }
/^v/{
  for (i = 2; i <= NF; i++) {
    lit = $i;
    idx = abs(lit);
    if (idx) a[idx] = lit;
  }
}
/^c/{
  satisfied = 0
  for (i = 2; i <= NF; i++) {
    lit = $i;
    idx = abs(lit);
    tmp = a[idx];
    if (lit < 0) tmp = -tmp;
    if (tmp > 0) satisfied = 1;
  }
}
/^w/{
  if (satisfied) next
  for (i = 2; i <= NF; i++) {
    lit = $i;
    idx = abs(lit);
    a[idx] = -a[idx];
  }
}
END {
  print "s SATISFIABLE"
  for (i in a)
    print "v", a[i]
  print "v 0"
}
'
exit 10
