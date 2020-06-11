# Use colors if '<stdin>' is connected to a terminal.

color_echo_options=""

if [ -t 1 ]
then
  BAD="\033[1;31m"  # bright red
  HILITE="\033[32m" # normal green
  GOOD="\033[1;32m" # bright green
  HIDE="\033[34m"   # cyan
  BOLD="\033[1m"    # bold color
  NORMAL="\033[0m"  # normal color

  if [ x"`echo -e 2>/dev/null`" = x ]
  then
    color_echo_options=" -e"
  fi
else
  BAD=""
  HILITE=""
  GOOD=""
  HIDE=""
  BOLD=""
  NORMAL=""
fi

cecho () {
  echo$color_echo_options $*
}
