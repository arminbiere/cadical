# Use colors if '<stdin>' is connected to a terminal.

if [ -t 1 ]
then
  BAD="\033[1;31m"	# bright red
  HILITE="\033[32m"	# normal green
  GOOD="\033[1;32m"	# bright green
  HIDE="\033[34m"	# cyan
  BOLD="\033[1m"        # bold color
  NORMAL="\033[0m"	# normal color
else
  BAD=""
  HILITE=""
  GOOD=""
  HIDE=""
  BOLD=""
  NORMAL=""
fi
