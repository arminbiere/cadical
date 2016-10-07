#!/bin/sh
COMPILE="`sed -e '/^COMPILE=/!d' -e 's,.*=,,' makefile`"
echo "#define VERSION \"`cat ../VERSION`\""
echo "#define COMPILE \"$COMPILE\""
echo "#define GITID \"`./get-git-id.sh`\""
