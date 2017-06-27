#!/bin/sh
set -e
set -u

# Grab the list of versioned lagda files in doc/
TARGETS=$(git ls-tree -r --name-only HEAD . | grep ".*\.lagda$")
for i in ${TARGETS}
do
  DIRECTORY=$( dirname  "$i" )
  NAME=$( basename "$i" .lagda )
  TARGET=${DIRECTORY}/${NAME}
  ./lagda2tex $i
  sed -f rules.sed -i latex/${TARGET}.tex
done

