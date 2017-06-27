#!/bin/sh

# Grab the list of versioned lagda files in doc/
TARGETS=$(git ls-tree -r --name-only HEAD doc/ | grep ".*\.lagda$")
# Remove each one of its src/*.agda counterpart
for i in ${TARGETS}
do
  TARGET=$(basename $i .lagda)
  DIRECTORY=$(dirname $i | sed "s|doc||")
  rm -f src/${DIRECTORY}/${TARGET}.agda
done
