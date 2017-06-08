#!/bin/sh

# Grab the list of versioned lagda files in doc/
TARGETS=$(git ls-tree -r --name-only HEAD doc/*.lagda)
# Remove each one of its src/*.agda counterpart
for i in ${TARGETS}
do
  TARGET=$(basename $i .lagda)
  rm -f src/${TARGET}.agda
done
