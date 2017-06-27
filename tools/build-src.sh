#!/bin/sh

# Stat by compiling the tool
ghc tools/LiterateToRawAgda.hs -o lit2raw

# Grab the list of versioned lagda files in doc/
TARGETS=$(git ls-tree -r --name-only HEAD doc/ | grep ".*\.lagda$")
# Convert each one of them & put it in src/
for i in ${TARGETS}
do
  TARGET=$(basename $i .lagda)
  DIRECTORY=$(dirname $i | sed "s|doc||")
  ./lit2raw $i
  mkdir -p src/${DIRECTORY}
  mv doc/${DIRECTORY}/${TARGET}.agda src/${DIRECTORY}
done
