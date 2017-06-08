#!/bin/sh

# Stat by compiling the tool
ghc tools/LiterateToRawAgda.hs -o lit2raw

# Grab the list of versioned lagda files in doc/
TARGETS=$(git ls-tree -r --name-only HEAD doc/*.lagda)
# Convert each one of them & put it in src/
for i in ${TARGETS}
do
  TARGET=$(basename $i .lagda)
  ./lit2raw $i
  mv doc/${TARGET}.agda src/
done
