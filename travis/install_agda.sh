#!/bin/sh
AGDA_VERSION=2.5.4.2

if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "$AGDA_VERSION" ]; then
  cabal update
  cabal install alex happy cpphs --force-reinstalls
  cabal install Agda-"$AGDA_VERSION" --force-reinstalls
  mkdir -p $HOME/.agda
  cp libraries-"$AGDA_VERSION" $HOME/.agda/
  cd $HOME/.agda/
  wget https://github.com/agda/agda-stdlib/archive/v0.17.tar.gz
  tar -xvzf v0.17.tar.gz
  cd -
fi
