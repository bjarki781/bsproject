#!/usr/bin/bash -x

ghc -O2 sysgen
./sysgen | sage maketex.sage

