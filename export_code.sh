#!/usr/bin/env sh

# Exports verified code as specified in the Isabelle theory
# Assumes that CWD is at the root of the Stack project and Isabelle is on PATH

# Clean export destination
echo "Cleaning ..."
rm -rf haskell/isabelle/src/Hyperdual

# Build theory with exporting enabled
echo "Exporting ..."
isabelle export -d . -o quick_and_dirty=true -o document=false -x "*:code/**" -O . -p 2 Hyperdual
