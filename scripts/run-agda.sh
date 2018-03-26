#! /usr/bin/env sh

agda_sources=$(find src -name "*.agda")

for i in $agda_sources; do
    echo "$i"
    agda -v0 "$i"
done

