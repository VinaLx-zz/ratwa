#! /usr/bin/env sh

cd src || exit 1

agda_sources=$(find . -name "*.agda")

for i in $agda_sources; do
    echo "$i"
    agda -v0 "--include-path=$AGDA_DIR/agda-stdlib/src" "$i"
done

