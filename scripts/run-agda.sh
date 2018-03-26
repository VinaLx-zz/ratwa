#! /usr/bin/env sh

for i in src/Ratwa/**/*.agda; do
    echo "$i"
    agda -v0 "$i"
done

