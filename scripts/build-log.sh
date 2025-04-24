#!/bin/sh


set -eu


dest="logs/$(date +%y%m%d_%H%M)"

echo "New log: $dest"

if ! /usr/bin/time -v stdbuf -oL pack build > "$dest" 2>&1;
then
    mv "$dest" "$dest.fail"
fi
