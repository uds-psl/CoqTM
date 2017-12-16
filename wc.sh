#!/bin/bash
# Please don't count this!
rm -rf TM/Compound.v
git ls-tree --full-tree HEAD -r --name-only | grep --line-regexp "^.*\.v$" | sort | xargs coqwc > wc.txt 2>/dev/null
