#!/bin/sh
# L_8(3) (64,21,8,6) in the abelian groups of order 64 that are not H x H; 5 parallel, below-normal.
cd "$(dirname "$0")"
printf '%s\n' "4 4 4" "2 4 8" "2 2 2 8" "2 2 16" "4 16" "2 32" "64" "2 2 2 2 4" |
  xargs -P 5 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target2\release\rat.exe -3 4000000000 {} > L64_$f.out 2>&1"'
