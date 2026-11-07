#!/bin/sh
# NL_8(2) (64,18,2,6) in all 11 abelian groups of order 64; 6 parallel, below-normal; node limit 4e9.
cd "$(dirname "$0")"
printf '%s\n' "2 2 2 2 2 2" "2 2 2 2 4" "2 2 2 8" "2 2 4 4" "2 2 16" "2 4 8" "2 32" "4 4 4" "4 16" "8 8" "64" |
  xargs -P 6 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target\release\rat.exe 2 4000000000 {} > o64_$f.out 2>&1"'
