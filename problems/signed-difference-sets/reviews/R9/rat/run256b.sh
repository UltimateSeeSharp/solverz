#!/bin/sh
# Larger groups of order 256: L_16(7) and NL_16(6), node limit 1e10, 5 parallel, below-normal.
cd "$(dirname "$0")"
printf '%s\n' "-7 10000000000 4 4 16" "6 10000000000 4 4 16" "-7 10000000000 4 8 8" "6 10000000000 4 8 8" "-7 10000000000 2 2 8 8" "6 10000000000 2 2 8 8" "-7 10000000000 4 4 4 4" "6 10000000000 4 4 4 4" |
  xargs -P 5 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target3\release\rat.exe {} > B256_$f.out 2>&1"'
