#!/bin/sh
# Heavy order-64 cases with the stronger pruning (target3): NL_8(2) and L_8(3) in C2^4 x C4, NL_8(2) in C2^6 (control).
cd "$(dirname "$0")"
printf '%s\n' "2 20000000000 2 2 2 2 4" "-3 20000000000 2 2 2 2 4" "2 20000000000 2 2 2 2 2 2" |
  xargs -P 3 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target3\release\rat.exe {} > H_$f.out 2>&1"'
