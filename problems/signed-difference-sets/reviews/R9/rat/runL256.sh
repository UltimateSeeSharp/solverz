#!/bin/sh
# L_16(7) (256,105,44,42) -> SDS(256,106,42) by the lemma; groups of order 256 with <= 59 rational classes. 5 parallel.
cd "$(dirname "$0")"
printf '%s\n' "256" "2 128" "4 64" "2 2 64" "8 32" "2 4 32" "2 2 2 32" "16 16" "2 8 16" |
  xargs -P 5 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target3\release\rat.exe -7 5000000000 {} > L256_$f.out 2>&1"'
