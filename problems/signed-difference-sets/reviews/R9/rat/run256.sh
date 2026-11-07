#!/bin/sh
# NL_16(6) (256,102,38,42) in abelian groups of order 256 with <= 59 rational classes; control: NL_16(8) in C16xC16
# (Malandro-Smith: 245760 PDS of size 136). 8 parallel, below-normal, node limit 5e9.
cd "$(dirname "$0")"
printf '%s\n' "8 5000000000 16 16" "6 5000000000 256" "6 5000000000 2 128" "6 5000000000 4 64" "6 5000000000 2 2 64" "6 5000000000 8 32" "6 5000000000 2 4 32" "6 5000000000 2 2 2 32" "6 5000000000 16 16" "6 5000000000 2 8 16" |
  xargs -P 8 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target\release\rat.exe {} > o256_$f.out 2>&1"'
