#!/bin/sh
# Frobenius-invariant cyclotomic unions for NL_n(n/2-2): m=5 (N=341), m=7 (N=381), m=8 (N=85, 255). 4 parallel, below-normal.
cd "$(dirname "$0")"
printf '%s\n' "16 85 42" "16 255 126" "14 381 186" "10 341 154" |
  xargs -P 4 -I{} sh -c 'f=$(echo "{}" | tr " " "_"); cmd //c "start /belownormal /wait /b target2\release\cyc.exe {} frob 5000000000 > big_$f.out 2>&1"'
