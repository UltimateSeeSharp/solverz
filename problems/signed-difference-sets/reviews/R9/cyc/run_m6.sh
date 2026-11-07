#!/bin/sh
# m = 6 (n = 64, r = 30): unions of cyclotomic classes in GF(2^12); below-normal, sequential.
cd "$(dirname "$0")"
for args in "12 21 10 all" "12 63 30 frob" "12 105 50 frob" "12 273 130 frob" "12 315 150 frob"; do
  set -- $args
  cmd //c "start /belownormal /wait /b target\release\cyc.exe $1 $2 $3 $4 3000000000 > m6_N$2_t$3_$4.out 2>&1"
done
