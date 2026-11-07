#!/bin/sh
cd problems/signed-difference-sets/reviews/R32
r() { echo "== $*"; nice -n 10 python eng.py "$@" 2>&1 | grep -v "^ *vec"; }
{
r 3,3,3 3,3,1 17 4 all
r 3,3,3 3,3,1 22 3
r 3,9 3,3 22 3
r 2,4,4 2,2,2 28 12
r 2,4,4 2,2,2 20 4
r 2,2,2,2,2 2,2,2,1,1 28 12
r 2,2,2,4 2,2,2,1 28 12
r 2,2,8 2,2,2 28 12
r 2,16 2,4 28 12
} > runall.out 2>&1
