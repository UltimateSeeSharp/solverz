#!/bin/sh
# Sequential Lean runs through the lock script; one at a time.
P=problems/signed-difference-sets
O=$P/reviews/R24
for f in reviews/R24/R6Check.lean reviews/R24/R6Control.lean lean/SignedDifferenceSets/SylowTrace.lean lean/SignedDifferenceSets/SylowCheck.lean lean/SignedDifferenceSets/SylowRows.lean; do
  b=$(basename $f .lean)
  sh $P/scratch/lenv-locked.sh refuter-r6 problems/signed-difference-sets/$f > $O/$b.out 2>&1
  echo "EXIT $?" >> $O/$b.out
done
echo alldone > $O/lean6.done
