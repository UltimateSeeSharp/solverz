# Understanding

**Holds.**
- Data: every even-total N ≤ 32 draws, and from N = 12 every opening draws (E1, E2); N = 35 too, one engine (E3).
- Turns and parity, in Lean: the parity law (C3); at a level position one drawing pick, or two picks after which the opponent cannot win, give a draw (C28, C30). So C1 reduces to one-sided statements, "the player to move does not win" from two starts (C27, C29, C31).
- High sets are solved: every turn is one pick, the rounds game (C13); even blocks draw at height ≥ 2p − 1 (C24, Lean), pair sets above 3·max offset (C21).
- Catch-Up's outcome is the sign of the margin game (C33); the gap bound C37 implies C1, is tight exactly at intervals, and holds on every subset of {1..22} (E17) and ~80 billion refuter positions.
- One-parameter families draw at every height in the data: blocks at real height ≥ 1/2 (C32, p ≤ 8), twins with a tie-break (C62, k ≤ 7); their drawing strategies switch at integer heights (C55, C62).
- Below height 1 the bottom twin pair peels by a mirror (C63, paper proof, refuter pending): C36's fam a for p even reduces to C62 at (p − 1, 3/2).
- Heuristic: drawn play stays low while the set is low, smallest numbers or pairs first (C36, C61 to N = 32, E8).

**Blocks.** The low phase. On high sets (smallest number ≥ the spread) every turn is one pick, and even blocks there draw by a potential argument (C24, in Lean). {1..N} starts low: a turn can take several small numbers to make change, and the value depends on the whole set, not on local features. Every local rule, bounded invariant and single strategy tried for this phase fails as N grows (C42–C46, C49, C54, C55). A proof must control play while the set is low: an invariant the defender keeps while making change, or a reason the value cannot change as the set deforms into a high one. Sharpened (2026-10-28): after any opening of {1..N}, the opponent can make change with the bottom run {1..k} plus one number and leave a block with holes at height up to about √(2N); every route tried (closed families, potentials, deformations crossed breakpoint by breakpoint) fails there (C43, C58, C59). The strongest reformulation is C37: the player to move never loses by more than the largest gap of the numbers left (deficit included), which implies C1 and is tight exactly at intervals.

**So a solution must.**
- Control the low phase for every N: a class of positions the defender keeps, or a value statement like C37, that contains the intervals, where every bound is tight (C37, C59); classes built from reachable positions do not hold as universal statements (C60, C61).
- Or carry the draw down in height from the solved high regime (C21, C24) to height 1, switching strategy at integer heights (C55, C62) across crossings that are not local (C58); C63 does the bottom unit for twins, and above height 1 the opponent's offset-1 answers break a one-round peel (C62).
- Either way it suffices to show that one player does not win from two starts (C31).
