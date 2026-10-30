# Understanding

**Holds.**
- Data: every even-total N ≤ 32 draws, and from N = 12 every opening draws (E1, E2), as other solvers and von Stengel (to N = 34) found (README); N = 33–35 come from one engine (E3).
- In our Lean: the parity law (C3), the level law and the two-token lemma (C28, C30); C1 needs only the leader's defense from two starts (C27, C29, C31).
- Lean in catch-up-research, not yet in our build: C31 (b) is a ray, V({2..N}, 1) ≠ win iff every Q_N(b) = (I_N ∖ {1, b}, b − 1) is no loss; its top five points b = N, …, N − 4 are no loss for large N (C73) and the rest reduces to interior and boundary cases (C74). Tools: exact-sum blocks (C77), increasing turns suffice for a defender (C78), every opening draws iff every pair is neutral (C75), score shift (C80).
- High and small sets are solved: one pick per turn, the rounds game (C13); even blocks from height 2p − 1 (C24, Lean), pair sets above 3·max offset (C21); two pairs (C11), three pairs at deficit 1 (C76).
- Catch-Up's outcome is the sign of the margin game (C33); the gap bound C37 would imply C1 (data E17).
- Data: density protects, no loss with at most 3 holes (E21, N ≤ 25), near-intervals draw from m = 14 (C4); one-parameter families draw at every height (C32, C62).
- Data: C74's hypotheses hold for N = 11..24, and its interior case is the j = 2 instance of C81, intervals minus j ≤ N/4 adjacent pairs never losing at deficit 1, which holds to N = 28 (losses only with 6–7 numbers left).
- Below height 1 the bottom twin pair peels by a mirror (C63, paper proof, refuter pending).

**Blocks.** The low phase. While the smallest number is below the spread, a turn can take several small numbers to make change, and the value depends on the whole set: every local rule, bounded invariant and single strategy fails as N grows (C42–C46, C49, C54, C55). After any opening the opponent can make change with the bottom run plus one number and leave a block with holes at height up to about √(2N), where closed families, potentials and deformations all fail (C43, C58, C59). The lessons of both attacks: the draw belongs to the whole interval, and arguments that see less lose it, whether they move one hole (C64), use parity or pair structure (C65), keep only the minimum and parity (C66), exclude local reply cycles (C67), lean on small guard numbers (C70) or on summaries (C42). The draw quota is paid across many turns (C72) and cannot be reserved at the first pick (C68). Step-by-step descents stop after a few steps: in the tail length (C71), in height above 1 (C62, C69). Explicit certificates grow exponentially in N (C79).

**So a solution must.**
- Close the middle of C31 (b)'s ray: Q_N(b) no loss between the endpoints (C73), through C74's interior (C81) and boundary cases, by an argument that uses the whole interval (C64–C67) and carries the quota across turns (C72).
- Be symbolic, a strategy or invariant for every N, not a certificate per N (C79).
- Other routes meet the same low phase: a value bound tight at intervals like C37 (C59), or a descent in height from the solved high regime past the integer heights (C55, C62, C69).
