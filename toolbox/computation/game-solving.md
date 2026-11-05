# Game solving
Solving finite games by search, and shipping the result as a checkable strategy.

### T113 Retrograde analysis
`compute` `prove` · stage: game-search · signals: game, exact-value
aka: endgame databases, backward induction, tablebases, strongly solved games, checkers, Awari, Syzygy, chess endgames
- What: computes game values backwards from terminal positions.
- Fits when: finite games with small endgames; strongly solving small games.
- Lean: only for tiny games, by structural recursion over the positions.
- Example: checkers' 10-piece database, 3.9·10¹³ positions in 237 GB ([Schaeffer et al.](https://www.cs.mcgill.ca/~dprecup/courses/AI/Materials/checkers_is_solved.pdf)); Awari strongly solved ([Romein–Bal](https://research.vu.nl/en/publications/solving-the-game-of-awari-using-parallel-retrograde-analysis/)); 7-piece chess in 16.7 TiB ([Syzygy](https://www.chessprogramming.org/Syzygy_Bases)).
- See also: T28, T114, T117

### T114 Proof-number search
`prove` · stage: game-search · signals: game
aka: df-pn, PNS, AND/OR trees, proof and disproof numbers, Connect Four, checkers
- What: best-first AND/OR search on proof and disproof numbers.
- Fits when: proving a win, loss or draw with the least work.
- Lean: the result is a strategy tree (T117).
- Example: the manager of the checkers proof; also Connect Four ([PNS](https://www.chessprogramming.org/Proof-Number_Search)).
- See also: T113, T117

### T115 Alpha-beta search from hypothesis positions
`prove` · stage: game-search · signals: game
aka: alpha-beta, weakly solving, Othello, hypothesis positions, minimax search
- What: picks a small set of positions whose values imply the root's, then solves each.
- Fits when: weakly solving mid-size games.
- Lean: —
- Example: Othello is a draw, from 2,587 hypothesis positions and about 1.5·10¹⁸ positions searched ([Takizawa](https://arxiv.org/abs/2310.19387)).
- See also: T114, T117

### T116 Domain pruning
`prove` · stage: game-search · signals: game
aka: inferior cells, virtual connections, decompositions, Hex, connection games, 8×8 Hex openings
- What: game-specific theorems shrink the tree.
- Fits when: connection games and other games with strong local theory.
- Lean: each pruning rule is a lemma to prove once.
- Example: all 8×8 Hex openings solved in about 301 hours on one desktop with 2 GB of RAM ([Henderson–Arneson–Hayward](https://www.ijcai.org/Abstract/09/091)).
- See also: T114

### T117 Strategy trees as certificates
`prove` · stage: certify · signals: game
aka: proof trees, solution trees, winning strategy certificate, recomputed leaves, checkers proof tree
- What: stores only the top of the proof tree and recomputes the leaves.
- Fits when: shipping a game result in checkable form.
- Lean: a strategy tree for a small game is checked by `decide` (all opponent replies covered).
- Example: the checkers proof keeps a tree of about 10⁷ positions and recomputes deeper lines on demand ([Schaeffer et al.](https://www.cs.mcgill.ca/~dprecup/courses/AI/Materials/checkers_is_solved.pdf)).
- See also: T113, T114, T123
