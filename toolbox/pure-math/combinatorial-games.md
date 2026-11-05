# Combinatorial game theory
Existence arguments for winning strategies, positional-game strategies, impartial and partizan game algebra, and periodicity results that turn a game into a finite check; game solving by search is in the computation area.

### T807 Strategy stealing
`prove` · stage: argue · signals: game, impossibility
aka: strategy-stealing argument, first-player win, non-constructive outcomes, Hex, Chomp, Sylver coinage, Hutchings' theorem, poset games, an extra move never hurts
- What: if the second player had a winning strategy, the first could steal it, so the first player wins or draws; the winning move stays unknown.
- Fits when: symmetric games where an extra move never hurts; games on numbers or posets.
- Lean: Mathlib has no combinatorial game theory (no `SetTheory/Game` in v4.35.0); a finite game's winner is checkable by `decide +kernel` on a strategy tree (T117).
- Example: first player wins Hex and Chomp (non-constructively) ([Wikipedia: Strategy-stealing argument](https://en.wikipedia.org/wiki/Strategy-stealing_argument), [Wikipedia: Chomp](https://en.wikipedia.org/wiki/Chomp)); Sylver coinage (Hutchings' theorem) and poset games ([Wikipedia: Sylver coinage](https://en.wikipedia.org/wiki/Sylver_coinage), [Wikipedia: Poset game](https://en.wikipedia.org/wiki/Poset_game)).
- See also: T809, T113, T117, T1030

### T808 Pairing strategies
`prove` · stage: argue · signals: game, set-family, construction
aka: pairing strategy, Maker–Breaker games, blocking every winning set, high-dimensional tic-tac-toe, Hales–Jewett pairing draws
- What: partitions the board into pairs and answers each move with its partner, blocking every winning set.
- Fits when: Maker–Breaker games where each winning line contains a pair.
- Lean: a pairing is finite data; that it meets every winning set is a `decide +kernel` check.
- Example: pairing draws in high-dimensional tic-tac-toe ([Wikipedia: Maker-Breaker game](https://en.wikipedia.org/wiki/Maker-Breaker_game)).
- See also: T810, T430

### T809 Mirror (symmetry) strategy
`prove` · stage: argue · signals: game, symmetric
aka: symmetry strategy, copycat strategy, mirror go, fixed-point-free involution of the board
- What: the second player copies the opponent's move through a symmetry of the board, keeping the position symmetric.
- Fits when: the board has a fixed-point-free symmetry and no move breaks it irreparably.
- Lean: the symmetry and its invariance are finite checks by `decide +kernel`.
- Example: "mirror go" and the limits of strategy stealing in symmetric games ([Wikipedia: Strategy-stealing argument](https://en.wikipedia.org/wiki/Strategy-stealing_argument)).
- See also: T807, T329

### T810 Erdős–Selfridge potential
`prove` · stage: argue · signals: game, set-family, random
aka: Erdős–Selfridge theorem, potential function strategy, weight 2^{-size}, Breaker win, Maker–Breaker, positional games, derandomizing the probabilistic method
- What: weights each unblocked winning set by 2^{−size}; Breaker keeps the total below 1 (as second player, Breaker wins if Σ2^{−|E|} < 1/2).
- Fits when: Maker–Breaker games with few or large winning sets; derandomizing the probabilistic method.
- Lean: the potential inequality for a given hypergraph is exact rational arithmetic (`norm_num`).
- Example: the Erdős–Selfridge theorem ([Wikipedia: Maker-Breaker game](https://en.wikipedia.org/wiki/Maker-Breaker_game), [Wikipedia: Positional game](https://en.wikipedia.org/wiki/Positional_game)).
- See also: T374, T808, T330, T1062

### T811 Matroid strategies
`prove` · stage: argue · signals: game, graph
aka: Shannon switching game, Lehman's theorem, two disjoint spanning trees, matroid union, connection games
- What: a connection game on a graph is won by the player who can secure two disjoint spanning trees.
- Fits when: connection games on graphs.
- Lean: two disjoint spanning trees of a given graph are a finite witness, checked by `decide +kernel`.
- Example: Lehman's solution of the Shannon switching game ([Wikipedia: Shannon switching game](https://en.wikipedia.org/wiki/Shannon_switching_game)).
- See also: T470

### T812 Sprague–Grundy theory
`prove` `compute` · stage: argue · signals: game, integers
aka: Sprague–Grundy theorem, Grundy values, nimbers, mex rule, nim-sum, XOR, impartial games, sums of games, Nim
- What: every impartial game is equivalent to a Nim heap; sums use nim-addition (XOR).
- Fits when: impartial games that decompose into independent components.
- Lean: Grundy values of a finite game by a recursive `mex` computation, checked by `decide +kernel`; Mathlib has no game theory in v4.35.0.
- Example: Nim and its relatives ([Wikipedia: Sprague–Grundy theorem](https://en.wikipedia.org/wiki/Sprague–Grundy_theorem), [Wikipedia: Nim](https://en.wikipedia.org/wiki/Nim), [Wikipedia: Mex](https://en.wikipedia.org/wiki/Mex_%28mathematics%29)).
- See also: T813, T821, T113

### T813 Periodicity theorems for octal and subtraction games
`prove` `compute` · stage: argue · signals: game, sequence, regular-structure
aka: periodicity certificates, Guy–Smith periodicity theorem, octal games, Kayles, subtraction games, eventually periodic Grundy sequences, linear recurrences mod m
- What: if Grundy values repeat for long enough relative to the rules, they are periodic forever; a finite computation then solves the game.
- Fits when: Grundy sequences of octal games; linear recurrences mod m (finite state space, so the period is found and checked).
- Lean: the computed prefix and period by `decide +kernel`, plus a Lean proof of the periodicity theorem for the game class. Skolem–Mahler–Lech does not give such a check: it is ineffective and the Skolem problem is open.
- Example: Kayles' eventually periodic Grundy values; Guy–Smith periodicity theorem ([Wikipedia: Octal game](https://en.wikipedia.org/wiki/Octal_game), [Wikipedia: Kayles](https://en.wikipedia.org/wiki/Kayles), [Wikipedia: Subtraction game](https://en.wikipedia.org/wiki/Subtraction_game)).
- See also: T812, T324, T121

### T814 Conway's canonical forms
`prove` `compute` · stage: argue · signals: game, order
aka: partizan theory, dominated options, reversible options, simplest form, On Numbers and Games, game comparison, guaranteed scoring games
- What: deletes dominated options and bypasses reversible ones to get a unique simplest form.
- Fits when: sums of partizan games; comparing positions.
- Lean: —
- Example: Conway's theory in On Numbers and Games; for guaranteed scoring games four reductions give a unique representative ([Wikipedia: Combinatorial game theory](https://en.wikipedia.org/wiki/Combinatorial_game_theory), [Wikipedia: On Numbers and Games](https://en.wikipedia.org/wiki/On_Numbers_and_Games), [arXiv:1505.07905](https://arxiv.org/abs/1505.07905)).
- See also: T815, T818, T728

### T815 Numbers and the simplicity rule
`compute` · stage: argue · signals: game, exact-value
aka: simplicity rule, surreal numbers, Hackenbush, cold games, number values
- What: a game that is a number is valued as the simplest number between its options.
- Fits when: cold games like Hackenbush.
- Lean: —
- Example: Hackenbush values and surreal numbers ([Wikipedia: Hackenbush](https://en.wikipedia.org/wiki/Hackenbush), [Wikipedia: Surreal number](https://en.wikipedia.org/wiki/Surreal_number)).
- See also: T814, T816

### T816 Temperature theory
`compute` · stage: argue · signals: game
aka: thermographs, cooling, hot games, temperature, play in the hottest component, Go endgames
- What: measures the urgency of hot games; play in the hottest component.
- Fits when: endgames that are sums of hot local fights.
- Lean: —
- Example: in a sum of hot components, moving in the hotter one wins more, as in the Hot game examples; used for Go endgames ([Wikipedia: Hot game](https://en.wikipedia.org/wiki/Hot_game)).
- See also: T815, T818

### T817 Misère quotients
`compute` `prove` · stage: argue · signals: game, group
aka: misère play, misère quotient monoid, Plambeck, indistinguishability, misère Nim
- What: computes the monoid quotient of positions under misère indistinguishability.
- Fits when: misère impartial games where Sprague–Grundy fails.
- Lean: a quotient for one game is finite data whose closure properties `decide +kernel` checks.
- Example: Plambeck's misère quotients ([arXiv:math/0501315](https://arxiv.org/abs/math/0501315), [Wikipedia: Misère](https://en.wikipedia.org/wiki/Misère)).
- See also: T812

### T818 Scoring-game theory
`compute` `prove` · stage: argue · signals: game, order
aka: guaranteed scoring games, scoring play, Go-like scoring, games won by points
- What: extends normal-play theory to games that end with scores.
- Fits when: games won by points, Go-like scoring.
- Lean: —
- Example: guaranteed scoring games ([arXiv:1505.07905](https://arxiv.org/abs/1505.07905)).
- See also: T814, T816

### T819 Parity and chain counting
`prove` · stage: argue · signals: game, parity
aka: long chain rule, tempo moves, control of the last move, Dots and Boxes, chain counting
- What: controls who moves last by counting chains or tempo moves.
- Fits when: Dots and Boxes-type control games.
- Lean: —
- Example: the long chain rule in Dots and Boxes ([Wikipedia: Dots and boxes](https://en.wikipedia.org/wiki/Dots_and_boxes)).
- See also: T332, T812

### T820 Beatty sequences for P-positions
`prove` · stage: argue · signals: game, sequence, integers
aka: Beatty sequences, Rayleigh's theorem, complementary sequences, Wythoff's game, golden ratio, P-positions, two-heap games
- What: characterizes losing positions by complementary Beatty sequences.
- Fits when: two-heap games with diagonal moves.
- Lean: Mathlib: `compl_beattySeq` (Rayleigh's theorem); the game side by hand.
- Example: Wythoff's game and the golden ratio ([Wikipedia: Wythoff's game](https://en.wikipedia.org/wiki/Wythoff's_game)).
- See also: T812, T538

### T821 Nimber arithmetic
`compute` · stage: argue · signals: game, finite-field
aka: nimbers, nim-multiplication, field of characteristic 2, coin-turning games, product games
- What: the field structure of nimbers solves product and coin-turning games.
- Fits when: impartial games with multiplicative structure.
- Lean: nim-sums and nim-products of small values by `decide +kernel`.
- Example: nim-multiplication ([Wikipedia: Nimber](https://en.wikipedia.org/wiki/Nimber)).
- See also: T812

### T822 Strategy construction for infinite pursuit games
`prove` · stage: construct · signals: game, geometry, construction
aka: angel problem, devil traps, potential strategies, infinite-board pursuit, Conway, Máthé, Kloster
- What: an explicit potential or "devil-trap" strategy settles an infinite game.
- Fits when: infinite-board pursuit problems.
- Lean: —
- Example: Conway's angel problem, solved by Máthé and Kloster ([Wikipedia: Angel problem](https://en.wikipedia.org/wiki/Angel_problem)).
- See also: T773, T810
