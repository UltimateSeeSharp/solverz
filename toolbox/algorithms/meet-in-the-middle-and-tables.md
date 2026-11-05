# Meet in the middle, tables and bit tricks
Speed and memory tricks for exhaustive runs: split searches, hashing, precomputed tables, ranking, Bloom filters, bit parallelism.

### T1130 Meet in the middle
`find` `compute` · stage: search · signals: additive, integers
aka: MITM, Horowitz–Sahni, two halves, sort and match, subset sum, O(2^{n/2})
- What: enumerates two halves, sorts them and matches.
- Fits when: sums or compositions of two independent halves; O(2^{n/2}) instead of 2ⁿ.
- Lean: a found solution by `decide`; "none" needs the full search as a certificate.
- Example: Horowitz–Sahni subset sum ([Wikipedia: Subset sum problem](https://en.wikipedia.org/wiki/Subset_sum_problem)).
- See also: T1131, T1132

### T1131 Schroeppel–Shamir space reduction
`find` `compute` · stage: search · signals: additive, integers
aka: space-reduced meet in the middle, four quarters, heaps, half-sums on the fly, O(2^{n/4}) memory, subset sum, out of RAM
- What: splits into four quarters and generates half-sums on the fly with heaps, using O(2^{n/4}) memory.
- Fits when: a meet-in-the-middle run does not fit 32 GB RAM.
- Lean: as for T1130.
- Example: subset sum with about 100 integers ([Wikipedia: Subset sum problem](https://en.wikipedia.org/wiki/Subset_sum_problem)).
- See also: T1130

### T1132 Generalized birthday (k-tree)
`find` · stage: search · signals: additive
aka: Wagner's algorithm, k-list problem, k-tree algorithm, XOR to a target, sum to a target, merging lists, matching partial bits
- What: merges k lists level by level, matching partial bits.
- Fits when: finding k elements that XOR or sum to a target.
- Lean: a found tuple by `decide`.
- Example: [Wagner, A Generalized Birthday Problem](https://people.eecs.berkeley.edu/~daw/papers/genbday.html).
- See also: T1130

### T1133 Transposition tables and Zobrist hashing
`compute` · stage: search
aka: Zobrist hashing, XOR hashing, incremental hashing, transpositions, state cache, dedupe during local search, O(changes) hash updates
- What: caches results of states reached by different paths, with hashes updated by XOR in O(changes).
- Fits when: DFS where transpositions are common; dedupe during local search.
- Lean: —
- Example: Zobrist XOR updates ([Wikipedia: Zobrist hashing](https://en.wikipedia.org/wiki/Zobrist_hashing)).
- See also: T1096, T1137

### T1134 Method of Four Russians
`compute` · stage: search · signals: matrix
aka: precomputed blocks, tabulate all small blocks, block steps, log-factor speedups, Boolean matrix multiplication, transitive closure, edit distance, small alphabets
- What: tabulates all small blocks once, then processes the input in block steps.
- Fits when: Boolean matrix work, DP with small alphabets.
- Lean: —
- Example: log-factor speedups for transitive closure and edit distance ([Wikipedia: Method of Four Russians](https://en.wikipedia.org/wiki/Method_of_Four_Russians)).
- See also: T1138

### T1135 Small jump tables for iterated maps
`compute` · stage: search · signals: integers, dynamics
aka: lookup tables, multi-step jumps, iterating a simple map over a range, Collatz verification, 3x+1, GPU-friendly tables, Barina
- What: precomputes O(N) entries that advance many steps at once, replacing huge tables.
- Fits when: iterating a simple map over a huge range (GPU friendly).
- Lean: prove the jump-table lemma once; ranges of this size do not fit the kernel (T154).
- Example: Collatz convergence checked at 2.2·10¹¹ numbers per second on one RTX 2080 ([Barina 2020](https://fit.vut.cz/research/publication-file/c168171/280316/Barina2020_Article_ConvergenceVerificationOfTheCo.pdf)).
- See also: T152, T154

### T1136 Perfect ranking and unranking
`compute` · stage: search · signals: order, set-family
aka: combinatorial number system, permutation ranking, k-subsets, bijective state indexing, arrays instead of hash sets, index-range splitting, work units, restartable jobs
- What: bijective maps between states and integers, used for arrays instead of hash sets and to give each worker a range of ranks.
- Fits when: dense state spaces (permutations, k-subsets); restartable parallel enumerations.
- Lean: a range split is a covering lemma for the pieces (T122).
- Example: the combinatorial number system ([Wikipedia: Combinatorial number system](https://en.wikipedia.org/wiki/Combinatorial_number_system)); linear-time permutation ranking ([Korf–Schultze](https://ai.dmi.unibas.ch/_files/teaching/fs21/ai/material/ai10-korf-schultze-aaai2005.pdf)).
- See also: T122, T1104, T1101

### T1137 Bloom filters for visited sets
`compute` · stage: search
aka: Bloom filter, probabilistic membership, maybe seen or never seen, false positives, visited sets, duplicate detection beyond RAM, k hash functions
- What: a bit array with k hashes answers "maybe seen" or "never seen"; false positives only, in a fraction of a hash table's memory.
- Fits when: duplicate detection in state spaces larger than RAM, where an occasional wrong prune is acceptable or re-checked.
- Lean: — (a false positive can prune an unseen state, so a search that uses one is not complete)
- Example: [Wikipedia: Bloom filter](https://en.wikipedia.org/wiki/Bloom_filter).
- See also: T1101, T1133

### T1138 Bitsets and SWAR
`compute` `find` · stage: search · signals: graph, set-family
aka: bit-parallel computation, bit slicing, SIMD within a register, popcount, AVX, adjacency rows, clique tests by AND, colouring checks, bitslice DES
- What: packs many booleans per word and runs many instances per instruction.
- Fits when: adjacency rows, clique tests by AND plus popcount, colouring checks; 64× or 256× (AVX) speedups.
- Lean: the same packing speeds up kernel checks (T121).
- Example: bitslice DES (Biham 1997) ([Wikipedia: Bit slicing](https://en.wikipedia.org/wiki/Bit_slicing)).
- See also: T121, T152
