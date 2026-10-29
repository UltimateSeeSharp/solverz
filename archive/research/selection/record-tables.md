# Record tables (checked 2026-10-26/27)

Tables where a result is an explicit object that beats a best-known value. Fit: discrete objects with a cheap property check, structured search (groups, lifts, symmetric codes) that also keeps the Lean check cheap, and a table not mined by AI-assisted crowds. "Quiet" means no 2024–2026 record changes and no LLM activity found; the web searches hit a session limit partway, so before starting a table recheck its changelog for the last 90 days, recent arXiv, and the watch lists below.

## Quiet candidates

### Graphs and geometry

| Table | Source | Why quiet | Lean check | Catch |
|---|---|---|---|---|
| Cages: smallest k-regular graph of girth g | [DS16](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS16), [Combinatorics Wiki](http://combinatoricswiki.org/wiki/Tables_and_Results), [KU Leuven data](https://github.com/AGT-Kulak/smallRegGirthGraphs) | Specialists only | Degree and girth by BFS; Cayley graphs and lifts need one BFS | [Exoo et al. 2025](https://arxiv.org/abs/2511.07247) took the easy entries; left e.g. (5,7) 152 vs 108, (6,7) 294 vs 188, (5,10), (5,11), cubic girth 13–20, first bounds for (6,9), (6,10) |
| Degree–diameter variants: bipartite, Cayley, directed, mixed, degree 17–20 | [Combinatorics Wiki](http://combinatoricswiki.org/wiki/The_Degree/Diameter_Problem) (plain HTTP) | Data from 2008–2012 | BFS | Literature check per entry; the general table's AI crowd may spread here |
| Rectilinear crossing number of K_n, n = 29–98 | [Aichholzer](http://www.ist.tugraz.at/aichholzer/research/rp/triangulations/crossing/) (plain HTTP) | Table unchanged since 2015; gaps e.g. n = 50: 84146 vs 84223, n = 75: 450078 vs 450492 | n integer points, O(n⁴) orientation tests, about 10⁷ at n = 100 | V3R1T4S targets K₂₈, HorizonMath K₉₉; halving lines on the same page had a 2025 record |
| (n, r)-arcs in PG(2, q), q = 11–19 (3-dimensional codes over GF(q)) | [Ball's table](https://web.mat.upc.edu/simeon.michael.ball/codebounds.html), [Braun q ≤ 31](https://arxiv.org/abs/2106.05908) | Last entries 2019 and 2021 | At most 381 points by 381 lines | Several putative arcs must be rigid (no symmetry), so local search, not group search |
| Smallest k-chromatic graph of girth g, k = 4 | [Exoo–Goedgebeur 2019](https://dmtcs.episciences.org/5259) | Quiet except n₆(4) | Needs a "not 3-colourable" certificate; about 2·10⁵ nodes at 64 vertices | [Rampone 2026](https://arxiv.org/abs/2608.23652) improved n₆(4) with a Lean-checked certificate; k ≥ 5 too heavy |
| Snarks: smallest-order records | [2406.16618](https://arxiv.org/abs/2406.16618) | One group, theory plus generation | Under 120 vertices; non-3-edge-colourability certificate | Moderate check cost |
| 0/1-polytopes with the most facets, d = 6–10 | [SMAPO](https://comopt.ifi.uni-heidelberg.de/software/SMAPO/general/general.htm), [A028497](https://oeis.org/A028497) | Records from 1997 random search | Each facet inequality on every vertex plus d tight independent vertices: about 10⁶ (d = 8) to 10⁸ (d = 10) | Two asymptotic papers in Aug 2026 may draw attention |
| Cubic acute sets in {0,1}ⁿ, n ≥ 11 | [A089676](https://oeis.org/A089676) | No work since 2018 | All triples, under 10⁶ | Small field |
| Mrs Perkins's quilts beyond the proved range | [A089046](https://oeis.org/A089046), [squaring.net](http://www.squaring.net/quilts/mrs-perkins-quilts.html) | Last changes 2017–2018 | A tiling of a few dozen squares | Recreational |
| Peaceable queens, n = 16–30 | [A250000](https://oeis.org/A250000) | Last bounds 2016–2019 | Trivial | Well-known puzzle; silent attempts likely |
| Orchard planting, 4 per line, n ≥ 21 | [A006065](https://oeis.org/A006065) | Last 2018–2020 | Exact if coordinates are rational | Records may need algebraic coordinates; the integer version is active |

### Codes and designs

| Table | Source | Why quiet | Lean check | Catch |
|---|---|---|---|---|
| Quantum and small-field linear codes | [codetables.de](https://www.codetables.de/) QECC (q = 3..8, n ≤ 100), [EAQECC](https://eaqecc.codetables.de/), linear codes over GF(7), GF(8), GF(9) | Specialists; few AI entries since 2026-09 | Minimum distance by enumeration while min(k, n − k) ≤ about 20 | V3R1T4S opened EAQECC-qutrit claims 2026-10-25 |
| Existence: circulant weighing matrices, relative and signed difference sets; small MOLS | [Gordon's data](https://github.com/dmgordo), [cyclic difference sets](https://dmgordon.org/papers/cds.pdf) | No competition found | Trivial | Many open cases probably do not exist |
| Ternary constant-composition codes, n ≤ 10 | [Svanström–Östergård–Bogdanova](https://research.aalto.fi/en/publications/bounds-and-constructions-for-ternary-constant-composition-codes/) | None found since 2014 | Trivial | Small payoff |
| Steiner systems S(2, k, v), open cases | Handbook of Combinatorial Designs; [Banakh et al. 2026](https://arxiv.org/abs/2604.04975) | Few groups | Pair checks, about 10⁵ | One group closes cases every few months; small v are hard |

### Colourings and additive combinatorics

| Table | Source | Why quiet | Lean check | Catch |
|---|---|---|---|---|
| Weak Schur numbers WS(k), k ≥ 6 | [Ageron et al. 2021](https://arxiv.org/abs/2112.03175), [Rowley 2021](https://arxiv.org/abs/2011.11292) | Nothing since 2021 | Partition of [646] or [2146]: up to about 2·10⁶ pair checks | The same group wrote a ChatGPT-assisted Schur paper in Jul 2026 |
| Postage-stamp / additive h-bases, k ≥ 25 | [Challis–Robinson 2010](https://cs.uwaterloo.ca/journals/JIS/VOL13/Challis/challis6.html), [A001212](https://oeis.org/A001212) | Exact only to k = 24 (2013–14) | Range by dynamic programming, about 10⁷ | No live table, only papers and OEIS |
| Narrow admissible k-tuples H(k) | [Sutherland](https://math.mit.edu/~primegaps/), [A008407](https://oeis.org/A008407) | None since about 2014 | About k·π(k) | Heavily optimized in 2013 (Polymath8); headroom uncertain |
| Off-diagonal van der Waerden w(2; 3, t), t = 31–39 | [AKS 2014](https://arxiv.org/abs/1102.5433) | No new values | 2-colouring of about [1500] | Small headroom; next to a busy area |
| Hales–Jewett / Gallai numbers | [Mouhib 2026](https://arxiv.org/abs/2606.22155) | One fresh paper with big jumps | Only through a symmetric-colouring reduction lemma proved in Lean | Raw colourings far too large |

## Crowded (avoid)

- Graphs: degree–diameter (general), small Ramsey lower bounds, ex(n; {C3, C4}), Zarankiewicz z(m, n; 3, 3), Kobon triangles, unit-distance graphs, queen domination, sorting networks, snake- and coil-in-the-box, Game of Life records.
- Geometry: Friedman's packings, Packomania, Heilbronn, kissing numbers, Tammes and Thomson, Game of Sloanes.
- Codes and designs: Brouwer's A(n, d), constant-weight, ternary, mixed and 5-ary tables, Kéri's covering codes (mined since Aug 2026), covering designs, covering arrays (tables no longer public), DNA GC-content codes, edit-metric codes, Hadamard orders below 2000, Golomb rulers, difference triangle sets.
- Colourings and number theory: Schur S(k), van der Waerden W(r, k), difference bases, merit factor (LABS), covering systems, superpermutations.
- Lists: the AlphaEvolve, EinsteinArena, HorizonMath and FrontierMath problem lists; the Erdős, formal-conjectures and OEIS conjecture collections.

## Watch lists

Who is mining what: [V3R1T4S record tables](https://github.com/elder-plinius/V3R1T4S/blob/main/known-unknowns/record-tables/README.md) and its [other lists](https://github.com/elder-plinius/V3R1T4S/tree/main/known-unknowns), [EinsteinArena](https://einsteinarena.com/), [HorizonMath baselines](https://raw.githubusercontent.com/ewang26/HorizonMath/main/data/baselines.json), [AlphaEvolve problems](https://github.com/google-deepmind/alphaevolve_repository_of_problems), [FrontierMath open problems](https://epoch.ai/frontiermath/open-problems), [Tao's AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems).
