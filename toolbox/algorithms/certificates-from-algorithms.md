# Certificates from algorithms
Algorithm-side ways to make outputs checkable or cross-checked: prepared proofs, closed-set certificates, orbit representatives, double generation.

### T1084 Proof-prepared counting (Merlin–Arthur)
`compute` · stage: certify · signals: polynomial, exact-value
aka: Merlin–Arthur proofs, proofs prepared at Camelot, batch evaluation, Reed–Solomon encoding, polynomial-evaluation proofs, Byzantine failures, verifiable counting, k-clique counting
- What: a prover computes a short polynomial-evaluation proof that verifiers check fast and independently.
- Fits when: counting results where verification can be cheaper than recomputation; verification is randomized, so not directly a Lean proof.
- Lean: — (randomized verification does not count; T126)
- Example: verifiable k-clique counting robust to Byzantine failures ([Björklund–Kaski](https://arxiv.org/abs/1602.01295)).
- See also: T125, T126, T1048

### T1085 Closed-set certificates
`prove` · stage: certify · signals: computation, dynamics, regular-structure
aka: regular invariants, finite-automaton certificate, closed under the step relation, inductive invariant, non-halting proof, finite automata reduction, FAR, Coq-BB5, Π1 claims about infinite runs
- What: a finite automaton describes a set of configurations that contains the start, is closed under the step relation and avoids the bad states.
- Fits when: Π1 claims about infinite runs; the checker verifies a hard-coded certificate instead of searching.
- Lean: check the hard-coded automaton's closure with a verified checker run by `decide +kernel` (T120).
- Example: FAR certificates hard-coded in Coq-BB5 ([bbchallenge, HTML](https://arxiv.org/html/2509.12337v1)).
- See also: T37, T112, T120, T1010

### T1086 Orbit-representative verification
`find` `prove` · stage: certify · signals: symmetric, colouring, graph
aka: check orbit representatives only, cliques through vertex 0, circulant colourings, G-invariant objects, symmetry shortens the check, Ramsey lower bounds
- What: checks a G-invariant object only on orbit representatives, e.g. only cliques through vertex 0 for a circulant colouring.
- Fits when: Lean checks of large symmetric objects; the kernel work shrinks by |G|.
- Lean: prove once that invariance reduces the check to representatives, then `decide` the representatives on packed data (T121).
- Example: circle colourings in Ramsey lower bounds ([Exoo–Tatarevic](https://arxiv.org/abs/1504.02403)).
- See also: T27, T91, T121

### T1087 Independent double generation
`compute` · stage: certify · signals: classification, exact-value
aka: two independent programs, cross-checked counts, consistency checks, non-null intermediate family, catalogue verification, R(4,5)=25
- What: generates the same class by two different methods or programs and compares the counts.
- Fits when: every result built on a catalogue; a null result needs a non-null intermediate family to check.
- Lean: — (a cross-check, not a proof; a catalogue still needs T30's cover lemma)
- Example: for R(4,5)=25, McKay–Radziszowski built a family of (4,5,24)-graphs on purpose so that consistency checks were possible ([McKay–Radziszowski](https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf)).
- See also: T30, T83
