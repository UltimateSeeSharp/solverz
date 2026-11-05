# Stuck

Situations and where to look; each entry's "Fits when" says more. How others
broke out: `breakthroughs/`, by what unlocked them.

- **The direct problem has no handle:** T1367 move to a neighbour, T300 specialize,
  T301 generalize, T304 reformulate in another domain, T309 finite-field model first.
- **Induction does not close; the hypothesis is too weak:** T302 strengthen the
  induction hypothesis, T335 induction variants, T334 minimal counterexample.
- **Every local rule fails; the answer depends on the whole object:** T1371 solve a
  richer model first, T330 monovariants and potential functions, T112 learning
  invariants from data, T324 reduce to a finite check.
- **An argument fails at one identifiable point:** T1369 root-cause the failure.
- **A tool or construction almost reaches the target:** T1372 tweak a near-miss,
  T1368 accept a weaker tool that fits.
- **Computed bounds match the best construction to many digits:** T1373 look for
  the exact certificate.
- **Data suggests a pattern, unproved:** other-fields/statistics-of-evidence, before
  building on it.
- **Decades of failed proofs; the truth value is in doubt:** T1370 bet on the other
  truth value, T136 property-based counterexample search.
- **Heavy machinery has failed for decades:** T1375 try elementary tools nobody tried.
- **Many strong people failed the same way:** T1011 prove the approach cannot work,
  algorithms/barriers.
- **An iteration has no progress measure:** T330 monovariants, T686 geometric flows
  with monotone quantities.
- **It works except at rare blow-ups:** T686 geometric flows with surgery.
- **Density zero, but a dense theorem exists:** T415 transference.
- **Random constructions stall at a known exponent:** T388 random and algebraic hybrids.
- **A big computer-found object nobody understands:** T123 shrink witnesses and
  certificates.
- **The home toolbox is exhausted:** T304 reformulate in another domain, T1374 bring
  in an outsider, breakthroughs/imported-tool.
- **The same ideas recur without progress:** T1376 step away and return.
- **The search is too big for this machine:** T154 one-PC sizing rule; stages
  `symmetry` and `generate` (`router.md`).
- **A certificate is too big for Lean's kernel:** T1021 certificate-size barrier,
  T123 shrink certificates, computation/certificate-design.
- **Only floating-point evidence:** computation/rigorous-numerics (stage `enclose`).
