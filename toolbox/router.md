# Router

The stages an attack of each kind typically passes through, and the families
that hold each stage's entries. All entries of a stage: grep `stage: <stage>`.
The order is typical, not required.

## prove
1. `explore`: what is probably true. computation/experimental-mathematics,
   computation/machine-learning-for-conjectures, other-fields/statistics-of-evidence,
   other-fields/physics-style-methods.
2. `reformulate`: pure-math/proof-strategies, then the families of the problem's signals.
3. `argue`: the pure-math families matching the problem's Object signals (README, Families).
4. `judge`: can the approach reach the goal at all? algorithms/barriers,
   algorithms/reductions-and-hardness, algorithms/proof-complexity.
5. `decide`: statements a prover or decision procedure settles. computation/automated-reasoning.
6. `certify`, `lean-tooling`: computation/certificate-design, computation/lean-automation,
   computation/formal-libraries, computation/ai-theorem-proving.

## find
1. `construct`: pure-math/designs-and-codes, pure-math/extremal-combinatorics,
   pure-math/probabilistic-method, pure-math/discrete-geometry, algorithms/construction-heuristics.
2. `encode`: computation/sat-solving, computation/constraint-solving,
   algorithms/reductions-and-hardness.
3. `symmetry`: algorithms/symmetry-reduction, computation/symmetry-and-generation.
4. `search`: computation/exhaustive-search, computation/sat-solving, algorithms/tree-search,
   algorithms/constraint-propagation, algorithms/meet-in-the-middle-and-tables.
5. `local-search`, `program-search`: computation/local-search, computation/learned-search,
   computation/program-search, algorithms/construction-heuristics.
6. `judge`: will the run fit? computation/hardware-and-scale.
7. `certify`: computation/certificate-design, algorithms/certificates-from-algorithms.

## bound
A better object: as `find`. A better limit:
1. `relax`: computation/semidefinite-and-sos, computation/linear-and-integer-programming,
   algorithms/relaxations-and-decomposition.
2. `argue`: the pure-math families of the problem's signals, e.g.
   pure-math/inequalities-and-estimation, pure-math/extremal-combinatorics.
3. `certify`: exact rational duals. computation/certificate-design.

## compute
1. `generate`: algorithms/generation-and-classification, computation/symmetry-and-generation.
2. `symmetry`: algorithms/symmetry-reduction.
3. `search`, `algebra`, `enclose`: algorithms/counting-and-dynamic-programming,
   algorithms/meet-in-the-middle-and-tables, algorithms/parameterized-algorithms,
   computation/exhaustive-search, computation/computer-algebra,
   computation/number-theoretic-computation, computation/rigorous-numerics.
4. `judge`: before running. computation/hardware-and-scale.
5. `certify`: computation/certificate-design, algorithms/certificates-from-algorithms;
   a second, independent method.

## Every kind
`practice`: other-fields/research-practice, other-fields/effort-allocation,
other-fields/collaboration. Stuck: `stuck.md`.
