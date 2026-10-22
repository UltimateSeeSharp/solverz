# Blueprint

Status: `conjectured` (holds in all computed cases) → `paper proof` → `statement approved` (user) → `formalized` (Lean, `lake build --wfail`, `#print axioms` clean).

| Lemma | Statement (plain terms) | Depends on | Status | Evidence |
|---|---|---|---|---|
| Main conjecture | On {1..N} with 1 + … + N even, optimal play is a draw | (open) | conjectured; Lean statement approved | Every even-total N ≤ 32 ([results/](results/)) |
| Every opening draws | For even-total N ≥ 12, every opening move of player 1 still leads to a draw (implies the main conjecture for those N) | (open) | conjectured | N ≤ 32 ([results/](results/)) |
| Parity law | In any position, the final score difference ≡ gap + sum of the numbers left (mod 2); so a draw needs gap ≡ sum left (mod 2) | none | paper proof | The two players take every remaining number between them: mover's final lead = −gap + (own − other's), and own − other's ≡ own + other's = sum left (mod 2) |
