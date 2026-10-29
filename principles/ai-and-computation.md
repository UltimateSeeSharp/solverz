# AI and computation

## What AI is good at, and where to check hardest
- Good: literature search (checked), code, routine calculations, checking many
  cases, adapting known proofs, constructions and counterexamples, combining
  techniques from distant areas.
- Check hardest: whether a turn was wrong, whether a subproblem is really
  easier, new techniques for deep conjectures.
- Typical slips: flipped equations, off-by-one, wrong lemma statements.
- Long outputs are beyond its own checking; short ones it can check honestly.
- Results cluster where humans were already close, or few had looked.

## How to use it
- Generate freely; trust only what is checked.
- Small independent pieces beat one long chain.
- Cheap tools first; frontier effort on the hard residue.
- When a proof is a grind, look for the sharper statement that explains it.
- Run the obvious computation before stating a conjecture.
- Delegate and work in parallel; don't wait on single calls.
- Sometimes plain computation beats any model.

## Computation and search
- Survey many cases or a whole family, not single cases.
- Evolve programs that generate candidates, not the candidates; short programs
  find structure and generalize in n.
- The scorer is the hard part and will be exploited: exact arithmetic, every
  side condition checked, solver failures raise errors, winners re-verified.
- Freeze the scorer during a run; a change is a new version.
- Search, cheapest first: local search; a database of good objects plus a
  model that samples new ones (PatternBoost); search over short programs.
- Advice and hints steer a search; compare plans by running each.
- Obfuscate famous problems, or the model recalls instead of searching.
- Numbers to formulas: exact small values, rationalize, spot the pattern, prove.
- Unread scientific code is untrusted; unit-test it against hand-worked cases.
