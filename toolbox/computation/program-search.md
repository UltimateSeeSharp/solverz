# Program search and synthesis
Searches over programs that build objects or meet a specification: LLM-evolved programs, CEGIS, library learning, invariant learning.

### T107 FunSearch
`find` `bound` · stage: program-search · signals: finite-field, additive, construction
aka: LLM-guided evolution, priority functions, program skeletons, evaluators, cap sets, cap set lower bound
- What: an LLM evolves the priority function of a fixed skeleton program; an evaluator scores outputs.
- Fits when: constructions definable by short programs.
- Lean: check the output object, not the program.
- Example: a cap set of size 512 in dimension 8, and an asymptotic lower bound of 2.2202, from about 10⁶ LLM samples ([Romera-Paredes et al.](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC10794145/fullTextXML)).
- See also: T93, T108, T109

### T108 AlphaEvolve
`find` `bound` · stage: program-search · signals: geometry, matrix, construction
aka: LLM coding agents, evolutionary program editing, evaluators, matrix multiplication, 4×4 complex matrices in 48 multiplications, kissing numbers, open problems
- What: LLM agents edit whole programs, guided by evaluators.
- Fits when: bound problems with a cheap numeric score.
- Lean: the evaluator should be the same check that Lean will run.
- Example: 4×4 complex matrix multiplication in 48 multiplications ([Novikov et al.](https://arxiv.org/abs/2506.13131)); of 50+ open problems, about 75% matched and 20% improved ([DeepMind](https://deepmind.google/discover/blog/alphaevolve-a-gemini-powered-coding-agent-for-designing-advanced-algorithms/)); 67 problems with Tao et al. ([Georgiev–Gómez-Serrano–Tao–Wagner](https://arxiv.org/abs/2511.02864)).
- See also: T99, T104, T107, T109

### T109 OpenEvolve
`find` `bound` · stage: program-search · signals: geometry, construction
aka: open-source AlphaEvolve, MAP-Elites, islands, OpenAI-compatible endpoint, local LLM, circle packing n=26
- What: an open-source AlphaEvolve with MAP-Elites and islands; it uses any OpenAI-compatible endpoint.
- Fits when: running the AlphaEvolve loop on this PC with a local or API model.
- Lean: as for AlphaEvolve (T108).
- Example: reproduces state-of-the-art circle packing for n=26 ([OpenEvolve](https://github.com/codelion/openevolve)).
- See also: T95, T108

### T110 CEGIS and sketching
`find` `prove` · stage: program-search · signals: logic, construction
aka: counterexample-guided inductive synthesis, program sketching, holes, ∃∀ synthesis, synthesizer-verifier loop
- What: a synthesizer fills holes from a few test inputs; a verifier returns counterexamples, which are added; repeat.
- Fits when: finding a parametrized object or program that satisfies a universal spec.
- Lean: the final object, plus a Lean proof (or `decide`) of the universal spec.
- Example: SAT-based sketch completion for ciphers and concurrent data structures ([Solar-Lezama](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2008/EECS-2008-177.html)); in mathematics, co-certificate learning (T8).
- See also: T8, T9, T112

### T111 Library learning (DreamCoder)
`find` · stage: program-search · signals: construction
aka: DreamCoder, wake-sleep, abstraction learning, program induction, reusable search primitives
- What: wake-sleep alternates growing a library of abstractions with training a search policy.
- Fits when: families of related constructions; reusable search primitives.
- Lean: —
- Example: rediscovered basics of functional programming, vector algebra and physics ([Ellis et al.](https://arxiv.org/abs/2006.08381)).
- See also: T107

### T112 ICE learning of invariants
`prove` · stage: program-search · signals: dynamics, game, computation
aka: inductive invariants, loop invariants, implication counterexamples, safety, never reaches a bad state, invariant synthesis
- What: learns inductive invariants from examples, counterexamples and implications.
- Fits when: proving that a process never reaches a bad state (games, dynamics, loops).
- Lean: prove initiation and preservation for the invariant (`decide`, `omega`, `nlinarith`).
- Example: convergent learners for numerical and quantified invariants ([Garg et al. CAV 2014](https://www.springerprofessional.de/en/ice-a-robust-framework-for-learning-invariants/2198224)).
- See also: T16, T58, T110
