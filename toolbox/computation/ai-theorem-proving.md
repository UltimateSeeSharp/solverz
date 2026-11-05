# AI theorem proving and research assistants
Language models and RL systems that write proofs, statements or literature reviews; their output counts only once Lean checks it.

### T138 AlphaProof
`prove` · stage: lean-tooling
aka: AlphaZero for proofs, RL theorem proving, autoformalized training corpus, test-time RL, IMO 2024, olympiad problems
- What: AlphaZero-style RL that writes Lean proofs, trained on millions of autoformalized problems, with test-time RL on variants.
- Fits when: hard competition-style lemmas, given heavy compute.
- Lean: native Lean proofs; recheck locally.
- Example: three of five non-geometry problems at IMO 2024, silver level together with AlphaGeometry 2 ([Hubert et al.](https://research.google/pubs/olympiad-level-formal-mathematical-reasoning-with-reinforcement-learning/)).
- See also: T141, T144, T146

### T139 AlphaGeometry
`prove` · stage: decide · signals: geometry
aka: Euclidean geometry, auxiliary points, deductive database, algebraic reasoning, synthetic training proofs, IMO geometry
- What: a language model proposes auxiliary points; a symbolic engine (deductive database plus algebraic reasoning) does the deduction; trained on 100M synthetic proofs.
- Fits when: Euclidean geometry.
- Lean: outputs are not Lean proofs; steps would need translation.
- Example: 25 of 30 IMO-level geometry problems ([Trinh et al.](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC10794143/fullTextXML)).
- See also: T138

### T140 Aristotle
`prove` · stage: lean-tooling
aka: Lean proof search service, informal lemma generation, formalization, geometry solver, IMO 2025, Erdős problems
- What: Lean proof search plus informal lemma generation and formalization, plus a geometry solver.
- Fits when: olympiad to research-level lemmas, as a service.
- Lean: Lean output; recheck locally under this repo's rules.
- Example: gold-equivalent at IMO 2025 ([Achim et al.](https://arxiv.org/abs/2510.01346)); Lean-verified full solutions to Erdős problems 205, 397 and 457 ([Tao's wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)).
- See also: T138, T147

### T141 Open neural provers
`prove` · stage: lean-tooling
aka: DeepSeek-Prover-V2, Goedel-Prover-V2, LLM provers, compiler feedback, self-correction, miniF2F, PutnamBench, local inference, quantized models
- What: LLMs fine-tuned with RL for Lean 4 that self-correct from compiler feedback.
- Fits when: offline proof search on this PC; an 8B model fits 8 GB of VRAM only when quantized (estimate).
- Lean: native Lean proofs.
- Example: Goedel-Prover-V2-8B reaches 84.6% on miniF2F at pass@32, and the 32B solves 86 PutnamBench problems at pass@184 ([Goedel-Prover-V2](https://arxiv.org/abs/2508.03613)); DeepSeek-Prover-V2 (671B) reports 88.9% on miniF2F at a much larger pass@ (not re-checked) ([DeepSeek](https://arxiv.org/abs/2504.21801)).
- See also: T142, T144, T145

### T142 Lean Copilot
`prove` · stage: lean-tooling
aka: LLM inference inside Lean, tactic suggestions, goal completion, premise selection, local or cloud models
- What: LLM inference inside Lean, local or cloud; suggests steps, completes goals, selects premises.
- Fits when: a local assistant inside agent loops.
- Lean: native Lean proofs.
- Example: automated 74.2% of proof steps in Mathematics in Lean, against 40.1% for aesop ([Song–Yang–Anandkumar](https://arxiv.org/abs/2404.12534)).
- See also: T141, T143

### T143 Retrieval-augmented proving
`prove` · stage: lean-tooling
aka: LeanDojo, ReProver, premise retrieval, Mathlib retrieval, right lemma over search depth
- What: retrieves premises from the library before each step.
- Fits when: proofs that need the right Mathlib lemma more than search depth.
- Lean: native Lean proofs.
- Example: LeanDojo and ReProver ([arXiv:2306.15626](https://arxiv.org/abs/2306.15626)).
- See also: T133, T135, T142

### T144 Proof-state tree search with a learned value
`prove` · stage: lean-tooling
aka: HyperTree Proof Search, HTPS, AlphaZero-like proof search, proof hypertrees, online training, value model
- What: AlphaZero-like search over proof hypertrees with online training.
- Fits when: local Lean search with a small model on this PC.
- Lean: native Lean proofs.
- Example: HyperTree Proof Search ([arXiv:2205.11491](https://arxiv.org/abs/2205.11491)).
- See also: T138, T141

### T145 Expert iteration over a statement curriculum
`prove` · stage: lean-tooling
aka: expert iteration, curriculum, training on found proofs, graded difficulty, related lemmas
- What: alternates proof search and training on found proofs, ordered by difficulty.
- Fits when: many related lemmas of graded difficulty.
- Lean: native Lean proofs.
- Example: Polu et al. ([arXiv:2202.01344](https://arxiv.org/abs/2202.01344)).
- See also: T141, T144

### T146 Autoformalization of statements
`prove` · stage: lean-tooling
aka: informal to Lean, statement translation, misformalization, statement audit, drafting statements
- What: translates informal statements into Lean, at scale.
- Fits when: drafting statements, which must then be audited.
- Lean: statements type-check but can be wrong; audit plus small-case `decide` tests.
- Example: AlphaProof's training corpus; DeepMind's formal-conjectures ([formal-conjectures](https://github.com/google-deepmind/formal-conjectures)).
- See also: T136, T138, T151

### T147 LLM literature search and triage
`prove` `find` `bound` `compute` · stage: practice
aka: literature review, prior work, existing solutions, Erdős problems, misstated problems, selection bias, GPT-5
- What: finds existing solutions, related results and misstatements before any attack.
- Fits when: the first step for every open problem.
- Lean: — (its output feeds statement audits).
- Example: GPT-5 literature search found existing full solutions to Erdős problems 339, 494, 515, 621 and 645; the same wiki warns about misstated problems and selection bias ([Tao's wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)).
- See also: T81, T140, T146
