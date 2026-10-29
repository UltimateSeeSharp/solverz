# Scepticism

## Red flags in an argument `[Sceptical]` `[Lex]`
- **Too easy.** "Blindfolded in New York, unblindfolded in Beijing, no ocean crossed." Find the error, or the precise reason there isn't one.
- **Proves too much.** Would the same argument prove something known to be false? (A "proof" of Fermat's Last Theorem that never uses n > 2 also proves it for n = 2.)
- **Sudden simplification.** Hard problem → hard problem → suddenly easy: the error is almost certainly at the jump.
- **Drift.** The computation no longer mentions what the problem is about (an RH "proof" that never mentions primes or zeta).
- **A twist on a popular method** that experts supposedly missed.
- **Reformulating forever**, until a restatement is easier because it's wrong.
- **Contradiction from loose computation.** Rerun the argument without the "false" assumption; if it still contradicts, the argument is broken. Prefer converting contradiction proofs into direct ones.
- **A missed case.** Tao's team "solved" a problem, then found they had bounded 12 of 13 terms; the 13th was worse than the other 12 combined and took two more years. List every case and check each.
- **Splitting into harder pieces.** A random decomposition usually makes each piece harder than the whole (a common AI move). Check each piece is really easier. `[Lex]`
- **Look for counterexamples before ambitious claims.** If none exists, the obstruction you hit "identifies the enemy". `[Sceptical]`

## Before believing a claimed result `[Obsess]`
1. What is the key new idea, and how does it differ from earlier attempts?
2. How does it relate to earlier partial results; why did those fall short?
3. What is the simplest new consequence? Which partial result survives if the full claim fails?
4. Why does it avoid the known counterexamples and obstructions?
5. What is the high-level strategy, and why does it work? ("Transform blindly until a miracle occurs" is a bad sign.)
6. What are the milestones (independently interesting intermediate results)?
7. Is it robust, or would one sign error destroy it? Alternate proofs or heuristics add confidence.
8. Have you tried hard to disprove it? There is rarely a rush.
9. Is the novel part given space proportional to its novelty?

## AI-specific `[Lex]` `[Methods]` `[Math20]`
- AI errors look flawless and turn out to be stupid; there is no "code smell". Fluent output is not evidence.
- Don't rely on an AI to correct its own errors; verify externally.
- AI literature search: of six suggested papers maybe one is real and relevant, four invented. Cite only what you opened. `[Lex]`
- Reporting bias: successes are announced, failures aren't. Judge capability with negative results included. `[ICM]`
- Experts reject a wrong proof from its structure ("this would imply something too strong") before finding the line with the error. Models can't do this big-picture check yet, so the refuter must try it explicitly. `[LittA16z]`
- AI-written crank papers now read plausibly: 12 of 13 recent arXiv papers with "Hodge conjecture" in the title were nonsense that took minutes, not seconds, to reject. `[LittEpoch]`
- Judge an AI result like a human one ("if a colleague did this, would I be pleased?"); a grind proof of a real problem is still signal. Novelty shows later, in whether the ideas get reused. `[LittEpoch]`
- Calibrate on length: a huge AI proof of a major result is almost surely wrong; nobody, human or model, has checked it. `[LittA16z]`
- A Lean artifact certifies the Lean statement, not the accompanying informal proof (`lean.md`). `[NSLost]`
