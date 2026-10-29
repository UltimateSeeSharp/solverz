# Problem solving

## Getting started
- **Cheat strategically.** If 10 things make the problem hard, turn off 9, solve that, swap which one is on; then merge a few at a time. Like a movie fight where the hero faces one attacker at a time. `[Lex]`
- **Toy models.** Strip the problem to its essentials, even if the result no longer models anything real; instructive beats realistic. `[Fut]` `[Sceptical]`
- **Finitize.** Turn "eventually" into "by when?"; finite versions build intuition. `[Lex]`
- **Try anything, even something stupid.** Paralysis ("I've tried nothing and I'm all out of ideas") is the failure mode. A method that's sure to fail is still worth running if *how* it fails is a clue. Failure in math is cheap. `[Lex]` `[Partial]` `[Fut]`
- **Ask dumb questions.** Delete a hypothesis; strengthen the conclusion; prove it with a different method; does X imply Y, is the converse true? `[Dumb]`
- **Think ahead.** Before proving a lemma: how will it be used, which features matter, would a weaker version do, is there a simpler formulation, can a hard-to-verify hypothesis be dropped? `[Ahead]`
- **Keep a list of ~10 favourite problems** and test every new trick you learn against them (Feynman). `[Fut]`
- **Make friends with the object.** Play with a new object: work out examples and special cases; find the smallest case your tools can't handle and attack that until it gives. Or go the other way: take a technique you have and ask which problems it is relevant to. `[LittEpoch]`
- **Motivated moves** (Gowers): every step should come from a standard move, not a rabbit out of a hat: look for an intermediate property; "pretend we've chosen it" (treat the unknown object as a variable and collect the properties it needs); generalize (from a yes/no property to a function with values); try the simplest example (addition before other operations, {0} before other sets); backtrack with what you learned ("we're done unless k is odd"). The chessboard-domino invariant falls out of these moves alone. `[GowersDB]`

## Making progress
- **Value partial progress.** Keeping a partial argument costs nothing. Ask which part a failed method *did* handle; split the problem by regime and use a different tool per piece; the leftover gap shows exactly what still needs a new idea. `[Partial]`
- **Progress is a tree, not a chain.** Keep the partly useful branches, prune the rest; "the door moved a little" is a signal worth following. `[Fut]`
- **Forward reconnaissance.** Assume the one bad case away and check the rest of the argument goes through. If that's the only obstacle, it's worth fighting; if there are several, consider giving up. `[Lex]`
- **Reformulate, decompose, normalize.** Find an equivalent formulation, split the goal into independent properties, use symmetry to remove degrees of freedom, build from simple pieces. `[Jac]`
- **Find the right quantity.** Breakthroughs often come from a quantity that behaves the same at every scale or is conserved (energy, Perelman's entropy); it turns an unmanageable problem into a manageable one. `[Lex]`
- **Get unstuck by switching**, to another problem or a modified one, rather than grinding. Don't obsess prematurely over one big problem; spend most time on feasible ones. `[Lex]` `[Obsess]` `[Waste]`

## Obstructions and structure
- **Counterexamples to nearby problems rule out methods.** Tao built a modified Navier–Stokes that does blow up, proving that any regularity proof must use something his modified equation lacks. Record such obstructions; they save the most time. `[Lex]` `[Sceptical]`
- **Robustness test.** Change the input slightly (delete a few primes, swap one number): if the property dies, any proof must use a delicate feature; if it survives, a broader statement may be true and easier. `[Lex]`
- **Structure vs randomness.** Show the object is either structured or random-like and handle both cases. `[Lex]`
- **Know your tools' limits.** Keep a library of counterexamples and model cases; know which obstructions each tool can handle; if a tool works like a magic wand, study it until you could do without it. `[Limits]`
- **Random models.** Number theorists predict by listing every known property of an object, building a random object with those properties, and asking what holds with probability 1 (Cohen–Lenstra). A cheap way to guess which way a conjecture goes. Expert credence about truth is only a little better than chance; views flip (elliptic curve ranks). `[LittEpoch]`
- **Let a predictor point to the features that matter.** In knot theory, a network predicted the signature from 20 hyperbolic invariants; checking which inputs it was sensitive to left 3, plotting those suggested inequalities (the first ones were false), and the right one was then proved by hand. `[MAP]`
- **How big problems usually fall:** toy cases solved → the method turns out to need property P → counterexamples where P fails → methods borrowed from other fields → reduction to a key conjecture → a special case → cascade. `[Sceptical]`

## After solving
- **Play with the solution**: remove hypotheses, strengthen conclusions, explain it to someone; if you can't explain it, you don't understand it. `[Solving]`
- **Explore the neighbourhood**: which conclusions survive when hypotheses change? **Ablation**: can it be proved without a key input? `[Math2]`
- **Use the wastebasket.** Shrink or shelve what doesn't work, but keep failed work privately and record mistakes. `[Waste]`
