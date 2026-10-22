---
name: digest
description: Write the digest of a formalized result (Digest stage) — key idea, where the difficulty was, prior work, follow-up questions — review it, and hand it to the user, who confirms it explains the result. E.g. `/digest catch-up L3`.
---

# Digest a result

Arguments: the problem folder and a blueprint node at `formalized`. Why: `principles/values.md` (what counts as done) `[ICM]`.

1. **Write** `problems/<p>/digest/<node>.md`:
   - the statement in plain terms, and its Lean name;
   - the key idea, then the proof at the level of an expert talk;
   - where the difficulty was, and how it was overcome;
   - prior work and how this differs;
   - follow-up questions the result raises `[Math2]`;
   - AI and tool use `[Leiden]`.
2. **Check proportions**: the key step gets the most space, not the routine lemmas; every claim cites the blueprint node, log entry or source behind it `[Workflows]`.
3. **Review**: run the `refuter` agent in `proof` mode on the write-up's argument and fix what it finds; then read the write-up line by line against the Lean proof's deviation list.
4. **Hand over**: add to "Awaiting review" in `state.md`: the digest, and the question "Does this explain the result to you?". The node moves to `digested` only after the user says yes.
