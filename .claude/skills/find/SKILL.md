---
name: find
description: Domain model and attack loop for a `find` problem: patterns, runs, objects, facts. Run by "attack <problem>" when the problem's kind is find.
hooks:
  Stop:
    - hooks:
        - type: command
          command: sh "$CLAUDE_PROJECT_DIR/.claude/hooks/never-stop.sh"
---

# Find

## Domain model
- **Problem** (find): does an object with `Valid` exist? Two goals, each a
  Lean statement: `∃ x, Valid x` and its negation, the second stated only
  once the user opens that side.
- **Pattern** (`P1`…): where to look: a restriction on the answer (a
  symmetry, a construction, an extension of a known object). Patterns
  nest; a looser one contains a tighter one.
  Status: `new` → `alive` (being searched) → `found` | `exhausted`.
- **Run** (`R1`…): one search of one pattern by one engine. States its
  scope beforehand; its code first reproduces known objects. Ends
  `found`, `exhausted`, or `inconclusive` (its best near-miss kept).
- **Object** (`O1`…): a candidate answer as a data file: known from the
  literature, a near-miss with its score, or the answer. Counts once Lean
  checks it.
- **Fact** (`F1`…): a statement about every answer (a count, a symmetry
  break, a known theorem, an obstruction). Cuts searches, and is the
  material of a non-existence proof.
  Status: `open` → `refuted` | `proved` → `verified` (Lean).

Relations: a run searches one pattern, uses facts, reads and writes
objects. A verified answer object settles the first goal. An exhausted
run kills its pattern once rechecked and every fact it used is proved; a
refuted fact reopens every pattern it killed. Facts that confine every
answer to exhausted patterns, all checked in Lean, settle the second.

## Files
`templates/find/` adds to `problems/<name>/`:
```
patterns/  _patterns.md (index), P1.md, P2.md, …
runs/      _runs.md (index), R1.md, R2.md, …
objects/   _objects.md (index: source, score, Lean-checked), O1.txt, O2.txt, …
facts/     _facts.md (index), F1.md, F2.md, …
```

## Start
The goal is `∃ x, Valid x`, `Valid` in `Statement.lean`. The researcher
builds the base itself: known objects from the literature (smaller sizes,
sibling cases) entered, one checked in Lean so `Valid` meets real data;
a first engine that reproduces them; the first patterns, those earlier
searches used first, with what they found. The `ideator` comes in when
the researcher has no next pattern of its own; nothing waits on it.

## Loop
1. Pick the most promising step now, in light of `understanding.md`: a
   pattern to run (new ones get their cheapest run first; alive ones a
   bigger run, or a looser pattern around the best near-miss), or a fact
   to work (one that cuts a search, one a run needs proved, or an
   obstruction that failures keep pointing to). Runs go in the
   background; facts are worked meanwhile.
2. A run: its scope stated and its engine validated before it starts
   (it reproduces known objects and rejects broken ones); its best
   near-miss kept as an object. A fact: tested on known objects and
   near-misses, then proved.
3. Before a status changes, the result is checked. Found: the object goes
   into `lean/<Name>/Answer.lean`, generated from its file, and Lean
   checks `Valid` on it. Exhausted: the `refuter` attacks engine and
   scope, a second engine or method rechecks it, and every fact it used
   is proved. A fact proved or refuted: the `refuter` attacks it first
   (CLAUDE.md, Refuter).
4. Record changed statuses with a journal line, and `state.md`;
   `understanding.md` says which answer the evidence favours, and why.
5. A goal verified (one case, for a table problem): it goes under "Needs
   the user" as a proposed Result (CLAUDE.md, Result); the last goal: stop
   and tell the user. Otherwise never stop
   (CLAUDE.md, Attack). When the evidence favours no object, propose
   opening the second goal under "Needs the user"; the search goes on.
