---
name: find
description: Domain model and attack loop for a `find` problem: patterns, experiments, objects, facts. Run by "attack <problem>" when the problem's kind is find.
---

# Find

## Domain model
- **Problem** (find): which of its Instances have an object with `Valid`?
- **Instance** (`N1`…, in `instances.csv`): one question: its parameters
  and its source's key. Two goals, each a Lean statement: `∃ x, Valid x`
  for its parameters, and its negation. A problem with one Instance states
  the second only once the user opens that side; with many, both are open
  from the start. Status: `open` → `exists` | `none`, with the evidence
  (ours, or a reference).
- **Pattern** (`P1`…): where to look: a restriction on the answer (a
  symmetry, a construction, an extension of a known object). Patterns
  nest; a looser one contains a tighter one.
  Status: `new` → `alive` (being searched) → `found` | `exhausted`.
- **Experiment** (CLAUDE.md, Files): here one search of one pattern by one
  engine, over the Instances it names. Ends `found`, `exhausted`, or
  `inconclusive` (its best near-miss kept).
- **Object** (`O1`…): a candidate answer as a data file, naming the
  Instance it answers, if any: known from the literature, a near-miss with
  its score, or the answer. Counts once Lean checks it.
- **Fact** (`F1`…): a statement about every answer, or about the answers
  of the Instances it names (a count, a symmetry break, a known theorem, an
  obstruction). Cuts searches, and is the material of a non-existence
  proof.
  Status: `open` → `refuted` | `proved` → `verified` (Lean).

Relations: an experiment searches one pattern over its Instances, uses facts,
reads and writes objects. A verified answer object settles its Instance's
first goal. An exhausted experiment kills its pattern for its Instances once
rechecked and every fact it used is proved; a refuted fact reopens every
pattern it killed. Facts that confine every answer of an Instance to
exhausted patterns, all checked in Lean, settle its second.

## Files
`templates/find/` adds to `problems/<name>/`:
```
instances.csv  one line per Instance, written by the importer and by tools, never by hand
patterns/  _patterns.md (index), P1.md, P2.md, …
objects/   _objects.md (index: source, score, Lean-checked), O1.txt, O2.txt, …
facts/     _facts.md (index), F1.md, F2.md, …
```
`instances.csv` columns: id (`N1`…); key (the source's); source (its status
there @ snapshot); status (open, exists, none); evidence (our IDs, or a
reference with its witness); lean (the theorem); solution (its Solution's ID,
once approved). Its importer is `solver/import/import.py` (Python, standard
library only); `settle.py` writes our answers, which the importer keeps on
reruns.

## Start
The importer (`solver/import/`) writes `instances.csv` from the source,
with what the source and the literature already settle; a problem with one
Instance gets one line. `Valid` in `Statement.lean` takes an Instance's
parameters; the goal's approval covers it and the rule that turns a key
into its Lean statement, tested on known Instances. Setup builds the base
on main: known objects from the literature (smaller sizes,
sibling cases) entered, one checked in Lean so `Valid` meets real data;
a first engine that reproduces them; the first patterns, those earlier
searches used first, with what they found. The `ideator` comes in when
the researcher has no next pattern of its own; nothing waits on it.

## Loop
1. Pick the most promising step now, in light of `understanding.md`, and
   the Instances it covers: a pattern to search (new ones get their cheapest
   experiment first; alive ones a bigger one, or a looser pattern around the
   best near-miss), or a fact to work (one that cuts a search, one an
   experiment needs proved, or an obstruction that failures keep pointing
   to). Experiments go in the background; facts are worked meanwhile.
2. An experiment: its best near-miss kept as an object. A fact: tested on known objects and
   near-misses, then proved.
3. Before a status changes, the result is checked. Found: the object goes
   into `lean/<Name>/Answer/N<id>.lean` (its Instance), generated from its
   file, and Lean checks `Valid` on it. An Instance settled none: its Lean
   proof goes into the same file. Exhausted: the `refuter` attacks engine and
   scope, a second engine or method rechecks it, and every fact it used
   is proved. A fact proved or refuted: the `refuter` attacks it first
   (CLAUDE.md, Roles).
4. Record changed statuses with a journal line, `instances.csv` (by
   `settle.py`) and `state.md`;
   `understanding.md` says which answer the evidence favours, and why.
5. An Instance settled (Lean-checked): it goes under "Needs the user" as a
   proposed Solution (CLAUDE.md, Files). Every Instance settled, or the
   user's scope covered: stop and tell the user. Otherwise never stop
   (CLAUDE.md, Attack). With one Instance: when the evidence favours no
   object, propose opening the second goal under "Needs the user"; the
   search goes on.
