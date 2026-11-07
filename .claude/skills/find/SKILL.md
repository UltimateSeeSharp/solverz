---
name: find
description: Module find: questions answered by an object (Instances, objects). Loaded by /solve when the problem's README lists it.
---

# Find

The module `find` adds these (`template/` in this folder) to the problem's
files (CLAUDE.md, Files).

| File | What it holds, how it is used |
|---|---|
| `instances.csv` | Its Instances (`N1`…): one question each, its parameters and its source's key and status; its statement is `∃ x, Valid x` for those parameters. Status `open` → `exists` \| `none`, with the evidence that settles it (an object, a claim, or a reference). A problem with one Instance states the `none` side only once the user opens it. Columns: id, key, source (its status there @ snapshot), status, evidence, lean (the theorem), solution (its Solution's ID). Written by the importer (`solver/import/`) and the settle tool, never by hand. |
| `objects/` | Its Objects (`O1`…): one answer as a data file (found, a near-miss with its score, or known from the literature), naming the Instances it answers. Counts once Lean checks `Valid` on it. |
| `corrections.md` | Where the source is wrong or behind: an Instance it lists open that the literature already settles, a stored object that fails `Valid`, a status its evidence does not support. Per entry: Instances, what the source says, what holds, the evidence, when it was sent. Not a Solution: the answer was known, or only the source erred. |
| `lean/<Problem>/Answer/` | `N<id>.lean`: checks one object, or settles one row. A claim that settles many rows lives in its topic file. |

## Settling rows

- An idea here also names the rows it covers; a search space that lies
  inside a looser one says so in its text.
- A search is an experiment over one idea's space and its rows; it uses
  claims, and reads and writes objects.
- `exists`: an object Lean checks, or a construction: a claim, proved in
  Lean, that an object exists for these parameters.
- `none`: a rule: a claim, proved in Lean, that a condition on the
  parameters rules out every object; one theorem and one Lean check over all
  the rows it settles.
- An exhausted search kills its idea for its rows; it settles `none` only
  through a claim Lean checks.
- A refuted claim reopens every row it settled.
- Where the source is wrong or behind, it goes into `corrections.md`;
  sending them goes under "Needs the user" (CLAUDE.md, The user decides:
  sharing outside the repo).

## Loop

Additions to `solve`'s steps:

- **Pick:** aim at what settles many rows: a rule or construction over one
  row at a time. A search earns its place by finding an object, testing a
  rule, or showing the structure a rule could use; a search per row is for
  the rows no rule reaches. New search spaces get their cheapest experiment
  first; alive ones a bigger one, or a looser space around the best
  near-miss. Searches go in the background; claims are worked meanwhile.
- **Work:** a search keeps its best near-miss as an object; a rule or
  construction is first checked against the rows whose answer is already
  known.
- **Check:** a found object goes into `Answer/N<id>.lean`, generated from its
  file, where Lean checks `Valid` on it. An exhausted search: the `refuter`
  attacks engine and scope, a second engine or method rechecks it, and every
  claim it used is proved.
- **Record:** `instances.csv` only through the settle tool.
- **Solved:** every row in scope settled, or the user's scope covered: tell
  the user. A row the source had open, newly settled, is part of a proposed
  Solution: the claim or object that settles it (CLAUDE.md, Files); if the
  literature had already settled it, a correction instead. With one
  Instance: when the evidence favours no object, propose opening the `none`
  side under "Needs the user"; the search goes on.
