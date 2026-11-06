# Find: setup

Run once by `choose`, on main, with `solve`'s setup.

1. The importer (`solver/import/`) writes `instances.csv` from the source,
   with what the source and the literature already settle; a problem with
   one Instance gets one line.
2. `Valid` in `Statement.lean` takes an Instance's parameters; the goal's
   approval covers it and the rule that turns a key into its Lean statement,
   tested on known Instances.
3. Known objects from the literature (smaller sizes, sibling cases) entered,
   one checked in Lean so `Valid` meets real data.
4. A first engine that reproduces them.
5. The first ideas, among them the search spaces earlier searches used
   first, with what they found.
