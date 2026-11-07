# For each solved row: is the Lean theorem named in instances.csv defined in a module reachable from the root?
import re, pathlib, sys, csv, collections
P = pathlib.Path(sys.argv[1]); root = P / 'lean'
def mod(p): return '.'.join(p.relative_to(root).with_suffix('').parts)
paths = list((root / 'SignedDifferenceSets').rglob('*.lean')) + [root / 'SignedDifferenceSets.lean']
text = {mod(p): p.read_text(encoding='utf-8') for p in paths}
imp = {m: re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', t, re.M) for m, t in text.items()}
seen, stack = set(), ['SignedDifferenceSets']
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m); stack += [x for x in imp.get(m, []) if x.startswith('SignedDifferenceSets')]
decl = collections.defaultdict(set)  # last name component -> modules
for m, t in text.items():
    for n in re.findall(r'^\s*(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev)\s+(\S+)', t, re.M):
        decl[n.split('.')[-1]].add(m)
rows = list(csv.DictReader(open(P / 'instances.csv', encoding='utf-8')))
bad = collections.Counter(); missing = collections.Counter(); ex = {}
for r in rows:
    if not r['lean'] or not (r['solution'] or r['status'] == 'exists'): continue
    for name in re.split(r'[;, ]+', r['lean'].strip()):
        if not name: continue
        last = name.split('.')[-1]
        prefix = name.rsplit('.', 1)[0].split('.')[1:]  # e.g. ['CosetRows'] or ['Answer','N3']
        mods = {m for m in decl.get(last, set()) if all(x in m.split('.') for x in prefix if not x.startswith('n'))} or decl.get(last, set())
        if not mods: missing[r['solution'] or 'pending'] += 1; ex.setdefault('missing ' + (r['solution'] or 'pending'), (r['id'], name)); continue
        if not (mods & seen): bad[r['solution'] or 'pending'] += 1; ex.setdefault('unreach ' + (r['solution'] or 'pending'), (r['id'], name, sorted(mods)[:2]))
print('unreachable by Z:', dict(bad)); print('name not found by Z:', dict(missing)); print(ex)
