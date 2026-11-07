# Lean modules not reachable by imports from the library root.
import re, pathlib, sys
root = pathlib.Path(sys.argv[1])
def mod(p): return '.'.join(p.relative_to(root).with_suffix('').parts)
paths = list((root / 'SignedDifferenceSets').rglob('*.lean')) + [root / 'SignedDifferenceSets.lean']
imp = {mod(p): re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', p.read_text(encoding='utf-8'), re.M) for p in paths}
seen, stack = set(), ['SignedDifferenceSets']
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m); stack += [x for x in imp.get(m, []) if x.startswith('SignedDifferenceSets')]
orph = sorted(set(imp) - seen)
print(len(imp), 'modules;', len(orph), 'unreachable:', orph)
