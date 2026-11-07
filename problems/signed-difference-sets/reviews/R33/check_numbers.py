# Independent recount of P1's numbers from instances.csv (not importing numbers.py).
import csv, re, sys, collections, math
P = sys.argv[1]
rows = list(csv.DictReader(open(P + '/instances.csv', encoding='utf-8')))
def key(r):
    v, k, l, sh = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[(.*)\]\)", r['key']).groups()
    return int(v), int(k), int(l), tuple(int(x) for x in sh.split(','))
ids = [r['id'] for r in rows]; assert len(set(ids)) == len(ids)
keys = [r['key'] for r in rows]; print('dup keys', len(keys) - len(set(keys)))
op = [r for r in rows if r['source'] == 'Open@e3bf810']
print('rows', len(rows), 'open', len(op))
corr = {'N10864','N12056','N13963','N16190','N18527','N19488','N49190','N67','N73','N49624','N14471'}
hw = [r for r in op if r['evidence'].startswith('He-Wu')]; hwid = {r['id'] for r in hw}
print('He-Wu evidence rows', len(hw), collections.Counter(r['status'] for r in hw))
print('He-Wu rows with solution', sum(bool(r['solution']) for r in hw))
after = [r for r in op if r['id'] not in hwid]
print('open after He-Wu', len(after))
sol = [r for r in after if r['solution']]
print('ours', len(sol), collections.Counter(r['status'] for r in sol))
print('ours outside open', sum(1 for r in rows if r['solution'] and r['source'] != 'Open@e3bf810'))
cr = [r for r in after if r['id'] in corr]; print('corrections in after', len(cr))
rest = [r for r in after if not r['solution'] and r['id'] not in corr]
print('rest', len(rest), collections.Counter(r['status'] for r in rest))
bands = collections.Counter()
for r in rest:
    v = key(r)[0]; bands[0 if v < 50 else 1 if v < 100 else 2 if v < 200 else 3 if v < 500 else 4] += 1
print('bands', sorted(bands.items()))
# Z consistency: each Z all one status
byz = collections.defaultdict(collections.Counter)
for r in sol: byz[r['solution']][r['status']] += 1
print({z: dict(c) for z, c in sorted(byz.items(), key=lambda t: int(t[0][1:]))})
# all solution rows have lean column?
print('solution rows w/o lean', sum(1 for r in sol if not r['lean']))
# s^2 square check on ours none rows
ns = 0
for r in sol:
    v, k, l, sh = key(r); s2 = k + l*(v-1)
    if s2 < 0 or math.isqrt(s2)**2 != s2: ns += 1
print('ours rows with non-square s^2', ns)
# group order matches v
print('shape mismatch', sum(1 for r in rows if math.prod(key(r)[3]) != key(r)[0]))
# Z11 condition
def z11(v,k,l): d=v-k; return v%2==1 and l%2==0 and d*(d-1) < v-1
c11 = collections.Counter(r['solution'] for r in sol if z11(*key(r)[:3]))
print('rows meeting Z11 cond by assigned Z', dict(c11))
print('Z11 rows failing cond', sum(1 for r in sol if r['solution']=='Z11' and not z11(*key(r)[:3])))
print('open rows meeting Z11 cond', sum(1 for r in rest if z11(*key(r)[:3])), 'He-Wu rows meeting', sum(1 for r in hw if z11(*key(r)[:3])))
