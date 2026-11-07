"""Do C17 (RcCert.Kills for every r) or C7 (markedcounts.cert) fire on any `exists` row or object? Mirrors Lean's checks."""
import csv, re, os, sys, math, time, glob
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(PF, 'solver'))
import markedcounts as mc

def even_quot(ms, r):
    out = []
    for m in ms:
        if r > 0 and m % 2 == 0: out.append(2); r -= 1
        else: out.append(1)
    return out

def rc_kills(ms, k, lam, r, s, m):
    eq = even_quot(ms, r)
    if not (all(x > 0 for x in ms) and all(mm % d == 0 for d, mm in zip(eq, ms)) and all(2 % d == 0 for d in eq)
            and math.prod(eq) == 2 ** r and r > 0 and m * m == k - lam and s * s == k + lam * (math.prod(ms) - 1)):
        return False
    return all((sp + m * (2 * j + 1 - 2 ** r)) % (2 ** r) != 0 for sp in (s, -s) for j in range(2 ** r))

def c17_fires(ms, k, lam):
    n, S = k - lam, k + lam * (math.prod(ms) - 1)
    if n < 0 or S < 0 or math.isqrt(n) ** 2 != n or math.isqrt(S) ** 2 != S: return None
    m, s = math.isqrt(n), math.isqrt(S)
    R = sum(1 for x in ms if x % 2 == 0)
    return [r for r in range(1, R + 1) if rc_kills(ms, k, lam, r, s, m)]

rows = []
for row in csv.DictReader(open(os.path.join(PF, 'instances.csv'), encoding='utf-8')):
    mt = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', row['key'])
    rows.append((row['id'], int(mt[1]), int(mt[2]), int(mt[3]), [int(x) for x in mt[4].split(',')], row['status'], row['evidence']))
objs = []
for f in glob.glob(os.path.join(PF, 'objects', 'O*.txt')):
    head = open(f, encoding='utf-8').readline()
    objs.append((os.path.basename(f), head.strip()))
ex = [r for r in rows if r[5] == 'exists']
print('exists rows', len(ex))
fired = 0
for r in ex:
    f = c17_fires(r[4], r[2], r[3])
    if f: fired += 1; print('C17 FIRES on exists', r[0], r[1:5], f, r[6][:60])
print('C17 fired on', fired)
# sanity: C17 fires on the 213 rows (r = R)
mode = sys.argv[1] if len(sys.argv) > 1 else 'c17'
if mode == 'c7':
    lim = float(sys.argv[2]) if len(sys.argv) > 2 else 1e9
    t0 = time.time(); n7 = 0
    for r in sorted(ex, key=lambda r: r[1]):
        if time.time() - t0 > lim: print('time limit at v =', r[1]); break
        try:
            c = mc.cert(r[1], r[2], r[3], r[4])
        except Exception as e:
            print('ERR', r[0], e); continue
        if c: n7 += 1; print('C7 FIRES on exists', r[0], r[1:5], c[:5], r[6][:60])
    print('C7 fired on', n7, 'elapsed', round(time.time() - t0))
