"""Exact recheck of the scripts' own kill witnesses: sc2_all.out (SC++) and m4_hits.txt (A2).
Per witness: the triple qualifies (quotient type of G, p not dividing h, p self-conjugate mod m,
p^(2j) | n, c = v/h), V recomputed, feasibility decided exactly (enumeration + 3x3 solve, or the
uncentred min-count DP). Resumable. Usage: python exact_recheck.py <out> <worker> <nworkers>"""
import sys, os, re, time, ctypes, ast, math
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xcommon import parse, primefac, self_conj, quotient_types, s_of, SCR
from xrules import V_of, feas_enum, feas_dp
out, w, nw = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
jobs = []
for l in open(SCR + '/refuter/rule-sc/sc2_all.out', encoding='utf-8'):
    t = l.split()
    if t[3] == 'open' or t[1] != 'open': continue
    kv = dict(x.split('=') for x in t[4:])
    jobs.append(('SC++', t[0], t[2], t[3], int(kv['p']), int(kv['j']), int(kv['h']), int(kv['m']), int(kv['c'])))
for l in open(SCR + '/ideator/m4_hits.txt'):
    i, key, rest = l.split(None, 2)
    ds, p, b, c, nv = ast.literal_eval(rest.strip())
    jobs.append(('A2', i, key, 'A2', p, b, math.prod(ds), math.lcm(*ds), c))
done = set()
if os.path.exists(out):
    done = {tuple(l.split()[:2]) for l in open(out)}
with open(out, 'a') as f:
    for ji, (rule, i, key, label, p, j, h, m, c) in enumerate(jobs):
        if ji % nw != w or (rule, i) in done: continue
        v, k, lam, sh = parse(key); n = k - lam; s = s_of(v, k, lam)
        ok = (h, m) in quotient_types(sh) and h > 1 and h % p != 0 and self_conj(p, m) \
            and n % p ** (2 * j) == 0 and c == v // h
        q = p ** j; V = V_of(c, h, s, q); Q = n + lam * c
        t0 = time.time()
        if len(V) <= 1: res = 'infeasible(|V|<=1)'
        else:
            kk, cc = (k, c) if rule == 'A2' else (None, None)
            r = feas_enum(V, h, s, Q, kk, cc, limit=2 * 10 ** 6) if len(V) <= 8 else None
            how = 'enum'
            if r is None and rule == 'SC++': r = feas_dp(V, h, s, Q); how = 'dp'
            res = {True: f'FEASIBLE({how})', False: f'infeasible({how})', None: 'undecided'}[r]
        f.write(f"{rule} {i} {key} {label} p={p} j={j} h={h} m={m} c={c} |V|={len(V)} qualifies={ok} {res} {time.time() - t0:.2f}s\n"); f.flush()
