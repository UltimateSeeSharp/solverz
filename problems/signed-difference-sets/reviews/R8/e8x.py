"""E8 cross-check of my SC++, A1, A2 on every (Instance, quotient E8 found a vector on, p).
Any E8 vector meets the class (lemma) and R2's moments, so SC++/A1 must never declare such a
quotient infeasible; A2 may only if the E8 vector breaks k <= sum maxm (not checked by E8)."""
import sys, math, ctypes, collections
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
sys.path.insert(0, '.')
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from xcommon import primefac, self_conj, s_of, SCR, KEY
from xrules import V_of, feas_milp, maxm
def feas_noupper(V, h, s, Q, k, c):
    nv = len(V)
    A = np.array([[1] * nv + [0], list(V) + [0], [x * x for x in V] + [0], [abs(x) for x in V] + [2]], float)
    r = milp(np.zeros(nv + 1), constraints=LinearConstraint(A, [h, s, Q, k], [h, s, Q, k]),
             integrality=np.ones(nv + 1), bounds=Bounds(0, max(h, k) + 1))
    return r.status != 2
st = collections.Counter(); bad = []; a2upper = []
w, nw = int(sys.argv[1]), int(sys.argv[2])
for li, l in enumerate(open(SCR + '/e8/combined.out', encoding='utf-8')):
    if li % nw != w: continue
    t = l.split()
    if len(t) < 4 or t[3] != 'open': continue
    mm = KEY.fullmatch(t[1]); v, k, lam = int(mm[1]), int(mm[2]), int(mm[3]); n = k - lam
    s = s_of(v, k, lam); fac = primefac(n)
    for item in t[4:]:
        H, flag = item.rsplit(':', 1)
        if flag != 'found': continue
        fs = [int(x) for x in H.strip('[]').split(',')]; h, m = math.prod(fs), math.lcm(*fs); c = v // h
        if h == 1: continue
        st['found quotients'] += 1
        for p, e in fac.items():
            if h % p == 0 or not self_conj(p, m): continue
            b = (e + 1) // 2; st['A1 triples'] += 1
            if p ** b > 2 * c: bad.append((t[0], H, p, e, 'A1'))
            if e < 2: continue
            q = p ** (e // 2); Q = n + lam * c; V = V_of(c, h, s, q); st['R triples'] += 1
            if len(V) <= 1: bad.append((t[0], H, p, e, 'R1')); continue
            if feas_milp(V, h, s, Q) is False: bad.append((t[0], H, p, e, 'R2'))
            if len(V) <= 7:
                st['A2 triples'] += 1
                if feas_milp(V, h, s, Q, k, c) is False:
                    if feas_noupper(V, h, s, Q, k, c): a2upper.append((t[0], t[1], H, p))
                    else: bad.append((t[0], H, p, e, 'A2 without upper bound'))
print(dict(st)); print('contradictions:', len(bad), bad[:20])
print('A2 infeasible only via k <= sum maxm on an E8-found quotient:', len(a2upper), a2upper[:20])
