"""Known verified SDSs vs SC++, A1, A2: (1) no rule (mine, sc2.verdict, ideator's tier() and m4())
kills their parameters; (2) on every coordinatewise quotient and qualifying p, the actual coset
sums meet every condition the rules assume (class, moments, m_h bookkeeping)."""
import sys, os, math, itertools, collections, ast, ctypes
sys.dont_write_bytecode = True
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
HERE = os.path.dirname(os.path.abspath(__file__))
SCR = "problems/signed-difference-sets/scratch"
sys.path.insert(0, HERE)
from xcommon import primefac, self_conj
from xrules import w_sc, w_a1, w_scpp, w_a2, maxm
import numpy as np
os.chdir(SCR + '/refuter/rule-sc'); sys.path.insert(0, SCR + '/refuter/rule-sc')
import known_sets as K, constructions, sc2
sys.path.insert(0, SCR + '/ideator')
import load as L
from ruleMa import quotients
import ruleM4
src = open(SCR + '/ideator/tiers.py').read()
fn = next(n for n in ast.parse(src).body if isinstance(n, ast.FunctionDef) and n.name == 'tier')
ns = dict(vars(L)); ns['quotients'] = quotients; ns['math'] = math
exec(compile(ast.Module([fn], []), 'tiers.py', 'exec'), ns); tier = ns['tier']
os.chdir(HERE)
stats = collections.Counter(); bad = []
from found_sets import found_sets, found_sets_he
for gen in (K.gordon_sets(), K.project_sets(), constructions.all_sets(), found_sets(), found_sets_he()):
    for name, shape, k, lam, A in gen:
        if not K.is_sds(A, k, lam): continue
        stats['sets'] += 1
        v = math.prod(shape); n = k - lam
        for rname, f in [('mine_SC', w_sc), ('mine_A1', w_a1), ('mine_SCpp', w_scpp), ('mine_A2', w_a2)]:
            w = f(v, k, lam, shape)
            if w: bad.append((name, rname, w))
        if sc2.verdict(v, k, lam, shape): bad.append((name, 'sc2', sc2.verdict(v, k, lam, shape)))
        t = tier(v, k, lam, tuple(shape))
        if t: bad.append((name, 'tiers.tier', t))
        try:
            w = ruleM4.m4(v, k, lam, tuple(shape))
        except Exception as ex:
            w = None; bad.append((name, 'ruleM4 error', repr(ex)))
        if w: bad.append((name, 'ruleM4.m4', w))
        s = math.isqrt(n + lam * v); assert s * s == n + lam * v
        fn_ = primefac(n)
        idx = np.indices(shape).reshape(len(shape), -1); flat = A.reshape(-1)
        for d in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
            h = math.prod(d)
            if h == 1: continue
            m = math.lcm(*d); c = v // h
            red = tuple(idx[i] % d[i] for i in range(len(shape)))
            a = np.zeros(d, dtype=np.int64); np.add.at(a, red, flat)
            mh = np.zeros(d, dtype=np.int64); np.add.at(mh, red, np.abs(flat))
            a = a.reshape(-1); mh = mh.reshape(-1)
            sig = int(a.sum())
            if sig == -s: a = -a
            elif sig != s: bad.append((name, 'sum', d, sig, s)); continue
            Q = n + lam * c
            if int((a * a).sum()) != Q: bad.append((name, 'sumsq', d))
            for p, e in fn_.items():
                if h % p == 0 or not self_conj(p, m): continue
                b = (e + 1) // 2; stats['A1 tests'] += 1
                if any((h * int(x) - s) % p ** b for x in a): bad.append((name, 'A1 class', d, p, e))
                if e < 2: continue
                q = p ** (e // 2); stats['class tests'] += 1; stats['j>=2'] += e >= 4; stats['c=1'] += c == 1
                if any((h * int(x) - s) % q for x in a): bad.append((name, 'class', d, p, e))
                A_ = int(np.abs(a).sum()); M_ = sum(maxm(int(x), c) for x in a)
                if not (A_ <= k <= M_ and (k - A_) % 2 == 0): bad.append((name, 'bookkeeping', d, p))
                if (mh > c).any() or ((mh - a) % 2).any() or (mh < np.abs(a)).any(): bad.append((name, 'm_h', d))
        stats[name[:2]] += 1
print(dict(stats)); print('violations/kills:', len(bad))
for x in bad[:60]: print(x)
