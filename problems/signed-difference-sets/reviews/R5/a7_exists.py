"""Run the ideator's own A7 code (mcontract.run, rmax 10, cap 3e5) on every 'exists' Instance; any KILL refutes."""
import sys, os, collections
sys.path.insert(0, '.'); from common import *
os.chdir(IDEA); sys.path.insert(0, IDEA)
import mcontract
out = open(sys.argv[1], 'a'); done = set()
for p in [sys.argv[1]]:
    pass
st = collections.Counter()
for i, key, s_, v, k, lam, sh in instances():
    if s_ != 'exists': continue
    res = mcontract.run(v, k, lam, sh, 10, 300000)
    st[res[0]] += 1; out.write(f"{i} {key} {res}\n"); out.flush()
out.write(f"# {dict(st)}\n")
