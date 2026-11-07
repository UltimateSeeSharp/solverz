"""Run all four rules on every row of instances.csv. Resumable.
Usage: python xrun.py <out> <worker> <nworkers>"""
import sys, os, ctypes
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xcommon import rows, parse
from xrules import w_sc, w_a1, w_scpp, w_a2
out, w, nw = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
done = {l.split()[0] for l in open(out, encoding='utf-8')} if os.path.exists(out) else set()
with open(out, 'a', encoding='utf-8') as f:
    for i, r in enumerate(rows()):
        if i % nw != w or r['id'] in done: continue
        v, k, lam, sh = parse(r['key'])
        res = [g(v, k, lam, sh) or '-' for g in (w_sc, w_a1, w_scpp, w_a2)]
        f.write(f"{r['id']} {r['status']} {r['key']} |" + '|'.join(res) + '\n'); f.flush()
