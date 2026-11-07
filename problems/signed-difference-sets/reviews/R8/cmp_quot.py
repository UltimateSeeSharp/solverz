import sys, math
sys.path.insert(0, '.')
from xcommon import rows, parse, quotient_types
sys.path.insert(0, 'problems/signed-difference-sets/scratch/ideator')
import os; os.chdir('problems/signed-difference-sets/scratch/ideator')
from ruleMa import quotients
bad = 0
for r in rows():
    v, k, lam, sh = parse(r['key'])
    a = {(o, math.lcm(*ds)) for ds, o in quotients(sh)}
    b = {t for t in quotient_types(sh) if t[0] > 1}
    if a != b: bad += 1
print('ruleMa.quotients (order, exponent) set mismatches:', bad)
