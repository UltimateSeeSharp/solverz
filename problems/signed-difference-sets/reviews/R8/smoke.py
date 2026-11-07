import sys, time
sys.path.insert(0, '.')
from xrules import *
from xcommon import *
t = time.time()
for key in ['SDS(80,55,6,[2,40])', 'SDS(37,36,8,[37])', 'SDS(45,37,21,[3,15])', 'SDS(48,27,2,[2,24])',
            'SDS(49,25,7,[49])', 'SDS(20,11,2,[2,10])', 'SDS(7,4,0,[7])', 'SDS(13,9,0,[13])', 'SDS(9,8,-1,[3,3])']:
    v, k, lam, sh = parse(key)
    print(key, w_sc(v, k, lam, sh), w_a1(v, k, lam, sh), w_scpp(v, k, lam, sh), w_a2(v, k, lam, sh))
print(time.time() - t)
