import sys, glob, math
sys.dont_write_bytecode = True
sys.path.insert(0, '.')
from xcommon import SCR, parse
tiers = {l.split()[0]: int(l.split()[2]) for l in open(SCR + '/ideator/tiers.txt')}
th = {l.split()[0] for l in open(SCR + '/ideator/m4_hits.txt')}
sc2 = {}
for l in open(SCR + '/refuter/rule-sc/sc2_all.out', encoding='utf-8'):
    t = l.split(); sc2[t[0]] = ' '.join(t[3:])
mine = {}
for f in glob.glob('xrun_*.out'):
    for l in open(f, encoding='utf-8'):
        head, *res = l.rstrip('\n').replace('|V|', 'nV').split('|'); mine[head.split()[0]] = (head, res)
ids = [i for i in tiers if tiers[i] == 0 and mine[i][1][3] != '-' and i not in th]
import os; os.chdir(SCR + '/ideator'); sys.path.insert(0, SCR + '/ideator')
import ruleM4
for i in ids:
    head, res = mine[i]; key = head.split()[2]
    print(i, key, '| mine A2:', res[3], '| sc2:', sc2[i], '| ruleM4.m4:', ruleM4.m4(*parse(key)[:3], tuple(parse(key)[3])))
