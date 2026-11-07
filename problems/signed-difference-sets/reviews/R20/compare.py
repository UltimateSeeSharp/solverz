import ast, collections
W = "problems/signed-difference-sets/"
mine = {}
for l in open(W + "reviews/R20/my_hits.txt"):
    id_ = l.split()[0]; mine[id_] = l.split(" ", 5)[5] if False else l
st = {}
import csv, re
for r in csv.DictReader(open(W + "instances.csv", newline='', encoding='utf-8')):
    st[r['id']] = (r['status'], r['evidence'])
ide = [l.split()[0] for l in open(W + "scratch/ideator/r2/ma_hits.txt")]
rest = set(l.split()[0] for l in open(W + "scratch/ideator/r2/rest.txt"))
target = set(l.split()[0] for l in open(W + "scratch/ideator/r2/target.txt"))
print("ideator hits", len(ide), "distinct", len(set(ide)))
miss = [i for i in ide if i not in mine]
print("ideator hits NOT in mine:", len(miss), miss[:20])
print("status of ideator hits now:", collections.Counter(st[i][0] for i in ide))
myopen = [i for i in mine if st[i][0] == 'open']
extra = [i for i in myopen if i not in set(ide)]
print("my open hits not in ideator list:", len(extra), "in rest.txt:", sum(i in rest for i in extra), "in target:", sum(i in target for i in extra))
print([i for i in extra if i in rest][:20])
mytarget = [i for i in mine if i in target]; mr = [i for i in mine if i in rest]
print("my hits within rest.txt:", len(mr), " within target:", len(mytarget))
