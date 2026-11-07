import itertools
G=[(a,b) for a in range(3) for b in range(3)]
cnt=0
for f in itertools.product((-1,0,1),repeat=9):
    if sum(1 for x in f if x)!=8: continue
    F=dict(zip(G,f))
    if all(sum(F[x]*F[((x[0]+g[0])%3,(x[1]+g[1])%3)] for x in G)==-1 for g in G if g!=(0,0)): cnt+=1
print('brute SDS(9,8,-1) in C3^2:',cnt)
