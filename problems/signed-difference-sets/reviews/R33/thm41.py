# Gordon Thm 4.1 at q = 19, r = 25: P = {(x,y): eta(x)eta(y) = 1} + {(0,y): y != 0}, N = {(0,0)} in GF(19) x GF(25).
import numpy as np
sq19 = {(x * x) % 19 for x in range(1, 19)}
eta19 = lambda x: 0 if x == 0 else (1 if x in sq19 else -1)
# GF(25) = F5[i]/(i^2 - 2) (2 is a nonsquare mod 5); element (a, b) = a + b i
def mul(u, w): return ((u[0] * w[0] + 2 * u[1] * w[1]) % 5, (u[0] * w[1] + u[1] * w[0]) % 5)
sq25 = {mul(u, u) for u in [(a, b) for a in range(5) for b in range(5)] if u != (0, 0)}
assert len(sq25) == 12
eta25 = lambda u: 0 if u == (0, 0) else (1 if u in sq25 else -1)
D = np.zeros((19, 5, 5))
for x in range(19):
    for a in range(5):
        for b in range(5):
            if eta19(x) * eta25((a, b)) == 1 or (x == 0 and (a, b) != (0, 0)): D[x, a, b] = 1
D[0, 0, 0] = -1
F = np.fft.fftn(D); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(int).ravel()
print('k =', int(ac[0]), 'off-zero values', sorted(set(ac[1:].tolist())))
