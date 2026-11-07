# Gauss periods of order 8 in GF(361) and PDS tests of class unions (own code).
import cmath, itertools
exec(open("n35840_cyc.py").read().split("# sign shape")[0])  # field, gen, logs, cls
def tr(z):  # absolute trace GF(361)->GF(19): z + z^19
    w = pw(z, 19); return (z[0] + w[0]) % p
cl = {c: [z for z in logs if cls(z) == c] for c in range(8)}
def period(c, a):  # eta_c under additive character psi_a(z) = e(Tr(a z)/19)
    return sum(cmath.exp(2j*cmath.pi*tr(mul(a, z))/p) for z in cl[c])
eta = [period(c, (1, 0)) for c in range(8)]
for c in range(8): print("eta_%d = %.6f %+.6fi" % (c, eta[c].real, eta[c].imag))
print("|eta_i + 2 eta_{i-1}|^2:", [round(abs(eta[i] + 2*eta[(i-1) % 8])**2, 6) for i in range(8)])
print("|eta_i + 2 eta_{i+1}|^2:", [round(abs(eta[i] + 2*eta[(i+1) % 8])**2, 6) for i in range(8)])
# PDS test via character values: a set S (0 excluded, S = -S) is a PDS iff psi(S) takes <= 2 values over nontrivial psi
def charvals(classes):
    return sorted(set((round(sum(eta[(c + s) % 8] for c in classes).real, 6), round(sum(eta[(c + s) % 8] for c in classes).imag, 6)) for s in range(8)))
for k in (1, 2):
    for S in itertools.combinations(range(8), k):
        v = charvals(S)
        if len(v) <= 2: print("union", S, "char values", v)
print("-1 in class", cls(((p-1) % p, 0)))
