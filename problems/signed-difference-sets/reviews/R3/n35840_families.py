# Which published families/operations could give (361,316,141)? Arithmetic checks.
from fractions import Fraction as F
v, k, lam = 361, 316, 141
print("DS integrality k(k-1)/(v-1) =", F(k*(k-1), v-1))
print("Gordon Prop 2.3 (4n-1,2n,n-2): n =", F(v+1, 4), "; Thm 4.1 (4n-9,2n-1,n-1): n =", F(v+9, 4))
print("order-4 cyclotomic supports a*90+b (b in 0,1):", sorted(a*90+b for a in range(5) for b in (0, 1)))
# PDS conversions D = P -/+ {0}, P symmetric PDS (v, k-1, lamP, mu=lam) with lamP - mu = +-2
for d in (2, -2):
    kp, mu = k-1, lam; lp = mu + d
    print("PDS (%d,%d,%d,%d): k(k-l-1) = %d vs mu(v-k-1) = %d" % (v, kp, lp, mu, kp*(kp-lp-1), mu*(v-kp-1)))
# Order-8 class sizes and sign-shape support sizes
f = (v-1)//8
print("order-8 supports a*45+b containing 316:", [(a, b) for a in range(9) for b in (0, 1) if a*f+b == k])
