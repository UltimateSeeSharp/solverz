import sys, pathlib; sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    import i15_check as c
ms, v, k, lam, D = c.read_obj("O40")
x = next(iter(D)); D2 = dict(D); D2[x] = -D2[x]
print("flip one sign:", c.check_set(ms, D2)[1] != {lam})
D3 = dict(D); del D3[x]; print("drop one:", c.check_set(ms, D3)[0] != k)
print("O40 in C125 instead:", c.check_set([125], {(a * 25 + b,): s for (a, b), s in D.items()})[1])
print("O40 in C25xC5 swapped coords lams:", sorted(c.check_set([25, 5], {(b, a % 5): s for (a, b), s in D.items()})[1])[:6])
