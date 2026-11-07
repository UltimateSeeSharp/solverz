"""Own SDS checker: D maps elements of Z_{m1} x ... x Z_{mr} (tuples) to +1/-1 (absent = 0)."""
import itertools
import numpy as np

try:  # below-normal priority (shared machine)
    import ctypes
    k32 = ctypes.windll.kernel32
    k32.SetPriorityClass(k32.GetCurrentProcess(), 0x4000)
except Exception:
    pass


def elements(mods):
    return list(itertools.product(*[range(m) for m in mods]))


def add(a, b, mods):
    return tuple((x + y) % m for x, y, m in zip(a, b, mods))


def check_direct(D, mods, k, lam):
    """Exact check from the definition: |supp| = k and sum_x D(x)D(x+g) = lam for all g != 0."""
    assert all(c in (1, -1) for c in D.values()), "coefficient not +-1"
    assert all(len(x) == len(mods) and all(0 <= xi < m for xi, m in zip(x, mods)) for x in D)
    if len(D) != k:
        return False, f"support {len(D)} != {k}"
    zero = tuple(0 for _ in mods)
    bad = []
    for g in elements(mods):
        if g == zero:
            continue
        s = sum(c * D.get(add(x, g, mods), 0) for x, c in D.items())
        if s != lam:
            bad.append((g, s))
            if len(bad) > 3:
                break
    return (not bad), bad


def check_fft(D, mods, k, lam):
    """Independent: |D^(chi)|^2 = k - lam for chi != 1 and (sum D)^2 = k + lam (v - 1)."""
    a = np.zeros(mods)
    for x, c in D.items():
        a[x] = c
    F = np.fft.fftn(a)
    p = np.abs(F) ** 2
    v = int(np.prod(mods))
    n = k - lam
    ok0 = round(a.sum()) ** 2 == k + lam * (v - 1)
    p.flat[0] = n
    return bool(ok0 and np.allclose(p, n, atol=1e-6)), float(np.max(np.abs(p - n)))


def split(D):
    return sum(1 for c in D.values() if c == 1), sum(1 for c in D.values() if c == -1)
