"""Exact (proof-grade) verification of bracketing equalities in O via full polarization.

For a word w with letter multiplicities m_c, f_T(X,Y,..) is homogeneous of degree m_c in letter c.
f_T1 == f_T2  <=>  Pol(f_T1 - f_T2) == 0  (char 0), where Pol is multilinear in n slots and symmetric
within each letter's slots:  Pol f_T (v_1..v_n) = sum over sigma in prod_c Sym(slots of c) of
T(v_sigma(1),...,v_sigma(n)) with slots permuted only within each letter group.
A multilinear map vanishes iff it vanishes on all basis tuples; basis products are +-basis, so this is
an exact integer computation (no sampling).
"""
import itertools
import numpy as np
from spectra import mul

def table(dim):
    E = np.eye(dim, dtype=np.int64)
    idx = np.zeros((dim, dim), dtype=np.int64); sgn = np.zeros((dim, dim), dtype=np.int64)
    P = 2147483647
    for i in range(dim):
        for j in range(dim):
            p = mul(E[i][None, :], E[j][None, :])[0]
            p = np.where(p > P // 2, p - P, p)
            k = int(np.nonzero(p)[0][0]); idx[i, j] = k; sgn[i, j] = p[k]
            assert abs(p[k]) == 1 and np.count_nonzero(p) == 1
    return idx, sgn

IDX, SGN = table(8)

def evaluate(t, slots):
    """slots: list of index arrays (N,) per position. returns (idx, sign) arrays."""
    if isinstance(t, int): return slots[t], np.ones_like(slots[t])
    li, ls = evaluate(t[0], slots); ri, rs = evaluate(t[1], slots)
    return IDX[li, ri], ls * rs * SGN[li, ri]

def polarized(t, word, dim=8):
    n = len(word)
    grid = np.array(list(itertools.product(range(dim), repeat=n)), dtype=np.int64)  # (dim^n, n)
    groups = {}
    for p, c in enumerate(word): groups.setdefault(c, []).append(p)
    perms_per = [list(itertools.permutations(g)) for g in groups.values()]
    keep = np.ones(len(grid), dtype=bool)
    for g in groups.values():
        for a, b in zip(g, g[1:]): keep &= grid[:, a] <= grid[:, b]
    grid = grid[keep]   # symmetric in each group: sorted representatives suffice
    out = np.zeros((len(grid), dim), dtype=np.int64)
    rows = np.arange(len(grid))
    for combo in itertools.product(*perms_per):
        perm = list(range(n))
        for g, pg in zip(groups.values(), combo):
            for a, b in zip(g, pg): perm[a] = b
        slots = [grid[:, perm[p]] for p in range(n)]
        i, s = evaluate(t, slots)
        np.add.at(out, (rows, i), s)
    return out

def certify_classes(word, classes):
    """True iff every class is exactly equal (all members' polarizations identical)."""
    for c in classes:
        ref = polarized(c[0], word)
        for t in c[1:]:
            if not np.array_equal(ref, polarized(t, word)): return False, (c[0], t)
    return True, None
