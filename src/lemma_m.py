"""Lemma M (moment formula) and Proposition S (separation) for three-block words x^a y^b z^c.

Substitute x = 1 + s e1, y = 1 + q e2, z = 1 + t e4 into a bracketing T. The coefficient of s^p q t^r is
A_T(p, r) = sum over P (p x's), one y_k, R (r z's) of the signed basis-unit value of T restricted to P+{y_k}+R.

Lemma M:  A_T(p, r) = sigma(w, p, r) * [ j*S_U(p, r) + (b-j)*S_V(p, r) ],  U = x^a' z^c' W,  V = z^c' x^a' W,
where Phi(T) = (j, a', c', W) is the Proposition T invariant and S_w(p, r) is the coefficient of s^p t^r in the
ordered Clifford product P_w = prod (1 + s X)^{run} / (1 + t Z)^{run}, with X^2 = Z^2 = 1, XZ = -ZX.
sigma depends on (w, p, r) only, not on T.

Proposition S: the t-linear and s-linear parts of j P_U + (b-j) P_V determine Phi (interior j) or the join word
(boundary j), so distinct D_N-components of x^a y^b z^c have distinct octonion maps.

Run: python src/lemma_m.py [n_direct] [n_formula]
  part 1 checks Lemma M against direct octonion evaluation on every bracketing, n <= n_direct;
  part 2 decodes Phi from the two linear profiles on every D_N-component, n <= n_direct;
  part 3 checks injectivity of the formula over the full Phi range, a + b + c <= n_formula (no trees needed).
"""
import sys, itertools
from math import comb
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact import IDX, SGN
from g2_reduction import comp_of

UNIT = {'x': 1, 'y': 2, 'z': 4}


def span(t):
    return (t, t) if isinstance(t, int) else (span(t[0])[0], span(t[1])[1])


def invariant(t, a, b, c):
    """Proposition T invariant (j, a', c', W); W read from the core outward."""
    lastx, firstz = a - 1, a + b
    path, node = [], t
    while True:
        L, R = node
        sl, sr = span(L), span(R)
        if sl[0] <= lastx and sl[1] >= firstz:
            path.append(('z', sr[1] - sr[0] + 1)); node = L; continue
        if sr[0] <= lastx and sr[1] >= firstz:
            path.append(('x', sl[1] - sl[0] + 1)); node = R; continue
        break
    L, R = node
    sl, sr = span(L), span(R)
    return (sl[1] - lastx, lastx - sl[0] + 1, sr[1] - firstz + 1, ''.join(s * n for s, n in reversed(path)))


def restrict(t, keep):
    if isinstance(t, int):
        return t if t in keep else None
    l, r = restrict(t[0], keep), restrict(t[1], keep)
    if l is None: return r
    if r is None: return l
    return (l, r)


def ev(t, w):
    if isinstance(t, int):
        return UNIT[w[t]], 1
    i1, s1 = ev(t[0], w); i2, s2 = ev(t[1], w)
    return IDX[i1, i2], s1 * s2 * SGN[i1, i2]


def A_direct(t, w, p, r):
    X = [i for i, ch in enumerate(w) if ch == 'x']; Y = [i for i, ch in enumerate(w) if ch == 'y']
    Z = [i for i, ch in enumerate(w) if ch == 'z']
    tot = {}
    for P in itertools.combinations(X, p):
        for R in itertools.combinations(Z, r):
            for y in Y:
                i, s = ev(restrict(t, set(P) | set(R) | {y}), w)
                tot[i] = tot.get(i, 0) + s
    nz = [v for v in tot.values() if v]
    assert len(nz) <= 1, 'value not on a single unit'
    return nz[0] if nz else 0


def runs(seq):
    out = []
    for ch in seq:
        if out and out[-1][0] == ch: out[-1][1] += 1
        else: out.append([ch, 1])
    return out


def S(seq, p, r):
    """Coefficient of s^p t^r (on X^[p] Z^[r]) in the ordered Clifford product of seq."""
    R = runs(seq); tot = 0
    def rec(i, pp, rr, ks):
        nonlocal tot
        if i == len(R):
            if pp == 0 and rr == 0:
                inv = sum(1 for u in range(len(R)) for v in range(u + 1, len(R))
                          if R[u][0] == 'z' and R[v][0] == 'x' and ks[u] % 2 and ks[v] % 2)
                coef = 1
                for (ch, m), k in zip(R, ks): coef *= comb(m, k)
                tot += coef * (-1) ** inv
            return
        ch, m = R[i]
        for k in range(m + 1):
            if ch == 'x' and k <= pp: rec(i + 1, pp - k, rr, ks + [k])
            if ch == 'z' and k <= rr: rec(i + 1, pp, rr - k, ks + [k])
    rec(0, p, r, [])
    return tot


def F(phi, a, b, c):
    j, ax, cz, W = phi
    U, V = 'x' * ax + 'z' * cz + W, 'z' * cz + 'x' * ax + W
    return tuple(j * S(U, p, r) + (b - j) * S(V, p, r) for p in range(a + 1) for r in range(c + 1))


def profiles(phi, a, b):
    """N(alpha): weighted # z's with alpha x's before; M(gamma): weighted # x's with gamma z's before."""
    j, ax, cz, W = phi
    N, M = {}, {}
    for wt, word in ((j, 'x' * ax + 'z' * cz + W), (b - j, 'z' * cz + 'x' * ax + W)):
        nx = nz = 0
        for ch in word:
            if ch == 'z': N[nx] = N.get(nx, 0) + wt; nz += 1
            else: M[nz] = M.get(nz, 0) + wt; nx += 1
    return ({k: v for k, v in N.items() if v}, {k: v for k, v in M.items() if v})


def word_from_N(N, nx):
    """Binary word from its z-profile (alpha -> count) and its number of x's."""
    out, x = [], 0
    for alpha in sorted(N):
        out.append('x' * (alpha - x) + 'z' * N[alpha]); x = alpha
    return ''.join(out) + 'x' * (nx - x)


def decode(N, M, a, b, c):
    """Proposition S: recover Phi (interior j) or the join word (boundary j) from the profiles."""
    if N.get(0, 0) and M.get(0, 0):
        ax = min(k for k in N if k > 0); cz = min(k for k in M if k > 0)
        j = b - N[0] // cz
        rest = dict(N); rest[0] -= (b - j) * cz; rest[ax] -= j * cz
        NW = {k - ax: v // b for k, v in rest.items() if v}
        return ('interior', j, ax, cz, word_from_N(NW, a - ax))
    side = 'j=0' if N.get(0, 0) else 'j=b'
    return (side, word_from_N({k: v // b for k, v in N.items()}, a))


def check(n_direct, n_formula):
    # parts 1-2: trees
    sig = {}; bad_formula = bad_sign = bad_decode = comps = 0
    for n in range(3, n_direct + 1):
        for a in range(1, n - 1):
            for b in range(1, n - a):
                c = n - a - b; w = 'x' * a + 'y' * b + 'z' * c
                comp = comp_of(w); code_of = {}
                for t, cid in comp.items():
                    phi = invariant(t, a, b, c)
                    if n <= n_direct - 1 or t is next(k for k, v in comp.items() if v == cid):
                        vec = F(phi, a, b, c); k = 0
                        for p in range(a + 1):
                            for r in range(c + 1):
                                d = A_direct(t, w, p, r)
                                if abs(d) != abs(vec[k]): bad_formula += 1
                                elif vec[k] and sig.setdefault((w, p, r), d // vec[k]) != d // vec[k]: bad_sign += 1
                                k += 1
                    code = decode(*profiles(phi, a, b), a, b, c)
                    if code_of.setdefault(cid, code) != code: bad_decode += 1
                if len(set(code_of.values())) != len(code_of): bad_decode += 1
                comps += len(code_of)
        print(f'n={n}: components {comps}, Lemma M mismatches {bad_formula}, sigma inconsistencies {bad_sign}, '
              f'decode failures {bad_decode}', flush=True)
    # part 3: formula-only injectivity over all Phi
    clashes = total = 0
    for n in range(3, n_formula + 1):
        for a in range(1, n - 1):
            for b in range(1, n - a):
                c = n - a - b; seen = {}
                for j in range(b + 1):
                    for ax in range(1, a + 1):
                        for cz in range(1, c + 1):
                            for pos in itertools.combinations(range(a + c - ax - cz), a - ax):
                                W = ''.join('x' if i in pos else 'z' for i in range(a + c - ax - cz))
                                key = F((j, ax, cz, W), a, b, c)
                                code = decode(*profiles((j, ax, cz, W), a, b), a, b, c)
                                if key in seen and seen[key] != code: clashes += 1
                                seen[key] = code
                count = len(seen); total += count
                if count != 1 + b * (comb(a + c, a) - 1): clashes += 1
    print(f'formula range a+b+c <= {n_formula}: {total} distinct maps, clashes/count mismatches {clashes}')
    return bad_formula + bad_sign + bad_decode + clashes


if __name__ == '__main__':
    nd = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    nf = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    sys.exit(1 if check(nd, nf) else 0)
