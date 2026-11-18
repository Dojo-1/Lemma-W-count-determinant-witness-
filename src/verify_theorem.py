"""Exact (sampling-free) verification of the flip-connectivity characterization for all words of length n.

Proven ingredients (see THEOREM.md):
  L1 context cancellation; W count-determinant witness  =>  in-class flip graph  ⊆  D_N
     (D_N = flips whose segment count matrix has rank <= 2).
  V  vanishing: <=2 letters in abc (Artin), or two of a,b,c powers of one letter (Artin on x and the third).
  I  theta^3 invariant: I_v(T) differs  =>  T, T' are different functions.
  C  certificates: a single axiom move (flexible/alternative/Moufang/Artin) t -> t' proves t ~ t'.
Per word:
  <=2 letters  : one class (Artin)                                                     -> connected
  interval     : every D_N edge satisfies V (=> components inside classes) and the I_v vectors
                 separate D_N components (=> classes = components)                   -> connected
  non-interval : some certified axiom move joins two different D_N components         -> disconnected
Rank computations are exact over Z (fraction-free); I_v uses integer vectors. No randomness.
"""
import sys, itertools, json, time
from collections import deque
from spectra import trees, canon_words
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
from certs import moves, letter_term, Theory

def span(t): return (t, t) if isinstance(t, int) else (span(t[0])[0], span(t[1])[1])

def rank3(rows):
    """exact rank of a 3 x m integer matrix (<=3) via 3x3 / 2x2 minors."""
    m = len(rows[0])
    for c in itertools.combinations(range(m), 3):
        a = [[r[j] for j in c] for r in rows]
        d = (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1]) - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
             + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))
        if d: return 3
    return 2  # (<=2 suffices for our purposes)

class Word:
    def __init__(self, w):
        self.w = w; self.L = sorted(set(w)); self.n = len(w)
        self.pref = {c: [0] for c in self.L}
        for ch in w:
            for c in self.L: self.pref[c].append(self.pref[c][-1] + (ch == c))
        self.rk = {}
    def cnt(self, i, j): return [self.pref[c][j + 1] - self.pref[c][i] for c in self.L]
    def letters(self, i, j): return {c for c in self.L if self.pref[c][j + 1] - self.pref[c][i]}
    def power(self, i, j):
        s = self.letters(i, j); return next(iter(s)) if len(s) == 1 else None
    def rank(self, a, b, c):
        key = (a, b, c)
        if key not in self.rk:
            self.rk[key] = 3 if len(self.L) >= 3 and rank3([self.cnt(*a), self.cnt(*b), self.cnt(*c)]) == 3 else 2
        return self.rk[key]
    def V(self, a, b, c):
        if len(self.letters(a[0], c[1])) <= 2: return True
        p = [self.power(*s) for s in (a, b, c)]
        return any(p[i] is not None and p[i] == p[j] for i, j in ((0, 1), (1, 2), (0, 2)))

def dflips(t, W, out_edges):
    if isinstance(t, int): return
    L, R = t
    if not isinstance(L, int):
        A, B = L; a, b, c = span(A), span(B), span(R)
        if W.rank(a, b, c) <= 2: out_edges.append(((A, (B, R)), (a, b, c)))
    if not isinstance(R, int):
        B, C = R; a, b, c = span(L), span(B), span(C)
        if W.rank(a, b, c) <= 2: out_edges.append((((L, B), C), (a, b, c)))
    sub = []; dflips(L, W, sub); out_edges += [((x, R), s) for x, s in sub]
    sub = []; dflips(R, W, sub); out_edges += [((L, x), s) for x, s in sub]

def shape_signs(t, n):
    """s_T(i,j,k) for i<j<k: +1 if T induces ((ij)k), -1 if (i(jk))."""
    lca = {}
    def rec(t):
        if isinstance(t, int): return [t]
        l, r = rec(t[0]), rec(t[1])
        for i in l:
            for j in r: lca[(i, j)] = id(t)
        return l + r
    rec(t)
    # depth of lca node: ((ij)k) iff lca(i,j) is strictly below lca(i,k)=lca(j,k)
    depth = {}
    def dep(t, d):
        depth[id(t)] = d
        if not isinstance(t, int): dep(t[0], d + 1); dep(t[1], d + 1)
    dep(t, 0)
    return {(i, j, k): (1 if depth[lca[(i, j)]] > depth[lca[(j, k)]] else -1)
            for i, j, k in itertools.combinations(range(n), 3)}

VECS = [{"x": (1, 0, 0), "y": (0, 1, 0), "z": (0, 0, 1), "u": (1, 1, 0), "v": (1, 2, 3), "w": (2, -1, 1), "t": (3, 1, -2), "r": (1, -3, 2), "s": (2, 2, -1)},
        {"x": (2, 1, 0), "y": (1, 3, 1), "z": (0, 1, 4), "u": (5, -1, 2), "v": (1, 1, 1), "w": (-2, 3, 1), "t": (1, 0, -1), "r": (4, 2, -3), "s": (-1, 4, 2)}]
def det3(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))

def I_vector(t, w):
    s = shape_signs(t, len(w))
    return tuple(sum(det3(V[w[i]], V[w[j]], V[w[k]]) * sg for (i, j, k), sg in s.items()) for V in VECS)

import numpy as np
def _cd(a, b):
    d = a.shape[-1]
    if d == 1: return a * b
    h = d // 2; a1, a2, b1, b2 = a[..., :h], a[..., h:], b[..., :h], b[..., h:]
    cj = lambda x: np.concatenate([x[..., :1], -x[..., 1:]], axis=-1)
    return np.concatenate([_cd(a1, b1) - _cd(cj(b2), a2), _cd(b2, a1) + _cd(a2, cj(b1))], axis=-1)
_PTS = np.random.default_rng(11).integers(-3, 4, size=(9, 4, 8)).astype(np.int64)  # letter x point x coord
def int_eval(t, w):
    idx = {c: i for i, c in enumerate("xyzuvwtrs")}
    def ev(t):
        if isinstance(t, int): return _PTS[idx[w[t]]]
        return _cd(ev(t[0]), ev(t[1]))
    return ev(t).tobytes()

def interval(w): return all(w[i] == w[i + 1] or w[i + 1] not in w[:i + 1] for i in range(len(w) - 1))

def verify(w, th):
    W = Word(w); ts = trees(0, len(w) - 1)
    if len(W.L) <= 2: return "connected (Artin)", True
    comp = {}; vio = 0
    for s in ts:
        if s in comp: continue
        comp[s] = s; dq = deque([s])
        while dq:
            x = dq.popleft(); e = []; dflips(x, W, e)
            for y, segs in e:
                if not interval(w) or W.V(*segs): pass
                else: vio += 1
                if y not in comp: comp[y] = s; dq.append(y)
    if interval(w):
        if vio: return f"FAIL: {vio} D_N edges not covered by V", False
        reps = {}
        for t, c in comp.items(): reps.setdefault(c, t)
        Ivals = {}
        for c, t in reps.items():
            Ivals.setdefault(I_vector(t, w), []).append(c)
        if all(len(v) == 1 for v in Ivals.values()):
            return f"connected: {len(reps)} components = classes (theta^3)", True
        # exact integer evaluation witnesses for the remaining ties (rigorous: distinct values => distinct maps)
        for group in Ivals.values():
            if len(group) == 1: continue
            vals = {}
            for c in group:
                vals.setdefault(int_eval(reps[c], w), []).append(c)
            if any(len(v) > 1 for v in vals.values()):
                return "FAIL: components not separated by theta^3 or exact evaluation", False
        return f"connected: {len(reps)} components = classes (theta^3 + exact eval)", True
    # non-interval: find a certified axiom move crossing D_N components
    lt = {letter_term(t, w): t for t in ts}
    for t in ts:
        for y, path in moves(letter_term(t, w), th):
            if y in lt and comp[lt[y]] != comp[t]:
                return f"disconnected: certified move across D_N components", True
    return "FAIL: no certified crossing move found", False

if __name__ == "__main__":
    th = Theory(list("xyzuvwtrs"))
    for n in range(3, int(sys.argv[1]) + 1):
        t0 = time.time(); ok = 0; tot = 0; fails = []
        for k in range(1, n + 1):
            for w in canon_words(n, k):
                msg, good = verify(w, th); tot += 1; ok += good
                if not good: fails.append((w, msg))
        print(f"n={n}: {ok}/{tot} words proved  fails={fails[:4]}  ({time.time()-t0:.0f}s)", flush=True)
