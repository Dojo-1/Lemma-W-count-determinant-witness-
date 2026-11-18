"""Word associative spectra of Cayley–Dickson algebras (H, O, S) over the associahedron.

For a word w of length n (letters may repeat), each of the C_{n-1} bracketings of w
induces a polynomial function A^k -> A. We compute:
  * the kernel partition (bracketings inducing the same function),
  * s_w(A) = number of classes,
  * flip-connectivity: is each class connected in the flip graph (associahedron 1-skeleton)?
Equality is tested by evaluation at random points of F_P (P = 2^31-1), T independent trials:
  distinctness is CERTIFIED by a witness; equality is randomized (Schwartz–Zippel,
  error <= (n/P)^T per pair).
"""
import itertools, random, sys, json
import numpy as np

P = 2147483647

def conj(x):
    y = (-x) % P
    y[..., 0] = x[..., 0]
    return y

def mul(a, b):
    d = a.shape[-1]
    if d == 1:
        return (a * b) % P
    h = d // 2
    a1, a2, b1, b2 = a[..., :h], a[..., h:], b[..., :h], b[..., h:]
    # Cayley–Dickson: (a1,a2)(b1,b2) = (a1 b1 - conj(b2) a2,  b2 a1 + a2 conj(b1))
    l = (mul(a1, b1) - mul(conj(b2), a2)) % P
    r = (mul(b2, a1) + mul(a2, conj(b1))) % P
    return np.concatenate([l, r], axis=-1)

def trees(i, j, memo={}):
    """All bracketings of positions i..j as nested tuples."""
    if (i, j) in memo: return memo[(i, j)]
    if i == j: res = [i]
    else:
        res = [(L, R) for k in range(i, j) for L in trees(i, k) for R in trees(k + 1, j)]
    memo[(i, j)] = res
    return res

def evaluate_all(n, leaves):
    """leaves: list of arrays (samples, dim) for positions 0..n-1. Returns list of (tree, value)."""
    memo = {}
    def go(i, j):
        if (i, j) in memo: return memo[(i, j)]
        if i == j: out = [(i, leaves[i])]
        else:
            out = []
            for k in range(i, j):
                for tl, vl in go(i, k):
                    for tr, vr in go(k + 1, j):
                        out.append(((tl, tr), mul(vl, vr)))
        memo[(i, j)] = out
        return out
    return go(0, n - 1)

def flips(t):
    """Trees reachable by one rotation ((AB)C) <-> (A(BC)) anywhere inside t."""
    out = []
    if isinstance(t, int): return out
    L, R = t
    if not isinstance(L, int):
        A, B = L; out.append((A, (B, R)))
    if not isinstance(R, int):
        B, C = R; out.append(((L, B), C))
    out += [(x, R) for x in flips(L)]
    out += [(L, x) for x in flips(R)]
    return out

def spectrum(word, dim, T=3, S=4, seed=0):
    rng = np.random.default_rng(seed)
    letters = sorted(set(word))
    n = len(word)
    sig = None
    for trial in range(T):
        vals = {c: rng.integers(0, P, size=(S, dim), dtype=np.int64) for c in letters}
        res = evaluate_all(n, [vals[c] for c in word])
        cur = {t: v.tobytes() for t, v in res}
        if sig is None: sig = {t: [h] for t, h in cur.items()}
        else:
            for t in sig: sig[t].append(cur[t])
    classes = {}
    for t, hs in sig.items(): classes.setdefault(tuple(hs), []).append(t)
    cls = list(classes.values())
    # flip-connectivity of each class
    comp_counts = []
    for c in cls:
        cs = set(c); seen = set(); comps = 0
        for s0 in c:
            if s0 in seen: continue
            comps += 1; stack = [s0]; seen.add(s0)
            while stack:
                x = stack.pop()
                for y in flips(x):
                    if y in cs and y not in seen: seen.add(y); stack.append(y)
        comp_counts.append(comps)
    return {"word": word, "n": n, "catalan": len(sig), "s": len(cls),
            "class_sizes": sorted((len(c) for c in cls), reverse=True),
            "disconnected_classes": sum(1 for k in comp_counts if k > 1),
            "max_components": max(comp_counts), "classes": cls, "comps": comp_counts}

def canon_words(n, k):
    """Restricted growth strings with exactly k letters (set partitions of [n] into k blocks)."""
    out = []
    def rec(w, m):
        if len(w) == n:
            if m == k: out.append("".join("xyzuvwtrs"[c] for c in w))
            return
        for c in range(min(m + 1, k)):
            rec(w + [c], max(m, c + 1))
    rec([], 0)
    return out

def _old_canon_words(n, k):
    """Words of length n over k letters, up to renaming letters (first occurrences in order) using all k letters."""
    out = []
    for w in itertools.product(range(k), repeat=n):
        seen = []
        for c in w:
            if c not in seen: seen.append(c)
        if seen == list(range(k)): out.append("".join("xyzuvwtrs"[c] for c in w))
    return out

def fmt(t, word):
    if isinstance(t, int): return word[t]
    return "(" + fmt(t[0], word) + fmt(t[1], word) + ")"

if __name__ == "__main__":
    for name, dim in (("H", 4), ("O", 8), ("S", 16)):
        for n in range(3, 6 + 1):
            row = []
            for w in ["".join("xyzuvw"[i] for i in range(n))]:
                r = spectrum(w, dim); row.append((w, r["s"], r["catalan"]))
            print(name, n, row)
