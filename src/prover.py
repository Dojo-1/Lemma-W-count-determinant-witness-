"""Derive bracketing equalities in O from classical laws only, and compare with measured classes.

Rules (all valid in the octonions):
  ART  flip ((A B) C) <-> (A (B C)) when A,B,C together involve <= 2 distinct letters (Artin).
  ALT  flip when two of A,B,C are value-equal (associator is alternating).
  MOU  (AB)(CA) = A((BC)A);  ((AB)A)C = A(B(AC));  ((CA)B)A = C(A(BA))   with A's value-equal.
  CONG congruence: equal subterms may be replaced.
Value-equality of subterms is decided recursively by the same procedure on the subword.
"""
from functools import lru_cache
from spectra import trees, flips, spectrum

def shift(t, d):
    return t + d if isinstance(t, int) else (shift(t[0], d), shift(t[1], d))

def span(t):
    if isinstance(t, int): return (t, t)
    return (span(t[0])[0], span(t[1])[1])

def canon(word):
    m = {}; return "".join(m.setdefault(c, "xyzuvwt"[len(m)]) for c in word)

@lru_cache(maxsize=None)
def proven_classes(word):
    """Return dict: relative tree -> class id, for all bracketings of word (positions 0..n-1)."""
    n = len(word)
    ts = trees(0, n - 1)
    if n == 1: return {0: 0}
    parent = {t: t for t in ts}
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a, b):
        a, b = find(a), find(b)
        if a != b: parent[a] = b
    def cls_of(t):
        """class key of a subtree t (absolute positions) inside word, via its subword."""
        i, j = span(t)
        sub = word[i:j + 1]
        cw = canon(sub)
        # relation between letters matters for value-equality across positions: compare raw subword
        return (sub, proven_classes(sub)[shift(t, -i)])
    def veq(a, b):
        return cls_of(a) == cls_of(b)
    def letters(t):
        i, j = span(t); return set(word[i:j + 1])
    # CONG: group by top split + subclasses
    groups = {}
    for t in ts:
        L, R = t; groups.setdefault((span(L)[1], cls_of(L), cls_of(R)), []).append(t)
    for g in groups.values():
        for x in g[1:]: union(g[0], x)
    changed = True
    while changed:
        changed = False
        before = len({find(t) for t in ts})
        for t in ts:
            L, R = t
            # top-level flip ((A B) C) -> (A (B C))
            if not isinstance(L, int):
                A, B = L; C = R
                ok = len(letters(A) | letters(B) | letters(C)) <= 2 or veq(A, B) or veq(B, C) or \
                     (span(A)[1]-span(A)[0] == span(C)[1]-span(C)[0] and veq(A, C))
                if ok: union(t, (A, (B, C)))
            # Moufang patterns
            # (AB)(CA) = A((BC)A)
            if not isinstance(L, int) and not isinstance(R, int):
                A1, B = L; Cc, A2 = R
                if same_len(A1, A2) and veq(A1, A2): union(t, (A1, ((B, Cc), A2)))
            # ((AB)A)C = A(B(AC))
            if not isinstance(L, int) and not isinstance(L[0], int):
                (A1, B), A2 = L; Cc = R
                if same_len(A1, A2) and veq(A1, A2): union(t, (A1, (B, (A2, Cc))))
            # ((CA)B)A = C(A(BA))
            if not isinstance(L, int) and not isinstance(L[0], int):
                (Cc, A1), B = L; A2 = R
                if same_len(A1, A2) and veq(A1, A2): union(t, (Cc, (A1, (B, A2))))
        # CONG again is implicit (subclasses fixed); classes may merge only via rules above
        changed = len({find(t) for t in ts}) != before
    roots = {}; return {t: roots.setdefault(find(t), len(roots)) for t in ts}

def same_len(a, b):
    sa, sb = span(a), span(b); return sa[1] - sa[0] == sb[1] - sb[0]

def compare(word, dim=8):
    pc = proven_classes(word)
    r = spectrum(word, dim, T=2, S=3)
    meas = {}
    for k, c in enumerate(r["classes"]):
        for t in c: meas[t] = k
    # proven equal => measured equal (soundness); measured equal & not proven => unexplained
    pairs_p = {}
    for t, c in pc.items(): pairs_p.setdefault(c, []).append(t)
    sound = all(len({meas[t] for t in g}) == 1 for g in pairs_p.values())
    n_proven = len(pairs_p); n_meas = r["s"]
    return sound, n_proven, n_meas, r
