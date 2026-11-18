"""Proposition C: for an interval word, two bracketings lie in the same D_N-component iff they induce the same
shape ((ij)k) / (i(jk)) on every leaf triple i<j<k whose three letters are pairwise distinct.
Run: python src/sigma_complete.py 8   (all interval words with >= 3 letters, n <= 8)
"""
import sys, itertools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from g2_reduction import comp_of
from verify_theorem import interval
from spectra import canon_words


def leaves(t):
    return [t] if isinstance(t, int) else leaves(t[0]) + leaves(t[1])


def shapes(t, out):
    """out[(i,j,k)] = +1 for ((ij)k), -1 for (i(jk)); recorded at the lowest common ancestor."""
    if isinstance(t, int):
        return
    L, R = leaves(t[0]), leaves(t[1])
    for i, j in itertools.combinations(L, 2):
        for k in R: out[(i, j, k)] = 1
    for i in L:
        for j, k in itertools.combinations(R, 2): out[(i, j, k)] = -1
    shapes(t[0], out); shapes(t[1], out)


def sigma(t, w):
    s = {}; shapes(t, s)
    return tuple(sorted((key, v) for key, v in s.items() if len({w[key[0]], w[key[1]], w[key[2]]}) == 3))


def check(nmax):
    bad = 0
    for n in range(3, nmax + 1):
        words = comps = 0
        for k in range(3, n + 1):
            for w in canon_words(n, k):
                if not interval(w): continue
                words += 1; cw = comp_of(w); fib = {}; cs = {}
                for t, c in cw.items():
                    s = sigma(t, w)
                    if cs.setdefault(c, s) != s: bad += 1          # sigma constant on components
                    if fib.setdefault(s, c) != c: bad += 1         # distinct components -> distinct sigma
                comps += len(cs)
        print(f'n={n}: interval words {words}, components {comps}, violations {bad}', flush=True)
    return bad


if __name__ == '__main__':
    sys.exit(1 if check(int(sys.argv[1]) if len(sys.argv) > 1 else 8) else 0)
