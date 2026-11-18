"""G3 via Lemma R (rigid separators): for every non-interval word over exactly 3 letters, find a Moufang
move T0 -> T1 and an absolutely rigid interval J in nodes(T0) symmetric-difference nodes(T1).

Lemma R. A node with span J is removed (or created) only by a rotation at its parent with J as the inner
node; that rotation's segment triple is (split of J, adjacent sibling interval). If every such triple has
count-matrix rank 3, no D_N flip touches J, so "J is a node" is constant on D_N-components. A Moufang move
toggling a rigid J therefore joins two different D_N-components -> class disconnected (Lemma W).
Closed form (3 letters): with t = counts(J) and n_s = u_s x t for each split s (u_s = counts of the left
part), J is rigid iff no nonempty right-context prefix count and no nonempty left-context suffix count is
orthogonal to any n_s.  Everything below is exact integer arithmetic; no component search is used.
Run: python src/rigid_separators.py 8
"""
import sys, time
from verify_theorem import Word, interval
from certs import moves, letter_term, Theory
from spectra import trees, canon_words

def nodes(t, acc):
    if isinstance(t, int): return (t, t)
    a = nodes(t[0], acc); b = nodes(t[1], acc); s = (a[0], b[1]); acc.add(s); return s

def rigid(W, i, k, n):
    for s in range(i, k):
        for m in range(k + 1, n):
            if W.rank((i, s), (s + 1, k), (k + 1, m)) <= 2: return False
        for h in range(0, i):
            if W.rank((h, i - 1), (i, s), (s + 1, k)) <= 2: return False
    return True

def certificate(w, th):
    W = Word(w); n = len(w); ts = trees(0, n - 1); lt = {letter_term(t, w): t for t in ts}
    for t in ts:
        for y, path in moves(letter_term(t, w), th):
            if not path[-1][1][0].startswith("moufang") or y not in lt: continue
            a = set(); nodes(t, a); b = set(); nodes(lt[y], b)
            for J in sorted(a ^ b, key=lambda s: s[1] - s[0]):
                if J[1] > J[0] and rigid(W, J[0], J[1], n):
                    return {"move": path[-1][1][0], "J": J, "factor": w[J[0]:J[1] + 1]}
    return None

if __name__ == "__main__":
    th = Theory(list("xyzuvwtrs"))
    for n in range(4, int(sys.argv[1]) + 1):
        t0 = time.time(); tot = ok = 0; miss = []; lens = {}
        for w in canon_words(n, 3):
            if interval(w): continue
            c = certificate(w, th); tot += 1
            if c: ok += 1; lens[len(c["factor"])] = lens.get(len(c["factor"]), 0) + 1
            else: miss.append(w)
        print(f"n={n}: rigid-separator certificates {ok}/{tot}; |J| histogram {dict(sorted(lens.items()))}; misses {miss[:5]} ({time.time()-t0:.0f}s)", flush=True)
        assert not miss
