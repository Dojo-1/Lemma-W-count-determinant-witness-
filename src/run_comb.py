"""Proposition Q' (run-comb certificates, P for all n), with cross-checks against Lemma R'.

Let w be a 3-letter word with runs rho_0 rho_1 ... (starts r_0 = 0 < r_1 < ...), letter l_t of rho_t. For m >= 1:
 (i)  for 1 <= t < m the letter outside {l_(t-1), l_t} occurs in w[r_(t+1):];
 (ii) with c = l_(m-1) and {p, q} the other letters, no split s in [r_m, n-2] has
      cnt_p(w[r_m..s]) * cnt_q(w[r_m:]) == cnt_q(w[r_m..s]) * cnt_p(w[r_m:]).
Then in any right comb whose blocks start at every run start, S = {[r_t, n-1] : 1 <= t <= m} is
self-certifying (Lemma R'). If moreover l_(t-1) == l_(t+1) for some 1 <= t <= m with w[r_(t+1)+1:] nonempty,
the left Moufang move x(Y(xC)) -> ((xY)x)C, with x the letters around Y = rho_t, deletes [r_t, n-1] in S:
w has a disconnected class. The same holds for the reversed word.

Run: python src/run_comb.py 9   (coverage; every certificate is re-checked with stable() and the move)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_theorem import Word, interval
from spectra import canon_words
from stable_separators import stable
from block_witness import witness
from certs import moves, letter_term, Theory


def run_starts(w):
    return [0] + [i for i in range(1, len(w)) if w[i] != w[i - 1]]


def qprime(w):
    """Return (m, t) certifying Q' for w, or None."""
    n, L, r = len(w), sorted(set(w)), run_starts(w)
    R, let = len(r), [w[i] for i in run_starts(w)]
    def cnt(i, j): return {c: w[i:j].count(c) for c in L}
    for m in range(1, R):
        if m >= 2:
            t = m - 1
            third = [c for c in L if c not in (let[t - 1], let[t])][0]
            if third not in w[r[t + 1]:]: break          # (i) fails for this and every larger m
        c = let[m - 1]; p, q = [x for x in L if x != c]; T = cnt(r[m], n)
        if any(cnt(r[m], s + 1)[p] * T[q] == cnt(r[m], s + 1)[q] * T[p] for s in range(r[m], n - 1)):
            continue                                        # (ii) fails
        for t in range(1, m + 1):
            if t + 1 < R and let[t - 1] == let[t + 1] and r[t + 1] + 1 <= n - 1:
                return m, t
    return None


def rcomb(units):
    tree = units[-1]
    for u in reversed(units[:-1]): tree = (u, tree)
    return tree


def trees_for(w, t):
    """T0: right comb over letters with the run rho_t as one block; T1: T0 after x(Y(xC)) -> ((xY)x)C."""
    n, r = len(w), run_starts(w)
    a, e = r[t], r[t + 1] - 1                       # Y = w[a..e]; x at a-1 and e+1
    Y = rcomb(list(range(a, e + 1)))
    C = rcomb(list(range(e + 2, n)))
    T0 = rcomb(list(range(0, a - 1)) + [(a - 1, (Y, (e + 1, C)))]) if a - 1 > 0 else (a - 1, (Y, (e + 1, C)))
    T1 = rcomb(list(range(0, a - 1)) + [(((a - 1, Y), e + 1), C)]) if a - 1 > 0 else (((a - 1, Y), e + 1), C)
    return T0, T1


def nodeset(t, acc):
    if isinstance(t, int): return (t, t)
    l = nodeset(t[0], acc); r = nodeset(t[1], acc); s = (l[0], r[1]); acc.add(s); return s


def check(w, th, m, t):
    """S lies inside stable(T0); T0 -> T1 is a left Moufang instance; T1 lacks [r_t, n-1]."""
    n, r = len(w), run_starts(w)
    T0, T1 = trees_for(w, t)
    S = {(r[u], n - 1) for u in range(1, m + 1)}
    if not S <= stable(T0, Word(w), n): return False
    if not any(y == letter_term(T1, w) and path[-1][1][0] == 'moufang_left'
               for y, path in moves(letter_term(T0, w), th)): return False
    b = set(); nodeset(T1, b)
    return (r[t], n - 1) not in b


if __name__ == '__main__':
    th = Theory(list("xyzuvwtrs"))
    for n in range(4, int(sys.argv[1]) + 1):
        tot = cov = both = bad = 0; miss = []
        for w in canon_words(n, 3):
            if interval(w): continue
            tot += 1
            hit = None
            for v in (w, w[::-1]):
                q = qprime(v)
                if q: hit = (v, q); break
            if hit:
                cov += 1
                if not check(hit[0], th, *hit[1]): bad += 1
            if hit or witness(w): both += 1
            else: miss.append(w)
        print(f"n={n}: non-interval 3-letter words {tot}; Q' certificates {cov} ({100*cov/tot:.1f} %), "
              f"cross-check failures {bad}; Theorem B or Q' {both}; neither {miss}", flush=True)
