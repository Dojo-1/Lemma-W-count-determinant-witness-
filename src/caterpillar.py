"""Caterpillar certificates: G3 for all n (Lemma Cat + Proposition E in THEOREM.md).

A non-interval word over three letters has a *run sequence* s (letters of its maximal runs; no two adjacent
equal; three letters; some letter in two runs; R >= 4 runs). A caterpillar for s peels runs off the ends:
'L' (left run), 'R' (right run) or 'D' (both end runs, when they carry the same letter), down to a bottom of
two runs. S = all path nodes except the root.

Lemma Cat (via Lemma R'): S is self-certifying when
  - each S-node J, entered by peeling letter a and left by peeling letter b, has a != b and third(a, b) in
    the next path node;
  - the bottom (runs u, v), entered by a, has a, u, v pairwise distinct.
A Moufang move deleting a node of S exists when there is a 'D' step (middle Moufang), or two consecutive
same-side steps peel runs x, Y with the next run on that side again x (left/right Moufang).

Proposition E: Good(s, e) (a certificate whose root, entered by letter e, also satisfies the S-condition)
holds for every valid s and every e except
  F1: e = s[0] = s[-1];  F2: s[:-1] uses only {e, u} and starts with e;  F2': mirror image.
In particular Good(s, None) always holds. Proof: induction on R (THEOREM.md); bases R = 4, 5 below.

Run: python src/caterpillar.py 12 9
  part 1: base cases R = 4, 5 (exhaustive), and the exact characterisation for 6 <= R <= 12 (sanity);
  part 2: word-level validation n <= 9: S inside stable(T0) (Lemma R'), and the predicted Moufang move.
"""
import sys, itertools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))

LET = 'xyz'


def third(a, b):
    return next(c for c in LET if c not in (a, b))


def valid(s):
    return len(set(s)) == 3 and len(s) > 3 and all(s[i] != s[i + 1] for i in range(len(s) - 1))


def failure(s, e):
    if e is None: return False
    if e == s[0] == s[-1]: return True
    if s[0] == e and len(set(s[:-1])) == 2: return True
    if s[-1] == e and len(set(s[1:])) == 2: return True
    return False


def find_move(s, steps):
    for k, (st, lo, hi) in enumerate(steps):
        if st == 'D': return ('D', k)
    for k in range(len(steps) - 1):
        st, lo, hi = steps[k]; st2, lo2, hi2 = steps[k + 1]
        if st != st2: continue
        nxt = lo2 + 1 if st == 'L' else hi2 - 1
        if s[nxt] != (s[lo] if st == 'L' else s[hi]): continue
        if k + 2 < len(steps) and steps[k + 2][0] != st: continue
        return (st, k)
    return None


def cert(s, entry=None):
    """Caterpillar steps [(step, lo, hi)] for run sequence s with root entry letter `entry`, or None."""
    def dfs(lo, hi, a, steps):
        if hi - lo == 1:
            if a is None or len({a, s[lo], s[hi]}) < 3: return None
            return steps if find_move(s, steps) else None
        opts = [('L', lo + 1, hi, s[lo]), ('R', lo, hi - 1, s[hi])]
        if s[lo] == s[hi] and hi - lo >= 3: opts.append(('D', lo + 1, hi - 1, s[lo]))
        for st, nlo, nhi, b in opts:
            if a is not None and (a == b or third(a, b) not in s[nlo:nhi + 1]): continue
            r = dfs(nlo, nhi, b, steps + [(st, lo, hi)])
            if r: return r
        return None
    return dfs(0, len(s) - 1, entry, [])


def sequences(R):
    for t in itertools.product(LET, repeat=R):
        s = ''.join(t)
        if valid(s): yield s


# ---------------------------------------------------------------- word level
def word_runs(w):
    out, i = [], 0
    while i < len(w):
        j = i
        while j + 1 < len(w) and w[j + 1] == w[i]: j += 1
        out.append((i, j)); i = j + 1
    return out


def rc(ls):
    t = ls[-1]
    for u in reversed(ls[:-1]): t = (u, t)
    return t


def lc(ls):
    t = ls[0]
    for u in ls[1:]: t = (t, u)
    return t


def build(w):
    """T0, S (spans), deleted span predicted by the move, for the caterpillar of w's run sequence."""
    R = word_runs(w); s = ''.join(w[a] for a, _ in R)
    steps = cert(s); mv = find_move(s, steps)
    letters = lambda r: list(range(R[r][0], R[r][1] + 1))
    Ystep = mv[1] + 1 if mv[0] in 'LR' else None
    st, lo, hi = steps[-1]
    blo, bhi = {'L': (lo + 1, hi), 'R': (lo, hi - 1), 'D': (lo + 1, hi - 1)}[st]
    t = lc(letters(blo) + letters(bhi)) if mv[0] == 'R' else rc(letters(blo) + letters(bhi))
    S = {(R[blo][0], R[bhi][1])}
    for k in range(len(steps) - 1, -1, -1):
        st, lo, hi = steps[k]
        if k >= 1: S.add((R[lo][0], R[hi][1]))
        if st == 'L':
            t = (rc(letters(lo)), t) if k == Ystep else rc(letters(lo) + [t])
        elif st == 'R':
            t = (t, lc(letters(hi))) if k == Ystep else lc([t] + letters(hi))
        else:
            Lr, Rr = letters(lo), letters(hi)
            N = (Lr[-1], (t, Rr[0]))
            for x in Rr[1:]: N = (N, x)
            t = rc(Lr[:-1] + [N]) if len(Lr) > 1 else N
    k = mv[1]; _, lo, hi = steps[k]
    nlo, nhi = {'L': (lo + 1, hi), 'R': (lo, hi - 1), 'D': (lo + 1, hi - 1)}[steps[k][0]]
    return t, S, (R[nlo][0], R[nhi][1])


def spans(t, acc):
    if isinstance(t, int): return (t, t)
    a = spans(t[0], acc); b = spans(t[1], acc); sp = (a[0], b[1]); acc.add(sp); return sp


def to_index(term):
    pos = [0]
    def go(x):
        if isinstance(x, str):
            pos[0] += 1; return pos[0] - 1
        return (go(x[0]), go(x[1]))
    return go(term)


if __name__ == '__main__':
    Rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    bad = 0
    for R in range(4, Rmax + 1):
        n = mism = 0
        for s in sequences(R):
            for e in (None, 'x', 'y', 'z'):
                n += 1
                good = cert(s, e) is not None
                if good == failure(s, e): mism += 1
        bad += mism
        tag = 'base case (proof)' if R <= 5 else 'sanity'
        print(f'R={R}: {n} (sequence, entry) pairs, Good <=> not failure violated {mism} [{tag}]', flush=True)
    from verify_theorem import Word, interval
    from spectra import canon_words
    from stable_separators import stable
    from certs import moves, letter_term, Theory
    th = Theory(list("xyzuvwtrs"))
    for n in range(4, nmax + 1):
        tot = ok = 0
        for w in canon_words(n, 3):
            if interval(w): continue
            tot += 1
            T0, S, dead = build(w)
            a = set(); spans(T0, a)
            if not (S <= a and dead in S and S <= stable(T0, Word(w), n)): continue
            for y, path in moves(letter_term(T0, w), th):
                if not path[-1][1][0].startswith('moufang'): continue
                b = set(); spans(to_index(y), b)
                if dead not in b: ok += 1; break
        bad += tot - ok
        print(f'n={n}: non-interval 3-letter words {tot}; caterpillar T0 with S inside stable(T0) and a Moufang '
              f'move deleting the predicted node: {ok}', flush=True)
    sys.exit(1 if bad else 0)
