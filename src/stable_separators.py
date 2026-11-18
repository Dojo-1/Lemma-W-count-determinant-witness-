"""Lemma R' (stable-node separators): a sound, local certificate that two bracketings lie in different
D_N-components, strictly stronger than Lemma R (absolute rigidity).

For a bracketing T, call a set S of internal nodes of T *self-certifying* if, for every J in S and every
rotation that would delete J -- children L, R of J and a sibling I such that L, R, I and J+I are laminar
with S, and the node created by the rotation is laminar with S - {J} -- the segment triple has count-matrix
rank 3. Then every tree in the D_N-component of T contains S (consider the first tree on a D_N path that
loses an element of S). Self-certification is monotone, so the union of all self-certifying sets, the
greatest fixpoint `stable(T)`, is self-certifying. A Moufang move T -> T' with stable(T) not inside nodes(T')
joins two different D_N-components; with Lemma W the class is disconnected.

Run: python src/stable_separators.py 8              (every non-interval 3-letter word, 4 <= n <= 8)
     python src/stable_separators.py words w1 w2 ... (certify given words, e.g. the G3-R counterexamples)
"""
import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_theorem import Word, interval
from certs import moves, letter_term, Theory
from spectra import trees, canon_words
from rigid_separators import nodes
def lam(A,B): return A[1]<B[0] or B[1]<A[0] or (A[0]<=B[0] and B[1]<=A[1]) or (B[0]<=A[0] and A[1]<=B[1])
def stable(t,W,n):
    """Greatest self-certifying set of internal nodes of t (constant on its D_N-component)."""
    S=set();nodes(t,S);S={J for J in S if J[1]>J[0] and J!=(0,n-1)}
    root=(0,n-1)
    def ok(J,S):
        i,k=J;rest=S-{J}
        for s in range(i,k):
            L,R=(i,s),(s+1,k)
            if not all(lam(L,K) and lam(R,K) for K in S): continue
            for m in range(k+1,n):       # ((L R) I) -> (L (R I)), new node R+I
                I=(k+1,m);P=(i,m);New=(s+1,m)
                if all(lam(I,K) and lam(P,K) for K in S) and all(lam(New,K) for K in rest) and W.rank(L,R,I)<=2: return False
            for h in range(0,i):         # (I (L R)) -> ((I L) R), new node I+L
                I=(h,i-1);P=(h,k);New=(h,s)
                if all(lam(I,K) and lam(P,K) for K in S) and all(lam(New,K) for K in rest) and W.rank(I,L,R)<=2: return False
        return True
    changed=True
    while changed:
        changed=False
        for J in sorted(S):
            if not ok(J,S): S.discard(J);changed=True
    return S
def certificate(w,th):
    W=Word(w);n=len(w);ts=trees(0,n-1);lt={letter_term(t,w):t for t in ts}
    for t in ts:
        for y,path in moves(letter_term(t,w),th):
            if not path[-1][1][0].startswith('moufang') or y not in lt: continue
            u=lt[y];b=set();nodes(u,b)
            hit=[J for J in stable(t,W,n) if J not in b]
            if hit: return (path[-1][1][0],letter_term(t,w),y,sorted(stable(t,W,n)),hit[0])
    return None
if __name__ == '__main__':
    th = Theory(list("xyzuvwtrs"))
    if sys.argv[1] == 'words':
        miss = 0
        for w in sys.argv[2:]:
            c = certificate(w, th); miss += c is None
            print(w, 'move', c[0] if c else None, 'stable(T0)', c[3] if c else None, 'separator', c[4] if c else None)
        sys.exit(1 if miss else 0)
    for n in range(4, int(sys.argv[1]) + 1):
        t0 = time.time(); tot = 0; miss = []
        for w in canon_words(n, 3):
            if interval(w): continue
            tot += 1
            if certificate(w, th) is None: miss.append(w)
        print(f'n={n}: non-interval 3-letter words {tot}, stable-separator certificates {tot-len(miss)}, misses {miss[:6]} ({time.time()-t0:.0f}s)', flush=True)
        assert not miss
