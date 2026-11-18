"""Independent brute-force check of Lemma I (interval words): rank(N)<=2  =>  V-condition,
over all consecutive segment triples of interval words up to length 12 (exhaustive)."""
import itertools
from verify_theorem import Word, interval
from spectra import canon_words
bad=0;checked=0
import sys
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 12
for n in range(3,NMAX+1):
    for k in range(3,min(n,8)+1):
        for w in canon_words(n,k):
            if not interval(w): continue
            W=Word(w)
            for i in range(n):
                for j in range(i,n):
                    for l in range(j+1,n):
                        for m in range(l+1,n):
                            a,b,c=(i,j),(j+1,l),(l+1,m)
                            checked+=1
                            if W.rank(a,b,c)<=2 and not W.V(a,b,c): bad+=1;print('COUNTEREXAMPLE',w,a,b,c)
print('triples checked',checked,'violations',bad)
