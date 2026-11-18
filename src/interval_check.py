import sys
from collections import deque
from spectra import trees, canon_words, spectrum, flips
def letters(t,w): return {w[t]} if isinstance(t,int) else letters(t[0],w)|letters(t[1],w)
def artin_flips(t,w):
    out=[]
    if isinstance(t,int): return out
    L,R=t
    if not isinstance(L,int) and len(letters(t,w))<=2: out.append((L[0],(L[1],R)))
    if not isinstance(R,int) and len(letters(t,w))<=2: out.append(((L,R[0]),R[1]))
    out+=[(x,R) for x in artin_flips(L,w)]+[(L,x) for x in artin_flips(R,w)]
    return out
def interval(w): return all(w[i]==w[i+1] or w[i+1] not in w[:i+1] for i in range(len(w)-1))
for n in range(3,int(sys.argv[1])+1):
    tot=agree=0;bad=[]
    for k in range(3,n+1):
        for w in canon_words(n,k):
            if not interval(w): continue
            ts=trees(0,n-1);comp={}
            for s in ts:
                if s in comp: continue
                comp[s]=s;dq=deque([s])
                while dq:
                    x=dq.popleft()
                    for y in artin_flips(x,w):
                        if y not in comp: comp[y]=s;dq.append(y)
            A={};[A.setdefault(c,set()).add(t) for t,c in comp.items()]
            meas={frozenset(c) for c in spectrum(w,8,T=1,S=4)['classes']}
            tot+=1;ok=meas=={frozenset(v) for v in A.values()};agree+=ok
            if not ok:bad.append(w)
    print(n,'interval words (>=3 letters)',tot,'Artin-flip components == measured classes:',agree,bad[:5],flush=True)
