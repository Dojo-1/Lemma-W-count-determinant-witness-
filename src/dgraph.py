"""D_N: flips NOT certified nonvanishing by Lemma W (rank of segment count matrix <= 2).
In-class graph (vanishing local associators) is a subgraph of D_N. Measure:
 (a) bad words: does some class meet >= 2 D_N-components?  (=> disconnection certified by W alone)
 (b) interval words: is every D_N edge a true in-class edge, and do classes equal D_N components?
"""
import sys, json
import numpy as np
from collections import deque
from spectra import trees, canon_words, spectrum
def span(t): return (t,t) if isinstance(t,int) else (span(t[0])[0],span(t[1])[1])
def counts(w,i,j,L): return [w[i:j+1].count(c) for c in L]
def rankN(w,a,b,c,L):
    return np.linalg.matrix_rank(np.array([counts(w,*a,L),counts(w,*b,L),counts(w,*c,L)],dtype=float))
def dflips(t,w,L):
    out=[]
    if isinstance(t,int): return out
    Lt,R=t
    if not isinstance(Lt,int):
        A,B=Lt;C=R
        if rankN(w,span(A),span(B),span(C),L)<=2: out.append((A,(B,C)))
    if not isinstance(R,int):
        A=Lt;B,C=R
        if rankN(w,span(A),span(B),span(C),L)<=2: out.append(((A,B),C))
    return out+[(x,R) for x in dflips(Lt,w,L)]+[(Lt,x) for x in dflips(R,w,L)]
def interval(w): return all(w[i]==w[i+1] or w[i+1] not in w[:i+1] for i in range(len(w)-1))
def comps(w,L):
    ts=trees(0,len(w)-1);comp={}
    for s in ts:
        if s in comp: continue
        comp[s]=s;dq=deque([s])
        while dq:
            x=dq.popleft()
            for y in dflips(x,w,L):
                if y not in comp: comp[y]=s;dq.append(y)
    return comp
for n in range(4,int(sys.argv[1])+1):
    bad_cert=bad_tot=0;bad_fail=[];int_tot=int_eq=0;int_fail=[]
    for k in range(3,n+1):
        for w in canon_words(n,k):
            L=sorted(set(w));comp=comps(w,L);cls=spectrum(w,8,T=1,S=4)['classes']
            if interval(w):
                int_tot+=1
                D={};[D.setdefault(c,set()).add(t) for t,c in comp.items()]
                ok={frozenset(c) for c in cls}=={frozenset(v) for v in D.values()}
                int_eq+=ok
                if not ok:int_fail.append(w)
            else:
                bad_tot+=1
                if any(len({comp[t] for t in c})>1 for c in cls): bad_cert+=1
                else: bad_fail.append(w)
    print(n,'bad words certified by W-separation:',bad_cert,'/',bad_tot,bad_fail[:6],'| interval: classes==D_N comps',int_eq,'/',int_tot,int_fail[:6],flush=True)
