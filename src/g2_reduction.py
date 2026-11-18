"""G2 reduction probes: (a) for interval words, D_N components are determined by the components
of all letter-triple restrictions; (b) x^a y^b z^c has 1 + b*(C(a+c,a)-1) components.
Run: python src/g2_reduction.py 7
"""
import sys, itertools
sys.path.insert(0,'src')
from collections import deque
from verify_theorem import Word, dflips, interval
from spectra import trees, canon_words
def comps(w):
    W=Word(w);ts=trees(0,len(w)-1);comp={}
    for s in ts:
        if s in comp: continue
        comp[s]=s;dq=deque([s])
        while dq:
            x=dq.popleft();e=[];dflips(x,W,e)
            for y,_ in e:
                if y not in comp: comp[y]=s;dq.append(y)
    return comp
def restrict(t,keep):
    if isinstance(t,int): return t if t in keep else None
    a,b=restrict(t[0],keep),restrict(t[1],keep)
    if a is None: return b
    if b is None: return a
    return (a,b)
def reindex(t,m):
    return m[t] if isinstance(t,int) else (reindex(t[0],m),reindex(t[1],m))
cache={}
def comp_of(word):
    if word not in cache: cache[word]=comps(word)
    return cache[word]
if __name__=='__main__':
    # (2) 3-block words: number of components
    print('x^a y^b z^c components:')
    for a in range(1,5):
        print(' a=%d:'%a,[[len(set(comp_of('x'*a+'y'*b+'z'*c).values())) for c in range(1,5)] for b in range(1,5)])
    # (1) triple-restriction injectivity on interval words with >=4 letters
    for n in range(4,int(sys.argv[1])+1):
        bad=0;tot=0
        for k in range(4,n+1):
            for w in canon_words(n,k):
                if not interval(w): continue
                tot+=1;cw=comp_of(w);L=sorted(set(w));sig={}
                for t,c in cw.items():
                    key=[]
                    for tri in itertools.combinations(L,3):
                        pos=[i for i,ch in enumerate(w) if ch in tri];m={p:j for j,p in enumerate(pos)}
                        sub=''.join(w[p] for p in pos)
                        key.append(comp_of(sub)[reindex(restrict(t,set(pos)),m)])
                    sig.setdefault(c,set()).add(tuple(key))
                # injective on components: distinct comps -> distinct keys, and keys constant per comp
                keys={}
                ok=all(len(v)==1 for v in sig.values())
                for c,v in sig.items():
                    kk=next(iter(v))
                    if kk in keys and keys[kk]!=c: ok=False
                    keys[kk]=c
                bad+=not ok
        print(n,'interval words with >=4 letters',tot,'triple-restriction NOT a complete component invariant:',bad,flush=True)
    