"""Three-block words x^a y^b z^c: the invariant Phi = (j, a', c', W) of Proposition T classifies D_N-components
(complete for 0<j<b; j always invariant) and the counts match 1 + b(C(a+c,a)-1). Run: python src/three_block.py"""
import sys
sys.path.insert(0,'src'); sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parent))
from math import comb
from g2_reduction import comp_of
def span(t): return (t,t) if isinstance(t,int) else (span(t[0])[0],span(t[1])[1])
def invariant(t,a,b,c):
    lastx,firstz=a-1,a+b
    path=[];node=t
    while True:
        L,R=node;sl,sr=span(L),span(R)
        if sl[0]<=lastx and sl[1]>=firstz: path.append(('z',sr[1]-sr[0]+1)); node=L; continue
        if sr[0]<=lastx and sr[1]>=firstz: path.append(('x',sl[1]-sl[0]+1)); node=R; continue
        break
    L,R=node;sl,sr=span(L),span(R)
    j=sl[1]-lastx
    core_x=lastx-sl[0]+1; core_z=sr[1]-firstz+1
    word=''.join(s*n for s,n in reversed(path))
    return (j,core_x,core_z,word)
bad=0
for a in range(1,4):
    for b in range(1,5):
        for c in range(1,4):
            w='x'*a+'y'*b+'z'*c;comp=comp_of(w)
            inv={}
            for t,cid in comp.items():
                inv.setdefault(cid,set()).add(invariant(t,a,b,c))
            # check: for each component, invariant set; for interior j, invariant should be constant & distinct
            cnt_by_j={}
            ok=True;seen={}
            for cid,S in inv.items():
                js={s[0] for s in S}
                if any(0<jj<b for jj in js):
                    if len(S)!=1: ok=False
                    s=next(iter(S))
                    if s in seen: ok=False
                    seen[s]=cid
                for jj in js: cnt_by_j.setdefault(jj,set()).add(cid)
            interior=sum(1 for cid,S in inv.items() if all(0<s[0]<b for s in S))
            boundary=sum(1 for cid,S in inv.items() if all(s[0] in (0,b) for s in S))
            mixed=len(inv)-interior-boundary
            C=comb(a+c,a)
            pred_ok= interior==(b-1)*(C-1) and boundary==C and mixed==0
            if not (ok and pred_ok): bad+=1;print('a,b,c',a,b,c,'interior',interior,'boundary',boundary,'mixed',mixed,'C',C,'invariant-complete',ok)
print('done, discrepancies:',bad)
