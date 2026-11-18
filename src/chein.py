"""Test octonion bracketing identities in Chein Moufang loops M(G,2) (G nonabelian => nonassociative Moufang)."""
import itertools
from spectra import fmt
def comp(p,q): return tuple(p[q[i]] for i in range(len(q)))
def inv(p):
    r=[0]*len(p)
    for i,x in enumerate(p): r[x]=i
    return tuple(r)
def S3(): return list(itertools.permutations(range(3)))
def D4():
    r=(1,2,3,0); f=(0,3,2,1); els={tuple(range(4))}; fr=[tuple(range(4))]
    while fr:
        x=fr.pop()
        for g in (r,f):
            y=comp(x,g)
            if y not in els: els.add(y); fr.append(y)
    return sorted(els)
def chein(els):
    def mul(a,b):
        (g,s),(h,t)=a,b
        if s==0 and t==0: return (comp(g,h),0)
        if s==0 and t==1: return (comp(h,g),1)
        if s==1 and t==0: return (comp(g,inv(h)),1)
        return (comp(inv(h),g),0)
    return [(g,s) for g in els for s in (0,1)], mul
def ev(t,word,assign,mul):
    if isinstance(t,int): return assign[word[t]]
    return mul(ev(t[0],word,assign,mul),ev(t[1],word,assign,mul))
def holds(word,t1,t2,L,mul):
    letters=sorted(set(word))
    for vals in itertools.product(L,repeat=len(letters)):
        a=dict(zip(letters,vals))
        if ev(t1,word,a,mul)!=ev(t2,word,a,mul): return False,{k:str(v) for k,v in a.items()}
    return True,None
tests={
 'moufang_mid xyzx':('xyzx',((0,1),(2,3)),(0,((1,2),3))),
 'moufang_left xyxz':('xyxz',(((0,1),2),3),(0,(1,(2,3)))),
 'flexible xyx':('xyx',((0,1),2),(0,(1,2))),
 'assoc xyz (control, must FAIL)':('xyz',((0,1),2),(0,(1,2))),
 'NEW? (xy)(z(xy)) = x(y((zx)y))':('xyzxy',((0,1),(2,(3,4))),(0,(1,((2,3),4)))),
}
if __name__=='__main__':
  for gname,G in (('S3',S3()),('D4',D4())):
    L,mul=chein(G)
    for k,(w,a,b) in tests.items():
        ok,ce=holds(w,a,b,L,mul); print(f'M({gname},2) order {len(L)}: {k}: {"holds" if ok else "FAILS"}', '' if ok else ce)
