import itertools, random, json
from chein import chein, S3, D4, ev
from spectra import spectrum, canon_words, fmt
loops=[('M(S3,2)',*chein(S3())),('M(D4,2)',*chein(D4()))]
rng=random.Random(1)
fails=[];checked=0;words=0
for n in range(3,6):
    for k in range(2,n+1):
        for w in canon_words(n,k):
            cls=[c for c in spectrum(w,8,T=1,S=4)['classes'] if len(c)>1]
            if not cls: continue
            words+=1; letters=sorted(set(w))
            for name,L,mul in loops:
                if len(L)**len(letters)<=5000: assigns=itertools.product(L,repeat=len(letters))
                else: assigns=(tuple(rng.choice(L) for _ in letters) for _ in range(3000))
                assigns=list(assigns)
                for c in cls:
                    for t in c[1:]:
                        checked+=1
                        for vals in assigns:
                            a=dict(zip(letters,vals))
                            if ev(c[0],w,a,mul)!=ev(t,w,a,mul):
                                fails.append((name,w,fmt(c[0],w),fmt(t,w))); break
print('words with nontrivial classes',words,'identity checks',checked,'failures',len(fails),fails[:5])
