import json, sys, time
from spectra import *
out={}
for name,dim,nmax in (("O",8,7),("S",16,6)):
    for n in range(3,nmax+1):
        t0=time.time();tot=0;words=0;disc_words=0;maxc=0;hist={};rows=[]
        for k in range(1,n+1):
            for w in canon_words(n,k):
                r=spectrum(w,dim,T=3,S=3)
                words+=1;tot+=r['s'];hist[r['s']]=hist.get(r['s'],0)+1
                if r['disconnected_classes']:disc_words+=1
                maxc=max(maxc,r['max_components'])
                rows.append([w,r['s'],r['disconnected_classes'],r['max_components']])
        out[f"{name}{n}"]=dict(words=words,sum_s=tot,disc_words=disc_words,max_components=maxc,hist=hist,rows=rows)
        print(name,n,'words',words,'sum_s',tot,'disc_words',disc_words,'maxcomp',maxc,'%.0fs'%(time.time()-t0),flush=True)
json.dump(out,open('sweep.json','w'))
