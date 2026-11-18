import json, sys
from multiprocessing import Pool
from spectra import spectrum, canon_words
def interval(w): return all(w[i]==w[i+1] or w[i+1] not in w[:i+1] for i in range(len(w)-1))
def job(w):
    r=spectrum(w,8,T=1,S=4,seed=hash(w)%1000)
    return w,r['s'],r['disconnected_classes'],r['max_components']
if __name__=='__main__':
    n=int(sys.argv[1]); words=[w for k in range(1,n+1) for w in canon_words(n,k)]
    with Pool() as p: rows=p.map(job,words,chunksize=8)
    bad=sum(1 for r in rows if r[2]); pred=[w for w in words if not (len(set(w))<=2 or interval(w))]
    mism=[r for r in rows if bool(r[2])!=(r[0] in set(pred))]
    print('n',n,'words',len(words),'bad',bad,'predicted',len(pred),'mismatches',len(mism),'sum_s',sum(r[1] for r in rows),'maxcomp',max(r[3] for r in rows))
    json.dump(rows,open(f'O{n}.json','w'))
