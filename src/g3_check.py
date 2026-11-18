"""G3 restricted to Moufang moves: every non-interval word over exactly 3 letters has a Moufang move
between different D_N components (exact; D_N via integer ranks)."""
import sys,time
from collections import deque
from verify_theorem import Word, dflips, interval
from certs import moves, letter_term, Theory
from spectra import trees, canon_words
th=Theory(list("xyzuvwtrs"))
for n in range(4,int(sys.argv[1])+1):
    t0=time.time();tot=ok=0;fails=[]
    for w in canon_words(n,3):
        if interval(w): continue
        W=Word(w);ts=trees(0,n-1);comp={}
        for s in ts:
            if s in comp: continue
            comp[s]=s;dq=deque([s])
            while dq:
                x=dq.popleft();e=[];dflips(x,W,e)
                for y,_ in e:
                    if y not in comp: comp[y]=s;dq.append(y)
        lt={letter_term(t,w):t for t in ts};found=False
        for t in ts:
            for y,path in moves(letter_term(t,w),th):
                if path[-1][1][0].startswith('moufang') and y in lt and comp[lt[y]]!=comp[t]: found=True;break
            if found:break
        tot+=1;ok+=found
        if not found:fails.append(w)
    print(f'n={n}: 3-letter non-interval words with a crossing Moufang move: {ok}/{tot} fails={fails[:5]} ({time.time()-t0:.0f}s)',flush=True)
