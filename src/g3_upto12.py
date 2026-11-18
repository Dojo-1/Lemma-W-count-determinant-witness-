"""G3 for n = 11, 12 by local certificates: Theorem B (block_witness) or, for the rest, Lemma R' (stable_separators).
Run: python src/g3_upto12.py   (~6 min)"""
import sys,time;from pathlib import Path;sys.path.insert(0,str(Path(__file__).resolve().parent))
from stable_separators import certificate
from certs import Theory
from verify_theorem import interval
from spectra import canon_words
from block_witness import witness
th=Theory(list("xyzuvwtrs"))
for n in (11,12):
    t0=time.time();tot=bm=0;miss=[]
    for w in canon_words(n,3):
        if interval(w): continue
        tot+=1
        if witness(w) is not None: continue
        bm+=1
        if certificate(w,th) is None: miss.append(w)
    print(f'n={n}: non-interval 3-letter words {tot}, Theorem B witnesses {tot-bm}, remaining {bm}, stable-separator certificates {bm-len(miss)}, misses {miss} ({time.time()-t0:.0f}s)',flush=True)
