"""G3 for 11 <= n <= 14 by local certificates: Theorem B (block_witness), else Proposition Q' (run_comb,
either orientation), else Lemma R' (stable_separators, full search).
Run: python src/g3_upto14.py 11 14"""
import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stable_separators import certificate
from run_comb import qprime
from certs import Theory
from verify_theorem import interval
from spectra import canon_words
from block_witness import witness
th = Theory(list("xyzuvwtrs"))
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    t0 = time.time(); tot = b = q = r = 0; miss = []; rest = []
    for w in canon_words(n, 3):
        if interval(w): continue
        tot += 1
        if witness(w) is not None: b += 1; continue
        if qprime(w) or qprime(w[::-1]): q += 1; continue
        rest.append(w)
    for w in rest:
        if certificate(w, th) is not None: r += 1
        else: miss.append(w)
    print(f'n={n}: non-interval 3-letter words {tot}: Theorem B {b}, Q\' {q}, Lemma R\' {r} {rest}, misses {miss} ({time.time()-t0:.0f}s)', flush=True)
    assert not miss
