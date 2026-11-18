"""Exact (proof-grade) certification of every measured class for all words of length <= N, via
full polarization on basis tuples (exact.py). Run: python src/certify_exact.py 5"""
import sys, time
from exact import certify_classes
from spectra import spectrum, canon_words
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
for n in range(3, N + 1):
    t0 = time.time(); fail = []; tot = 0
    for k in range(2, n + 1):
        for w in canon_words(n, k):
            ok, _ = certify_classes(w, spectrum(w, 8, T=1, S=4)["classes"]); tot += 1
            if not ok: fail.append(w)
    print(f"n={n}: {tot - len(fail)}/{tot} words, every class exactly certified; failures={fail} ({time.time()-t0:.0f}s)", flush=True)
    assert not fail
