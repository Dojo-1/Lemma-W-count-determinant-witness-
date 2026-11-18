"""Cross-check word-bracketing partitions against ZFC-A-'s independent octonion tensors.

Tensors are parsed by ZFC-A-'s own `rationalalgebracheck.multiplication_table` from
examples/rational_algebra/octonion_o8/model.json (algebras F0, F1, F2; F1/F2 are presented in
sheared coordinates). The bracketing partition of a word is basis-independent, so all three
must reproduce our partitions exactly.
"""
import json, sys
import numpy as np
import os
from pathlib import Path
ZFCA = Path(os.environ.get("ZFCA_ROOT", Path(__file__).resolve().parents[1] / "ZFC-A-"))  # checkout of Dojo-1/ZFC-A-
sys.path.insert(0, str(ZFCA / "src"))
from rationalalgebracheck import multiplication_table
from spectra import trees, canon_words, spectrum

P = 2147483647
model = json.load(open(ZFCA / "examples/rational_algebra/octonion_o8/model.json"))

def tensor_mod_p(name):
    T = multiplication_table(model["algebras"][name]["products"], 8)
    arr = np.zeros((8, 8, 8), dtype=object)
    for i in range(8):
        for j in range(8):
            for k in range(8):
                q = T[i][j][k]
                arr[i, j, k] = (q.numerator * pow(q.denominator, -1, P)) % P
    return arr.astype(np.int64), T

def mk_mul(Tp):
    def mul(a, b):  # a,b: (S,8)
        out = np.zeros_like(a)
        for i in range(8):
            for j in range(8):
                coef = (a[:, i] * b[:, j]) % P
                out = (out + coef[:, None] * Tp[i, j][None, :]) % P
        return out
    return mul

def partition(word, mul, S=4, seed=7):
    rng = np.random.default_rng(seed)
    vals = {c: rng.integers(0, P, size=(S, 8), dtype=np.int64) for c in set(word)}
    memo = {}
    def go(i, j):
        if (i, j) in memo: return memo[(i, j)]
        if i == j: out = [(i, vals[word[i]])]
        else:
            out = [((tl, tr), mul(vl, vr)) for k in range(i, j) for tl, vl in go(i, k) for tr, vr in go(k + 1, j)]
        memo[(i, j)] = out; return out
    cl = {}
    for t, v in go(0, len(word) - 1): cl.setdefault(v.tobytes(), set()).add(t)
    return {frozenset(c) for c in cl.values()}

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for name in ("F0", "F1", "F2"):
        Tp, T = tensor_mod_p(name); mul = mk_mul(Tp)
        bad = 0; tot = 0
        for n in range(3, nmax + 1):
            for k in range(2, n + 1):
                for w in canon_words(n, k):
                    mine = {frozenset(c) for c in spectrum(w, 8, T=1, S=4)["classes"]}
                    theirs = partition(w, mul)
                    tot += 1; bad += mine != theirs
        dens = sorted({q.denominator for a in T for b in a for q in b})
        print(f"{name}: words {tot}, partition mismatches {bad}, tensor denominators {dens}", flush=True)
