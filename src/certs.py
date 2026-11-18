"""Emit ZFC-A- equational certificates for derivable octonion bracketing equalities.

Theory: sort O, constants = letters, binary `mul`. Axioms (all valid in every alternative algebra,
hence in O): flexible, left_alt, right_alt, moufang_mid, moufang_left, moufang_right, plus
Artin instances `artin_k`: (A B) C = A (B C) where A,B,C are fixed bracketed words in two
variables a,b (valid by Artin's theorem: 2-generated subalgebras of alternative algebras are
associative). Proofs are found by BFS over single rewrites inside one word's bracketings, then
serialized and replayed by ZFC-A-'s own certcheck.replay.
"""
import json, sys, itertools
from collections import deque
import os
from pathlib import Path
ZFCA = Path(os.environ.get("ZFCA_ROOT", Path(__file__).resolve().parents[1] / "ZFC-A-"))  # checkout of Dojo-1/ZFC-A-
sys.path.insert(0, str(ZFCA / "src"))
try:
    from certcheck import replay, digest   # optional: only needed to emit/replay certificates
except ImportError:
    replay = digest = None
from spectra import trees, canon_words, spectrum, fmt

V = lambda name: [name]
def M(a, b): return ["mul", a, b]

BASE_AXIOMS = {
    "flexible":      (["a", "b"], M(M(V("a"), V("b")), V("a")), M(V("a"), M(V("b"), V("a")))),
    "left_alt":      (["a", "b"], M(M(V("a"), V("a")), V("b")), M(V("a"), M(V("a"), V("b")))),
    "right_alt":     (["a", "b"], M(M(V("b"), V("a")), V("a")), M(V("b"), M(V("a"), V("a")))),
    "moufang_mid":   (["a", "b", "c"], M(M(V("a"), V("b")), M(V("c"), V("a"))), M(V("a"), M(M(V("b"), V("c")), V("a")))),
    "moufang_left":  (["a", "b", "c"], M(M(M(V("a"), V("b")), V("a")), V("c")), M(V("a"), M(V("b"), M(V("a"), V("c"))))),
    "moufang_right": (["a", "b", "c"], M(M(M(V("c"), V("a")), V("b")), V("a")), M(V("c"), M(V("a"), M(V("b"), V("a"))))),
}

# --- terms over letters: nested tuples of letters (strings)
def letter_term(t, word):
    return word[t] if isinstance(t, int) else (letter_term(t[0], word), letter_term(t[1], word))

def to_json(t):
    return [t] if isinstance(t, str) else M(to_json(t[0]), to_json(t[1]))

def letters(t):
    return {t} if isinstance(t, str) else letters(t[0]) | letters(t[1])

def generalize2(A, B, C):
    """Map a 2-letter triple to variables a,b (first-seen order). Returns (pattern json, subst)."""
    order = []
    for L in (A, B, C):
        for ch in json.dumps(L):
            pass
    seen = []
    def walk(t):
        if isinstance(t, str):
            if t not in seen: seen.append(t)
        else: walk(t[0]); walk(t[1])
    walk(A); walk(B); walk(C)
    names = dict(zip(seen, ["a", "b"]))
    def gen(t): return V(names[t]) if isinstance(t, str) else M(gen(t[0]), gen(t[1]))
    return gen, {names[k]: [k] for k in seen}, [names[k] for k in seen]

class Theory:
    def __init__(self, alphabet):
        self.artin = {}  # key json -> name
        self.alphabet = alphabet
    def artin_name(self, A, B, C):
        gen, subst, vars_ = generalize2(A, B, C)
        lhs = M(M(gen(A), gen(B)), gen(C)); rhs = M(gen(A), M(gen(B), gen(C)))
        key = json.dumps([lhs, rhs, vars_])
        if key not in self.artin: self.artin[key] = (f"artin_{len(self.artin)}", vars_, lhs, rhs)
        return self.artin[key][0], subst
    def json(self):
        ax = {}
        for name, (vs, l, r) in BASE_AXIOMS.items():
            ax[name] = {"variables": {v: "O" for v in vs}, "equation": {"lhs": l, "rhs": r}}
        for _, (name, vs, l, r) in self.artin.items():
            ax[name] = {"variables": {v: "O" for v in vs}, "equation": {"lhs": l, "rhs": r}}
        syms = {c: {"inputs": [], "output": "O"} for c in self.alphabet}
        syms["mul"] = {"inputs": ["O", "O"], "output": "O"}
        return {"format": "zfca-equational-theory-v1", "sorts": ["O"], "symbols": syms, "axioms": ax}

def matches(pattern, term, env):
    """pattern json over variables a,b,c (lists of len1 with var name) vs letter term."""
    if pattern[0] == "mul":
        if isinstance(term, str): return False
        return matches(pattern[1], term[0], env) and matches(pattern[2], term[1], env)
    v = pattern[0]
    if v in env: return env[v] == term
    env[v] = term; return True

def inst(pattern, env):
    if pattern[0] == "mul": return (inst(pattern[1], env), inst(pattern[2], env))
    return env[pattern[0]]

def local_moves(t, th):
    """Yield (new_term, step_descriptor) for rewrites at the root of t."""
    for name, (vs, l, r) in BASE_AXIOMS.items():
        for src, dst, d in ((l, r, "fwd"), (r, l, "bwd")):
            env = {}
            if matches(src, t, env) and set(env) == set(vs):
                yield inst(dst, env), (name, {v: to_json(env[v]) for v in vs}, d)
    if not isinstance(t, str):
        L, R = t
        if not isinstance(L, str):  # ((A B) C) -> (A (B C))
            A, B = L; C = R
            if len(letters(t)) <= 2:
                name, subst = th.artin_name(A, B, C)
                yield (A, (B, C)), (name, None, "fwd", (A, B, C))
        if not isinstance(R, str):  # (A (B C)) -> ((A B) C)
            A = L; B, C = R
            if len(letters(t)) <= 2:
                name, subst = th.artin_name(A, B, C)
                yield ((A, B), C), (name, None, "bwd", (A, B, C))

def moves(t, th):
    for nt, d in local_moves(t, th): yield nt, [("here", d)]
    if not isinstance(t, str):
        for nt, path in moves(t[0], th): yield (nt, t[1]), [("L",)] + path
        for nt, path in moves(t[1], th): yield (t[0], nt), [("R",)] + path

class Emitter:
    def __init__(self, th): self.th = th; self.steps = []; self.k = 0
    def new(self, step):
        sid = f"s{self.k}"; self.k += 1; step["id"] = sid; self.steps.append(step); return sid
    def rewrite(self, t, path):
        """Equation t = t' for a single rewrite at path."""
        head = path[0]
        if head[0] == "here":
            d = head[1]
            name = d[0]
            if d[1] is None:  # artin
                A, B, C = d[3]
                _, subst = self.th.artin_name(A, B, C)
                sid = self.new({"rule": "axiom", "name": name, "subst": subst})
            else:
                sid = self.new({"rule": "axiom", "name": name, "subst": d[1]})
            if d[2] == "bwd": sid = self.new({"rule": "symm", "premise": sid})
            return sid
        if head[0] == "L":
            p = self.rewrite(t[0], path[1:]); q = self.new({"rule": "refl", "term": to_json(t[1])})
        else:
            p = self.new({"rule": "refl", "term": to_json(t[0])}); q = self.rewrite(t[1], path[1:])
        return self.new({"rule": "cong", "symbol": "mul", "premises": [p, q]})

def derive_components(word, th):
    ts = [letter_term(t, word) for t in trees(0, len(word) - 1)]
    tset = set(ts); comp = {}; parent = {}
    for s in ts:
        if s in comp: continue
        comp[s] = s; parent[s] = None; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y, path in moves(x, th):
                if y in tset and y not in comp:
                    comp[y] = s; parent[y] = (x, path); dq.append(y)
    return ts, comp, parent

def certificate_for(word, target, comp, parent, th):
    chain = []; y = target
    while parent[y] is not None:
        x, path = parent[y]; chain.append((x, path)); y = x
    chain.reverse(); root = y
    em = Emitter(th); cur = None
    for x, path in chain:
        sid = em.rewrite(x, path)
        cur = sid if cur is None else em.new({"rule": "trans", "left": cur, "right": sid})
    return root, em, cur

if __name__ == "__main__":
    if replay is None:
        sys.exit("certificate replay needs Dojo-1/ZFC-A- (set ZFCA_ROOT)")
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    th = Theory(list("xyzuvwt"))
    jobs = []; stats = {"words": 0, "nontrivial_eqs": 0, "comp_vs_measured_equal": 0, "comp_finer": 0}
    for n in range(3, nmax + 1):
        for k in range(1, n + 1):
            for w in canon_words(n, k):
                ts, comp, parent = derive_components(w, th)
                meas = spectrum(w, 8, T=1, S=4)
                mclasses = {frozenset(letter_term(t, w) for t in c) for c in meas["classes"]}
                comps = {}
                for t, c in comp.items(): comps.setdefault(c, set()).add(t)
                dclasses = {frozenset(v) for v in comps.values()}
                stats["words"] += 1
                stats["comp_vs_measured_equal"] += dclasses == mclasses
                stats["comp_finer"] += dclasses != mclasses
                for t in ts:
                    if parent[t] is not None: jobs.append((w, t, comp, parent))
    theory = th.json(); tdig = digest(theory)
    ok = 0; fails = []; ledger = {}
    for w, t, comp, parent in jobs:
        root, em, res = certificate_for(w, t, comp, parent, th)
        goal = {"equation": {"lhs": to_json(root), "rhs": to_json(t)},
                "assumptions": sorted({s["name"] for s in em.steps if s["rule"] == "axiom"})}
        cert = {"format": "zfca-equational-certificate-v1", "theory_sha256": tdig,
                "steps": [{k: v for k, v in s.items()} for s in em.steps], "result": res, "goal": goal}
        try:
            replay(theory, cert, tdig, digest(goal)); ok += 1
            for a in goal["assumptions"]: ledger[a.split("_")[0] if a.startswith("artin") else a] = ledger.get(a.split("_")[0] if a.startswith("artin") else a, 0) + 1
        except Exception as e:
            fails.append((w, str(e)))
        stats["nontrivial_eqs"] += 1
    OUT = Path(os.environ.get("CERT_OUT", Path(__file__).resolve().parents[1] / "certificates" / "generated")); OUT.mkdir(parents=True, exist_ok=True)
    json.dump(theory, open(OUT / "theory.json", "w"))
    if jobs:
        w, t, comp, parent = next(j for j in jobs if j[0] == "xyzx")
        root, em, res = certificate_for(w, t, comp, parent, th)
        goal = {"equation": {"lhs": to_json(root), "rhs": to_json(t)}, "assumptions": sorted({s["name"] for s in em.steps if s["rule"] == "axiom"})}
        json.dump({"format": "zfca-equational-certificate-v1", "theory_sha256": tdig, "steps": em.steps, "result": res, "goal": goal}, open(OUT / "certificate_xyzx.json", "w"), indent=1)
    print(json.dumps(stats), "certificates replayed OK:", ok, "/", len(jobs), "failures:", fails[:3])
    print("theory sha256:", tdig, "artin instances:", len(th.artin), "assumption usage:", ledger)
