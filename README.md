# Lemma W — count-determinant witness

**Octonion bracketings, the associahedron, and which identities are local.**

A bracketing of a word `w` (letters may repeat) is a vertex of the associahedron `Kₙ`; a single reassociation is an edge. In the octonions 𝕆 several bracketings can induce the same polynomial map. This repository studies those *kernel classes*. When is every class connected in `Kₙ`, so that every identity is reachable by single reassociations that are themselves identities?

**Theorem (proved for every word of length ≤ 9; general n reduced to two stated claims).** In 𝕆 every kernel class of `w` is flip-connected **iff** `w` has at most two distinct letters, or each letter occurs in one contiguous run. The number of words of length `n` (up to renaming letters) with a disconnected class is

```
Bell(n) − 2ⁿ + n  =  0, 0, 0, 3, 25, 145, 756, 3892, 20644   (n = 1..9)
```

Full statements and proofs: **[THEOREM.md](THEOREM.md)**.

## Lemma W

> Let `a, b, c` be consecutive segments of `w` and `N` the 3 × |letters| matrix of letter multiplicities. If `rank N = 3`, then the local associator `[A, B, C]` is not identically zero, for **every** bracketing `A, B, C` of the segments.

*Proof.* Choose letters `x, y, z` with `det N_{xyz} ≠ 0`. Specialise `x, y, z ↦ exp(θe₁), exp(θe₂), exp(θe₄)` and every other letter to `1`. Then `[A,B,C] = θ³ det(N_{xyz}) [e₁,e₂,e₄] + O(θ⁴)` by trilinearity and alternation, and `[e₁,e₂,e₄] ≠ 0`. ∎

Basis-unit sign evaluations see only parities, and miss cases such as `[x², y, z] ≠ 0`; exponentials keep the counts. Lemma W combines with **context cancellation** (𝕆 is a division algebra, so an edge stays inside a class iff its local associator vanishes). Together they say the in-class flip graph lies inside `D_N`, the flips with `rank N ≤ 2`. Two equal bracketings in different `D_N`-components therefore *prove* a class disconnected.

## Evidence

| claim | status | instrument |
|---|---|---|
| General lemmas: context cancellation, Lemma W, vanishing via Artin, interval rank lemma, θ³ invariant, Moufang lifting under killing, Catalan-ness for distinct letters | proved | [THEOREM.md](THEOREM.md) |
| Characterization for all 26,439 words, n ≤ 9 | proved by exact computation; no sampling | `src/verify_theorem.py` ([log n ≤ 9](data/verify9.log)) |
| (G3) every non-interval 3-letter word has a Moufang move across `D_N`-components | n ≤ 9 exact; general open | `src/g3_check.py` |
| (G3-R) …via a Moufang move toggling an *absolutely rigid* interval (Lemma R) | holds n ≤ 9; **false** from n = 10 (G3 still holds there) | `src/rigid_separators.py` ([log](data/rigid9.log)) |
| Theorem B: words with a ratio-primitive block witness are disconnected (all n) | proved; covers 99.55 % of non-interval 3-letter words at n = 12 | `src/block_witness.py` |
| G2 ⇐ triple-restriction completeness (a) + three-block case (b) | reduction proved; (b) proved (below); (a) verified n ≤ 7 | `src/g2_reduction.py` |
| Proposition T: `D_N`-components of `xᵃyᵇzᶜ` classified by an explicit invariant; count `1 + b(C(a+c,a) − 1)` | proved (all a, b, c) | `src/three_block.py` |
| Lemma M + Proposition S: moment formula via Cayley–Dickson absorption; linear moments separate all components of `xᵃyᵇzᶜ`, so G2 holds for every three-block word | proved (all a, b, c); exact checks n ≤ 8, formula injectivity a+b+c ≤ 12 | `src/lemma_m.py` |
| (G2) interval words have no non-local identities | n ≤ 9 exact; general open | `src/verify_theorem.py` |
| Interval rank lemma (also proved by cases) | brute force: 1,997,801 triples, n ≤ 12 | `src/lemmaI_check.py` |
| Every class exactly certified by full polarization over basis tuples | n ≤ 6 | `src/certify_exact.py`, `src/exact.py` ([log](data/exact6.log)) |
| Equalities derivable from flexible/alternative/Moufang/Artin laws serialised as certificates | 517/517 replay (n ≤ 5) under Dojo-1/ZFC-A- `certcheck.replay` | `src/certs.py`, [certificates/](certificates/) |
| Partitions agree with ZFC-A-'s independent octonion tensors (F0, F1, F2) | n ≤ 6, 0 mismatches | `src/crosscheck.py` ([log](data/cross6.log)) |
| All observed 𝕆 bracketing identities hold in the Chein Moufang loops M(S₃,2), M(D₄,2) | n ≤ 5, 1000 checks | `src/chein.py`, `src/chein_sweep.py` |

**What is counted as proved.** Equalities: derivations from laws valid in every alternative algebra, or exact polarization. Inequalities: Lemma W, the θ³ invariant, or a distinct exact integer evaluation. The earlier randomized sweeps (`src/sweep.py`, `src/n8.py`, [data/sweep.json](data/sweep.json)) were exploratory and are no longer load-bearing.

## Word spectra (new sequences, no OEIS match on 2026-11-18)

Σ over words of length `n` (up to renaming) of the number of distinct bracketing maps:

- 𝕆: `1, 2, 6, 31, 258, 2877, 38107, 572090` (n = 1..8, randomized measurement)
- sedenions 𝕊: `1, 2, 8, 55, 529, 6248` (n = 1..6, randomized measurement)

For distinct letters both are Catalan (proved for 𝕆 in THEOREM.md). Sedenion non-locality comes from cubes and long alternations; no characterization yet.

## Run

```bash
pip install -r requirements.txt
python src/verify_theorem.py 8        # exact proof for every word of length <= 8 (~30 s)
python src/g3_check.py 8              # G3 for 3-letter words
python src/lemmaI_check.py 10         # interval rank lemma, brute force
python src/certify_exact.py 5         # full-polarization certification of classes
# optional: certificate replay with a checkout of Dojo-1/ZFC-A-
ZFCA_ROOT=/path/to/ZFC-A- python src/certs.py 5
```

CI ([verify.yml](.github/workflows/verify.yml)) reruns the exact verification on every push.

## Prior art and scope

Associative spectra for distinct variables (Csákány–Waldhauser 2000; Liebscher–Waldhauser; Huang–Lehtonen). Bol–Moufang identities, which cover the n = 4 case (Fenyves; Phillips–Vojtěchovský). The free Moufang loop word problem. A bounded search found no prior treatment of repeated-letter word spectra in 𝕆/𝕊, the flip-connectivity characterization, or the sequences above. That is absence of evidence, not a novelty certificate.

Origin: the kernel quotient of a Tendril from the associahedron into 𝕆 ([Dojo-1/Tendrils](https://github.com/Dojo-1/Tendrils)); certificate format from [Dojo-1/ZFC-A-](https://github.com/Dojo-1/ZFC-A-).

No license has been chosen yet.
