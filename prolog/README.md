# Prolog formalization (SWI-Prolog)

Seven programs. Each one checks independently what the Lean development proves:

```bash
swipl -q -g main -t halt caterpillar.pl   # run-sequence combinatorics, finite base, constructive Prop. E
swipl -q -g main -t halt octonion.pl      # octonion identities and Lemma W's core
swipl -q -g main -t halt trees.pl         # G3 end to end, from words to bracketings
swipl -q -g main -t halt algebra.pl       # Lemma W expansion, L1, Artin, K (octonion side)
swipl -q -g main -t halt g2.pl            # K (combinatorial side, Moufang lift), G2: T, M, S, C
swipl -q -g run -t halt proofs.pl         # the Lean constructions for K's lift, C (⇐), T, M, run and validated
swipl -q -g run -t halt assembly.pl       # moment = coefficient, moments → profiles, the assembled G2
```

## `caterpillar.pl`: Proposition E

The definitions are the same as in Lean, written as logic programs:
- `valid/1`, `failure/2`, `cond/3`;
- the certificate relations `chain/3` and `cat/3`. Their derivation terms use the constructors `bottom`, `l`, `r`, `d`, `passL`, `passR`, `passD`, `moveD`, `moveL`, `moveR`. The same relation checks a given derivation and searches for one.

`construct/3` is the induction proof of Proposition E written as a program: it follows the case analysis without search.

Checks:
- the base, exhaustively (240 cases);
- all 44,670 constructed certificates up to 12 runs, each re-checked by `cat/3`;
- the exact characterization up to 9 runs;
- every non-interval word of length ≤ 9.

## `octonion.pl`: the octonion identities

Integer octonions use the repository's Cayley–Dickson table.

**Identity checks.** Moufang left, right and middle, left and right alternative, and flexible. The check is **complete, not sampled**. The product is bilinear, and each identity is linear in some arguments and quadratic in one. So it holds everywhere iff it holds when the linear arguments range over the basis `e_i` and the quadratic one over `e_i` and `e_i + e_j`. That is 2,304 cases for each Moufang identity. Random 7-digit tests run on top, plus a negative control: associativity fails, so the check can fail.

**Lemma W core.** `[X,Y,Z] = det(X,Y,Z)·[e₁,e₂,e₄]` on `span(e₁,e₂,e₄)`. The identity is trilinear, so the 27 basis triples are a complete check. Also `[e₁,e₂,e₄] = 2e₇`.

## `trees.pl`: G3 end to end

For each non-interval 3-letter word, `construct/3` builds the run-level certificate and `glue_cat/6` turns it into bracketings `T₀`, `T₁` and a chain of path nodes. This mirrors the Lean `glue_cat`. Each link is then checked independently:

- **(a)** `mouf/3`: `T₁` comes from `T₀` by one left, right or middle Moufang move with a single repeated letter.
- **(b)** `pchain/3`: the position-level chain conditions of Lemma Cat hold, and the chain nodes are nodes of `T₀`.
- **(c)** `certified/4`: **Lemma Cat's conclusion by brute force.** Every compatible rotation that would delete a chain node has determinant ≠ 0.
- **(d)** **Exact D_N-component search** by breadth-first search, with no use of Lemma R′. `T₁` is not reachable, and every reachable tree keeps all chain nodes, which is Lemma R′'s conclusion.
- **(e)** `T₀` and `T₁` evaluate to the same octonion under random integer octonions for x, y, z.

Results (`../data/prolog_trees.log`):

| Lengths | Checks | Words |
|---|---|---|
| n ≤ 9 | (a)–(e), including the exact component search | 4,330 |
| n = 10 | (a)–(c) and (e) | 9,294 |

Negative controls confirm that `certified/4` and `mouf/3` can fail.

## `algebra.pl`: Lemma W's expansion, L1, Artin, K

Random integer tests with a fixed seed ([log](../data/prolog_algebra.log)):
- **Lemma W.** Series truncated after `θ³`, letters `x, y, z` substituted by `1 + θe₁/e₂/e₄ + θ²r + θ³t` (`r, t` random), a fourth letter with `q = 0`. The local associator has zero `θ⁰..θ²` coefficients and `θ³` coefficient `2·det·e₇` (300 rounds). Control: `[x,y,z]` has a nonzero `θ³` term.
- **L1.** `N(ab) = N(a)N(b)`, `a·ā = N(a)`, no zero divisors; `C[S₁] = C[S₂] ⟺ S₁ = S₂` for random contexts and nonzero letter values (300 cases, both outcomes occur).
- **Artin.** Every bracketing of a word over two random octonions (n ≤ 7) has one value. Control: a third value separates the bracketings of `uvz`.
- **K.** Killed letters set to `1` give the restricted bracketing's value.

## `g2.pl`: K and G2, exhaustively on small words

Exact `D_N`-components by breadth-first search over all bracketings, with `D_N` = all `3 × 3` count minors zero ([log](../data/prolog_g2.log)):

| Statement | Range | Result |
|---|---|---|
| K: flips ↦ flips or identities, `D_N` ↦ `D_N` or identities | all 426 four-letter words, n ≤ 7, every letter killed | ok |
| K: Moufang moves between different components of the 3-letter image lift | same words | 5,892 moves, all lift |
| Prop. T: invariant constant and complete, count `1 + b(C(a+c,a) − 1)` | 56 three-block words, n ≤ 8 | 694 components |
| Lemma M: direct octonion-unit coefficients = `±[j S_{ω₊} + (b−j) S_{ω₋}]`, sign uniform in `T` | every bracketing, n ≤ 6 | 521 bracketings |
| Prop. S: profiles decode the invariant | every bracketing, n ≤ 7; formula range `a+b+c ≤ 10` | 291 components; 3,422 maps |
| Prop. C: `D_N`-components = σ-classes | 99 interval words with ≥ 3 letters, n ≤ 7 | 2,804 components |

Controls: for the non-interval word `[0,1,2,1,0]` the σ-classes (11) differ from the components (10); Lemma M with `j` and `b − j` swapped fails.

## `proofs.pl`: the Lean proofs as programs

Each program builds what the corresponding Lean proof builds; independent checkers validate the output ([log](../data/prolog_proofs.log)):

| Lean proof | Program | Range | Result |
|---|---|---|---|
| `lift_mouf`, `lift_separates` | gap-absorption lift (`lift_tree`, `lift_mouf`; pivot splits, `wrapL`/`wrapR`) | every Moufang move of every 3-letter image of a 4-letter word, n ≤ 7 | 9,984 lifts; the 5,892 component-crossing moves lift to crossing moves |
| `propC_backward` | root-split path builder (equal splits, cases B and C, two-letter rotations to a comb) | every σ-equal pair of every interval word with ≥ 3 letters, n ≤ 7 | 33,216 paths, every step a `D_N`-flip |
| `sh_sub`, `cx_omega`, `β_eq_ωq` | shapes from `cx(q, r)`; `cx` from the absorption word; absorption word = `ω₊`/`ω₋` | every bracketing and `y`-leaf, three-block words, n ≤ 8 | 29,646 pairs |
| `walk`, `lemmaM` | walk value of every restriction; exact moment (sign and unit) | every bracketing and `(p, r)`, n ≤ 7 | 24,692 cases |

Control: on the non-interval word `[0,1,2,1,0]` the path builder fails for a σ-equal pair.

## `assembly.pl`: the last steps of G2

([log](../data/prolog_assembly.log))

| Lean proof | Program | Range | Result |
|---|---|---|---|
| `coef_moment`, `subst_eq` | octonion polynomial multiplication of `1+se₁, 1+qe₂, 1+te₄` along the bracketing; coefficient vs. moment; evaluation at random points | every bracketing of three-block words, n ≤ 7 | 2,501 bracketings |
| `key_of_K` | `κ(p,r)` from the coefficients alone; homogeneous sums in base `2m+1` give `N` and `M`; decode | every bracketing, n ≤ 7 | profiles equal the invariant's; 291 components separated |
| `G2Final.g2` | differing triple → kill → renumber → Kronecker valuation → pull back → evaluate | every pair in different components of interval words with ≥ 3 letters, n ≤ 6 | 21,108 pairs separated |

Control: 142 pairs in the same component take equal values.

Prolog executes and checks. It is not a proof assistant: the all-length statements are the Lean theorems `Caterpillar.propE`, `Caterpillar.g3_trees`, `Octonion.moufang_*`, `Octonion.lemmaW_expansion`, `Octonion.context_cancel`, `Octonion.artin`, `Octonion.kill_DN`, `Octonion.lift_separates`, `Octonion.propC_iff`, `PropT.propT`, `LemmaM.lemmaM`, `PropS.propS_interior`, `Coeff.coef_moment`, `Profiles.key_of_K` and `G2Final.g2`.
