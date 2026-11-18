# Lean 4 / Lake formalization

Lean 4.15, core library only (no Mathlib). Build with `lake build`. It contains no `sorry`, `admit` or
`native_decide`. The main theorems depend only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

| file | content |
|---|---|
| `Caterpillar/Basic.lean` | run sequences (`NoAdj`, `AllThree`, `Valid`), conditions (C1)/(C2) as `Cond`, certificates `Chain` (no move) and `Cat` (with a middle, left or right Moufang move), the excluded entries `Failure` |
| `Caterpillar/Decide.lean` | executable searches `chainB`, `catB` with soundness proofs (`catB_sound : catB n s a = true → Cat s a`) |
| `Caterpillar/Base.lean` | **finite base**: `base4`, `base5` are checked by the kernel (`decide +kernel`) over all 81 + 243 lists × 4 entries |
| `Caterpillar/PropE.lean` | **Proposition E**: `propE : s.length = n → Valid s → ¬ Failure s e → Cat s e`, by strong induction (cases `L`, `R`, `D`); `cat_of_valid` |
| `Caterpillar/Det.lean` | **determinant core of Lemma Cat**: `rank3` says two single-letter segments `aⁱ, bˡ` (`a ≠ b`) and a third segment containing `third a b` give `det ≠ 0` in all six row orders; `third_of_distinct` covers the bottom case |
| `Caterpillar/Counts.lean` | count vectors of intervals of a word `w : Nat → L3`, single-letter intervals (`cnt_const`), positivity (`cnt_pos_of_sub`), laminarity `Lam` |
| `Caterpillar/LemmaCat.lean` | **Lemma Cat**: the laminarity classification. Every rotation compatible with `S` that would delete a chain node has a single-letter sibling (`sibling_left/right`) and a split cutting a single-letter peel; with `rank3` its determinant is nonzero. `certified_inner`, `certified_bottom`, and **`chain_selfCert`**: a position-level caterpillar chain (`PChain`) is self-certifying |
| `Caterpillar/RPrime.lean` | planar binary trees, rotations, `D_N`-flips (`det = 0`), reachability; **Lemma R′** (`stable_of_reach`: every tree `D_N`-reachable from `T₀` contains a self-certifying `S ⊆ subs T₀`, by the first-loss argument), `separated`, and **`caterpillar_separates`**: Lemma Cat + R′ |
| `Caterpillar/Glue.lean` | run lists (`Runs`), combs, the Moufang relation `Mouf` (left, right, middle Moufang patterns with a repeated single letter), and the translation of run-level certificates into bracketings (`glue_chain`, `glue_cat`). It ends with **`g3_trees`**: for every word over three letters that uses all three and is not an interval word, there are bracketings `T₀`, `T₁` with `Mouf w T₀ T₁` and `¬ Reach (DNStep w) T₀ T₁`. `DNStep` is symmetric (`dnstep_symm`), so `Reach` is the same-component relation |
| `Caterpillar/Octonion.lean` | integer octonions (repository table) and a **verified polynomial normaliser** (`norm`, `evalP_norm`, `eq_of_norm`). It proves, for all integer octonions, the **Moufang identities** (`moufang_left`, `moufang_right`, `moufang_middle`), the **alternative and flexible laws**, `[e₁,e₂,e₄] = 2e₇ ≠ 0`, and the **algebraic core of Lemma W** (`lemmaW_span`: `[X,Y,Z] = det(X,Y,Z)·[e₁,e₂,e₄]` on `span(e₁,e₂,e₄)`). Each identity is one kernel check per component; together they take about 7 minutes. Because these are polynomial identities over `ℤ`, they hold over every commutative ring, in particular `ℝ` |
| `Caterpillar/LemmaW.lean` | **Lemma W's expansion step.** Truncated series `c₀ + c₁θ + c₂θ² + c₃θ³` over integer octonions, letters substituted by `1 + θq_ℓ + θ²r_ℓ + θ³t_ℓ` with `q_ℓ` the count coordinates on `e₁, e₂, e₄` and `r_ℓ, t_ℓ` arbitrary (this covers `exp(θq_ℓ)` and every higher-order correction). **`lemmaW_expansion`**: the local associator of any `A, B, C` has vanishing `θ⁰, θ¹, θ²` coefficients and `θ³` coefficient `2·det(count matrix)·e₇` |
| `Caterpillar/Division.lean` | **L1.** Conjugate and norm; `x·x̄ = N(x)`, `N(ab) = N(a)N(b)`; no zero divisors (`mul_eq_zero`); left and right cancellation. **`context_cancel`**: for nonzero letter values, `C[S₁] = C[S₂] ⟺ S₁ = S₂` in every context `C`; **`flip_iff_assoc`**: a flip changes the value iff the local associator is nonzero |
| `Caterpillar/Artin.lean` | **Artin's theorem.** `Sp(u,v) = ℤ⟨1, u, v, uv⟩` is closed under multiplication (via `x² = t(x)x − N(x)` and the commutation formula) and the associator vanishes on it (trilinear, alternating, `[u,v,uv] = 0`). **`artin`**: with letter values in `{u, v}`, bracketings with the same leaf letters are equal. **Lemma V** (`lemmaV_two_letters`, `lemmaV_powers*`): the associator vanishes when `A, B, C` use ≤ 2 letters, or when two of them are powers of one letter |
| `Caterpillar/Kill.lean` | **K.** `kill` deletes the leaves of killed letters. `kill_ev`: setting killed letters to `1` gives the restricted value; `kill_id`: identities restrict to identities; `kill_flip`: a flip restricts to the identity or a flip; `kill_DN`: a `D_N`-flip (all `3 × 3` count minors `0`) restricts to a `D_N`-flip or the identity |
| `Caterpillar/G2.lean` | **Proposition T, count**: `propT_interior` (`Σ_{p<a,q<c} C(p+q,p) = C(a+c,a) − 1`) and `propT_count` (`(b−1)(C(a+c,a)−1) + C(a+c−1,a) + C(a+c−1,c) = 1 + b(C(a+c,a)−1)`). **Proposition C (⇒), core** (`propC_forward`): in an interval word, a flip whose segments carry pairwise distinct letters has a positive `3 × 3` minor, so `D_N`-flips change no distinct-letter triple shape |
| `Caterpillar/PropS.lean` | **Proposition S, decoding.** `prof_inj`: a binary word is fixed by its `z`-profile and its number of `x`'s. With the Lemma M profiles `N = j·prof ω₊ + (b−j)·prof ω₋` and `M(0)`: `N_eq` (explicit form), `propS_kind` (interior vs boundary), **`propS_interior`** (`N, M(0)` determine `Φ = (j,a′,c′,W)`), **`propS_boundary`** (`N` fixes the join word) |
| `Caterpillar/Words.lean` | `runSeq` (run collapse), `noAdj_runSeq`, `mem_runSeq`, `valid_runSeq`, and **`cat_of_word`**: every word over three letters that uses all three and is not an interval word (`¬ (runSeq w).Nodup`) has a caterpillar certificate |

**Scope.** Formalized:
- G3 in full, as a statement about bracketings (`g3_trees`). It combines Proposition E, Lemma Cat, Lemma R′ and the translation into trees.
- The octonion identities G3 uses: the Moufang identities that make `T₀` and `T₁` equal maps.
- Lemma W: the algebraic core and the expansion step (`lemmaW_expansion`).
- L1, context cancellation, from the division-algebra property (`context_cancel`, `flip_iff_assoc`).
- Artin's theorem and Lemma V (`artin`, `lemmaV_*`).
- K: specialisation and the restriction of (`D_N`-)flips (`kill_ev`, `kill_id`, `kill_DN`).
- G2, in part: Proposition T's count, Proposition C (⇒), Proposition S's decoding.

Not formalized (manuscript arguments in [THEOREM.md](../THEOREM.md), checked on bounded ranges in [`../prolog/g2.pl`](../prolog/g2.pl)):
- K's Moufang lift (a Moufang move of the image lifts to one of the word);
- Proposition T's classification (`Φ` constant on `D_N`-components and complete);
- Lemma M, the moment formula linking octonion maps to the profiles `N, M`;
- Proposition C (⇐), the induction on root splits.

The interval-word predicate is used in its run form (`runSeq w` has no repeated letter).
