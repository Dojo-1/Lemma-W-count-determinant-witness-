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
| `Caterpillar/Words.lean` | `runSeq` (run collapse), `noAdj_runSeq`, `mem_runSeq`, `valid_runSeq`, and **`cat_of_word`**: every word over three letters that uses all three and is not an interval word (`¬ (runSeq w).Nodup`) has a caterpillar certificate |

**Scope.** Formalized:
- the run-sequence combinatorics and the finite base;
- the induction step of Proposition E;
- Lemma Cat in full (laminarity classification plus determinants), at the level of position intervals;
- Lemma R′ on planar binary trees.

Not formalized:
- **The translation step.** Turning a run-level certificate (`Cat`) into a position-level chain (`PChain`), a tree `T₀` that contains it, and the Moufang image `T₁`. It is constructive and written out in `src/caterpillar.py` (`build`), but not yet in Lean.
- **The octonion facts:** Lemma W, the Moufang identities, killing (K), and G2. These stay manuscript arguments in [THEOREM.md](../THEOREM.md).

The interval-word predicate is used in its run form ("each letter forms one run" ⇔ `runSeq w` has no
repeated letter).
