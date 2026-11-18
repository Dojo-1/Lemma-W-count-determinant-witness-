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
| `Caterpillar/Words.lean` | `runSeq` (run collapse), `noAdj_runSeq`, `mem_runSeq`, `valid_runSeq`, and **`cat_of_word`**: every word over three letters that uses all three and is not an interval word (`¬ (runSeq w).Nodup`) has a caterpillar certificate |

**Scope.** G3 is formalized in full, as a statement about bracketings (`Caterpillar.g3_trees`):
- Proposition E;
- Lemma Cat;
- Lemma R′;
- the translation into trees.

What remains outside Lean is octonion algebra:
- the Moufang identities hold in 𝕆, so `T₀` and `T₁` are equal maps;
- Lemma W: a rank-3 local associator is nonzero, so in-class flips are `D_N`-flips;
- killing letters (K) and G2.

These are manuscript arguments in [THEOREM.md](../THEOREM.md). The interval-word predicate is used in its run form (`runSeq w` has no repeated letter).
