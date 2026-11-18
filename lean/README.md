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
| `Caterpillar/Words.lean` | `runSeq` (run collapse), `noAdj_runSeq`, `mem_runSeq`, `valid_runSeq`, and **`cat_of_word`**: every word over three letters that uses all three and is not an interval word (`¬ (runSeq w).Nodup`) has a caterpillar certificate |

**Scope.** Formalized: the run-sequence combinatorics, the finite base, the induction step of Proposition E,
and the determinant arithmetic of Lemma Cat.

Not formalized; these stay manuscript arguments in [THEOREM.md](../THEOREM.md):
- the laminarity classification in Lemma Cat, i.e. that every rotation that could delete a node of `S`
  has the two-single-letter shape;
- Lemma R′;
- the octonion facts: Lemma W, the Moufang identities, killing (K), and G2.

The interval-word predicate is used in its run form ("each letter forms one run" ⇔ `runSeq w` has no
repeated letter).
