import Spec

/-!
# Statements of Record (`Challenge`)

This file is the **trusted challenge** verified by `lake comparator --paranoid` against `Solution.lean`.
It imports **only** `Spec` (zero imports from the proof library `Caterpillar/`).

Every theorem below is checked for exact statement and definition identity against `Solution.lean`,
restricted to the standard axioms `propext`, `Quot.sound`, and `Classical.choice`, and replayed
through all six bundled kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`,
`con-ron`).

In addition to the main mathematical theorems, this file includes **algebraic and non-vacuity anchors**:
* `octonion_unital` + `octonion_norm_mul` + `octonion_non_associative`: by Hurwitz's theorem, an
  8-dimensional unital composition algebra is uniquely the octonions (ruling out typos in `sgnT`).
* `kerconn_two_letters_example`, `kerconn_interval_example`, and `not_kerconn_example`: witness
  that both the connected and disconnected sides of `main` are non-empty.
* `bell_small_values` and `disconnected_count_four_five`: anchor the combinatorial count.
-/

namespace Challenge
open Spec

/-! ## Headline mathematical theorems -/

/-- **Main theorem.** Every kernel class of octonion bracketings of `wl` is flip-connected
if and only if `wl` has at most two distinct letters or every letter occupies one contiguous run. -/
theorem main (wl : List Nat) :
    KerConn (wd wl) wl.length ↔ TwoLetters wl ∨ Interval wl := by
  sorry

/-- **The Bell-number count.** Among the `Bell(n)` canonical words of length `n = m + 1 ≥ 1`,
exactly `Bell(n) − 2ⁿ + n` have a disconnected kernel class. -/
theorem count_disconnected (m : Nat) :
    ((rgs (m + 1)).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length
      + 2 ^ (m + 1) = bell (m + 1) + (m + 1) := by
  sorry

/-- **Canonical representatives.** Every word is an injective renaming of a unique restricted
growth string of the same length. -/
theorem canonical (w : List Nat) :
    ∃ v ∈ rgs w.length, Renaming w v ∧ ∀ v' ∈ rgs w.length, Renaming w v' → v' = v := by
  sorry

/-- Restricted growth strings of length `n` are pairwise distinct. -/
theorem rgs_nodup (n : Nat) : (rgs n).Nodup := by
  sorry

/-- Flip-connectivity of kernel classes is invariant under injective renaming of letters. -/
theorem kerconn_rename (w v : List Nat) (hr : Renaming w v) :
    KerConn (wd w) w.length ↔ KerConn (wd v) v.length := by
  sorry

/-- **Stirling recurrence** `S(n+1, k+1) = (k+1)·S(n, k+1) + S(n, k)` for `n = m + 1 ≥ 1`. -/
theorem stirling_rec (m k : Nat) :
    stirling (m + 2) (k + 1) = (k + 1) * stirling (m + 1) (k + 1) + 1 * stirling (m + 1) k := by
  sorry

/-- **Bell sum** `Bell(n) = Σ_{k ≤ n} S(n, k)`. -/
theorem bell_eq_sum (n : Nat) : bell n = ssum (stirling n) (n + 1) := by
  sorry

/-- **Lemma W over `ℤ`.** Any rank-3 triple `(A, B, C)` has a nonzero associator at an integer
octonion valuation whose letter values are all nonzero. -/
theorem lemmaW_exists (w : Nat → Nat) (A B C : Tree) (h : ¬ DN w A B C) :
    ∃ ρ : Nat → O, (∀ ℓ, ρ ℓ ≠ zero) ∧ assoc (ev w ρ A) (ev w ρ B) (ev w ρ C) ≠ zero := by
  sorry

/-- **One-way inclusion `E_id ⊆ E(D_N)`.** Every map-preserving flip has count matrix of rank ≤ 2. -/
theorem kerflip_dn (w : Nat → Nat) {T U : Tree} (h : KerFlip w T U) : DNStep w T U := by
  sorry

/-! ## Algebraic integrity and non-vacuity anchors -/

/-- `one = e₀` is a two-sided multiplicative identity on `O`. -/
theorem octonion_unital (a : O) : mul one a = a ∧ mul a one = a := by
  sorry

/-- **Composition algebra (Hurwitz anchor):** `N(ab) = N(a) N(b)` on `Fin 8 → Int`. -/
theorem octonion_norm_mul (a b : O) : nrm (mul a b) = nrm a * nrm b := by
  sorry

/-- **Non-associativity witness:** `[e₁, e₂, e₄] ≠ 0`. -/
theorem octonion_non_associative : assoc (unit 1) (unit 2) (unit 4) ≠ zero := by
  sorry

/-- **Moufang identities** (left, right, middle) hold identically on `O`. -/
theorem octonion_moufang (a b c : O) :
    mul a (mul b (mul a c)) = mul (mul (mul a b) a) c ∧
    mul (mul (mul c a) b) a = mul c (mul a (mul b a)) ∧
    mul (mul a b) (mul c a) = mul a (mul (mul b c) a) := by
  sorry

/-- Non-vacuity witness: a non-interval 2-letter word (`xyxy`) is flip-connected. -/
theorem kerconn_two_letters_example : KerConn (wd [0, 1, 0, 1]) 4 := by
  sorry

/-- Non-vacuity witness: a 3-letter interval word (`xxyz`) is flip-connected. -/
theorem kerconn_interval_example : KerConn (wd [0, 0, 1, 2]) 4 := by
  sorry

/-- Non-vacuity witness: a 4-letter non-interval 3-letter word (`xyzx`) has a disconnected class. -/
theorem not_kerconn_example : ¬ KerConn (wd [0, 1, 2, 0]) 4 := by
  sorry

/-- Anchor values of `bell` for `n = 0, …, 5`. -/
theorem bell_small_values : (List.range 6).map bell = [1, 1, 2, 5, 15, 52] := by
  sorry

/-- Concrete disconnected-word counts at `n = 4` (`3`) and `n = 5` (`25`). -/
theorem disconnected_count_four_five :
    ((rgs 4).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length = 3 ∧
    ((rgs 5).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length = 25 := by
  sorry

end Challenge
