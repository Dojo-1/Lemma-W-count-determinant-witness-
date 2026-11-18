import Caterpillar.Octonion
import Caterpillar.RPrime

/-!
# Lemma W: the expansion step

Letters are mapped to truncated power series `1 + s·q + s²·r + s³·t` with octonion coefficients. The
chosen letters `x, y, z` get `q = e₁, e₂, e₄`, every other letter gets `q = 0`, and the higher
coefficients `r, t` are arbitrary. This covers `x ↦ exp(θ q)`: the argument is ring-theoretic and runs
verbatim over `ℚ`, where `exp(θq) = 1 + θq + θ²q²/2 + θ³q³/6 + …`.

* `val_coeff0`, `val_coeff1`: every bracketing evaluates to `1 + s·Σ + O(s²)`, where `Σ` is the
  count-weighted sum of the letters' linear terms, whatever the bracketing.
* `sassoc_low`, `sassoc_three`: for three such series, the associator has no `s⁰, s¹, s²` terms, and its
  `s³` coefficient is `[P₁, Q₁, R₁]`.
* **`lemmaW_expansion`**: the `s³` coefficient of the local associator `[A, B, C]` of any three
  bracketings is `det(N_xyz) · [e₁, e₂, e₄] = 2·det(N_xyz)·e₇`. So it is nonzero when `rank N = 3`.
-/

namespace Octonion
open Caterpillar (Tree)

def oadd (a b : O) : O := fun k => a k + b k
def one : O := unit 0
def zero : O := fun _ => 0

def addP (P Q : OP) : OP := fun k => P k ++ Q k
def oneP : OP := fun k => if k.val = 0 then [(1, [])] else []

theorem evalO_addP (ρ : Nat → Int) (P Q : OP) : evalO ρ (addP P Q) = oadd (evalO ρ P) (evalO ρ Q) := by
  funext k; simp [evalO, addP, oadd, evalP_append]

theorem evalO_oneP (ρ : Nat → Int) : evalO ρ oneP = one := by
  funext k; simp only [evalO, oneP, one, unit]; split <;> rename_i h
  · simp [evalP, evalM, Fin.ext_iff, h]
  · simp [evalP, Fin.ext_iff, h]

/-! ## Bilinearity and unit, as polynomial identities -/

def mulOneL : OP := mulP A oneP
def oneMulL : OP := mulP oneP A
def distL_L : OP := mulP (addP A B) C
def distL_R : OP := addP (mulP A C) (mulP B C)
def distR_L : OP := mulP A (addP B C)
def distR_R : OP := addP (mulP A B) (mulP A C)

theorem mulOne_all : ∀ k, idCheck1 mulOneL A k = true := by apply all8 <;> decide +kernel
theorem oneMul_all : ∀ k, idCheck1 oneMulL A k = true := by apply all8 <;> decide +kernel
theorem distL_all : ∀ k, idCheck1 distL_L distL_R k = true := by apply all8 <;> decide +kernel
theorem distR_all : ∀ k, idCheck1 distR_L distR_R k = true := by apply all8 <;> decide +kernel

theorem mul_one (a : O) : mul a one = a := by
  have := eq_of_idCheck1 (val3 a a a) _ _ mulOne_all
  simpa only [mulOneL, evalO_mulP, evalO_oneP, A, evalO_var0] using this

theorem one_mul (a : O) : mul one a = a := by
  have := eq_of_idCheck1 (val3 a a a) _ _ oneMul_all
  simpa only [oneMulL, evalO_mulP, evalO_oneP, A, evalO_var0] using this

theorem add_mul (a b c : O) : mul (oadd a b) c = oadd (mul a c) (mul b c) := by
  have := eq_of_idCheck1 (val3 a b c) _ _ distL_all
  simpa only [distL_L, distL_R, evalO_mulP, evalO_addP, A, B, C, evalO_var0, evalO_var8, evalO_var16] using this

theorem mul_add (a b c : O) : mul a (oadd b c) = oadd (mul a b) (mul a c) := by
  have := eq_of_idCheck1 (val3 a b c) _ _ distR_all
  simpa only [distR_L, distR_R, evalO_mulP, evalO_addP, A, B, C, evalO_var0, evalO_var8, evalO_var16] using this

/-! ## Truncated series `c₀ + c₁s + c₂s² + c₃s³` -/

structure Ser where
  c0 : O
  c1 : O
  c2 : O
  c3 : O

def sm (P Q : Ser) : Ser where
  c0 := mul P.c0 Q.c0
  c1 := oadd (mul P.c0 Q.c1) (mul P.c1 Q.c0)
  c2 := oadd (oadd (mul P.c0 Q.c2) (mul P.c1 Q.c1)) (mul P.c2 Q.c0)
  c3 := oadd (oadd (oadd (mul P.c0 Q.c3) (mul P.c1 Q.c2)) (mul P.c2 Q.c1)) (mul P.c3 Q.c0)

def ssub (P Q : Ser) : Ser := ⟨sub P.c0 Q.c0, sub P.c1 Q.c1, sub P.c2 Q.c2, sub P.c3 Q.c3⟩

/-- the associator of series -/
def sassoc (P Q R : Ser) : Ser := ssub (sm (sm P Q) R) (sm P (sm Q R))

/-- **No `s⁰, s¹, s²` terms.** -/
theorem sassoc_low (P Q R : Ser) (hP : P.c0 = one) (hQ : Q.c0 = one) (hR : R.c0 = one) :
    (sassoc P Q R).c0 = zero ∧ (sassoc P Q R).c1 = zero ∧ (sassoc P Q R).c2 = zero := by
  simp only [sassoc, ssub, sm, hP, hQ, hR, mul_one, one_mul, add_mul, mul_add]
  refine ⟨?_, ?_, ?_⟩ <;> funext k <;> simp only [sub, oadd, zero] <;> omega

/-- **The `s³` coefficient is `[P₁, Q₁, R₁]`.** -/
theorem sassoc_three (P Q R : Ser) (hP : P.c0 = one) (hQ : Q.c0 = one) (hR : R.c0 = one) :
    (sassoc P Q R).c3 = assoc P.c1 Q.c1 R.c1 := by
  simp only [sassoc, ssub, sm, hP, hQ, hR, mul_one, one_mul, add_mul, mul_add, assoc]
  funext k; simp only [sub, oadd]; omega

/-! ## Bracketings under the substitution -/

/-- the substitution: letter `ℓ ↦ 1 + s·q ℓ + s²·r ℓ + s³·t ℓ` -/
def subst (q r t : Nat → O) (ℓ : Nat) : Ser := ⟨one, q ℓ, r ℓ, t ℓ⟩

def val (w : Nat → Nat) (q r t : Nat → O) : Tree → Ser
  | .leaf i => subst q r t (w i)
  | .node l r' => sm (val w q r t l) (val w q r t r')

/-- the linear term: count-weighted sum of the letters' `q` -/
def lin (w : Nat → Nat) (q : Nat → O) : Tree → O
  | .leaf i => q (w i)
  | .node l r => oadd (lin w q l) (lin w q r)

theorem val_coeff0 (w : Nat → Nat) (q r t : Nat → O) : ∀ T : Tree, (val w q r t T).c0 = one
  | .leaf _ => rfl
  | .node l r' => by simp only [val, sm]; rw [val_coeff0 w q r t l, val_coeff0 w q r t r', mul_one]

theorem val_coeff1 (w : Nat → Nat) (q r t : Nat → O) : ∀ T : Tree, (val w q r t T).c1 = lin w q T
  | .leaf _ => rfl
  | .node l r' => by
    simp only [val, sm, lin]
    rw [val_coeff0 w q r t l, val_coeff0 w q r t r', one_mul, mul_one, val_coeff1 w q r t l,
      val_coeff1 w q r t r']
    funext k; simp only [oadd]; omega

/-- linear terms for the chosen letters `x, y, z`: `e₁, e₂, e₄`; all other letters `0` -/
def qxyz (lx ly lz : Nat) (ℓ : Nat) : O :=
  sp (fun j => if j.val = 0 then (if ℓ = lx then 1 else 0) else if j.val = 1 then (if ℓ = ly then 1 else 0)
    else if j.val = 2 then (if ℓ = lz then 1 else 0) else 0)

/-- number of leaves of `T` carrying letter `ℓ` -/
def count (w : Nat → Nat) (ℓ : Nat) : Tree → Int
  | .leaf i => if w i = ℓ then 1 else 0
  | .node l r => count w ℓ l + count w ℓ r

/-- the count vector of `T` on the chosen letters, in coordinates `0, 1, 2` -/
def cvec (w : Nat → Nat) (lx ly lz : Nat) (T : Tree) : O :=
  fun j => if j.val = 0 then count w lx T else if j.val = 1 then count w ly T
    else if j.val = 2 then count w lz T else 0

theorem lin_eq (w : Nat → Nat) (lx ly lz : Nat) : ∀ T : Tree,
    lin w (qxyz lx ly lz) T = sp (cvec w lx ly lz T)
  | .leaf i => by
    funext k; simp only [lin, qxyz, sp, cvec, count]
    repeat (first | split | simp_all [eq_comm])
  | .node l r => by
    simp only [lin]; rw [lin_eq w lx ly lz l, lin_eq w lx ly lz r]
    funext k; simp only [oadd, sp, cvec, count]
    split <;> (try split) <;> (try split) <;> omega

/-- **Lemma W, expansion step.** For any bracketings `A, B, C` (of consecutive segments of `w`) and any
higher-order terms `r, t`, the local associator `[A, B, C]` has no terms below `s³`, and its `s³`
coefficient is `det(N_xyz)·[e₁, e₂, e₄]`, i.e. `2·det(N_xyz)` on `e₇` and `0` elsewhere. -/
theorem lemmaW_expansion (w : Nat → Nat) (lx ly lz : Nat) (r t : Nat → O) (TA TB TC : Tree) :
    let P := val w (qxyz lx ly lz) r t TA
    let Q := val w (qxyz lx ly lz) r t TB
    let R := val w (qxyz lx ly lz) r t TC
    (sassoc P Q R).c0 = zero ∧ (sassoc P Q R).c1 = zero ∧ (sassoc P Q R).c2 = zero ∧
    (sassoc P Q R).c3 = fun k => if k.val = 7 then
      2 * det3c (cvec w lx ly lz TA) (cvec w lx ly lz TB) (cvec w lx ly lz TC) else 0 := by
  intro P Q R
  have h0 := val_coeff0 w (qxyz lx ly lz) r t
  obtain ⟨l0, l1, l2⟩ := sassoc_low P Q R (h0 TA) (h0 TB) (h0 TC)
  refine ⟨l0, l1, l2, ?_⟩
  rw [sassoc_three P Q R (h0 TA) (h0 TB) (h0 TC)]
  simp only [P, Q, R, val_coeff1, lin_eq]
  exact lemmaW_span _ _ _

end Octonion
