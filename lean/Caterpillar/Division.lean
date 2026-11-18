import Caterpillar.LemmaW

/-!
# L1: 𝕆 is a division algebra, and context cancellation

* `norm_mul`: `N(ab) = N(a)N(b)` (composition algebra), via `x·x̄ = N(x)·1` and the polynomial identity
  `(ab)·conj(ab) = N(a)N(b)·1`.
* `mul_eq_zero`: no zero divisors. `mul_left_cancel` and `mul_right_cancel`: left and right
  multiplication by a nonzero octonion is injective.
* `val_ne_zero`: a bracketing of nonzero letter values is nonzero.
* **`context_cancel` (L1)**: for every valuation with nonzero letter values,
  `C[S₁] = C[S₂] ⟺ S₁ = S₂`, for every context `C`.
-/

namespace Octonion
open Caterpillar (Tree)

def nrm (a : O) : Int := sum8 fun i => a i * a i
def conj (a : O) : O := fun k => if k.val = 0 then a k else - a k
def smul (s : Int) (a : O) : O := fun k => s * a k

def conjP (P : OP) : OP := fun k => if k.val = 0 then P k else neg (P k)
def nrmP (P : OP) : Poly := psum8 fun i => pmul (P i) (P i)

theorem evalO_conjP (ρ : Nat → Int) (P : OP) : evalO ρ (conjP P) = conj (evalO ρ P) := by
  funext k; simp only [evalO, conjP, conj]; split <;> simp [evalP_neg]

theorem evalP_nrmP (ρ : Nat → Int) (P : OP) : evalP ρ (nrmP P) = nrm (evalO ρ P) := by
  unfold nrmP nrm; rw [evalP_psum8]; simp only [evalP_pmul]; rfl

/-- `x·x̄ = N(x)·1` -/
def nconjL : OP := mulP A (conjP A)
def nconjR : OP := fun k => if k.val = 0 then nrmP A else []
theorem nconj_all : ∀ k, idCheck1 nconjL nconjR k = true := by apply all8 <;> decide +kernel

/-- `(ab)·conj(ab) = N(a)N(b)·1` -/
def compL : OP := mulP (mulP A B) (conjP (mulP A B))
def compR : OP := fun k => if k.val = 0 then pmul (nrmP A) (nrmP B) else []
theorem comp_c0 : idCheck1 compL compR 0 = true := by decide +kernel
theorem comp_c1 : idCheck1 compL compR 1 = true := by decide +kernel
theorem comp_c2 : idCheck1 compL compR 2 = true := by decide +kernel
theorem comp_c3 : idCheck1 compL compR 3 = true := by decide +kernel
theorem comp_c4 : idCheck1 compL compR 4 = true := by decide +kernel
theorem comp_c5 : idCheck1 compL compR 5 = true := by decide +kernel
theorem comp_c6 : idCheck1 compL compR 6 = true := by decide +kernel
theorem comp_c7 : idCheck1 compL compR 7 = true := by decide +kernel
theorem comp_all : ∀ k, idCheck1 compL compR k = true :=
  all8 comp_c0 comp_c1 comp_c2 comp_c3 comp_c4 comp_c5 comp_c6 comp_c7

theorem evalO_scalar0 (ρ : Nat → Int) (p : Poly) :
    evalO ρ (fun k => if k.val = 0 then p else []) = smul (evalP ρ p) one := by
  funext k; simp only [evalO, smul, one, unit]; split <;> rename_i h
  · simp [Fin.ext_iff, h]
  · simp [evalP, Fin.ext_iff, h]

theorem mul_conj (a : O) : mul a (conj a) = smul (nrm a) one := by
  have := eq_of_idCheck1 (val3 a a a) _ _ nconj_all
  have e : evalO (val3 a a a) nconjR = smul (nrm a) one := by
    unfold nconjR; rw [evalO_scalar0, evalP_nrmP]; simp only [A, evalO_var0]
  rw [e] at this
  simpa only [nconjL, evalO_mulP, evalO_conjP, A, evalO_var0] using this

theorem comp_one (a b : O) : mul (mul a b) (conj (mul a b)) = smul (nrm a * nrm b) one := by
  have := eq_of_idCheck1 (val3 a b b) _ _ comp_all
  have e : evalO (val3 a b b) compR = smul (nrm a * nrm b) one := by
    unfold compR; rw [evalO_scalar0, evalP_pmul, evalP_nrmP, evalP_nrmP]
    simp only [A, B, evalO_var0, evalO_var8]
  rw [e] at this
  simpa only [compL, evalO_mulP, evalO_conjP, A, B, evalO_var0, evalO_var8] using this

/-- **Composition:** `N(ab) = N(a)N(b)`. -/
theorem norm_mul (a b : O) : nrm (mul a b) = nrm a * nrm b := by
  have h1 := congrFun (mul_conj (mul a b)) 0
  have h2 := congrFun (comp_one a b) 0
  rw [h1] at h2
  simpa [smul, one, unit] using h2

theorem sq_nonneg' (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    simpa [Int.neg_mul_neg] using this

theorem nrm_eq_zero (a : O) (h : nrm a = 0) : a = zero := by
  have s : ∀ i, 0 ≤ a i * a i := fun i => sq_nonneg' (a i)
  have := s 0; have := s 1; have := s 2; have := s 3; have := s 4; have := s 5; have := s 6; have := s 7
  simp only [nrm, sum8] at h
  have all : a 0 * a 0 = 0 ∧ a 1 * a 1 = 0 ∧ a 2 * a 2 = 0 ∧ a 3 * a 3 = 0 ∧ a 4 * a 4 = 0 ∧
      a 5 * a 5 = 0 ∧ a 6 * a 6 = 0 ∧ a 7 * a 7 = 0 := by omega
  have key : ∀ i : Fin 8, a i * a i = 0 := by
    intro i
    match i with
    | ⟨0, _⟩ => exact all.1 | ⟨1, _⟩ => exact all.2.1 | ⟨2, _⟩ => exact all.2.2.1
    | ⟨3, _⟩ => exact all.2.2.2.1 | ⟨4, _⟩ => exact all.2.2.2.2.1 | ⟨5, _⟩ => exact all.2.2.2.2.2.1
    | ⟨6, _⟩ => exact all.2.2.2.2.2.2.1 | ⟨7, _⟩ => exact all.2.2.2.2.2.2.2
  funext i
  rcases Int.mul_eq_zero.1 (key i) with h | h <;> simpa [zero] using h

/-- **No zero divisors.** -/
theorem mul_eq_zero (a b : O) (h : mul a b = zero) : a = zero ∨ b = zero := by
  have hn : nrm (mul a b) = 0 := by rw [h]; simp [nrm, sum8, zero]
  rw [norm_mul] at hn
  rcases Int.mul_eq_zero.1 hn with h1 | h1
  · exact Or.inl (nrm_eq_zero a h1)
  · exact Or.inr (nrm_eq_zero b h1)

def negO (a : O) : O := fun k => - a k

theorem mul_neg_right (a b : O) : mul a (negO b) = negO (mul a b) := by
  funext k; simp only [mul, negO, sum8]; simp only [Int.mul_neg]; omega

theorem mul_neg_left (a b : O) : mul (negO a) b = negO (mul a b) := by
  funext k; simp only [mul, negO, sum8]; simp only [Int.mul_neg, Int.neg_mul]; omega

theorem sub_eq_add_neg (b c : O) : sub b c = oadd b (negO c) := by
  funext k; simp only [sub, oadd, negO]; omega

theorem sub_eq_zero (b c : O) : sub b c = zero ↔ b = c := by
  constructor
  · intro h; funext k; have := congrFun h k; simp [sub, zero] at this; omega
  · intro h; subst h; funext k; simp [sub, zero]

/-- left multiplication by a nonzero octonion is injective -/
theorem mul_left_cancel (a b c : O) (ha : a ≠ zero) (h : mul a b = mul a c) : b = c := by
  have : mul a (sub b c) = zero := by
    rw [sub_eq_add_neg, mul_add, mul_neg_right, h, ← sub_eq_add_neg]; exact (sub_eq_zero _ _).2 rfl
  rcases mul_eq_zero a (sub b c) this with h1 | h1
  · exact absurd h1 ha
  · exact (sub_eq_zero b c).1 h1

theorem mul_right_cancel (a b c : O) (ha : a ≠ zero) (h : mul b a = mul c a) : b = c := by
  have : mul (sub b c) a = zero := by
    rw [sub_eq_add_neg, add_mul, mul_neg_left, h, ← sub_eq_add_neg]; exact (sub_eq_zero _ _).2 rfl
  rcases mul_eq_zero (sub b c) a this with h1 | h1
  · exact (sub_eq_zero b c).1 h1
  · exact absurd h1 ha

/-! ## Bracketings and contexts -/

/-- the value of a bracketing when letter `ℓ` takes the value `ρ ℓ` -/
def ev (w : Nat → Nat) (ρ : Nat → O) : Tree → O
  | .leaf i => ρ (w i)
  | .node l r => mul (ev w ρ l) (ev w ρ r)

theorem val_ne_zero (w : Nat → Nat) (ρ : Nat → O) (hρ : ∀ ℓ, ρ ℓ ≠ zero) : ∀ T, ev w ρ T ≠ zero
  | .leaf i => hρ (w i)
  | .node l r => by
    intro h
    rcases mul_eq_zero _ _ h with h1 | h1
    · exact val_ne_zero w ρ hρ l h1
    · exact val_ne_zero w ρ hρ r h1

/-- a bracketing with a hole -/
inductive Ctx
  | hole
  | inL (c : Ctx) (r : Tree)
  | inR (l : Tree) (c : Ctx)

def fill : Ctx → Tree → Tree
  | .hole, S => S
  | .inL c r, S => .node (fill c S) r
  | .inR l c, S => .node l (fill c S)

/-- **L1 (context cancellation).** For every valuation with nonzero letter values,
`C[S₁] = C[S₂] ⟺ S₁ = S₂`. -/
theorem context_cancel (w : Nat → Nat) (ρ : Nat → O) (hρ : ∀ ℓ, ρ ℓ ≠ zero) :
    ∀ (c : Ctx) (S1 S2 : Tree), ev w ρ (fill c S1) = ev w ρ (fill c S2) ↔ ev w ρ S1 = ev w ρ S2
  | .hole, _, _ => Iff.rfl
  | .inL c r, S1, S2 => by
    simp only [fill, ev]
    rw [← context_cancel w ρ hρ c S1 S2]
    exact ⟨mul_right_cancel _ _ _ (val_ne_zero w ρ hρ r), fun h => by rw [h]⟩
  | .inR l c, S1, S2 => by
    simp only [fill, ev]
    rw [← context_cancel w ρ hρ c S1 S2]
    exact ⟨mul_left_cancel _ _ _ (val_ne_zero w ρ hρ l), fun h => by rw [h]⟩

/-- **L1, edge form.** A flip `(AB)C → A(BC)` inside a context changes the value of the whole
bracketing iff the local associator is nonzero (for nonzero letter values). -/
theorem flip_iff_assoc (w : Nat → Nat) (ρ : Nat → O) (hρ : ∀ ℓ, ρ ℓ ≠ zero) (c : Ctx) (TA TB TC : Tree) :
    ev w ρ (fill c (.node (.node TA TB) TC)) = ev w ρ (fill c (.node TA (.node TB TC))) ↔
      assoc (ev w ρ TA) (ev w ρ TB) (ev w ρ TC) = zero := by
  rw [context_cancel w ρ hρ c]
  simp only [ev, assoc]
  exact (sub_eq_zero _ _).symm

end Octonion
