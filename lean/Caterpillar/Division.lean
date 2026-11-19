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

private def normMulOk (i j k l : Idx) : Bool :=
  if ieq i j && ieq k l then true
  else if ieq (ixr i k) (ixr j l) then
    ieq (ixr j k) (ixr i l) && ((isgn i k != isgn j l) != (isgn j k != isgn i l))
  else
    !(ieq (ixr j k) (ixr i l))

private theorem normMulOk_b : allIdx4 normMulOk = true := rfl

private theorem toFin_inj {a b : Idx} (h : a.toFin = b.toFin) : a = b := by
  rw [← toIdx_toFin a, ← toIdx_toFin b, h]

private theorem ieq_iff (a b : Idx) : ieq a b = true ↔ a = b := by
  constructor
  · exact ieq_true
  · intro h; subst h; cases a <;> rfl

private theorem b2i_add_zero {x y : Bool} (h : (x != y) = true) : b2i x + b2i y = 0 := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem sum8_mul_r (f : Fin 8 → Int) (c : Int) : sum8 f * c = sum8 fun i => f i * c := by
  simp only [sum8, Int.add_mul]

private theorem sum8_unit_unit (p q : Fin 8) :
    (sum8 fun m => unit p m * unit q m) = if p = q then 1 else 0 := by
  rw [sum8_unit_mul p (unit q)]; rfl

private def nmF (i j k l : Fin 8) : Int := if bxr i k = bxr j l then bsgn i k * bsgn j l else 0
private def nmG (i j k l : Fin 8) : Int := if i = j ∧ k = l then 1 else 0

private theorem normMul_sgn (i j k l : Fin 8) :
    (nmF i j k l + nmF j i k l) + (nmF i j l k + nmF j i l k) =
    (nmG i j k l + nmG j i k l) + (nmG i j l k + nmG j i l k) := by
  have hok := allIdx4_spec normMulOk_b (toIdx i) (toIdx j) (toIdx k) (toIdx l)
  have hbxr : ∀ a b c d : Fin 8, bxr a b = bxr c d ↔ ixr (toIdx a) (toIdx b) = ixr (toIdx c) (toIdx d) := by
    intro a b c d; unfold bxr; exact ⟨toFin_inj, fun e => congrArg Idx.toFin e⟩
  have hsq : ∀ a b : Fin 8, bsgn a b * bsgn a b = 1 := by
    intro a b; unfold bsgn; rw [← b2i_xor]; cases isgn (toIdx a) (toIdx b) <;> rfl
  by_cases hij : i = j ∧ k = l
  · obtain ⟨rfl, rfl⟩ := hij
    simp only [nmF, nmG, and_self, ite_true, hsq]
  · have hG1 : nmG i j k l = 0 := by unfold nmG; simp only [hij, ite_false]
    have hG2 : nmG j i k l = 0 := by
      unfold nmG; have h' : ¬(j = i ∧ k = l) := fun h => hij ⟨h.1.symm, h.2⟩; simp only [h', ite_false]
    have hG3 : nmG i j l k = 0 := by
      unfold nmG; have h' : ¬(i = j ∧ l = k) := fun h => hij ⟨h.1, h.2.symm⟩; simp only [h', ite_false]
    have hG4 : nmG j i l k = 0 := by
      unfold nmG; have h' : ¬(j = i ∧ l = k) := fun h => hij ⟨h.1.symm, h.2.symm⟩; simp only [h', ite_false]
    rw [hG1, hG2, hG3, hG4]
    have hcond : (ieq (toIdx i) (toIdx j) && ieq (toIdx k) (toIdx l)) = false := by
      cases h1 : ieq (toIdx i) (toIdx j) <;> cases h2 : ieq (toIdx k) (toIdx l) <;> try rfl
      exfalso; apply hij
      have e1 := congrArg Idx.toFin (ieq_true h1)
      have e2 := congrArg Idx.toFin (ieq_true h2)
      rw [toFin_toIdx, toFin_toIdx] at e1 e2
      exact ⟨e1, e2⟩
    unfold normMulOk at hok
    rw [hcond] at hok
    simp only [Bool.false_eq_true, ite_false] at hok
    cases h1 : ieq (ixr (toIdx i) (toIdx k)) (ixr (toIdx j) (toIdx l))
    · rw [h1] at hok; simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true'] at hok
      have n1 : bxr i k ≠ bxr j l := fun e => by
        have := (ieq_iff _ _).2 ((hbxr i k j l).1 e); rw [h1] at this; exact Bool.false_ne_true this
      have n2 : bxr j k ≠ bxr i l := fun e => by
        have := (ieq_iff _ _).2 ((hbxr j k i l).1 e); rw [hok] at this; exact Bool.false_ne_true this
      have n1' : bxr j l ≠ bxr i k := Ne.symm n1
      have n2' : bxr i l ≠ bxr j k := Ne.symm n2
      simp only [nmF, n1, n2, n1', n2', ite_false]
    · rw [h1] at hok; simp only [ite_true, Bool.and_eq_true] at hok
      have e1 : bxr i k = bxr j l := (hbxr i k j l).2 (ieq_true h1)
      have e2 : bxr j k = bxr i l := (hbxr j k i l).2 (ieq_true hok.1)
      simp only [nmF, e1, e2, ite_true]
      have hz := b2i_add_zero hok.2
      have hpair : bsgn i k * bsgn j l + bsgn j k * bsgn i l = 0 := by
        simpa only [bsgn, b2i_xor] using hz
      have hpair2 : bsgn i l * bsgn j k + bsgn j l * bsgn i k = 0 := by
        rw [Int.mul_comm (bsgn i l), Int.mul_comm (bsgn j l), Int.add_comm]; exact hpair
      rw [hpair, hpair2]; rfl

/-- **Composition:** `N(ab) = N(a)N(b)`. -/
theorem norm_mul (a b : O) : nrm (mul a b) = nrm a * nrm b := by
  have hmul : ∀ m, mul a b m = sum8 fun i => sum8 fun k => a i * (b k * (bsgn i k * unit (bxr i k) m)) := by
    intro m
    have h : mul a b = osum8 fun k => osum8 fun i => smulO (a i * (b k * bsgn i k)) (unit (bxr i k)) := by
      conv => lhs; rw [decompO a, decompO b]
      simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
      funext x; simp only [osum8, smulO, sum8_mul_l]
      congr 1; funext k; congr 1; funext i; ac_rfl
    have := congrFun h m
    simp only [osum8, smulO] at this
    rw [this, sum8_swap]
    congr 1; funext i; congr 1; funext k; simp only [Int.mul_assoc]
  have hL : nrm (mul a b) =
      sum8 fun i => sum8 fun j => a i * (a j * (sum8 fun k => sum8 fun l => b k * (b l * nmF i j k l))) := by
    unfold nrm
    simp only [hmul, sum8_mul_r, sum8_mul_l]
    have pull_m : ∀ (F : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Fin 8 → Int),
        (sum8 fun m => sum8 fun i => sum8 fun k => sum8 fun j => sum8 fun l => F m i j k l) =
        (sum8 fun i => sum8 fun j => sum8 fun k => sum8 fun l => sum8 fun m => F m i j k l) := by
      intro F
      rw [sum8_swap]
      congr 1; funext i
      have s1 : (sum8 fun m => sum8 fun k => sum8 fun j => sum8 fun l => F m i j k l) =
                (sum8 fun k => sum8 fun m => sum8 fun j => sum8 fun l => F m i j k l) := sum8_swap _
      rw [s1]
      have s2 : (sum8 fun k => sum8 fun m => sum8 fun j => sum8 fun l => F m i j k l) =
                (sum8 fun k => sum8 fun j => sum8 fun m => sum8 fun l => F m i j k l) := by
        congr 1; funext k; exact sum8_swap _
      rw [s2, sum8_swap]
      congr 1; funext j; congr 1; funext k; exact sum8_swap _
    rw [pull_m]
    congr 1; funext i; congr 1; funext j; congr 1; funext k; congr 1; funext l
    have hinner : (sum8 fun m => a j * (b l * (bsgn j l * unit (bxr j l) m)) *
        (a i * (b k * (bsgn i k * unit (bxr i k) m)))) =
        a i * (a j * (b k * (b l * ((bsgn i k * bsgn j l) * (sum8 fun m => unit (bxr i k) m * unit (bxr j l) m))))) := by
      simp only [sum8_mul_l]
      congr 1; funext m; ac_rfl
    rw [hinner, sum8_unit_unit]
    unfold nmF
    by_cases h : bxr i k = bxr j l
    · simp only [h, ite_true, Int.mul_one]
    · simp only [h, ite_false, Int.mul_zero]
  have hR : nrm a * nrm b =
      sum8 fun i => sum8 fun j => a i * (a j * (sum8 fun k => sum8 fun l => b k * (b l * nmG i j k l))) := by
    have hdiag : ∀ x : O, nrm x = sum8 fun i => sum8 fun j => x i * (x j * (if i = j then 1 else 0)) := by
      intro x; unfold nrm; congr 1; funext i
      have h1 : (sum8 fun j => x i * (x j * (if i = j then 1 else 0))) =
                x i * (sum8 fun j => unit i j * x j) := by
        simp only [sum8_mul_l]; congr 1; funext j; simp only [unit]
        by_cases h : i = j
        · subst h; simp only [ite_true, Int.mul_one, Int.one_mul]
        · have hs : j ≠ i := Ne.symm h; simp only [h, hs, ite_false, Int.mul_zero, Int.zero_mul]
      rw [h1, sum8_unit_mul]
    rw [hdiag a, hdiag b, sum8_mul_r]
    congr 1; funext i; rw [sum8_mul_r]; congr 1; funext j
    simp only [sum8_mul_l]
    congr 1; funext k; congr 1; funext l
    unfold nmG
    by_cases hi : i = j <;> by_cases hk : k = l
    · simp only [hi, hk, and_self, ite_true, Int.mul_one, Int.mul_assoc]
    · simp only [hi, hk, and_false, ite_true, ite_false, Int.mul_zero]
    · simp only [hi, hk, false_and, ite_false, Int.mul_zero, Int.zero_mul]
    · simp only [hi, hk, and_self, ite_false, Int.mul_zero]
  rw [hL, hR]
  exact eq_of_sym2_2 a b nmF nmG normMul_sgn

/-- `(ab)·conj(ab) = N(a)N(b)·1` -/
theorem comp_one (a b : O) : mul (mul a b) (conj (mul a b)) = smul (nrm a * nrm b) one := by
  rw [mul_conj, norm_mul]

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
