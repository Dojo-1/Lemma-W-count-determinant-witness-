import Caterpillar.Closure

/-!
# Lemma W over the integers: rank 3 forces a nonzero associator

`lemmaW_expansion` works with truncated series `1 + s q + s² r + s³ t`. Over `ℤ` the truncation is a
congruence: put `s = M` and work modulo `M⁴`.

* `Cg D x y`: `x = y + D·z` for an integer octonion `z`. It is respected by products and differences.
* `tv_sm`: `tv(P)·tv(Q) ≡ tv(P·Q) (mod M⁴)`, where `tv(P) = P₀ + M P₁ + M² P₂ + M³ P₃`.
* `ev_cg`: under `ℓ ↦ 1 + M q_ℓ`, every bracketing is `tv` of its series, modulo `M⁴`.
* **`lemmaW_exists`**: if some count minor of `(A, B, C)` is nonzero, the integer valuation with
  `M = 2|det| + 1` gives a nonzero associator `[A, B, C]` (its `e₇` coordinate is `2 det M³ (mod M⁴)`).
  Every letter value has real part `1`, so it is nonzero and context cancellation applies.
* **`kerflip_dn`**: a flip that keeps the map is a `D_N`-flip, for **any** word.
-/

namespace WExist
open Caterpillar (Tree)
open Octonion

def Cg (D : Int) (x y : O) : Prop := ∃ z : O, x = oadd y (smul D z)

theorem cg_refl (D : Int) (x : O) : Cg D x x := ⟨zero, by funext k; simp [oadd, smul, zero]⟩

theorem cg_trans {D : Int} {x y u : O} (h1 : Cg D x y) (h2 : Cg D y u) : Cg D x u := by
  obtain ⟨z1, rfl⟩ := h1; obtain ⟨z2, rfl⟩ := h2
  exact ⟨oadd z2 z1, by funext k; simp only [oadd, smul, Int.mul_add]; omega⟩

theorem cg_mul {D : Int} {a a' b b' : O} (ha : Cg D a a') (hb : Cg D b b') : Cg D (mul a b) (mul a' b') := by
  obtain ⟨za, rfl⟩ := ha; obtain ⟨zb, rfl⟩ := hb
  refine ⟨oadd (oadd (mul za b') (mul a' zb)) (smul D (mul za zb)), ?_⟩
  simp only [add_mul, mul_add, smul_mul, mul_smul]
  funext k; simp only [oadd, smul, Int.mul_add]; omega

theorem cg_sub {D : Int} {a a' b b' : O} (ha : Cg D a a') (hb : Cg D b b') : Cg D (sub a b) (sub a' b') := by
  obtain ⟨za, rfl⟩ := ha; obtain ⟨zb, rfl⟩ := hb
  exact ⟨sub za zb, by funext k; simp only [oadd, smul, sub, Int.mul_sub]; omega⟩

/-- the series evaluated at `s = M` -/
def tv (M : Int) (s : Ser) : O :=
  oadd (oadd (oadd s.c0 (smul M s.c1)) (smul (M * M) s.c2)) (smul (M * M * M) s.c3)

theorem tv_sm (M : Int) (P Q : Ser) : Cg (M * M * M * M) (mul (tv M P) (tv M Q)) (tv M (sm P Q)) := by
  refine ⟨oadd (oadd (oadd (oadd (oadd (mul P.c1 Q.c3) (mul P.c3 Q.c1)) (mul P.c2 Q.c2))
    (smul M (mul P.c2 Q.c3))) (smul M (mul P.c3 Q.c2))) (smul (M * M) (mul P.c3 Q.c3)), ?_⟩
  simp only [tv, sm, add_mul, mul_add, smul_mul, mul_smul]
  funext k; simp only [oadd, smul, Int.mul_add, Int.mul_assoc]; omega

theorem tv_ssub (M : Int) (P Q : Ser) : tv M (ssub P Q) = sub (tv M P) (tv M Q) := by
  funext k; simp only [tv, ssub, oadd, smul, sub, Int.mul_sub]; omega

def zr : Nat → O := fun _ => zero

/-- the integer valuation `ℓ ↦ 1 + M q_ℓ` -/
def ρM (M : Int) (q : Nat → O) (ℓ : Nat) : O := tv M (subst q zr zr ℓ)

theorem ev_cg (w : Nat → Nat) (q : Nat → O) (M : Int) :
    ∀ T : Tree, Cg (M * M * M * M) (ev w (ρM M q) T) (tv M (val w q zr zr T))
  | .leaf _ => cg_refl _ _
  | .node l r => by
    simp only [ev, val]
    exact cg_trans (cg_mul (ev_cg w q M l) (ev_cg w q M r)) (tv_sm M _ _)

theorem count_eq (w : Nat → Nat) (ℓ : Nat) : ∀ T : Tree, count w ℓ T = cnt w ℓ T
  | .leaf _ => rfl
  | .node l r => by simp only [count, cnt, count_eq w ℓ l, count_eq w ℓ r]

theorem det_eq (w : Nat → Nat) (p q r : Nat) (A B C : Tree) :
    det3c (cvec w p q r A) (cvec w p q r B) (cvec w p q r C) = minor w A B C p q r := by
  simp [det3c, cvec, minor, count_eq]

/-- **Lemma W over ℤ.** A rank-3 triple has a nonzero associator at an integer valuation whose letter
values are all nonzero. -/
theorem lemmaW_exists (w : Nat → Nat) (A B C : Tree) (h : ¬ DN w A B C) :
    ∃ ρ : Nat → O, (∀ ℓ, ρ ℓ ≠ zero) ∧ assoc (ev w ρ A) (ev w ρ B) (ev w ρ C) ≠ zero := by
  obtain ⟨p, q, r, hm⟩ : ∃ p q r, minor w A B C p q r ≠ 0 := by
    apply Classical.byContradiction; intro hn; apply h; intro p q r
    apply Classical.byContradiction; intro hne; exact hn ⟨p, q, r, hne⟩
  generalize hd : minor w A B C p q r = d at hm
  let M : Int := ((2 * d.natAbs + 1 : Nat) : Int)
  have hM : M.natAbs = 2 * d.natAbs + 1 := Int.natAbs_ofNat _
  refine ⟨ρM M (qxyz p q r), ?_, ?_⟩
  · intro ℓ he
    have := congrFun he 0
    simp [ρM, tv, subst, zr, oadd, smul, zero, one, unit, qxyz, sp] at this
  · intro he
    -- the associator modulo `M⁴`
    have c1 := ev_cg w (qxyz p q r) M
    have key : Cg (M * M * M * M) (assoc (ev w (ρM M (qxyz p q r)) A) (ev w (ρM M (qxyz p q r)) B)
        (ev w (ρM M (qxyz p q r)) C)) (tv M (sassoc (val w (qxyz p q r) zr zr A) (val w (qxyz p q r) zr zr B)
        (val w (qxyz p q r) zr zr C))) := by
      simp only [assoc, sassoc, tv_ssub]
      exact cg_sub (cg_trans (cg_mul (cg_trans (cg_mul (c1 A) (c1 B)) (tv_sm M _ _)) (c1 C)) (tv_sm M _ _))
        (cg_trans (cg_mul (c1 A) (cg_trans (cg_mul (c1 B) (c1 C)) (tv_sm M _ _))) (tv_sm M _ _))
    obtain ⟨l0, l1, l2, l3⟩ := lemmaW_expansion w p q r zr zr A B C
    obtain ⟨z, hz⟩ := key
    rw [he] at hz
    have h7 := congrFun hz 7
    simp only [tv, oadd, smul, l0, l1, l2, l3, zero] at h7
    simp only [show ((7 : Fin 8).val = 7) from rfl, if_true, det_eq, hd] at h7
    -- `0 = M³ (2d + M z₇)`
    have hM0 : M ≠ 0 := by intro e; rw [e] at hM; simp at hM
    have e1 : M * (M * (M * (2 * d + M * z 7))) = 0 := by
      simp only [Int.mul_add, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_assoc] at h7 ⊢; omega
    have e2 : 2 * d + M * z 7 = 0 := by
      rcases Int.mul_eq_zero.1 e1 with e | e; · exact absurd e hM0
      rcases Int.mul_eq_zero.1 e with e | e; · exact absurd e hM0
      rcases Int.mul_eq_zero.1 e with e | e; · exact absurd e hM0
      exact e
    have e3 : (2 * d).natAbs = M.natAbs * (z 7).natAbs := by
      rw [← Int.natAbs_mul, show 2 * d = -(M * z 7) by omega, Int.natAbs_neg]
    have e4 : (2 * d).natAbs = 2 * d.natAbs := by rw [Int.natAbs_mul]; rfl
    rw [e4, hM] at e3
    rcases Nat.eq_zero_or_pos (z 7).natAbs with h0 | h0
    · rw [h0, Nat.mul_zero] at e3; exact hm (by omega)
    · have := Nat.le_mul_of_pos_right (2 * d.natAbs + 1) h0; omega

/-- **Map-preserving flips are `D_N`-flips**, for every word. -/
theorem kerflip_dn (w : Nat → Nat) {T U : Tree} (h : Closure.KerFlip w T U) : DNStep w T U := by
  obtain ⟨hf, he⟩ := h
  cases hf with
  | fwd c A B C =>
    by_cases hd : DN w A B C
    · exact DNStep.fwd c A B C hd
    · obtain ⟨ρ, hρ, hne⟩ := lemmaW_exists w A B C hd
      exact absurd ((flip_iff_assoc w ρ hρ c A B C).1 (he ρ)) hne
  | bwd c A B C =>
    by_cases hd : DN w A B C
    · exact DNStep.bwd c A B C hd
    · obtain ⟨ρ, hρ, hne⟩ := lemmaW_exists w A B C hd
      exact absurd ((flip_iff_assoc w ρ hρ c A B C).1 (he ρ).symm) hne

theorem kerreach_dn (w : Nat → Nat) {T U : Tree} (h : DReach (Closure.KerFlip w) T U) : DReach (DNStep w) T U := by
  induction h with
  | refl => exact DReach.refl _
  | tail _ st ih => exact DReach.tail ih (kerflip_dn w st)

end WExist
