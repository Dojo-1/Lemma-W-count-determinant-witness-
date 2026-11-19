import Caterpillar.Coeff

/-!
# Proposition S: from the linear moments to the profiles

For a word `ω` in `x, z` with `n` x's, put `u = 2m + 1` and evaluate the `t`-linear moments
homogeneously: `Φ_ω(m) = Σ_p S(ω, p, 1) mᵖ (m+1)^{n−p}`. Then (`Phi_eq`)

  `Φ_ω(m) = Σ_{z ∈ ω} u^{#x before z} = Σ_α N_ω(α) uᵅ`,

the homogeneous form of `Σ_z (1+s)^{α_z}(1−s)^{n−α_z}` at `s = m/(m+1)`. Symmetrically (`Phi'_eq`) the
`s`-linear moments give `Σ_{x ∈ ω} u^{#z after x}`, whose top base-`u` digit is the number of leading
x's, `M(0)`. With `u` larger than twice every digit, the digits are unique: the linear moments determine
the profile `N` and `M(0)` (`profiles_of_moments`).
-/

namespace Profiles
open Caterpillar (Tree)
open Octonion LemmaM Coeff

/-- `Σ_{p ≤ N} f p · mᵖ (m+1)^{N−p}` -/
def hs (m : Int) (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | N + 1 => f 0 * ipow (m + 1) (N + 1) + m * hs m (fun p => f (p + 1)) N

theorem hs_add (m : Int) : ∀ N (f g : Nat → Int), hs m (fun p => f p + g p) N = hs m f N + hs m g N
  | 0, _, _ => rfl
  | N + 1, f, g => by simp only [hs, hs_add m N (fun p => f (p + 1)) (fun p => g (p + 1)), Int.add_mul, Int.mul_add]; omega

theorem hs_smul (m s : Int) : ∀ N (f : Nat → Int), hs m (fun p => s * f p) N = s * hs m f N
  | 0, _ => rfl
  | N + 1, f => by
    simp only [hs, hs_smul m s N (fun p => f (p + 1)), Int.mul_add]
    rw [Int.mul_assoc, Int.mul_left_comm m s]

theorem hs_congr (m : Int) : ∀ N (f g : Nat → Int), (∀ p ≤ N, f p = g p) → hs m f N = hs m g N
  | 0, f, g, h => h 0 (Nat.le_refl 0)
  | N + 1, f, g, h => by
    simp only [hs, h 0 (by omega), hs_congr m N (fun p => f (p + 1)) (fun p => g (p + 1)) (fun p hp => h _ (by omega))]

/-- shifting the coefficients up multiplies by `m` -/
theorem hs_shift (m : Int) (N : Nat) (f : Nat → Int) :
    hs m (fun p => match p with | 0 => 0 | p' + 1 => f p') (N + 1) = m * hs m f N := by
  simp only [hs]; simp

/-- raising the degree with a zero top coefficient multiplies by `m + 1` -/
theorem hs_ext (m : Int) : ∀ N (f : Nat → Int), f (N + 1) = 0 → hs m f (N + 1) = (m + 1) * hs m f N
  | 0, f, h => by simp only [hs, h, ipow]; rw [Int.mul_zero, Int.add_zero, Int.one_mul, Int.mul_comm]
  | N + 1, f, h => by
    rw [hs, hs_ext m N (fun p => f (p + 1)) h, hs]
    rw [show ipow (m + 1) (N + 1 + 1) = ipow (m + 1) (N + 1) * (m + 1) from rfl, Int.mul_add (m + 1)]
    ac_rfl

/-! ## `Ssum` -/

theorem Ssum_vanish : ∀ (ω : List Bool) (p r : Nat), (ω.count true < p ∨ ω.count false < r) → Ssum ω p r = 0
  | [], p, r, h => by simp at h; simp only [Ssum]; rw [ite_eq_right (by omega)]
  | true :: ω, p, r, h => by
    simp only [List.count_cons_self, List.count_cons, beq_iff_eq, reduceCtorEq, ite_false,
      Nat.add_zero] at h
    simp only [Ssum, Ssum_vanish ω p r (by omega)]
    cases p with
    | zero => rfl
    | succ p => simp only [Ssum_vanish ω p r (by omega)]; rfl
  | false :: ω, p, r, h => by
    simp only [List.count_cons_self, List.count_cons, Bool.false_eq_true, beq_iff_eq, ite_false,
      Nat.add_zero] at h
    simp only [Ssum, Ssum_vanish ω p r (by omega)]
    cases r with
    | zero => rfl
    | succ r => simp only [Ssum_vanish ω p r (by omega)]; simp

theorem cT (ω : List Bool) : (true :: ω).count true = ω.count true + 1 := by simp
theorem cF (ω : List Bool) : (true :: ω).count false = ω.count false := by simp
theorem cT' (ω : List Bool) : (false :: ω).count true = ω.count true := by simp
theorem cF' (ω : List Bool) : (false :: ω).count false = ω.count false + 1 := by simp

/-- `Σ_p (−1)ᵖ C(n, p) mᵖ (m+1)^{n−p} = 1` -/
theorem B_eq (m : Int) : ∀ ω : List Bool, hs m (fun p => negPow p * Ssum ω p 0) (ω.count true) = 1
  | [] => by simp [hs, Ssum, negPow]
  | true :: ω => by
    rw [cT]
    have e : (fun p => negPow p * Ssum (true :: ω) p 0) =
        fun p => negPow p * Ssum ω p 0 + (match p with | 0 => 0 | p' + 1 => (-1) * (negPow p' * Ssum ω p' 0)) := by
      funext p; cases p with
      | zero => simp [Ssum]
      | succ p => simp only [Ssum, Int.mul_add, negPow]; split <;> split <;> omega
    rw [e, hs_add, hs_ext m _ (fun p => negPow p * Ssum ω p 0) (by
      show negPow (ω.count true + 1) * Ssum ω (ω.count true + 1) 0 = 0
      rw [Ssum_vanish ω _ 0 (by omega), Int.mul_zero]),
      hs_shift, hs_smul, B_eq m ω]
    omega
  | false :: ω => by
    rw [cT']
    have e : (fun p => negPow p * Ssum (false :: ω) p 0) = fun p => negPow p * Ssum ω p 0 := by
      funext p; simp [Ssum]
    rw [e, B_eq m ω]

/-- `z`-weights: `Σ_z u^{#x before z}` -/
def zsum (u : Int) : List Bool → Int
  | [] => 0
  | true :: ω => u * zsum u ω
  | false :: ω => zsum u ω + 1

/-- **the `t`-linear moments**: `Σ_p S(ω,p,1) mᵖ(m+1)^{n−p} = Σ_z (2m+1)^{#x before z}` -/
theorem Phi_eq (m : Int) : ∀ ω : List Bool, hs m (fun p => Ssum ω p 1) (ω.count true) = zsum (2 * m + 1) ω
  | [] => by simp [hs, Ssum, zsum]
  | true :: ω => by
    rw [cT]
    have e : (fun p => Ssum (true :: ω) p 1) = fun p => Ssum ω p 1 + (match p with | 0 => 0 | p' + 1 => Ssum ω p' 1) := by
      funext p; cases p <;> simp [Ssum]
    rw [e, hs_add, hs_ext m _ (fun p => Ssum ω p 1) (Ssum_vanish ω _ 1 (by omega)), hs_shift, Phi_eq m ω, zsum]
    rw [← Int.add_mul]; congr 1; omega
  | false :: ω => by
    rw [cT']
    have e : (fun p => Ssum (false :: ω) p 1) = fun p => Ssum ω p 1 + negPow p * Ssum ω p 0 := by
      funext p; simp [Ssum]
    rw [e, hs_add, Phi_eq m ω, B_eq m ω, zsum]

/-- `Σ_r C(n, r) mʳ (m+1)^{n−r} = (2m+1)ⁿ` -/
theorem D_eq (m : Int) : ∀ ω : List Bool, hs m (fun r => Ssum ω 0 r) (ω.count false) = ipow (2 * m + 1) (ω.count false)
  | [] => by simp [hs, Ssum, ipow]
  | true :: ω => by
    rw [cF]
    have e : (fun r => Ssum (true :: ω) 0 r) = fun r => Ssum ω 0 r := by funext r; simp [Ssum]
    rw [e, D_eq m ω]
  | false :: ω => by
    rw [cF']
    have e : (fun r => Ssum (false :: ω) 0 r) = fun r => Ssum ω 0 r + (match r with | 0 => 0 | r' + 1 => Ssum ω 0 r') := by
      funext r; cases r <;> simp [Ssum, negPow]
    rw [e, hs_add, hs_ext m _ (fun r => Ssum ω 0 r) (Ssum_vanish ω 0 _ (by omega)), hs_shift, D_eq m ω, ipow]
    rw [← Int.add_mul, Int.mul_comm]; congr 1; omega

/-- number of x's followed by exactly `e` z's -/
def cntAfter : List Bool → Nat → Nat
  | [], _ => 0
  | true :: ω, e => (if e = ω.count false then 1 else 0) + cntAfter ω e
  | false :: ω, e => cntAfter ω e

theorem cntAfter_vanish : ∀ (ω : List Bool) (e : Nat), ω.count false < e → cntAfter ω e = 0
  | [], _, _ => rfl
  | true :: ω, e, h => by rw [cF] at h; simp only [cntAfter, cntAfter_vanish ω e h]; rw [ite_eq_right (by omega)]
  | false :: ω, e, h => by rw [cF'] at h; exact cntAfter_vanish ω e (by omega)

theorem dsum_top (M : Int) : ∀ N (D : Nat → Int), D N = 0 → dsum M D (N + 1) = dsum M D N
  | 0, D, h => by simp only [dsum, h]; simp
  | N + 1, D, h => by
    show D 0 + M * dsum M (fun e => D (e + 1)) (N + 1) = D 0 + M * dsum M (fun e => D (e + 1)) N
    rw [dsum_top M N (fun e => D (e + 1)) h]

/-- **the `s`-linear moments**: `Σ_r S(ω,1,r) mʳ(m+1)^{c−r} = Σ_e cntAfter(e) (2m+1)ᵉ` -/
theorem Phi'_eq (m : Int) : ∀ ω : List Bool,
    hs m (fun r => Ssum ω 1 r) (ω.count false) = dsum (2 * m + 1) (fun e => (cntAfter ω e : Int)) (ω.count false + 1)
  | [] => by simp [hs, Ssum, dsum, cntAfter]
  | true :: ω => by
    rw [cF]
    have e : (fun r => Ssum (true :: ω) 1 r) = fun r => Ssum ω 1 r + Ssum ω 0 r := by funext r; simp [Ssum]
    have e2 : (fun e => (cntAfter (true :: ω) e : Int)) =
        fun e => (if ω.count false = e then (1 : Int) else 0) + (cntAfter ω e : Int) := by
      funext e; simp only [cntAfter]; by_cases h : e = ω.count false
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [e, hs_add, Phi'_eq m ω, D_eq m ω, e2, dsum_add,
      dsum_single (2 * m + 1) 1 (ω.count false + 1) (ω.count false) (by omega)]
    rw [Int.mul_one]; omega
  | false :: ω => by
    rw [cF']
    have e : (fun r => Ssum (false :: ω) 1 r) =
        fun r => Ssum ω 1 r + (match r with | 0 => 0 | r' + 1 => (-1) * Ssum ω 1 r') := by
      funext r; cases r <;> simp [Ssum, negPow]
    have e2 : (fun e => (cntAfter (false :: ω) e : Int)) = fun e => (cntAfter ω e : Int) := by funext e; rfl
    rw [e, hs_add, hs_ext m _ (fun r => Ssum ω 1 r) (Ssum_vanish ω 1 (ω.count false + 1) (by omega)), hs_shift, hs_smul,
      Phi'_eq m ω, e2, dsum_top (2 * m + 1) (ω.count false + 1) (fun e => (cntAfter ω e : Int)) (by
        show (cntAfter ω (ω.count false + 1) : Int) = 0
        rw [cntAfter_vanish ω _ (by omega)]; rfl)]
    have h1 : ∀ X : Int, (-1) * X = -X := fun X => by omega
    simp only [Int.add_mul, Int.one_mul, h1, Int.mul_neg]; omega

theorem cntAfter_lead : ∀ ω : List Bool, cntAfter ω (ω.count false) = PropS.lead ω
  | [] => rfl
  | true :: ω => by rw [cF]; simp only [cntAfter, ite_true, PropS.lead, cntAfter_lead ω]; omega
  | false :: ω => by rw [cF']; simp only [cntAfter, PropS.lead]; exact cntAfter_vanish ω _ (by omega)

theorem zsum_prof (u : Int) : ∀ ω : List Bool,
    zsum u ω = dsum u (fun α => (PropS.prof ω α : Int)) (ω.count true + 1)
  | [] => by simp [zsum, dsum, PropS.prof]
  | true :: ω => by
    rw [cT, zsum, zsum_prof u ω]
    show _ = (PropS.prof (true :: ω) 0 : Int) + u * dsum u (fun e => (PropS.prof (true :: ω) (e + 1) : Int)) (ω.count true + 1)
    simp [PropS.prof]
  | false :: ω => by
    rw [cT', zsum, zsum_prof u ω]
    have e : (fun α => (PropS.prof (false :: ω) α : Int)) = fun α => (if 0 = α then (1 : Int) else 0) + (PropS.prof ω α : Int) := by
      funext α; simp only [PropS.prof]; by_cases h : α = 0
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [e, dsum_add, dsum_single u 1 (ω.count true + 1) 0 (by omega)]; simp [ipow]; omega

/-! ## digits and counts -/

theorem dsum_smul (M s : Int) : ∀ N (D : Nat → Int), dsum M (fun e => s * D e) N = s * dsum M D N
  | 0, _ => by simp [dsum]
  | N + 1, D => by
    simp only [dsum, dsum_smul M s N (fun e => D (e + 1)), Int.mul_add]
    rw [Int.mul_left_comm M s]

theorem prof_le : ∀ (ω : List Bool) (α : Nat), PropS.prof ω α ≤ ω.count false
  | [], _ => by simp [PropS.prof]
  | true :: ω, 0 => by simp [PropS.prof]
  | true :: ω, α + 1 => by simp only [PropS.prof, cF]; exact prof_le ω α
  | false :: ω, α => by simp only [PropS.prof, cF']; have := prof_le ω α; split <;> omega

theorem prof_vanish : ∀ (ω : List Bool) (α : Nat), ω.count true < α → PropS.prof ω α = 0
  | [], _, _ => by simp [PropS.prof]
  | true :: ω, 0, h => by simp [PropS.prof]
  | true :: ω, α + 1, h => by rw [cT] at h; simp only [PropS.prof]; exact prof_vanish ω α (by omega)
  | false :: ω, α, h => by
    rw [cT'] at h; simp only [PropS.prof, prof_vanish ω α h]; rw [ite_eq_right (by omega)]

theorem cntAfter_le : ∀ (ω : List Bool) (e : Nat), cntAfter ω e ≤ ω.count true
  | [], _ => by simp [cntAfter]
  | true :: ω, e => by simp only [cntAfter, cT]; have := cntAfter_le ω e; split <;> omega
  | false :: ω, e => by simp only [cntAfter, cT']; exact cntAfter_le ω e

theorem nx_count : ∀ ω : List Bool, PropS.nx ω = ω.count true
  | [] => rfl
  | true :: ω => by simp only [PropS.nx, cT, nx_count ω]
  | false :: ω => by simp only [PropS.nx, cT', nx_count ω]

/-! ## the three-block case -/

variable (a b c : Nat)

theorem ωp_eq (T : Tree) : PropT.ωp a b T = PropS.ωp (PropT.a' a b T) (PropT.c' a b T) (PropT.W a b T) := by
  simp [PropT.ωp, PropS.ωp, List.append_assoc]
theorem ωm_eq (T : Tree) : PropT.ωm a b T = PropS.ωm (PropT.a' a b T) (PropT.c' a b T) (PropT.W a b T) := by
  simp [PropT.ωm, PropS.ωm, List.append_assoc]

/-- the bracket `j·S(ω₊,p,r) + (b−j)·S(ω₋,p,r)` of Lemma M -/
def Kc (T : Tree) (p r : Nat) : Int :=
  (PropT.j a b T : Int) * Ssum (PropT.ωp a b T) p r + ((b - PropT.j a b T : Nat) : Int) * Ssum (PropT.ωm a b T) p r

theorem Eu_sign (p r : Nat) : (Eu p r).1 = 1 ∨ (Eu p r).1 = -1 := by
  simp only [Eu, Bs, mu]
  rcases sgn_pm (if p % 2 = 1 then 1 else 0) (if r % 2 = 1 then 4 else 0) with h1 | h1 <;>
  rcases sgn_pm (xr (if p % 2 = 1 then 1 else 0) (if r % 2 = 1 then 4 else 0)) 2 with h2 | h2 <;> simp [h1, h2]

def DN (U : Tree) (α : Nat) : Int :=
  (PropT.j a b U : Int) * PropS.prof (PropT.ωp a b U) α + ((b - PropT.j a b U : Nat) : Int) * PropS.prof (PropT.ωm a b U) α
def DA (U : Tree) (e : Nat) : Int :=
  (PropT.j a b U : Int) * cntAfter (PropT.ωp a b U) e + ((b - PropT.j a b U : Nat) : Int) * cntAfter (PropT.ωm a b U) e
def mm : Int := b * (a + c) + 1

section
variable (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
include ha hb hc

theorem counts (T : Tree) (h : PropT.TB a b c T) :
    (PropT.ωp a b T).count true = a ∧ (PropT.ωp a b T).count false = c ∧
    (PropT.ωm a b T).count true = a ∧ (PropT.ωm a b T).count false = c ∧
    1 ≤ PropT.a' a b T ∧ 1 ≤ PropT.c' a b T ∧ PropT.a' a b T + (PropT.W a b T).count true = a ∧
    PropT.j a b T ≤ b := by
  have g : PropT.Good a b T := ⟨h.wf, by rw [h.lo]; omega, by have := h.hi; omega⟩
  have f := PropT.core_facts a b hb T g
  have := h.lo; have := h.hi
  have := f.wt; have := f.wf'; have := f.ulo; have := f.vhi; have := f.thi; have := f.tlo; have := f.uhi'
  simp only [PropT.ωp, PropT.ωm, PropT.a', PropT.c', PropT.j, List.count_append, List.count_replicate]
  simp; omega

/-- Lemma M turns equal moments into equal brackets -/
theorem K_of_moment (T T' : Tree) (h : PropT.TB a b c T) (h' : PropT.TB a b c T') (p r : Nat)
    (hm : moment a b c T p r = moment a b c T' p r) : Kc a b T p r = Kc a b T' p r := by
  rw [lemmaM a b c ha hb hc T h, lemmaM a b c ha hb hc T' h'] at hm
  have := congrFun hm (Eu p r).2
  simp only [toO, sc, smul, unit, ite_true, Int.mul_one] at this
  have hs : σ p r = 1 ∨ σ p r = -1 := by simp only [σ, negPow]; split <;> simp
  rcases Eu_sign p r with e | e <;> rcases hs with s | s <;> simp only [e, s] at this <;> simp only [Kc] <;> omega

/-- **Proposition S, moments to profiles, and the decoding: equal brackets give equal keys** -/
theorem key_of_K (T T' : Tree) (h : PropT.TB a b c T) (h' : PropT.TB a b c T')
    (hK : ∀ p r, p ≤ a → r ≤ c → Kc a b T p r = Kc a b T' p r) : PropT.key a b T = PropT.key a b T' := by
  obtain ⟨p1, p2, m1, m2, ha1, hc1, hw1, hj1⟩ := counts a b c ha hb hc T h
  obtain ⟨p1', p2', m1', m2', ha1', hc1', hw1', hj1'⟩ := counts a b c ha hb hc T' h'
  have hm : mm a b c = b * (a + c) + 1 := rfl
  -- the `t`-linear moments: the profile `N`
  have tlin : ∀ U : Tree, (PropT.ωp a b U).count true = a → (PropT.ωm a b U).count true = a →
      hs (mm a b c) (fun p => Kc a b U p 1) a = dsum (2 * mm a b c + 1) (DN a b U) (a + 1) := by
    intro U e1 e2
    have P1 := Phi_eq (mm a b c) (PropT.ωp a b U); rw [e1, zsum_prof, e1] at P1
    have P2 := Phi_eq (mm a b c) (PropT.ωm a b U); rw [e2, zsum_prof, e2] at P2
    simp only [Kc]; rw [hs_add, hs_smul, hs_smul, P1, P2, ← dsum_smul, ← dsum_smul, ← dsum_add]; rfl
  have rlin : ∀ U : Tree, (PropT.ωp a b U).count false = c → (PropT.ωm a b U).count false = c →
      hs (mm a b c) (fun r => Kc a b U 1 r) c = dsum (2 * mm a b c + 1) (DA a b U) (c + 1) := by
    intro U e1 e2
    have P1 := Phi'_eq (mm a b c) (PropT.ωp a b U); rw [e1] at P1
    have P2 := Phi'_eq (mm a b c) (PropT.ωm a b U); rw [e2] at P2
    simp only [Kc]; rw [hs_add, hs_smul, hs_smul, P1, P2, ← dsum_smul, ← dsum_smul, ← dsum_add]; rfl
  have hbc : (0 : Int) ≤ (b : Int) * (a + c) := Int.mul_nonneg (by omega) (by omega)
  have hu : (0 : Int) < 2 * mm a b c + 1 := by omega
  -- digit bounds
  have dig : ∀ (U : Tree) (P Q : Nat) (k : Nat), PropT.j a b U ≤ b → P ≤ k → Q ≤ k →
      0 ≤ (PropT.j a b U : Int) * P + ((b - PropT.j a b U : Nat) : Int) * Q ∧
      (PropT.j a b U : Int) * P + ((b - PropT.j a b U : Nat) : Int) * Q ≤ (b : Int) * k := by
    intro U P Q k hj hP hQ
    have c1 : ((b - PropT.j a b U : Nat) : Int) = (b : Int) - PropT.j a b U := by omega
    have i1 : (PropT.j a b U : Int) * P ≤ (PropT.j a b U : Int) * k := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have i2 : ((b - PropT.j a b U : Nat) : Int) * Q ≤ ((b - PropT.j a b U : Nat) : Int) * k :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have i3 : (0 : Int) ≤ (PropT.j a b U : Int) * P := Int.mul_nonneg (by omega) (by omega)
    have i4 : (0 : Int) ≤ ((b - PropT.j a b U : Nat) : Int) * Q := Int.mul_nonneg (by omega) (by omega)
    have e : (PropT.j a b U : Int) * k + ((b - PropT.j a b U : Nat) : Int) * k = (b : Int) * k := by
      rw [← Int.add_mul, c1]; congr 1; omega
    omega
  have bA : (b : Int) * a ≤ b * (a + c) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have bC : (b : Int) * c ≤ b * (a + c) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  -- the profile `N`
  have hN : ∀ α, PropS.N b (PropT.j a b T) (PropT.a' a b T) (PropT.c' a b T) (PropT.W a b T) α =
      PropS.N b (PropT.j a b T') (PropT.a' a b T') (PropT.c' a b T') (PropT.W a b T') α := by
    have hd := tlin T p1 m1; have hd' := tlin T' p1' m1'
    have heq : hs (mm a b c) (fun p => Kc a b T p 1) a = hs (mm a b c) (fun p => Kc a b T' p 1) a :=
      hs_congr _ a _ _ (fun p hp => hK p 1 hp (by omega))
    rw [hd, hd'] at heq
    have z := digits_zero (2 * mm a b c + 1) hu (a + 1) (fun e => DN a b T e - DN a b T' e) (fun e _ => by
      have u1 : 0 ≤ DN a b T e ∧ DN a b T e ≤ (b : Int) * c := dig T _ _ c hj1 (by have := prof_le (PropT.ωp a b T) e; omega) (by have := prof_le (PropT.ωm a b T) e; omega)
      have u2 : 0 ≤ DN a b T' e ∧ DN a b T' e ≤ (b : Int) * c := dig T' _ _ c hj1' (by have := prof_le (PropT.ωp a b T') e; omega) (by have := prof_le (PropT.ωm a b T') e; omega)
      show -(2 * mm a b c + 1) < 2 * (DN a b T e - DN a b T' e) ∧ 2 * (DN a b T e - DN a b T' e) < 2 * mm a b c + 1
      omega) (by rw [dsum_sub, heq]; omega)
    intro α
    simp only [PropS.N, ← ωp_eq, ← ωm_eq]
    by_cases hα : α < a + 1
    · have h0 : DN a b T α = DN a b T' α := by have := z α hα; omega
      simp only [DN] at h0
      have e : ((PropT.j a b T * PropS.prof (PropT.ωp a b T) α + (b - PropT.j a b T) * PropS.prof (PropT.ωm a b T) α : Nat) : Int) =
          ((PropT.j a b T' * PropS.prof (PropT.ωp a b T') α + (b - PropT.j a b T') * PropS.prof (PropT.ωm a b T') α : Nat) : Int) := by
        push_cast; exact h0
      exact_mod_cast e
    · rw [prof_vanish _ α (by omega), prof_vanish _ α (by omega), prof_vanish _ α (by omega), prof_vanish _ α (by omega)]
      simp
  -- the moment `M(0)`
  have hM : PropS.M0 b (PropT.j a b T) (PropT.a' a b T) (PropT.c' a b T) (PropT.W a b T) =
      PropS.M0 b (PropT.j a b T') (PropT.a' a b T') (PropT.c' a b T') (PropT.W a b T') := by
    have hd := rlin T p2 m2; have hd' := rlin T' p2' m2'
    have heq : hs (mm a b c) (fun r => Kc a b T 1 r) c = hs (mm a b c) (fun r => Kc a b T' 1 r) c :=
      hs_congr _ c _ _ (fun r hr => hK 1 r (by omega) hr)
    rw [hd, hd'] at heq
    have z := digits_zero (2 * mm a b c + 1) hu (c + 1) (fun e => DA a b T e - DA a b T' e) (fun e _ => by
      have u1 : 0 ≤ DA a b T e ∧ DA a b T e ≤ (b : Int) * a := dig T _ _ a hj1 (by have := cntAfter_le (PropT.ωp a b T) e; omega) (by have := cntAfter_le (PropT.ωm a b T) e; omega)
      have u2 : 0 ≤ DA a b T' e ∧ DA a b T' e ≤ (b : Int) * a := dig T' _ _ a hj1' (by have := cntAfter_le (PropT.ωp a b T') e; omega) (by have := cntAfter_le (PropT.ωm a b T') e; omega)
      show -(2 * mm a b c + 1) < 2 * (DA a b T e - DA a b T' e) ∧ 2 * (DA a b T e - DA a b T' e) < 2 * mm a b c + 1
      omega) (by rw [dsum_sub, heq]; omega) c (by omega)
    have h0 : DA a b T c = DA a b T' c := by omega
    simp only [DA] at h0
    have l1 := cntAfter_lead (PropT.ωp a b T); have l2 := cntAfter_lead (PropT.ωm a b T)
    have l3 := cntAfter_lead (PropT.ωp a b T'); have l4 := cntAfter_lead (PropT.ωm a b T')
    rw [p2] at l1; rw [m2] at l2; rw [p2'] at l3; rw [m2'] at l4
    simp only [PropS.M0, ← ωp_eq, ← ωm_eq, ← l1, ← l2, ← l3, ← l4]
    have e : ((PropT.j a b T * cntAfter (PropT.ωp a b T) c + (b - PropT.j a b T) * cntAfter (PropT.ωm a b T) c : Nat) : Int) =
        ((PropT.j a b T' * cntAfter (PropT.ωp a b T') c + (b - PropT.j a b T') * cntAfter (PropT.ωm a b T') c : Nat) : Int) := by
      push_cast; exact h0
    exact_mod_cast e
  -- decoding (Proposition S)
  have hx : PropT.a' a b T + PropS.nx (PropT.W a b T) = PropT.a' a b T' + PropS.nx (PropT.W a b T') := by
    rw [nx_count, nx_count]; omega
  obtain ⟨k1, k2⟩ := PropS.propS_kind b (PropT.j a b T) _ _ (PropT.W a b T) ha1 hc1
  obtain ⟨k1', k2'⟩ := PropS.propS_kind b (PropT.j a b T') _ _ (PropT.W a b T') ha1' hc1'
  rw [hM] at k1; rw [hN 0] at k2
  simp only [PropT.key]
  by_cases z1 : PropT.j a b T = 0
  · have z2 : PropT.j a b T' = 0 := by
      apply Classical.byContradiction; intro hne
      have := k1'.2 (by omega); have := k1.1 this; omega
    simp only [z1, z2, ite_true, PropT.Key.join.injEq]
    rw [ωm_eq, ωm_eq]
    apply PropS.propS_boundary b (by omega) _ _ (by rw [nx_count, nx_count, ← ωm_eq, ← ωm_eq, m1, m1'])
    intro α; have := hN α; rw [z1, z2, PropS.N_boundary0, PropS.N_boundary0] at this; exact this
  by_cases zb : PropT.j a b T = b
  · have z2 : PropT.j a b T' = b := by
      apply Classical.byContradiction; intro hne
      have := k2'.2 (by omega); have := k2.1 this; omega
    have hb0 : ¬ b = 0 := by omega
    simp only [zb, z2, hb0, ite_true, ite_false, PropT.Key.join.injEq]
    rw [ωp_eq, ωp_eq]
    apply PropS.propS_boundary b (by omega) _ _ (by rw [nx_count, nx_count, ← ωp_eq, ← ωp_eq, p1, p1'])
    intro α; rw [← PropS.N_boundaryb, ← PropS.N_boundaryb]
    have := hN α; rw [zb, z2] at this; exact this
  · have z2 : PropT.j a b T' ≠ 0 := by
      intro e; have := k1.2 (by omega); have := k1'.1 this; omega
    have zb2 : PropT.j a b T' ≠ b := by
      intro e; have := k2.2 (by omega); have := k2'.1 this; omega
    simp only [z1, zb, z2, zb2, ite_false, PropT.Key.inner.injEq]
    exact PropS.propS_interior b _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ha1 hc1 ha1' hc1' hx hN hM

/-- the Kronecker valuation `x, y, z ↦ 1 + M e₁, 1 + M^{n+1} e₂, 1 + M^{(n+1)²} e₄` -/
def kronρ : Nat → O :=
  ρs (ipow 2 (a + b + c + 2) + 1) (ipow (ipow 2 (a + b + c + 2) + 1) (a + b + c + 1))
    (ipow (ipow 2 (a + b + c + 2) + 1) ((a + b + c + 1) * (a + b + c + 1)))

/-- **G2 for three-block words, key form.** Bracketings with the same value at the Kronecker valuation have
the same invariant. -/
theorem key_of_map (T T' : Tree) (h : PropT.TB a b c T) (h' : PropT.TB a b c T')
    (hev : ev (PropT.w3 a b) (kronρ a b c) T = ev (PropT.w3 a b) (kronρ a b c) T') : PropT.key a b T = PropT.key a b T' := by
  apply key_of_K a b c ha hb hc T T' h h'
  intro p r hp hr
  apply K_of_moment a b c ha hb hc T T' h h' p r
  rw [← coef_moment a b c ha hb hc T h, ← coef_moment a b c ha hb hc T' h']
  exact coef_of_map a b c ha hb hc T T' h h' hev p 1 r (by omega) (by omega) (by omega)

/-- **Theorem G2 for three-block words.** Different `D_N`-components of `xᵃyᵇzᶜ` are different octonion maps;
the Kronecker valuation separates them. -/
theorem g2_three (T T' : Tree) (h : PropT.TB a b c T) (h' : PropT.TB a b c T')
    (hsep : ¬ DReach (DNStep (PropT.w3 a b)) T T') : ev (PropT.w3 a b) (kronρ a b c) T ≠ ev (PropT.w3 a b) (kronρ a b c) T' := by
  intro hev
  exact hsep ((PropT.propT a b c ha hb hc T T' h h').2 (key_of_map a b c ha hb hc T T' h h' hev))

end

end Profiles
