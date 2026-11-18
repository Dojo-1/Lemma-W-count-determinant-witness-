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
  | [], p, r, h => by simp at h; simp only [Ssum]; rw [if_neg (by omega)]
  | true :: ω, p, r, h => by
    simp only [List.count_cons_self, List.count_cons, Bool.false_eq_true, beq_iff_eq, reduceCtorEq, if_false,
      Nat.add_zero] at h
    simp only [Ssum, Ssum_vanish ω p r (by omega)]
    cases p with
    | zero => rfl
    | succ p => simp only [Ssum_vanish ω p r (by omega)]; rfl
  | false :: ω, p, r, h => by
    simp only [List.count_cons_self, List.count_cons, Bool.false_eq_true, beq_iff_eq, reduceCtorEq, if_false,
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
  | true :: ω, e, h => by rw [cF] at h; simp only [cntAfter, cntAfter_vanish ω e h]; rw [if_neg (by omega)]
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
  | true :: ω => by rw [cF]; simp only [cntAfter, if_true, PropS.lead, cntAfter_lead ω]; omega
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

end Profiles
