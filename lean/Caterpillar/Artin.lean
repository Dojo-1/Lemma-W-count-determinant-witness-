import Caterpillar.Division

/-!
# Artin's theorem for 𝕆, and Lemma V

For octonions `u, v`, let `Sp(u, v) = {α + βu + γv + δ·uv : α, β, γ, δ ∈ ℤ}`.
* `sp_mul`: `Sp(u, v)` is closed under multiplication, using `x² = t(x)x − N(x)` and
  `vu = −uv + t(u)v + t(v)u + (t(uv) − t(u)t(v))`.
* `assoc_sp`: the associator vanishes on `Sp(u, v)`. It is trilinear and alternating, and
  `[u, v, uv] = 0`.
* **`artin`**: every bracketing of a word whose letters take values in `{u, v}` lies in `Sp(u, v)`, and any
  two bracketings of the same word have the same value. That is Artin's theorem for two generators.
* **`lemmaV_two_letters`**, **`lemmaV_powers`**: the two cases of Lemma V.
-/

namespace Octonion
open Caterpillar (Tree)

/-! ## Linear-algebra helpers -/

theorem smul_mul (s : Int) (a b : O) : mul (smul s a) b = smul s (mul a b) := by
  funext k; simp only [mul, smul, sum8, Int.mul_add, Int.mul_assoc, Int.mul_left_comm s]

theorem mul_smul (s : Int) (a b : O) : mul a (smul s b) = smul s (mul a b) := by
  funext k; simp only [mul, smul, sum8, Int.mul_add, Int.mul_assoc, Int.mul_left_comm s]

def tr (x : O) : Int := 2 * x 0

/-! ## Identities -/

def negP (P : OP) : OP := fun k => neg (P k)
def constP (p : Poly) (P : OP) : OP := fun k => pmul p (P k)
def scal0 (p : Poly) : OP := fun k => if k.val = 0 then p else []

theorem evalO_negP (ρ : Nat → Int) (P : OP) : evalO ρ (negP P) = negO (evalO ρ P) := by
  funext k; simp [evalO, negP, negO, evalP_neg]
theorem evalO_constP (ρ : Nat → Int) (p : Poly) (P : OP) : evalO ρ (constP p P) = smul (evalP ρ p) (evalO ρ P) := by
  funext k; simp [evalO, constP, smul, evalP_pmul]
theorem evalO_scal0 (ρ : Nat → Int) (p : Poly) : evalO ρ (scal0 p) = smul (evalP ρ p) one :=
  evalO_scalar0 ρ p

theorem ev_c0 (a b c : O) (s : Int) : evalP (val3 a b c) [(s, [0])] = s * a 0 := by
  simp [evalP, evalM, val3]
theorem ev_c8 (a b c : O) (s : Int) : evalP (val3 a b c) [(s, [8])] = s * b 0 := by
  simp [evalP, evalM, val3]
theorem ev_c08 (a b c : O) (s : Int) : evalP (val3 a b c) [(s, [0, 8])] = s * (a 0 * b 0) := by
  simp [evalP, evalM, val3]

/-- `x² = t(x)·x − N(x)·1` -/
def quadL : OP := mulP A A
def quadR : OP := addP (constP [(2, [0])] A) (negP (scal0 (nrmP A)))
theorem quad_all : ∀ k, idCheck1 quadL quadR k = true := by apply all8 <;> decide +kernel

/-- `vu = −uv + t(u)v + t(v)u + (t(uv) − t(u)t(v))·1` -/
def commL : OP := mulP B A
def commR : OP := addP (addP (addP (negP (mulP A B)) (constP [(2, [0])] B)) (constP [(2, [8])] A))
  (scal0 (psmul 2 (mulP A B 0) ++ [(-4, [0, 8])]))
theorem comm_all : ∀ k, idCheck1 commL commR k = true := by apply all8 <;> decide +kernel

/-- `[u, v, uv] = 0` -/
def baseL : OP := mulP (mulP A B) (mulP A B)
def baseR : OP := mulP A (mulP B (mulP A B))
theorem base_c0 : idCheck1 baseL baseR 0 = true := by decide +kernel
theorem base_c1 : idCheck1 baseL baseR 1 = true := by decide +kernel
theorem base_c2 : idCheck1 baseL baseR 2 = true := by decide +kernel
theorem base_c3 : idCheck1 baseL baseR 3 = true := by decide +kernel
theorem base_c4 : idCheck1 baseL baseR 4 = true := by decide +kernel
theorem base_c5 : idCheck1 baseL baseR 5 = true := by decide +kernel
theorem base_c6 : idCheck1 baseL baseR 6 = true := by decide +kernel
theorem base_c7 : idCheck1 baseL baseR 7 = true := by decide +kernel

theorem evalO_const (ρ : Nat → Int) (p : Poly) (P : OP) :
    evalO ρ (fun k => pmul p (P k)) = smul (evalP ρ p) (evalO ρ P) := by
  funext k; simp [evalO, smul, evalP_pmul]

theorem quad (x : O) : mul x x = oadd (smul (tr x) x) (negO (smul (nrm x) one)) := by
  have := eq_of_idCheck1 (val3 x x x) _ _ quad_all
  simp only [quadL, quadR, evalO_mulP, evalO_addP, evalO_constP, evalO_negP, evalO_scal0, evalP_nrmP,
    ev_c0, A, evalO_var0] at this
  rw [this]; simp only [tr]

theorem comm (u v : O) : mul v u = oadd (oadd (oadd (negO (mul u v)) (smul (tr u) v)) (smul (tr v) u))
    (smul (tr (mul u v) - 4 * (u 0 * v 0)) one) := by
  have := eq_of_idCheck1 (val3 u v v) _ _ comm_all
  have e0 : evalP (val3 u v v) (mulP (varO 0) (varO 8) 0) = mul u v 0 := by
    have := congrFun (evalO_mulP (val3 u v v) (varO 0) (varO 8)) 0
    simp only [evalO] at this; rw [this, evalO_var0, evalO_var8]
  simp only [commL, commR, evalO_mulP, evalO_addP, evalO_constP, evalO_negP, evalO_scal0, evalP_append,
    evalP_psmul, e0, ev_c0, ev_c8, ev_c08, A, B, evalO_var0, evalO_var8] at this
  rw [this]; simp only [tr]
  have hs : 2 * mul u v 0 + -4 * (u 0 * v 0) = 2 * mul u v 0 - 4 * (u 0 * v 0) := by omega
  rw [hs]

theorem assoc_base (u v : O) : assoc u v (mul u v) = zero := by
  have := eq_of_idCheck1 (val3 u v v) baseL baseR
    (all8 base_c0 base_c1 base_c2 base_c3 base_c4 base_c5 base_c6 base_c7)
  simp only [baseL, baseR, evalO_mulP, A, B, evalO_var0, evalO_var8] at this
  unfold assoc; rw [this]; exact (sub_eq_zero _ _).2 rfl

/-! ## The associator is trilinear and alternating -/

theorem assoc_add1 (a a' b c : O) : assoc (oadd a a') b c = oadd (assoc a b c) (assoc a' b c) := by
  simp only [assoc, add_mul, mul_add]; funext k; simp only [sub, oadd]; omega
theorem assoc_add2 (a b b' c : O) : assoc a (oadd b b') c = oadd (assoc a b c) (assoc a b' c) := by
  simp only [assoc, add_mul, mul_add]; funext k; simp only [sub, oadd]; omega
theorem assoc_add3 (a b c c' : O) : assoc a b (oadd c c') = oadd (assoc a b c) (assoc a b c') := by
  simp only [assoc, add_mul, mul_add]; funext k; simp only [sub, oadd]; omega
theorem assoc_smul1 (s : Int) (a b c : O) : assoc (smul s a) b c = smul s (assoc a b c) := by
  simp only [assoc, smul_mul, mul_smul]; funext k; simp only [sub, smul]; rw [Int.mul_sub]
theorem assoc_smul2 (s : Int) (a b c : O) : assoc a (smul s b) c = smul s (assoc a b c) := by
  simp only [assoc, smul_mul, mul_smul]; funext k; simp only [sub, smul]; rw [Int.mul_sub]
theorem assoc_smul3 (s : Int) (a b c : O) : assoc a b (smul s c) = smul s (assoc a b c) := by
  simp only [assoc, smul_mul, mul_smul]; funext k; simp only [sub, smul]; rw [Int.mul_sub]

theorem assoc_xxy (x y : O) : assoc x x y = zero := by
  unfold assoc; rw [left_alternative]; exact (sub_eq_zero _ _).2 rfl
theorem assoc_yxx (x y : O) : assoc y x x = zero := by
  unfold assoc; rw [right_alternative]; exact (sub_eq_zero _ _).2 rfl
theorem assoc_xyx (x y : O) : assoc x y x = zero := by
  unfold assoc; rw [flexible]; exact (sub_eq_zero _ _).2 rfl

theorem oadd_eq_zero {a b : O} (h : oadd a b = zero) : a = negO b := by
  funext k; have := congrFun h k; simp [oadd, zero, negO] at this ⊢; omega

theorem skew12 (x y z : O) : assoc x y z = negO (assoc y x z) := by
  have h := assoc_xxy (oadd x y) z
  rw [assoc_add1, assoc_add2, assoc_add2, assoc_xxy, assoc_xxy] at h
  apply oadd_eq_zero; funext k; have := congrFun h k; simp only [oadd, zero] at this ⊢; omega

theorem skew23 (x y z : O) : assoc x y z = negO (assoc x z y) := by
  have h := assoc_yxx (oadd y z) x
  rw [assoc_add2, assoc_add3, assoc_add3, assoc_yxx, assoc_yxx] at h
  apply oadd_eq_zero; funext k; have := congrFun h k; simp only [oadd, zero] at this ⊢; omega

theorem negO_zero : negO zero = zero := by funext k; simp [negO, zero]

theorem assoc_one1 (b c : O) : assoc one b c = zero := by
  unfold assoc; rw [one_mul, one_mul]; exact (sub_eq_zero _ _).2 rfl
theorem assoc_one2 (a c : O) : assoc a one c = zero := by
  unfold assoc; rw [mul_one, one_mul]; exact (sub_eq_zero _ _).2 rfl
theorem assoc_one3 (a b : O) : assoc a b one = zero := by
  unfold assoc; rw [mul_one, mul_one]; exact (sub_eq_zero _ _).2 rfl

/-! ## The span `Sp(u, v)` -/

def comb (u v : O) (α β γ δ : Int) : O :=
  oadd (oadd (oadd (smul α one) (smul β u)) (smul γ v)) (smul δ (mul u v))

def InSp (u v x : O) : Prop := ∃ α β γ δ, x = comb u v α β γ δ

theorem sp_add {u v x y : O} (hx : InSp u v x) (hy : InSp u v y) : InSp u v (oadd x y) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx; obtain ⟨a', b', c', d', rfl⟩ := hy
  refine ⟨a + a', b + b', c + c', d + d', ?_⟩
  funext k; simp only [comb, oadd, smul, Int.add_mul]; omega

theorem sp_smul {u v x : O} (s : Int) (hx : InSp u v x) : InSp u v (smul s x) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  refine ⟨s * a, s * b, s * c, s * d, ?_⟩
  funext k; simp only [comb, oadd, smul, Int.mul_add, Int.mul_assoc]

theorem sp_neg {u v x : O} (hx : InSp u v x) : InSp u v (negO x) := by
  have := sp_smul (-1) hx
  have e : smul (-1) x = negO x := by funext k; simp [smul, negO]
  rwa [e] at this

theorem sp_one (u v : O) : InSp u v one := ⟨1, 0, 0, 0, by funext k; simp [comb, oadd, smul]⟩
theorem sp_u (u v : O) : InSp u v u := ⟨0, 1, 0, 0, by funext k; simp [comb, oadd, smul]⟩
theorem sp_v (u v : O) : InSp u v v := ⟨0, 0, 1, 0, by funext k; simp [comb, oadd, smul]⟩
theorem sp_uv (u v : O) : InSp u v (mul u v) := ⟨0, 0, 0, 1, by funext k; simp [comb, oadd, smul]⟩

set_option maxHeartbeats 4000000 in
/-- the basis products lie in the span -/
theorem sp_basis (u v : O) : ∀ e f, e ∈ [one, u, v, mul u v] → f ∈ [one, u, v, mul u v] →
    InSp u v (mul e f) := by
  have hq : ∀ x, InSp u v x → InSp u v (mul x x) := fun x hx => by
    rw [quad]; exact sp_add (sp_smul _ hx) (sp_neg (sp_smul _ (sp_one u v)))
  have hvu : InSp u v (mul v u) := by
    rw [comm u v]
    exact sp_add (sp_add (sp_add (sp_neg (sp_uv u v)) (sp_smul _ (sp_v u v))) (sp_smul _ (sp_u u v)))
      (sp_smul _ (sp_one u v))
  have huuv : InSp u v (mul u (mul u v)) := by
    rw [← left_alternative, quad, add_mul, smul_mul, mul_neg_left, smul_mul, one_mul]
    exact sp_add (sp_smul _ (sp_uv u v)) (sp_neg (sp_smul _ (sp_v u v)))
  have huvv : InSp u v (mul (mul u v) v) := by
    rw [right_alternative, quad, mul_add, mul_smul, mul_neg_right, mul_smul, mul_one]
    exact sp_add (sp_smul _ (sp_uv u v)) (sp_neg (sp_smul _ (sp_u u v)))
  have hvuv : InSp u v (mul v (mul u v)) := by
    rw [← flexible, comm u v, add_mul, add_mul, add_mul, mul_neg_left, smul_mul, smul_mul, smul_mul, one_mul]
    refine sp_add (sp_add (sp_add (sp_neg huvv) (sp_smul _ (hq v (sp_v u v)))) (sp_smul _ (sp_uv u v)))
      (sp_smul _ (sp_v u v))
  have huvu : InSp u v (mul (mul u v) u) := by
    rw [flexible, comm u v, mul_add, mul_add, mul_add, mul_neg_right, mul_smul, mul_smul, mul_smul, mul_one]
    refine sp_add (sp_add (sp_add (sp_neg huuv) (sp_smul _ (sp_uv u v))) (sp_smul _ (hq u (sp_u u v))))
      (sp_smul _ (sp_u u v))
  intro e f he hf
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he hf
  rcases he with h1 | h1 | h1 | h1 <;> rcases hf with h2 | h2 | h2 | h2 <;> rw [h1, h2]
  · rw [one_mul]; exact sp_one u v
  · rw [one_mul]; exact sp_u u v
  · rw [one_mul]; exact sp_v u v
  · rw [one_mul]; exact sp_uv u v
  · rw [mul_one]; exact sp_u u v
  · exact hq _ (sp_u u v)
  · exact sp_uv u v
  · exact huuv
  · rw [mul_one]; exact sp_v u v
  · exact hvu
  · exact hq _ (sp_v u v)
  · exact hvuv
  · rw [mul_one]; exact sp_uv u v
  · exact huvu
  · exact huvv
  · exact hq _ (sp_uv u v)

theorem mul_comb_left (u v : O) (α β γ δ : Int) (y : O) :
    mul (comb u v α β γ δ) y =
      oadd (oadd (oadd (smul α (mul one y)) (smul β (mul u y))) (smul γ (mul v y))) (smul δ (mul (mul u v) y)) := by
  simp only [comb, add_mul, smul_mul]

theorem mul_comb_right (u v : O) (x : O) (α β γ δ : Int) :
    mul x (comb u v α β γ δ) =
      oadd (oadd (oadd (smul α (mul x one)) (smul β (mul x u))) (smul γ (mul x v))) (smul δ (mul x (mul u v))) := by
  simp only [comb, mul_add, mul_smul]

/-- **Closure.** `Sp(u, v)` is a subring. -/
theorem sp_mul {u v x y : O} (hx : InSp u v x) (hy : InSp u v y) : InSp u v (mul x y) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', rfl⟩ := hy
  have B := sp_basis u v
  have row : ∀ e, e ∈ [one, u, v, mul u v] → InSp u v (mul e (comb u v a' b' c' d')) := by
    intro e he
    rw [mul_comb_right]
    exact sp_add (sp_add (sp_add (sp_smul _ (B e one he (by simp))) (sp_smul _ (B e u he (by simp))))
      (sp_smul _ (B e v he (by simp)))) (sp_smul _ (B e (mul u v) he (by simp)))
  rw [mul_comb_left]
  exact sp_add (sp_add (sp_add (sp_smul _ (row one (by simp))) (sp_smul _ (row u (by simp))))
    (sp_smul _ (row v (by simp)))) (sp_smul _ (row (mul u v) (by simp)))

set_option maxHeartbeats 4000000 in
/-- the associator on basis triples -/
theorem assoc_basis (u v : O) : ∀ e f g, e ∈ [one, u, v, mul u v] → f ∈ [one, u, v, mul u v] →
    g ∈ [one, u, v, mul u v] → assoc e f g = zero := by
  have b := assoc_base u v
  have p2 : assoc v u (mul u v) = zero := by rw [skew12, b, negO_zero]
  have p3 : assoc u (mul u v) v = zero := by rw [skew23, b, negO_zero]
  have p4 : assoc (mul u v) u v = zero := by rw [skew12, p3, negO_zero]
  have p5 : assoc v (mul u v) u = zero := by rw [skew23, p2, negO_zero]
  have p6 : assoc (mul u v) v u = zero := by rw [skew12, p5, negO_zero]
  intro e f g he hf hg
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he hf hg
  rcases he with h1 | h1 | h1 | h1 <;> rcases hf with h2 | h2 | h2 | h2 <;>
    rcases hg with h3 | h3 | h3 | h3 <;> rw [h1, h2, h3]
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one1 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one3 _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _
  · exact assoc_one3 _ _
  · exact assoc_xyx _ _
  · exact assoc_yxx _ _
  · exact b
  · exact assoc_one3 _ _
  · exact assoc_xyx _ _
  · exact p3
  · exact assoc_yxx _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one3 _ _
  · exact assoc_yxx _ _
  · exact assoc_xyx _ _
  · exact p2
  · exact assoc_one3 _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _
  · exact assoc_one3 _ _
  · exact p5
  · exact assoc_xyx _ _
  · exact assoc_yxx _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one2 _ _
  · exact assoc_one3 _ _
  · exact assoc_yxx _ _
  · exact p4
  · exact assoc_xyx _ _
  · exact assoc_one3 _ _
  · exact p6
  · exact assoc_yxx _ _
  · exact assoc_xyx _ _
  · exact assoc_one3 _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _
  · exact assoc_xxy _ _

theorem assoc_comb1 (u v : O) (α β γ δ : Int) (y z : O) : assoc (comb u v α β γ δ) y z =
    oadd (oadd (oadd (smul α (assoc one y z)) (smul β (assoc u y z))) (smul γ (assoc v y z)))
      (smul δ (assoc (mul u v) y z)) := by
  simp only [comb, assoc_add1, assoc_smul1]
theorem assoc_comb2 (u v : O) (x : O) (α β γ δ : Int) (z : O) : assoc x (comb u v α β γ δ) z =
    oadd (oadd (oadd (smul α (assoc x one z)) (smul β (assoc x u z))) (smul γ (assoc x v z)))
      (smul δ (assoc x (mul u v) z)) := by
  simp only [comb, assoc_add2, assoc_smul2]
theorem assoc_comb3 (u v : O) (x y : O) (α β γ δ : Int) : assoc x y (comb u v α β γ δ) =
    oadd (oadd (oadd (smul α (assoc x y one)) (smul β (assoc x y u))) (smul γ (assoc x y v)))
      (smul δ (assoc x y (mul u v))) := by
  simp only [comb, assoc_add3, assoc_smul3]

theorem smul_zero' (s : Int) : smul s zero = zero := by funext k; simp [smul, zero]
theorem oadd_zero' : oadd zero zero = zero := by funext k; simp [oadd, zero]

/-- **The associator vanishes on `Sp(u, v)`.** -/
theorem assoc_sp1 {u v x : O} (hx : InSp u v x) (f g : O) (hf : f ∈ [one, u, v, mul u v])
    (hg : g ∈ [one, u, v, mul u v]) : assoc x f g = zero := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have B := assoc_basis u v
  rw [assoc_comb1, B one f g (by simp) hf hg, B u f g (by simp) hf hg, B v f g (by simp) hf hg,
    B (mul u v) f g (by simp) hf hg]
  simp only [smul_zero', oadd_zero']

theorem assoc_sp2 {u v x y : O} (hx : InSp u v x) (hy : InSp u v y) (g : O) (hg : g ∈ [one, u, v, mul u v]) :
    assoc x y g = zero := by
  obtain ⟨a, b, c, d, rfl⟩ := hy
  rw [assoc_comb2, assoc_sp1 hx one g (by simp) hg, assoc_sp1 hx u g (by simp) hg, assoc_sp1 hx v g (by simp) hg,
    assoc_sp1 hx (mul u v) g (by simp) hg]
  simp only [smul_zero', oadd_zero']

/-- **The associator vanishes on `Sp(u, v)`.** -/
theorem assoc_sp {u v x y z : O} (hx : InSp u v x) (hy : InSp u v y) (hz : InSp u v z) :
    assoc x y z = zero := by
  obtain ⟨a, b, c, d, rfl⟩ := hz
  rw [assoc_comb3, assoc_sp2 hx hy one (by simp), assoc_sp2 hx hy u (by simp), assoc_sp2 hx hy v (by simp),
    assoc_sp2 hx hy (mul u v) (by simp)]
  simp only [smul_zero', oadd_zero']

/-! ## Artin's theorem and Lemma V -/

/-- letters of the leaves of `T`, left to right -/
def lettersT (w : Nat → Nat) : Tree → List Nat
  | .leaf i => [w i]
  | .node l r => lettersT w l ++ lettersT w r

theorem ev_sp (w : Nat → Nat) (ρ : Nat → O) (u v : O) (h : ∀ ℓ, ρ ℓ = u ∨ ρ ℓ = v) :
    ∀ T, InSp u v (ev w ρ T)
  | .leaf i => by rcases h (w i) with e | e <;> simp only [ev, e] <;> first | exact sp_u u v | exact sp_v u v
  | .node l r => sp_mul (ev_sp w ρ u v h l) (ev_sp w ρ u v h r)

/-- **Artin's theorem (two generators).** If every letter takes a value in `{u, v}`, then any two
bracketings with the same sequence of leaf letters have the same value. -/
theorem artin (w w' : Nat → Nat) (ρ : Nat → O) (u v : O) (h : ∀ ℓ, ρ ℓ = u ∨ ρ ℓ = v) :
    ∀ T T' : Tree, lettersT w T = lettersT w' T' → ev w ρ T = ev w' ρ T' := by
  -- every bracketing equals the right-normed product of its letters
  let rn : List Nat → O := fun L => L.foldr (fun ℓ acc => mul (ρ ℓ) acc) one
  have rn_sp : ∀ L, InSp u v (rn L) := by
    intro L; induction L with
    | nil => exact sp_one u v
    | cons ℓ L ih =>
      show InSp u v (mul (ρ ℓ) (rn L))
      rcases h ℓ with e | e <;> rw [e] <;> first | exact sp_mul (sp_u u v) ih | exact sp_mul (sp_v u v) ih
  have rn_app : ∀ L M, rn (L ++ M) = mul (rn L) (rn M) := by
    intro L M; induction L with
    | nil => show rn M = mul one (rn M); rw [one_mul]
    | cons ℓ L ih =>
      show mul (ρ ℓ) (rn (L ++ M)) = mul (mul (ρ ℓ) (rn L)) (rn M)
      rw [ih]
      have hρ : InSp u v (ρ ℓ) := by rcases h ℓ with e | e <;> rw [e] <;> first | exact sp_u u v | exact sp_v u v
      have := assoc_sp hρ (rn_sp L) (rn_sp M)
      unfold assoc at this
      exact ((sub_eq_zero _ _).1 this).symm
  have key : ∀ (w : Nat → Nat) T, ev w ρ T = rn (lettersT w T) := by
    intro w T; induction T with
    | leaf i => show ρ (w i) = mul (ρ (w i)) one; rw [mul_one]
    | node l r ihl ihr => simp only [ev, lettersT]; rw [rn_app, ihl, ihr]
  intro T T' hT
  rw [key w T, key w' T', hT]

/-- **Lemma V, two letters.** If `A, B, C` only involve letters valued in `{u, v}`, their associator vanishes. -/
theorem lemmaV_two_letters (w : Nat → Nat) (ρ : Nat → O) (u v : O) (h : ∀ ℓ, ρ ℓ = u ∨ ρ ℓ = v)
    (TA TB TC : Tree) : assoc (ev w ρ TA) (ev w ρ TB) (ev w ρ TC) = zero :=
  assoc_sp (ev_sp w ρ u v h TA) (ev_sp w ρ u v h TB) (ev_sp w ρ u v h TC)

/-- a bracketing all of whose leaves carry the value `x` (a power of one letter) -/
theorem power_sp (w : Nat → Nat) (ρ : Nat → O) (x z : O) :
    ∀ T, (∀ i, i ∈ lettersT w T → ρ i = x) → InSp x z (ev w ρ T)
  | .leaf i, h => by simp only [ev]; rw [h (w i) (by simp [lettersT])]; exact sp_u x z
  | .node l r, h => sp_mul (power_sp w ρ x z l (fun i hi => h i (by simp [lettersT, hi])))
      (power_sp w ρ x z r (fun i hi => h i (by simp [lettersT, hi])))

/-- **Lemma V, powers.** If two of `a, b, c` are powers of one letter, the associator vanishes
(the third segment is arbitrary). -/
theorem lemmaV_powers (w : Nat → Nat) (ρ : Nat → O) (x : O) (TA TB TC : Tree)
    (hA : ∀ i, i ∈ lettersT w TA → ρ i = x) (hB : ∀ i, i ∈ lettersT w TB → ρ i = x) :
    assoc (ev w ρ TA) (ev w ρ TB) (ev w ρ TC) = zero := by
  have z := ev w ρ TC
  have hC : InSp x (ev w ρ TC) (ev w ρ TC) := sp_v _ _
  exact assoc_sp (power_sp w ρ x _ TA hA) (power_sp w ρ x _ TB hB) hC

theorem lemmaV_powers_AC (w : Nat → Nat) (ρ : Nat → O) (x : O) (TA TB TC : Tree)
    (hA : ∀ i, i ∈ lettersT w TA → ρ i = x) (hC : ∀ i, i ∈ lettersT w TC → ρ i = x) :
    assoc (ev w ρ TA) (ev w ρ TB) (ev w ρ TC) = zero :=
  assoc_sp (power_sp w ρ x _ TA hA) (sp_v x (ev w ρ TB)) (power_sp w ρ x _ TC hC)

theorem lemmaV_powers_BC (w : Nat → Nat) (ρ : Nat → O) (x : O) (TA TB TC : Tree)
    (hB : ∀ i, i ∈ lettersT w TB → ρ i = x) (hC : ∀ i, i ∈ lettersT w TC → ρ i = x) :
    assoc (ev w ρ TA) (ev w ρ TB) (ev w ρ TC) = zero :=
  assoc_sp (sp_v x (ev w ρ TA)) (power_sp w ρ x _ TB hB) (power_sp w ρ x _ TC hC)

end Octonion
