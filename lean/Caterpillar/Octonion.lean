/-!
# Octonions over `ℤ`, and the identities the theorem uses

The integer octonions are `O := Fin 8 → Int`, with the Cayley–Dickson table of the repository
(`e_i e_j = sgn(i, j) e_{i xor j}`). Polynomial identities are proved by a small *verified* polynomial
normaliser (`Poly`, `norm`, `evalP_norm`). An identity whose two sides normalise to the same polynomial
holds for all integer arguments, and as an identity of polynomials with integer coefficients it holds
over every commutative ring, in particular over `ℝ`.

Proved here:
* the **Moufang identities** (left, right, middle), which are the moves used by Theorem G3;
* the **alternative** and **flexible** laws;
* the **determinant identity at the heart of Lemma W**: for `X, Y, Z ∈ span(e₁, e₂, e₄)`,
  `[X, Y, Z] = det(X, Y, Z) · [e₁, e₂, e₄]`;
* `[e₁, e₂, e₄] ≠ 0`.
-/

namespace Octonion

/-! ## Verified polynomial normalisation -/

abbrev Mono := List Nat
abbrev Poly := List (Int × Mono)

def evalM (ρ : Nat → Int) : Mono → Int
  | [] => 1
  | v :: m => ρ v * evalM ρ m

def evalP (ρ : Nat → Int) : Poly → Int
  | [] => 0
  | (c, m) :: p => c * evalM ρ m + evalP ρ p

theorem evalM_append (ρ : Nat → Int) : ∀ m n : Mono, evalM ρ (m ++ n) = evalM ρ m * evalM ρ n
  | [], n => by simp [evalM]
  | v :: m, n => by
    show ρ v * evalM ρ (m ++ n) = ρ v * evalM ρ m * evalM ρ n
    rw [evalM_append ρ m n, Int.mul_assoc]

theorem evalP_append (ρ : Nat → Int) : ∀ p q : Poly, evalP ρ (p ++ q) = evalP ρ p + evalP ρ q
  | [], q => by simp [evalP]
  | (c, m) :: p, q => by
    show c * evalM ρ m + evalP ρ (p ++ q) = c * evalM ρ m + evalP ρ p + evalP ρ q
    rw [evalP_append ρ p q, Int.add_assoc]

/-- insertion of a variable into a sorted monomial -/
def ins (v : Nat) : Mono → Mono
  | [] => [v]
  | u :: m => if v ≤ u then v :: u :: m else u :: ins v m

def isort : Mono → Mono
  | [] => []
  | v :: m => ins v (isort m)

theorem evalM_ins (ρ : Nat → Int) (v : Nat) : ∀ m, evalM ρ (ins v m) = ρ v * evalM ρ m
  | [] => rfl
  | u :: m => by
    unfold ins
    split
    · rfl
    · simp only [evalM]; rw [evalM_ins ρ v m, Int.mul_left_comm]

theorem evalM_isort (ρ : Nat → Int) : ∀ m, evalM ρ (isort m) = evalM ρ m
  | [] => rfl
  | v :: m => by simp only [isort, evalM]; rw [evalM_ins, evalM_isort ρ m]

/-- lexicographic order on monomials -/
def monoLe : Mono → Mono → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => if a < b then true else if b < a then false else monoLe m n

def merge : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, x :: p, [] => x :: p
  | n + 1, x :: p, y :: q =>
    if monoLe x.2 y.2 then x :: merge n p (y :: q) else y :: merge n (x :: p) q

theorem evalP_merge (ρ : Nat → Int) : ∀ n p q, evalP ρ (merge n p q) = evalP ρ p + evalP ρ q
  | 0, p, q => evalP_append ρ p q
  | _ + 1, [], q => by simp [merge, evalP]
  | _ + 1, x :: p, [] => by simp [merge, evalP]
  | n + 1, (c, m) :: p, (d, k) :: q => by
    unfold merge
    split
    · simp only [evalP]; rw [evalP_merge ρ n p ((d, k) :: q)]; simp only [evalP]; omega
    · simp only [evalP]; rw [evalP_merge ρ n ((c, m) :: p) q]; simp only [evalP]; omega

/-- even- and odd-position halves (two linear passes; no shared intermediate pairs, which the kernel
would re-evaluate) -/
def evens : Poly → Poly
  | [] => []
  | [x] => [x]
  | x :: _ :: p => x :: evens p

def odds : Poly → Poly
  | [] => []
  | [_] => []
  | _ :: y :: p => y :: odds p

theorem evalP_split (ρ : Nat → Int) : ∀ p, evalP ρ p = evalP ρ (evens p) + evalP ρ (odds p)
  | [] => by simp [evens, odds, evalP]
  | [x] => by simp [evens, odds, evalP]
  | (c, m) :: (d, k) :: p => by
    simp only [evens, odds, evalP]; rw [evalP_split ρ p]; omega

def msort : Nat → Poly → Poly
  | 0, p => p
  | n + 1, p =>
    match p with
    | [] => []
    | [x] => [x]
    | _ :: _ :: _ => merge p.length (msort n (evens p)) (msort n (odds p))

theorem evalP_msort (ρ : Nat → Int) : ∀ n p, evalP ρ (msort n p) = evalP ρ p
  | 0, p => rfl
  | n + 1, [] => rfl
  | n + 1, [x] => rfl
  | n + 1, x :: y :: p => by
    simp only [msort]
    rw [evalP_merge, evalP_msort ρ n, evalP_msort ρ n, ← evalP_split]

/-- merge adjacent equal monomials and drop zero coefficients -/
def collapse : Poly → Poly
  | [] => []
  | (c, m) :: p =>
    match collapse p with
    | [] => if c = 0 then [] else [(c, m)]
    | (d, k) :: r =>
      if m = k then (if c + d = 0 then r else (c + d, m) :: r)
      else if c = 0 then (d, k) :: r else (c, m) :: (d, k) :: r

theorem evalP_collapse (ρ : Nat → Int) : ∀ p, evalP ρ (collapse p) = evalP ρ p
  | [] => rfl
  | (c, m) :: p => by
    have ih := evalP_collapse ρ p
    simp only [collapse]
    split
    · rename_i h; rw [h] at ih
      split
      · rename_i hc; subst hc; simp [evalP] at ih ⊢; omega
      · simp [evalP] at ih ⊢; omega
    · rename_i d k r h
      rw [h] at ih
      split
      · rename_i hmk; subst hmk
        split
        · rename_i hcd
          simp only [evalP] at ih ⊢
          rw [← ih]
          have : c * evalM ρ m + d * evalM ρ m = (c + d) * evalM ρ m := by rw [Int.add_mul]
          rw [← Int.add_assoc, this, hcd]; simp
        · simp only [evalP] at ih ⊢; rw [← ih, Int.add_mul]; omega
      · split
        · rename_i _ hc; subst hc; simp only [evalP] at ih ⊢; rw [← ih]; omega
        · simp only [evalP] at ih ⊢; rw [ih]

def norm (p : Poly) : Poly := collapse (msort 64 (p.map fun t => (t.1, isort t.2)))

theorem evalP_mapsort (ρ : Nat → Int) : ∀ p : Poly, evalP ρ (p.map fun t => (t.1, isort t.2)) = evalP ρ p
  | [] => rfl
  | (c, m) :: p => by simp only [List.map, evalP]; rw [evalM_isort, evalP_mapsort ρ p]

theorem evalP_norm (ρ : Nat → Int) (p : Poly) : evalP ρ (norm p) = evalP ρ p := by
  unfold norm; rw [evalP_collapse, evalP_msort, evalP_mapsort]

def neg (p : Poly) : Poly := p.map fun t => (-t.1, t.2)

theorem evalP_neg (ρ : Nat → Int) : ∀ p, evalP ρ (neg p) = - evalP ρ p
  | [] => rfl
  | (c, m) :: p => by
    show -c * evalM ρ m + evalP ρ (neg p) = -(c * evalM ρ m + evalP ρ p)
    rw [evalP_neg ρ p, Int.neg_mul]; omega

/-- **Soundness of the identity check.** -/
theorem eq_of_norm (ρ : Nat → Int) (p q : Poly) (h : norm (p ++ neg q) = []) : evalP ρ p = evalP ρ q := by
  have := evalP_norm ρ (p ++ neg q)
  rw [h, evalP_append, evalP_neg] at this
  simp [evalP] at this; omega

def pmul (p q : Poly) : Poly := p.flatMap fun t => q.map fun u => (t.1 * u.1, t.2 ++ u.2)

theorem evalP_pmul (ρ : Nat → Int) : ∀ p q, evalP ρ (pmul p q) = evalP ρ p * evalP ρ q
  | [], q => by simp [pmul, evalP]
  | (c, m) :: p, q => by
    have hrow : ∀ q : Poly, evalP ρ (q.map fun u => (c * u.1, m ++ u.2)) = c * evalM ρ m * evalP ρ q := by
      intro q
      induction q with
      | nil => simp [evalP]
      | cons u q ih =>
        obtain ⟨d, k⟩ := u
        simp only [List.map, evalP, evalM_append] at ih ⊢
        rw [ih, Int.mul_add]
        congr 1
        simp only [Int.mul_assoc, Int.mul_left_comm]
    have := evalP_pmul ρ p q
    simp only [pmul, List.flatMap_cons, evalP_append] at this ⊢
    rw [this, hrow]; simp only [evalP]; rw [Int.add_mul]

def psmul (s : Int) (p : Poly) : Poly := p.map fun t => (s * t.1, t.2)

theorem evalP_psmul (ρ : Nat → Int) (s : Int) : ∀ p, evalP ρ (psmul s p) = s * evalP ρ p
  | [] => by simp [psmul, evalP]
  | (c, m) :: p => by
    show s * c * evalM ρ m + evalP ρ (psmul s p) = s * (c * evalM ρ m + evalP ρ p)
    rw [evalP_psmul ρ s p, Int.mul_add, Int.mul_assoc]

/-! ## Octonions -/

abbrev O := Fin 8 → Int

def sgnT : List (List Int) :=
  [[1, 1, 1, 1, 1, 1, 1, 1], [1, -1, 1, -1, 1, -1, -1, 1], [1, -1, -1, 1, 1, 1, -1, -1],
   [1, 1, -1, -1, 1, -1, 1, -1], [1, -1, -1, -1, -1, 1, 1, 1], [1, 1, -1, 1, -1, -1, -1, 1],
   [1, 1, 1, -1, -1, 1, -1, -1], [1, -1, 1, 1, -1, -1, 1, -1]]

def sgn (i j : Fin 8) : Int := (sgnT.getD i.val []).getD j.val 0

/-- `i xor j` -/
def xr (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by decide)⟩

def sum8 (f : Fin 8 → Int) : Int := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7

/-- octonion product: `(ab)_k = Σᵢ sgn(i, i⊕k) aᵢ b_{i⊕k}`, i.e. `eᵢ eⱼ = sgn(i,j) e_{i⊕j}` -/
def mul (a b : O) : O := fun k => sum8 fun i => sgn i (xr i k) * a i * b (xr i k)

def unit (i : Fin 8) : O := fun j => if j = i then 1 else 0

def sub (a b : O) : O := fun k => a k - b k

/-- associator -/
def assoc (a b c : O) : O := sub (mul (mul a b) c) (mul a (mul b c))

/-! ## Symbolic octonions -/

abbrev OP := Fin 8 → Poly

def psum8 (f : Fin 8 → Poly) : Poly := f 0 ++ f 1 ++ f 2 ++ f 3 ++ f 4 ++ f 5 ++ f 6 ++ f 7

theorem evalP_psum8 (ρ : Nat → Int) (f : Fin 8 → Poly) : evalP ρ (psum8 f) = sum8 fun i => evalP ρ (f i) := by
  simp only [psum8, evalP_append, sum8]

def mulP (P Q : OP) : OP := fun k => psum8 fun i => psmul (sgn i (xr i k)) (pmul (P i) (Q (xr i k)))

def evalO (ρ : Nat → Int) (P : OP) : O := fun k => evalP ρ (P k)

theorem evalO_mulP (ρ : Nat → Int) (P Q : OP) : evalO ρ (mulP P Q) = mul (evalO ρ P) (evalO ρ Q) := by
  funext k
  simp only [evalO, mulP, mul, evalP_psum8, evalP_psmul, evalP_pmul, Int.mul_assoc]

def varO (base : Nat) : OP := fun i => [(1, [base + i.val])]

/-- the valuation sending variables `base + i` to `a i` -/
def val3 (a b c : O) (v : Nat) : Int :=
  if h : v < 8 then a ⟨v, h⟩ else if h' : v < 16 then b ⟨v - 8, by omega⟩
  else if h'' : v < 24 then c ⟨v - 16, by omega⟩ else 0

theorem evalO_var0 (a b c : O) : evalO (val3 a b c) (varO 0) = a := by
  funext i; simp [evalO, varO, evalP, evalM, val3, i.isLt]

theorem evalO_var8 (a b c : O) : evalO (val3 a b c) (varO 8) = b := by
  funext i
  have := i.isLt
  simp [evalO, varO, evalP, evalM, val3, show ¬ 8 + i.val < 8 by omega, show 8 + i.val < 16 by omega]

theorem evalO_var16 (a b c : O) : evalO (val3 a b c) (varO 16) = c := by
  funext i
  have := i.isLt
  simp [evalO, varO, evalP, evalM, val3, show ¬ 16 + i.val < 8 by omega,
    show ¬ 16 + i.val < 16 by omega, show 16 + i.val < 24 by omega]

/-- the identity check for one component: the normal form of `L_k − R_k` vanishes -/
def idCheck1 (L R : OP) (k : Fin 8) : Bool := norm (L k ++ neg (R k)) == []

theorem eq_of_idCheck1 (ρ : Nat → Int) (L R : OP) (h : ∀ k, idCheck1 L R k = true) :
    evalO ρ L = evalO ρ R := by
  funext k
  exact eq_of_norm ρ _ _ (by have := h k; simpa [idCheck1] using this)

theorem all8 {P : Fin 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) : ∀ k, P k
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4 | ⟨5, _⟩ => h5 | ⟨6, _⟩ => h6 | ⟨7, _⟩ => h7

/-! ## Fast basis-expansion machinery for multilinear octonion identities -/

/-- Pure 8-constructor basis index for 1-step iota reduction across all kernels. -/
inductive Idx | i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7

def Idx.toFin : Idx → Fin 8
  | .i0 => 0 | .i1 => 1 | .i2 => 2 | .i3 => 3
  | .i4 => 4 | .i5 => 5 | .i6 => 6 | .i7 => 7

def toIdx (i : Fin 8) : Idx :=
  match i.val with
  | 0 => .i0 | 1 => .i1 | 2 => .i2 | 3 => .i3
  | 4 => .i4 | 5 => .i5 | 6 => .i6 | _ => .i7

theorem toFin_toIdx (i : Fin 8) : (toIdx i).toFin = i := by
  rcases i with ⟨v, hv⟩
  match v, hv with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem toIdx_toFin (i : Idx) : toIdx i.toFin = i := by cases i <;> rfl

def ieq : Idx → Idx → Bool
  | .i0, .i0 | .i1, .i1 | .i2, .i2 | .i3, .i3
  | .i4, .i4 | .i5, .i5 | .i6, .i6 | .i7, .i7 => true
  | _, _ => false

theorem ieq_true {a b : Idx} (h : ieq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem ieq_false {a b : Idx} (h : ieq a b = false) : a ≠ b := by
  intro e; subst e; cases a <;> exact absurd h (by decide)

def allIdx (f : Idx → Bool) : Bool :=
  f .i0 && f .i1 && f .i2 && f .i3 && f .i4 && f .i5 && f .i6 && f .i7

theorem allIdx_spec {f : Idx → Bool} (h : allIdx f = true) : ∀ i : Idx, f i = true := by
  have h0 : f .i0 = true ∧ f .i1 = true ∧ f .i2 = true ∧ f .i3 = true ∧
            f .i4 = true ∧ f .i5 = true ∧ f .i6 = true ∧ f .i7 = true := by
    simp only [allIdx, Bool.and_eq_true] at h
    exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
           h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  intro i
  cases i
  · exact h0.1
  · exact h0.2.1
  · exact h0.2.2.1
  · exact h0.2.2.2.1
  · exact h0.2.2.2.2.1
  · exact h0.2.2.2.2.2.1
  · exact h0.2.2.2.2.2.2.1
  · exact h0.2.2.2.2.2.2.2

def allIdx2 (f : Idx → Idx → Bool) : Bool := allIdx fun i => allIdx fun j => f i j
def allIdx3 (f : Idx → Idx → Idx → Bool) : Bool := allIdx fun i => allIdx2 fun j k => f i j k
def allIdx4 (f : Idx → Idx → Idx → Idx → Bool) : Bool := allIdx fun i => allIdx3 fun j k l => f i j k l

theorem allIdx2_spec {f} (h : allIdx2 f = true) (i j : Idx) : f i j = true :=
  allIdx_spec (allIdx_spec h i) j
theorem allIdx3_spec {f} (h : allIdx3 f = true) (i j k : Idx) : f i j k = true :=
  allIdx2_spec (allIdx_spec h i) j k
theorem allIdx4_spec {f} (h : allIdx4 f = true) (i j k l : Idx) : f i j k l = true :=
  allIdx3_spec (allIdx_spec h i) j k l

def ixr : Idx → Idx → Idx
  | .i0, j => j | i, .i0 => i
  | .i1, .i1 => .i0 | .i1, .i2 => .i3 | .i1, .i3 => .i2 | .i1, .i4 => .i5 | .i1, .i5 => .i4 | .i1, .i6 => .i7 | .i1, .i7 => .i6
  | .i2, .i1 => .i3 | .i2, .i2 => .i0 | .i2, .i3 => .i1 | .i2, .i4 => .i6 | .i2, .i5 => .i7 | .i2, .i6 => .i4 | .i2, .i7 => .i5
  | .i3, .i1 => .i2 | .i3, .i2 => .i1 | .i3, .i3 => .i0 | .i3, .i4 => .i7 | .i3, .i5 => .i6 | .i3, .i6 => .i5 | .i3, .i7 => .i4
  | .i4, .i1 => .i5 | .i4, .i2 => .i6 | .i4, .i3 => .i7 | .i4, .i4 => .i0 | .i4, .i5 => .i1 | .i4, .i6 => .i2 | .i4, .i7 => .i3
  | .i5, .i1 => .i4 | .i5, .i2 => .i7 | .i5, .i3 => .i6 | .i5, .i4 => .i1 | .i5, .i5 => .i0 | .i5, .i6 => .i3 | .i5, .i7 => .i2
  | .i6, .i1 => .i7 | .i6, .i2 => .i4 | .i6, .i3 => .i5 | .i6, .i4 => .i2 | .i6, .i5 => .i3 | .i6, .i6 => .i0 | .i6, .i7 => .i1
  | .i7, .i1 => .i6 | .i7, .i2 => .i5 | .i7, .i3 => .i4 | .i7, .i4 => .i3 | .i7, .i5 => .i2 | .i7, .i6 => .i1 | .i7, .i7 => .i0

/-- `false` represents `+1`, `true` represents `-1`. -/
def isgn : Idx → Idx → Bool
  | .i0, _ => false | _, .i0 => false
  | .i1, .i1 => true  | .i1, .i2 => false | .i1, .i3 => true  | .i1, .i4 => false | .i1, .i5 => true  | .i1, .i6 => true  | .i1, .i7 => false
  | .i2, .i1 => true  | .i2, .i2 => true  | .i2, .i3 => false | .i2, .i4 => false | .i2, .i5 => false | .i2, .i6 => true  | .i2, .i7 => true
  | .i3, .i1 => false | .i3, .i2 => true  | .i3, .i3 => true  | .i3, .i4 => false | .i3, .i5 => true  | .i3, .i6 => false | .i3, .i7 => true
  | .i4, .i1 => true  | .i4, .i2 => true  | .i4, .i3 => true  | .i4, .i4 => true  | .i4, .i5 => false | .i4, .i6 => false | .i4, .i7 => false
  | .i5, .i1 => false | .i5, .i2 => true  | .i5, .i3 => false | .i5, .i4 => true  | .i5, .i5 => true  | .i5, .i6 => true  | .i5, .i7 => false
  | .i6, .i1 => false | .i6, .i2 => false | .i6, .i3 => true  | .i6, .i4 => true  | .i6, .i5 => false | .i6, .i6 => true  | .i6, .i7 => true
  | .i7, .i1 => true  | .i7, .i2 => false | .i7, .i3 => false | .i7, .i4 => true  | .i7, .i5 => true  | .i7, .i6 => false | .i7, .i7 => true

def b2i (b : Bool) : Int := if b then -1 else 1

theorem b2i_xor (a b : Bool) : b2i (a != b) = b2i a * b2i b := by
  cases a <;> cases b <;> rfl

def eqSum2 (a b c d : Bool) : Bool := (a == c && b == d) || (a == d && b == c)

theorem b2i_eqSum2 {a b c d : Bool} (h : eqSum2 a b c d = true) :
    b2i a + b2i b = b2i c + b2i d := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | exact absurd h (by decide)

inductive Cnt4 | c0 | c1 | c2 | c3 | c4

def inc4 : Bool → Cnt4 → Cnt4
  | false, c => c
  | true, .c0 => .c1 | true, .c1 => .c2 | true, .c2 => .c3 | true, .c3 => .c4 | true, .c4 => .c4

def cnt4Eq : Cnt4 → Cnt4 → Bool
  | .c0, .c0 | .c1, .c1 | .c2, .c2 | .c3, .c3 | .c4, .c4 => true
  | _, _ => false

def cntVal : Cnt4 → Int
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4

theorem cnt4Eq_val {x y : Cnt4} (h : cnt4Eq x y = true) : cntVal x = cntVal y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

def cnt4 (a b c d : Bool) : Cnt4 := inc4 a (inc4 b (inc4 c (inc4 d .c0)))

theorem b2i_sum4_cnt (a b c d : Bool) :
    (b2i a + b2i b) + (b2i c + b2i d) = 4 - 2 * cntVal (cnt4 a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def eqSum4 (a b c d e f g h : Bool) : Bool := cnt4Eq (cnt4 a b c d) (cnt4 e f g h)

theorem b2i_eqSum4 {a b c d e f g h : Bool} (hk : eqSum4 a b c d e f g h = true) :
    (b2i a + b2i b) + (b2i c + b2i d) = (b2i e + b2i f) + (b2i g + b2i h) := by
  rw [b2i_sum4_cnt, b2i_sum4_cnt, cnt4Eq_val hk]

def bxr (i j : Fin 8) : Fin 8 := (ixr (toIdx i) (toIdx j)).toFin
def bsgn (i j : Fin 8) : Int := b2i (isgn (toIdx i) (toIdx j))

private theorem ixr_comm_b : allIdx2 (fun i j => ieq (ixr i j) (ixr j i)) = true := rfl
private theorem ixr_assoc_b : allIdx3 (fun i j k => ieq (ixr (ixr i j) k) (ixr i (ixr j k))) = true := rfl

theorem ixr_comm (i j : Idx) : ixr i j = ixr j i := ieq_true (allIdx2_spec ixr_comm_b i j)
theorem ixr_assoc (i j k : Idx) : ixr (ixr i j) k = ixr i (ixr j k) :=
  ieq_true (allIdx3_spec ixr_assoc_b i j k)

theorem bxr_comm (i j : Fin 8) : bxr i j = bxr j i := by
  unfold bxr; rw [ixr_comm]

theorem bxr_assoc (i j k : Fin 8) : bxr (bxr i j) k = bxr i (bxr j k) := by
  unfold bxr; simp only [toIdx_toFin]; rw [ixr_assoc]

private theorem bxr_eq_b : allIdx2 (fun i j => bxr i.toFin j.toFin == xr i.toFin j.toFin) = true := rfl
private theorem bsgn_eq_b : allIdx2 (fun i j => bsgn i.toFin j.toFin == sgn i.toFin j.toFin) = true := rfl
private theorem ixr_inv_b : allIdx2 (fun i j => ieq (ixr i (ixr i j)) j) = true := rfl

theorem bxr_eq (i j : Fin 8) : bxr i j = xr i j := by
  have h := allIdx2_spec bxr_eq_b (toIdx i) (toIdx j)
  rw [toFin_toIdx, toFin_toIdx] at h
  exact beq_iff_eq.1 h

theorem bsgn_eq (i j : Fin 8) : bsgn i j = sgn i j := by
  have h := allIdx2_spec bsgn_eq_b (toIdx i) (toIdx j)
  rw [toFin_toIdx, toFin_toIdx] at h
  exact beq_iff_eq.1 h

theorem bxr_inv (i j : Fin 8) : bxr i (bxr i j) = j := by
  unfold bxr; simp only [toIdx_toFin]
  rw [ieq_true (allIdx2_spec ixr_inv_b (toIdx i) (toIdx j)), toFin_toIdx]

def smulO (s : Int) (a : O) : O := fun k => s * a k
def osum8 (f : Fin 8 → O) : O := fun k => sum8 fun i => f i k

theorem decompO (a : O) : a = osum8 fun i => smulO (a i) (unit i) := by
  funext k; rcases k with ⟨k, hk⟩
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [osum8, smulO, sum8, unit]

theorem mul_osum8_l (f : Fin 8 → O) (b : O) : mul (osum8 f) b = osum8 fun i => mul (f i) b := by
  funext k; simp only [mul, osum8, sum8, Int.mul_add, Int.add_mul]; omega

theorem mul_osum8_r (a : O) (f : Fin 8 → O) : mul a (osum8 f) = osum8 fun i => mul a (f i) := by
  funext k; simp only [mul, osum8, sum8, Int.mul_add]; omega

theorem mul_smulO_l (s : Int) (a b : O) : mul (smulO s a) b = smulO s (mul a b) := by
  funext k; simp only [mul, smulO, sum8, Int.mul_add, Int.mul_assoc, Int.mul_left_comm s]

theorem mul_smulO_r (s : Int) (a b : O) : mul a (smulO s b) = smulO s (mul a b) := by
  funext k; simp only [mul, smulO, sum8, Int.mul_add, Int.mul_assoc, Int.mul_left_comm s]

theorem smulO_smulO (s t : Int) (a : O) : smulO s (smulO t a) = smulO (s * t) a := by
  funext k; simp only [smulO, Int.mul_assoc]

theorem sum8_unit_mul (i : Fin 8) (f : Fin 8 → Int) :
    (sum8 fun m => unit i m * f m) = f i := by
  rcases i with ⟨v, hv⟩
  match v, hv with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [sum8, unit]

theorem mul_unit_eq (i j : Fin 8) : mul (unit i) (unit j) = smulO (bsgn i j) (unit (bxr i j)) := by
  funext k
  have h1 : mul (unit i) (unit j) k = sum8 fun m => unit i m * (sgn m (xr m k) * unit j (xr m k)) := by
    simp only [mul]
    congr 1; funext m
    simp only [Int.mul_assoc, Int.mul_left_comm (unit i m)]
  rw [h1, sum8_unit_mul]
  rw [← bxr_eq i k, ← bsgn_eq i (bxr i k)]
  simp only [smulO, unit]
  by_cases h : bxr i k = j
  · subst h
    rw [bxr_inv i k]; simp only [ite_true]
  · have hk : k ≠ bxr i j := by
      intro e; subst e; exact h (bxr_inv i j)
    simp only [h, hk, ite_false, Int.mul_zero]

theorem sum8_add (f g : Fin 8 → Int) : sum8 f + sum8 g = sum8 fun i => f i + g i := by
  simp only [sum8]; omega

theorem sum8_swap (f : Fin 8 → Fin 8 → Int) :
    (sum8 fun i => sum8 fun j => f i j) = (sum8 fun i => sum8 fun j => f j i) := by
  simp only [sum8]; omega

theorem sum8_mul_l (c : Int) (f : Fin 8 → Int) : c * sum8 f = sum8 fun i => c * f i := by
  simp only [sum8, Int.mul_add]

theorem eq_of_sym2 (a : O) (f g : Fin 8 → Fin 8 → Int)
    (h : ∀ i j : Fin 8, f i j + f j i = g i j + g j i) :
    (sum8 fun i => sum8 fun j => a i * (a j * f i j)) =
    (sum8 fun i => sum8 fun j => a i * (a j * g i j)) := by
  have swap : ∀ H : Fin 8 → Fin 8 → Int,
      (sum8 fun i => sum8 fun j => a i * (a j * H i j)) =
      (sum8 fun i => sum8 fun j => a i * (a j * H j i)) := by
    intro H
    rw [sum8_swap]
    congr 1; funext i; congr 1; funext j
    rw [← Int.mul_assoc, Int.mul_comm (a j) (a i), Int.mul_assoc]
  have hs : (sum8 fun i => sum8 fun j => a i * (a j * f i j)) +
            (sum8 fun i => sum8 fun j => a i * (a j * f j i)) =
            (sum8 fun i => sum8 fun j => a i * (a j * g i j)) +
            (sum8 fun i => sum8 fun j => a i * (a j * g j i)) := by
    rw [sum8_add, sum8_add]
    congr 1; funext i; rw [sum8_add, sum8_add]
    congr 1; funext j
    rw [← Int.mul_add, ← Int.mul_add, ← Int.mul_add, ← Int.mul_add, h i j]
  rw [← swap f, ← swap g] at hs
  omega

theorem eq_of_sym2_2 (a b : O) (f g : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Int)
    (h : ∀ i j k l : Fin 8,
      (f i j k l + f j i k l) + (f i j l k + f j i l k) =
      (g i j k l + g j i k l) + (g i j l k + g j i l k)) :
    (sum8 fun i => sum8 fun j => a i * (a j * (sum8 fun k => sum8 fun l => b k * (b l * f i j k l)))) =
    (sum8 fun i => sum8 fun j => a i * (a j * (sum8 fun k => sum8 fun l => b k * (b l * g i j k l)))) := by
  apply eq_of_sym2 a
  intro i j
  rw [sum8_add, sum8_add]
  have h1 : (sum8 fun k => (sum8 fun l => b k * (b l * f i j k l)) + (sum8 fun l => b k * (b l * f j i k l))) =
            (sum8 fun k => sum8 fun l => b k * (b l * (f i j k l + f j i k l))) := by
    congr 1; funext k; rw [sum8_add]; congr 1; funext l; rw [← Int.mul_add, ← Int.mul_add]
  have h2 : (sum8 fun k => (sum8 fun l => b k * (b l * g i j k l)) + (sum8 fun l => b k * (b l * g j i k l))) =
            (sum8 fun k => sum8 fun l => b k * (b l * (g i j k l + g j i k l))) := by
    congr 1; funext k; rw [sum8_add]; congr 1; funext l; rw [← Int.mul_add, ← Int.mul_add]
  rw [h1, h2]
  exact eq_of_sym2 b _ _ (fun k l => h i j k l)

/-! ## The identities (verified by polarized basis sign identities) -/

def A := varO 0
def B := varO 8
def C := varO 16

private def mlB (i j k l : Idx) : Bool := (isgn j l != isgn k (ixr j l)) != isgn i (ixr k (ixr j l))
private def mrB (i j k l : Idx) : Bool := (isgn i k != isgn (ixr i k) j) != isgn (ixr (ixr i k) j) l
private theorem moufang_left_b :
    allIdx4 (fun i j k l => eqSum2 (mlB i j k l) (mlB j i k l) (mrB i j k l) (mrB j i k l)) = true := rfl

private def mrlB (i j k l : Idx) : Bool := (isgn l i != isgn (ixr l i) k) != isgn (ixr (ixr l i) k) j
private def mrrB (i j k l : Idx) : Bool := (isgn k j != isgn i (ixr k j)) != isgn l (ixr i (ixr k j))
private theorem moufang_right_b :
    allIdx4 (fun i j k l => eqSum2 (mrlB i j k l) (mrlB j i k l) (mrrB i j k l) (mrrB j i k l)) = true := rfl

private def mmlB (i j k l : Idx) : Bool := (isgn i k != isgn l j) != isgn (ixr i k) (ixr l j)
private def mmrB (i j k l : Idx) : Bool := (isgn k l != isgn (ixr k l) j) != isgn i (ixr (ixr k l) j)
private theorem moufang_middle_b :
    allIdx4 (fun i j k l => eqSum2 (mmlB i j k l) (mmlB j i k l) (mmrB i j k l) (mmrB j i k l)) = true := rfl

private theorem left_alt_b :
    allIdx3 (fun i j k => eqSum2 (isgn i j != isgn (ixr i j) k) (isgn j i != isgn (ixr j i) k)
      (isgn j k != isgn i (ixr j k)) (isgn i k != isgn j (ixr i k))) = true := rfl

private theorem right_alt_b :
    allIdx3 (fun i j k => eqSum2 (isgn k i != isgn (ixr k i) j) (isgn k j != isgn (ixr k j) i)
      (isgn i j != isgn k (ixr i j)) (isgn j i != isgn k (ixr j i))) = true := rfl

private theorem flexible_b :
    allIdx3 (fun i j k => eqSum2 (isgn i k != isgn (ixr i k) j) (isgn j k != isgn (ixr j k) i)
      (isgn k j != isgn i (ixr k j)) (isgn k i != isgn j (ixr k i))) = true := rfl

private def mlS (i j k l : Fin 8) : Int := bsgn j l * bsgn k (bxr j l) * bsgn i (bxr k (bxr j l))
private def mrS (i j k l : Fin 8) : Int := bsgn i k * bsgn (bxr i k) j * bsgn (bxr (bxr i k) j) l
private theorem moufang_left_sgn (i j k l : Fin 8) :
    mlS i j k l + mlS j i k l = mrS i j k l + mrS j i k l := by
  have h := b2i_eqSum2 (allIdx4_spec moufang_left_b (toIdx i) (toIdx j) (toIdx k) (toIdx l))
  simpa only [mlS, mrS, mlB, mrB, bsgn, bxr, toIdx_toFin, b2i_xor] using h

private def mrlS (i j k l : Fin 8) : Int := bsgn l i * bsgn (bxr l i) k * bsgn (bxr (bxr l i) k) j
private def mrrS (i j k l : Fin 8) : Int := bsgn k j * bsgn i (bxr k j) * bsgn l (bxr i (bxr k j))
private theorem moufang_right_sgn (i j k l : Fin 8) :
    mrlS i j k l + mrlS j i k l = mrrS i j k l + mrrS j i k l := by
  have h := b2i_eqSum2 (allIdx4_spec moufang_right_b (toIdx i) (toIdx j) (toIdx k) (toIdx l))
  simpa only [mrlS, mrrS, mrlB, mrrB, bsgn, bxr, toIdx_toFin, b2i_xor] using h

private def mmlS (i j k l : Fin 8) : Int := bsgn i k * bsgn l j * bsgn (bxr i k) (bxr l j)
private def mmrS (i j k l : Fin 8) : Int := bsgn k l * bsgn (bxr k l) j * bsgn i (bxr (bxr k l) j)
private theorem moufang_middle_sgn (i j k l : Fin 8) :
    mmlS i j k l + mmlS j i k l = mmrS i j k l + mmrS j i k l := by
  have h := b2i_eqSum2 (allIdx4_spec moufang_middle_b (toIdx i) (toIdx j) (toIdx k) (toIdx l))
  simpa only [mmlS, mmrS, mmlB, mmrB, bsgn, bxr, toIdx_toFin, b2i_xor] using h

private theorem left_alt_sgn (i j k : Fin 8) :
    bsgn i j * bsgn (bxr i j) k + bsgn j i * bsgn (bxr j i) k =
    bsgn j k * bsgn i (bxr j k) + bsgn i k * bsgn j (bxr i k) := by
  have h := b2i_eqSum2 (allIdx3_spec left_alt_b (toIdx i) (toIdx j) (toIdx k))
  simpa only [bsgn, bxr, toIdx_toFin, b2i_xor] using h

private theorem right_alt_sgn (i j k : Fin 8) :
    bsgn k i * bsgn (bxr k i) j + bsgn k j * bsgn (bxr k j) i =
    bsgn i j * bsgn k (bxr i j) + bsgn j i * bsgn k (bxr j i) := by
  have h := b2i_eqSum2 (allIdx3_spec right_alt_b (toIdx i) (toIdx j) (toIdx k))
  simpa only [bsgn, bxr, toIdx_toFin, b2i_xor] using h

private theorem flexible_sgn (i j k : Fin 8) :
    bsgn i k * bsgn (bxr i k) j + bsgn j k * bsgn (bxr j k) i =
    bsgn k j * bsgn i (bxr k j) + bsgn k i * bsgn j (bxr k i) := by
  have h := b2i_eqSum2 (allIdx3_spec flexible_b (toIdx i) (toIdx j) (toIdx k))
  simpa only [bsgn, bxr, toIdx_toFin, b2i_xor] using h

theorem bxr_left_comm (a b c : Fin 8) : bxr a (bxr b c) = bxr b (bxr a c) := by
  rw [← bxr_assoc, bxr_comm a b, bxr_assoc]

private theorem bxr4_sym (i j k l : Fin 8) :
    bxr i (bxr k (bxr j l)) = bxr (bxr (bxr i k) j) l ∧
    bxr (bxr (bxr l i) k) j = bxr l (bxr i (bxr k j)) ∧
    bxr (bxr i k) (bxr l j) = bxr i (bxr (bxr k l) j) ∧
    bxr i (bxr k (bxr j l)) = bxr j (bxr k (bxr i l)) ∧
    bxr l (bxr i (bxr k j)) = bxr l (bxr j (bxr k i)) ∧
    bxr i (bxr (bxr k l) j) = bxr j (bxr (bxr k l) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [bxr_assoc]
  · simp only [bxr_assoc]
  · simp only [bxr_assoc]
  · rw [bxr_left_comm k j l, bxr_left_comm i j, bxr_left_comm k i l]
  · rw [bxr_comm k j, bxr_left_comm i j, bxr_comm k i]
  · rw [bxr_comm (bxr k l) j, bxr_left_comm i j, bxr_comm (bxr k l) i]

private theorem bxr3_sym (i j k : Fin 8) :
    bxr (bxr i j) k = bxr i (bxr j k) ∧
    bxr (bxr k i) j = bxr k (bxr i j) ∧
    bxr (bxr i k) j = bxr i (bxr k j) ∧
    bxr i (bxr j k) = bxr j (bxr i k) ∧
    bxr k (bxr i j) = bxr k (bxr j i) ∧
    bxr i (bxr k j) = bxr j (bxr k i) := by
  refine ⟨bxr_assoc i j k, bxr_assoc k i j, bxr_assoc i k j, bxr_left_comm i j k, ?_, ?_⟩
  · rw [bxr_comm i j]
  · rw [bxr_comm k j, bxr_left_comm i j, bxr_comm k i]

/-- **Left Moufang identity** `a(b(ac)) = ((ab)a)c`, for all integer octonions. -/
theorem moufang_left (a b c : O) : mul a (mul b (mul a c)) = mul (mul (mul a b) a) c := by
  conv => lhs; rw [decompO a, decompO b, decompO c]
  conv => rhs; rw [decompO a, decompO b, decompO c]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO]
  congr 1; funext l; congr 1
  simp only [sum8_mul_l]
  have swap23 : ∀ F : Fin 8 → Fin 8 → Fin 8 → Int,
      (sum8 fun j => sum8 fun k => sum8 fun i => F j k i) =
      (sum8 fun j => sum8 fun i => sum8 fun k => F j k i) := fun F => by
    congr 1; funext j; exact sum8_swap _
  conv => lhs; rw [swap23]
  conv => rhs; rw [swap23]
  have hL : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * bsgn j l * (b k * bsgn k (bxr j l) * (a i * bsgn i (bxr k (bxr j l)) * unit (bxr i (bxr k (bxr j l))) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * (mlS i j k l * unit (bxr i (bxr k (bxr j l))) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; unfold mlS; ac_rfl
  have hR : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * (b k * (a i * bsgn i k * bsgn (bxr i k) j * bsgn (bxr (bxr i k) j) l * unit (bxr (bxr (bxr i k) j) l) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * (mrS i j k l * unit (bxr i (bxr k (bxr j l))) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; rw [← (bxr4_sym i j k l).1]; unfold mrS; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [sum8_add, sum8_add]
  congr 1; funext k
  rw [← (bxr4_sym i j k l).2.2.2.1]
  have h1 := moufang_left_sgn i j k l
  simp only [← Int.mul_add, ← Int.add_mul]
  rw [h1]

/-- **Right Moufang identity** `((ca)b)a = c(a(ba))`. -/
theorem moufang_right (a b c : O) : mul (mul (mul c a) b) a = mul c (mul a (mul b a)) := by
  conv => lhs; rw [decompO a, decompO b, decompO c]
  conv => rhs; rw [decompO a, decompO b, decompO c]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO, sum8_mul_l]
  have swap23 : ∀ F : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Int,
      (sum8 fun j => sum8 fun k => sum8 fun i => sum8 fun l => F j k i l) =
      (sum8 fun j => sum8 fun i => sum8 fun k => sum8 fun l => F j k i l) := fun F => by
    congr 1; funext j; exact sum8_swap _
  conv => lhs; rw [swap23]
  conv => rhs; rw [swap23]
  have hL : (sum8 fun j => sum8 fun i => sum8 fun k => sum8 fun l =>
      a j * (b k * (a i * (c l * bsgn l i * bsgn (bxr l i) k * bsgn (bxr (bxr l i) k) j * unit (bxr (bxr (bxr l i) k) j) m)))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => sum8 fun l => b k * (c l * (mrlS i j k l * unit (bxr l (bxr i (bxr k j))) m)))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; congr 1; funext l; rw [(bxr4_sym i j k l).2.1]; unfold mrlS; ac_rfl
  have hR : (sum8 fun j => sum8 fun i => sum8 fun k => sum8 fun l =>
      a j * (b k * bsgn k j * (a i * bsgn i (bxr k j) * (c l * bsgn l (bxr i (bxr k j)) * unit (bxr l (bxr i (bxr k j))) m)))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => sum8 fun l => b k * (c l * (mrrS i j k l * unit (bxr l (bxr i (bxr k j))) m)))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; congr 1; funext l; unfold mrrS; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [sum8_add, sum8_add]
  congr 1; funext k; rw [sum8_add, sum8_add]
  congr 1; funext l
  rw [← (bxr4_sym i j k l).2.2.2.2.1]
  have h1 := moufang_right_sgn i j k l
  simp only [← Int.mul_add, ← Int.add_mul]
  rw [h1]

/-- **Middle Moufang identity** `(ab)(ca) = a((bc)a)`. -/
theorem moufang_middle (a b c : O) : mul (mul a b) (mul c a) = mul a (mul (mul b c) a) := by
  conv => lhs; rw [decompO a, decompO b, decompO c]
  conv => rhs; rw [decompO a, decompO b, decompO c]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO, sum8_mul_l]
  have reord : ∀ F : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Int,
      (sum8 fun j => sum8 fun l => sum8 fun k => sum8 fun i => F j l k i) =
      (sum8 fun j => sum8 fun i => sum8 fun l => sum8 fun k => F j l k i) := fun F => by
    congr 1; funext j
    have s1 : (sum8 fun l => sum8 fun k => sum8 fun i => F j l k i) =
              (sum8 fun l => sum8 fun i => sum8 fun k => F j l k i) := by
      congr 1; funext l; exact sum8_swap _
    rw [s1]; exact sum8_swap _
  conv => lhs; rw [reord]
  conv => rhs; rw [reord]
  have hL : (sum8 fun j => sum8 fun i => sum8 fun l => sum8 fun k =>
      a j * (c l * bsgn l j * (b k * (a i * bsgn i k * bsgn (bxr i k) (bxr l j) * unit (bxr (bxr i k) (bxr l j)) m)))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun l => sum8 fun k => c l * (b k * (mmlS i j k l * unit (bxr i (bxr (bxr k l) j)) m)))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext l; congr 1; funext k; rw [(bxr4_sym i j k l).2.2.1]; unfold mmlS; ac_rfl
  have hR : (sum8 fun j => sum8 fun i => sum8 fun l => sum8 fun k =>
      a j * (c l * (b k * bsgn k l * bsgn (bxr k l) j * (a i * bsgn i (bxr (bxr k l) j) * unit (bxr i (bxr (bxr k l) j)) m)))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun l => sum8 fun k => c l * (b k * (mmrS i j k l * unit (bxr i (bxr (bxr k l) j)) m)))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext l; congr 1; funext k; unfold mmrS; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [sum8_add, sum8_add]
  congr 1; funext l; rw [sum8_add, sum8_add]
  congr 1; funext k
  rw [← (bxr4_sym i j k l).2.2.2.2.2]
  have h1 := moufang_middle_sgn i j k l
  simp only [← Int.mul_add, ← Int.add_mul]
  rw [h1]

theorem left_alternative (a b : O) : mul (mul a a) b = mul a (mul a b) := by
  conv => lhs; rw [decompO a, decompO b]
  conv => rhs; rw [decompO a, decompO b]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO]
  congr 1; funext k; congr 1
  simp only [sum8_mul_l]
  have hL : (sum8 fun j => sum8 fun i =>
      a j * (a i * bsgn i j * bsgn (bxr i j) k * unit (bxr (bxr i j) k) m)) =
      (sum8 fun j => sum8 fun i => a j * (a i * ((bsgn i j * bsgn (bxr i j) k) * unit (bxr i (bxr j k)) m))) := by
    congr 1; funext j; congr 1; funext i
    rw [(bxr3_sym i j k).1]; ac_rfl
  have hR : (sum8 fun j => sum8 fun i =>
      a j * bsgn j k * (a i * bsgn i (bxr j k) * unit (bxr i (bxr j k)) m)) =
      (sum8 fun j => sum8 fun i => a j * (a i * ((bsgn j k * bsgn i (bxr j k)) * unit (bxr i (bxr j k)) m))) := by
    congr 1; funext j; congr 1; funext i; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [← (bxr3_sym i j k).2.2.2.1]
  have h1 := left_alt_sgn i j k
  simp only [← Int.add_mul]
  rw [h1]

theorem right_alternative (a b : O) : mul (mul b a) a = mul b (mul a a) := by
  conv => lhs; rw [decompO a, decompO b]
  conv => rhs; rw [decompO a, decompO b]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO, sum8_mul_l]
  have hL : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * (a i * (b k * bsgn k i * bsgn (bxr k i) j * unit (bxr (bxr k i) j) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * ((bsgn k i * bsgn (bxr k i) j) * unit (bxr k (bxr i j)) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; rw [(bxr3_sym i j k).2.1]; ac_rfl
  have hR : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * (a i * bsgn i j * (b k * bsgn k (bxr i j) * unit (bxr k (bxr i j)) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * ((bsgn i j * bsgn k (bxr i j)) * unit (bxr k (bxr i j)) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [sum8_add, sum8_add]
  congr 1; funext k
  rw [← (bxr3_sym i j k).2.2.2.2.1]
  have h1 := right_alt_sgn i j k
  simp only [← Int.mul_add, ← Int.add_mul]
  rw [h1]

theorem flexible (a b : O) : mul (mul a b) a = mul a (mul b a) := by
  conv => lhs; rw [decompO a, decompO b]
  conv => rhs; rw [decompO a, decompO b]
  simp only [mul_osum8_l, mul_osum8_r, mul_smulO_l, mul_smulO_r, mul_unit_eq, smulO_smulO]
  funext m; simp only [osum8, smulO, sum8_mul_l]
  have swap23 : ∀ F : Fin 8 → Fin 8 → Fin 8 → Int,
      (sum8 fun j => sum8 fun k => sum8 fun i => F j k i) =
      (sum8 fun j => sum8 fun i => sum8 fun k => F j k i) := fun F => by
    congr 1; funext j; exact sum8_swap _
  conv => lhs; rw [swap23]
  conv => rhs; rw [swap23]
  have hL : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * (b k * (a i * bsgn i k * bsgn (bxr i k) j * unit (bxr (bxr i k) j) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * ((bsgn i k * bsgn (bxr i k) j) * unit (bxr i (bxr k j)) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; rw [(bxr3_sym i j k).2.2.1]; ac_rfl
  have hR : (sum8 fun j => sum8 fun i => sum8 fun k =>
      a j * (b k * bsgn k j * (a i * bsgn i (bxr k j) * unit (bxr i (bxr k j)) m))) =
      (sum8 fun j => sum8 fun i => a j * (a i * sum8 fun k => b k * ((bsgn k j * bsgn i (bxr k j)) * unit (bxr i (bxr k j)) m))) := by
    congr 1; funext j; congr 1; funext i; simp only [sum8_mul_l]
    congr 1; funext k; ac_rfl
  rw [hL, hR]
  apply eq_of_sym2 a
  intro j i
  rw [sum8_add, sum8_add]
  congr 1; funext k
  rw [← (bxr3_sym i j k).2.2.2.2.2]
  have h1 := flexible_sgn i j k
  simp only [← Int.mul_add, ← Int.add_mul]
  rw [h1]

/-! ## Lemma W, algebraic core -/

/-- `x₁e₁ + x₂e₂ + x₃e₄` with symbolic coefficients `x_{base}, x_{base+1}, x_{base+2}` -/
def spanP (base : Nat) : OP := fun i =>
  if i.val = 1 then [(1, [base])] else if i.val = 2 then [(1, [base + 1])]
  else if i.val = 4 then [(1, [base + 2])] else []

def subP (P Q : OP) : OP := fun k => P k ++ neg (Q k)

def assocP (P Q R : OP) : OP := subP (mulP (mulP P Q) R) (mulP P (mulP Q R))

/-- `det(x, y, z)` as a polynomial in the nine coefficients `0..2`, `8..10`, `16..18` -/
def detP : Poly :=
  [(1, [0, 9, 18]), (-1, [0, 10, 17]), (-1, [1, 8, 18]), (1, [1, 10, 16]), (1, [2, 8, 17]), (-1, [2, 9, 16])]

/-- the constant associator `[e₁, e₂, e₄]` -/
def e124 : O := assoc (unit 1) (unit 2) (unit 4)

theorem e124_val : e124 = fun k => if k.val = 7 then 2 else 0 := by
  funext k; revert k; decide

theorem e124_ne_zero : e124 ≠ fun _ => 0 := by
  intro h; have := congrFun h 7; rw [e124_val] at this; exact absurd this (by decide)

def lemmaW_L : OP := assocP (spanP 0) (spanP 8) (spanP 16)
def lemmaW_R : OP := fun k => if k.val = 7 then psmul 2 detP else []
theorem lemmaW_all : ∀ k, idCheck1 lemmaW_L lemmaW_R k = true := by
  apply all8 <;> decide +kernel

theorem evalO_subP (ρ : Nat → Int) (P Q : OP) : evalO ρ (subP P Q) = sub (evalO ρ P) (evalO ρ Q) := by
  funext k; simp only [evalO, subP, sub, evalP_append, evalP_neg]; omega

/-- `x₀e₁ + x₁e₂ + x₂e₄` -/
def sp (x : O) : O := fun i => if i.val = 1 then x 0 else if i.val = 2 then x 1 else if i.val = 4 then x 2 else 0

theorem evalO_spanP (a b c : O) (base : Nat) (hb : base = 0 ∨ base = 8 ∨ base = 16) :
    evalO (val3 a b c) (spanP base) = sp (if base = 0 then a else if base = 8 then b else c) := by
  funext i
  rcases hb with rfl | rfl | rfl <;>
  · simp only [evalO, spanP, sp]
    split <;> (try split) <;> (try split) <;> simp_all [evalP, evalM, val3]

/-- `det` of the coordinate triples `(x 0, x 1, x 2)` -/
def det3c (x y z : O) : Int :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

/-- **Lemma W, algebraic core.** For `X, Y, Z` in the span of `e₁, e₂, e₄`,
`[X, Y, Z] = det(X, Y, Z) · [e₁, e₂, e₄]`, where `[e₁, e₂, e₄] = 2e₇ ≠ 0`. So rank-3 coefficient
matrices give a nonzero associator. -/
theorem lemmaW_span (a b c : O) :
    assoc (sp a) (sp b) (sp c) = fun k => if k.val = 7 then 2 * det3c a b c else 0 := by
  have h := eq_of_idCheck1 (val3 a b c) _ _ lemmaW_all
  simp only [lemmaW_L, assocP, evalO_subP, evalO_mulP] at h
  rw [evalO_spanP a b c 0 (by simp), evalO_spanP a b c 8 (by simp), evalO_spanP a b c 16 (by simp)] at h
  simp only [ite_true, ite_eq_right (show (8 : Nat) ≠ 0 by decide), ite_eq_right (show (16 : Nat) ≠ 0 by decide),
    ite_eq_right (show (16 : Nat) ≠ 8 by decide)] at h
  unfold assoc
  rw [h]
  funext k
  simp only [evalO, lemmaW_R]
  split
  · rw [evalP_psmul]; congr 1
    simp [detP, evalP, evalM, val3, det3c]
    simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg]
    omega
  · rfl

end Octonion
