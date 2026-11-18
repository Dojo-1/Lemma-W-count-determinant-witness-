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
  simp [evalO, varO, evalP, evalM, val3]
  rw [dif_neg (by omega), dif_pos (by omega)]; congr 1; ext; simp; omega

theorem evalO_var16 (a b c : O) : evalO (val3 a b c) (varO 16) = c := by
  funext i
  have := i.isLt
  simp [evalO, varO, evalP, evalM, val3]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]; congr 1; ext; simp; omega

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

/-! ## The identities (one kernel check per component keeps memory bounded) -/

def A := varO 0
def B := varO 8
def C := varO 16

def moufang_left_L : OP := mulP A (mulP B (mulP A C))
def moufang_left_R : OP := mulP (mulP (mulP A B) A) C
theorem moufang_left_c0 : idCheck1 moufang_left_L moufang_left_R 0 = true := by decide +kernel
theorem moufang_left_c1 : idCheck1 moufang_left_L moufang_left_R 1 = true := by decide +kernel
theorem moufang_left_c2 : idCheck1 moufang_left_L moufang_left_R 2 = true := by decide +kernel
theorem moufang_left_c3 : idCheck1 moufang_left_L moufang_left_R 3 = true := by decide +kernel
theorem moufang_left_c4 : idCheck1 moufang_left_L moufang_left_R 4 = true := by decide +kernel
theorem moufang_left_c5 : idCheck1 moufang_left_L moufang_left_R 5 = true := by decide +kernel
theorem moufang_left_c6 : idCheck1 moufang_left_L moufang_left_R 6 = true := by decide +kernel
theorem moufang_left_c7 : idCheck1 moufang_left_L moufang_left_R 7 = true := by decide +kernel
theorem moufang_left_all : ∀ k, idCheck1 moufang_left_L moufang_left_R k = true :=
  all8 moufang_left_c0 moufang_left_c1 moufang_left_c2 moufang_left_c3 moufang_left_c4 moufang_left_c5 moufang_left_c6 moufang_left_c7

def moufang_right_L : OP := mulP (mulP (mulP C A) B) A
def moufang_right_R : OP := mulP C (mulP A (mulP B A))
theorem moufang_right_c0 : idCheck1 moufang_right_L moufang_right_R 0 = true := by decide +kernel
theorem moufang_right_c1 : idCheck1 moufang_right_L moufang_right_R 1 = true := by decide +kernel
theorem moufang_right_c2 : idCheck1 moufang_right_L moufang_right_R 2 = true := by decide +kernel
theorem moufang_right_c3 : idCheck1 moufang_right_L moufang_right_R 3 = true := by decide +kernel
theorem moufang_right_c4 : idCheck1 moufang_right_L moufang_right_R 4 = true := by decide +kernel
theorem moufang_right_c5 : idCheck1 moufang_right_L moufang_right_R 5 = true := by decide +kernel
theorem moufang_right_c6 : idCheck1 moufang_right_L moufang_right_R 6 = true := by decide +kernel
theorem moufang_right_c7 : idCheck1 moufang_right_L moufang_right_R 7 = true := by decide +kernel
theorem moufang_right_all : ∀ k, idCheck1 moufang_right_L moufang_right_R k = true :=
  all8 moufang_right_c0 moufang_right_c1 moufang_right_c2 moufang_right_c3 moufang_right_c4 moufang_right_c5 moufang_right_c6 moufang_right_c7

def moufang_middle_L : OP := mulP (mulP A B) (mulP C A)
def moufang_middle_R : OP := mulP A (mulP (mulP B C) A)
theorem moufang_middle_c0 : idCheck1 moufang_middle_L moufang_middle_R 0 = true := by decide +kernel
theorem moufang_middle_c1 : idCheck1 moufang_middle_L moufang_middle_R 1 = true := by decide +kernel
theorem moufang_middle_c2 : idCheck1 moufang_middle_L moufang_middle_R 2 = true := by decide +kernel
theorem moufang_middle_c3 : idCheck1 moufang_middle_L moufang_middle_R 3 = true := by decide +kernel
theorem moufang_middle_c4 : idCheck1 moufang_middle_L moufang_middle_R 4 = true := by decide +kernel
theorem moufang_middle_c5 : idCheck1 moufang_middle_L moufang_middle_R 5 = true := by decide +kernel
theorem moufang_middle_c6 : idCheck1 moufang_middle_L moufang_middle_R 6 = true := by decide +kernel
theorem moufang_middle_c7 : idCheck1 moufang_middle_L moufang_middle_R 7 = true := by decide +kernel
theorem moufang_middle_all : ∀ k, idCheck1 moufang_middle_L moufang_middle_R k = true :=
  all8 moufang_middle_c0 moufang_middle_c1 moufang_middle_c2 moufang_middle_c3 moufang_middle_c4 moufang_middle_c5 moufang_middle_c6 moufang_middle_c7

def left_alt_L : OP := mulP (mulP A A) B
def left_alt_R : OP := mulP A (mulP A B)
theorem left_alt_c0 : idCheck1 left_alt_L left_alt_R 0 = true := by decide +kernel
theorem left_alt_c1 : idCheck1 left_alt_L left_alt_R 1 = true := by decide +kernel
theorem left_alt_c2 : idCheck1 left_alt_L left_alt_R 2 = true := by decide +kernel
theorem left_alt_c3 : idCheck1 left_alt_L left_alt_R 3 = true := by decide +kernel
theorem left_alt_c4 : idCheck1 left_alt_L left_alt_R 4 = true := by decide +kernel
theorem left_alt_c5 : idCheck1 left_alt_L left_alt_R 5 = true := by decide +kernel
theorem left_alt_c6 : idCheck1 left_alt_L left_alt_R 6 = true := by decide +kernel
theorem left_alt_c7 : idCheck1 left_alt_L left_alt_R 7 = true := by decide +kernel
theorem left_alt_all : ∀ k, idCheck1 left_alt_L left_alt_R k = true :=
  all8 left_alt_c0 left_alt_c1 left_alt_c2 left_alt_c3 left_alt_c4 left_alt_c5 left_alt_c6 left_alt_c7

def right_alt_L : OP := mulP (mulP B A) A
def right_alt_R : OP := mulP B (mulP A A)
theorem right_alt_c0 : idCheck1 right_alt_L right_alt_R 0 = true := by decide +kernel
theorem right_alt_c1 : idCheck1 right_alt_L right_alt_R 1 = true := by decide +kernel
theorem right_alt_c2 : idCheck1 right_alt_L right_alt_R 2 = true := by decide +kernel
theorem right_alt_c3 : idCheck1 right_alt_L right_alt_R 3 = true := by decide +kernel
theorem right_alt_c4 : idCheck1 right_alt_L right_alt_R 4 = true := by decide +kernel
theorem right_alt_c5 : idCheck1 right_alt_L right_alt_R 5 = true := by decide +kernel
theorem right_alt_c6 : idCheck1 right_alt_L right_alt_R 6 = true := by decide +kernel
theorem right_alt_c7 : idCheck1 right_alt_L right_alt_R 7 = true := by decide +kernel
theorem right_alt_all : ∀ k, idCheck1 right_alt_L right_alt_R k = true :=
  all8 right_alt_c0 right_alt_c1 right_alt_c2 right_alt_c3 right_alt_c4 right_alt_c5 right_alt_c6 right_alt_c7

def flexible_id_L : OP := mulP (mulP A B) A
def flexible_id_R : OP := mulP A (mulP B A)
theorem flexible_id_c0 : idCheck1 flexible_id_L flexible_id_R 0 = true := by decide +kernel
theorem flexible_id_c1 : idCheck1 flexible_id_L flexible_id_R 1 = true := by decide +kernel
theorem flexible_id_c2 : idCheck1 flexible_id_L flexible_id_R 2 = true := by decide +kernel
theorem flexible_id_c3 : idCheck1 flexible_id_L flexible_id_R 3 = true := by decide +kernel
theorem flexible_id_c4 : idCheck1 flexible_id_L flexible_id_R 4 = true := by decide +kernel
theorem flexible_id_c5 : idCheck1 flexible_id_L flexible_id_R 5 = true := by decide +kernel
theorem flexible_id_c6 : idCheck1 flexible_id_L flexible_id_R 6 = true := by decide +kernel
theorem flexible_id_c7 : idCheck1 flexible_id_L flexible_id_R 7 = true := by decide +kernel
theorem flexible_id_all : ∀ k, idCheck1 flexible_id_L flexible_id_R k = true :=
  all8 flexible_id_c0 flexible_id_c1 flexible_id_c2 flexible_id_c3 flexible_id_c4 flexible_id_c5 flexible_id_c6 flexible_id_c7

/-- **Left Moufang identity** `a(b(ac)) = ((ab)a)c`, for all integer octonions. -/
theorem moufang_left (a b c : O) : mul a (mul b (mul a c)) = mul (mul (mul a b) a) c := by
  have := eq_of_idCheck1 (val3 a b c) _ _ moufang_left_all
  simp only [moufang_left_L, moufang_left_R, evalO_mulP, A, B, C, evalO_var0, evalO_var8, evalO_var16] at this
  exact this

/-- **Right Moufang identity** `((ca)b)a = c(a(ba))`. -/
theorem moufang_right (a b c : O) : mul (mul (mul c a) b) a = mul c (mul a (mul b a)) := by
  have := eq_of_idCheck1 (val3 a b c) _ _ moufang_right_all
  simp only [moufang_right_L, moufang_right_R, evalO_mulP, A, B, C, evalO_var0, evalO_var8, evalO_var16] at this
  exact this

/-- **Middle Moufang identity** `(ab)(ca) = a((bc)a)`. -/
theorem moufang_middle (a b c : O) : mul (mul a b) (mul c a) = mul a (mul (mul b c) a) := by
  have := eq_of_idCheck1 (val3 a b c) _ _ moufang_middle_all
  simp only [moufang_middle_L, moufang_middle_R, evalO_mulP, A, B, C, evalO_var0, evalO_var8, evalO_var16] at this
  exact this

theorem left_alternative (a b : O) : mul (mul a a) b = mul a (mul a b) := by
  have := eq_of_idCheck1 (val3 a b b) _ _ left_alt_all
  simp only [left_alt_L, left_alt_R, evalO_mulP, A, B, evalO_var0, evalO_var8] at this
  exact this

theorem right_alternative (a b : O) : mul (mul b a) a = mul b (mul a a) := by
  have := eq_of_idCheck1 (val3 a b b) _ _ right_alt_all
  simp only [right_alt_L, right_alt_R, evalO_mulP, A, B, evalO_var0, evalO_var8] at this
  exact this

theorem flexible (a b : O) : mul (mul a b) a = mul a (mul b a) := by
  have := eq_of_idCheck1 (val3 a b b) _ _ flexible_id_all
  simp only [flexible_id_L, flexible_id_R, evalO_mulP, A, B, evalO_var0, evalO_var8] at this
  exact this

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
  simp only [if_true, if_neg (show (8 : Nat) ≠ 0 by decide), if_neg (show (16 : Nat) ≠ 0 by decide),
    if_neg (show (16 : Nat) ≠ 8 by decide)] at h
  unfold assoc
  rw [h]
  funext k
  simp only [evalO, lemmaW_R]
  split
  · rw [evalP_psmul]; congr 1
    simp [detP, evalP, evalM, val3, det3c]
    simp only [Int.mul_sub, Int.sub_eq_add_neg, Int.mul_add, Int.mul_assoc, Int.neg_mul, Int.mul_neg]
    omega
  · rfl

end Octonion
