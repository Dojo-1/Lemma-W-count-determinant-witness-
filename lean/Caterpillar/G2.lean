import Caterpillar.Kill

/-!
# G2: the parts of Propositions T and C formalized here

* `propT_count`: the counting identity of Proposition T,
  `(b−1)(C(a+c,a) − 1) + C(a+c−1,a) + C(a+c−1,c) = 1 + b·(C(a+c,a) − 1)` for `a, c ≥ 1`, and the
  interior sum `Σ_{p<a, q<c} C(p+q, p) = C(a+c, a) − 1`.
* `propC_forward`: the core of Proposition C (⇒). In an interval word (letters non-decreasing along
  the word), a flip `(AB)C → A(BC)` whose segments contain pairwise distinct letters `x ∈ A, y ∈ B,
  z ∈ C` is not a `D_N`-flip: the `(x, y, z)` minor of its count matrix is positive. So `D_N`-flips
  change no shape of a distinct-letter triple.
-/

namespace Octonion
open Caterpillar (Tree)

/-! ## Proposition T: counting -/

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_gt : ∀ n k, n < k → choose n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]

/-- `C(n, n) = 1` -/
theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_gt n (n + 1) (by omega)]

/-- symmetric form `Bn a c = C(a+c, a)` -/
def Bn (a c : Nat) : Nat := choose (a + c) a

theorem B_zero_left (c : Nat) : Bn 0 c = 1 := by simp [Bn, choose_zero_right]
theorem B_zero_right (a : Nat) : Bn a 0 = 1 := by simp [Bn, choose_self]

/-- Pascal in symmetric form -/
theorem B_succ (a c : Nat) : Bn (a + 1) (c + 1) = Bn a (c + 1) + Bn (a + 1) c := by
  simp only [Bn]
  have h1 : a + 1 + (c + 1) = (a + (c + 1)) + 1 := by omega
  have h2 : a + 1 + c = a + (c + 1) := by omega
  rw [h1, choose_succ_succ, h2]

/-- hockey stick along one row: `Σ_{q<c} B(p, q) = B(p+1, c−1)`, written for `c + 1` -/
def rowSum (p : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => rowSum p q + Bn p q

theorem rowSum_eq (p : Nat) : ∀ c, rowSum p (c + 1) = Bn (p + 1) c
  | 0 => by simp [rowSum, B_zero_right]
  | c + 1 => by
    rw [rowSum, rowSum_eq p c, B_succ]
    omega

/-- the interior sum `S a c = Σ_{p<a, q<c} B(p, q)` -/
def S : Nat → Nat → Nat
  | 0, _ => 0
  | p + 1, c => S p c + rowSum p c

/-- **Proposition T, interior count.** `Σ_{p<a, q<c} C(p+q, p) = C(a+c, a) − 1`. -/
theorem propT_interior : ∀ a c, S a c + 1 = Bn a c
  | 0, c => by simp [S, B_zero_left]
  | a + 1, 0 => by
    have : ∀ p, rowSum p 0 = 0 := fun _ => rfl
    have h0 : ∀ a, S a 0 = 0 := by
      intro a; induction a with
      | zero => rfl
      | succ a ih => simp [S, ih, this]
    simp [h0, B_zero_right]
  | a + 1, c + 1 => by
    simp only [S]
    rw [rowSum_eq a c]
    have := propT_interior a (c + 1)
    rw [B_succ]; omega

/-- **Proposition T, total count.** For `a, c ≥ 1`:
`(b−1)(C(a+c,a) − 1) + C(a+c−1,a) + C(a+c−1,c) = 1 + b·(C(a+c,a) − 1)`. -/
theorem propT_count (a b c : Nat) (hb : 1 ≤ b) :
    (b - 1) * (Bn (a + 1) (c + 1) - 1) + Bn (a + 1) c + Bn a (c + 1) = 1 + b * (Bn (a + 1) (c + 1) - 1) := by
  have hP := B_succ a c
  have hpos : 1 ≤ Bn a (c + 1) := by have := propT_interior a (c + 1); omega
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [hP]
  have e : Bn a (c + 1) + Bn (a + 1) c - 1 = (Bn a (c + 1) - 1) + Bn (a + 1) c := by omega
  rw [e, Nat.succ_mul, Nat.mul_add]
  omega

/-! ## Proposition C (⇒) -/

theorem cnt_eq_count (w : Nat → Nat) (ℓ : Nat) : ∀ T, cnt w ℓ T = ((lettersT w T).count ℓ : Int)
  | .leaf i => by
    simp only [cnt, lettersT]
    by_cases h : w i = ℓ
    · subst h; simp
    · simp [List.count_cons, h]
  | .node l r => by
    simp only [cnt, lettersT, List.count_append, cnt_eq_count w ℓ l, cnt_eq_count w ℓ r]; push_cast; rfl

theorem count_zero_of {L : List Nat} {ℓ : Nat} (h : ∀ m ∈ L, m ≠ ℓ) : L.count ℓ = 0 :=
  List.count_eq_zero.2 (fun hm => h ℓ hm rfl)

theorem count_pos_of {L : List Nat} {ℓ : Nat} (h : ℓ ∈ L) : 0 < L.count ℓ :=
  List.count_pos_iff.2 h

/-- **Proposition C (⇒), core.** In an interval word the letters along `A, B, C` are non-decreasing.
If `A, B, C` contain pairwise distinct letters `x, y, z`, the `(x, y, z)` minor is positive, so the flip
`(AB)C → A(BC)` is not a `D_N`-flip. -/
theorem propC_forward (w : Nat → Nat) (A TB C : Tree)
    (hs : List.Pairwise (· ≤ ·) (lettersT w A ++ lettersT w TB ++ lettersT w C))
    (x y z : Nat) (hx : x ∈ lettersT w A) (hy : y ∈ lettersT w TB) (hz : z ∈ lettersT w C)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    0 < minor w A TB C x y z ∧ ¬ DN w A TB C := by
  rw [List.pairwise_append, List.pairwise_append] at hs
  obtain ⟨⟨_, _, hAB⟩, _, hABC⟩ := hs
  have hAC : ∀ a ∈ lettersT w A, ∀ c ∈ lettersT w C, a ≤ c := fun a ha c hc => hABC a (by simp [ha]) c hc
  have hBC : ∀ b ∈ lettersT w TB, ∀ c ∈ lettersT w C, b ≤ c := fun b hb c hc => hABC b (by simp [hb]) c hc
  have lxy : x < y := by have := hAB x hx y hy; omega
  have lyz : y < z := by have := hBC y hy z hz; omega
  -- zero entries
  have aZ : (lettersT w A).count z = 0 := count_zero_of fun m hm => by have := hAB m hm y hy; omega
  have cX : (lettersT w C).count x = 0 := count_zero_of fun m hm => by have := hBC y hy m hm; omega
  have bz_cy : 0 < (lettersT w TB).count z → (lettersT w C).count y = 0 := by
    intro h; apply count_zero_of; intro m hm
    have := hBC z (List.count_pos_iff.1 h) m hm; omega
  have bx_ay : 0 < (lettersT w TB).count x → (lettersT w A).count y = 0 := by
    intro h; apply count_zero_of; intro m hm
    have := hAB m hm x (List.count_pos_iff.1 h); omega
  have pa := count_pos_of hx; have pb := count_pos_of hy; have pc := count_pos_of hz
  have t1 : (lettersT w TB).count z * (lettersT w C).count y = 0 := by
    rcases Nat.eq_zero_or_pos ((lettersT w TB).count z) with h | h
    · simp [h]
    · simp [bz_cy h]
  have t2 : (lettersT w A).count y * (lettersT w TB).count x = 0 := by
    rcases Nat.eq_zero_or_pos ((lettersT w TB).count x) with h | h
    · simp [h]
    · simp [bx_ay h]
  have hpos : 0 < (lettersT w A).count x * ((lettersT w TB).count y * (lettersT w C).count z) :=
    Nat.mul_pos pa (Nat.mul_pos pb pc)
  have e1 : (lettersT w A).count x * ((lettersT w TB).count z * (lettersT w C).count y) = 0 := by
    rw [t1]; simp
  have e2 : (lettersT w A).count y * ((lettersT w TB).count x * (lettersT w C).count z) = 0 := by
    rw [← Nat.mul_assoc, t2]; simp
  have hpos' : (0 : Int) < ((lettersT w A).count x : Int) * (((lettersT w TB).count y : Int) * (lettersT w C).count z) := by
    exact_mod_cast hpos
  have e1' : ((lettersT w A).count x : Int) * (((lettersT w TB).count z : Int) * (lettersT w C).count y) = 0 := by
    exact_mod_cast e1
  have e2' : ((lettersT w A).count y : Int) * (((lettersT w TB).count x : Int) * (lettersT w C).count z) = 0 := by
    exact_mod_cast e2
  have aZ' : ((lettersT w A).count z : Int) = 0 := by rw [aZ]; rfl
  have cX' : ((lettersT w C).count x : Int) = 0 := by rw [cX]; rfl
  have : minor w A TB C x y z > 0 := by
    simp only [minor, cnt_eq_count, aZ', cX', Int.mul_zero, Int.zero_mul, Int.sub_zero,
      Int.add_zero, Int.mul_sub]
    omega
  exact ⟨this, fun h => by have := h x y z; omega⟩

end Octonion
