import Caterpillar.LemmaM

/-!
# The moment as a coefficient

Substitute `x = 1 + s e₁`, `y = 1 + q e₂`, `z = 1 + t e₄` into a bracketing `T` of `xᵃyᵇzᶜ`.

* `expand`: multilinear expansion. For all integers `s, q, t`,
  `T(1+se₁, 1+qe₂, 1+te₄) = Σ_{S ⊆ leaves} s^{#x(S)} q^{#y(S)} t^{#z(S)} · T|_S(e₁, e₂, e₄)`
  (`T|_∅ = 1`). So `polyT T`, the list of these terms, is the polynomial of the substituted map
  (`subst_eq`).
* `coef_moment`: the `sᵖ q tʳ` coefficient of `polyT T` is `moment T p r` (Lemma M's sum).
* `coef_of_map`: the map determines these coefficients. If two bracketings agree at the single point
  `s = M, q = M^{n+1}, t = M^{(n+1)²}` with `M = 2^{n+2} + 1` (Kronecker substitution), all their
  coefficients agree (balanced base-`M` digits are unique; coefficients are bounded by `2ⁿ`).
-/

namespace Coeff
open Caterpillar (Tree)
open Octonion PropT LemmaM

/-! ## sums of octonions -/

theorem oadd_comm (x y : O) : oadd x y = oadd y x := by funext k; simp only [oadd]; omega
theorem oadd_assoc (x y z : O) : oadd (oadd x y) z = oadd x (oadd y z) := by funext k; simp only [oadd]; omega
theorem zero_oadd (x : O) : oadd zero x = x := by funext k; simp [oadd, zero]
theorem oadd_zero (x : O) : oadd x zero = x := by funext k; simp [oadd, zero]

theorem osum_append (l l' : List O) : osum (l ++ l') = oadd (osum l) (osum l') := by
  induction l with
  | nil => simp [osum, zero_oadd]
  | cons x l ih => rw [List.cons_append, osum, osum, ih, oadd_assoc]

theorem osum_perm {l l' : List O} (h : l.Perm l') : osum l = osum l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [osum, ih]
  | swap x y l => simp only [osum]; rw [← oadd_assoc, ← oadd_assoc, oadd_comm x y]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem osum_zero {α : Type} (l : List α) (f : α → O) (h : ∀ x ∈ l, f x = zero) : osum (l.map f) = zero := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map, osum, h x (by simp), ih (fun y hy => h y (by simp [hy])), zero_oadd]

theorem osum_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → O) :
    osum ((l.flatMap g).map f) = osum (l.map fun x => osum ((g x).map f)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, osum_append, ih, List.map, osum]

theorem osum_congr {α : Type} (l : List α) (f g : α → O) (h : ∀ x ∈ l, f x = g x) :
    osum (l.map f) = osum (l.map g) := by rw [List.map_congr_left h]

theorem mul_oadd_l (x y z : O) : mul (oadd x y) z = oadd (mul x z) (mul y z) := by
  funext k; simp only [mul, oadd, sum8, Int.mul_add, Int.add_mul]; omega
theorem mul_oadd_r (x y z : O) : mul z (oadd x y) = oadd (mul z x) (mul z y) := by
  funext k; simp only [mul, oadd, sum8, Int.mul_add]; omega
theorem mul_zero_l (x : O) : mul zero x = zero := by funext k; simp [mul, zero, sum8]
theorem mul_zero_r (x : O) : mul x zero = zero := by funext k; simp [mul, zero, sum8]

theorem mul_osum_l {α : Type} (l : List α) (f : α → O) (z : O) :
    mul (osum (l.map f)) z = osum (l.map fun x => mul (f x) z) := by
  induction l with
  | nil => exact mul_zero_l z
  | cons x l ih => simp only [List.map, osum, mul_oadd_l, ih]
theorem mul_osum_r {α : Type} (l : List α) (f : α → O) (z : O) :
    mul z (osum (l.map f)) = osum (l.map fun x => mul z (f x)) := by
  induction l with
  | nil => exact mul_zero_r z
  | cons x l ih => simp only [List.map, osum, mul_oadd_r, ih]

theorem smul_smul_mul (s t : Int) (x y : O) : mul (smul s x) (smul t y) = smul (s * t) (mul x y) := by
  rw [smul_mul, mul_smul]; funext k; simp only [smul]; rw [Int.mul_assoc]

/-- sums over subsets, invariant under reordering the ground list -/
theorem osum_subs_perm {l l' : List Nat} (hp : l.Perm l') : ∀ f : List Nat → O,
    (∀ K K', K.Perm K' → f K = f K') → osum ((subs l).map f) = osum ((subs l').map f) := by
  have cons_eq : ∀ (x : Nat) (l : List Nat) (f : List Nat → O),
      osum ((subs (x :: l)).map f) = oadd (osum ((subs l).map f)) (osum ((subs l).map fun K => f (x :: K))) := by
    intro x l f; simp only [subs, List.map_append, List.map_map, osum_append]; rfl
  induction hp with
  | nil => intro f _; rfl
  | cons x _ ih =>
    intro f hf
    rw [cons_eq, cons_eq, ih f hf, ih (fun K => f (x :: K)) (fun K K' h => hf _ _ (h.cons x))]
  | swap x y l =>
    intro f hf
    simp only [cons_eq]
    have e : (fun K => f (x :: y :: K)) = (fun K => f (y :: x :: K)) := funext fun K => hf _ _ (List.Perm.swap y x K)
    rw [e, oadd_assoc, oadd_assoc, ← oadd_assoc (osum ((subs l).map fun K => f (x :: K))),
      oadd_comm (osum ((subs l).map fun K => f (x :: K))), oadd_assoc]
  | trans _ _ ih1 ih2 => intro f hf; rw [ih1 f hf, ih2 f hf]

/-! ## the multilinear expansion -/

variable (a b : Nat)

/-- all subsets of the leaves, in the order produced by expanding the product -/
def subsT : Tree → List (List Nat)
  | .leaf i => [[], [i]]
  | .node L R => (subsT L).flatMap fun A => (subsT R).map fun B => A ++ B

theorem subsT_sub : ∀ (T : Tree) (S : List Nat), S ∈ subsT T → ∀ i ∈ S, i ∈ lv T
  | .leaf i, S, h, j, hj => by
    simp only [subsT, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp_all [lv]
  | .node L R, S, h, j, hj => by
    simp only [subsT, List.mem_flatMap, List.mem_map] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    simp only [lv, List.mem_append] at hj ⊢
    rcases hj with hj | hj
    · exact Or.inl (subsT_sub L A hA j hj)
    · exact Or.inr (subsT_sub R B hB j hj)

theorem subsT_length : ∀ T : Tree, (subsT T).length = 2 ^ (lv T).length
  | .leaf _ => rfl
  | .node L R => by
    simp only [subsT, lv, List.length_append, Nat.pow_add, ← subsT_length L, ← subsT_length R]
    generalize subsT L = l; induction l with
    | nil => simp
    | cons x l ih => simp [List.flatMap_cons, ih, Nat.add_mul]; omega

/-- `T` restricted to the leaves in `S` -/
def restrictTo (T : Tree) (S : List Nat) : Option Tree := kill (fun i => i) (fun i => !decide (i ∈ S)) T

def ex (S : List Nat) : Nat := (S.filter fun i => decide (i < a)).length
def ey (S : List Nat) : Nat := (S.filter fun i => decide (a ≤ i ∧ i < a + b)).length
def ez (S : List Nat) : Nat := (S.filter fun i => decide (a + b ≤ i)).length

def ipow (s : Int) : Nat → Int
  | 0 => 1
  | n + 1 => ipow s n * s

theorem ipow_add (s : Int) (m : Nat) : ∀ n, ipow s (m + n) = ipow s m * ipow s n
  | 0 => by simp [ipow]
  | n + 1 => by rw [← Nat.add_assoc, ipow, ipow, ipow_add s m n, Int.mul_assoc]

/-- the monomial `s^{#x} q^{#y} t^{#z}` -/
def mono (s q t : Int) (S : List Nat) : Int := ipow s (ex a S) * ipow q (ey a b S) * ipow t (ez a b S)

/-- `x, y, z ↦ 1 + s e₁, 1 + q e₂, 1 + t e₄` -/
def ρs (s q t : Int) (ℓ : Nat) : O := oadd one (smul (if ℓ = 0 then s else if ℓ = 1 then q else t) (unit (ρ3 ℓ)))

theorem kill_congr (K1 K2 : Nat → Bool) : ∀ T : Tree, (∀ i ∈ lv T, K1 i = K2 i) →
    kill (fun i => i) K1 T = kill (fun i => i) K2 T
  | .leaf i, h => by simp [kill, h i (by simp [lv])]
  | .node L R, h => by
    simp only [kill, kill_congr K1 K2 L (fun i hi => h i (by simp [lv, hi])),
      kill_congr K1 K2 R (fun i hi => h i (by simp [lv, hi]))]

theorem evo_node (w : Nat → Nat) (ρ : Nat → O) (W : Nat → Nat) (Kd : Nat → Bool) (L R : Tree) :
    evo w ρ (kill W Kd (.node L R)) = mul (evo w ρ (kill W Kd L)) (evo w ρ (kill W Kd R)) := by
  simp only [kill]
  cases kill W Kd L <;> cases kill W Kd R <;> simp [evo, ev, one_mul, mul_one]

theorem mono_append (s q t : Int) (A B : List Nat) : mono a b s q t (A ++ B) = mono a b s q t A * mono a b s q t B := by
  simp only [mono, ex, ey, ez, List.filter_append, List.length_append, ipow_add]
  simp only [Int.mul_assoc, Int.mul_left_comm]

/-- **the multilinear expansion** -/
theorem expand (s q t : Int) : ∀ T : Tree, (lv T).Pairwise (· < ·) →
    ev (w3 a b) (ρs s q t) T =
      osum ((subsT T).map fun S => smul (mono a b s q t S) (evo (w3 a b) ρO (restrictTo T S)))
  | .leaf i, _ => by
    simp only [subsT, List.map, osum, ev, ρs, restrictTo, kill, List.not_mem_nil, decide_false,
      Bool.not_false, ite_true, List.mem_singleton, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [evo, ev, ρO, mono, ex, ey, ez, List.filter_nil, List.filter_cons, List.length_nil, ipow]
    funext k
    simp only [oadd, smul, zero, w3]
    by_cases h1 : i < a
    · have n1 : ¬ (a ≤ i ∧ i < a + b) := by omega
      have n2 : ¬ a + b ≤ i := by omega
      simp [h1, n1, n2, ipow]
    · by_cases h2 : i < a + b
      · have n2 : ¬ a + b ≤ i := by omega
        simp [h1, h2, n2, show a ≤ i by omega, ipow]
      · simp [h1, h2, show a + b ≤ i by omega, ipow]
  | .node L R, hpw => by
    simp only [lv] at hpw
    have pL := (List.pairwise_append.1 hpw).1; have pR := (List.pairwise_append.1 hpw).2.1
    rw [ev, expand s q t L pL, expand s q t R pR, mul_osum_l]
    simp only [mul_osum_r, subsT, osum_flatMap, List.map_map]
    apply osum_congr; intro A hA; apply osum_congr; intro B hB
    simp only [Function.comp, restrictTo, evo_node, mono_append]
    have eL : kill (fun i => i) (fun i => !decide (i ∈ A ++ B)) L = kill (fun i => i) (fun i => !decide (i ∈ A)) L := by
      apply kill_congr; intro i hi
      have : i ∉ B := fun h => Nat.lt_irrefl i (pw_lt hpw hi (subsT_sub R B hB i h))
      simp [this]
    have eR : kill (fun i => i) (fun i => !decide (i ∈ A ++ B)) R = kill (fun i => i) (fun i => !decide (i ∈ B)) R := by
      apply kill_congr; intro i hi
      have : i ∉ A := fun h => Nat.lt_irrefl i (pw_lt hpw (subsT_sub L A hA i h) hi)
      simp [this]
    rw [eL, eR, smul_smul_mul]

/-! ## the polynomial of the substituted map and its coefficients -/

/-- the polynomial `Σ_S T|_S(e₁,e₂,e₄) · s^{#x} q^{#y} t^{#z}` as a list of (coefficient, exponents) -/
def polyT (T : Tree) : List (O × Nat × Nat × Nat) :=
  (subsT T).map fun S => (evo (w3 a b) ρO (restrictTo T S), ex a S, ey a b S, ez a b S)

def evalPoly (P : List (O × Nat × Nat × Nat)) (s q t : Int) : O :=
  osum (P.map fun m => smul (ipow s m.2.1 * ipow q m.2.2.1 * ipow t m.2.2.2) m.1)

/-- the coefficient of `sⁱ qᵏ tˡ` -/
def coef (P : List (O × Nat × Nat × Nat)) (e : Nat × Nat × Nat) : O :=
  osum (P.map fun m => if m.2 = e then m.1 else zero)

/-- **`polyT T` is the substituted map**: `T(1+se₁, 1+qe₂, 1+te₄) = polyT T (s, q, t)` -/
theorem subst_eq (T : Tree) (hpw : (lv T).Pairwise (· < ·)) (s q t : Int) :
    ev (w3 a b) (ρs s q t) T = evalPoly (polyT a b T) s q t := by
  rw [expand a b s q t T hpw, evalPoly, polyT, List.map_map]; rfl

/-! ### reordering subsets -/

theorem flatMap_map_cons (x : Nat) (l : List (List Nat)) (g : List Nat → List (List Nat))
    (hg : ∀ A, g (x :: A) = (g A).map (x :: ·)) :
    (l.map (x :: ·)).flatMap g = (l.flatMap g).map (x :: ·) := by
  induction l with
  | nil => rfl
  | cons A l ih => simp only [List.map, List.flatMap_cons, hg, ih, List.map_append]

theorem subs_append_perm (l2 : List Nat) : ∀ l1 : List Nat,
    (subs (l1 ++ l2)).Perm ((subs l1).flatMap fun A => (subs l2).map (A ++ ·))
  | [] => by simp [subs]
  | x :: l1 => by
    have ih := subs_append_perm l2 l1
    simp only [List.cons_append, subs, List.flatMap_append]
    rw [flatMap_map_cons x _ (fun A => (subs l2).map (A ++ ·)) (fun A => by simp [List.map_map])]
    exact ih.append (ih.map _)

theorem perm_flatMap {l l' : List (List Nat)} (h : l.Perm l') (g : List Nat → List (List Nat)) :
    (l.flatMap g).Perm (l'.flatMap g) := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih => simp only [List.flatMap_cons]; exact ih.append_left _
  | swap x y l =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem flatMap_congr_perm (l : List (List Nat)) (g g' : List Nat → List (List Nat)) (h : ∀ A, (g A).Perm (g' A)) :
    (l.flatMap g).Perm (l.flatMap g') := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => simp only [List.flatMap_cons]; exact (h x).append ih

theorem subsT_perm : ∀ T : Tree, (subsT T).Perm (subs (lv T))
  | .leaf i => by simp only [subsT, subs, lv, List.map]; exact List.Perm.refl _
  | .node L R => by
    simp only [subsT, lv]
    exact ((flatMap_congr_perm _ _ _ (fun A => (subsT_perm R).map _)).trans
      (perm_flatMap (subsT_perm L) _)).trans (subs_append_perm _ _).symm

/-! ### subsets with exactly one `y` -/

theorem osum_dropY (isY : Nat → Bool) (Z : List Nat) (g : List Nat → O)
    (hg : ∀ S, (∃ x ∈ S, isY x = true) → g S = zero) :
    ∀ Y : List Nat, (∀ y ∈ Y, isY y = true) → osum ((subs (Y ++ Z)).map g) = osum ((subs Z).map g)
  | [], _ => rfl
  | y :: Y, hY => by
    rw [List.cons_append, subs, List.map_append, List.map_map, osum_append]
    rw [osum_dropY isY Z g hg Y (fun y' h => hY y' (by simp [h])),
      osum_zero (subs (Y ++ Z)) (g ∘ fun x => y :: x) (fun S _ => hg _ ⟨y, by simp, hY y (by simp)⟩), oadd_zero]

theorem osum_one (isY : Nat → Bool) (Z : List Nat) (hZ : ∀ z ∈ Z, isY z = false) :
    ∀ (Y : List Nat) (f : List Nat → O), (∀ y ∈ Y, isY y = true) →
      (∀ S, (S.filter isY).length ≠ 1 → f S = zero) →
      osum ((subs (Y ++ Z)).map f) = osum (Y.map fun k => osum ((subs Z).map fun K => f (k :: K)))
  | [], f, _, hf => by
    simp only [List.nil_append, List.map, osum]
    apply osum_zero; intro S hS; apply hf
    have : S.filter isY = [] := List.filter_eq_nil_iff.2 (fun x hx => by
      have := hZ x ((subs_sub Z S hS).subset hx); simp [this])
    simp [this]
  | y :: Y, f, hY, hf => by
    rw [List.cons_append, subs, List.map_append, List.map_map, osum_append, List.map, osum]
    rw [osum_one isY Z hZ Y f (fun y' h => hY y' (by simp [h])) hf, oadd_comm]
    have hy := hY y (by simp)
    have hd : osum (List.map (f ∘ fun x => y :: x) (subs (Y ++ Z))) = osum (List.map (fun K => f (y :: K)) (subs Z)) := by
      apply osum_dropY isY Z (f ∘ fun x => y :: x) _ Y (fun y' h => hY y' (by simp [h]))
      intro S ⟨x, hx, hxy⟩
      show f (y :: S) = zero
      apply hf
      have : 2 ≤ ((y :: S).filter isY).length := by
        rw [List.filter_cons_of_pos hy, List.length_cons]
        have : x ∈ S.filter isY := List.mem_filter.2 ⟨hx, hxy⟩
        have := List.length_pos_of_mem this; omega
      omega
    rw [hd]

/-! ### the coefficient is the moment -/

def isY (i : Nat) : Bool := decide (a ≤ i ∧ i < a + b)

theorem count_map_true (f : Nat → Bool) : ∀ K : List Nat, (K.map f).count true = (K.filter f).length
  | [] => rfl
  | x :: K => by
    cases h : f x <;> simp [h, count_map_true f K]

theorem count_map_false (f : Nat → Bool) : ∀ K : List Nat, (K.map f).count false = (K.filter fun i => !f i).length
  | [] => rfl
  | x :: K => by
    cases h : f x <;> simp [h, count_map_false f K]

theorem range_split (c : Nat) : List.range' 0 (a + b + c) = List.range' 0 a ++ List.range' a b ++ List.range' (a + b) c := by
  have h1 : List.range' 0 a ++ List.range' (0 + a) b = List.range' 0 (a + b) := List.range'_append_1
  have h2 : List.range' 0 (a + b) ++ List.range' (0 + (a + b)) c = List.range' 0 (a + b + c) := List.range'_append_1
  simp only [Nat.zero_add] at h1 h2
  rw [h1, h2]

theorem filter_isY (c : Nat) : (List.range' 0 (a + b + c)).filter (isY a b) = List.range' a b := by
  rw [range_split, List.filter_append, List.filter_append]
  rw [List.filter_eq_nil_iff.2 (fun x hx => by simp [List.mem_range'_1] at hx; simp [isY]; omega),
    List.filter_eq_self.2 (fun x hx => by simp [List.mem_range'_1] at hx; simp [isY]; omega),
    List.filter_eq_nil_iff.2 (fun x hx => by simp [List.mem_range'_1] at hx; simp [isY]; omega)]
  simp

theorem filter_notY (c : Nat) : (List.range' 0 (a + b + c)).filter (fun i => !isY a b i) = XZ a b c := by
  simp only [XZ]; apply List.filter_congr; intro i _
  simp only [isY, nonY]
  by_cases h1 : i < a <;> by_cases h2 : a + b ≤ i <;> simp [h1, h2] <;> omega

section
variable (c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T : Tree) (h : TB a b c T)
include ha hb hc h

/-- **the moment is the `sᵖ q tʳ` coefficient of the substituted map** -/
theorem coef_moment (p r : Nat) : coef (polyT a b T) (p, 1, r) = moment a b c T p r := by
  have hlv := lvT a b c ha hb hc T h
  simp only [coef, polyT, List.map_map]
  let g : List Nat → O := fun S => if (ex a S, ey a b S, ez a b S) = (p, 1, r) then evo (w3 a b) ρO (restrictTo T S) else zero
  have eg : ((fun m : O × Nat × Nat × Nat => if m.2 = (p, 1, r) then m.1 else zero) ∘
      fun S => (evo (w3 a b) ρO (restrictTo T S), ex a S, ey a b S, ez a b S)) = g := rfl
  rw [eg, osum_perm ((subsT_perm T).map g), hlv]
  have pY : (List.range' 0 (a + b + c)).Perm (List.range' a b ++ XZ a b c) := by
    rw [← filter_isY a b c, ← filter_notY a b c]; exact (List.filter_append_perm _ _).symm
  rw [osum_subs_perm pY g (by
    intro K K' hp
    have e1 : ∀ f : Nat → Bool, (K.filter f).length = (K'.filter f).length := fun f => (hp.filter f).length_eq
    have he : (ex a K, ey a b K, ez a b K) = (ex a K', ey a b K', ez a b K') := by simp only [ex, ey, ez, e1]
    have e2 : restrictTo T K = restrictTo T K' := by
      simp only [restrictTo]; congr 1; funext i; simp [hp.mem_iff]
    simp only [g, he, e2])]
  rw [osum_one (isY a b) (XZ a b c) (fun z hz => by
      simp only [XZ, List.mem_filter, nonY, decide_eq_true_eq] at hz; simp [isY]; omega)
    (List.range' a b) g (fun y hy => by simp [List.mem_range'_1] at hy; simp [isY]; omega)
    (fun S hS => by
      simp only [g]; rw [ite_eq_right]; intro e; simp only [Prod.mk.injEq] at e; apply hS; simp only [ey] at e
      rw [← e.2.1]; rfl)]
  simp only [moment]
  apply osum_congr; intro k hk; apply osum_congr; intro K hK
  simp only [List.mem_range'_1] at hk
  have sub : ∀ i ∈ K, nonY a b i = true := fun i hi =>
    (List.mem_filter.1 ((subs_sub _ K hK).subset hi)).2
  have hx : ex a (k :: K) = ex a K := by simp [ex, show ¬ k < a by omega]
  have hz : ez a b (k :: K) = ez a b K := by simp [ez, show ¬ a + b ≤ k by omega]
  have hy : ey a b (k :: K) = 1 := by
    have : K.filter (fun i => decide (a ≤ i ∧ i < a + b)) = [] := List.filter_eq_nil_iff.2 (fun i hi => by
      have := sub i hi; simp only [nonY, decide_eq_true_eq] at this; simp only [decide_eq_true_eq]; omega)
    rw [ey, List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega), List.length_cons, this]; rfl
  have hct : (K.map (lb a)).count true = ex a K := by rw [count_map_true]; rfl
  have hcf : (K.map (lb a)).count false = ez a b K := by
    rw [count_map_false]; simp only [ez]; congr 1; apply List.filter_congr; intro i hi
    have := sub i hi; simp only [nonY, decide_eq_true_eq] at this
    by_cases h1 : i < a <;> simp [lb, h1] <;> omega
  have hres : restrictTo T (k :: K) = restrict T k K := by
    simp only [restrictTo, restrict]; congr 1; funext i; simp [keepK]
  simp only [g, hx, hy, hz, hres, condB, hct, hcf, Prod.mk.injEq, true_and]
  by_cases e : ex a K = p ∧ ez a b K = r <;> simp [e]

end

/-! ## the map determines the coefficients (Kronecker substitution) -/

theorem osum_apply {α : Type} (l : List α) (f : α → O) (k : Fin 8) : (osum (l.map f)) k = isum (l.map fun x => f x k) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map, osum, isum, oadd, ih]

/-- base-`M` value of the digits `D 0, …, D (N−1)` -/
def dsum (M : Int) (D : Nat → Int) : Nat → Int
  | 0 => 0
  | N + 1 => D 0 + M * dsum M (fun e => D (e + 1)) N

theorem dsum_add (M : Int) : ∀ N (D1 D2 : Nat → Int), dsum M (fun e => D1 e + D2 e) N = dsum M D1 N + dsum M D2 N
  | 0, _, _ => rfl
  | N + 1, D1, D2 => by simp only [dsum, dsum_add M N (fun e => D1 (e + 1)) (fun e => D2 (e + 1)), Int.mul_add]; omega

theorem dsum_sub (M : Int) : ∀ N (D1 D2 : Nat → Int), dsum M (fun e => D1 e - D2 e) N = dsum M D1 N - dsum M D2 N
  | 0, _, _ => rfl
  | N + 1, D1, D2 => by simp only [dsum, dsum_sub M N (fun e => D1 (e + 1)) (fun e => D2 (e + 1)), Int.mul_sub]; omega

theorem dsum_zero (M : Int) : ∀ N, dsum M (fun _ => 0) N = 0
  | 0 => rfl
  | N + 1 => by simp only [dsum, dsum_zero M N]; simp

theorem dsum_single (M : Int) (d : Int) : ∀ (N e0 : Nat), e0 < N → dsum M (fun e => if e0 = e then d else 0) N = ipow M e0 * d
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, 0, _ => by
    simp only [dsum, ite_true]
    have : (fun e => if 0 = e + 1 then d else (0 : Int)) = fun _ => 0 := funext fun e => by simp
    rw [this, dsum_zero]; simp [ipow]
  | N + 1, e0 + 1, h => by
    simp only [dsum, show ¬ (e0 + 1 = 0) by omega, ite_false, Nat.add_right_cancel_iff]
    rw [dsum_single M d N e0 (by omega), ipow]; simp only [Int.zero_add]
    rw [Int.mul_comm (ipow M e0) M, Int.mul_assoc]

/-- regroup a sum of monomials by exponent -/
theorem regroup (M : Int) (E : List Nat → Nat) (v : List Nat → Int) (N : Nat) :
    ∀ L : List (List Nat), (∀ S ∈ L, E S < N) →
      isum (L.map fun S => ipow M (E S) * v S) = dsum M (fun e => isum (L.map fun S => if E S = e then v S else 0)) N
  | [], _ => by simp only [List.map, isum]; rw [dsum_zero]
  | S :: L, h => by
    simp only [List.map, isum]
    rw [dsum_add M N (fun e => if E S = e then v S else 0), dsum_single M (v S) N (E S) (h S (by simp)),
      regroup M E v N L (fun S' h' => h S' (by simp [h']))]

/-- **balanced base-`M` digits are unique** -/
theorem digits_zero (M : Int) (hM : 0 < M) : ∀ (N : Nat) (D : Nat → Int), (∀ e < N, -M < 2 * D e ∧ 2 * D e < M) →
    dsum M D N = 0 → ∀ e < N, D e = 0
  | 0, _, _, _, e, he => absurd he (Nat.not_lt_zero _)
  | N + 1, D, hb, hs, e, he => by
    simp only [dsum] at hs
    have b0 := hb 0 (by omega)
    have hr : dsum M (fun e => D (e + 1)) N = 0 := by
      apply Classical.byContradiction; intro hne
      rcases Int.lt_or_gt_of_ne hne with hl | hl
      · have : M * dsum M (fun e => D (e + 1)) N ≤ -M := by
          have := Int.mul_le_mul_of_nonneg_left (show dsum M (fun e => D (e + 1)) N ≤ -1 by omega) (Int.le_of_lt hM)
          simpa using this
        omega
      · have : M ≤ M * dsum M (fun e => D (e + 1)) N := by
          have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ dsum M (fun e => D (e + 1)) N by omega) (Int.le_of_lt hM)
          simpa using this
        omega
    rw [hr, Int.mul_zero, Int.add_zero] at hs
    cases e with
    | zero => exact hs
    | succ e => exact digits_zero M hM N (fun e => D (e + 1)) (fun e' h' => hb (e' + 1) (by omega)) hr e (by omega)

theorem ipow_mul (M : Int) (A : Nat) : ∀ e, ipow (ipow M A) e = ipow M (A * e)
  | 0 => by simp [ipow]
  | e + 1 => by rw [ipow, ipow_mul M A e, Nat.mul_succ, ipow_add]

theorem sgn_pm : ∀ i j : Fin 8, sgn i j = 1 ∨ sgn i j = -1 := by decide

theorem uev_sign (w : Nat → Nat) (ρ : Nat → Fin 8) : ∀ T, (uev w ρ T).1 = 1 ∨ (uev w ρ T).1 = -1
  | .leaf _ => Or.inl rfl
  | .node L R => by
    simp only [uev, mu]
    rcases uev_sign w ρ L with h1 | h1 <;> rcases uev_sign w ρ R with h2 | h2 <;>
      rcases sgn_pm (uev w ρ L).2 (uev w ρ R).2 with h3 | h3 <;> simp [h1, h2, h3]

/-- every term of the expansion has coordinates in `{−1, 0, 1}` -/
theorem term_bound (U : Tree) (S' : List Nat) (k : Fin 8) :
    -1 ≤ evo (w3 a b) ρO (restrictTo U S') k ∧ evo (w3 a b) ρO (restrictTo U S') k ≤ 1 := by
  cases restrictTo U S' with
  | none => simp only [evo, one, unit]; split <;> omega
  | some V =>
    simp only [evo]
    show -1 ≤ ev (w3 a b) (fun ℓ => unit (ρ3 ℓ)) V k ∧ ev (w3 a b) (fun ℓ => unit (ρ3 ℓ)) V k ≤ 1
    rw [ev_uev]; simp only [toO, smul, unit]
    rcases uev_sign (w3 a b) ρ3 V with h | h <;> rw [h] <;> split <;> omega

theorem isum_bound (f : List Nat → Int) (hf : ∀ S, -1 ≤ f S ∧ f S ≤ 1) :
    ∀ L : List (List Nat), -(L.length : Int) ≤ isum (L.map f) ∧ isum (L.map f) ≤ L.length
  | [] => by simp [isum]
  | S :: L => by
    have := isum_bound f hf L; have := hf S
    simp only [List.map, isum, List.length_cons]; push_cast; omega

def kron (n : Nat) (S : List Nat) : Nat := ex a S + (n + 1) * (ey a b S + (n + 1) * ez a b S)
def kron0 (i j l n : Nat) : Nat := i + (n + 1) * (j + (n + 1) * l)

theorem kron_inj (A x y z x' y' z' : Nat) (hA : 0 < A) (hx : x < A) (hx' : x' < A) (hy : y < A) (hy' : y' < A)
    (h : x + A * (y + A * z) = x' + A * (y' + A * z')) : x = x' ∧ y = y' ∧ z = z' := by
  have e1 : x = x' := by
    have := congrArg (· % A) h; simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at this
    exact this
  subst e1
  have h2 : y + A * z = y' + A * z' := Nat.eq_of_mul_eq_mul_left hA (by omega)
  have e2 : y = y' := by
    have := congrArg (· % A) h2; simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hy'] at this
    exact this
  subst e2
  exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hA (by omega)⟩

theorem sub_len (T : Tree) (S : List Nat) (hS : S ∈ subsT T) :
    S.length ≤ (lv T).length := by
  have hsub : S.Sublist (lv T) := by
    have := (subsT_perm T).mem_iff.1 hS; exact subs_sub _ S this
  exact hsub.length_le

theorem ipow_two (n : Nat) : ipow 2 n = ((2 ^ n : Nat) : Int) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ipow, ih, Nat.pow_succ]; push_cast; rfl

theorem ex_le (S : List Nat) : ex a S ≤ S.length := List.length_filter_le _ _
theorem ey_le (S : List Nat) : ey a b S ≤ S.length := List.length_filter_le _ _
theorem ez_le (S : List Nat) : ez a b S ≤ S.length := List.length_filter_le _ _

section
variable (c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T T' : Tree) (h : TB a b c T) (h' : TB a b c T')
include ha hb hc h h'

/-- **the map determines the coefficients.** Agreement at the single Kronecker point
`s = M, q = M^{n+1}, t = M^{(n+1)²}`, `M = 2^{n+2} + 1`, forces equal coefficients. -/
theorem coef_of_map
    (hev : ev (w3 a b) (ρs (ipow 2 (a + b + c + 2) + 1) (ipow (ipow 2 (a + b + c + 2) + 1) (a + b + c + 1))
        (ipow (ipow 2 (a + b + c + 2) + 1) ((a + b + c + 1) * (a + b + c + 1)))) T =
      ev (w3 a b) (ρs (ipow 2 (a + b + c + 2) + 1) (ipow (ipow 2 (a + b + c + 2) + 1) (a + b + c + 1))
        (ipow (ipow 2 (a + b + c + 2) + 1) ((a + b + c + 1) * (a + b + c + 1)))) T')
    (i j l : Nat) (hi : i ≤ a + b + c) (hj : j ≤ a + b + c) (hl : l ≤ a + b + c) :
    coef (polyT a b T) (i, j, l) = coef (polyT a b T') (i, j, l) := by
  generalize hn : a + b + c = n at hev hi hj hl
  generalize hM : ipow 2 (n + 2) + 1 = M at hev
  have X0 : (0 : Int) ≤ ((2 ^ n : Nat) : Int) := Int.natCast_nonneg _
  have hM4 : M = 4 * ((2 ^ n : Nat) : Int) + 1 := by
    rw [← hM, ipow_two, show n + 2 = n + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]; push_cast; omega
  have hM0 : 0 < M := by omega
  have lenT : (lv T).length = n := by rw [lvT a b c ha hb hc T h, List.length_range']; omega
  have lenT' : (lv T').length = n := by rw [lvT a b c ha hb hc T' h', List.length_range']; omega
  let A := n + 1
  let N := A + A * (A + A * A)
  have kb : ∀ (U : Tree), (lv U).length = n → ∀ S ∈ subsT U, kron a b n S < N := by
    intro U hU S hS
    have := sub_len U S hS
    have e1 := ex_le a S; have e2 := ey_le a b S; have e3 := ez_le a b S
    simp only [kron, N, A]
    have m1 : (n + 1) * ez a b S ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    have m2 : (n + 1) * (ey a b S + (n + 1) * ez a b S) ≤ (n + 1) * ((n + 1) + (n + 1) * (n + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  let v : Tree → List Nat → Fin 8 → Int := fun U S k => evo (w3 a b) ρO (restrictTo U S) k
  let C : Tree → Fin 8 → Nat → Int := fun U k e => isum ((subsT U).map fun S => if kron a b n S = e then v U S k else 0)
  have evC : ∀ U : Tree, TB a b c U → (lv U).length = n → ∀ k,
      ev (w3 a b) (ρs M (ipow M (n + 1)) (ipow M ((n + 1) * (n + 1)))) U k = dsum M (C U k) N := by
    intro U hU hlen k
    rw [subst_eq a b U (pw_wf U hU.wf), evalPoly, polyT, List.map_map, osum_apply]
    rw [← regroup M (kron a b n) (fun S => v U S k) N (subsT U) (kb U hlen)]
    congr 1; apply List.map_congr_left; intro S _
    simp only [Function.comp, smul, ipow_mul, kron, v]
    rw [← ipow_add, ← ipow_add]
    congr 2; rw [Nat.mul_assoc (n + 1) (n + 1), Nat.mul_add (n + 1) (ey a b S)]; omega
  have hbound : ∀ U : Tree, (lv U).length = n → ∀ k e, -((2 ^ n : Nat) : Int) ≤ C U k e ∧ C U k e ≤ ((2 ^ n : Nat) : Int) := by
    intro U hU k e
    have := isum_bound (fun S => if kron a b n S = e then v U S k else 0) (fun S => by
      by_cases hk : kron a b n S = e
      · simp only [hk, ite_true]; exact term_bound a b U S k
      · simp only [hk, ite_false]; omega) (subsT U)
    rw [subsT_length, hU] at this; exact this
  have coefC : ∀ U : Tree, (lv U).length = n → ∀ k,
      coef (polyT a b U) (i, j, l) k = C U k (kron0 i j l n) := by
    intro U hU k
    simp only [coef, polyT, List.map_map, osum_apply]
    apply congrArg isum; apply List.map_congr_left; intro S hS
    have := sub_len U S hS
    have e1 := ex_le a S; have e2 := ey_le a b S
    simp only [Function.comp, v]
    by_cases e : (ex a S, ey a b S, ez a b S) = (i, j, l)
    · simp only [Prod.mk.injEq] at e; obtain ⟨r1, r2, r3⟩ := e
      have ke : kron a b n S = kron0 i j l n := by simp only [kron, kron0, r1, r2, r3]
      simp only [r1, r2, r3, ke, ite_true]
    · have ne : kron a b n S ≠ kron0 i j l n := by
        simp only [kron, kron0]; intro e'
        obtain ⟨r1, r2, r3⟩ := kron_inj (n + 1) _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) e'
        exact e (by rw [r1, r2, r3])
      rw [ite_eq_right e, ite_eq_right ne]; simp [zero]
  funext k
  rw [coefC T lenT k, coefC T' lenT' k]
  have hd : dsum M (fun e => C T k e - C T' k e) N = 0 := by
    have e1 := evC T h lenT k; have e2 := evC T' h' lenT' k
    rw [dsum_sub, ← e1, ← e2, hev]; omega
  have := digits_zero M hM0 N (fun e => C T k e - C T' k e) (fun e _ => by
    show -M < 2 * (C T k e - C T' k e) ∧ 2 * (C T k e - C T' k e) < M
    have b1 := hbound T lenT k e; have b2 := hbound T' lenT' k e; omega) hd (kron0 i j l n) (by
    simp only [kron0, N, A]
    have m1 : (n + 1) * l ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    have m2 : (n + 1) * (j + (n + 1) * l) ≤ (n + 1) * ((n + 1) + (n + 1) * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
    omega)
  exact Int.sub_eq_zero.mp this

end

end Coeff
