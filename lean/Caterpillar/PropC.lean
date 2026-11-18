import Caterpillar.Lift

/-!
# Proposition C (⇐): σ-classes are `D_N`-connected

For a bracketing `T` and leaves `i < j < k`, `sh T i j k = true` iff `T` induces `((ij)k)` on them.
`SigEq w T T'` says `T, T'` induce the same shape on every leaf triple with pairwise distinct letters.

**`propC_backward`.** For an interval word (`w` non-decreasing along positions) and bracketings
`T, T'` of the same increasing leaf list, `SigEq w T T'` implies that `T, T'` are joined by
`D_N`-flips. The proof is the manuscript's induction on root splits:
* equal splits: induction on both sides;
* unequal splits: no distinct-letter triple crosses the three segments, so either the word has ≤ 2
  letters on these leaves (`two_conn`: then every flip is a `D_N`-flip and rotations connect all
  bracketings), or the first two segments carry one letter, or the last two do; one `D_N`-flip then
  reduces to equal splits.

With `propC_forward` this gives Proposition C: `D_N`-components = σ-classes (`propC`).
-/

namespace Octonion
open Caterpillar (Tree)

/-! ## reachability -/

theorem DReach.single {R : Tree → Tree → Prop} {T U : Tree} (h : R T U) : DReach R T U :=
  DReach.tail (DReach.refl T) h

theorem DReach.trans {R : Tree → Tree → Prop} {T U V : Tree} (h1 : DReach R T U) (h2 : DReach R U V) :
    DReach R T V := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact DReach.tail ih h

theorem DNStep.symm {w : Nat → Nat} {T U : Tree} (h : DNStep w T U) : DNStep w U T := by
  cases h with
  | fwd c A B C hd => exact DNStep.bwd c A B C hd
  | bwd c A B C hd => exact DNStep.fwd c A B C hd

theorem DReach.symm {w : Nat → Nat} {T U : Tree} (h : DReach (DNStep w) T U) : DReach (DNStep w) U T := by
  induction h with
  | refl => exact DReach.refl _
  | tail _ h ih => exact DReach.trans (DReach.single h.symm) ih

theorem step_inL {w : Nat → Nat} {S S' : Tree} (R : Tree) (h : DNStep w S S') :
    DNStep w (.node S R) (.node S' R) := by
  cases h with
  | fwd c A B C hd => exact DNStep.fwd (.inL c R) A B C hd
  | bwd c A B C hd => exact DNStep.bwd (.inL c R) A B C hd

theorem step_inR {w : Nat → Nat} (L : Tree) {S S' : Tree} (h : DNStep w S S') :
    DNStep w (.node L S) (.node L S') := by
  cases h with
  | fwd c A B C hd => exact DNStep.fwd (.inR L c) A B C hd
  | bwd c A B C hd => exact DNStep.bwd (.inR L c) A B C hd

theorem reach_inL {w : Nat → Nat} {S S' : Tree} (R : Tree) (h : DReach (DNStep w) S S') :
    DReach (DNStep w) (.node S R) (.node S' R) := by
  induction h with
  | refl => exact DReach.refl _
  | tail _ h ih => exact DReach.tail ih (step_inL R h)

theorem reach_inR {w : Nat → Nat} (L : Tree) {S S' : Tree} (h : DReach (DNStep w) S S') :
    DReach (DNStep w) (.node L S) (.node L S') := by
  induction h with
  | refl => exact DReach.refl _
  | tail _ h ih => exact DReach.tail ih (step_inR L h)

/-! ## minors -/

theorem cnt_const (w : Nat → Nat) (y : Nat) (p : Nat) :
    ∀ T, (∀ i ∈ lv T, w i = y) → cnt w p T = if p = y then cnt w y T else 0
  | .leaf i, h => by
    have := h i (by simp [lv]); simp only [cnt]
    by_cases hp : p = y
    · subst hp; simp
    · simp only [hp, if_false]; rw [this]; simp [Ne.symm hp]
  | .node l r, h => by
    have hl := cnt_const w y p l (fun i hi => h i (by simp [lv, hi]))
    have hr := cnt_const w y p r (fun i hi => h i (by simp [lv, hi]))
    simp only [cnt, hl, hr]; split <;> simp

theorem cnt_zero (w : Nat → Nat) (p : Nat) : ∀ T, (∀ i ∈ lv T, w i ≠ p) → cnt w p T = 0
  | .leaf i, h => by simp [cnt, h i (by simp [lv])]
  | .node l r, h => by
    simp only [cnt, cnt_zero w p l (fun i hi => h i (by simp [lv, hi])),
      cnt_zero w p r (fun i hi => h i (by simp [lv, hi]))]; rfl

theorem minor_pq (w : Nat → Nat) (A B C : Tree) (p r : Nat) : minor w A B C p p r = 0 := by
  simp only [minor]; simp [Int.sub_self]
theorem minor_qr (w : Nat → Nat) (A B C : Tree) (p q : Nat) : minor w A B C p q q = 0 := by
  simp only [minor, Int.sub_self, Int.mul_zero, Int.zero_add, Int.zero_sub]; omega
theorem minor_pr (w : Nat → Nat) (A B C : Tree) (p q : Nat) : minor w A B C p q p = 0 := by
  simp only [minor]
  have e1 : cnt w q B * cnt w p C - cnt w p B * cnt w q C = -(cnt w p B * cnt w q C - cnt w q B * cnt w p C) := by
    omega
  rw [e1]
  simp only [Int.mul_neg]; omega

/-- all letters in `{a, c}`: every flip is a `D_N`-flip -/
theorem dn_two (w : Nat → Nat) (a c : Nat) (A B C : Tree)
    (h : ∀ i ∈ lv A ++ lv B ++ lv C, w i = a ∨ w i = c) : DN w A B C := by
  intro p q r
  by_cases hpq : p = q; · subst hpq; exact minor_pq ..
  by_cases hqr : q = r; · subst hqr; exact minor_qr ..
  by_cases hpr : p = r; · subst hpr; exact minor_pr ..
  have z : ∀ s, s ≠ a → s ≠ c → ∀ T, (∀ i ∈ lv T, w i = a ∨ w i = c) → cnt w s T = 0 := by
    intro s ha hc T hT; apply cnt_zero; intro i hi e; rcases hT i hi with h' | h' <;> omega
  have hA : ∀ i ∈ lv A, w i = a ∨ w i = c := fun i hi => h i (by simp [hi])
  have hB : ∀ i ∈ lv B, w i = a ∨ w i = c := fun i hi => h i (by simp [hi])
  have hC : ∀ i ∈ lv C, w i = a ∨ w i = c := fun i hi => h i (by simp [hi])
  by_cases hp : p = a ∨ p = c
  · by_cases hq : q = a ∨ q = c
    · have hr1 : r ≠ a := by omega
      have hr2 : r ≠ c := by omega
      simp only [minor, z r hr1 hr2 A hA, z r hr1 hr2 B hB, z r hr1 hr2 C hC]; simp
    · simp only [minor, z q (by omega) (by omega) A hA, z q (by omega) (by omega) B hB, z q (by omega) (by omega) C hC]
      simp
  · simp only [minor, z p (by omega) (by omega) A hA, z p (by omega) (by omega) B hB, z p (by omega) (by omega) C hC]
    simp

/-- two rows carry one letter `y` only: the flip is a `D_N`-flip -/
theorem dn_AB (w : Nat → Nat) (y : Nat) (A B C : Tree) (hA : ∀ i ∈ lv A, w i = y) (hB : ∀ i ∈ lv B, w i = y) :
    DN w A B C := by
  intro p q r
  simp only [minor, cnt_const w y p A hA, cnt_const w y q A hA, cnt_const w y r A hA,
    cnt_const w y p B hB, cnt_const w y q B hB, cnt_const w y r B hB]
  by_cases hp : p = y <;> by_cases hq : q = y <;> by_cases hr : r = y <;>
    simp only [hp, hq, hr, if_true, if_false, Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.zero_sub,
      Int.add_zero, Int.sub_self, Int.neg_zero, Int.mul_neg, Int.neg_mul] <;> omega

theorem dn_BC (w : Nat → Nat) (y : Nat) (A B C : Tree) (hB : ∀ i ∈ lv B, w i = y) (hC : ∀ i ∈ lv C, w i = y) :
    DN w A B C := by
  intro p q r
  simp only [minor, cnt_const w y p B hB, cnt_const w y q B hB, cnt_const w y r B hB,
    cnt_const w y p C hC, cnt_const w y q C hC, cnt_const w y r C hC]
  by_cases hp : p = y <;> by_cases hq : q = y <;> by_cases hr : r = y <;>
    simp only [hp, hq, hr, if_true, if_false, Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.zero_sub,
      Int.add_zero, Int.sub_self, Int.neg_zero, Int.mul_neg, Int.neg_mul] <;> omega

/-! ## rotations connect all bracketings of a two-letter segment -/

theorem merge_rc (w : Nat → Nat) (a c : Nat) :
    ∀ (r : List Nat) (i j : Nat) (s : List Nat), (∀ t ∈ i :: r ++ j :: s, w t = a ∨ w t = c) →
      DReach (DNStep w) (.node (rc i r) (rc j s)) (rc i (r ++ j :: s))
  | [], i, j, s, _ => DReach.refl _
  | k :: r, i, j, s, h => by
    have e : lv (.leaf i) ++ lv (rc k r) ++ lv (rc j s) = i :: k :: r ++ j :: s := by simp [lv, lv_rc]
    have step : DNStep w (.node (.node (.leaf i) (rc k r)) (rc j s)) (.node (.leaf i) (.node (rc k r) (rc j s))) :=
      DNStep.fwd .hole _ _ _ (dn_two w a c _ _ _ (fun t ht => h t (e ▸ ht)))
    have ih := merge_rc w a c r k j s (fun t ht => h t (by
      show t ∈ i :: (k :: r ++ j :: s); exact List.mem_cons_of_mem i ht))
    exact DReach.trans (DReach.single step) (reach_inR (.leaf i) ih)

theorem to_rc (w : Nat → Nat) (a c : Nat) :
    ∀ (T : Tree) (i : Nat) (r : List Nat), lv T = i :: r → (∀ t ∈ lv T, w t = a ∨ w t = c) →
      DReach (DNStep w) T (rc i r)
  | .leaf k, i, r, e, _ => by
    simp only [lv, List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact DReach.refl _
  | .node L R, i, r, e, h => by
    obtain ⟨i', r', hL⟩ := lv_cons L
    obtain ⟨j, s, hR⟩ := lv_cons R
    simp only [lv, hL, hR, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have h1 := to_rc w a c L i' r' hL (fun t ht => h t (by simp [lv, ht]))
    have h2 := to_rc w a c R j s hR (fun t ht => h t (by simp [lv, ht]))
    refine DReach.trans (reach_inL R h1) (DReach.trans (reach_inR _ h2) (merge_rc w a c r' i' j s ?_))
    intro t ht; apply h t; simp only [lv, hL, hR]; simpa using ht

theorem two_conn (w : Nat → Nat) (a c : Nat) (T T' : Tree) (e : lv T = lv T')
    (h : ∀ t ∈ lv T, w t = a ∨ w t = c) : DReach (DNStep w) T T' := by
  obtain ⟨i, r, hT⟩ := lv_cons T
  exact DReach.trans (to_rc w a c T i r hT h)
    (to_rc w a c T' i r (e ▸ hT) (fun t ht => h t (e ▸ ht))).symm

/-! ## triple shapes -/

def sh : Tree → Nat → Nat → Nat → Bool
  | .leaf _, _, _, _ => false
  | .node L R, i, j, k => if k ∈ lv L then sh L i j k else if i ∈ lv R then sh R i j k else decide (j ∈ lv L)

theorem sh_L (L R : Tree) (i j k : Nat) (h : k ∈ lv L) : sh (.node L R) i j k = sh L i j k := by
  simp [sh, h]
theorem sh_R (L R : Tree) (i j k : Nat) (h1 : k ∉ lv L) (h2 : i ∈ lv R) : sh (.node L R) i j k = sh R i j k := by
  simp [sh, h1, h2]
theorem sh_M (L R : Tree) (i j k : Nat) (h1 : k ∉ lv L) (h2 : i ∉ lv R) :
    sh (.node L R) i j k = decide (j ∈ lv L) := by
  simp [sh, h1, h2]

def Distinct (w : Nat → Nat) (i j k : Nat) : Prop := w i ≠ w j ∧ w j ≠ w k ∧ w i ≠ w k

/-- same shape on every distinct-letter triple -/
def SigEq (w : Nat → Nat) (T T' : Tree) : Prop :=
  ∀ i j k, i ∈ lv T → j ∈ lv T → k ∈ lv T → i < j → j < k → Distinct w i j k → sh T i j k = sh T' i j k

theorem SigEq.symm {w : Nat → Nat} {T T' : Tree} (e : lv T = lv T') (h : SigEq w T T') : SigEq w T' T := by
  intro i j k hi hj hk h1 h2 hd; rw [← e] at hi hj hk; exact (h i j k hi hj hk h1 h2 hd).symm

def MonoW (w : Nat → Nat) : Prop := ∀ i j, i ≤ j → w i ≤ w j

/-- order and disjointness of the parts of an increasing list -/
theorem pw_lt {X Y : List Nat} (h : (X ++ Y).Pairwise (· < ·)) {x y : Nat} (hx : x ∈ X) (hy : y ∈ Y) : x < y :=
  (List.pairwise_append.1 h).2.2 x hx y hy

theorem pw_nmem {X Y : List Nat} (h : (X ++ Y).Pairwise (· < ·)) {y : Nat} (hy : y ∈ Y) : y ∉ X :=
  fun hx => Nat.lt_irrefl y (pw_lt h hx hy)

theorem pw_nmem' {X Y : List Nat} (h : (X ++ Y).Pairwise (· < ·)) {x : Nat} (hx : x ∈ X) : x ∉ Y :=
  fun hy => Nat.lt_irrefl x (pw_lt h hx hy)

/-! ## the induction -/

/-- the induction hypothesis -/
def IH (w : Nat → Nat) (n : Nat) : Prop :=
  ∀ T T' : Tree, (lv T).length ≤ n → lv T = lv T' → (lv T).Pairwise (· < ·) → SigEq w T T' →
    DReach (DNStep w) T T'

theorem lv_len_pos (T : Tree) : 1 ≤ (lv T).length := by
  obtain ⟨i, r, h⟩ := lv_cons T; simp [h]

/-- equal root splits -/
theorem eq_split (w : Nat → Nat) (n : Nat) (ih : IH w n) (L R L' R' : Tree)
    (e1 : lv L = lv L') (e2 : lv R = lv R') (hpw : (lv L ++ lv R).Pairwise (· < ·))
    (hlen : (lv L ++ lv R).length ≤ n + 1) (hs : SigEq w (.node L R) (.node L' R')) :
    DReach (DNStep w) (.node L R) (.node L' R') := by
  have lL := lv_len_pos L; have lR := lv_len_pos R
  simp only [List.length_append] at hlen
  have hL : DReach (DNStep w) L L' := ih L L' (by omega) e1 (List.pairwise_append.1 hpw).1 (by
    intro i j k hi hj hk h1 h2 hd
    have := hs i j k (by simp [lv, hi]) (by simp [lv, hj]) (by simp [lv, hk]) h1 h2 hd
    rwa [sh_L L R i j k hk, sh_L L' R' i j k (e1 ▸ hk)] at this)
  have hR : DReach (DNStep w) R R' := ih R R' (by omega) e2 (List.pairwise_append.1 hpw).2.1 (by
    intro i j k hi hj hk h1 h2 hd
    have := hs i j k (by simp [lv, hi]) (by simp [lv, hj]) (by simp [lv, hk]) h1 h2 hd
    rwa [sh_R L R i j k (pw_nmem hpw hk) hi, sh_R L' R' i j k (e1 ▸ pw_nmem hpw hk) (e2 ▸ hi)] at this)
  exact DReach.trans (reach_inL R hL) (reach_inR L' hR)

/-- unequal root splits, `lv L' = lv L ++ M` -/
theorem uneq_split (w : Nat → Nat) (hw : MonoW w) (n : Nat) (ih : IH w n) (L R L' R' : Tree) (M : List Nat)
    (hM : M ≠ []) (h1 : lv L' = lv L ++ M) (h2 : lv R = M ++ lv R')
    (hpw : (lv L ++ lv R).Pairwise (· < ·)) (hlen : (lv L ++ lv R).length ≤ n + 1)
    (hs : SigEq w (.node L R) (.node L' R')) :
    DReach (DNStep w) (.node L R) (.node L' R') := by
  -- the three segments X = lv L, Y = M, Z = lv R'
  have pw3 : (lv L ++ (M ++ lv R')).Pairwise (· < ·) := h2 ▸ hpw
  have pXY : (lv L ++ M).Pairwise (· < ·) := (List.pairwise_append.1 (by simpa [List.append_assoc] using pw3 :
    ((lv L ++ M) ++ lv R').Pairwise (· < ·))).1
  have pYZ : (M ++ lv R').Pairwise (· < ·) := (List.pairwise_append.1 pw3).2.1
  have pXYZ : ((lv L ++ M) ++ lv R').Pairwise (· < ·) := by simpa [List.append_assoc] using pw3
  have xy : ∀ x ∈ lv L, ∀ y ∈ M, x < y := fun x hx y hy => pw_lt pXY hx hy
  have yz : ∀ y ∈ M, ∀ z ∈ lv R', y < z := fun y hy z hz => pw_lt pYZ hy hz
  have xz : ∀ x ∈ lv L, ∀ z ∈ lv R', x < z := fun x hx z hz => pw_lt pXYZ (by simp [hx]) hz
  have lL := lv_len_pos L; have lR' := lv_len_pos R'
  have lenR : (lv R).length ≤ n := by simp only [List.length_append] at hlen; omega
  have lenL' : (lv L').length ≤ n := by
    rw [h1]; simp only [List.length_append] at hlen ⊢; rw [h2] at hlen; simp only [List.length_append] at hlen; omega
  -- (*) no distinct-letter triple crosses the segments
  have star : ∀ x ∈ lv L, ∀ y ∈ M, ∀ z ∈ lv R', ¬ Distinct w x y z := by
    intro x hx y hy z hz hd
    have := hs x y z (by simp [lv, hx]) (by simp [lv, h2, hy]) (by simp [lv, h2, hz])
      (xy x hx y hy) (yz y hy z hz) hd
    rw [sh_M L R x y z (pw_nmem hpw (by rw [h2]; simp [hz])) (pw_nmem' hpw hx),
      sh_M L' R' x y z (by rw [h1]; exact pw_nmem pXYZ hz) (by rw [h1] at *; exact pw_nmem' pXYZ (by simp [hx]))]
      at this
    have : y ∈ lv L := by simpa [h1, hy] using this
    exact pw_nmem pXY hy this
  have memL' : ∀ t ∈ lv L', t ∈ lv (.node L R) := by
    intro t ht; rw [h1, List.mem_append] at ht; simp only [lv, h2, List.mem_append]
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have mono : ∀ i j, i < j → w i ≤ w j := fun i j h => hw i j (Nat.le_of_lt h)
  obtain ⟨y0, hy0⟩ : ∃ y0, y0 ∈ M := by cases M with | nil => exact absurd rfl hM | cons a _ => exact ⟨a, by simp⟩
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∈ lv L := by obtain ⟨i, _, h⟩ := lv_cons L; exact ⟨i, by simp [h]⟩
  obtain ⟨z0, hz0⟩ : ∃ z0, z0 ∈ lv R' := by obtain ⟨i, _, h⟩ := lv_cons R'; exact ⟨i, by simp [h]⟩
  -- a bracketing `Pt` of `M`; its shape is irrelevant
  obtain ⟨Pt, hPt⟩ : ∃ Pt : Tree, lv Pt = M := by
    cases M with
    | nil => exact absurd rfl hM
    | cons a t => exact ⟨rc a t, lv_rc a t⟩
  by_cases hB : ∀ x ∈ lv L, ∀ y ∈ M, w x = w y
  · -- case (B): `X ++ Y` is a power of one letter `w y0`
    have cB : ∀ i ∈ lv L ++ M, w i = w y0 := by
      intro i hi; simp only [List.mem_append] at hi
      rcases hi with hi | hi
      · exact hB i hi y0 hy0
      · rw [← hB x0 hx0 i hi, hB x0 hx0 y0 hy0]
    -- R ~ node Pt R'
    have r1 : DReach (DNStep w) R (.node Pt R') := ih R (.node Pt R') lenR (by simp [lv, hPt, h2])
      (List.pairwise_append.1 hpw).2.1 (by
        intro i j k hi hj hk hij hjk hd
        have hT := hs i j k (by simp [lv, hi]) (by simp [lv, hj]) (by simp [lv, hk]) hij hjk hd
        rw [sh_R L R i j k (pw_nmem hpw hk) hi] at hT
        rw [h2] at hi hj hk
        simp only [List.mem_append] at hi hj hk
        by_cases hiM : i ∈ M
        · have hjZ : j ∈ lv R' := by
            rcases hj with hj | hj
            · exact absurd (by rw [cB i (by simp [hiM]), cB j (by simp [hj])]) hd.1
            · exact hj
          have hkZ : k ∈ lv R' := by
            rcases hk with hk | hk
            · exact absurd (yz k hk j hjZ) (by omega)
            · exact hk
          rw [hT, sh_M L' R' i j k (by rw [h1]; exact pw_nmem pXYZ hkZ) (by rw [h1] at *; exact pw_nmem' pXYZ (by simp [hiM])),
            sh_M Pt R' i j k (by rw [hPt]; exact pw_nmem pYZ hkZ) (pw_nmem' pYZ hiM)]
          simp only [h1, hPt, List.mem_append, decide_eq_decide]
          constructor
          · intro h; exfalso; rcases h with h | h
            · exact absurd (xz j h j hjZ) (Nat.lt_irrefl j)
            · exact pw_nmem pYZ hjZ h
          · intro h; exact absurd h (pw_nmem pYZ hjZ)
        · have hiZ : i ∈ lv R' := by rcases hi with hi | hi; exact absurd hi hiM; exact hi
          have hjZ : j ∈ lv R' := by
            rcases hj with hj | hj; exact absurd (yz j hj i hiZ) (by omega); exact hj
          have hkZ : k ∈ lv R' := by
            rcases hk with hk | hk; exact absurd (yz k hk i hiZ) (by omega); exact hk
          rw [hT, sh_R L' R' i j k (by rw [h1]; exact pw_nmem pXYZ hkZ) hiZ,
            sh_R Pt R' i j k (by rw [hPt]; exact pw_nmem pYZ hkZ) hiZ])
    -- node L (node Pt R') → node (node L Pt) R'
    have st : DNStep w (.node L (.node Pt R')) (.node (.node L Pt) R') :=
      DNStep.bwd .hole L Pt R' (dn_AB w (w y0) L Pt R' (fun i hi => cB i (by simp [hi]))
        (fun i hi => cB i (by simp [hPt ▸ hi])))
    -- node L Pt ~ L'
    have r2 : DReach (DNStep w) (.node L Pt) L' := ih (.node L Pt) L' (by simp only [lv, hPt]; rw [← h1]; exact lenL')
      (by simp [lv, hPt, h1]) (by simp only [lv, hPt]; exact pXY) (by
        intro i j k hi hj _ _ _ hd
        simp only [lv, hPt] at hi hj
        exact absurd (by rw [cB i hi, cB j hj]) hd.1)
    exact DReach.trans (reach_inR L r1) (DReach.trans (DReach.single st) (reach_inL R' r2))
  by_cases hC : ∀ y ∈ M, ∀ z ∈ lv R', w y = w z
  · -- case (C): `Y ++ Z` is a power of one letter `w y0`
    have cC : ∀ i ∈ M ++ lv R', w i = w y0 := by
      intro i hi; simp only [List.mem_append] at hi
      rcases hi with hi | hi
      · rw [hC i hi z0 hz0, ← hC y0 hy0 z0 hz0]
      · exact (hC y0 hy0 i hi).symm
    -- L' ~ node L Pt
    have r1 : DReach (DNStep w) L' (.node L Pt) := ih L' (.node L Pt) lenL' (by simp [lv, hPt, h1])
      (by rw [h1]; exact pXY) (by
        intro i j k hi hj hk hij hjk hd
        have hT := hs i j k (memL' i hi) (memL' j hj) (memL' k hk) hij hjk hd
        rw [sh_L L' R' i j k hk] at hT
        rw [h1] at hi hj hk
        simp only [List.mem_append] at hi hj hk
        have hiX : i ∈ lv L := by
          rcases hi with hi | hi; exact hi
          rcases hk with hk | hk; exact absurd (xy k hk i hi) (by omega)
          exact absurd (by rw [cC i (by simp [hi]), cC k (by simp [hk])]) hd.2.2
        have hjX : j ∈ lv L := by
          rcases hj with hj | hj; exact hj
          rcases hk with hk | hk; exact absurd (xy k hk j hj) (by omega)
          exact absurd (by rw [cC j (by simp [hj]), cC k (by simp [hk])]) hd.2.1
        rw [← hT]
        rcases hk with hkX | hkM
        · rw [sh_L L R i j k hkX, sh_L L Pt i j k hkX]
        · rw [sh_M L R i j k (pw_nmem pXY hkM) (pw_nmem' hpw hiX),
            sh_M L Pt i j k (pw_nmem pXY hkM) (by rw [hPt]; exact pw_nmem' pXY hiX)])
    have st : DNStep w (.node (.node L Pt) R') (.node L (.node Pt R')) :=
      DNStep.fwd .hole L Pt R' (dn_BC w (w y0) L Pt R' (fun i hi => cC i (by simp [hPt ▸ hi]))
        (fun i hi => cC i (by simp [hi])))
    have r2 : DReach (DNStep w) (.node Pt R') R := ih (.node Pt R') R
      (by simp only [lv, hPt]; rw [← h2]; exact lenR) (by simp [lv, hPt, h2]) (by simp only [lv, hPt]; exact pYZ) (by
        intro i j k hi hj _ _ _ hd
        simp only [lv, hPt] at hi hj
        exact absurd (by rw [cC i hi, cC j hj]) hd.1)
    have : DReach (DNStep w) (.node L' R') (.node L R) :=
      DReach.trans (reach_inL R' r1) (DReach.trans (DReach.single st) (reach_inR L r2))
    exact this.symm
  · -- case (A): two letters
    obtain ⟨x1, hx1, y1, hy1, nxy⟩ : ∃ x ∈ lv L, ∃ y ∈ M, w x ≠ w y := by
      apply Classical.byContradiction; intro hn; apply hB; intro x hx y hy
      apply Classical.byContradiction; intro hne; exact hn ⟨x, hx, y, hy, hne⟩
    obtain ⟨y2, hy2, z2, hz2, nyz⟩ : ∃ y ∈ M, ∃ z ∈ lv R', w y ≠ w z := by
      apply Classical.byContradiction; intro hn; apply hC; intro y hy z hz
      apply Classical.byContradiction; intro hne; exact hn ⟨y, hy, z, hz, hne⟩
    have notD : ∀ x ∈ lv L, ∀ y ∈ M, ∀ z ∈ lv R', w x = w y ∨ w y = w z ∨ w x = w z := by
      intro x hx y hy z hz
      have := star x hx y hy z hz
      by_cases e1 : w x = w y
      · exact Or.inl e1
      by_cases e2 : w y = w z
      · exact Or.inr (Or.inl e2)
      by_cases e3 : w x = w z
      · exact Or.inr (Or.inr e3)
      exact absurd ⟨e1, e2, e3⟩ this
    have allZ : ∀ z ∈ lv R', w z = w y1 := by
      intro z hz
      have m1 := mono x1 y1 (xy x1 hx1 y1 hy1); have m2 := mono y1 z (yz y1 hy1 z hz)
      rcases notD x1 hx1 y1 hy1 z hz with h | h | h <;> omega
    have allX : ∀ x ∈ lv L, w x = w y2 := by
      intro x hx
      have m1 := mono x y2 (xy x hx y2 hy2); have m2 := mono y2 z2 (yz y2 hy2 z2 hz2)
      rcases notD x hx y2 hy2 z2 hz2 with h | h | h <;> omega
    have allY : ∀ y ∈ M, w y = w y2 ∨ w y = w y1 := by
      intro y hy
      rcases notD x1 hx1 y hy z2 hz2 with h | h | h
      · exact Or.inl (by rw [← h, allX x1 hx1])
      · exact Or.inr (by rw [h, allZ z2 hz2])
      · exfalso
        have m1 := mono x1 y1 (xy x1 hx1 y1 hy1); have m2 := mono y1 z2 (yz y1 hy1 z2 hz2)
        rw [allX x1 hx1, allZ z2 hz2] at h
        have := allX x1 hx1; have := allZ z2 hz2; omega
    apply two_conn w (w y2) (w y1) _ _ (by simp [lv, h1, h2])
    intro t ht
    simp only [lv, h2, List.mem_append] at ht
    rcases ht with ht | ht | ht
    · exact Or.inl (allX t ht)
    · exact allY t ht
    · exact Or.inr (allZ t ht)

/-- **Proposition C (⇐).** In an interval word, bracketings with the same distinct-letter triple
shapes lie in the same `D_N`-component. -/
theorem propC_backward (w : Nat → Nat) (hw : MonoW w) : ∀ n, IH w n := by
  intro n
  induction n with
  | zero => intro T _ hl; have := lv_len_pos T; omega
  | succ n ih =>
    intro T T' hl e hpw hs
    cases T with
    | leaf i =>
      cases T' with
      | leaf i' => simp only [lv, List.cons.injEq] at e; rw [e.1]; exact DReach.refl _
      | node L' R' =>
        have := lv_len_pos L'; have := lv_len_pos R'
        have := congrArg List.length e; simp [lv] at this; omega
    | node L R =>
      cases T' with
      | leaf i' =>
        have := lv_len_pos L; have := lv_len_pos R
        have := congrArg List.length e; simp [lv] at this; omega
      | node L' R' =>
        simp only [lv] at e hl hpw
        rcases List.append_eq_append_iff.1 e with ⟨M, e1, e2⟩ | ⟨M, e1, e2⟩
        · by_cases hM : M = []
          · subst hM; simp only [List.append_nil, List.nil_append] at e1 e2
            exact eq_split w n ih L R L' R' e1.symm e2 hpw hl hs
          · exact uneq_split w hw n ih L R L' R' M hM e1 e2 hpw hl hs
        · by_cases hM : M = []
          · subst hM; simp only [List.append_nil, List.nil_append] at e1 e2
            exact eq_split w n ih L R L' R' e1 e2.symm hpw hl hs
          · have e' : lv L' ++ lv R' = lv L ++ lv R := e.symm
            have := uneq_split w hw n ih L' R' L R M hM e1 e2 (e' ▸ hpw) (e' ▸ hl)
              (SigEq.symm (by simp only [lv]; exact e) hs)
            exact this.symm

/-- **Proposition C.** For an interval word and bracketings of the same increasing leaf list,
same distinct-letter triple shapes ⟹ same `D_N`-component. -/
theorem propC (w : Nat → Nat) (hw : MonoW w) (T T' : Tree) (e : lv T = lv T')
    (hpw : (lv T).Pairwise (· < ·)) (hs : SigEq w T T') : DReach (DNStep w) T T' :=
  propC_backward w hw _ T T' (Nat.le_refl _) e hpw hs

end Octonion
