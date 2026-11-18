import Caterpillar.Counts

/-!
# Lemma Cat: caterpillar node sets are self-certifying

A *rotation site* is a consecutive triple `X = (x0, x1)`, `Y = (x1+1, y1)`, `Z = (y1+1, z1)`. The rotation
`(XY)Z ↔ X(YZ)` deletes one of `XY`, `YZ` and creates the other. A set `S` of intervals is
*self-certifying* (Lemma R′) when every rotation that would delete some `J ∈ S` has `det ≠ 0`. Only
rotations compatible with `S` count: `X, Y, Z, XYZ` are laminar with `S`, and the created node is laminar
with `S − {J}`.

`chain_selfCert`: a position-level caterpillar chain satisfying the letter conditions (C1), (C2) gives
a self-certifying set. This is the laminarity classification together with the determinant core `rank3`.
-/

namespace Caterpillar

/-- `J ⊊ P`, both well formed -/
def SSub (J P : Ival) : Prop := P.1 ≤ J.1 ∧ J.2 ≤ P.2 ∧ (P.1 < J.1 ∨ J.2 < P.2) ∧ J.1 ≤ J.2

/-- every position of `P` outside `J` carries the letter `a` -/
def SideLetter (w : Word) (P J : Ival) (a : L3) : Prop :=
  ∀ p, P.1 ≤ p → p ≤ P.2 → (p < J.1 ∨ J.2 < p) → w p = a

/-- All rotations that would delete `J` and are compatible with `S` have nonzero determinant. -/
def Certified (w : Word) (root : Ival) (S : List Ival) (J : Ival) : Prop :=
  ∀ x0 x1 y1 z1 : Nat, x0 ≤ x1 → x1 < y1 → y1 < z1 → root.1 ≤ x0 → z1 ≤ root.2 →
    (∀ K ∈ S, Lam (x0, x1) K ∧ Lam (x1 + 1, y1) K ∧ Lam (y1 + 1, z1) K ∧ Lam (x0, z1) K) →
    (((x0, y1) = J ∧ ∀ K ∈ S, K ≠ J → Lam (x1 + 1, z1) K) ∨
     ((x1 + 1, z1) = J ∧ ∀ K ∈ S, K ≠ J → Lam (x0, y1) K)) →
    det3 (cnt w (x0, x1)) (cnt w (x1 + 1, y1)) (cnt w (y1 + 1, z1)) ≠ 0

def SelfCert (w : Word) (root : Ival) (S : List Ival) : Prop := ∀ J ∈ S, Certified w root S J

theorem natCast_ne_zero_of_le {x y : Nat} (h : x ≤ y) : ((y + 1 - x : Nat) : Int) ≠ 0 := by omega

/-- third letter for a pairwise distinct triple, in the orders used below -/
theorem third_uav : ∀ a u v : L3, a ≠ u → a ≠ v → u ≠ v → third u a = v := by decide

/-- sibling lies in `P \ J`: from laminarity with `P` (or from the root bound when `P` is the root) -/
theorem sibling_right (P J : Ival) (root : Ival) (x0 y1 z1 : Nat) (hJ : SSub J P)
    (hx : x0 = J.1) (hy : y1 = J.2) (hP : P = root ∨ (Lam (y1 + 1, z1) P ∧ Lam (x0, z1) P))
    (hr : z1 ≤ root.2) (hz : y1 < z1) : ∀ p, y1 + 1 ≤ p → p ≤ z1 → P.1 ≤ p ∧ p ≤ P.2 := by
  unfold SSub at hJ
  rcases hP with rfl | ⟨h1, h2⟩
  · intro p h1 h2; omega
  · unfold Lam at h1 h2; simp only at h1 h2; intro p hp1 hp2; omega

theorem sibling_left (P J : Ival) (root : Ival) (x0 x1 z1 : Nat) (hJ : SSub J P)
    (hx : x1 + 1 = J.1) (hz : z1 = J.2) (hP : P = root ∨ (Lam (x0, x1) P ∧ Lam (x0, z1) P))
    (hr : root.1 ≤ x0) (hxx : x0 ≤ x1) : ∀ p, x0 ≤ p → p ≤ x1 → P.1 ≤ p ∧ p ≤ P.2 := by
  unfold SSub at hJ
  rcases hP with rfl | ⟨h1, h2⟩
  · intro p h1 h2; omega
  · unfold Lam at h1 h2; simp only at h1 h2; intro p hp1 hp2; omega

/-- **Inner node.** `J ⊊ P` entered by `a`; `J' ⊊ J` (in `S`) left by peeling `b ≠ a`; `J'` contains
`third a b`. -/
theorem certified_inner (w : Word) (root : Ival) (S : List Ival) (P J J' : Ival) (a b : L3)
    (hJP : SSub J P) (hJ'J : SSub J' J) (hP : P = root ∨ P ∈ S) (hJ'S : J' ∈ S)
    (ha : SideLetter w P J a) (hb : SideLetter w J J' b) (hab : a ≠ b)
    (hc : ∃ p, J'.1 ≤ p ∧ p ≤ J'.2 ∧ w p = third a b) : Certified w root S J := by
  intro x0 x1 y1 z1 h01 h12 h23 hr1 hr2 hlam hdel
  have hba : b ≠ a := fun e => hab e.symm
  have hJ'lam := hlam J' hJ'S
  unfold Lam at hJ'lam; simp only at hJ'lam
  have hJP' := hJP; have hJ'J' := hJ'J
  unfold SSub at hJP' hJ'J'
  rcases hdel with ⟨hJeq, _⟩ | ⟨hJeq, _⟩
  · -- deleted `XY = J`, sibling `Z` on the right
    have hx : x0 = J.1 := by rw [← hJeq]
    have hy : y1 = J.2 := by rw [← hJeq]
    have hPl : P = root ∨ (Lam (y1 + 1, z1) P ∧ Lam (x0, z1) P) := by
      rcases hP with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(hlam P h).2.2.1, (hlam P h).2.2.2⟩
    have hZ := sibling_right P J root x0 y1 z1 hJP hx hy hPl hr2 h23
    have cZ : cnt w (y1 + 1, z1) = ev a ((z1 + 1 - (y1 + 1) : Nat) : Int) :=
      cnt_const w _ a (by simp; omega) (fun p h1 h2 => ha p (hZ p h1 h2).1 (hZ p h1 h2).2 (Or.inr (by omega)))
    have hZn := natCast_ne_zero_of_le (show y1 + 1 ≤ z1 by omega)
    by_cases hsplit : x1 < J'.1
    · -- `X` is a `b`-piece, `Y ⊇ J'`
      have cX : cnt w (x0, x1) = ev b ((x1 + 1 - x0 : Nat) : Int) :=
        cnt_const w _ b (by simp; omega) (fun p h1 h2 => hb p (by simp at h1; omega) (by simp at h2; omega)
          (Or.inl (by simp at h2; omega)))
      have hY : cnt w (x1 + 1, y1) (third a b) ≠ 0 :=
        cnt_pos_of_sub w _ J' _ hJ'J'.2.2.2 (by simp; omega) hc
      rw [cX, cZ]
      have := (rank3 a b hab _ _ hZn (natCast_ne_zero_of_le h01) (cnt w (x1 + 1, y1)) hY).2.2.2.2.1
      exact this
    · -- `Y` is a `b`-piece, `X ⊇ J'`
      have hY2 : J'.2 < x1 + 1 := by omega
      have cY : cnt w (x1 + 1, y1) = ev b ((y1 + 1 - (x1 + 1) : Nat) : Int) :=
        cnt_const w _ b (by simp; omega) (fun p h1 h2 => hb p (by simp at h1; omega) (by simp at h2; omega)
          (Or.inr (by simp at h1; omega)))
      have hX : cnt w (x0, x1) (third a b) ≠ 0 :=
        cnt_pos_of_sub w _ J' _ hJ'J'.2.2.2 (by simp; omega) hc
      rw [cY, cZ]
      exact (rank3 a b hab _ _ hZn (natCast_ne_zero_of_le (show x1 + 1 ≤ y1 by omega)) (cnt w (x0, x1)) hX).2.2.2.2.2
  · -- deleted `YZ = J`, sibling `X` on the left
    have hx : x1 + 1 = J.1 := by rw [← hJeq]
    have hz : z1 = J.2 := by rw [← hJeq]
    have hPl : P = root ∨ (Lam (x0, x1) P ∧ Lam (x0, z1) P) := by
      rcases hP with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(hlam P h).1, (hlam P h).2.2.2⟩
    have hX := sibling_left P J root x0 x1 z1 hJP hx hz hPl hr1 h01
    have cX : cnt w (x0, x1) = ev a ((x1 + 1 - x0 : Nat) : Int) :=
      cnt_const w _ a (by simp; omega) (fun p h1 h2 => ha p (hX p h1 h2).1 (hX p h1 h2).2 (Or.inl (by omega)))
    have hXn := natCast_ne_zero_of_le h01
    by_cases hsplit : y1 < J'.1
    · -- `Y` is a `b`-piece, `Z ⊇ J'`
      have cY : cnt w (x1 + 1, y1) = ev b ((y1 + 1 - (x1 + 1) : Nat) : Int) :=
        cnt_const w _ b (by simp; omega) (fun p h1 h2 => hb p (by simp at h1; omega) (by simp at h2; omega)
          (Or.inl (by simp at h2; omega)))
      have hZ : cnt w (y1 + 1, z1) (third a b) ≠ 0 :=
        cnt_pos_of_sub w _ J' _ hJ'J'.2.2.2 (by simp; omega) hc
      rw [cX, cY]
      exact (rank3 a b hab _ _ hXn (natCast_ne_zero_of_le (show x1 + 1 ≤ y1 by omega)) (cnt w (y1 + 1, z1)) hZ).1
    · -- `Z` is a `b`-piece, `Y ⊇ J'`
      have cZ : cnt w (y1 + 1, z1) = ev b ((z1 + 1 - (y1 + 1) : Nat) : Int) :=
        cnt_const w _ b (by simp; omega) (fun p h1 h2 => hb p (by simp at h1; omega) (by simp at h2; omega)
          (Or.inr (by simp at h1; omega)))
      have hY : cnt w (x1 + 1, y1) (third a b) ≠ 0 :=
        cnt_pos_of_sub w _ J' _ hJ'J'.2.2.2 (by simp; omega) hc
      rw [cX, cZ]
      exact (rank3 a b hab _ _ hXn (natCast_ne_zero_of_le (show y1 + 1 ≤ z1 by omega)) (cnt w (x1 + 1, y1)) hY).2.1

/-- **Bottom node.** `J` = a `u`-run followed by a `v`-run, entered by `a`, with `a, u, v` distinct. -/
theorem certified_bottom (w : Word) (root : Ival) (S : List Ival) (P J : Ival) (a u v : L3) (q : Nat)
    (hJP : SSub J P) (hP : P = root ∨ P ∈ S) (ha : SideLetter w P J a)
    (hq1 : J.1 ≤ q) (hq2 : q < J.2)
    (hu : ∀ p, J.1 ≤ p → p ≤ q → w p = u) (hv : ∀ p, q < p → p ≤ J.2 → w p = v)
    (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) : Certified w root S J := by
  intro x0 x1 y1 z1 h01 h12 h23 hr1 hr2 hlam hdel
  have hJP' := hJP
  unfold SSub at hJP'
  have hua : u ≠ a := fun e => hau e.symm
  have hva : v ≠ a := fun e => hav e.symm
  have hvu : v ≠ u := fun e => huv e.symm
  have t1 : third u a = v := third_uav a u v hau hav huv
  have t2 : third v a = u := third_uav a v u hav hau hvu
  rcases hdel with ⟨hJeq, _⟩ | ⟨hJeq, _⟩
  · have hx : x0 = J.1 := by rw [← hJeq]
    have hy : y1 = J.2 := by rw [← hJeq]
    have hPl : P = root ∨ (Lam (y1 + 1, z1) P ∧ Lam (x0, z1) P) := by
      rcases hP with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(hlam P h).2.2.1, (hlam P h).2.2.2⟩
    have hZ := sibling_right P J root x0 y1 z1 hJP hx hy hPl hr2 h23
    have cZ : cnt w (y1 + 1, z1) = ev a ((z1 + 1 - (y1 + 1) : Nat) : Int) :=
      cnt_const w _ a (by simp; omega) (fun p h1 h2 => ha p (hZ p h1 h2).1 (hZ p h1 h2).2 (Or.inr (by omega)))
    have hZn := natCast_ne_zero_of_le (show y1 + 1 ≤ z1 by omega)
    by_cases hs : x1 ≤ q
    · have cX : cnt w (x0, x1) = ev u ((x1 + 1 - x0 : Nat) : Int) :=
        cnt_const w _ u (by simp; omega) (fun p h1 h2 => hu p (by simp at h1; omega) (by simp at h2; omega))
      have hY : cnt w (x1 + 1, y1) (third u a) ≠ 0 :=
        cnt_pos_of_sub w _ (J.2, J.2) _ (Nat.le_refl _) (by simp; omega) ⟨J.2, Nat.le_refl _, Nat.le_refl _, by rw [t1]; exact hv _ hq2 (Nat.le_refl _)⟩
      rw [cX, cZ]
      exact (rank3 u a hua _ _ (natCast_ne_zero_of_le h01) hZn (cnt w (x1 + 1, y1)) hY).2.1
    · have cY : cnt w (x1 + 1, y1) = ev v ((y1 + 1 - (x1 + 1) : Nat) : Int) :=
        cnt_const w _ v (by simp; omega) (fun p h1 h2 => hv p (by simp at h1; omega) (by simp at h2; omega))
      have hX : cnt w (x0, x1) (third v a) ≠ 0 :=
        cnt_pos_of_sub w _ (J.1, J.1) _ (Nat.le_refl _) (by simp; omega) ⟨J.1, Nat.le_refl _, Nat.le_refl _, by rw [t2]; exact hu _ (Nat.le_refl _) hq1⟩
      rw [cY, cZ]
      exact (rank3 v a hva _ _ (natCast_ne_zero_of_le (show x1 + 1 ≤ y1 by omega)) hZn (cnt w (x0, x1)) hX).2.2.1
  · have hx : x1 + 1 = J.1 := by rw [← hJeq]
    have hz : z1 = J.2 := by rw [← hJeq]
    have hPl : P = root ∨ (Lam (x0, x1) P ∧ Lam (x0, z1) P) := by
      rcases hP with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(hlam P h).1, (hlam P h).2.2.2⟩
    have hX := sibling_left P J root x0 x1 z1 hJP hx hz hPl hr1 h01
    have cX : cnt w (x0, x1) = ev a ((x1 + 1 - x0 : Nat) : Int) :=
      cnt_const w _ a (by simp; omega) (fun p h1 h2 => ha p (hX p h1 h2).1 (hX p h1 h2).2 (Or.inl (by omega)))
    have hXn := natCast_ne_zero_of_le h01
    by_cases hs : y1 ≤ q
    · have cY : cnt w (x1 + 1, y1) = ev u ((y1 + 1 - (x1 + 1) : Nat) : Int) :=
        cnt_const w _ u (by simp; omega) (fun p h1 h2 => hu p (by simp at h1; omega) (by simp at h2; omega))
      have hZ : cnt w (y1 + 1, z1) (third u a) ≠ 0 :=
        cnt_pos_of_sub w _ (J.2, J.2) _ (Nat.le_refl _) (by simp; omega) ⟨J.2, Nat.le_refl _, Nat.le_refl _, by rw [t1]; exact hv _ hq2 (Nat.le_refl _)⟩
      rw [cX, cY]
      exact (rank3 u a hua _ _ (natCast_ne_zero_of_le (show x1 + 1 ≤ y1 by omega)) hXn (cnt w (y1 + 1, z1)) hZ).2.2.2.1
    · have cZ : cnt w (y1 + 1, z1) = ev v ((z1 + 1 - (y1 + 1) : Nat) : Int) :=
        cnt_const w _ v (by simp; omega) (fun p h1 h2 => hv p (by simp at h1; omega) (by simp at h2; omega))
      have hY : cnt w (x1 + 1, y1) (third v a) ≠ 0 :=
        cnt_pos_of_sub w _ (J.1, J.1) _ (Nat.le_refl _) (by simp; omega) ⟨J.1, Nat.le_refl _, Nat.le_refl _, by rw [t2]; exact hu _ (Nat.le_refl _) hq1⟩
      rw [cX, cZ]
      exact (rank3 v a hva _ _ (natCast_ne_zero_of_le (show y1 + 1 ≤ z1 by omega)) hXn (cnt w (x1 + 1, y1)) hY).2.2.2.2.1

/-- Position-level caterpillar chain below `P`: a list of path nodes with their entry letters. -/
def PChain (w : Word) : Ival → List (Ival × L3) → Prop
  | _, [] => False
  | P, [(J, a)] => SSub J P ∧ SideLetter w P J a ∧
      ∃ q u v, J.1 ≤ q ∧ q < J.2 ∧ (∀ p, J.1 ≤ p → p ≤ q → w p = u) ∧
        (∀ p, q < p → p ≤ J.2 → w p = v) ∧ a ≠ u ∧ a ≠ v ∧ u ≠ v
  | P, (J, a) :: (J', b) :: rest => SSub J P ∧ SideLetter w P J a ∧ a ≠ b ∧
      (∃ p, J'.1 ≤ p ∧ p ≤ J'.2 ∧ w p = third a b) ∧ PChain w J ((J', b) :: rest)

theorem pchain_head {w : Word} {P : Ival} {J : Ival} {a : L3} {rest : List (Ival × L3)}
    (h : PChain w P ((J, a) :: rest)) : SSub J P ∧ SideLetter w P J a := by
  match rest, h with
  | [], h => exact ⟨h.1, h.2.1⟩
  | _ :: _, h => exact ⟨h.1, h.2.1⟩

/-- **Lemma Cat.** Every node of a caterpillar chain is certified. -/
theorem pchain_certified (w : Word) (root : Ival) (S : List Ival) :
    ∀ (L : List (Ival × L3)) (P : Ival), PChain w P L → (P = root ∨ P ∈ S) →
      (∀ x ∈ L, x.1 ∈ S) → ∀ x ∈ L, Certified w root S x.1
  | [], _, h, _, _ => absurd h (by simp [PChain])
  | [(J, a)], P, h, hP, hS => by
    intro x hx
    simp at hx; subst hx
    obtain ⟨hJP, ha, q, u, v, h1, h2, hu, hv, hau, hav, huv⟩ := h
    exact certified_bottom w root S P J a u v q hJP hP ha h1 h2 hu hv hau hav huv
  | (J, a) :: (J', b) :: rest, P, h, hP, hS => by
    obtain ⟨hJP, ha, hab, hc, hrest⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have hJ'S : J' ∈ S := hS (J', b) (by simp)
      obtain ⟨hJ'J, hb⟩ := pchain_head hrest
      exact certified_inner w root S P J J' a b hJP hJ'J hP hJ'S ha hb hab hc
    · exact pchain_certified w root S ((J', b) :: rest) J hrest (Or.inr (hS (J, a) (by simp)))
        (fun y hy => hS y (List.mem_cons_of_mem _ hy)) x hx

/-- **Lemma Cat (set form).** The path nodes of a caterpillar chain from the root form a
self-certifying set. -/
theorem chain_selfCert (w : Word) (root : Ival) (L : List (Ival × L3)) (h : PChain w root L) :
    SelfCert w root (L.map Prod.fst) := by
  intro J hJ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hJ
  exact pchain_certified w root (L.map Prod.fst) L root h (Or.inl rfl)
    (fun y hy => List.mem_map_of_mem _ hy) x hx

end Caterpillar
