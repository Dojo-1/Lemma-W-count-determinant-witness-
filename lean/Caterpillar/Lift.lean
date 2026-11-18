import Caterpillar.PropS

/-!
# K: Moufang moves lift

Bracketings carry their leaf positions (`lv`). Killing the letters `K` deletes leaves (`kill`), so a
bracketing `T` of the leaf list `L` restricts to a bracketing of `L.filter alive`.

* `lift_tree`: every bracketing of the surviving leaves is the restriction of a bracketing of `L`.
* `lift_mouf`: **every Moufang move** (left, right or middle, repeated variable a single letter) between
  bracketings of the surviving leaves is the restriction of a Moufang move between bracketings of `L`.
  Killed leaves in each gap of the pattern are absorbed by a non-repeated variable (`Y`, `B`, `C`) or by
  the context, as in the manuscript.
* `kill_reach`: `D_N`-reachability restricts (from `kill_DN`).
* `lift_separates`: a Moufang move between **different** `D_N`-components of the restriction lifts to a
  Moufang move between different `D_N`-components of the original word.
-/

namespace Octonion
open Caterpillar (Tree)

/-- leaf positions, left to right -/
def lv : Tree → List Nat
  | .leaf i => [i]
  | .node l r => lv l ++ lv r

theorem lv_cons : ∀ T : Tree, ∃ i r, lv T = i :: r
  | .leaf i => ⟨i, [], rfl⟩
  | .node l r => by
    obtain ⟨i, r', h⟩ := lv_cons l
    exact ⟨i, r' ++ lv r, by simp [lv, h]⟩

/-- Moufang moves whose repeated variable is a single letter (left, right, middle), in any context -/
inductive Mouf (w : Nat → Nat) : Tree → Tree → Prop
  | left (x x1 : Nat) (Y C : Tree) : w x = w x1 →
      Mouf w (.node (.leaf x) (.node Y (.node (.leaf x1) C))) (.node (.node (.node (.leaf x) Y) (.leaf x1)) C)
  | right (x x1 : Nat) (C Y : Tree) : w x = w x1 →
      Mouf w (.node (.node (.node C (.leaf x)) Y) (.leaf x1)) (.node C (.node (.leaf x) (.node Y (.leaf x1))))
  | middle (x x1 : Nat) (B C : Tree) : w x = w x1 →
      Mouf w (.node (.leaf x) (.node (.node B C) (.leaf x1))) (.node (.node (.leaf x) B) (.node C (.leaf x1)))
  | inL {l l' : Tree} (r : Tree) : Mouf w l l' → Mouf w (.node l r) (.node l' r)
  | inR (l : Tree) {r r' : Tree} : Mouf w r r' → Mouf w (.node l r) (.node l r')

def alive (w : Nat → Nat) (K : Nat → Bool) (i : Nat) : Bool := !K (w i)

def lvo : Option Tree → List Nat
  | none => []
  | some T => lv T

/-- the surviving leaves are the leaves of the restriction -/
theorem kill_spec (w : Nat → Nat) (K : Nat → Bool) : ∀ T, (lv T).filter (alive w K) = lvo (kill w K T)
  | .leaf i => by
    cases h : K (w i) <;> simp [List.filter, alive, kill, h, lvo, lv]
  | .node l r => by
    simp only [lv, kill, List.filter_append, kill_spec w K l, kill_spec w K r]
    cases kill w K l <;> cases kill w K r <;> simp [lvo, lv]

theorem kill_none_of (w : Nat → Nat) (K : Nat → Bool) (T : Tree) (h : (lv T).filter (alive w K) = []) :
    kill w K T = none := by
  rw [kill_spec] at h
  cases e : kill w K T with
  | none => rfl
  | some T' => rw [e] at h; obtain ⟨i, r, hr⟩ := lv_cons T'; simp [lvo, hr] at h

theorem kill_leaf_alive (w : Nat → Nat) (K : Nat → Bool) (i : Nat) (h : alive w K i = true) :
    kill w K (.leaf i) = some (.leaf i) := by
  simp only [alive, Bool.not_eq_true'] at h; simp [kill, h]

/-- split a list at an alive pivot -/
theorem pivot (p : Nat → Bool) : ∀ (L X Y : List Nat) (a : Nat), L.filter p = X ++ a :: Y →
    ∃ Q R, L = Q ++ a :: R ∧ Q.filter p = X ∧ R.filter p = Y
  | [], X, Y, a, h => by cases X <;> simp at h
  | b :: L, X, Y, a, h => by
    cases hb : p b
    · rw [List.filter_cons_of_neg (by simp [hb])] at h
      obtain ⟨Q, R, e, hQ, hR⟩ := pivot p L X Y a h
      exact ⟨b :: Q, R, by simp [e], by rw [List.filter_cons_of_neg (by simp [hb])]; exact hQ, hR⟩
    · rw [List.filter_cons_of_pos hb] at h
      cases X with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact ⟨[], L, by simp [h.1], rfl, h.2⟩
      | cons c X =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨Q, R, e, hQ, hR⟩ := pivot p L X Y a h.2
        exact ⟨b :: Q, R, by simp [e], by rw [List.filter_cons_of_pos hb, hQ, h.1], hR⟩

theorem alive_of_mem {p : Nat → Bool} {L X Y : List Nat} {a : Nat} (h : L.filter p = X ++ a :: Y) : p a = true := by
  have : a ∈ L.filter p := by rw [h]; simp
  exact (List.mem_filter.1 this).2

/-- split a list according to a split of its surviving part (the second part nonempty) -/
theorem split2 (p : Nat → Bool) (L X Y : List Nat) (a : Nat) (h : L.filter p = X ++ a :: Y) :
    ∃ L1 L2, L = L1 ++ L2 ∧ L1.filter p = X ∧ L2.filter p = a :: Y := by
  obtain ⟨Q, R, e, hQ, hR⟩ := pivot p L X Y a h
  exact ⟨Q, a :: R, e, hQ, by rw [List.filter_cons_of_pos (alive_of_mem h), hR]⟩

/-- right comb on a nonempty list -/
def rc : Nat → List Nat → Tree
  | i, [] => .leaf i
  | i, j :: r => .node (.leaf i) (rc j r)

theorem lv_rc : ∀ i r, lv (rc i r) = i :: r
  | _, [] => rfl
  | i, j :: r => by simp [rc, lv, lv_rc j r]

def wrapL : List Nat → Tree → Tree
  | [], T => T
  | i :: r, T => .node (rc i r) T

def wrapR : List Nat → Tree → Tree
  | [], T => T
  | i :: r, T => .node T (rc i r)

theorem lv_wrapL (P : List Nat) (T : Tree) : lv (wrapL P T) = P ++ lv T := by
  cases P <;> simp [wrapL, lv, lv_rc]

theorem lv_wrapR (P : List Nat) (T : Tree) : lv (wrapR P T) = lv T ++ P := by
  cases P <;> simp [wrapR, lv, lv_rc]

theorem kill_wrapL (w : Nat → Nat) (K : Nat → Bool) (P : List Nat) (T : Tree) (h : P.filter (alive w K) = []) :
    kill w K (wrapL P T) = kill w K T := by
  cases P with
  | nil => rfl
  | cons i r =>
    have : kill w K (rc i r) = none := kill_none_of w K _ (by rw [lv_rc]; exact h)
    simp only [wrapL, kill, this]

theorem kill_wrapR (w : Nat → Nat) (K : Nat → Bool) (P : List Nat) (T : Tree) (h : P.filter (alive w K) = []) :
    kill w K (wrapR P T) = kill w K T := by
  cases P with
  | nil => rfl
  | cons i r =>
    have : kill w K (rc i r) = none := kill_none_of w K _ (by rw [lv_rc]; exact h)
    simp only [wrapR, kill, this]
    cases kill w K T <;> rfl

theorem mouf_wrapL (w : Nat → Nat) (P : List Nat) {T T' : Tree} (h : Mouf w T T') : Mouf w (wrapL P T) (wrapL P T') := by
  cases P with
  | nil => exact h
  | cons i r => exact Mouf.inR _ h

theorem mouf_wrapR (w : Nat → Nat) (P : List Nat) {T T' : Tree} (h : Mouf w T T') : Mouf w (wrapR P T) (wrapR P T') := by
  cases P with
  | nil => exact h
  | cons i r => exact Mouf.inL _ h

/-- **every bracketing of the surviving leaves lifts** -/
theorem lift_tree (w : Nat → Nat) (K : Nat → Bool) :
    ∀ (T' : Tree) (L : List Nat), L.filter (alive w K) = lv T' → ∃ T, lv T = L ∧ kill w K T = some T'
  | .leaf i, L, h => by
    obtain ⟨P, R, e, hP, hR⟩ := pivot _ L [] [] i (by simpa [lv] using h)
    refine ⟨wrapR R (wrapL P (.leaf i)), by simp [lv_wrapR, lv_wrapL, lv, e], ?_⟩
    rw [kill_wrapR w K R _ hR, kill_wrapL w K P _ hP]
    exact kill_leaf_alive w K i (alive_of_mem (X := []) (Y := []) (by simpa [lv] using h))
  | .node A B, L, h => by
    obtain ⟨b, rest, hb⟩ := lv_cons B
    obtain ⟨L1, L2, e, h1, h2⟩ := split2 _ L (lv A) rest b (by rw [h]; simp [lv, hb])
    obtain ⟨TA, eA, kA⟩ := lift_tree w K A L1 h1
    obtain ⟨TB, eB, kB⟩ := lift_tree w K B L2 (by rw [h2, hb])
    exact ⟨.node TA TB, by simp [lv, eA, eB, e], by simp [kill, kA, kB]⟩

/-- **K, Moufang lift.** A Moufang move between bracketings of the surviving leaves is the restriction of
a Moufang move between bracketings of all leaves. -/
theorem lift_mouf (w : Nat → Nat) (K : Nat → Bool) {T0' T1' : Tree} (hm : Mouf w T0' T1') :
    ∀ L : List Nat, L.filter (alive w K) = lv T0' →
      ∃ T0 T1, lv T0 = L ∧ kill w K T0 = some T0' ∧ kill w K T1 = some T1' ∧ Mouf w T0 T1 := by
  induction hm with
  | left x x1 Y C hx =>
    intro L h
    have h' : L.filter (alive w K) = [] ++ x :: (lv Y ++ x1 :: lv C) := by rw [h]; simp [lv]
    obtain ⟨P, L', e1, hP, hL'⟩ := pivot _ L _ _ x h'
    obtain ⟨Q, R, e2, hQ, hR⟩ := pivot _ L' _ _ x1 hL'
    obtain ⟨TY, eY, kY⟩ := lift_tree w K Y Q hQ
    obtain ⟨TC, eC, kC⟩ := lift_tree w K C R hR
    have kx : K (w x) = false := by simpa [alive] using alive_of_mem h'
    have kx1 : K (w x1) = false := by simpa [alive] using alive_of_mem hL'
    refine ⟨wrapL P (.node (.leaf x) (.node TY (.node (.leaf x1) TC))),
      wrapL P (.node (.node (.node (.leaf x) TY) (.leaf x1)) TC), ?_, ?_, ?_, mouf_wrapL w P (Mouf.left x x1 TY TC hx)⟩
    · simp [lv_wrapL, lv, eY, eC, e1, e2]
    · rw [kill_wrapL w K P _ hP]; simp [kill, kx, kx1, kY, kC]
    · rw [kill_wrapL w K P _ hP]; simp [kill, kx, kx1, kY, kC]
  | right x x1 C Y hx =>
    intro L h
    have h' : L.filter (alive w K) = lv C ++ x :: (lv Y ++ x1 :: []) := by rw [h]; simp [lv]
    obtain ⟨Q, L', e1, hQ, hL'⟩ := pivot _ L _ _ x h'
    obtain ⟨Q2, S, e2, hQ2, hS⟩ := pivot _ L' _ _ x1 hL'
    obtain ⟨TC, eC, kC⟩ := lift_tree w K C Q hQ
    obtain ⟨TY, eY, kY⟩ := lift_tree w K Y Q2 hQ2
    have kx : K (w x) = false := by simpa [alive] using alive_of_mem h'
    have kx1 : K (w x1) = false := by simpa [alive] using alive_of_mem hL'
    refine ⟨wrapR S (.node (.node (.node TC (.leaf x)) TY) (.leaf x1)),
      wrapR S (.node TC (.node (.leaf x) (.node TY (.leaf x1)))), ?_, ?_, ?_, mouf_wrapR w S (Mouf.right x x1 TC TY hx)⟩
    · simp [lv_wrapR, lv, eY, eC, e1, e2]
    · rw [kill_wrapR w K S _ hS]; simp [kill, kx, kx1, kY, kC]
    · rw [kill_wrapR w K S _ hS]; simp [kill, kx, kx1, kY, kC]
  | middle x x1 B C hx =>
    intro L h
    obtain ⟨c, rest, hc⟩ := lv_cons C
    have h' : L.filter (alive w K) = [] ++ x :: ((lv B ++ lv C) ++ x1 :: []) := by rw [h]; simp [lv]
    obtain ⟨P, L', e1, hP, hL'⟩ := pivot _ L _ _ x h'
    obtain ⟨Q, S, e2, hQ, hS⟩ := pivot _ L' _ _ x1 hL'
    obtain ⟨QB, QC, e3, hQB, hQC⟩ := split2 _ Q (lv B) rest c (by rw [hQ, hc])
    obtain ⟨TB, eB, kB⟩ := lift_tree w K B QB hQB
    obtain ⟨TC, eC, kC⟩ := lift_tree w K C QC (by rw [hQC, hc])
    have kx : K (w x) = false := by simpa [alive] using alive_of_mem h'
    have kx1 : K (w x1) = false := by simpa [alive] using alive_of_mem hL'
    refine ⟨wrapL P (wrapR S (.node (.leaf x) (.node (.node TB TC) (.leaf x1)))),
      wrapL P (wrapR S (.node (.node (.leaf x) TB) (.node TC (.leaf x1)))), ?_, ?_, ?_,
      mouf_wrapL w P (mouf_wrapR w S (Mouf.middle x x1 TB TC hx))⟩
    · simp [lv_wrapL, lv_wrapR, lv, eB, eC, e1, e2, e3]
    · rw [kill_wrapL w K P _ hP, kill_wrapR w K S _ hS]; simp [kill, kx, kx1, kB, kC]
    · rw [kill_wrapL w K P _ hP, kill_wrapR w K S _ hS]; simp [kill, kx, kx1, kB, kC]
  | @inL l l' r _ ih =>
    intro L h
    obtain ⟨b, rest, hb⟩ := lv_cons r
    obtain ⟨L1, L2, e, h1, h2⟩ := split2 _ L (lv l) rest b (by rw [h]; simp [lv, hb])
    obtain ⟨T0, T1, e0, k0, k1, m⟩ := ih L1 h1
    obtain ⟨Tr, er, kr⟩ := lift_tree w K r L2 (by rw [h2, hb])
    exact ⟨.node T0 Tr, .node T1 Tr, by simp [lv, e0, er, e], by simp [kill, k0, kr], by simp [kill, k1, kr],
      Mouf.inL _ m⟩
  | @inR l r r' _ ih =>
    intro L h
    obtain ⟨b, rest, hb⟩ := lv_cons r
    obtain ⟨L1, L2, e, h1, h2⟩ := split2 _ L (lv l) rest b (by rw [h]; simp [lv, hb])
    obtain ⟨T0, T1, e0, k0, k1, m⟩ := ih L2 (by rw [h2, hb])
    obtain ⟨Tl, el, kl⟩ := lift_tree w K l L1 h1
    exact ⟨.node Tl T0, .node Tl T1, by simp [lv, e0, el, e], by simp [kill, k0, kl], by simp [kill, k1, kl],
      Mouf.inR _ m⟩

/-! ## `D_N`-components restrict -/

/-- a `D_N`-flip (rank ≤ 2) anywhere in the bracketing, in either direction -/
inductive DNStep (w : Nat → Nat) : Tree → Tree → Prop
  | fwd (c : Ctx) (A B C : Tree) : DN w A B C → DNStep w (fill c (.node (.node A B) C)) (fill c (.node A (.node B C)))
  | bwd (c : Ctx) (A B C : Tree) : DN w A B C → DNStep w (fill c (.node A (.node B C))) (fill c (.node (.node A B) C))

/-- reflexive–transitive closure -/
inductive DReach (R : Tree → Tree → Prop) : Tree → Tree → Prop
  | refl (T : Tree) : DReach R T T
  | tail {T U V : Tree} : DReach R T U → R U V → DReach R T V

theorem kill_step (w : Nat → Nat) (K : Nat → Bool) {T U : Tree} (h : DNStep w T U) :
    kill w K T = kill w K U ∨ ∃ S S', kill w K T = some S ∧ kill w K U = some S' ∧ DNStep w S S' := by
  cases h with
  | fwd c A B C hd =>
    rcases kill_DN w K c A B C hd with e | ⟨A', B', C', hd', e1, e2⟩
    · exact Or.inl e
    · exact Or.inr ⟨_, _, e1, e2, DNStep.fwd _ _ _ _ hd'⟩
  | bwd c A B C hd =>
    rcases kill_DN w K c A B C hd with e | ⟨A', B', C', hd', e1, e2⟩
    · exact Or.inl e.symm
    · exact Or.inr ⟨_, _, e2, e1, DNStep.bwd _ _ _ _ hd'⟩

/-- **K, components.** `D_N`-reachability restricts to `D_N`-reachability. -/
theorem kill_reach (w : Nat → Nat) (K : Nat → Bool) {T U : Tree} (h : DReach (DNStep w) T U) :
    ∀ S, kill w K T = some S → ∃ S', kill w K U = some S' ∧ DReach (DNStep w) S S' := by
  induction h with
  | refl => intro S hS; exact ⟨S, hS, DReach.refl _⟩
  | tail _ hst ih =>
    intro S hS
    obtain ⟨S1, h1, r1⟩ := ih S hS
    rcases kill_step w K hst with e | ⟨A, B, eA, eB, st⟩
    · exact ⟨S1, by rw [← e]; exact h1, r1⟩
    · rw [h1] at eA; cases eA
      exact ⟨B, eB, DReach.tail r1 st⟩

/-- **K, Moufang lift between components.** A Moufang move between different `D_N`-components of the
restriction lifts to a Moufang move between different `D_N`-components of the word. -/
theorem lift_separates (w : Nat → Nat) (K : Nat → Bool) {T0' T1' : Tree} (hm : Mouf w T0' T1')
    (hsep : ¬ DReach (DNStep w) T0' T1') (L : List Nat) (hL : L.filter (alive w K) = lv T0') :
    ∃ T0 T1, lv T0 = L ∧ kill w K T0 = some T0' ∧ kill w K T1 = some T1' ∧ Mouf w T0 T1 ∧
      ¬ DReach (DNStep w) T0 T1 := by
  obtain ⟨T0, T1, e, k0, k1, m⟩ := lift_mouf w K hm L hL
  refine ⟨T0, T1, e, k0, k1, m, fun r => hsep ?_⟩
  obtain ⟨S', hS', r'⟩ := kill_reach w K r T0' k0
  rw [k1] at hS'; cases hS'; exact r'

end Octonion
