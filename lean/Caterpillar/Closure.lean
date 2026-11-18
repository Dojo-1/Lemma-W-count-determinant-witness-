import Caterpillar.G2Final

/-!
# Closure: kernel classes of interval words

* `dn_assoc_zero` (Lemma I + Lemma V): in an interval word a `D_N`-flip `(AB)C → A(BC)` has local associator
  `0` at every valuation. By `propC_forward` no distinct-letter triple crosses `A × B × C`, so either `A, B` are
  powers of one letter, or `B, C` are, or `A ∪ B ∪ C` uses two letters; Lemma V covers each case.
* `reach_ev` (the converse of G2): bracketings in the same `D_N`-component are equal maps.
* **`g2_iff`**: for an interval word, `T, T'` are equal maps ⟺ they lie in the same `D_N`-component.
* **`kernel_flip_connected`**: every kernel class of an interval word is connected by flips that stay in
  the class; **`kernel_flip_connected_two`**: the same for words with at most two letters.
-/

namespace Closure
open Caterpillar (Tree)
open Octonion

theorem ev_congr (w : Nat → Nat) (ρ ρ' : Nat → O) : ∀ T : Tree, (∀ ℓ ∈ lettersT w T, ρ ℓ = ρ' ℓ) →
    ev w ρ T = ev w ρ' T
  | .leaf i, h => h (w i) (by simp [lettersT])
  | .node l r, h => by
    simp only [ev, ev_congr w ρ ρ' l (fun ℓ hℓ => h ℓ (by simp [lettersT, hℓ])),
      ev_congr w ρ ρ' r (fun ℓ hℓ => h ℓ (by simp [lettersT, hℓ]))]

theorem ev_fill_congr (w : Nat → Nat) (ρ : Nat → O) {X Y : Tree} (h : ev w ρ X = ev w ρ Y) :
    ∀ c : Ctx, ev w ρ (fill c X) = ev w ρ (fill c Y)
  | .hole => h
  | .inL c R => by simp only [fill, ev, ev_fill_congr w ρ h c]
  | .inR L c => by simp only [fill, ev, ev_fill_congr w ρ h c]

theorem letters_ne (w : Nat → Nat) (T : Tree) : ∃ ℓ, ℓ ∈ lettersT w T := by
  obtain ⟨i, r, h⟩ := lv_cons T; exact ⟨w i, by rw [lettersT_eq, h]; simp⟩

/-- **Lemma I + Lemma V**: a `D_N`-flip of an interval word has vanishing local associator -/
theorem dn_assoc_zero (w : Nat → Nat) (hw : MonoW w) (A B C : Tree)
    (hs : (lv A ++ lv B ++ lv C).Pairwise (· < ·)) (hd : DN w A B C) (ρ : Nat → O) :
    assoc (ev w ρ A) (ev w ρ B) (ev w ρ C) = zero := by
  have hle : List.Pairwise (· ≤ ·) (lettersT w A ++ lettersT w B ++ lettersT w C) := by
    simp only [lettersT_eq, ← List.map_append]
    exact List.pairwise_map.2 (hs.imp (fun h => hw _ _ (Nat.le_of_lt h)))
  have hle' := hle
  rw [List.pairwise_append, List.pairwise_append] at hle'
  obtain ⟨⟨_, _, oXY⟩, _, oXYZ⟩ := hle'
  have oXZ : ∀ x ∈ lettersT w A, ∀ z ∈ lettersT w C, x ≤ z := fun x hx z hz => oXYZ x (by simp [hx]) z hz
  have oYZ : ∀ y ∈ lettersT w B, ∀ z ∈ lettersT w C, y ≤ z := fun y hy z hz => oXYZ y (by simp [hy]) z hz
  -- no distinct-letter triple crosses (Proposition C (⇒))
  have star : ∀ x ∈ lettersT w A, ∀ y ∈ lettersT w B, ∀ z ∈ lettersT w C, x = y ∨ y = z := by
    intro x hx y hy z hz
    by_cases e1 : x = y; · exact Or.inl e1
    by_cases e2 : y = z; · exact Or.inr e2
    exfalso
    have := oXY x hx y hy; have := oYZ y hy z hz
    exact (propC_forward w A B C hle x y z hx hy hz e1 e2 (by omega)).2 hd
  obtain ⟨x0, hx0⟩ := letters_ne w A
  obtain ⟨y0, hy0⟩ := letters_ne w B
  obtain ⟨z0, hz0⟩ := letters_ne w C
  by_cases hB : ∀ x ∈ lettersT w A, ∀ y ∈ lettersT w B, x = y
  · apply lemmaV_powers w ρ (ρ y0)
    · intro i hi; rw [hB i hi y0 hy0]
    · intro i hi; rw [← hB x0 hx0 i hi, hB x0 hx0 y0 hy0]
  by_cases hC : ∀ y ∈ lettersT w B, ∀ z ∈ lettersT w C, y = z
  · apply lemmaV_powers_BC w ρ (ρ y0)
    · intro i hi; rw [hC i hi z0 hz0, ← hC y0 hy0 z0 hz0]
    · intro i hi; rw [← hC y0 hy0 i hi]
  -- two letters
  obtain ⟨x1, hx1, y1, hy1, n1⟩ : ∃ x ∈ lettersT w A, ∃ y ∈ lettersT w B, x ≠ y := by
    apply Classical.byContradiction; intro hn; apply hB; intro x hx y hy
    apply Classical.byContradiction; intro hne; exact hn ⟨x, hx, y, hy, hne⟩
  obtain ⟨y2, hy2, z2, hz2, n2⟩ : ∃ y ∈ lettersT w B, ∃ z ∈ lettersT w C, y ≠ z := by
    apply Classical.byContradiction; intro hn; apply hC; intro y hy z hz
    apply Classical.byContradiction; intro hne; exact hn ⟨y, hy, z, hz, hne⟩
  have allZ : ∀ z ∈ lettersT w C, z = y1 := by
    intro z hz; rcases star x1 hx1 y1 hy1 z hz with e | e
    · exact absurd e n1
    · exact e.symm
  have allX : ∀ x ∈ lettersT w A, x = y2 := by
    intro x hx; rcases star x hx y2 hy2 z2 hz2 with e | e
    · exact e
    · exact absurd e n2
  have allY : ∀ y ∈ lettersT w B, y = y2 ∨ y = y1 := by
    intro y hy; rcases star x1 hx1 y hy z2 hz2 with e | e
    · exact Or.inl (by rw [← e, allX x1 hx1])
    · exact Or.inr (by rw [e, allZ z2 hz2])
  let ρ' : Nat → O := fun ℓ => if ℓ = y2 then ρ y2 else ρ y1
  have agree : ∀ T : Tree, (∀ ℓ ∈ lettersT w T, ℓ = y2 ∨ ℓ = y1) → ev w ρ T = ev w ρ' T := by
    intro T hT; apply ev_congr; intro ℓ hℓ
    rcases hT ℓ hℓ with e | e
    · simp [ρ', e]
    · simp only [ρ']; split
      · next h => rw [e] at h ⊢; rw [h]
      · rw [e]
  rw [agree A (fun ℓ h => Or.inl (allX ℓ h)), agree B allY, agree C (fun ℓ h => Or.inr (allZ ℓ h))]
  exact lemmaV_two_letters w ρ' (ρ y2) (ρ y1) (fun ℓ => by simp only [ρ']; split <;> simp) A B C

theorem flip_ev (w : Nat → Nat) (ρ : Nat → O) (A B C : Tree) (h : assoc (ev w ρ A) (ev w ρ B) (ev w ρ C) = zero) :
    ev w ρ (.node (.node A B) C) = ev w ρ (.node A (.node B C)) := by
  simp only [ev]; exact (sub_eq_zero _ _).1 h

/-- a `D_N`-step of an interval word preserves the map -/
theorem dnstep_ev (w : Nat → Nat) (hw : MonoW w) {T U : Tree} (h : DNStep w T U) (hpw : (lv T).Pairwise (· < ·))
    (ρ : Nat → O) : ev w ρ T = ev w ρ U := by
  cases h with
  | fwd c A B C hd =>
    have hs : (lv A ++ lv B ++ lv C).Pairwise (· < ·) := by
      have := dnstep_sig.sublist_fill c (.node (.node A B) C); simp only [lv] at this
      exact hpw.sublist this
    exact ev_fill_congr w ρ (flip_ev w ρ A B C (dn_assoc_zero w hw A B C hs hd ρ)) c
  | bwd c A B C hd =>
    have hs : (lv A ++ lv B ++ lv C).Pairwise (· < ·) := by
      have := dnstep_sig.sublist_fill c (.node A (.node B C)); simp only [lv, List.append_assoc] at this ⊢
      exact hpw.sublist this
    exact (ev_fill_congr w ρ (flip_ev w ρ A B C (dn_assoc_zero w hw A B C (by simpa [List.append_assoc] using hs) hd ρ)) c).symm

/-- **the converse of G2**: the same `D_N`-component gives the same map -/
theorem reach_ev (w : Nat → Nat) (hw : MonoW w) {T U : Tree} (h : DReach (DNStep w) T U)
    (hpw : (lv T).Pairwise (· < ·)) (ρ : Nat → O) : ev w ρ T = ev w ρ U := by
  induction h with
  | refl => rfl
  | tail r st ih =>
    rw [ih]
    exact dnstep_ev w hw st (by rw [← (reach_sig w hw r hpw).1]; exact hpw) ρ

/-- **G2 as an equivalence.** For an interval word, two bracketings of the same increasing leaf list are
equal octonion maps iff they lie in the same `D_N`-component. -/
theorem g2_iff (w : Nat → Nat) (hw : MonoW w) (T T' : Tree) (e : lv T = lv T') (hpw : (lv T).Pairwise (· < ·)) :
    (∀ ρ : Nat → O, ev w ρ T = ev w ρ T') ↔ DReach (DNStep w) T T' := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    obtain ⟨ρ, hρ⟩ := G2Final.g2 w hw T T' e hpw hn
    exact hρ (h ρ)
  · intro h ρ; exact reach_ev w hw h hpw ρ

/-! ## kernel classes are flip-connected -/

/-- any flip (rotation) in any context -/
inductive FlipStep : Tree → Tree → Prop
  | fwd (c : Ctx) (A B C : Tree) : FlipStep (fill c (.node (.node A B) C)) (fill c (.node A (.node B C)))
  | bwd (c : Ctx) (A B C : Tree) : FlipStep (fill c (.node A (.node B C))) (fill c (.node (.node A B) C))

/-- a flip inside the kernel class: it does not change the map -/
def KerFlip (w : Nat → Nat) (T U : Tree) : Prop := FlipStep T U ∧ ∀ ρ : Nat → O, ev w ρ T = ev w ρ U

theorem dnstep_flip {w : Nat → Nat} {T U : Tree} (h : DNStep w T U) : FlipStep T U := by
  cases h with
  | fwd c A B C _ => exact FlipStep.fwd c A B C
  | bwd c A B C _ => exact FlipStep.bwd c A B C

/-- **Interval words**: every kernel class is connected by flips inside the class. -/
theorem kernel_flip_connected (w : Nat → Nat) (hw : MonoW w) (T T' : Tree) (e : lv T = lv T')
    (hpw : (lv T).Pairwise (· < ·)) (h : ∀ ρ : Nat → O, ev w ρ T = ev w ρ T') : DReach (KerFlip w) T T' := by
  have r := (g2_iff w hw T T' e hpw).1 h
  -- every `D_N`-step along the way stays in the kernel class
  have key : ∀ U, DReach (DNStep w) T U → DReach (KerFlip w) T U := by
    intro U hr
    induction hr with
    | refl => exact DReach.refl _
    | tail r' st ih =>
      exact DReach.tail ih ⟨dnstep_flip st, dnstep_ev w hw st (by rw [← (reach_sig w hw r' hpw).1]; exact hpw)⟩
  exact key T' r

/-- **Words with at most two letters**: all bracketings are one kernel class, connected by flips. -/
theorem kernel_flip_connected_two (w : Nat → Nat) (a c : Nat) (T T' : Tree) (e : lv T = lv T')
    (h2 : ∀ t ∈ lv T, w t = a ∨ w t = c) :
    (∀ ρ : Nat → O, ev w ρ T = ev w ρ T') ∧ DReach (KerFlip w) T T' := by
  have same : ∀ U U' : Tree, lv U = lv U' → (∀ t ∈ lv U, w t = a ∨ w t = c) → ∀ ρ : Nat → O, ev w ρ U = ev w ρ U' := by
    intro U U' eU hU ρ
    let ρ' : Nat → O := fun ℓ => if ℓ = a then ρ a else ρ c
    have agree : ∀ V : Tree, (∀ t ∈ lv V, w t = a ∨ w t = c) → ev w ρ V = ev w ρ' V := by
      intro V hV; apply ev_congr; intro ℓ hℓ
      rw [lettersT_eq, List.mem_map] at hℓ; obtain ⟨t, ht, rfl⟩ := hℓ
      rcases hV t ht with e' | e'
      · simp [ρ', e']
      · simp only [ρ']; split
        · next hh => rw [e'] at hh ⊢; rw [hh]
        · rw [e']
    rw [agree U hU, agree U' (fun t ht => hU t (eU ▸ ht))]
    exact artin w w ρ' (ρ a) (ρ c) (fun ℓ => by simp only [ρ']; split <;> simp) U U'
      (by rw [lettersT_eq, lettersT_eq, eU])
  refine ⟨same T T' e h2, ?_⟩
  have r := two_conn w a c T T' e h2
  have key : ∀ U, DReach (DNStep w) T U → lv U = lv T → DReach (KerFlip w) T U := by
    intro U hr
    induction hr with
    | refl => intro _; exact DReach.refl _
    | @tail U0 V0 r' st ih =>
      intro hU
      have eU : lv U0 = lv V0 := by
        cases st with
        | fwd c A B C _ => exact lv_fill (by simp [lv]) c
        | bwd c A B C _ => exact lv_fill (by simp [lv]) c
      have ih' := ih (eU.trans hU)
      refine DReach.tail ih' ⟨dnstep_flip st, ?_⟩
      intro ρ
      exact same _ _ eU (by rw [eU, hU]; exact h2) ρ
  exact key T' r e.symm

end Closure
