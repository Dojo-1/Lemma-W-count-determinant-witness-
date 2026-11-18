import Caterpillar.PropC

/-!
# Proposition C (⇒), full form, and Proposition C as an equivalence

* `sh_fill`: changing a subtree changes only the shapes of triples inside it.
* `sh_flip`: a `D_N`-flip `(AB)C → A(BC)` of an interval word keeps every distinct-letter triple shape:
  only triples in `A × B × C` change, and `propC_forward` excludes distinct letters there.
* `reach_sig`: `D_N`-reachable bracketings have equal σ.
* **`propC_iff`**: for an interval word, `T ∼_D T' ⟺ σ(T) = σ(T')`.
-/

namespace Octonion
open Caterpillar (Tree)

theorem lettersT_eq (w : Nat → Nat) : ∀ T, lettersT w T = (lv T).map w
  | .leaf _ => rfl
  | .node l r => by simp [lettersT, lv, lettersT_eq w l, lettersT_eq w r]

theorem lv_fill {X Y : Tree} (e : lv X = lv Y) : ∀ c : Ctx, lv (fill c X) = lv (fill c Y)
  | .hole => e
  | .inL c R => by simp only [fill, lv, lv_fill e c]
  | .inR L c => by simp only [fill, lv, lv_fill e c]

/-- equal shapes inside `X, Y` give equal shapes in every context -/
theorem sh_fill (w : Nat → Nat) {X Y : Tree} (e : lv X = lv Y)
    (hs : ∀ i j k, i ∈ lv X → j ∈ lv X → k ∈ lv X → i < j → j < k → Distinct w i j k → sh X i j k = sh Y i j k) :
    ∀ c : Ctx, ∀ i j k, (lv (fill c X)).Pairwise (· < ·) → i ∈ lv (fill c X) → j ∈ lv (fill c X) →
      k ∈ lv (fill c X) → i < j → j < k → Distinct w i j k → sh (fill c X) i j k = sh (fill c Y) i j k
  | .hole, i, j, k, _, hi, hj, hk, h1, h2, hd => hs i j k hi hj hk h1 h2 hd
  | .inL c R, i, j, k, hpw, hi, hj, hk, h1, h2, hd => by
    simp only [fill, lv, List.mem_append] at hpw hi hj hk ⊢
    have e' := lv_fill e c
    by_cases hkL : k ∈ lv (fill c X)
    · have hiL : i ∈ lv (fill c X) := by
        rcases hi with hi | hi; exact hi; exact absurd (pw_lt hpw hkL hi) (by omega)
      have hjL : j ∈ lv (fill c X) := by
        rcases hj with hj | hj; exact hj; exact absurd (pw_lt hpw hkL hj) (by omega)
      rw [sh_L _ _ i j k hkL, sh_L _ _ i j k (e' ▸ hkL)]
      exact sh_fill w e hs c i j k (List.pairwise_append.1 hpw).1 hiL hjL hkL h1 h2 hd
    · by_cases hiR : i ∈ lv R
      · rw [sh_R _ _ i j k hkL hiR, sh_R _ _ i j k (e' ▸ hkL) hiR]
      · rw [sh_M _ _ i j k hkL hiR, sh_M _ _ i j k (e' ▸ hkL) hiR, e']
  | .inR L c, i, j, k, hpw, hi, hj, hk, h1, h2, hd => by
    simp only [fill, lv, List.mem_append] at hpw hi hj hk ⊢
    have e' := lv_fill e c
    by_cases hkL : k ∈ lv L
    · rw [sh_L _ _ i j k hkL, sh_L _ _ i j k hkL]
    · have hkR : k ∈ lv (fill c X) := by rcases hk with hk | hk; exact absurd hk hkL; exact hk
      by_cases hiR : i ∈ lv (fill c X)
      · have hjR : j ∈ lv (fill c X) := by
          rcases hj with hj | hj; exact absurd (pw_lt hpw hj hiR) (by omega); exact hj
        rw [sh_R _ _ i j k hkL hiR, sh_R _ _ i j k hkL (e' ▸ hiR)]
        exact sh_fill w e hs c i j k (List.pairwise_append.1 hpw).2.1 hiR hjR hkR h1 h2 hd
      · rw [sh_M _ _ i j k hkL hiR, sh_M _ _ i j k hkL (e' ▸ hiR)]

/-- a `D_N`-flip of an interval word keeps all distinct-letter triple shapes -/
theorem sh_flip (w : Nat → Nat) (hw : MonoW w) (A B C : Tree) (hd : DN w A B C)
    (hpw : (lv A ++ lv B ++ lv C).Pairwise (· < ·)) :
    ∀ i j k, i ∈ lv (.node (.node A B) C) → j ∈ lv (.node (.node A B) C) → k ∈ lv (.node (.node A B) C) →
      i < j → j < k → Distinct w i j k → sh (.node (.node A B) C) i j k = sh (.node A (.node B C)) i j k := by
  have pAB : (lv A ++ lv B).Pairwise (· < ·) := (List.pairwise_append.1 hpw).1
  have oAB : ∀ s ∈ lv A, ∀ t ∈ lv B, s < t := fun s hs t ht => pw_lt pAB hs ht
  have oAC : ∀ s ∈ lv A, ∀ t ∈ lv C, s < t := fun s hs t ht => pw_lt hpw (by simp [hs]) ht
  have oBC : ∀ s ∈ lv B, ∀ t ∈ lv C, s < t := fun s hs t ht => pw_lt hpw (by simp [hs]) ht
  intro i j k hi hj hk h1 h2 hdd
  simp only [lv, List.mem_append] at hi hj hk
  -- every impossible ordering is excluded by `omega`
  have nA : ∀ t, t ∈ lv B ∨ t ∈ lv C → t ∉ lv A := by
    intro t ht ha; rcases ht with ht | ht
    · exact absurd (oAB t ha t ht) (Nat.lt_irrefl t)
    · exact absurd (oAC t ha t ht) (Nat.lt_irrefl t)
  have nB : ∀ t, t ∈ lv A ∨ t ∈ lv C → t ∉ lv B := by
    intro t ht hb; rcases ht with ht | ht
    · exact absurd (oAB t ht t hb) (Nat.lt_irrefl t)
    · exact absurd (oBC t hb t ht) (Nat.lt_irrefl t)
  have nC : ∀ t, t ∈ lv A ∨ t ∈ lv B → t ∉ lv C := by
    intro t ht hc; rcases ht with ht | ht
    · exact absurd (oAC t ht t hc) (Nat.lt_irrefl t)
    · exact absurd (oBC t ht t hc) (Nat.lt_irrefl t)
  have cross : i ∈ lv A → j ∈ lv B → k ∈ lv C → False := by
    intro hi hj hk
    have hs : List.Pairwise (· ≤ ·) (lettersT w A ++ lettersT w B ++ lettersT w C) := by
      simp only [lettersT_eq, ← List.map_append]
      exact List.pairwise_map.2 (hpw.imp (fun h => hw _ _ (Nat.le_of_lt h)))
    exact (propC_forward w A B C hs (w i) (w j) (w k) (by simp [lettersT_eq]; exact ⟨i, hi, rfl⟩)
      (by simp [lettersT_eq]; exact ⟨j, hj, rfl⟩) (by simp [lettersT_eq]; exact ⟨k, hk, rfl⟩)
      hdd.1 hdd.2.1 hdd.2.2).2 hd
  rcases hi with (hi | hi) | hi <;> rcases hj with (hj | hj) | hj <;> rcases hk with (hk | hk) | hk
  all_goals first
    | (exfalso; first
        | exact cross hi hj hk
        | (have := oAB _ hj _ hi; omega) | (have := oAB _ hk _ hi; omega) | (have := oAB _ hk _ hj; omega)
        | (have := oAC _ hj _ hi; omega) | (have := oAC _ hk _ hi; omega) | (have := oAC _ hk _ hj; omega)
        | (have := oBC _ hj _ hi; omega) | (have := oBC _ hk _ hi; omega) | (have := oBC _ hk _ hj; omega))
    | skip
  all_goals
    have := nA i; have := nA j; have := nA k; have := nB i; have := nB j; have := nB k
    have := nC i; have := nC j; have := nC k
    simp_all [sh, lv]

/-- a `D_N`-step keeps the leaves and σ -/
theorem dnstep_sig (w : Nat → Nat) (hw : MonoW w) {T U : Tree} (h : DNStep w T U)
    (hpw : (lv T).Pairwise (· < ·)) : lv T = lv U ∧ SigEq w T U := by
  cases h with
  | fwd c A B C hd =>
    have e : lv (.node (.node A B) C) = lv (.node A (.node B C)) := by simp [lv]
    refine ⟨lv_fill e c, ?_⟩
    intro i j k hi hj hk h1 h2 hdd
    refine sh_fill w e ?_ c i j k hpw hi hj hk h1 h2 hdd
    have : (lv A ++ lv B ++ lv C).Pairwise (· < ·) := by
      have := sublist_fill c (.node (.node A B) C); simp only [lv] at this
      exact hpw.sublist this
    exact sh_flip w hw A B C hd this
  | bwd c A B C hd =>
    have e : lv (.node A (.node B C)) = lv (.node (.node A B) C) := by simp [lv]
    refine ⟨lv_fill e c, ?_⟩
    intro i j k hi hj hk h1 h2 hdd
    refine sh_fill w e ?_ c i j k hpw hi hj hk h1 h2 hdd
    have : (lv A ++ lv B ++ lv C).Pairwise (· < ·) := by
      have := sublist_fill c (.node A (.node B C)); simp only [lv, List.append_assoc] at this ⊢
      exact hpw.sublist this
    intro i j k hi hj hk h1 h2 hdd
    exact (sh_flip w hw A B C hd (by simpa [List.append_assoc] using this) i j k
      (by simpa [lv, List.append_assoc] using hi) (by simpa [lv, List.append_assoc] using hj)
      (by simpa [lv, List.append_assoc] using hk) h1 h2 hdd).symm
where
  sublist_fill : ∀ (c : Ctx) (X : Tree), (lv X).Sublist (lv (fill c X))
    | .hole, _ => List.Sublist.refl _
    | .inL c R, X => by simp only [fill, lv]; exact (sublist_fill c X).trans (List.sublist_append_left _ _)
    | .inR L c, X => by simp only [fill, lv]; exact (sublist_fill c X).trans (List.sublist_append_right _ _)

theorem SigEq.trans {w : Nat → Nat} {T U V : Tree} (e : lv T = lv U) (h1 : SigEq w T U) (h2 : SigEq w U V) :
    SigEq w T V := by
  intro i j k hi hj hk a b d
  rw [h1 i j k hi hj hk a b d, h2 i j k (e ▸ hi) (e ▸ hj) (e ▸ hk) a b d]

/-- **Proposition C (⇒).** `D_N`-reachable bracketings of an interval word have equal σ. -/
theorem reach_sig (w : Nat → Nat) (hw : MonoW w) {T U : Tree} (h : DReach (DNStep w) T U)
    (hpw : (lv T).Pairwise (· < ·)) : lv T = lv U ∧ SigEq w T U := by
  induction h with
  | refl => exact ⟨rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨e1, s1⟩ := ih
    obtain ⟨e2, s2⟩ := dnstep_sig w hw hst (e1 ▸ hpw)
    exact ⟨e1.trans e2, SigEq.trans e1 s1 s2⟩

/-- **Proposition C.** For an interval word and bracketings of the same increasing leaf list:
`T, T'` lie in the same `D_N`-component iff they induce the same shape on every distinct-letter triple. -/
theorem propC_iff (w : Nat → Nat) (hw : MonoW w) (T T' : Tree) (e : lv T = lv T')
    (hpw : (lv T).Pairwise (· < ·)) : DReach (DNStep w) T T' ↔ SigEq w T T' :=
  ⟨fun h => (reach_sig w hw h hpw).2, fun h => propC w hw T T' e hpw h⟩

end Octonion
