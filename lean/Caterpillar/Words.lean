import Caterpillar.PropE

/-!
# From words to run sequences

`runSeq w` collapses maximal runs of a word over three letters. A word is an *interval word* exactly
when each letter occupies one run, i.e. when `runSeq w` has no repeated letter. For a non-interval word
that uses all three letters, the run sequence is `Valid`, so Proposition E applies.
-/

namespace Caterpillar

def runSeq : List L3 → List L3
  | [] => []
  | a :: t =>
    match runSeq t with
    | [] => [a]
    | b :: r => if a = b then b :: r else a :: b :: r

theorem runSeq_cons_head (a : L3) (t : List L3) : ∃ r, runSeq (a :: t) = a :: r := by
  simp only [runSeq]
  split
  · exact ⟨[], rfl⟩
  · rename_i b r _
    by_cases h : a = b
    · subst h; simp
    · simp [h]

theorem noAdj_runSeq : ∀ w : List L3, NoAdj (runSeq w)
  | [] => trivial
  | a :: t => by
    have ih := noAdj_runSeq t
    simp only [runSeq]
    split
    · trivial
    · rename_i b r hr
      rw [hr] at ih
      by_cases h : a = b
      · simp [h]; exact ih
      · simp [h]; exact ⟨h, ih⟩

theorem mem_runSeq : ∀ (w : List L3) (c : L3), c ∈ runSeq w ↔ c ∈ w
  | [] , c => by simp [runSeq]
  | a :: t, c => by
    have ih := mem_runSeq t c
    simp only [runSeq]
    split
    · rename_i hr
      rw [hr] at ih
      have : t = [] := by
        cases t with
        | nil => rfl
        | cons x t' => obtain ⟨r, hr'⟩ := runSeq_cons_head x t'; rw [hr'] at hr; cases hr
      subst this; simp
    · rename_i b r hr
      rw [hr] at ih
      by_cases h : a = b
      · subst h
        simp only [if_true, List.mem_cons] at ih ⊢
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (ih.1 (Or.inr h))
        · rintro (h | h)
          · exact Or.inl h
          · exact ih.2 h
      · simp only [h, if_false, List.mem_cons] at ih ⊢; rw [ih]

/-- A list over three letters that uses all of them and has at most 3 entries has no repeat. -/
theorem nodup_of_short (l : List L3) (h3 : AllThree l) (hl : l.length ≤ 3) : l.Nodup := by
  have key : ∀ k, k ≤ 3 → ∀ l ∈ allLists k, AllThree l → l.Nodup := by
    intro k hk
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
  exact key l.length hl l (mem_allLists l) h3

theorem valid_runSeq (w : List L3) (h3 : AllThree w) (hni : ¬ (runSeq w).Nodup) :
    Valid (runSeq w) := by
  have h3' : AllThree (runSeq w) := fun c => (mem_runSeq w c).2 (h3 c)
  refine ⟨noAdj_runSeq w, h3', ?_⟩
  rcases Nat.lt_or_ge (runSeq w).length 4 with hlt | h
  · exact absurd (nodup_of_short _ h3' (by omega)) hni
  · exact h

/-- **G3, run-sequence form.** Every non-interval word over three letters has a caterpillar certificate. -/
theorem cat_of_word (w : List L3) (h3 : AllThree w) (hni : ¬ (runSeq w).Nodup) :
    Cat (runSeq w) none := by
  have := valid_runSeq w h3 hni
  exact cat_of_valid _ this

end Caterpillar
