import Caterpillar.Base

/-!
# Proposition E: every valid run sequence has a caterpillar certificate

`propE : Valid s → ¬ Failure s e → Cat s e`, by strong induction on the length. The bases (4 and 5 runs)
come from `Base.lean`; the step peels an end run (`L`/`R`) or both equal end runs (`D`).
-/

namespace Caterpillar

/-! ## List lemmas -/

theorem noAdj_tail {c : L3} {t : List L3} (h : NoAdj (c :: t)) : NoAdj t := by
  match t, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem noAdj_head_ne {c : L3} {t : List L3} (h : NoAdj (c :: t)) : t.head? ≠ some c := by
  match t, h with
  | [], _ => simp
  | b :: _, h => simpa [eq_comm] using h.1

theorem noAdj_append_iff (t : List L3) (c : L3) :
    NoAdj (t ++ [c]) ↔ NoAdj t ∧ t.getLast? ≠ some c := by
  induction t with
  | nil => simp [NoAdj]
  | cons a t ih =>
    match t with
    | [] => simp [NoAdj]
    | b :: t' =>
      have : (a :: b :: t') ++ [c] = a :: (b :: (t' ++ [c])) := rfl
      rw [this]
      simp only [NoAdj] at ih ⊢
      rw [show b :: (t' ++ [c]) = (b :: t') ++ [c] from rfl, ih]
      simp only [List.getLast?_cons_cons]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

theorem letters_of_two :
    ∀ a b x c : L3, a ≠ b → a ≠ x → b ≠ x → c ≠ x → c = a ∨ c = b := by decide

/-- A list with no equal neighbours and ≥ 2 entries that avoids `x` contains every other letter. -/
theorem mem_of_avoid {l : List L3} (hn : NoAdj l) (hl : 2 ≤ l.length) {x : L3} (hx : x ∉ l)
    {c : L3} (hc : c ≠ x) : c ∈ l := by
  match l, hn, hl with
  | a :: b :: r, hn, _ =>
    have ha : a ≠ x := fun h => hx (h ▸ List.mem_cons_self _ _)
    have hb : b ≠ x := fun h => hx (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _))
    rcases letters_of_two a b x c hn.1 ha hb hc with h | h
    · exact h ▸ List.mem_cons_self _ _
    · exact h ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)

theorem not_allThree {t : List L3} (h : ¬ AllThree t) : ∃ x, x ∉ t := by
  rw [allThree_iff] at h
  by_cases h0 : (0 : L3) ∈ t
  · by_cases h1 : (1 : L3) ∈ t
    · exact ⟨2, fun h2 => h ⟨h0, h1, h2⟩⟩
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

theorem third_mem {a b : L3} {t : List L3} (h : AllThree t) : third a b ∈ t := h _

/-- Every list with ≥ 2 entries is `c0 :: (m ++ [cl])`. -/
theorem split_ends : ∀ (s : List L3), 2 ≤ s.length → ∃ c0 m cl, s = c0 :: (m ++ [cl])
  | c0 :: t, h => by
    have ht : t ≠ [] := by intro e; subst e; simp at h
    obtain ⟨m, cl, rfl⟩ : ∃ m cl, t = m ++ [cl] := by
      rcases List.eq_nil_or_concat t with e | ⟨m, cl, e⟩
      · exact absurd e ht
      · exact ⟨m, cl, e.trans (List.concat_eq_append _ _)⟩
    exact ⟨c0, m, cl, rfl⟩

theorem head?_of_two {m : List L3} (h : 1 ≤ m.length) : ∃ h0 r, m = h0 :: r := by
  match m, h with
  | h0 :: r, _ => exact ⟨h0, r, rfl⟩

theorem getLast?_cons_append (a c : L3) (m : List L3) : (a :: (m ++ [c])).getLast? = some c := by
  rw [show a :: (m ++ [c]) = (a :: m) ++ [c] from rfl, List.getLast?_append]; simp

theorem dropLast_cons_append (a c : L3) (m : List L3) : (a :: (m ++ [c])).dropLast = a :: m := by
  rw [show a :: (m ++ [c]) = (a :: m) ++ [c] from rfl, List.dropLast_concat]

theorem getLast?_append_single (c : L3) (m : List L3) : (m ++ [c]).getLast? = some c := by
  rw [List.getLast?_append]; simp

/-! ## The induction -/

theorem propE : ∀ (n : Nat) (s : List L3) (e : Option L3),
    s.length = n → Valid s → ¬ Failure s e → Cat s e := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s e hn hv hf
  obtain ⟨hna, hall, hlen⟩ := hv
  -- bases
  by_cases h4 : n = 4
  · exact cat_of_baseOK base4 s e (hn.trans h4) ⟨hna, hall, hlen⟩ hf
  by_cases h5 : n = 5
  · exact cat_of_baseOK base5 s e (hn.trans h5) ⟨hna, hall, hlen⟩ hf
  have h6 : 6 ≤ n := by omega
  obtain ⟨c0, m, cl, rfl⟩ := split_ends s (by omega)
  have hmlen : m.length + 2 = n := by simp at hn; omega
  -- neighbour facts
  have hna' : NoAdj (c0 :: m) ∧ (c0 :: m).getLast? ≠ some cl := by
    rw [← noAdj_append_iff]; simpa using hna
  have hm : NoAdj m := noAdj_tail hna'.1
  have hmh : m.head? ≠ some c0 := noAdj_head_ne hna'.1
  obtain ⟨m0, mr, hm0⟩ := head?_of_two (m := m) (by omega)
  have hml : m.getLast? ≠ some cl := by
    have := hna'.2; rw [hm0] at this ⊢; simpa using this
  have hmem : ∀ x, x ∈ c0 :: (m ++ [cl]) ↔ x = c0 ∨ x ∈ m ∨ x = cl := by
    intro x; simp [or_assoc]
  have htail_na : NoAdj (m ++ [cl]) := noAdj_tail hna
  -- facts about the failure predicate on the pieces
  have hfail_tail : ∀ p, c0 ≠ cl ∨ AllThree (m.tail ++ [cl]) → p = c0 →
      ¬ Failure (m ++ [cl]) (some p) := by
    intro p hcase hp; subst hp
    simp only [Failure, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    rw [hm0] at hmh ⊢
    simp only [List.cons_append, List.head?_cons, List.tail_cons] at hmh ⊢
    rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩)
    · exact hmh h1
    · exact hmh h1
    · rcases hcase with hc | hc
      · exact hc (Option.some.inj h1).symm
      · exact h2 (by simpa [hm0] using hc)
  -- `e` is not the excluded letter
  rcases Classical.em (c0 = cl) with hp | hne
  · ----- Case 2: equal ends `p`
    subst hp
    have he : e ≠ some c0 := by
      rintro rfl; exact hf (Or.inl ⟨rfl, getLast?_cons_append _ _ _⟩)
    have hcond : ∀ t, AllThree t → Cond e c0 t := by
      intro t ht
      cases e with
      | none => trivial
      | some a => exact ⟨fun h => he (h ▸ rfl), third_mem ht⟩
    by_cases hmall : AllThree m
    · -- D step
      refine Cat.passD c0 m e (by omega) (hcond m hmall) ?_
      refine ih m.length (by omega) m (some c0) rfl ⟨hm, hmall, by omega⟩ ?_
      simp only [Failure]
      rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hmh h1
      · exact hmh h1
      · exact hml h1
    · -- the middle avoids a letter, which must be `c0`; peel `L`
      obtain ⟨x, hx⟩ := not_allThree hmall
      have hxc : x = c0 := by
        rcases (hmem x).1 (hall x) with h | h | h
        · exact h
        · exact absurd h hx
        · exact h
      subst hxc
      have hother : ∀ c, c ≠ x → c ∈ m := fun c hc => mem_of_avoid hm (by omega) hx hc
      have htail_all : AllThree (m ++ [x]) := by
        intro c; by_cases hc : c = x
        · simp [hc]
        · exact List.mem_append_left _ (hother c hc)
      refine Cat.passL x (m ++ [x]) e (by simp; omega) (hcond _ htail_all) ?_
      refine ih (m ++ [x]).length (by simp; omega) _ (some x) rfl ⟨htail_na, htail_all, by simp; omega⟩ ?_
      apply hfail_tail x (Or.inr ?_) rfl
      intro c
      by_cases hc : c = x
      · simp [hc]
      · apply List.mem_append_left
        have hmr : m.tail = mr := by rw [hm0]; rfl
        rw [hmr]
        have hmrna : NoAdj mr := by rw [hm0] at hm; exact noAdj_tail hm
        have hxmr : x ∉ mr := fun h => hx (by rw [hm0]; exact List.mem_cons_of_mem _ h)
        exact mem_of_avoid hmrna (by rw [hm0] at hmlen; simp at hmlen; omega) hxmr hc
  · ----- Case 1: different ends
    -- the two peels
    have tryL : (e ≠ some c0) → AllThree (m ++ [cl]) → Cat (c0 :: (m ++ [cl])) e := by
      intro he hta
      refine Cat.passL c0 (m ++ [cl]) e (by simp; omega) ?_ ?_
      · cases e with
        | none => trivial
        | some a => exact ⟨fun h => he (h ▸ rfl), third_mem hta⟩
      · exact ih (m ++ [cl]).length (by simp; omega) _ (some c0) rfl
          ⟨htail_na, hta, by simp; omega⟩ (hfail_tail c0 (Or.inl hne) rfl)
    have tryR : (e ≠ some cl) → AllThree (c0 :: m) → Cat (c0 :: (m ++ [cl])) e := by
      intro he hta
      have : c0 :: (m ++ [cl]) = (c0 :: m) ++ [cl] := rfl
      rw [this]
      refine Cat.passR cl (c0 :: m) e (by simp; omega) ?_ ?_
      · cases e with
        | none => trivial
        | some a => exact ⟨fun h => he (h ▸ rfl), third_mem hta⟩
      · refine ih (c0 :: m).length (by simp; omega) _ (some cl) rfl
          ⟨hna'.1, hta, by simp; omega⟩ ?_
        simp only [Failure, List.head?_cons]
        rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
        · exact hne (Option.some.inj h1)
        · exact hne (Option.some.inj h1)
        · exact hna'.2 h1
    by_cases hL : e ≠ some c0 ∧ AllThree (m ++ [cl])
    · exact tryL hL.1 hL.2
    by_cases hR : e ≠ some cl ∧ AllThree (c0 :: m)
    · exact tryR hR.1 hR.2
    exfalso
    have hdl : (c0 :: (m ++ [cl])).dropLast = c0 :: m := dropLast_cons_append _ _ _
    have htl : (c0 :: (m ++ [cl])).tail = m ++ [cl] := rfl
    rcases Classical.em (e = some c0) with he0 | he0 <;>
    rcases Classical.em (e = some cl) with he1 | he1
    · exact hne (Option.some.inj (he0.symm.trans he1))
    · -- e = c0 and the prefix misses a letter: (F2)
      have : ¬ AllThree (c0 :: m) := fun h => hR ⟨he1, h⟩
      subst he0
      exact hf (Or.inr (Or.inl ⟨rfl, by rw [hdl]; exact this⟩))
    · -- e = cl and the suffix misses a letter: (F2')
      have : ¬ AllThree (m ++ [cl]) := fun h => hL ⟨he0, h⟩
      subst he1
      exact hf (Or.inr (Or.inr ⟨getLast?_cons_append _ _ _, by rw [htl]; exact this⟩))
    · -- both sides miss a letter: impossible
      have hA : ¬ AllThree (m ++ [cl]) := fun h => hL ⟨he0, h⟩
      have hB : ¬ AllThree (c0 :: m) := fun h => hR ⟨he1, h⟩
      obtain ⟨x, hx⟩ := not_allThree hA
      obtain ⟨y, hy⟩ := not_allThree hB
      have hxm : x ∉ m := fun h => hx (List.mem_append_left _ h)
      have hxc : x = c0 := by
        rcases (hmem x).1 (hall x) with h | h | h
        · exact h
        · exact absurd h hxm
        · exact absurd (h ▸ List.mem_append_right _ (List.mem_singleton_self _)) hx
      have hym : y ∉ m := fun h => hy (List.mem_cons_of_mem _ h)
      have hyc : y = cl := by
        rcases (hmem y).1 (hall y) with h | h | h
        · exact absurd (h ▸ List.mem_cons_self _ _) hy
        · exact absurd h hym
        · exact h
      have : y ≠ x := by rw [hxc, hyc]; exact fun h => hne h.symm
      exact hym (mem_of_avoid hm (by omega) hxm this)

/-- **Proposition E** at the root: every valid run sequence has a caterpillar certificate. -/
theorem cat_of_valid (s : List L3) (h : Valid s) : Cat s none :=
  propE s.length s none rfl h (by simp [Failure])

end Caterpillar
