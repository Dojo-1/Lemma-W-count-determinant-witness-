import Caterpillar.Basic

/-!
# Decision procedures and their soundness

`chainB`, `catB` are executable searches for `Chain`/`Cat` certificates. Their soundness theorems let
the finite base of Proposition E be discharged by `decide` (kernel evaluation).
-/

namespace Caterpillar

instance decNoAdj : (s : List L3) → Decidable (NoAdj s)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: t =>
    match decNoAdj (b :: t) with
    | isTrue h => if hab : a = b then isFalse (fun h' => h'.1 hab) else isTrue ⟨hab, h⟩
    | isFalse h => isFalse (fun h' => h h'.2)

theorem allThree_iff (s : List L3) : AllThree s ↔ ((0 : L3) ∈ s ∧ (1 : L3) ∈ s ∧ (2 : L3) ∈ s) := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · intro ⟨h0, h1, h2⟩ c
    match c with
    | ⟨0, _⟩ => exact h0
    | ⟨1, _⟩ => exact h1
    | ⟨2, _⟩ => exact h2

instance (s : List L3) : Decidable (AllThree s) := decidable_of_iff _ (allThree_iff s).symm

instance (s : List L3) : Decidable (Valid s) := by unfold Valid; infer_instance

instance (a : Option L3) (b : L3) (r : List L3) : Decidable (Cond a b r) := by
  cases a <;> unfold Cond <;> infer_instance

instance (s : List L3) (e : Option L3) : Decidable (Failure s e) := by
  cases e <;> unfold Failure <;> infer_instance

/-- `s = tr.reverse ++ [c]` when `s.reverse = c :: tr`. -/
theorem eq_of_reverse_eq_cons {s tr : List L3} {c : L3} (h : s.reverse = c :: tr) :
    s = tr.reverse ++ [c] := by
  have := congrArg List.reverse h
  simpa using this

def bottomB : List L3 → Option L3 → Bool
  | [u, v], some b => decide (b ≠ u ∧ b ≠ v ∧ u ≠ v)
  | _, _ => false

theorem bottomB_sound {s : List L3} {a : Option L3} (h : bottomB s a = true) :
    ∃ u v b, s = [u, v] ∧ a = some b ∧ b ≠ u ∧ b ≠ v ∧ u ≠ v := by
  unfold bottomB at h
  split at h
  · rename_i u v b
    exact ⟨u, v, b, rfl, rfl, of_decide_eq_true h⟩
  · exact absurd h (by simp)

def stepLB (rec : List L3 → Option L3 → Bool) (s : List L3) (a : Option L3) : Bool :=
  match s with
  | c :: t => decide (2 ≤ t.length) && decide (Cond a c t) && rec t (some c)
  | [] => false

def stepRB (rec : List L3 → Option L3 → Bool) (s : List L3) (a : Option L3) : Bool :=
  match s.reverse with
  | c :: tr => decide (2 ≤ tr.reverse.length) && decide (Cond a c tr.reverse) && rec tr.reverse (some c)
  | [] => false

def stepDB (rec : List L3 → Option L3 → Bool) (s : List L3) (a : Option L3) : Bool :=
  match s with
  | p :: r =>
    match r.reverse with
    | q :: mr => decide (p = q) && decide (2 ≤ mr.reverse.length) && decide (Cond a p mr.reverse) &&
        rec mr.reverse (some p)
    | [] => false
  | [] => false

theorem stepLB_sound {rec : List L3 → Option L3 → Bool} {P : List L3 → Option L3 → Prop}
    (hrec : ∀ s a, rec s a = true → P s a) {s : List L3} {a : Option L3} (h : stepLB rec s a = true) :
    ∃ c t, s = c :: t ∧ 2 ≤ t.length ∧ Cond a c t ∧ P t (some c) := by
  unfold stepLB at h
  split at h
  · rename_i c t
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨c, t, rfl, h.1.1, h.1.2, hrec _ _ h.2⟩
  · exact absurd h (by simp)

theorem stepRB_sound {rec : List L3 → Option L3 → Bool} {P : List L3 → Option L3 → Prop}
    (hrec : ∀ s a, rec s a = true → P s a) {s : List L3} {a : Option L3} (h : stepRB rec s a = true) :
    ∃ c t, s = t ++ [c] ∧ 2 ≤ t.length ∧ Cond a c t ∧ P t (some c) := by
  unfold stepRB at h
  split at h
  · rename_i c tr hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨c, tr.reverse, eq_of_reverse_eq_cons hs, h.1.1, h.1.2, hrec _ _ h.2⟩
  · exact absurd h (by simp)

theorem stepDB_sound {rec : List L3 → Option L3 → Bool} {P : List L3 → Option L3 → Prop}
    (hrec : ∀ s a, rec s a = true → P s a) {s : List L3} {a : Option L3} (h : stepDB rec s a = true) :
    ∃ p m, s = p :: (m ++ [p]) ∧ 2 ≤ m.length ∧ Cond a p m ∧ P m (some p) := by
  unfold stepDB at h
  split at h
  · rename_i p r
    split at h
    · rename_i q mr hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hpq, hl⟩, hc⟩, hp⟩ := h
      subst hpq
      exact ⟨p, mr.reverse, by rw [eq_of_reverse_eq_cons hr], hl, hc, hrec _ _ hp⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

def chainB : Nat → List L3 → Option L3 → Bool
  | 0, _, _ => false
  | n + 1, s, a =>
    bottomB s a || stepLB (chainB n) s a || stepRB (chainB n) s a || stepDB (chainB n) s a

theorem chainB_sound : ∀ n s a, chainB n s a = true → Chain s a
  | 0, _, _, h => absurd h (by simp [chainB])
  | n + 1, s, a, h => by
    simp only [chainB, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · obtain ⟨u, v, b, rfl, rfl, h1, h2, h3⟩ := bottomB_sound h
      exact Chain.bottom b u v h1 h2 h3
    · obtain ⟨c, t, rfl, hl, hc, hp⟩ := stepLB_sound (chainB_sound n) h
      exact Chain.stepL c t a hl hc hp
    · obtain ⟨c, t, rfl, hl, hc, hp⟩ := stepRB_sound (chainB_sound n) h
      exact Chain.stepR c t a hl hc hp
    · obtain ⟨p, m, rfl, hl, hc, hp⟩ := stepDB_sound (chainB_sound n) h
      exact Chain.stepD p m a hl hc hp

def chainLB (n : Nat) (s : List L3) (a : Option L3) : Bool := bottomB s a || stepLB (chainB n) s a
def chainRB (n : Nat) (s : List L3) (a : Option L3) : Bool := bottomB s a || stepRB (chainB n) s a

theorem chainLB_sound {n s a} (h : chainLB n s a = true) : ChainL s a := by
  simp only [chainLB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (bottomB_sound h)
  · exact Or.inr (stepLB_sound (chainB_sound n) h)

theorem chainRB_sound {n s a} (h : chainRB n s a = true) : ChainR s a := by
  simp only [chainRB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (bottomB_sound h)
  · exact Or.inr (stepRB_sound (chainB_sound n) h)

/-- left Moufang pattern at the front of `s` -/
def moveLB (n : Nat) (s : List L3) (a : Option L3) : Bool :=
  match s with
  | x :: y :: x' :: t => decide (x = x') && decide (Cond a x (y :: x :: t)) &&
      decide (Cond (some x) y (x :: t)) && chainLB n (x :: t) (some y)
  | _ => false

/-- right Moufang pattern at the back of `s` (read on the reversal) -/
def moveRB (n : Nat) (s : List L3) (a : Option L3) : Bool :=
  match s.reverse with
  | x :: y :: x' :: tr => decide (x = x') && decide (Cond a x (tr.reverse ++ [x, y])) &&
      decide (Cond (some x) y (tr.reverse ++ [x])) && chainRB n (tr.reverse ++ [x]) (some y)
  | _ => false

def catB : Nat → List L3 → Option L3 → Bool
  | 0, _, _ => false
  | n + 1, s, a =>
    stepLB (catB n) s a || stepRB (catB n) s a || stepDB (catB n) s a || stepDB (chainB n) s a ||
    moveLB n s a || moveRB n s a

theorem catB_sound : ∀ n s a, catB n s a = true → Cat s a
  | 0, _, _, h => absurd h (by simp [catB])
  | n + 1, s, a, h => by
    simp only [catB, Bool.or_eq_true] at h
    rcases h with ((((h | h) | h) | h) | h) | h
    · obtain ⟨c, t, rfl, hl, hc, hp⟩ := stepLB_sound (catB_sound n) h
      exact Cat.passL c t a hl hc hp
    · obtain ⟨c, t, rfl, hl, hc, hp⟩ := stepRB_sound (catB_sound n) h
      exact Cat.passR c t a hl hc hp
    · obtain ⟨p, m, rfl, hl, hc, hp⟩ := stepDB_sound (catB_sound n) h
      exact Cat.passD p m a hl hc hp
    · obtain ⟨p, m, rfl, hl, hc, hp⟩ := stepDB_sound (chainB_sound n) h
      exact Cat.moveD p m a hl hc hp
    · unfold moveLB at h
      split at h
      · rename_i x y x' t
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hx, h1⟩, h2⟩, h3⟩ := h
        subst hx
        exact Cat.moveL x y t a h1 h2 (chainLB_sound h3)
      · exact absurd h (by simp)
    · unfold moveRB at h
      split at h
      · rename_i x y x' tr hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hx, h1⟩, h2⟩, h3⟩ := h
        subst hx
        have : s = tr.reverse ++ [x, y, x] := by
          have := congrArg List.reverse hs
          simpa using this
        subst this
        exact Cat.moveR x y tr.reverse a h1 h2 (chainRB_sound h3)
      · exact absurd h (by simp)

end Caterpillar
