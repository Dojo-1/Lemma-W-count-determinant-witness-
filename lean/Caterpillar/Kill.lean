import Caterpillar.Artin

/-!
# K: killing letters

Setting the letters of a set `K` to `1` is a specialisation. On bracketings it deletes the leaves that
carry a killed letter (`kill`).

* `kill_ev`: the value of `T` at a valuation with `ρ ℓ = 1` on killed letters equals the value of
  the restricted bracketing (or `1` if nothing survives).
* `kill_id`: identities of `w` map to identities of the restriction.
* `kill_flip`: a flip `(AB)C → A(BC)` in any context restricts either to the identity or to a flip
  `(A'B')C' → A'(B'C')` in a restricted context, with surviving letter counts unchanged.
* `kill_minor`: hence every `3 × 3` minor of the restricted count matrix is a minor of the original
  one. A `D_N`-edge (all minors `0`, i.e. rank ≤ 2) restricts to a `D_N`-edge or to the identity.
-/

namespace Octonion
open Caterpillar (Tree)

/-- delete the leaves whose letter is killed -/
def kill (w : Nat → Nat) (K : Nat → Bool) : Tree → Option Tree
  | .leaf i => if K (w i) then none else some (.leaf i)
  | .node l r =>
    match kill w K l, kill w K r with
    | none, x => x
    | some a, none => some a
    | some a, some b => some (.node a b)

/-- value of an optional bracketing (`none` ↦ `1`) -/
def evo (w : Nat → Nat) (ρ : Nat → O) : Option Tree → O
  | none => one
  | some T => ev w ρ T

theorem kill_ev (w : Nat → Nat) (K : Nat → Bool) (ρ : Nat → O) (hK : ∀ ℓ, K ℓ = true → ρ ℓ = one) :
    ∀ T, ev w ρ T = evo w ρ (kill w K T)
  | .leaf i => by
    simp only [kill]
    split
    · next h => simp only [evo, ev]; exact hK _ h
    · rfl
  | .node l r => by
    simp only [ev, kill]
    rw [kill_ev w K ρ hK l, kill_ev w K ρ hK r]
    cases kill w K l <;> cases kill w K r <;> simp only [evo, one_mul, mul_one]
    all_goals rfl

/-- **K, identities.** Killing is a specialisation: equal maps restrict to equal maps. -/
theorem kill_id (w : Nat → Nat) (K : Nat → Bool) (T T' : Tree)
    (h : ∀ ρ : Nat → O, ev w ρ T = ev w ρ T') :
    ∀ ρ : Nat → O, (∀ ℓ, K ℓ = true → ρ ℓ = one) → evo w ρ (kill w K T) = evo w ρ (kill w K T') := by
  intro ρ hK
  rw [← kill_ev w K ρ hK, ← kill_ev w K ρ hK]
  exact h ρ

/-! ## restriction of flips -/

/-- restrict a context: either the hole is killed away entirely … no, contexts are restricted
relative to a surviving hole; `killC` returns the restricted context. -/
def killC (w : Nat → Nat) (K : Nat → Bool) : Ctx → Ctx
  | .hole => .hole
  | .inL c r =>
    match kill w K r with
    | none => killC w K c
    | some r' => .inL (killC w K c) r'
  | .inR l c =>
    match kill w K l with
    | none => killC w K c
    | some l' => .inR l' (killC w K c)

/-- killing commutes with filling a context whose hole survives -/
theorem kill_fill (w : Nat → Nat) (K : Nat → Bool) (S S' : Tree) (hS : kill w K S = some S') :
    ∀ c : Ctx, kill w K (fill c S) = some (fill (killC w K c) S')
  | .hole => by simp [fill, killC, hS]
  | .inL c r => by
    simp only [fill, kill, killC, kill_fill w K S S' hS c]
    cases kill w K r <;> rfl
  | .inR l c => by
    simp only [fill, kill, killC, kill_fill w K S S' hS c]
    cases kill w K l <;> rfl

/-- killing commutes with filling: if the hole is killed away, the context's own restriction remains -/
theorem kill_fill_none (w : Nat → Nat) (K : Nat → Bool) (S1 S2 : Tree)
    (h1 : kill w K S1 = kill w K S2) : ∀ c : Ctx, kill w K (fill c S1) = kill w K (fill c S2)
  | .hole => h1
  | .inL c r => by simp only [fill, kill, kill_fill_none w K S1 S2 h1 c]
  | .inR l c => by simp only [fill, kill, kill_fill_none w K S1 S2 h1 c]

/-- **K, flips.** A flip restricts to the identity or to a flip of the restricted parts. -/
theorem kill_flip (w : Nat → Nat) (K : Nat → Bool) (c : Ctx) (A B C : Tree) :
    kill w K (fill c (.node (.node A B) C)) = kill w K (fill c (.node A (.node B C))) ∨
    ∃ A' B' C', kill w K A = some A' ∧ kill w K B = some B' ∧ kill w K C = some C' ∧
      kill w K (fill c (.node (.node A B) C)) = some (fill (killC w K c) (.node (.node A' B') C')) ∧
      kill w K (fill c (.node A (.node B C))) = some (fill (killC w K c) (.node A' (.node B' C'))) := by
  cases hA : kill w K A <;> cases hB : kill w K B <;> cases hC : kill w K C
  case some.some.some A' B' C' =>
    right
    refine ⟨A', B', C', rfl, rfl, rfl, ?_, ?_⟩
    · apply kill_fill; simp [kill, hA, hB, hC]
    · apply kill_fill; simp [kill, hA, hB, hC]
  all_goals
    left; apply kill_fill_none; simp [kill, hA, hB, hC]

/-! ## letter counts and minors -/

def cnt (w : Nat → Nat) (ℓ : Nat) : Tree → Int
  | .leaf i => if w i = ℓ then 1 else 0
  | .node l r => cnt w ℓ l + cnt w ℓ r

def cnto (w : Nat → Nat) (ℓ : Nat) : Option Tree → Int
  | none => 0
  | some T => cnt w ℓ T

/-- surviving letters keep their counts; killed letters get count `0` -/
theorem cnt_kill (w : Nat → Nat) (K : Nat → Bool) (ℓ : Nat) :
    ∀ T, cnto w ℓ (kill w K T) = if K ℓ then 0 else cnt w ℓ T
  | .leaf i => by
    simp only [kill, cnt]
    by_cases h : K (w i) = true
    · simp only [h, if_true, cnto]
      by_cases e : w i = ℓ
      · subst e; simp [h]
      · simp [e]
    · simp only [h, cnto, cnt]
      by_cases e : w i = ℓ
      · subst e; simp [h, cnt]
      · simp [e, cnt]
  | .node l r => by
    have hl := cnt_kill w K ℓ l; have hr := cnt_kill w K ℓ r
    simp only [kill, cnt]
    revert hl hr
    cases K ℓ <;> cases kill w K l <;> cases kill w K r <;> intro hl hr <;>
      simp only [cnto, cnt, Bool.false_eq_true, if_true, if_false] at hl hr ⊢ <;> omega

/-- the `3 × 3` minor of the count matrix of `(A, B, C)` on letters `p, q, r` -/
def minor (w : Nat → Nat) (A B C : Tree) (p q r : Nat) : Int :=
  cnt w p A * (cnt w q B * cnt w r C - cnt w r B * cnt w q C)
  - cnt w q A * (cnt w p B * cnt w r C - cnt w r B * cnt w p C)
  + cnt w r A * (cnt w p B * cnt w q C - cnt w q B * cnt w p C)

/-- a flip is a `D_N`-flip when its count matrix has rank ≤ 2 (all `3 × 3` minors vanish) -/
def DN (w : Nat → Nat) (A B C : Tree) : Prop := ∀ p q r, minor w A B C p q r = 0

theorem minor_kill (w : Nat → Nat) (K : Nat → Bool) (A B C A' B' C' : Tree)
    (hA : kill w K A = some A') (hB : kill w K B = some B') (hC : kill w K C = some C') (p q r : Nat) :
    minor w A' B' C' p q r =
      (if K p ∨ K q ∨ K r then 0 else minor w A B C p q r) := by
  have e : ∀ ℓ X X', kill w K X = some X' → cnt w ℓ X' = if K ℓ then 0 else cnt w ℓ X := by
    intro ℓ X X' h; have := cnt_kill w K ℓ X; rw [h] at this; exact this
  simp only [minor, e p A A' hA, e q A A' hA, e r A A' hA, e p B B' hB, e q B B' hB, e r B B' hB,
    e p C C' hC, e q C C' hC, e r C C' hC]
  by_cases hp : K p = true <;> by_cases hq : K q = true <;> by_cases hr : K r = true <;>
    simp [hp, hq, hr]

/-- **K, `D_N`-edges.** Deleting columns cannot raise rank: a `D_N`-flip restricts to a `D_N`-flip or to
the identity. -/
theorem kill_DN (w : Nat → Nat) (K : Nat → Bool) (c : Ctx) (A B C : Tree) (h : DN w A B C) :
    kill w K (fill c (.node (.node A B) C)) = kill w K (fill c (.node A (.node B C))) ∨
    ∃ A' B' C', DN w A' B' C' ∧
      kill w K (fill c (.node (.node A B) C)) = some (fill (killC w K c) (.node (.node A' B') C')) ∧
      kill w K (fill c (.node A (.node B C))) = some (fill (killC w K c) (.node A' (.node B' C'))) := by
  rcases kill_flip w K c A B C with e | ⟨A', B', C', hA, hB, hC, e1, e2⟩
  · exact Or.inl e
  · refine Or.inr ⟨A', B', C', ?_, e1, e2⟩
    intro p q r
    rw [minor_kill w K A B C A' B' C' hA hB hC]
    split
    · rfl
    · exact h p q r

end Octonion
