/-!
# Caterpillar certificates: run-sequence combinatorics

A non-interval word over three letters has a *run sequence* `s : List L3`: the letters of its maximal
runs. Such a sequence has no two equal neighbours, uses all three letters and has `≥ 4` entries
(`Valid`). A *caterpillar* peels runs off the ends of `s`: the left run (`L`), the right run (`R`), or
both end runs when they carry the same letter (`D`). It continues down to a bottom of two runs.

* `Chain s a` — such a peeling satisfying the letter conditions (C1), (C2) of Lemma Cat, where `a` is the
  letter by which `s` was entered (`none` at the root);
* `Cat s a` — the same, together with a Moufang move (`D`, or the left/right Moufang pattern).

Lemma Cat (THEOREM.md) turns `Cat s none` into a Moufang move between different `D_N`-components. This
file and `PropE.lean` prove `Valid s → Cat s none` for every `s` (Proposition E).
-/

namespace Caterpillar

abbrev L3 := Fin 3

/-- The letter different from `a` and `b` (meaningful when `a ≠ b`). -/
def third (a b : L3) : L3 := ⟨(6 - a.val - b.val) % 3, Nat.mod_lt _ (by decide)⟩

theorem third_ne_left : ∀ a b : L3, a ≠ b → third a b ≠ a := by decide
theorem third_ne_right : ∀ a b : L3, a ≠ b → third a b ≠ b := by decide

/-- No two equal neighbours. -/
def NoAdj : List L3 → Prop
  | a :: b :: t => a ≠ b ∧ NoAdj (b :: t)
  | _ => True

/-- All three letters occur. -/
def AllThree (s : List L3) : Prop := ∀ c : L3, c ∈ s

def Valid (s : List L3) : Prop := NoAdj s ∧ AllThree s ∧ 4 ≤ s.length

/-- Condition (C1) for a node entered by `a` and left by peeling `b`; `rest` is the next node. -/
def Cond (a : Option L3) (b : L3) (rest : List L3) : Prop :=
  match a with
  | none => True
  | some a => a ≠ b ∧ third a b ∈ rest

/-- Certificates satisfying (C1), (C2), without a move requirement. -/
inductive Chain : List L3 → Option L3 → Prop
  | bottom (a u v : L3) : a ≠ u → a ≠ v → u ≠ v → Chain [u, v] (some a)
  | stepL (c : L3) (t : List L3) (a : Option L3) :
      2 ≤ t.length → Cond a c t → Chain t (some c) → Chain (c :: t) a
  | stepR (c : L3) (t : List L3) (a : Option L3) :
      2 ≤ t.length → Cond a c t → Chain t (some c) → Chain (t ++ [c]) a
  | stepD (p : L3) (m : List L3) (a : Option L3) :
      2 ≤ m.length → Cond a p m → Chain m (some p) → Chain (p :: (m ++ [p])) a

/-- After the left Moufang pattern the next step is `L` or the bottom. -/
def ChainL (s : List L3) (a : Option L3) : Prop :=
  (∃ u v b, s = [u, v] ∧ a = some b ∧ b ≠ u ∧ b ≠ v ∧ u ≠ v) ∨
  (∃ c t, s = c :: t ∧ 2 ≤ t.length ∧ Cond a c t ∧ Chain t (some c))

/-- Mirror image of `ChainL`. -/
def ChainR (s : List L3) (a : Option L3) : Prop :=
  (∃ u v b, s = [u, v] ∧ a = some b ∧ b ≠ u ∧ b ≠ v ∧ u ≠ v) ∨
  (∃ c t, s = t ++ [c] ∧ 2 ≤ t.length ∧ Cond a c t ∧ Chain t (some c))

/-- Certificates with a Moufang move. -/
inductive Cat : List L3 → Option L3 → Prop
  | passL (c : L3) (t : List L3) (a : Option L3) :
      2 ≤ t.length → Cond a c t → Cat t (some c) → Cat (c :: t) a
  | passR (c : L3) (t : List L3) (a : Option L3) :
      2 ≤ t.length → Cond a c t → Cat t (some c) → Cat (t ++ [c]) a
  | passD (p : L3) (m : List L3) (a : Option L3) :
      2 ≤ m.length → Cond a p m → Cat m (some p) → Cat (p :: (m ++ [p])) a
  /-- middle Moufang `x((BC)x) → (xB)(Cx)` at a `D` step -/
  | moveD (p : L3) (m : List L3) (a : Option L3) :
      2 ≤ m.length → Cond a p m → Chain m (some p) → Cat (p :: (m ++ [p])) a
  /-- left Moufang `x(Y(xC)) → ((xY)x)C`: peel `x`, peel `y`, next left run is `x` again -/
  | moveL (x y : L3) (t : List L3) (a : Option L3) :
      Cond a x (y :: x :: t) → Cond (some x) y (x :: t) → ChainL (x :: t) (some y) →
      Cat (x :: y :: x :: t) a
  /-- right Moufang `((Cx)Y)x → C(x(Yx))` -/
  | moveR (x y : L3) (t : List L3) (a : Option L3) :
      Cond a x (t ++ [x, y]) → Cond (some x) y (t ++ [x]) → ChainR (t ++ [x]) (some y) →
      Cat (t ++ [x, y, x]) a

/-- The excluded entries of Proposition E. -/
def Failure (s : List L3) (e : Option L3) : Prop :=
  match e with
  | none => False
  | some p =>
      (s.head? = some p ∧ s.getLast? = some p) ∨
      (s.head? = some p ∧ ¬ AllThree s.dropLast) ∨
      (s.getLast? = some p ∧ ¬ AllThree s.tail)

end Caterpillar
