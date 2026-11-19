import Caterpillar.Det

/-!
# Count vectors of segments, and laminarity of intervals

A word is a function `w : Nat → L3` (positions `0 … N-1` matter). An interval is a pair `(lo, hi)` with
`lo ≤ hi`. The count vector of an interval records the letter multiplicities.
-/

namespace Caterpillar

abbrev Word := Nat → L3
abbrev Ival := Nat × Nat

/-- multiplicity of `c` in positions `lo, …, lo + len - 1` -/
def cntR (w : Word) (c : L3) : Nat → Nat → Nat
  | _, 0 => 0
  | lo, len + 1 => (if w lo = c then 1 else 0) + cntR w c (lo + 1) len

/-- count vector of the interval `I = (lo, hi)` -/
def cnt (w : Word) (I : Ival) : Vec := fun c => (cntR w c I.1 (I.2 + 1 - I.1) : Int)

theorem cntR_split (w : Word) (c : L3) : ∀ lo l1 l2,
    cntR w c lo (l1 + l2) = cntR w c lo l1 + cntR w c (lo + l1) l2
  | lo, 0, l2 => by simp [cntR]
  | lo, l1 + 1, l2 => by
    rw [show l1 + 1 + l2 = (l1 + l2) + 1 by omega]
    simp only [cntR]
    rw [cntR_split w c (lo + 1) l1 l2, show lo + 1 + l1 = lo + (l1 + 1) by omega]
    omega

theorem cntR_const (w : Word) (a c : L3) : ∀ lo len,
    (∀ p, lo ≤ p → p < lo + len → w p = a) → cntR w c lo len = if c = a then len else 0
  | lo, 0, _ => by simp [cntR]
  | lo, len + 1, h => by
    simp only [cntR]
    rw [cntR_const w a c (lo + 1) len (fun p h1 h2 => h p (by omega) (by omega)), h lo (by omega) (by omega)]
    by_cases hc : c = a
    · subst hc; simp; omega
    · have : ¬ a = c := fun e => hc e.symm
      simp [hc, this]

theorem cntR_pos (w : Word) (c : L3) (lo len p : Nat) (h1 : lo ≤ p) (h2 : p < lo + len) (hp : w p = c) :
    1 ≤ cntR w c lo len := by
  have e : len = (p - lo) + (1 + (len - (p - lo) - 1)) := by omega
  rw [e, cntR_split, cntR_split, show lo + (p - lo) = p by omega]
  simp [cntR, hp]
  omega

theorem cntR_mono (w : Word) (c : L3) (lo len lo' len' : Nat) (h1 : lo ≤ lo') (h2 : lo' + len' ≤ lo + len) :
    cntR w c lo' len' ≤ cntR w c lo len := by
  have e : len = (lo' - lo) + (len' + (len - (lo' - lo) - len')) := by omega
  rw [e, cntR_split, cntR_split, show lo + (lo' - lo) = lo' by omega]
  omega

/-- An interval carrying a single letter `a` has count vector `ev a |I|`. -/
theorem cnt_const (w : Word) (I : Ival) (a : L3) (hI : I.1 ≤ I.2)
    (h : ∀ p, I.1 ≤ p → p ≤ I.2 → w p = a) : cnt w I = ev a ((I.2 + 1 - I.1 : Nat) : Int) := by
  funext c
  simp only [cnt, ev]
  rw [cntR_const w a c I.1 _ (fun p h1 h2 => h p h1 (by omega))]
  split <;> simp

/-- A segment containing the interval `J` contains each of its letters. -/
theorem cnt_pos_of_sub (w : Word) (I J : Ival) (c : L3) (_hJ : J.1 ≤ J.2) (hsub : I.1 ≤ J.1 ∧ J.2 ≤ I.2)
    (hc : ∃ p, J.1 ≤ p ∧ p ≤ J.2 ∧ w p = c) : cnt w I c ≠ 0 := by
  obtain ⟨p, h1, h2, hp⟩ := hc
  have := cntR_pos w c I.1 (I.2 + 1 - I.1) p (by omega) (by omega) hp
  simp only [cnt]
  omega

/-- laminar intervals: nested or disjoint -/
def Lam (X Y : Ival) : Prop :=
  (X.1 ≤ Y.1 ∧ Y.2 ≤ X.2) ∨ (Y.1 ≤ X.1 ∧ X.2 ≤ Y.2) ∨ X.2 < Y.1 ∨ Y.2 < X.1

end Caterpillar
