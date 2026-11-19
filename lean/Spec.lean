/-!
# Trusted Specification (`Spec`)

Pure, proof-free definitions for the flip-connectivity theorem on octonion bracketing classes,
its Bell-number count, canonical word representatives, and Lemma W over `ℤ`.

This file imports nothing outside Lean's core `Init` prelude and contains **no proofs and no tactics**.
Both `Challenge.lean` (statements of record) and `Solution.lean` (verified proofs) import this module,
so `lake comparator --paranoid` guarantees exact definitional identity across every declaration
referenced by the target theorem types.
-/

namespace Spec

/-! ## 1. Integer octonions (`O := Fin 8 → Int`) -/

abbrev O := Fin 8 → Int

/-- Cayley–Dickson sign table (`eᵢ eⱼ = sgn(i, j) e_{i ⊕ j}`). -/
def sgnT : List (List Int) :=
  [[ 1,  1,  1,  1,  1,  1,  1,  1],
   [ 1, -1,  1, -1,  1, -1, -1,  1],
   [ 1, -1, -1,  1,  1,  1, -1, -1],
   [ 1,  1, -1, -1,  1, -1,  1, -1],
   [ 1, -1, -1, -1, -1,  1,  1,  1],
   [ 1,  1, -1,  1, -1, -1, -1,  1],
   [ 1,  1,  1, -1, -1,  1, -1, -1],
   [ 1, -1,  1,  1, -1, -1,  1, -1]]

def sgn (i j : Fin 8) : Int := (sgnT.getD i.val []).getD j.val 0

/-- Bitwise XOR on `Fin 8`. -/
def xr (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (Nat.zero_lt_succ 7)⟩

def sum8 (f : Fin 8 → Int) : Int :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7

/-- Octonion product `(ab)_k = Σᵢ sgn(i, i ⊕ k) aᵢ b_{i ⊕ k}`. -/
def mul (a b : O) : O := fun k => sum8 fun i => sgn i (xr i k) * a i * b (xr i k)

def unit (i : Fin 8) : O := fun j => if j = i then 1 else 0
def zero : O := fun _ => 0
def one : O := unit 0
def sub (a b : O) : O := fun k => a k - b k

/-- Associator `[a, b, c] = (ab)c − a(bc)`. -/
def assoc (a b c : O) : O := sub (mul (mul a b) c) (mul a (mul b c))

/-- Squared Euclidean norm `N(a) = Σᵢ aᵢ²`. -/
def nrm (a : O) : Int := sum8 fun i => a i * a i

/-! ## 2. Bracketings, evaluation, local flips, and kernel classes -/

/-- Planar binary trees whose leaves carry word positions. -/
inductive Tree
  | leaf (i : Nat)
  | node (l r : Tree)

/-- Leaf positions from left to right. -/
def lv : Tree → List Nat
  | .leaf i => [i]
  | .node l r => lv l ++ lv r

/-- Value of a bracketing when letter `w i` is substituted by `ρ (w i)`. -/
def ev (w : Nat → Nat) (ρ : Nat → O) : Tree → O
  | .leaf i => ρ (w i)
  | .node l r => mul (ev w ρ l) (ev w ρ r)

/-- Single-hole tree context. -/
inductive Ctx
  | hole
  | inL (c : Ctx) (r : Tree)
  | inR (l : Tree) (c : Ctx)

def fill : Ctx → Tree → Tree
  | .hole, S => S
  | .inL c r, S => .node (fill c S) r
  | .inR l c, S => .node l (fill c S)

/-- A single associahedron edge (reassociation flip `(AB)C ↔ A(BC)` in any context). -/
inductive FlipStep : Tree → Tree → Prop
  | fwd (c : Ctx) (A B C : Tree) :
      FlipStep (fill c (.node (.node A B) C)) (fill c (.node A (.node B C)))
  | bwd (c : Ctx) (A B C : Tree) :
      FlipStep (fill c (.node A (.node B C))) (fill c (.node (.node A B) C))

/-- A flip that stays inside the same kernel class (preserves the octonion map). -/
def KerFlip (w : Nat → Nat) (T U : Tree) : Prop :=
  FlipStep T U ∧ ∀ ρ : Nat → O, ev w ρ T = ev w ρ U

/-- Reflexive–transitive closure of a relation on trees. -/
inductive DReach (R : Tree → Tree → Prop) : Tree → Tree → Prop
  | refl (T : Tree) : DReach R T T
  | tail {T U V : Tree} : DReach R T U → R U V → DReach R T V

/-! ## 3. Words, flip-connectivity, and the characterization predicates -/

def wd (wl : List Nat) (p : Nat) : Nat := wl.getD p 0

/-- Every letter occupies a single contiguous run. -/
def Interval (wl : List Nat) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → k < wl.length → wd wl i = wd wl k → wd wl j = wd wl i

/-- The word uses at most two distinct letters. -/
def TwoLetters (wl : List Nat) : Prop :=
  ∃ a c, ∀ x ∈ wl, x = a ∨ x = c

/-- Every kernel class of bracketings of `0, …, n − 1` is connected by map-preserving flips. -/
def KerConn (w : Nat → Nat) (n : Nat) : Prop :=
  ∀ T T' : Tree, lv T = List.range n → lv T' = List.range n →
    (∀ ρ : Nat → O, ev w ρ T = ev w ρ T') → DReach (KerFlip w) T T'

/-! ## 4. Count matrices, `3 × 3` minors, and `D_N`-flips (Lemma W) -/

/-- Multiplicity of letter `ℓ` in the leaves of `T`. -/
def cnt (w : Nat → Nat) (ℓ : Nat) : Tree → Int
  | .leaf i => if w i = ℓ then 1 else 0
  | .node l r => cnt w ℓ l + cnt w ℓ r

/-- `3 × 3` minor of the letter-count matrix of `(A, B, C)` on letters `(p, q, r)`. -/
def minor (w : Nat → Nat) (A B C : Tree) (p q r : Nat) : Int :=
  cnt w p A * (cnt w q B * cnt w r C - cnt w r B * cnt w q C)
  - cnt w q A * (cnt w p B * cnt w r C - cnt w r B * cnt w p C)
  + cnt w r A * (cnt w p B * cnt w q C - cnt w q B * cnt w p C)

/-- Rank ≤ 2 condition: all `3 × 3` count minors vanish. -/
def DN (w : Nat → Nat) (A B C : Tree) : Prop :=
  ∀ p q r, minor w A B C p q r = 0

/-- A flip whose local count matrix has rank ≤ 2. -/
inductive DNStep (w : Nat → Nat) : Tree → Tree → Prop
  | fwd (c : Ctx) (A B C : Tree) : DN w A B C →
      DNStep w (fill c (.node (.node A B) C)) (fill c (.node A (.node B C)))
  | bwd (c : Ctx) (A B C : Tree) : DN w A B C →
      DNStep w (fill c (.node A (.node B C))) (fill c (.node (.node A B) C))

/-! ## 5. Canonical words (restricted growth strings), Bell and Stirling numbers -/

/-- One more than the largest letter occurring in `w` (`0` for `[]`). -/
def nl (w : List Nat) : Nat := w.foldr (fun x m => max (x + 1) m) 0

/-- One-letter extensions of a restricted growth string. -/
def ext (w : List Nat) : List (List Nat) :=
  (List.range (nl w + 1)).map (fun c => w ++ [c])

/-- Restricted growth strings of length `n`: one canonical word per set partition. -/
def rgs : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (rgs n).flatMap ext

/-- `n`-th Bell number (number of restricted growth strings of length `n`). -/
def bell (n : Nat) : Nat := (rgs n).length

/-- `v` is obtained from `w` by an injective renaming of its letters. -/
def Renaming (w v : List Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ x ∈ w, ∀ y ∈ w, f x = f y → x = y) ∧ v = w.map f

/-- Stirling number of the second kind `S(n, k)`: canonical words of length `n` using `k` letters. -/
def stirling (n k : Nat) : Nat := (rgs n).countP (fun w => decide (nl w = k))

/-- Partial sum `Σ_{k < N} f k`. -/
def ssum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => ssum f N + f N

end Spec
