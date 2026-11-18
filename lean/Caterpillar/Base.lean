import Caterpillar.Decide

/-!
# Finite base of Proposition E: run sequences with 4 and 5 runs

Every list of length `n` over `L3` occurs in `allLists n`; for `n = 4, 5` the kernel checks, by `decide`,
that `catB` finds a certificate for every valid sequence and every non-excluded entry letter.
-/

namespace Caterpillar

def allLists : Nat → List (List L3)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap fun l => [0, 1, 2].map fun c => c :: l

theorem mem_allLists : ∀ (s : List L3), s ∈ allLists s.length
  | [] => by simp [allLists]
  | c :: t => by
    simp only [allLists, List.length_cons, List.mem_flatMap, List.mem_map]
    refine ⟨t, mem_allLists t, c, ?_, rfl⟩
    match c with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp
    | ⟨2, _⟩ => simp

def entries : List (Option L3) := [none, some 0, some 1, some 2]

theorem mem_entries (e : Option L3) : e ∈ entries := by
  match e with
  | none => simp [entries]
  | some ⟨0, _⟩ => simp [entries]
  | some ⟨1, _⟩ => simp [entries]
  | some ⟨2, _⟩ => simp [entries]

def baseOK (n : Nat) : Bool :=
  (allLists n).all fun s => entries.all fun e =>
    !(decide (Valid s)) || decide (Failure s e) || catB (n + 1) s e

theorem base4 : baseOK 4 = true := by decide +kernel
theorem base5 : baseOK 5 = true := by decide +kernel

theorem cat_of_baseOK {n : Nat} (hb : baseOK n = true) (s : List L3) (e : Option L3)
    (hn : s.length = n) (hv : Valid s) (hf : ¬ Failure s e) : Cat s e := by
  unfold baseOK at hb
  rw [List.all_eq_true] at hb
  have h1 := hb s (hn ▸ mem_allLists s)
  rw [List.all_eq_true] at h1
  have h2 := h1 e (mem_entries e)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
  rcases h2 with (h | h) | h
  · exact absurd hv h
  · exact absurd h hf
  · exact catB_sound _ _ _ h

end Caterpillar
