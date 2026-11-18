import Caterpillar.Basic

/-!
# The determinant core of Lemma Cat

Laminarity (THEOREM.md, Lemma Cat) forces every rotation that could delete a node of `S` to have two
segments that are single-letter pieces `aⁱ`, `bˡ` with `a ≠ b`. The third segment is an arbitrary count
vector `v`. In any order of the three rows the determinant is `± i·l·v(third a b)`, so it is nonzero as soon
as the third letter occurs in the third segment. The bottom case reduces to the same statement (for runs
`u, v` and sibling `a` pairwise distinct, `third a u = v` and `third a v = u`).
-/

namespace Caterpillar

abbrev Vec := L3 → Int

def det3 (x y z : Vec) : Int :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

/-- the count vector of `aᵏ` -/
def ev (a : L3) (k : Int) : Vec := fun c => if c = a then k else 0

theorem det_ss_v (a b : L3) (hab : a ≠ b) (i l : Int) (v : Vec) :
    det3 (ev a i) (ev b l) v = i * l * v (third a b) ∨
    det3 (ev a i) (ev b l) v = -(i * l * v (third a b)) := by
  match a, b with
  | ⟨0,_⟩, ⟨0,_⟩ | ⟨1,_⟩, ⟨1,_⟩ | ⟨2,_⟩, ⟨2,_⟩ => exact absurd rfl hab
  | ⟨0,_⟩, ⟨1,_⟩ => left; simp [det3, ev, third, Int.mul_assoc]
  | ⟨1,_⟩, ⟨0,_⟩ => right; simp [det3, ev, third, Int.mul_assoc]
  | ⟨0,_⟩, ⟨2,_⟩ => right; simp [det3, ev, third, Int.mul_assoc]
  | ⟨2,_⟩, ⟨0,_⟩ => left; simp [det3, ev, third, Int.mul_assoc]
  | ⟨1,_⟩, ⟨2,_⟩ => left; simp [det3, ev, third, Int.mul_assoc]
  | ⟨2,_⟩, ⟨1,_⟩ => right; simp [det3, ev, third, Int.mul_assoc]

theorem det_s_v_s (a b : L3) (hab : a ≠ b) (i l : Int) (v : Vec) :
    det3 (ev a i) v (ev b l) = i * l * v (third a b) ∨
    det3 (ev a i) v (ev b l) = -(i * l * v (third a b)) := by
  match a, b with
  | ⟨0,_⟩, ⟨0,_⟩ | ⟨1,_⟩, ⟨1,_⟩ | ⟨2,_⟩, ⟨2,_⟩ => exact absurd rfl hab
  | ⟨0,_⟩, ⟨1,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨1,_⟩, ⟨0,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨0,_⟩, ⟨2,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨2,_⟩, ⟨0,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨1,_⟩, ⟨2,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨2,_⟩, ⟨1,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem det_v_s_s (a b : L3) (hab : a ≠ b) (i l : Int) (v : Vec) :
    det3 v (ev a i) (ev b l) = i * l * v (third a b) ∨
    det3 v (ev a i) (ev b l) = -(i * l * v (third a b)) := by
  match a, b with
  | ⟨0,_⟩, ⟨0,_⟩ | ⟨1,_⟩, ⟨1,_⟩ | ⟨2,_⟩, ⟨2,_⟩ => exact absurd rfl hab
  | ⟨0,_⟩, ⟨1,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨1,_⟩, ⟨0,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨0,_⟩, ⟨2,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨2,_⟩, ⟨0,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨1,_⟩, ⟨2,_⟩ => left; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  | ⟨2,_⟩, ⟨1,_⟩ => right; simp [det3, ev, third, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem ne_zero_of_pm {d x : Int} (h : d = x ∨ d = -x) (hx : x ≠ 0) : d ≠ 0 := by
  rcases h with h | h <;> omega

/-- **Rank 3.** Two single-letter segments `aⁱ, bˡ` (`a ≠ b`, `i, l ≠ 0`) and a third segment containing
the third letter give a nonzero determinant, whatever the order of the three segments. -/
theorem rank3 (a b : L3) (hab : a ≠ b) (i l : Int) (hi : i ≠ 0) (hl : l ≠ 0) (v : Vec)
    (hv : v (third a b) ≠ 0) :
    det3 (ev a i) (ev b l) v ≠ 0 ∧ det3 (ev a i) v (ev b l) ≠ 0 ∧ det3 v (ev a i) (ev b l) ≠ 0 ∧
    det3 (ev b l) (ev a i) v ≠ 0 ∧ det3 (ev b l) v (ev a i) ≠ 0 ∧ det3 v (ev b l) (ev a i) ≠ 0 := by
  have hx : i * l * v (third a b) ≠ 0 := Int.mul_ne_zero (Int.mul_ne_zero hi hl) hv
  have hba : b ≠ a := fun h => hab h.symm
  have hy : l * i * v (third b a) ≠ 0 := by
    have hsym : ∀ a b : L3, third b a = third a b := by decide
    rw [hsym a b, Int.mul_comm l i]; exact hx
  exact ⟨ne_zero_of_pm (det_ss_v a b hab i l v) hx, ne_zero_of_pm (det_s_v_s a b hab i l v) hx,
    ne_zero_of_pm (det_v_s_s a b hab i l v) hx, ne_zero_of_pm (det_ss_v b a hba l i v) hy,
    ne_zero_of_pm (det_s_v_s b a hba l i v) hy, ne_zero_of_pm (det_v_s_s b a hba l i v) hy⟩

/-- Bottom case: for `a, u, v` pairwise distinct the third letter of `(a, u)` is `v`. -/
theorem third_of_distinct : ∀ a u v : L3, a ≠ u → a ≠ v → u ≠ v → third a u = v := by decide

end Caterpillar
