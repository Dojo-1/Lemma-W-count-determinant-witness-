import Caterpillar.G2

/-!
# Proposition S: the decoding step

Words in `x, z` are `List Bool` (`true = x`, `false = z`). For a word `ω`, `prof ω α` counts the `z`'s
of `ω` preceded by exactly `α` `x`'s, and `lead ω` counts the `x`'s preceded by no `z`.

By Lemma M, the `t`-linear moments of a bracketing of `xᵃyᵇzᶜ` with invariant `Φ = (j, a′, c′, W)`
determine the weighted profile `N = j·prof ω₊ + (b−j)·prof ω₋`, and the `s`-linear moments determine
`M(0) = j·lead ω₊ + (b−j)·lead ω₋`, where `ω₊ = x^{a′} z^{c′} W` and `ω₋ = z^{c′} x^{a′} W`.

* `prof_inj`: a word is fixed by its `z`-profile and its number of `x`'s.
* `propS_interior`: for `0 < j < b`, `(N, M(0))` determines `Φ`.
* `propS_boundary`: for `j = 0` (resp. `j = b`), `N` determines `ω₋` (resp. `ω₊`), the join word.
* `propS_kind`: `M(0) > 0 ↔ j > 0` and `N(0) > 0 ↔ j < b`, so the profiles also tell the cases apart.
-/

namespace PropS

def prof : List Bool → Nat → Nat
  | [], _ => 0
  | true :: _, 0 => 0
  | true :: ω, α + 1 => prof ω α
  | false :: ω, α => (if α = 0 then 1 else 0) + prof ω α

def nx : List Bool → Nat
  | [] => 0
  | true :: ω => nx ω + 1
  | false :: ω => nx ω

def lead : List Bool → Nat
  | true :: ω => lead ω + 1
  | _ => 0

/-- **A binary word is fixed by its `z`-profile and its number of `x`'s.** -/
theorem prof_inj : ∀ ω ω' : List Bool, nx ω = nx ω' → (∀ α, prof ω α = prof ω' α) → ω = ω'
  | [], [], _, _ => rfl
  | [], true :: _, h, _ => by simp [nx] at h
  | [], false :: _, _, h => by have := h 0; simp [prof] at this <;> omega
  | true :: _, [], h, _ => by simp [nx] at h
  | false :: _, [], _, h => by have := h 0; simp [prof] at this <;> omega
  | true :: _, false :: _, _, h => by have := h 0; simp [prof] at this <;> omega
  | false :: _, true :: _, _, h => by have := h 0; simp [prof] at this <;> omega
  | true :: r, true :: r', hn, h => by
    simp only [nx] at hn
    rw [prof_inj r r' (by omega) (fun α => h (α + 1))]
  | false :: r, false :: r', hn, h => by
    simp only [nx] at hn
    rw [prof_inj r r' hn (fun α => by have := h α; simp only [prof] at this; omega)]

theorem prof_x (W : List Bool) (α : Nat) : prof (true :: W) α = if α = 0 then 0 else prof W (α - 1) := by
  cases α <;> simp [prof]

theorem prof_xs (W : List Bool) : ∀ a α, prof (List.replicate a true ++ W) α = if a ≤ α then prof W (α - a) else 0
  | 0, α => by simp
  | a + 1, α => by
    simp only [List.replicate_succ, List.cons_append, prof_x, prof_xs W a]
    by_cases h : α = 0
    · simp [h]
    · simp only [h, ite_false]
      by_cases h2 : a ≤ α - 1
      · rw [ite_eq_left h2, ite_eq_left (by omega)]; congr 1; omega
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem prof_zs (W : List Bool) : ∀ c α, prof (List.replicate c false ++ W) α = (if α = 0 then c else 0) + prof W α
  | 0, α => by simp
  | c + 1, α => by
    show prof (false :: (List.replicate c false ++ W)) α = _
    rw [prof, prof_zs W c]
    split <;> omega

def ωp (a c : Nat) (W : List Bool) : List Bool := List.replicate a true ++ (List.replicate c false ++ W)
def ωm (a c : Nat) (W : List Bool) : List Bool := List.replicate c false ++ (List.replicate a true ++ W)

/-- the `t`-linear profile from Lemma M -/
def N (b j a c : Nat) (W : List Bool) (α : Nat) : Nat := j * prof (ωp a c W) α + (b - j) * prof (ωm a c W) α
/-- the `s`-linear moment at `γ = 0` from Lemma M -/
def M0 (b j a c : Nat) (W : List Bool) : Nat := j * lead (ωp a c W) + (b - j) * lead (ωm a c W)

theorem lead_xs (W : List Bool) (c : Nat) (hc : 1 ≤ c) : ∀ a, lead (List.replicate a true ++ (List.replicate c false ++ W)) = a
  | 0 => by obtain ⟨c, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩; simp [List.replicate_succ, lead]
  | a + 1 => by
    show lead (true :: (List.replicate a true ++ (List.replicate c false ++ W))) = a + 1
    rw [lead, lead_xs W c hc a]

theorem lead_zs (V : List Bool) (c : Nat) (hc : 1 ≤ c) : lead (List.replicate c false ++ V) = 0 := by
  obtain ⟨c, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩; simp [List.replicate_succ, lead]

theorem jb_mul (b j p : Nat) (hj : j ≤ b) : j * p + (b - j) * p = b * p := by
  rw [← Nat.add_mul]; congr 1; omega

theorem N_at0 (b j a c : Nat) (W : List Bool) (ha : 1 ≤ a) : N b j a c W 0 = (b - j) * c := by
  simp only [N, ωp, ωm, prof_xs, prof_zs]
  simp [show ¬ a ≤ 0 by omega]

theorem N_below (b j a c : Nat) (W : List Bool) (α : Nat) (h0 : 0 < α) (h1 : α < a) : N b j a c W α = 0 := by
  simp only [N, ωp, ωm, prof_xs, prof_zs]
  simp [show ¬ a ≤ α by omega, show α ≠ 0 by omega]

theorem N_ata (b j a c : Nat) (W : List Bool) (hj : j ≤ b) (ha : 1 ≤ a) :
    N b j a c W a = b * prof W 0 + j * c := by
  simp only [N, ωp, ωm, prof_xs, prof_zs]
  simp only [Nat.le_refl, ite_true, Nat.sub_self, show a ≠ 0 by omega, ite_false, Nat.zero_add, Nat.mul_add]
  have := jb_mul b j (prof W 0) hj; omega

theorem N_above (b j a c : Nat) (W : List Bool) (hj : j ≤ b) (β : Nat) (hβ : 0 < β) :
    N b j a c W (a + β) = b * prof W β := by
  simp only [N, ωp, ωm, prof_xs, prof_zs]
  simp only [show a ≤ a + β by omega, ite_true, Nat.add_sub_cancel_left, show a + β ≠ 0 by omega, ite_false,
    Nat.zero_add, show β ≠ 0 by omega]
  exact jb_mul b j _ hj

theorem M0_eq (b j a c : Nat) (W : List Bool) (hc : 1 ≤ c) : M0 b j a c W = j * a := by
  simp only [M0, ωp, ωm, lead_xs W c hc, lead_zs _ c hc]; simp

/-- the profiles tell interior and boundary components apart -/
theorem propS_kind (b j a c : Nat) (W : List Bool) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    (0 < M0 b j a c W ↔ 0 < j) ∧ (0 < N b j a c W 0 ↔ j < b) := by
  rw [M0_eq b j a c W hc, N_at0 b j a c W ha]
  constructor
  · constructor
    · intro h; rcases Nat.eq_zero_or_pos j with e | e
      · subst e; simp at h
      · exact e
    · intro h; exact Nat.mul_pos h ha
  · constructor
    · intro h
      rcases Nat.lt_or_ge j b with e | e
      · exact e
      · have : b - j = 0 := by omega
        rw [this] at h; simp at h
    · intro h; exact Nat.mul_pos (by omega) hc

/-- **Proposition S, interior components.** For `0 < j < b`, the profile `N` and the moment `M(0)`
determine `Φ = (j, a′, c′, W)` (among invariants of the same word `xᵃyᵇzᶜ`). -/
theorem propS_interior (b j a c j' a' c' : Nat) (W W' : List Bool)
    (hj : 0 < j ∧ j < b) (hj' : 0 < j' ∧ j' < b) (ha : 1 ≤ a) (hc : 1 ≤ c) (ha' : 1 ≤ a') (hc' : 1 ≤ c')
    (hx : a + nx W = a' + nx W')
    (hN : ∀ α, N b j a c W α = N b j' a' c' W' α) (hM : M0 b j a c W = M0 b j' a' c' W') :
    j = j' ∧ a = a' ∧ c = c' ∧ W = W' := by
  rw [M0_eq _ _ _ _ _ hc, M0_eq _ _ _ _ _ hc'] at hM
  -- `a′` is the least positive index where `N` is nonzero
  have haa : a = a' := by
    rcases Nat.lt_trichotomy a a' with h | h | h
    · exfalso
      have h1 := hN a
      rw [N_ata b j a c W (by omega) ha, N_below b j' a' c' W' a (by omega) h] at h1
      have := Nat.mul_pos hj.1 hc; omega
    · exact h
    · exfalso
      have h1 := hN a'
      rw [N_ata b j' a' c' W' (by omega) ha', N_below b j a c W a' (by omega) h] at h1
      have := Nat.mul_pos hj'.1 hc'; omega
  subst haa
  have hjj : j = j' := Nat.eq_of_mul_eq_mul_right (by omega) hM
  subst hjj
  have hcc : c = c' := by
    have h1 := hN 0
    rw [N_at0 b j a c W ha, N_at0 b j a c' W' ha] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  subst hcc
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply prof_inj W W' (by omega)
  intro β
  rcases Nat.eq_zero_or_pos β with hβ | hβ
  · subst hβ
    have h1 := hN a
    rw [N_ata b j a c W (by omega) ha, N_ata b j a c W' (by omega) ha] at h1
    exact Nat.eq_of_mul_eq_mul_left (show 0 < b by omega) (show b * prof W 0 = b * prof W' 0 by omega)
  · have h1 := hN (a + β)
    rw [N_above b j a c W (by omega) β hβ, N_above b j a c W' (by omega) β hβ] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1

/-- **Proposition S, boundary components.** For `j = 0` the profile is `b·prof ω₋`, for `j = b` it is
`b·prof ω₊`; either way it fixes the join word (`ω₋`, resp. `ω₊`), the complete invariant. -/
theorem propS_boundary (b : Nat) (hb : 0 < b) (ω ω' : List Bool) (hx : nx ω = nx ω')
    (hN : ∀ α, b * prof ω α = b * prof ω' α) : ω = ω' :=
  prof_inj ω ω' hx (fun α => Nat.eq_of_mul_eq_mul_left hb (hN α))

theorem N_boundary0 (b a c : Nat) (W : List Bool) (α : Nat) : N b 0 a c W α = b * prof (ωm a c W) α := by
  simp [N]

theorem N_boundaryb (b a c : Nat) (W : List Bool) (α : Nat) : N b b a c W α = b * prof (ωp a c W) α := by
  simp [N]

end PropS
