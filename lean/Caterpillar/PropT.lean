import Caterpillar.PropCF

/-!
# Proposition T: the classification of `D_N`-components of `xᵃyᵇzᶜ`

Positions `0 … n−1`, `n = a + b + c`; `x` on `[0, a)`, `y` on `[a, a+b)`, `z` on `[a+b, n)` (`w3`).
Bracketings are `WF` trees (consecutive leaves).

* `core`: the lowest node `K = (U, V)` containing the last `x` and the first `z`, and the word `W` of
  attached blocks read from `K` outward (`true = x`, `false = z`). `Φ = (j, a′, c′, W)` with
  `a′ = a − U.lo`, `j = U.hi + 1 − a`, `c′ = V.hi + 1 − (a+b)`; `ω₊ = x^{a′} z^{c′} W`, `ω₋ = z^{c′} x^{a′} W`.
* `key`: `Φ` for interior `j`, the join word `ω₋` (`j = 0`) or `ω₊` (`j = b`) otherwise.
* `sh_sub`: the shape of `(x_p, y_q, z_r)` is `((xy)z)` iff `p` lies in the child of `lca(q, r)` that
  contains `q`; so σ is the function `cx(q, r)` = number of `x`'s in that child (`sig_iff_cx`).
* `cx_omega`: `cx(q, r)` = number of `x`'s before the `(r − a − b)`-th `z` of `ω_q`, where `ω_q = ω₊` if
  `y_q` lies in `U` and `ω₋` otherwise (the absorption word of `y_q`).
* `key_iff_cx`: `key T = key T' ⟺ cx_T = cx_T'`.
* **`propT`**: `T ∼_D T' ⟺ key T = key T'`. So the invariant is constant on `D_N`-components and
  separates them.
-/

namespace PropT
open Caterpillar (Tree)
open Octonion

variable (a b c : Nat)

def w3 (i : Nat) : Nat := if i < a then 0 else if i < a + b then 1 else 2

theorem w3_mono : MonoW (w3 a b) := by
  intro i j h; simp only [w3]; split <;> split <;> (try split) <;> (try split) <;> omega

/-! ## consecutive trees -/

theorem lv_wf : ∀ T : Tree, T.WF → lv T = List.range' T.lo (T.hi + 1 - T.lo)
  | .leaf i, _ => by simp only [lv, Tree.lo, Tree.hi]; rw [show i + 1 - i = 1 by omega]; rfl
  | .node L R, ⟨hL, hR, e⟩ => by
    have h1 := Tree.lo_le_hi L hL; have h2 := Tree.lo_le_hi R hR
    simp only [lv, lv_wf L hL, lv_wf R hR, Tree.lo, Tree.hi]
    rw [e]
    obtain ⟨m1, hm1⟩ : ∃ m, L.hi + 1 - L.lo = m := ⟨_, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m, R.hi + 1 - (L.hi + 1) = m := ⟨_, rfl⟩
    have h3 : R.hi + 1 - L.lo = m2 + m1 := by omega
    have h4 : L.hi + 1 = L.lo + m1 := by omega
    rw [hm1, hm2, h3, h4, List.range'_append_1]

theorem mem_wf (T : Tree) (h : T.WF) (i : Nat) : i ∈ lv T ↔ T.lo ≤ i ∧ i ≤ T.hi := by
  have := Tree.lo_le_hi T h
  rw [lv_wf T h, List.mem_range'_1]; omega

theorem pw_wf (T : Tree) (h : T.WF) : (lv T).Pairwise (· < ·) := by
  rw [lv_wf T h]; exact List.pairwise_lt_range' _ _

/-! ## shapes through the lowest common ancestor -/

/-- the child of `lca(q, r)` that contains `q` (for `q < r` in the tree) -/
def sub (q r : Nat) : Tree → Tree
  | .leaf i => .leaf i
  | .node L R => if r ≤ L.hi then sub q r L else if R.lo ≤ q then sub q r R else L

theorem sub_lo (q r : Nat) : ∀ T : Tree, T.WF → T.lo ≤ (sub q r T).lo
  | .leaf _, _ => Nat.le_refl _
  | .node L R, ⟨hL, hR, e⟩ => by
    have := Tree.lo_le_hi L hL
    simp only [sub]
    split
    · exact sub_lo q r L hL
    · split
      · have := sub_lo q r R hR; simp only [Tree.lo] at *; omega
      · exact Nat.le_refl _

theorem sub_mem (q r : Nat) : ∀ T : Tree, T.WF → T.lo ≤ q → q < r → r ≤ T.hi →
    (sub q r T).lo ≤ q ∧ q ≤ (sub q r T).hi ∧ (sub q r T).WF
  | .leaf i, _, h1, h2, h3 => by simp [Tree.lo, Tree.hi] at *; omega
  | .node L R, ⟨hL, hR, e⟩, h1, h2, h3 => by
    have := Tree.lo_le_hi L hL; have := Tree.lo_le_hi R hR
    simp only [sub, Tree.lo, Tree.hi] at *
    split
    · exact sub_mem q r L hL h1 h2 (by omega)
    · split
      · exact sub_mem q r R hR (by omega) h2 h3
      · exact ⟨h1, by omega, hL⟩

/-- **the shape of `(p, q, r)` is `((pq)r)` iff `p` lies in the `q`-child of `lca(q, r)`** -/
theorem sh_sub (p q r : Nat) : ∀ T : Tree, T.WF → T.lo ≤ p → p < q → q < r → r ≤ T.hi →
    sh T p q r = decide ((sub q r T).lo ≤ p)
  | .leaf i, _, h1, h2, h3, h4 => by simp [Tree.lo, Tree.hi] at *; omega
  | .node L R, ⟨hL, hR, e⟩, h1, h2, h3, h4 => by
    have := Tree.lo_le_hi L hL; have := Tree.lo_le_hi R hR
    simp only [Tree.lo, Tree.hi] at h1 h4
    by_cases hr : r ≤ L.hi
    · have hs : sub q r (.node L R) = sub q r L := by simp [sub, hr]
      simp only [hs]; rw [sh_L L R p q r ((mem_wf L hL r).2 ⟨by omega, hr⟩)]
      exact sh_sub p q r L hL h1 h2 h3 hr
    · have hrL : r ∉ lv L := fun h => hr ((mem_wf L hL r).1 h).2
      by_cases hp : R.lo ≤ p
      · have hs : sub q r (.node L R) = sub q r R := by simp only [sub, if_neg hr]; rw [if_pos (by omega)]
        simp only [hs]; rw [sh_R L R p q r hrL ((mem_wf R hR p).2 ⟨hp, by omega⟩)]
        exact sh_sub p q r R hR hp h2 h3 h4
      · have hpR : p ∉ lv R := fun h => hp ((mem_wf R hR p).1 h).1
        rw [sh_M L R p q r hrL hpR]
        by_cases hq : R.lo ≤ q
        · have hs : sub q r (.node L R) = sub q r R := by simp only [sub, if_neg hr]; rw [if_pos hq]
          simp only [hs]
          have := sub_lo q r R hR
          have hq' : q ∉ lv L := fun h => by have := ((mem_wf L hL q).1 h).2; omega
          simp only [hq', decide_false]; symm; simp only [decide_eq_false_iff_not]; omega
        · have hs : sub q r (.node L R) = L := by simp only [sub, if_neg hr]; rw [if_neg hq]
          simp only [hs]
          have hq' : q ∈ lv L := (mem_wf L hL q).2 ⟨by omega, by omega⟩
          simp only [hq', decide_true]; symm; simp only [decide_eq_true_eq]; omega

/-- number of `x`'s in the `q`-child of `lca(q, r)` -/
def cx (T : Tree) (q r : Nat) : Nat := a - (sub q r T).lo

/-- a three-block bracketing: consecutive leaves `0 … n−1` -/
structure TB (T : Tree) : Prop where
  wf : T.WF
  lo : T.lo = 0
  hi : T.hi + 1 = a + b + c

/-- **σ is the function `cx`.** -/
theorem sig_iff_cx (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T T' : Tree) (h : TB a b c T) (h' : TB a b c T') :
    SigEq (w3 a b) T T' ↔ ∀ q r, a ≤ q → q < a + b → a + b ≤ r → r < a + b + c → cx a T q r = cx a T' q r := by
  have shx : ∀ U : Tree, TB a b c U → ∀ p q r, p < a → a ≤ q → q < a + b → a + b ≤ r → r < a + b + c →
      sh U p q r = decide (a - cx a U q r ≤ p) := by
    intro U hU p q r hp hq1 hq2 hr1 hr2
    rw [sh_sub p q r U hU.wf (by rw [hU.lo]; omega) (by omega) (by omega) (by have := hU.hi; omega)]
    simp only [cx]; congr 1; apply propext; omega
  constructor
  · intro hs q r hq1 hq2 hr1 hr2
    have l1 := sub_lo q r T h.wf; have l2 := sub_lo q r T' h'.wf
    have m1 := sub_mem q r T h.wf (by rw [h.lo]; omega) (by omega) (by have := h.hi; omega)
    have m2 := sub_mem q r T' h'.wf (by rw [h'.lo]; omega) (by omega) (by have := h'.hi; omega)
    simp only [cx]
    apply Classical.byContradiction; intro hne
    -- a witness `p` between the two thresholds
    have key : ∀ p, p < a → sh T p q r = sh T' p q r := by
      intro p hp
      apply hs p q r ((mem_wf T h.wf p).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩)
        ((mem_wf T h.wf q).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩)
        ((mem_wf T h.wf r).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩) (by omega) (by omega)
      simp only [Distinct, w3]; split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
    have e1 := shx T h; have e2 := shx T' h'
    simp only [cx] at e1 e2
    rcases Nat.lt_or_ge (sub q r T).lo (sub q r T').lo with hl | hl
    · have hp : (sub q r T).lo < a := by omega
      have := key (sub q r T).lo hp
      rw [e1 _ q r hp hq1 hq2 hr1 hr2, e2 _ q r hp hq1 hq2 hr1 hr2] at this
      simp only [decide_eq_decide] at this; omega
    · have hl' : (sub q r T').lo < (sub q r T).lo := by omega
      have hp : (sub q r T').lo < a := by omega
      have := key (sub q r T').lo hp
      rw [e1 _ q r hp hq1 hq2 hr1 hr2, e2 _ q r hp hq1 hq2 hr1 hr2] at this
      simp only [decide_eq_decide] at this; omega
  · intro hcx p q r hp hq hr h1 h2 hd
    have hp' := (mem_wf T h.wf p).1 hp; have hq' := (mem_wf T h.wf q).1 hq; have hr' := (mem_wf T h.wf r).1 hr
    have := h.hi; rw [h.lo] at hp' hq' hr'
    have hx : p < a ∧ a ≤ q ∧ q < a + b ∧ a + b ≤ r := by
      simp only [Distinct, w3] at hd
      split at hd <;> split at hd <;> (try split at hd) <;> (try split at hd) <;> (try split at hd) <;>
        (try split at hd) <;> omega
    rw [shx T h p q r hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 (by omega), shx T' h' p q r hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 (by omega),
      hcx q r hx.2.1 hx.2.2.1 hx.2.2.2 (by omega)]

/-! ## the invariant `Φ` -/

/-- core `(U, V)` and attachment word `W` (core outward; `true = x`, `false = z`) -/
def core : Tree → Tree × Tree × List Bool
  | .leaf i => (.leaf i, .leaf i, [])
  | .node L R =>
    if a + b ≤ L.hi then
      ((core L).1, (core L).2.1, (core L).2.2 ++ List.replicate (R.hi + 1 - R.lo) false)
    else if R.lo + 1 ≤ a then
      ((core R).1, (core R).2.1, (core R).2.2 ++ List.replicate (L.hi + 1 - L.lo) true)
    else (L, R, [])

def U (T : Tree) : Tree := (core a b T).1
def V (T : Tree) : Tree := (core a b T).2.1
def W (T : Tree) : List Bool := (core a b T).2.2
def a' (T : Tree) : Nat := a - (U a b T).lo
def j (T : Tree) : Nat := (U a b T).hi + 1 - a
def c' (T : Tree) : Nat := (V a b T).hi + 1 - (a + b)
def ωp (T : Tree) : List Bool := List.replicate (a' a b T) true ++ List.replicate (c' a b T) false ++ W a b T
def ωm (T : Tree) : List Bool := List.replicate (c' a b T) false ++ List.replicate (a' a b T) true ++ W a b T

/-- the absorption word of `y_q` -/
def ωq (T : Tree) (q : Nat) : List Bool := if q ≤ (U a b T).hi then ωp a b T else ωm a b T

inductive Key
  | inner (j a' c' : Nat) (W : List Bool)
  | join (ω : List Bool)
  deriving DecidableEq

/-- the absorption word of `y_q` read off a key -/
def fam (k : Key) (q : Nat) : List Bool :=
  match k with
  | .join ω => ω
  | .inner j a' c' W => if q < a + j then List.replicate a' true ++ List.replicate c' false ++ W
      else List.replicate c' false ++ List.replicate a' true ++ W

/-- the complete invariant of Proposition T -/
def key (T : Tree) : Key :=
  if j a b T = 0 then .join (ωm a b T) else if j a b T = b then .join (ωp a b T)
  else .inner (j a b T) (a' a b T) (c' a b T) (W a b T)

/-- a subtree containing the last `x` and the first `z` -/
structure Good (T : Tree) : Prop where
  wf : T.WF
  lo : T.lo + 1 ≤ a
  hi : a + b ≤ T.hi

structure CoreFacts (T : Tree) : Prop where
  uwf : (U a b T).WF
  vwf : (V a b T).WF
  uv : (V a b T).lo = (U a b T).hi + 1
  ulo : (U a b T).lo + 1 ≤ a
  uhi : a ≤ (U a b T).hi + 1
  uhi' : (U a b T).hi < a + b
  vhi : a + b ≤ (V a b T).hi
  tlo : T.lo ≤ (U a b T).lo
  thi : (V a b T).hi ≤ T.hi
  wt : (W a b T).count true = (U a b T).lo - T.lo
  wf' : (W a b T).count false = T.hi - (V a b T).hi

theorem core_facts (hb : 1 ≤ b) : ∀ T : Tree, Good a b T → CoreFacts a b T
  | .leaf i, h => by have := h.lo; have := h.hi; simp [Tree.lo, Tree.hi] at *; omega
  | .node L R, ⟨⟨hL, hR, e⟩, hlo, hhi⟩ => by
    have := Tree.lo_le_hi L hL; have := Tree.lo_le_hi R hR
    simp only [Tree.lo, Tree.hi] at hlo hhi
    by_cases h1 : a + b ≤ L.hi
    · have f := core_facts hb L ⟨hL, hlo, h1⟩
      have eU : U a b (.node L R) = U a b L := by simp [U, core, h1]
      have eV : V a b (.node L R) = V a b L := by simp [V, core, h1]
      have eW : W a b (.node L R) = W a b L ++ List.replicate (R.hi + 1 - R.lo) false := by simp [W, core, h1]
      have := f.wt; have := f.wf'; have := f.thi; have := f.tlo
      refine ⟨by rw [eU]; exact f.uwf, by rw [eV]; exact f.vwf, by rw [eU, eV]; exact f.uv, by rw [eU]; exact f.ulo, by rw [eU]; exact f.uhi,
        by rw [eU]; exact f.uhi', by rw [eV]; exact f.vhi, by rw [eU]; exact f.tlo, by rw [eV]; simp only [Tree.hi]; omega,
        by rw [eW, eU]; simp [List.count_replicate, Tree.lo]; omega,
        by rw [eW, eV]; simp [List.count_replicate, Tree.hi]; omega⟩
    · by_cases h2 : R.lo + 1 ≤ a
      · have f := core_facts hb R ⟨hR, h2, hhi⟩
        have eU : U a b (.node L R) = U a b R := by simp [U, core, h1, h2]
        have eV : V a b (.node L R) = V a b R := by simp [V, core, h1, h2]
        have eW : W a b (.node L R) = W a b R ++ List.replicate (L.hi + 1 - L.lo) true := by simp [W, core, h1, h2]
        have := f.wt; have := f.wf'; have := f.thi; have := f.tlo
        refine ⟨by rw [eU]; exact f.uwf, by rw [eV]; exact f.vwf, by rw [eU, eV]; exact f.uv, by rw [eU]; exact f.ulo, by rw [eU]; exact f.uhi,
          by rw [eU]; exact f.uhi', by rw [eV]; exact f.vhi, by rw [eU]; simp only [Tree.lo]; omega,
          by rw [eV]; exact f.thi,
          by rw [eW, eU]; simp [List.count_replicate, Tree.lo]; omega,
          by rw [eW, eV]; simp [List.count_replicate, Tree.hi]; omega⟩
      · have eU : U a b (.node L R) = L := by simp [U, core, h1, h2]
        have eV : V a b (.node L R) = R := by simp [V, core, h1, h2]
        have eW : W a b (.node L R) = [] := by simp [W, core, h1, h2]
        refine ⟨by rw [eU]; exact hL, by rw [eV]; exact hR, by rw [eU, eV]; exact e, by rw [eU]; omega, by rw [eU]; omega, by rw [eU]; omega,
          by rw [eV]; omega, by rw [eU]; simp [Tree.lo], by rw [eV]; simp [Tree.hi], by rw [eW, eU]; simp [Tree.lo],
          by rw [eW, eV]; simp [Tree.hi]⟩

/-! ## `cx` from the absorption words -/

/-- number of `true`s before the `t`-th `false` -/
def xb : List Bool → Nat → Nat
  | [], _ => 0
  | true :: ω, t => xb ω t + 1
  | false :: _, 0 => 0
  | false :: ω, t + 1 => xb ω t

theorem xb_t (ω : List Bool) (t : Nat) : xb (true :: ω) t = xb ω t + 1 := rfl
theorem xb_f0 (ω : List Bool) : xb (false :: ω) 0 = 0 := rfl
theorem xb_fs (ω : List Bool) (t : Nat) : xb (false :: ω) (t + 1) = xb ω t := rfl

theorem xb_app_lt : ∀ (ω τ : List Bool) (t : Nat), t < ω.count false → xb (ω ++ τ) t = xb ω t
  | [], _, _, h => by simp at h
  | true :: ω, τ, t, h => by rw [List.cons_append, xb_t, xb_t, xb_app_lt ω τ t (by simpa using h)]
  | false :: ω, τ, 0, _ => rfl
  | false :: ω, τ, t + 1, h => by
    rw [List.cons_append, xb_fs, xb_fs]; exact xb_app_lt ω τ t (by simp at h; omega)

theorem xb_rep_true (m : Nat) : ∀ (ω : List Bool) (t : Nat), xb (List.replicate m true ++ ω) t = m + xb ω t := by
  induction m with
  | zero => intro ω t; simp
  | succ m ih => intro ω t; rw [List.replicate_succ, List.cons_append, xb_t, ih]; omega

theorem xb_rep_false (m : Nat) : ∀ (ω : List Bool) (t : Nat), t < m → xb (List.replicate m false ++ ω) t = 0 := by
  induction m with
  | zero => intro ω t h; omega
  | succ m ih =>
    intro ω t h; cases t with
    | zero => rfl
    | succ t => rw [List.replicate_succ, List.cons_append, xb_fs]; exact ih ω t (by omega)

theorem xb_app_ge : ∀ (ω : List Bool) (m t : Nat), ω.count false ≤ t → t < ω.count false + m →
    xb (ω ++ List.replicate m false) t = ω.count true
  | [], m, t, _, h2 => by
    have := xb_rep_false m [] t (by simpa using h2); simpa using this
  | true :: ω, m, t, h1, h2 => by
    rw [List.cons_append, xb_t, xb_app_ge ω m t (by simpa using h1) (by simpa using h2)]; simp
  | false :: ω, m, t, h1, h2 => by
    obtain ⟨t, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by simp at h1; omega⟩
    rw [List.cons_append, xb_fs, xb_app_ge ω m t (by simp at h1; omega) (by simp at h2; omega)]; simp

/-- **the moments of σ are read off the absorption word** -/
theorem cx_omega (hb : 1 ≤ b) : ∀ T : Tree, Good a b T → ∀ q r, a ≤ q → q < a + b → a + b ≤ r → r ≤ T.hi →
    cx a T q r = xb (ωq a b T q) (r - (a + b))
  | .leaf i, h, _, _, _, _, _, _ => by have := h.lo; have := h.hi; simp [Tree.lo, Tree.hi] at *; omega
  | .node L R, ⟨⟨hL, hR, e⟩, hlo, hhi⟩, q, r, hq1, hq2, hr1, hr2 => by
    have := Tree.lo_le_hi L hL; have := Tree.lo_le_hi R hR
    simp only [Tree.lo, Tree.hi] at hlo hhi hr2
    by_cases h1 : a + b ≤ L.hi
    · have gL : Good a b L := ⟨hL, hlo, h1⟩
      have f := core_facts a b hb L gL
      have eU : U a b (.node L R) = U a b L := by simp [U, core, h1]
      have eW : W a b (.node L R) = W a b L ++ List.replicate (R.hi + 1 - R.lo) false := by simp [W, core, h1]
      have ea : a' a b (.node L R) = a' a b L := by simp [a', eU]
      have ec : c' a b (.node L R) = c' a b L := by simp [c', V, core, h1]
      have eq' : ωq a b (.node L R) q = ωq a b L q ++ List.replicate (R.hi + 1 - R.lo) false := by
        simp only [ωq, ωp, ωm, eU, eW, ea, ec]; split <;> simp
      have cnt : (ωq a b L q).count false = L.hi + 1 - (a + b) := by
        have := f.wf'; have := f.vhi; have := f.thi
        simp only [ωq, ωp, ωm, c']; split <;> simp [List.count_replicate] <;> omega
      have cntT : (ωq a b L q).count true = a - L.lo := by
        have := f.wt; have := f.ulo; have := f.tlo
        simp only [ωq, ωp, ωm, a']; split <;> simp [List.count_replicate] <;> omega
      rw [eq']
      by_cases hr : r ≤ L.hi
      · have : sub q r (.node L R) = sub q r L := by simp [sub, hr]
        simp only [cx, this]
        rw [xb_app_lt _ _ _ (by omega)]
        exact cx_omega hb L gL q r hq1 hq2 hr1 hr
      · have : sub q r (.node L R) = L := by simp only [sub, if_neg hr]; rw [if_neg (by omega)]
        simp only [cx, this]
        rw [xb_app_ge _ _ _ (by omega) (by omega), cntT]
    · by_cases h2 : R.lo + 1 ≤ a
      · have gR : Good a b R := ⟨hR, h2, hhi⟩
        have f := core_facts a b hb R gR
        have eU : U a b (.node L R) = U a b R := by simp [U, core, h1, h2]
        have eW : W a b (.node L R) = W a b R ++ List.replicate (L.hi + 1 - L.lo) true := by simp [W, core, h1, h2]
        have ea : a' a b (.node L R) = a' a b R := by simp [a', eU]
        have ec : c' a b (.node L R) = c' a b R := by simp [c', V, core, h1, h2]
        have eq' : ωq a b (.node L R) q = ωq a b R q ++ List.replicate (L.hi + 1 - L.lo) true := by
          simp only [ωq, ωp, ωm, eU, eW, ea, ec]; split <;> simp
        have cnt : (ωq a b R q).count false = R.hi + 1 - (a + b) := by
          have := f.wf'; have := f.vhi; have := f.thi
          simp only [ωq, ωp, ωm, c']; split <;> simp [List.count_replicate] <;> omega
        have : sub q r (.node L R) = sub q r R := by
          simp only [sub]; rw [if_neg (by omega), if_pos (by omega)]
        simp only [cx, this, eq']
        rw [xb_app_lt _ _ _ (by omega)]
        exact cx_omega hb R gR q r hq1 hq2 hr1 hr2
      · -- the core
        have eU : U a b (.node L R) = L := by simp [U, core, h1, h2]
        have eV : V a b (.node L R) = R := by simp [V, core, h1, h2]
        have eW : W a b (.node L R) = [] := by simp [W, core, h1, h2]
        simp only [ωq, ωp, ωm, eU, eW, a', c', eV, List.append_nil]
        by_cases hq : q ≤ L.hi
        · rw [if_pos hq]
          have : sub q r (.node L R) = L := by
            simp only [sub]; rw [if_neg (by omega), if_neg (by omega)]
          simp only [cx, this]
          have e0 := xb_rep_false (R.hi + 1 - (a + b)) [] (r - (a + b)) (by omega)
          simp only [List.append_nil] at e0
          rw [xb_rep_true, e0]; rfl
        · rw [if_neg hq]
          have es : sub q r (.node L R) = sub q r R := by
            simp only [sub]; rw [if_neg (by omega), if_pos (by omega)]
          have sl := sub_lo q r R hR
          simp only [cx, es]
          rw [xb_rep_false _ _ _ (by omega)]
          omega

/-! ## `cx` determines the key and conversely -/

theorem xb_inj : ∀ ω ω' : List Bool, ω.count true = ω'.count true → ω.count false = ω'.count false →
    (∀ t, t < ω.count false → xb ω t = xb ω' t) → ω = ω'
  | [], [], _, _, _ => rfl
  | [], true :: _, h, _, _ => by simp at h
  | [], false :: _, _, h, _ => by simp at h
  | true :: _, [], h, _, _ => by simp at h
  | false :: _, [], _, h, _ => by simp at h
  | true :: ω, true :: ω', h1, h2, h3 => by
    rw [xb_inj ω ω' (by simpa using h1) (by simpa using h2) (fun t ht => by
      have := h3 t (by simpa using ht); simp only [xb] at this; omega)]
  | false :: ω, false :: ω', h1, h2, h3 => by
    rw [xb_inj ω ω' (by simpa using h1) (by simpa using h2) (fun t ht => by
      have := h3 (t + 1) (by simp; omega); simpa [xb] using this)]
  | true :: ω, false :: ω', _, h2, h3 => by have := h3 0 (by rw [h2]; simp); simp [xb] at this
  | false :: ω, true :: ω', _, _, h3 => by have := h3 0 (by simp); simp [xb] at this

theorem lead_t {m' k' : Nat} {τ' : List Bool} : ∀ (m k : Nat) (τ : List Bool), 1 ≤ k →
    List.replicate m true ++ (List.replicate k false ++ τ) = List.replicate m' true ++ (List.replicate k' false ++ τ') →
    1 ≤ k' → m = m' := by
  intro m; induction m generalizing m' with
  | zero => intro k τ hk e hk'; cases m' with
    | zero => rfl
    | succ m' => obtain ⟨k, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩; simp [List.replicate_succ] at e
  | succ m ih => intro k τ hk e hk'; cases m' with
    | zero => obtain ⟨k', rfl⟩ : ∃ t, k' = t + 1 := ⟨k' - 1, by omega⟩; simp [List.replicate_succ] at e
    | succ m' => simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at e
                 rw [ih k τ hk e hk']

theorem lead_f {m' k' : Nat} {τ' : List Bool} : ∀ (m k : Nat) (τ : List Bool), 1 ≤ k →
    List.replicate m false ++ (List.replicate k true ++ τ) = List.replicate m' false ++ (List.replicate k' true ++ τ') →
    1 ≤ k' → m = m' := by
  intro m; induction m generalizing m' with
  | zero => intro k τ hk e hk'; cases m' with
    | zero => rfl
    | succ m' => obtain ⟨k, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩; simp [List.replicate_succ] at e
  | succ m ih => intro k τ hk e hk'; cases m' with
    | zero => obtain ⟨k', rfl⟩ : ∃ t, k' = t + 1 := ⟨k' - 1, by omega⟩; simp [List.replicate_succ] at e
    | succ m' => simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at e
                 rw [ih k τ hk e hk']

theorem rep_cancel {m : Nat} {β : Bool} {τ τ' : List Bool} (e : List.replicate m β ++ τ = List.replicate m β ++ τ') : τ = τ' :=
  List.append_cancel_left e

/-- for a bracketing of `xᵃyᵇzᶜ`: the counts of its words -/
theorem ω_counts (hb : 1 ≤ b) (T : Tree) (h : TB a b c T) (ha : 1 ≤ a) (hc : 1 ≤ c) (q : Nat) :
    (ωq a b T q).count true = a ∧ (ωq a b T q).count false = c ∧ 1 ≤ a' a b T ∧ 1 ≤ c' a b T := by
  have g : Good a b T := ⟨h.wf, by rw [h.lo]; omega, by have := h.hi; omega⟩
  have f := core_facts a b hb T g
  have := h.lo; have := h.hi
  have := f.wt; have := f.wf'; have := f.ulo; have := f.vhi; have := f.thi; have := f.tlo
  refine ⟨?_, ?_, by simp only [a']; omega, by simp only [c']; omega⟩ <;>
    simp only [ωq, ωp, ωm, a', c'] <;> split <;> simp [List.count_replicate] <;> omega

theorem head_p (T : Tree) (h1 : 1 ≤ a' a b T) : (ωp a b T).head? = some true := by
  obtain ⟨k, hk⟩ : ∃ k, a' a b T = k + 1 := ⟨a' a b T - 1, by omega⟩
  simp [ωp, hk, List.replicate_succ]
theorem head_m (T : Tree) (h1 : 1 ≤ c' a b T) : (ωm a b T).head? = some false := by
  obtain ⟨k, hk⟩ : ∃ k, c' a b T = k + 1 := ⟨c' a b T - 1, by omega⟩
  simp [ωm, hk, List.replicate_succ]

/-- **the key and the family of absorption words determine each other** -/
theorem key_iff_ωq (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T T' : Tree) (h : TB a b c T) (h' : TB a b c T') :
    key a b T = key a b T' ↔ ∀ q, a ≤ q → q < a + b → ωq a b T q = ωq a b T' q := by
  have g : Good a b T := ⟨h.wf, by rw [h.lo]; omega, by have := h.hi; omega⟩
  have g' : Good a b T' := ⟨h'.wf, by rw [h'.lo]; omega, by have := h'.hi; omega⟩
  have f := core_facts a b hb T g; have f' := core_facts a b hb T' g'
  obtain ⟨_, _, pa, pc⟩ := ω_counts a b c hb T h ha hc a
  obtain ⟨_, _, pa', pc'⟩ := ω_counts a b c hb T' h' ha hc a
  have jb : j a b T ≤ b := by simp only [j]; have := f.uhi'; omega
  have jb' : j a b T' ≤ b := by simp only [j]; have := f'.uhi'; omega
  have side : ∀ q, (q ≤ (U a b T).hi ↔ q < a + j a b T) := by intro q; simp only [j]; have := f.uhi; omega
  have side' : ∀ q, (q ≤ (U a b T').hi ↔ q < a + j a b T') := by intro q; simp only [j]; have := f'.uhi; omega
  have fam_eq : ∀ (U' : Tree) (hU' : TB a b c U'), ∀ q, a ≤ q → q < a + b → ωq a b U' q = fam a (key a b U') q := by
    intro U' hU' q hq1 hq2
    have g1 : Good a b U' := ⟨hU'.wf, by rw [hU'.lo]; omega, by have := hU'.hi; omega⟩
    have f1 := core_facts a b hb U' g1
    have s1 : q ≤ (U a b U').hi ↔ q < a + j a b U' := by simp only [j]; have := f1.uhi; omega
    have jb1 : j a b U' ≤ b := by simp only [j]; have := f1.uhi'; omega
    simp only [key, ωq]
    by_cases j0 : j a b U' = 0
    · simp only [j0, if_true, fam]; rw [if_neg (by rw [s1]; omega)]
    by_cases jb0 : j a b U' = b
    · have hb0 : b ≠ 0 := by omega
      simp only [j0, jb0, hb0, if_true, if_false, fam]; rw [if_pos (by rw [s1]; omega)]
    · simp only [j0, jb0, if_false, fam, ωp, ωm]
      by_cases hq : q ≤ (U a b U').hi
      · rw [if_pos hq, if_pos (s1.1 hq)]
      · rw [if_neg hq, if_neg (fun h => hq (s1.2 h))]
  constructor
  · intro hk q hq1 hq2
    rw [fam_eq T h q hq1 hq2, fam_eq T' h' q hq1 hq2, hk]
  · intro hω
    -- `j` is read off the first letters
    have hj : j a b T = j a b T' := by
      apply Classical.byContradiction; intro hne
      rcases Nat.lt_or_ge (j a b T) (j a b T') with hl | hl
      · have := hω (a + j a b T) (by omega) (by omega)
        simp only [ωq] at this
        rw [if_neg (by rw [side]; omega), if_pos (by rw [side']; omega)] at this
        have := congrArg List.head? this; rw [head_m a b T pc, head_p a b T' pa'] at this; simp at this
      · have := hω (a + j a b T') (by omega) (by omega)
        simp only [ωq] at this
        rw [if_pos (by rw [side]; omega), if_neg (by rw [side']; omega)] at this
        have := congrArg List.head? this; rw [head_p a b T pa, head_m a b T' pc'] at this; simp at this
    simp only [key, hj]
    by_cases j0 : j a b T' = 0
    · simp only [j0, if_true]
      have := hω a (by omega) (by omega)
      simp only [ωq] at this; rw [if_neg (by rw [side]; omega), if_neg (by rw [side']; omega)] at this
      rw [this]
    by_cases jb0 : j a b T' = b
    · have hb0 : b ≠ 0 := by omega
      simp only [j0, jb0, hb0, if_true, if_false]
      have := hω a (by omega) (by omega)
      simp only [ωq] at this; rw [if_pos (by rw [side]; omega), if_pos (by rw [side']; omega)] at this
      rw [this]
    simp only [j0, jb0, if_false, Key.inner.injEq, true_and]
    have ep := hω a (by omega) (by omega)
    simp only [ωq] at ep; rw [if_pos (by rw [side]; omega), if_pos (by rw [side']; omega)] at ep
    have em := hω (a + b - 1) (by omega) (by omega)
    simp only [ωq] at em; rw [if_neg (by rw [side]; omega), if_neg (by rw [side']; omega)] at em
    simp only [ωp, List.append_assoc] at ep
    simp only [ωm, List.append_assoc] at em
    have ea : a' a b T = a' a b T' := lead_t _ _ _ pc ep pc'
    have ec : c' a b T = c' a b T' := lead_f _ _ _ pa em pa'
    rw [ea, ec] at ep
    exact ⟨ea, ec, rep_cancel (rep_cancel ep)⟩

/-- **cx and the key determine each other** -/
theorem key_iff_cx (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T T' : Tree) (h : TB a b c T) (h' : TB a b c T') :
    key a b T = key a b T' ↔
      ∀ q r, a ≤ q → q < a + b → a + b ≤ r → r < a + b + c → cx a T q r = cx a T' q r := by
  have g : Good a b T := ⟨h.wf, by rw [h.lo]; omega, by have := h.hi; omega⟩
  have g' : Good a b T' := ⟨h'.wf, by rw [h'.lo]; omega, by have := h'.hi; omega⟩
  rw [key_iff_ωq a b c ha hb hc T T' h h']
  have := h.hi; have := h'.hi
  constructor
  · intro hω q r hq1 hq2 hr1 hr2
    rw [cx_omega a b hb T g q r hq1 hq2 hr1 (by omega), cx_omega a b hb T' g' q r hq1 hq2 hr1 (by omega),
      hω q hq1 hq2]
  · intro hcx q hq1 hq2
    obtain ⟨t1, f1, _, _⟩ := ω_counts a b c hb T h ha hc q
    obtain ⟨t2, f2, _, _⟩ := ω_counts a b c hb T' h' ha hc q
    apply xb_inj _ _ (by rw [t1, t2]) (by rw [f1, f2])
    intro t ht; rw [f1] at ht
    have e := hcx q (a + b + t) hq1 hq2 (by omega) (by omega)
    rw [cx_omega a b hb T g q _ hq1 hq2 (by omega) (by omega), cx_omega a b hb T' g' q _ hq1 hq2 (by omega) (by omega),
      show a + b + t - (a + b) = t by omega] at e
    exact e

/-- **Proposition T (classification).** For bracketings of `xᵃyᵇzᶜ`: `T, T'` lie in the same
`D_N`-component iff they have the same invariant (`Φ` for interior `j`, the join word for `j ∈ {0, b}`).
So the invariant is constant on each `D_N`-component and tells components apart. -/
theorem propT (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T T' : Tree) (h : TB a b c T) (h' : TB a b c T') :
    DReach (DNStep (w3 a b)) T T' ↔ key a b T = key a b T' := by
  have e : lv T = lv T' := by rw [lv_wf T h.wf, lv_wf T' h'.wf, h.lo, h'.lo, h.hi, h'.hi]
  rw [propC_iff (w3 a b) (w3_mono a b) T T' e (pw_wf T h.wf), sig_iff_cx a b c ha hb hc T T' h h',
    key_iff_cx a b c ha hb hc T T' h h']

end PropT
