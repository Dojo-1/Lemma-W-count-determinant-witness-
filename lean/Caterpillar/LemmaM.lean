import Caterpillar.PropT

/-!
# Lemma M: the moment formula

Substitute `x = 1 + s e₁`, `y = 1 + q e₂`, `z = 1 + t e₄` into a bracketing `T` of `xᵃyᵇzᶜ`. The
`sᵖ q tʳ` coefficient is the sum, over `p` x-leaves, one y-leaf `y_k` and `r` z-leaves, of the value of
`T` restricted to them with `x, y, z ↦ e₁, e₂, e₄` (`moment`). **Lemma M** (`lemmaM`):

  `moment T p r = σ(p, r) · [ j·S(ω₊, p, r) + (b − j)·S(ω₋, p, r) ] · E(p, r)`

with `Φ(T) = (j, a′, c′, W)` from Proposition T, `ω₊ = x^{a′} z^{c′} W`, `ω₋ = z^{c′} x^{a′} W`,
`S(ω, p, r)` the signed count of sub-selections of `ω` with `p` x's and `r` z's (sign `(−1)^{#(z before x)}`,
the `sᵖtʳ` coefficient of the ordered `Cl₂` product), and `σ(p, r) = ±1`, `E(p, r)` a unit that depend
only on `(p, r)`, not on `T`.

The proof follows the manuscript: values are signed units (`SU`); `H = ⟨1, e₁, e₄, e₅⟩` is associative
and `h(cℓ) = (ch)ℓ`, `(cℓ)h = (c h̄)ℓ` for `c, h ∈ H`, `ℓ = e₂` (`walkL`, `walkR`, finite checks). So the
value of a restriction is `(−1)^{#z} · e^{ω} · e₂` with `ω` the absorption word of `y_k` (`term`), and
`e^{ω} = (−1)^{inv(ω) + ⌊p/2⌋ + ⌊r/2⌋} e₁^{p mod 2} e₄^{r mod 2}` (`prodW_eq`). Summing over sub-selections
(`sum_subs_perm`, `sum_S`) and using Proposition T's absorption words (`β_eq_ωq`) gives the formula.
-/

namespace LemmaM
open Caterpillar (Tree)
open Octonion PropT

/-! ## signed units -/

abbrev SU := Int × Fin 8

def mu (x y : SU) : SU := (x.1 * y.1 * sgn x.2 y.2, xr x.2 y.2)
def cs (j : Fin 8) : Int := if j = 0 then 1 else -1
def cj (x : SU) : SU := (x.1 * cs x.2, x.2)
def sc (s : Int) (x : SU) : SU := (s * x.1, x.2)
def toO (x : SU) : O := smul x.1 (unit x.2)
def inH (i : Fin 8) : Bool := i == 0 || i == 1 || i == 4 || i == 5

theorem mul_unit_k : ∀ i j k : Fin 8, mul (unit i) (unit j) k = sgn i j * unit (xr i j) k := by decide +kernel

theorem mul_toO (x y : SU) : mul (toO x) (toO y) = toO (mu x y) := by
  simp only [toO, smul_mul, mul_smul, mu]
  funext k; simp only [smul, mul_unit_k]; simp only [Int.mul_assoc, Int.mul_left_comm]

/-! finite facts about units of `H` and `ℓ = e₂` -/

theorem fL : ∀ i j : Fin 8, inH i = true → inH j = true →
    xr j (xr i 2) = xr (xr i j) 2 ∧ sgn i 2 * sgn j (xr i 2) = sgn i j * sgn (xr i j) 2 := by decide
theorem fR : ∀ i j : Fin 8, inH i = true → inH j = true →
    xr (xr i 2) j = xr (xr i j) 2 ∧ sgn i 2 * sgn (xr i 2) j = cs j * sgn i j * sgn (xr i j) 2 := by decide
theorem fA : ∀ i j k : Fin 8, inH i = true → inH j = true → inH k = true →
    xr (xr i j) k = xr i (xr j k) ∧ sgn i j * sgn (xr i j) k = sgn j k * sgn i (xr j k) := by decide
theorem fC : ∀ i j : Fin 8, inH i = true → inH j = true → inH (xr i j) = true := by decide
theorem f0 : ∀ i : Fin 8, xr 0 i = i ∧ sgn 0 i = 1 := by decide

/-- `h(cℓ) = (ch)ℓ` on `H` -/
theorem walkL (c h : SU) (hc : inH c.2 = true) (hh : inH h.2 = true) :
    mu h (mu c (1, 2)) = mu (mu c h) (1, 2) := by
  obtain ⟨s, i⟩ := c; obtain ⟨t, j⟩ := h
  obtain ⟨e1, e2⟩ := fL i j hc hh
  simp only [mu, e1, Prod.mk.injEq, and_true]
  calc t * (s * 1 * sgn i 2) * sgn j (xr i 2) = s * t * (sgn i 2 * sgn j (xr i 2)) := by
        simp only [Int.mul_one]; ac_rfl
    _ = s * t * (sgn i j * sgn (xr i j) 2) := by rw [e2]
    _ = s * t * sgn i j * 1 * sgn (xr i j) 2 := by simp only [Int.mul_one]; ac_rfl

/-- `(cℓ)h = (c h̄)ℓ` on `H` -/
theorem walkR (c h : SU) (hc : inH c.2 = true) (hh : inH h.2 = true) :
    mu (mu c (1, 2)) h = mu (mu c (cj h)) (1, 2) := by
  obtain ⟨s, i⟩ := c; obtain ⟨t, j⟩ := h
  obtain ⟨e1, e2⟩ := fR i j hc hh
  simp only [mu, cj, e1, Prod.mk.injEq, and_true]
  calc s * 1 * sgn i 2 * t * sgn (xr i 2) j = s * t * (sgn i 2 * sgn (xr i 2) j) := by
        simp only [Int.mul_one]; ac_rfl
    _ = s * t * (cs j * sgn i j * sgn (xr i j) 2) := by rw [e2]
    _ = s * (t * cs j) * sgn i j * 1 * sgn (xr i j) 2 := by simp only [Int.mul_one]; ac_rfl

theorem mu_assoc (x y z : SU) (hx : inH x.2 = true) (hy : inH y.2 = true) (hz : inH z.2 = true) :
    mu (mu x y) z = mu x (mu y z) := by
  obtain ⟨s, i⟩ := x; obtain ⟨t, j⟩ := y; obtain ⟨u, k⟩ := z
  obtain ⟨e1, e2⟩ := fA i j k hx hy hz
  simp only [mu, e1, Prod.mk.injEq, and_true]
  calc s * t * sgn i j * u * sgn (xr i j) k = s * t * u * (sgn i j * sgn (xr i j) k) := by ac_rfl
    _ = s * t * u * (sgn j k * sgn i (xr j k)) := by rw [e2]
    _ = s * (t * u * sgn j k) * sgn i (xr j k) := by ac_rfl

theorem mu_one (x : SU) : mu (1, 0) x = x := by
  obtain ⟨s, i⟩ := x; obtain ⟨e1, e2⟩ := f0 i; simp [mu, e1, e2]

theorem mu_sc (s : Int) (x y : SU) : mu (sc s x) y = sc s (mu x y) := by
  simp only [mu, sc, Prod.mk.injEq, and_true]; ac_rfl

theorem sc_sc (s t : Int) (x : SU) : sc s (sc t x) = sc (s * t) x := by
  simp only [sc, Prod.mk.injEq, and_true]; ac_rfl

/-! ## values of bracketings with unit letters -/

def uev (w : Nat → Nat) (ρ : Nat → Fin 8) : Tree → SU
  | .leaf i => (1, ρ (w i))
  | .node L R => mu (uev w ρ L) (uev w ρ R)

theorem ev_uev (w : Nat → Nat) (ρ : Nat → Fin 8) : ∀ T, ev w (fun ℓ => unit (ρ ℓ)) T = toO (uev w ρ T)
  | .leaf i => by funext k; simp [ev, uev, toO, smul]
  | .node L R => by simp only [ev, uev, ev_uev w ρ L, ev_uev w ρ R, mul_toO]

/-- `true ↦ e₁`, `false ↦ e₄` -/
def ub (β : Bool) : SU := (1, if β then 1 else 4)

/-- ordered product of a word -/
def prodW : List Bool → SU
  | [] => (1, 0)
  | β :: ω => mu (ub β) (prodW ω)

theorem prodW_H : ∀ ω, inH (prodW ω).2 = true
  | [] => rfl
  | β :: ω => fC _ _ (by cases β <;> rfl) (prodW_H ω)

theorem prodW_append : ∀ u v : List Bool, prodW (u ++ v) = mu (prodW u) (prodW v)
  | [], v => (mu_one _).symm
  | β :: u, v => by
    show prodW (β :: (u ++ v)) = mu (prodW (β :: u)) (prodW v)
    rw [prodW, prodW, prodW_append u v, mu_assoc _ _ _ (by cases β <;> rfl) (prodW_H u) (prodW_H v)]

/-- in `H` the value of a bracketing is the ordered product of its letters (associativity) -/
theorem uev_H (w : Nat → Nat) (ρ : Nat → Fin 8) (f : Nat → Bool) :
    ∀ T, (∀ i ∈ lv T, ρ (w i) = (ub (f i)).2) → uev w ρ T = prodW ((lv T).map f)
  | .leaf i, hf => by
    simp only [uev, lv, List.map, prodW, hf i (by simp [lv])]
    rw [show mu (ub (f i)) (1, 0) = (1, (ub (f i)).2) from ?_]
    cases f i <;> decide
  | .node L R, hf => by
    simp only [uev, lv, List.map_append, prodW_append, uev_H w ρ f L (fun i hi => hf i (by simp [lv, hi])),
      uev_H w ρ f R (fun i hi => hf i (by simp [lv, hi]))]

def negPow (n : Nat) : Int := if n % 2 = 0 then 1 else -1

theorem negPow_add (m n : Nat) : negPow (m + n) = negPow m * negPow n := by
  simp only [negPow]; split <;> split <;> split <;> omega

theorem fU : ∀ β : Bool, sgn (ub β).2 0 = 1 ∧ xr (ub β).2 0 = (ub β).2 ∧ sgn (ub β).2 (ub β).2 = -1 ∧
    xr (ub β).2 (ub β).2 = 0 ∧ cs (ub β).2 = -1 ∧ cs 0 = 1 := by decide

theorem ub1 (β : Bool) : (ub β).1 = 1 := by cases β <;> rfl

/-- powers of one imaginary unit -/
theorem pow_form (β : Bool) : ∀ m, prodW (List.replicate m β) =
    (negPow (m / 2), if m % 2 = 0 then 0 else (ub β).2)
  | 0 => rfl
  | m + 1 => by
    obtain ⟨h1, h2, h3, h4, _, _⟩ := fU β
    rw [List.replicate_succ, prodW, pow_form β m]
    by_cases hm : m % 2 = 0
    · rw [if_pos hm, if_neg (show ¬ (m + 1) % 2 = 0 by omega)]
      simp only [mu, ub1, h1, h2, Int.one_mul, Int.mul_one, Prod.mk.injEq, and_true]
      congr 1; omega
    · rw [if_neg hm, if_pos (show (m + 1) % 2 = 0 by omega)]
      simp only [mu, ub1, h3, h4, Int.one_mul, Prod.mk.injEq, and_true]
      simp only [negPow]
      have : (m + 1) / 2 = m / 2 + 1 := by omega
      rw [this]; split <;> split <;> omega

/-- conjugating a power of one imaginary unit -/
theorem cj_pow (β : Bool) (m : Nat) : cj (prodW (List.replicate m β)) = sc (negPow m) (prodW (List.replicate m β)) := by
  obtain ⟨_, _, _, _, h5, h6⟩ := fU β
  rw [pow_form β m]
  simp only [cj, sc, Prod.mk.injEq, and_true]
  by_cases hm : m % 2 = 0
  · simp only [hm, if_true, h6, negPow]; omega
  · simp only [hm, if_false, h5, negPow]; omega

theorem mu_sc' (s : Int) (x y : SU) : mu x (sc s y) = sc s (mu x y) := by
  simp only [mu, sc, Prod.mk.injEq, and_true]; ac_rfl

theorem negPow_mod (m n : Nat) (h : m % 2 = n % 2) : negPow m = negPow n := by
  simp only [negPow, h]

/-! ## the product of a word -/

/-- `e₁^{pp} e₄^{rr}` -/
def Bs (pp rr : Nat) : SU := mu (1, if pp % 2 = 1 then 1 else 0) (1, if rr % 2 = 1 then 4 else 0)

theorem FX : ∀ pp rr : Fin 2, mu (ub true) (Bs pp rr) = sc (negPow pp) (Bs (pp + 1) rr) := by decide
theorem FZ : ∀ pp rr : Fin 2, mu (ub false) (Bs pp rr) = sc (negPow (pp + rr)) (Bs pp (rr + 1)) := by decide

theorem Bs_eq_of_mod {pp rr pp' rr' : Nat} (h1 : pp % 2 = pp' % 2) (h2 : rr % 2 = rr' % 2) : Bs pp rr = Bs pp' rr' := by
  simp only [Bs, h1, h2]

theorem Bs_mod (pp rr : Nat) : Bs pp rr = Bs (pp % 2) (rr % 2) := by simp [Bs, Nat.mod_mod]

/-- number of pairs `z` before `x` -/
def inv : List Bool → Nat
  | [] => 0
  | true :: ω => inv ω
  | false :: ω => inv ω + ω.count true

/-- **the ordered product of a word** `= (−1)^{inv + ⌊p/2⌋ + ⌊r/2⌋} e₁^{p mod 2} e₄^{r mod 2}` -/
theorem prodW_eq : ∀ ω : List Bool, prodW ω =
    sc (negPow (inv ω + ω.count true / 2 + ω.count false / 2)) (Bs (ω.count true) (ω.count false))
  | [] => by decide
  | true :: ω => by
    rw [prodW, prodW_eq ω, mu_sc', Bs_mod]
    have := FX ⟨ω.count true % 2, Nat.mod_lt _ (by decide)⟩ ⟨ω.count false % 2, Nat.mod_lt _ (by decide)⟩
    simp only [Fin.val_add, Fin.isValue] at this
    rw [this, sc_sc, ← negPow_add, Bs_mod]
    simp only [inv, List.count_cons_self, List.count_cons, Bool.false_eq_true, if_false, beq_iff_eq]
    simp only [reduceCtorEq, if_false, Nat.add_zero]
    congr 1
    · apply negPow_mod; omega
    · apply Bs_eq_of_mod
      all_goals (try simp only [Fin.val_add, Fin.val_one, Fin.val_zero, Fin.isValue])
      all_goals omega
  | false :: ω => by
    rw [prodW, prodW_eq ω, mu_sc', Bs_mod]
    have := FZ ⟨ω.count true % 2, Nat.mod_lt _ (by decide)⟩ ⟨ω.count false % 2, Nat.mod_lt _ (by decide)⟩
    simp only [Fin.val_add, Fin.isValue] at this
    rw [this, sc_sc, ← negPow_add, Bs_mod]
    simp only [inv, List.count_cons_self, List.count_cons, Bool.false_eq_true, if_false, beq_iff_eq]
    simp only [reduceCtorEq, if_false, Nat.add_zero]
    congr 1
    · apply negPow_mod; omega
    · apply Bs_eq_of_mod
      all_goals (try simp only [Fin.val_add, Fin.val_one, Fin.val_zero, Fin.isValue])
      all_goals omega

/-! ## the walk from `y_k` to the root -/

variable (a b : Nat)

/-- `x, y, z ↦ e₁, e₂, e₄` -/
def ρ3 (ℓ : Nat) : Fin 8 := if ℓ = 0 then 1 else if ℓ = 1 then 2 else 4

/-- `true` for an `x`-position -/
def lb (i : Nat) : Bool := decide (i < a)

/-- the leaves absorbed by `y_k` on its way to the root, in order (each sibling left to right) -/
def ablP (k : Nat) : Tree → List Nat
  | .leaf _ => []
  | .node L R => if k ∈ lv L then ablP k L ++ lv R else ablP k R ++ lv L

theorem rho_x (i : Nat) (h : i < a) : ρ3 (w3 a b i) = (ub (lb a i)).2 := by
  simp [ρ3, w3, lb, ub, h]
theorem rho_z (i : Nat) (h : a + b ≤ i) : ρ3 (w3 a b i) = (ub (lb a i)).2 := by
  simp [ρ3, w3, lb, ub, show ¬ i < a by omega, show ¬ i < a + b by omega]
theorem rho_y (i : Nat) (h1 : a ≤ i) (h2 : i < a + b) : ρ3 (w3 a b i) = 2 := by
  simp [ρ3, w3, show ¬ i < a by omega, h2]

/-- **the walk.** For a bracketing in which `k` is the only `y`-leaf, `x`'s lie left of it and `z`'s right
of it: value `= (−1)^{#z} · e^{ω} · e₂`, `ω` the absorption word of `y_k`. -/
theorem walk (k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) : ∀ S : Tree, (lv S).Pairwise (· < ·) → k ∈ lv S →
    (∀ i ∈ lv S, i ≠ k → (i < k → i < a) ∧ (k < i → a + b ≤ i)) →
    uev (w3 a b) ρ3 S =
      mu (sc (negPow (((ablP k S).map (lb a)).count false)) (prodW ((ablP k S).map (lb a)))) (1, 2)
  | .leaf i, _, hk, _ => by
    simp only [lv, List.mem_singleton] at hk; subst hk
    simp only [uev, ablP, List.map, List.count_nil, prodW, rho_y a b k hk1 hk2]
    rw [show sc (negPow 0) (1, 0) = (1, 0) from rfl, mu_one]
  | .node L R, hpw, hk, hx => by
    simp only [lv] at hpw hk hx
    have pL := (List.pairwise_append.1 hpw).1; have pR := (List.pairwise_append.1 hpw).2.1
    have oLR : ∀ s ∈ lv L, ∀ t ∈ lv R, s < t := fun s hs t ht => pw_lt hpw hs ht
    by_cases hkL : k ∈ lv L
    · have zR : ∀ i ∈ lv R, a + b ≤ i ∧ lb a i = false := by
        intro i hi
        have hki := oLR k hkL i hi
        have := (hx i (by simp [hi]) (by omega)).2 hki
        exact ⟨this, by simp [lb]; omega⟩
      have hR : uev (w3 a b) ρ3 R = prodW ((lv R).map (lb a)) :=
        uev_H _ _ _ R (fun i hi => rho_z a b i (zR i hi).1)
      have rep : (lv R).map (lb a) = List.replicate (lv R).length false :=
        List.map_eq_replicate_iff.2 (fun i hi => (zR i hi).2)
      have ih := walk k hk1 hk2 L pL hkL (fun i hi hne => hx i (by simp [hi]) hne)
      simp only [uev, ablP, if_pos hkL, ih, hR]
      rw [walkR (sc _ (prodW _)) (prodW _) (prodW_H _) (prodW_H _), rep, cj_pow]
      simp only [mu_sc, mu_sc', sc_sc, List.map_append, prodW_append, rep, List.count_append,
        List.count_replicate_self, negPow_add]
      rw [Int.mul_comm]
    · have xL : ∀ i ∈ lv L, i < a ∧ lb a i = true := by
        intro i hi
        have hk' : k ∈ lv R := by rcases List.mem_append.1 hk with h | h; exact absurd h hkL; exact h
        have hik := oLR i hi k hk'
        have := (hx i (by simp [hi]) (by omega)).1 hik
        exact ⟨this, by simp [lb]; omega⟩
      have hkR : k ∈ lv R := by rcases List.mem_append.1 hk with h | h; exact absurd h hkL; exact h
      have hL : uev (w3 a b) ρ3 L = prodW ((lv L).map (lb a)) :=
        uev_H _ _ _ L (fun i hi => rho_x a b i (xL i hi).1)
      have rep : (lv L).map (lb a) = List.replicate (lv L).length true :=
        List.map_eq_replicate_iff.2 (fun i hi => (xL i hi).2)
      have ih := walk k hk1 hk2 R pR hkR (fun i hi hne => hx i (by simp [hi]) hne)
      simp only [uev, ablP, if_neg hkL, ih, hL]
      rw [walkL (sc _ (prodW _)) (prodW _) (prodW_H _) (prodW_H _)]
      simp only [mu_sc, mu_sc', sc_sc, List.map_append, prodW_append, rep, List.count_append,
        List.count_replicate, Bool.true_eq_false, beq_iff_eq, reduceCtorEq, if_false, Nat.add_zero]

end LemmaM
