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

/-! ## restrictions and absorption lists -/

theorem ablP_sub (k : Nat) : ∀ T : Tree, ∀ i ∈ ablP k T, i ∈ lv T
  | .leaf _, i, h => by simp [ablP] at h
  | .node L R, i, h => by
    simp only [ablP] at h
    split at h
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_append.2 (Or.inl (ablP_sub k L i h))
      · exact List.mem_append.2 (Or.inr h)
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_append.2 (Or.inr (ablP_sub k R i h))
      · exact List.mem_append.2 (Or.inl h)

theorem ablP_perm (k : Nat) : ∀ T : Tree, k ∈ lv T → (ablP k T).Perm ((lv T).erase k)
  | .leaf i, hk => by simp only [lv, List.mem_singleton] at hk; subst hk; simp [ablP, lv]
  | .node L R, hk => by
    simp only [lv] at hk ⊢
    simp only [ablP]
    split
    · next h =>
      rw [List.erase_append_left _ h]
      exact (ablP_perm k L h).append_right _
    · next h =>
      have hR : k ∈ lv R := by rcases List.mem_append.1 hk with e | e; exact absurd e h; exact e
      rw [List.erase_append_right _ h]
      exact ((ablP_perm k R hR).append_right _).trans List.perm_append_comm

/-- restriction commutes with the absorption list -/
theorem ablP_kill (w : Nat → Nat) (Kd : Nat → Bool) (k : Nat) : ∀ T S : Tree, (lv T).Pairwise (· < ·) →
    kill w Kd T = some S → k ∈ lv S → ablP k S = (ablP k T).filter (alive w Kd)
  | .leaf i, S, _, h, hk => by
    simp only [kill] at h; split at h
    · cases h
    · cases h; simp [ablP]
  | .node L R, S, hn, h, hk => by
    simp only [lv] at hn
    have nL := (List.pairwise_append.1 hn).1; have nR := (List.pairwise_append.1 hn).2.1
    have dj : ∀ x ∈ lv L, ∀ y ∈ lv R, x ≠ y := fun x hx y hy => Nat.ne_of_lt (pw_lt hn hx hy)
    have sL := kill_spec w Kd L; have sR := kill_spec w Kd R
    have emp : ∀ X : Tree, kill w Kd X = none → (ablP k X).filter (alive w Kd) = [] := by
      intro X hX
      have := kill_spec w Kd X; rw [hX] at this; simp only [lvo] at this
      rw [List.filter_eq_nil_iff] at this ⊢
      exact fun x hx => this x (ablP_sub k X x hx)
    have empL : ∀ X : Tree, kill w Kd X = none → (lv X).filter (alive w Kd) = [] := by
      intro X hX; have := kill_spec w Kd X; rw [hX] at this; exact this
    have sub' : ∀ (X X' : Tree), kill w Kd X = some X' → ∀ x ∈ lv X', x ∈ lv X := by
      intro X X' hX x hx
      have := kill_spec w Kd X; rw [hX] at this; simp only [lvo] at this
      rw [← this] at hx; exact (List.mem_filter.1 hx).1
    simp only [kill] at h
    cases hL : kill w Kd L <;> cases hR : kill w Kd R <;> rw [hL, hR] at h <;> simp only at h
    · cases h
    · next R' =>
      cases h
      have hkR := sub' R S hR k hk
      have hkL : k ∉ lv L := fun e => dj k e k hkR rfl
      simp only [ablP, if_neg hkL, List.filter_append, empL L hL, List.append_nil]
      exact ablP_kill w Kd k R S nR hR hk
    · next L' =>
      cases h
      have hkL := sub' L S hL k hk
      simp only [ablP, if_pos hkL, List.filter_append, empL R hR, List.append_nil]
      exact ablP_kill w Kd k L S nL hL hk
    · next L' R' =>
      cases h
      have eR : (lv R).filter (alive w Kd) = lv R' := by rw [sR, hR]; rfl
      have eL : (lv L).filter (alive w Kd) = lv L' := by rw [sL, hL]; rfl
      simp only [lv] at hk
      by_cases hkL : k ∈ lv L
      · have hkL' : k ∈ lv L' := by
          rcases List.mem_append.1 hk with e | e
          · exact e
          · exact absurd hkL (fun e' => dj k e' k (sub' R R' hR k e) rfl)
        simp only [ablP, if_pos hkL, if_pos hkL', List.filter_append, eR]
        rw [ablP_kill w Kd k L L' nL hL hkL']
      · have hkL' : k ∉ lv L' := fun e => hkL (sub' L L' hL k e)
        have hkR' : k ∈ lv R' := by rcases List.mem_append.1 hk with e | e; exact absurd e hkL'; exact e
        simp only [ablP, if_neg hkL, if_neg hkL', List.filter_append, eL]
        rw [ablP_kill w Kd k R R' nR hR hkR']

/-! ## the absorption word of `y_k` is Proposition T's `ω_k` -/

/-- letters of positions (`y`'s dropped) -/
def lw (l : List Nat) : List Bool := l.filterMap (fun i => if i < a then some true else if a + b ≤ i then some false else none)

theorem lw_append (l l' : List Nat) : lw a b (l ++ l') = lw a b l ++ lw a b l' := List.filterMap_append l l' _

theorem lw_range' : ∀ m s, (lw a b (List.range' s m)).count true = min (s + m) a - min s a ∧
    (lw a b (List.range' s m)).count false = (s + m) - max s (a + b)
  | 0, s => by constructor <;> simp [lw] <;> omega
  | m + 1, s => by
    obtain ⟨h1, h2⟩ := lw_range' m (s + 1)
    rw [List.range'_succ]
    simp only [lw, List.filterMap_cons] at h1 h2 ⊢
    by_cases hs : s < a
    · simp only [hs, if_true, List.count_cons_self, List.count_cons]; simp only [h1, h2]
      constructor <;> (try simp) <;> omega
    · simp only [hs, if_false]
      by_cases hz : a + b ≤ s
      · simp only [hz, if_true, List.count_cons_self, List.count_cons]; simp only [h1, h2]
        constructor <;> (try simp) <;> omega
      · simp only [hz, if_false]; simp only [h1, h2]; constructor <;> omega

theorem lw_erase (k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) : ∀ l : List Nat, lw a b (l.erase k) = lw a b l
  | [] => rfl
  | x :: l => by
    by_cases hx : x = k
    · subst hx; simp [lw, show ¬ x < a by omega, show ¬ a + b ≤ x by omega]
    · rw [List.erase_cons_tail (by simpa using hx)]
      simp only [lw, List.filterMap_cons] at *
      have := lw_erase k hk1 hk2 l; simp only [lw] at this; rw [this]

theorem lw_perm {l l' : List Nat} (h : l.Perm l') : (lw a b l).Perm (lw a b l') := h.filterMap _

theorem lw_ge (l : List Nat) (h : ∀ i ∈ l, a ≤ i) : lw a b l = List.replicate (lw a b l).length false := by
  apply List.eq_replicate_iff.2; refine ⟨rfl, ?_⟩
  intro β hβ; simp only [lw, List.mem_filterMap] at hβ
  obtain ⟨i, hi, e⟩ := hβ; have := h i hi
  rw [if_neg (by omega)] at e; split at e <;> simp_all

theorem lw_lt (l : List Nat) (h : ∀ i ∈ l, i < a + b) : lw a b l = List.replicate (lw a b l).length true := by
  apply List.eq_replicate_iff.2; refine ⟨rfl, ?_⟩
  intro β hβ; simp only [lw, List.mem_filterMap] at hβ
  obtain ⟨i, hi, e⟩ := hβ; have := h i hi
  split at e
  · simp_all
  · rw [if_neg (by omega)] at e; cases e

/-- the absorption word of `y_k` in `S` -/
def β (k : Nat) (S : Tree) : List Bool := lw a b (ablP k S)

theorem β_counts (k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) (S : Tree) (hS : S.WF) (hk : k ∈ lv S) :
    (β a b k S).count true = min (S.hi + 1) a - min S.lo a ∧
    (β a b k S).count false = (S.hi + 1) - max S.lo (a + b) := by
  have p := lw_perm a b (ablP_perm k S hk)
  rw [lw_erase a b k hk1 hk2, lv_wf S hS] at p
  have := Tree.lo_le_hi S hS
  obtain ⟨h1, h2⟩ := lw_range' a b (S.hi + 1 - S.lo) S.lo
  simp only [β]; rw [p.count_eq, p.count_eq, h1, h2]
  constructor <;> congr 1 <;> omega

/-- the `x`'s before the `t`-th `z` of `β` -/
theorem β_xb (k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) : ∀ S : Tree, S.WF → k ∈ lv S → ∀ t, a + b + t ≤ S.hi →
    xb (β a b k S) t = a - (PropT.sub k (a + b + t) S).lo
  | .leaf i, _, hk, t, ht => by simp [lv] at hk; subst hk; simp [Tree.hi] at ht; omega
  | .node L R, ⟨hL, hR, e⟩, hk, t, ht => by
    have := Tree.lo_le_hi L hL; have := Tree.lo_le_hi R hR
    simp only [Tree.hi] at ht
    have memS := mem_wf (.node L R) ⟨hL, hR, e⟩ k
    have kS := memS.1 hk; simp only [Tree.lo, Tree.hi] at kS
    by_cases hkL : k ≤ L.hi
    · have hkL' : k ∈ lv L := (mem_wf L hL k).2 ⟨kS.1, hkL⟩
      have eβ : β a b k (.node L R) = β a b k L ++ lw a b (lv R) := by
        simp only [β, ablP, if_pos hkL', lw_append]
      have geR : ∀ i ∈ lv R, a ≤ i := fun i hi => by have := ((mem_wf R hR i).1 hi).1; omega
      have cR := lw_range' a b (R.hi + 1 - R.lo) R.lo
      rw [← lv_wf R hR] at cR
      have mR : (lw a b (lv R)).length = (lw a b (lv R)).count false := by
        have e := lw_ge a b (lv R) geR; rw [e]; simp
      obtain ⟨c1, c2⟩ := β_counts a b k hk1 hk2 L hL hkL'
      rw [eβ, lw_ge a b (lv R) geR]
      by_cases hr : a + b + t ≤ L.hi
      · have hs : PropT.sub k (a + b + t) (.node L R) = PropT.sub k (a + b + t) L := by simp [PropT.sub, hr]
        rw [hs, xb_app_lt _ _ _ (by rw [c2]; omega)]
        exact β_xb k hk1 hk2 L hL hkL' t hr
      · have hs : PropT.sub k (a + b + t) (.node L R) = L := by
          simp only [PropT.sub, if_neg hr]; rw [if_neg (by omega)]
        rw [hs, xb_app_ge _ _ _ (by rw [c2]; omega) (by rw [c2, mR, cR.2]; omega), c1]
        omega
    · have hkR : k ∈ lv R := (mem_wf R hR k).2 ⟨by omega, kS.2⟩
      have hkL' : k ∉ lv L := fun h => hkL ((mem_wf L hL k).1 h).2
      have eβ : β a b k (.node L R) = β a b k R ++ lw a b (lv L) := by
        simp only [β, ablP, if_neg hkL', lw_append]
      have ltL : ∀ i ∈ lv L, i < a + b := fun i hi => by have := ((mem_wf L hL i).1 hi).2; omega
      obtain ⟨c1, c2⟩ := β_counts a b k hk1 hk2 R hR hkR
      have hs : PropT.sub k (a + b + t) (.node L R) = sub k (a + b + t) R := by
        simp only [PropT.sub]; rw [if_neg (by omega), if_pos (by omega)]
      rw [eβ, lw_lt a b (lv L) ltL, hs, xb_app_lt _ _ _ (by rw [c2]; omega)]
      exact β_xb k hk1 hk2 R hR hkR t ht

/-- **the absorption word of `y_k` is `ω₊` (if `y_k` lies in the core's left child) or `ω₋`** -/
theorem β_eq_ωq (c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T : Tree) (h : TB a b c T) (k : Nat)
    (hk1 : a ≤ k) (hk2 : k < a + b) : β a b k T = ωq a b T k := by
  have hk : k ∈ lv T := (mem_wf T h.wf k).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩
  obtain ⟨c1, c2⟩ := β_counts a b k hk1 hk2 T h.wf hk
  obtain ⟨t1, t2, _, _⟩ := ω_counts a b c hb T h ha hc k
  have := h.hi; rw [h.lo] at c1 c2
  have g : Good a b T := ⟨h.wf, by rw [h.lo]; omega, by omega⟩
  apply xb_inj _ _ (by rw [c1, t1]; omega) (by rw [c2, t2]; omega)
  intro t ht; rw [c2] at ht
  rw [β_xb a b k hk1 hk2 T h.wf hk t (by omega)]
  have := cx_omega a b hb T g k (a + b + t) hk1 hk2 (by omega) (by omega)
  simp only [cx] at this; rw [this]; congr 1; omega

/-! ## sums over sub-selections -/

def subs : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => subs l ++ (subs l).map (x :: ·)

def isum : List Int → Int
  | [] => 0
  | x :: l => x + isum l

theorem isum_append (l l' : List Int) : isum (l ++ l') = isum l + isum l' := by
  induction l with
  | nil => simp [isum]
  | cons x l ih => rw [List.cons_append, isum, isum, ih, Int.add_assoc]

theorem isum_mul (s : Int) (l : List Int) : isum (l.map (s * ·)) = s * isum l := by
  induction l with
  | nil => simp [isum]
  | cons x l ih => simp only [List.map, isum, ih, Int.mul_add]

theorem isum_map_mul (s : Int) (g : List Nat → Int) (l : List (List Nat)) :
    isum (l.map fun x => s * g x) = s * isum (l.map g) := by
  induction l with
  | nil => simp [isum]
  | cons x l ih => simp only [List.map, isum, ih, Int.mul_add]

theorem isum_map_mul' (s : Int) (g : Nat → Int) (l : List Nat) :
    isum (l.map fun x => s * g x) = s * isum (l.map g) := by
  induction l with
  | nil => simp [isum]
  | cons x l ih => simp only [List.map, isum, ih, Int.mul_add]

theorem isum_subs_cons (x : Nat) (l : List Nat) (H : List Nat → Int) :
    isum ((subs (x :: l)).map H) = isum ((subs l).map H) + isum ((subs l).map (fun K => H (x :: K))) := by
  simp only [subs, List.map_append, List.map_map, isum_append]; rfl

/-- sums over subsets do not depend on the order in which the ground set is listed -/
theorem sum_subs_perm {l l' : List Nat} (hp : l.Perm l') : ∀ H : List Nat → Int,
    (∀ K K', K.Perm K' → H K = H K') → isum ((subs l).map H) = isum ((subs l').map H) := by
  induction hp with
  | nil => intro H _; rfl
  | cons x _ ih =>
    intro H hH
    rw [isum_subs_cons, isum_subs_cons, ih H hH, ih (fun K => H (x :: K)) (fun K K' h => hH _ _ (h.cons x))]
  | swap x y l =>
    intro H hH
    simp only [isum_subs_cons]
    have e : (fun K => H (x :: y :: K)) = (fun K => H (y :: x :: K)) := funext fun K => hH _ _ (List.Perm.swap y x K)
    rw [e]; omega
  | trans _ _ ih1 ih2 => intro H hH; rw [ih1 H hH, ih2 H hH]

theorem subs_sub : ∀ (l K : List Nat), K ∈ subs l → K.Sublist l
  | [], K, h => by simp [subs] at h; subst h; exact List.Sublist.slnil
  | x :: l, K, h => by
    simp only [subs, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨K', h, rfl⟩
    · exact (subs_sub l K h).cons x
    · exact (subs_sub l K' h).cons₂ x

theorem filter_of_sub : ∀ (l K : List Nat), l.Nodup → K ∈ subs l → l.filter (fun i => decide (i ∈ K)) = K
  | [], K, _, h => by simp [subs] at h; subst h; rfl
  | x :: l, K, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [subs, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨K', h, rfl⟩
    · have hx : x ∉ K := fun e => hn.1 ((subs_sub l K h).subset e)
      rw [List.filter_cons_of_neg (by simpa using hx)]
      exact filter_of_sub l K hn.2 h
    · rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [List.filter_congr (q := fun i => decide (i ∈ K')) (fun y hy => by
        have : y ≠ x := fun e => hn.1 (e ▸ hy)
        simp [this])]
      exact filter_of_sub l K' hn.2 h

theorem count_one : ∀ (l : List Nat) (x : Nat), l.Nodup → x ∈ l → l.count x = 1
  | [], _, _, h => by simp at h
  | y :: l, x, hn, h => by
    rw [List.nodup_cons] at hn
    by_cases e : y = x
    · subst e; rw [List.count_cons_self, List.count_eq_zero_of_not_mem hn.1]
    · rw [List.count_cons_of_ne (Ne.symm e)]
      exact count_one l x hn.2 (by simpa [Ne.symm e] using h)

theorem perm_filter_mem (l K : List Nat) (hl : l.Nodup) (hK : K.Nodup) (hsub : ∀ x ∈ K, x ∈ l) :
    (l.filter (fun i => decide (i ∈ K))).Perm K := by
  rw [List.perm_iff_count]; intro x
  by_cases hx : x ∈ K
  · rw [List.count_filter (by simpa using hx), count_one l x hl (hsub x hx), count_one K x hK hx]
  · rw [List.count_eq_zero_of_not_mem (by simp [hx]), List.count_eq_zero_of_not_mem hx]

/-- the signed count of sub-selections with `p` x's and `r` z's (sign `(−1)^{#(z before x)}`) -/
def Ssum : List Bool → Nat → Nat → Int
  | [], p, r => if p = 0 ∧ r = 0 then 1 else 0
  | true :: ω, p, r => Ssum ω p r + (match p with | 0 => 0 | p' + 1 => Ssum ω p' r)
  | false :: ω, p, r => Ssum ω p r + (match r with | 0 => 0 | r' + 1 => negPow p * Ssum ω p r')

def condB (f : Nat → Bool) (p r : Nat) (K : List Nat) : Bool :=
  decide ((K.map f).count true = p ∧ (K.map f).count false = r)

theorem inv_false (ω : List Bool) : inv (false :: ω) = inv ω + ω.count true := rfl

theorem sum_S (f : Nat → Bool) : ∀ (l : List Nat) (p r : Nat),
    isum ((subs l).map (fun K => if condB f p r K then negPow (inv (K.map f)) else 0)) = Ssum (l.map f) p r
  | [], p, r => by
    simp only [subs, List.map, isum, condB, List.count_nil]
    by_cases h : p = 0 ∧ r = 0
    · simp [h, Ssum, inv, negPow]
    · simp only [Ssum, h, if_false]; simp only [decide_eq_true_eq]
      rw [if_neg (by omega)]; rfl
  | x :: l, p, r => by
    rw [isum_subs_cons, sum_S f l p r]
    simp only [List.map_cons]
    cases hx : f x
    · -- z
      simp only [Ssum]; congr 1
      cases r with
      | zero =>
        have : ∀ K : List Nat, condB f p 0 (x :: K) = false := by
          intro K; simp [condB, hx]
        simp only [this]; clear this
        induction subs l with
        | nil => rfl
        | cons _ _ ih => simp only [List.map, isum, ih]; rfl
      | succ r =>
        dsimp only
        rw [← sum_S f l p r, ← isum_mul, List.map_map]
        congr 1; apply List.map_congr_left; intro K _
        simp only [condB, List.map_cons, hx, List.count_cons_self, List.count_cons]
        simp only [Bool.true_eq_false, beq_iff_eq, reduceCtorEq, if_false, Nat.add_zero]
        by_cases h : (K.map f).count true = p ∧ (K.map f).count false = r
        · simp only [show (K.map f).count true = p ∧ (K.map f).count false + 1 = r + 1 by omega, decide_true,
            if_true, inv_false, Function.comp]
          rw [negPow_add, Int.mul_comm]; simp [h]
        · simp only [show ¬ ((K.map f).count true = p ∧ (K.map f).count false + 1 = r + 1) by omega,
            decide_false, Bool.false_eq_true, if_false, Function.comp]
          simp [h]
    · -- x
      simp only [Ssum]; congr 1
      cases p with
      | zero =>
        have : ∀ K : List Nat, condB f 0 r (x :: K) = false := by
          intro K; simp [condB, hx]
        simp only [this]; clear this
        induction subs l with
        | nil => rfl
        | cons _ _ ih => simp only [List.map, isum, ih]; rfl
      | succ p =>
        dsimp only
        rw [← sum_S f l p r]
        congr 1; apply List.map_congr_left; intro K _
        simp only [condB, List.map_cons, hx, List.count_cons_self, List.count_cons]
        simp only [Bool.false_eq_true, beq_iff_eq, reduceCtorEq, if_false, Nat.add_zero, inv]
        by_cases h : (K.map f).count true = p ∧ (K.map f).count false = r
        · simp only [show (K.map f).count true + 1 = p + 1 ∧ (K.map f).count false = r by omega, decide_true, h]
        · simp only [show ¬ ((K.map f).count true + 1 = p + 1 ∧ (K.map f).count false = r) by omega,
            decide_false, h]

/-! ## the moment formula -/

def nonY (i : Nat) : Bool := decide (i < a ∨ a + b ≤ i)
/-- the `x`- and `z`-positions of `xᵃyᵇzᶜ` -/
def XZ (c : Nat) : List Nat := (List.range' 0 (a + b + c)).filter (nonY a b)
def keepK (k : Nat) (K : List Nat) (i : Nat) : Bool := decide (i = k) || decide (i ∈ K)
/-- `T` restricted to the leaves `{k} ∪ K` -/
def restrict (T : Tree) (k : Nat) (K : List Nat) : Option Tree := kill (fun i => i) (fun i => !keepK k K i) T
def ρO (ℓ : Nat) : O := unit (ρ3 ℓ)
def osum : List O → O
  | [] => zero
  | x :: l => oadd x (osum l)

/-- **the `sᵖ q tʳ` moment**: the sum over `p` x-leaves, one y-leaf `y_k` and `r` z-leaves of the value of
`T` restricted to them, with `x, y, z ↦ e₁, e₂, e₄` -/
def moment (c : Nat) (T : Tree) (p r : Nat) : O :=
  osum ((List.range' a b).map fun k => osum ((subs (XZ a b c)).map fun K =>
    if condB (lb a) p r K then evo (w3 a b) ρO (restrict T k K) else zero))

def σ (p r : Nat) : Int := negPow (r + p / 2 + r / 2)
/-- the unit `e₁^{p mod 2} e₄^{r mod 2} e₂` -/
def Eu (p r : Nat) : SU := mu (Bs p r) (1, 2)

theorem toO_zero (x : SU) : toO (sc 0 x) = zero := by funext k; simp [toO, sc, smul, zero]
theorem toO_add (s t : Int) (x : SU) : oadd (toO (sc s x)) (toO (sc t x)) = toO (sc (s + t) x) := by
  funext k; simp only [oadd, toO, sc, smul, Int.add_mul]
theorem toO_sc (s : Int) (x : SU) : toO (sc s x) = smul s (toO x) := by
  funext k; simp only [toO, sc, smul, Int.mul_assoc]

theorem osum_toO (E : SU) (G : List Nat → Int) : ∀ L : List (List Nat),
    osum (L.map fun K => toO (sc (G K) E)) = toO (sc (isum (L.map G)) E)
  | [] => (toO_zero E).symm
  | K :: L => by simp only [List.map, osum, isum, osum_toO E G L, toO_add]

theorem osum_toO' (E : SU) (G : Nat → Int) : ∀ L : List Nat,
    osum (L.map fun k => toO (sc (G k) E)) = toO (sc (isum (L.map G)) E)
  | [] => (toO_zero E).symm
  | K :: L => by simp only [List.map, osum, isum, osum_toO' E G L, toO_add]

theorem lw_map (l : List Nat) (h : ∀ i ∈ l, nonY a b i = true) : lw a b l = l.map (lb a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (by simp); simp only [nonY, decide_eq_true_eq] at hx
    simp only [lw, List.filterMap_cons, List.map_cons, lb] at ih ⊢
    rw [ih (fun i hi => h i (by simp [hi]))]
    by_cases e : x < a
    · simp [e]
    · simp [e, show a + b ≤ x by omega]

theorem lw_filter_nonY (l : List Nat) : lw a b (l.filter (nonY a b)) = lw a b l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases e : nonY a b x = true
    · rw [List.filter_cons_of_pos e]; simp only [lw, List.filterMap_cons] at ih ⊢; rw [ih]
    · rw [List.filter_cons_of_neg e]; simp only [nonY, decide_eq_true_eq] at e
      simp only [lw, List.filterMap_cons] at ih ⊢; rw [ih]
      rw [if_neg (by omega), if_neg (by omega)]

theorem filter_erase_not (p : Nat → Bool) (k : Nat) (hk : p k = false) :
    ∀ l : List Nat, (l.erase k).filter p = l.filter p
  | [] => rfl
  | x :: l => by
    by_cases e : x = k
    · subst e; simp [hk]
    · rw [List.erase_cons_tail (by simpa using e)]
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx, List.filter_cons_of_pos hx, filter_erase_not p k hk l]
      · rw [List.filter_cons_of_neg hx, List.filter_cons_of_neg hx, filter_erase_not p k hk l]

theorem isum_const (X : Int) : ∀ m s : Nat, isum ((List.range' s m).map fun _ => X) = m * X
  | 0, _ => by simp [isum]
  | m + 1, s => by rw [List.range'_succ, List.map_cons, isum, isum_const X m (s + 1)]; push_cast; rw [Int.add_mul]; omega

section
variable (c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (T : Tree) (h : TB a b c T)
include ha hb hc h

theorem lvT : lv T = List.range' 0 (a + b + c) := by
  rw [lv_wf T h.wf, h.lo, h.hi]; simp

theorem nodupT : (lv T).Nodup := by rw [lvT a b c ha hb hc T h]; exact List.nodup_range' _ _

theorem ablP_nodup (k : Nat) (hk : k ∈ lv T) : (ablP k T).Nodup :=
  (ablP_perm k T hk).symm.nodup ((nodupT a b c ha hb hc T h).erase k)

theorem k_not_ablP (k : Nat) (hk : k ∈ lv T) : k ∉ ablP k T := fun e =>
  (nodupT a b c ha hb hc T h).not_mem_erase ((ablP_perm k T hk).mem_iff.1 e)

theorem XZ_sub (K : List Nat) (hK : K ∈ subs (XZ a b c)) : ∀ i ∈ K, i ∈ lv T ∧ nonY a b i = true := by
  intro i hi
  have := (subs_sub _ K hK).subset hi
  simp only [XZ, List.mem_filter] at this
  exact ⟨by rw [lvT a b c ha hb hc T h]; exact this.1, this.2⟩

/-- **one restriction**: its value is `σ(p,r)·(−1)^{inv}·E(p,r)` -/
theorem term (p r k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) (K : List Nat) (hK : K ∈ subs (XZ a b c)) :
    (if condB (lb a) p r K then evo (w3 a b) ρO (restrict T k K) else zero) =
      toO (sc (σ p r * (if condB (lb a) p r K then
        negPow (inv (lw a b ((ablP k T).filter (fun i => decide (i ∈ K))))) else 0)) (Eu p r)) := by
  by_cases hcond : condB (lb a) p r K = true
  · simp only [hcond, if_true]
    have hk : k ∈ lv T := (mem_wf T h.wf k).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩
    have sub := XZ_sub a b c ha hb hc T h K hK
    have al : alive (fun i => i) (fun i => !keepK k K i) = keepK k K := by funext i; simp [alive]
    have spec := kill_spec (fun i => i) (fun i => !keepK k K i) T
    rw [al] at spec
    obtain ⟨S, hS⟩ : ∃ S, restrict T k K = some S := by
      cases e : restrict T k K with
      | some S => exact ⟨S, rfl⟩
      | none =>
        exfalso; simp only [restrict] at e; rw [e] at spec; simp only [lvo] at spec
        have : k ∈ (lv T).filter (keepK k K) := List.mem_filter.2 ⟨hk, by simp [keepK]⟩
        rw [spec] at this; simp at this
    have lvS : lv S = (lv T).filter (keepK k K) := by simp only [restrict] at hS; rw [spec, hS]; rfl
    have pwS : (lv S).Pairwise (· < ·) := by rw [lvS]; exact (pw_wf T h.wf).filter _
    have kS : k ∈ lv S := by rw [lvS]; exact List.mem_filter.2 ⟨hk, by simp [keepK]⟩
    have oth : ∀ i ∈ lv S, i ≠ k → (i < k → i < a) ∧ (k < i → a + b ≤ i) := by
      intro i hi hne
      rw [lvS, List.mem_filter] at hi
      have : i ∈ K := by simpa [keepK, hne] using hi.2
      have := (sub i this).2; simp only [nonY, decide_eq_true_eq] at this
      constructor <;> intro <;> omega
    have hw := walk a b k hk1 hk2 S pwS kS oth
    have hab : ablP k S = (ablP k T).filter (fun i => decide (i ∈ K)) := by
      rw [ablP_kill (fun i => i) (fun i => !keepK k K i) k T S (pw_wf T h.wf) hS kS, al]
      apply List.filter_congr; intro i hi
      have : i ≠ k := fun e => k_not_ablP a b c ha hb hc T h k hk (e ▸ hi)
      simp [keepK, this]
    generalize hβ' : (ablP k T).filter (fun i => decide (i ∈ K)) = β' at hab ⊢
    have memβ : ∀ i ∈ β', nonY a b i = true := by
      intro i hi; rw [← hβ', List.mem_filter] at hi; exact (sub i (by simpa using hi.2)).2
    have hmap : (ablP k S).map (lb a) = lw a b β' := by rw [hab, lw_map a b _ memβ]
    -- counts through the permutation `β' ~ K`
    have pK : β'.Perm K := hβ' ▸ perm_filter_mem _ _ (ablP_nodup a b c ha hb hc T h k hk)
      ((subs_sub _ K hK).nodup ((List.nodup_range' _ _).sublist (List.filter_sublist _)))
      (fun x hx => by
        have hxT := (sub x hx).1
        have hne : x ≠ k := by
          intro e; have := (sub x hx).2; subst e; simp only [nonY, decide_eq_true_eq] at this; omega
        exact (ablP_perm k T hk).mem_iff.2 ((List.mem_erase_of_ne hne).2 hxT))
    have hlwK : lw a b K = K.map (lb a) := lw_map a b K (fun i hi => (sub i hi).2)
    have pl := lw_perm a b pK
    simp only [condB, decide_eq_true_eq] at hcond
    have ct : (lw a b β').count true = p := by rw [pl.count_eq, hlwK, hcond.1]
    have cf : (lw a b β').count false = r := by rw [pl.count_eq, hlwK, hcond.2]
    rw [hS]; simp only [evo]
    show ev (w3 a b) (fun ℓ => unit (ρ3 ℓ)) S = _
    rw [ev_uev, hw, hmap, prodW_eq, ct, cf]
    simp only [Eu, σ, mu_sc, sc_sc, negPow_add]
    congr 1; simp only [sc, Prod.mk.injEq, and_true]; ac_rfl
  · simp only [hcond, Bool.false_eq_true, if_false, Int.mul_zero, toO_zero]

/-- **one `y`-leaf**: the restrictions through `y_k` sum to `S(ω_k, p, r)` -/
theorem sum_k (p r k : Nat) (hk1 : a ≤ k) (hk2 : k < a + b) :
    isum ((subs (XZ a b c)).map fun K => if condB (lb a) p r K then
        negPow (inv (lw a b ((ablP k T).filter (fun i => decide (i ∈ K))))) else 0) = Ssum (ωq a b T k) p r := by
  have hk : k ∈ lv T := (mem_wf T h.wf k).2 ⟨by rw [h.lo]; omega, by have := h.hi; omega⟩
  obtain ⟨l', hl'⟩ : ∃ l', l' = (ablP k T).filter (nonY a b) := ⟨_, rfl⟩
  have nk : nonY a b k = false := by simp only [nonY, decide_eq_false_iff_not]; omega
  have pl : (XZ a b c).Perm l' := by
    have := (ablP_perm k T hk).filter (nonY a b)
    rw [filter_erase_not _ k nk, lvT a b c ha hb hc T h] at this
    rw [hl']; exact this.symm
  have nl' : l'.Nodup := by rw [hl']; exact (List.filter_sublist _).nodup (ablP_nodup a b c ha hb hc T h k hk)
  rw [sum_subs_perm pl _ (by
    intro K K' hp
    have e1 : condB (lb a) p r K = condB (lb a) p r K' := by
      simp only [condB, (hp.map (lb a)).count_eq]
    have e2 : (ablP k T).filter (fun i => decide (i ∈ K)) = (ablP k T).filter (fun i => decide (i ∈ K')) :=
      List.filter_congr (fun i _ => by simp [hp.mem_iff])
    rw [e1, e2])]
  have : ∀ K ∈ subs l', (if condB (lb a) p r K then
      negPow (inv (lw a b ((ablP k T).filter (fun i => decide (i ∈ K))))) else 0) =
      (if condB (lb a) p r K then negPow (inv (K.map (lb a))) else 0) := by
    intro K hK
    have sK : ∀ i ∈ K, i ∈ l' := fun i hi => (subs_sub _ K hK).subset hi
    have e : (ablP k T).filter (fun i => decide (i ∈ K)) = K := by
      rw [← filter_of_sub l' K nl' hK]; subst hl'; rw [List.filter_filter]
      apply List.filter_congr; intro i _
      by_cases hi : i ∈ K
      · have := List.mem_filter.1 (sK i hi); simp [hi, this.1, this.2]
      · simp [hi]
    rw [e, lw_map a b K (fun i hi => (List.mem_filter.1 (hl' ▸ sK i hi)).2)]
  rw [List.map_congr_left this, sum_S (lb a) l' p r, ← lw_map a b l' (fun i hi => by
    rw [hl'] at hi; exact (List.mem_filter.1 hi).2), hl', lw_filter_nonY]
  have := β_eq_ωq a b c ha hb hc T h k hk1 hk2
  simp only [β] at this; rw [this]

/-- **Lemma M (moment formula).** For every bracketing `T` of `xᵃyᵇzᶜ` with invariant `Φ = (j, a′, c′, W)`:
`moment T p r = σ(p, r) · [ j·S(ω₊, p, r) + (b − j)·S(ω₋, p, r) ] · E(p, r)`. -/
theorem lemmaM (p r : Nat) :
    moment a b c T p r = toO (sc (σ p r * ((j a b T : Int) * Ssum (ωp a b T) p r +
      ((b - j a b T : Nat) : Int) * Ssum (ωm a b T) p r)) (Eu p r)) := by
  have g : Good a b T := ⟨h.wf, by rw [h.lo]; omega, by have := h.hi; omega⟩
  have f := core_facts a b hb T g
  have jb : j a b T ≤ b := by simp only [j]; have := f.uhi'; omega
  simp only [moment]
  -- each inner sum
  have inner : ∀ k ∈ List.range' a b, osum ((subs (XZ a b c)).map fun K =>
      if condB (lb a) p r K then evo (w3 a b) ρO (restrict T k K) else zero) =
      toO (sc (σ p r * Ssum (ωq a b T k) p r) (Eu p r)) := by
    intro k hk; rw [List.mem_range'_1] at hk
    rw [List.map_congr_left (fun K hK => term a b c ha hb hc T h p r k hk.1 (by omega) K hK),
      osum_toO, isum_map_mul, sum_k a b c ha hb hc T h p r k hk.1 (by omega)]
  rw [List.map_congr_left inner, osum_toO' (Eu p r) (fun k => σ p r * Ssum (ωq a b T k) p r), isum_map_mul']
  congr 2
  -- split `y`-leaves by the side of the core they lie on
  have split : List.range' a b = List.range' a (j a b T) ++ List.range' (a + j a b T) (b - j a b T) := by
    rw [List.range'_append_1]; congr 1; omega
  have side : ∀ k, k ≤ (U a b T).hi ↔ k < a + j a b T := by intro k; simp only [j]; have := f.uhi; omega
  rw [split, List.map_append, isum_append]
  have e1 : (List.range' a (j a b T)).map (fun k => Ssum (ωq a b T k) p r) =
      (List.range' a (j a b T)).map (fun _ => Ssum (ωp a b T) p r) := by
    apply List.map_congr_left; intro k hk; rw [List.mem_range'_1] at hk
    simp only [ωq]; rw [if_pos ((side k).2 (by omega))]
  have e2 : (List.range' (a + j a b T) (b - j a b T)).map (fun k => Ssum (ωq a b T k) p r) =
      (List.range' (a + j a b T) (b - j a b T)).map (fun _ => Ssum (ωm a b T) p r) := by
    apply List.map_congr_left; intro k hk; rw [List.mem_range'_1] at hk
    simp only [ωq]; rw [if_neg (fun e => by have := (side k).1 e; omega)]
  rw [e1, e2, isum_const, isum_const]

end

end LemmaM
