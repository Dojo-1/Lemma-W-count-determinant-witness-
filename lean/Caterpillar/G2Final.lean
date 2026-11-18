import Caterpillar.Profiles

/-!
# Theorem G2, assembled

**`g2`.** Let `w` be an interval word (letters non-decreasing along the positions) and `T, T'` bracketings
of the same increasing leaf list. If `T, T'` lie in different `D_N`-components, there is an integer
octonion valuation of the letters on which `T` and `T'` take different values.

*Proof (as in the manuscript).* By Proposition C (`propC_iff`), `T, T'` differ in the shape of a leaf triple
`p < q < r` with distinct letters `u < v < x`. Kill every other letter (`sh_kill`: shapes of surviving
triples are kept). Renumber the surviving leaves `0, 1, …` (`rn`): the restrictions become bracketings of the
three-block word `x^{a′} y^{b′} z^{c′}` that still differ on that triple, so they lie in different
components (Proposition C again), and the Kronecker valuation separates them (`Profiles.g2_three`, which
uses Proposition T, Lemma M, the coefficient extraction and Proposition S). Setting the killed letters to `1`
pulls the separating valuation back to `w` (`kill_ev`).
-/

namespace G2Final
open Caterpillar (Tree)
open Octonion

/-! ## killing keeps the shapes of surviving triples -/

theorem kill_none_mem (w : Nat → Nat) (K : Nat → Bool) (T : Tree) (h : kill w K T = none) :
    ∀ x ∈ lv T, alive w K x = false := by
  intro x hx
  have e := kill_spec w K T; rw [h] at e; simp only [lvo] at e
  cases hc : alive w K x
  · rfl
  · have : x ∈ (lv T).filter (alive w K) := List.mem_filter.2 ⟨hx, hc⟩
    rw [e] at this; simp at this

theorem mem_kill (w : Nat → Nat) (K : Nat → Bool) (T S : Tree) (h : kill w K T = some S) (x : Nat)
    (hx : alive w K x = true) : x ∈ lv S ↔ x ∈ lv T := by
  have := kill_spec w K T; rw [h] at this; simp only [lvo] at this
  rw [← this, List.mem_filter]; simp [hx]

theorem sh_kill (w : Nat → Nat) (K : Nat → Bool) (p q r : Nat) (hp : alive w K p = true)
    (hq : alive w K q = true) (hr : alive w K r = true) :
    ∀ T S : Tree, (lv T).Pairwise (· < ·) → p ∈ lv T → q ∈ lv T → r ∈ lv T → p < q → q < r →
      kill w K T = some S → sh S p q r = sh T p q r
  | .leaf _, S, _, _, _, _, _, _, h => by
    simp only [kill] at h; split at h
    · cases h
    · cases h; rfl
  | .node L R, S, hpw, mp, mq, mr, h1, h2, h => by
    simp only [lv] at hpw mp mq mr
    have pL := (List.pairwise_append.1 hpw).1; have pR := (List.pairwise_append.1 hpw).2.1
    have dj : ∀ x ∈ lv L, x ∉ lv R := fun x hx hx' => Nat.lt_irrefl x (pw_lt hpw hx hx')
    have dj' : ∀ x ∈ lv R, x ∉ lv L := fun x hx hx' => dj x hx' hx
    simp only [kill] at h
    cases hL : kill w K L <;> cases hR : kill w K R <;> rw [hL, hR] at h <;> simp only at h
    · cases h
    · next R' =>
      cases h
      have nL := kill_none_mem w K L hL
      have inR : ∀ x, alive w K x = true → x ∈ lv L ++ lv R → x ∈ lv R := by
        intro x hx m; rcases List.mem_append.1 m with e | e
        · have := nL x e; rw [hx] at this; cases this
        · exact e
      have kR := inR r hr mr; have pR' := inR p hp mp; have qR := inR q hq mq
      rw [sh_R L R p q r (dj' r kR) pR']
      exact sh_kill w K p q r hp hq hr R S pR pR' qR kR h1 h2 hR
    · next L' =>
      cases h
      have nR := kill_none_mem w K R hR
      have inL : ∀ x, alive w K x = true → x ∈ lv L ++ lv R → x ∈ lv L := by
        intro x hx m; rcases List.mem_append.1 m with e | e
        · exact e
        · have := nR x e; rw [hx] at this; cases this
      have kL := inL r hr mr; have pL' := inL p hp mp; have qL := inL q hq mq
      rw [sh_L L R p q r kL]
      exact sh_kill w K p q r hp hq hr L S pL pL' qL kL h1 h2 hL
    · next L' R' =>
      cases h
      have eL := fun x (hx : alive w K x = true) => mem_kill w K L L' hL x hx
      have eR := fun x (hx : alive w K x = true) => mem_kill w K R R' hR x hx
      simp only [sh, eL r hr, eR p hp]
      by_cases hrL : r ∈ lv L
      · have pL' : p ∈ lv L := by
          rcases List.mem_append.1 mp with e | e; · exact e
          · exact absurd (pw_lt hpw hrL e) (by omega)
        have qL : q ∈ lv L := by
          rcases List.mem_append.1 mq with e | e; · exact e
          · exact absurd (pw_lt hpw hrL e) (by omega)
        simp only [hrL, if_true]
        exact sh_kill w K p q r hp hq hr L L' pL pL' qL hrL h1 h2 hL
      · simp only [hrL, if_false]
        by_cases hpR : p ∈ lv R
        · have rR : r ∈ lv R := by rcases List.mem_append.1 mr with e | e; exact absurd e hrL; exact e
          have qR : q ∈ lv R := by
            rcases List.mem_append.1 mq with e | e
            · exact absurd (pw_lt hpw e hpR) (by omega)
            · exact e
          simp only [hpR, if_true]
          exact sh_kill w K p q r hp hq hr R R' pR hpR qR rR h1 h2 hR
        · simp only [hpR, if_false, eL q hq]

/-! ## renumbering the surviving leaves -/

def idx (L : List Nat) (i : Nat) : Nat := (L.filter fun x => decide (x < i)).length

def rn (L : List Nat) : Tree → Tree
  | .leaf i => .leaf (idx L i)
  | .node l r => .node (rn L l) (rn L r)

theorem lv_rn (L : List Nat) : ∀ T, lv (rn L T) = (lv T).map (idx L)
  | .leaf _ => rfl
  | .node l r => by simp [rn, lv, lv_rn L l, lv_rn L r]

theorem idx_cons (l0 : Nat) (L : List Nat) (i : Nat) : idx (l0 :: L) i = (if l0 < i then 1 else 0) + idx L i := by
  simp only [idx, List.filter_cons]; split <;> simp_all <;> omega

theorem idx_head (l0 : Nat) (L : List Nat) (h : ∀ z ∈ L, l0 < z) : idx (l0 :: L) l0 = 0 := by
  rw [idx_cons, if_neg (Nat.lt_irrefl _)]; simp only [idx, Nat.zero_add]
  rw [List.filter_eq_nil_iff.2 (fun z hz => by have := h z hz; simp; omega)]; rfl

theorem idx_lt : ∀ (L : List Nat), L.Pairwise (· < ·) → ∀ x ∈ L, ∀ y ∈ L, x < y → idx L x < idx L y
  | [], _, x, hx, _, _, _ => by simp at hx
  | l0 :: L, hp, x, hx, y, hy, hxy => by
    rw [List.pairwise_cons] at hp
    have hy' : y ∈ L := by
      rcases List.mem_cons.1 hy with e | e
      · subst e; rcases List.mem_cons.1 hx with e' | e'
        · omega
        · exact absurd (hp.1 x e') (by omega)
      · exact e
    rw [idx_cons, idx_cons, if_pos (hp.1 y hy')]
    rcases List.mem_cons.1 hx with e | e
    · subst e; rw [if_neg (Nat.lt_irrefl _)]
      have := idx_head x L hp.1; rw [idx_cons, if_neg (Nat.lt_irrefl _)] at this; omega
    · rw [if_pos (hp.1 x e)]; have := idx_lt L hp.2 x e y hy' hxy; omega

theorem idx_inj (L : List Nat) (hp : L.Pairwise (· < ·)) (x y : Nat) (hx : x ∈ L) (hy : y ∈ L)
    (h : idx L x = idx L y) : x = y := by
  rcases Nat.lt_trichotomy x y with e | e | e
  · have := idx_lt L hp x hx y hy e; omega
  · exact e
  · have := idx_lt L hp y hy x hx e; omega

theorem map_succ_range' : ∀ (s n : Nat), (List.range' s n).map (· + 1) = List.range' (s + 1) n
  | _, 0 => rfl
  | s, n + 1 => by rw [List.range'_succ, List.map_cons, map_succ_range' (s + 1) n, List.range'_succ]

theorem map_idx : ∀ L : List Nat, L.Pairwise (· < ·) → L.map (idx L) = List.range' 0 L.length
  | [], _ => rfl
  | l0 :: L, hp => by
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, idx_head l0 L hp.1, List.length_cons, List.range'_succ]
    congr 1
    rw [← map_succ_range' 0 L.length, ← map_idx L hp.2, List.map_map]
    apply List.map_congr_left; intro x hx
    simp only [Function.comp, idx_cons, if_pos (hp.1 x hx)]; omega

theorem mem_rn (L : List Nat) (hp : L.Pairwise (· < ·)) (T : Tree) (hT : ∀ y ∈ lv T, y ∈ L) (x : Nat) (hx : x ∈ L) :
    idx L x ∈ lv (rn L T) ↔ x ∈ lv T := by
  rw [lv_rn, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩; rw [idx_inj L hp y x (hT y hy) hx e] at hy; exact hy
  · intro h; exact ⟨x, h, rfl⟩

theorem sh_rn (L : List Nat) (hp : L.Pairwise (· < ·)) (p q r : Nat) (hpL : p ∈ L) (hqL : q ∈ L) (hrL : r ∈ L) :
    ∀ T : Tree, (∀ y ∈ lv T, y ∈ L) → sh (rn L T) (idx L p) (idx L q) (idx L r) = sh T p q r
  | .leaf _, _ => rfl
  | .node l r', hT => by
    have hl : ∀ y ∈ lv l, y ∈ L := fun y hy => hT y (by simp [lv, hy])
    have hr' : ∀ y ∈ lv r', y ∈ L := fun y hy => hT y (by simp [lv, hy])
    simp only [rn, sh, mem_rn L hp l hl r hrL, mem_rn L hp r' hr' p hpL, mem_rn L hp l hl q hqL,
      sh_rn L hp p q r hpL hqL hrL l hl, sh_rn L hp p q r hpL hqL hrL r' hr']

theorem ev_rn (L : List Nat) (w w' : Nat → Nat) (ρ ρ' : Nat → O) :
    ∀ T : Tree, (∀ y ∈ lv T, ρ (w y) = ρ' (w' (idx L y))) → ev w ρ T = ev w' ρ' (rn L T)
  | .leaf i, h => h i (by simp [lv])
  | .node l r, h => by
    simp only [ev, rn, ev_rn L w w' ρ ρ' l (fun y hy => h y (by simp [lv, hy])),
      ev_rn L w w' ρ ρ' r (fun y hy => h y (by simp [lv, hy]))]

/-- a bracketing whose leaves are `s, s+1, …, s+m−1` is consecutive -/
theorem wf_of_lv : ∀ (T : Tree) (s m : Nat), lv T = List.range' s m → T.WF ∧ T.lo = s ∧ T.hi + 1 = s + m
  | .leaf i, s, m, h => by
    cases m with
    | zero => simp [lv] at h
    | succ m =>
      rw [List.range'_succ] at h; simp only [lv, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      cases m with
      | zero => exact ⟨trivial, rfl, rfl⟩
      | succ m => rw [List.range'_succ] at h2; simp at h2
  | .node L R, s, m, h => by
    simp only [lv] at h
    have hk : (lv L).length ≤ m := by have := congrArg List.length h; simp at this; omega
    have sp : List.range' s m = List.range' s (lv L).length ++ List.range' (s + (lv L).length) (m - (lv L).length) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [sp] at h
    obtain ⟨e1, e2⟩ := List.append_inj h (by simp)
    obtain ⟨w1, l1, h1⟩ := wf_of_lv L _ _ e1
    obtain ⟨w2, l2, h2⟩ := wf_of_lv R _ _ e2
    exact ⟨⟨w1, w2, by omega⟩, l1, by simp only [Caterpillar.Tree.hi]; omega⟩

/-! ## counting with filters -/

theorem len_filter_le (L : List Nat) (p q : Nat → Bool) (h : ∀ z ∈ L, p z = true → q z = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons z L ih =>
    have ih := ih (fun x hx => h x (by simp [hx]))
    by_cases hp : p z = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h z (by simp) hp)]; simp; omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q z = true
      · rw [List.filter_cons_of_pos hq]; simp; omega
      · rw [List.filter_cons_of_neg hq]; exact ih

theorem len_filter_lt (L : List Nat) (p q : Nat → Bool) (h : ∀ z ∈ L, p z = true → q z = true)
    (y : Nat) (hy : y ∈ L) (hqy : q y = true) (hpy : p y = false) :
    (L.filter p).length < (L.filter q).length := by
  induction L with
  | nil => simp at hy
  | cons z L ih =>
    have hle := len_filter_le L p q (fun x hx => h x (by simp [hx]))
    rcases List.mem_cons.1 hy with e | e
    · subst e
      rw [List.filter_cons_of_neg (by simp [hpy]), List.filter_cons_of_pos hqy]; simp; omega
    · have ih := ih (fun x hx => h x (by simp [hx])) e
      by_cases hp : p z = true
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h z (by simp) hp)]; simp; omega
      · rw [List.filter_cons_of_neg hp]
        by_cases hq : q z = true
        · rw [List.filter_cons_of_pos hq]; simp; omega
        · rw [List.filter_cons_of_neg hq]; exact ih

theorem len_filter_or (L : List Nat) (p q : Nat → Bool) (h : ∀ z ∈ L, ¬ (p z = true ∧ q z = true)) :
    (L.filter fun z => p z || q z).length = (L.filter p).length + (L.filter q).length := by
  induction L with
  | nil => simp
  | cons z L ih =>
    have ih := ih (fun x hx => h x (by simp [hx]))
    have hz := h z (by simp)
    cases hp : p z <;> cases hq : q z <;> simp_all [List.filter_cons] <;> omega

/-! ## the theorem -/

/-- **Theorem G2.** In an interval word, bracketings in different `D_N`-components are different octonion
maps: some integer octonion valuation of the letters separates them. -/
theorem g2 (w : Nat → Nat) (hw : MonoW w) (T T' : Tree) (e : lv T = lv T') (hpw : (lv T).Pairwise (· < ·))
    (hsep : ¬ DReach (DNStep w) T T') : ∃ ρ : Nat → O, ev w ρ T ≠ ev w ρ T' := by
  -- a triple with distinct letters whose shapes differ (Proposition C)
  have hσ : ¬ SigEq w T T' := fun hs => hsep ((propC_iff w hw T T' e hpw).2 hs)
  obtain ⟨p, q, r, hp, hq, hr, h1, h2, hd, hne⟩ : ∃ p q r, p ∈ lv T ∧ q ∈ lv T ∧ r ∈ lv T ∧ p < q ∧ q < r ∧
      Distinct w p q r ∧ sh T p q r ≠ sh T' p q r := by
    apply Classical.byContradiction; intro hn; apply hσ; intro i j k hi hj hk a1 a2 d
    apply Classical.byContradiction; intro hne; exact hn ⟨i, j, k, hi, hj, hk, a1, a2, d, hne⟩
  have m1 := hw p q (Nat.le_of_lt h1); have m2 := hw q r (Nat.le_of_lt h2)
  obtain ⟨d1, d2, d3⟩ := hd
  have n1 : w r ≠ w p := Ne.symm d3
  have n2 : w r ≠ w q := Ne.symm d2
  have n3 : w q ≠ w p := Ne.symm d1
  -- kill every other letter
  let K : Nat → Bool := fun ℓ => !(decide (ℓ = w p) || decide (ℓ = w q) || decide (ℓ = w r))
  have al : ∀ y, alive w K y = true ↔ (w y = w p ∨ w y = w q ∨ w y = w r) := by
    intro y; simp only [alive, K, Bool.not_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
  let L := (lv T).filter (alive w K)
  have someS : ∀ U : Tree, lv U = lv T → ∃ S, kill w K U = some S ∧ lv S = L := by
    intro U hU
    have sp := kill_spec w K U
    cases hk : kill w K U with
    | none =>
      exfalso; rw [hk] at sp; simp only [lvo] at sp
      have : p ∈ (lv U).filter (alive w K) := List.mem_filter.2 ⟨hU ▸ hp, (al p).2 (Or.inl rfl)⟩
      rw [sp] at this; simp at this
    | some S => exact ⟨S, rfl, by rw [hk] at sp; simp only [lvo] at sp; rw [← sp, hU]⟩
  obtain ⟨S, hS, lS⟩ := someS T rfl
  obtain ⟨S', hS', lS'⟩ := someS T' e.symm
  have pwL : L.Pairwise (· < ·) := hpw.filter _
  have memL : ∀ y, y ∈ L ↔ y ∈ lv T ∧ alive w K y = true := fun y => List.mem_filter
  have pL : p ∈ L := (memL p).2 ⟨hp, (al p).2 (Or.inl rfl)⟩
  have qL : q ∈ L := (memL q).2 ⟨hq, (al q).2 (Or.inr (Or.inl rfl))⟩
  have rL : r ∈ L := (memL r).2 ⟨hr, (al r).2 (Or.inr (Or.inr rfl))⟩
  have letL : ∀ y ∈ L, w y = w p ∨ w y = w q ∨ w y = w r := fun y hy => (al y).1 ((memL y).1 hy).2
  -- the three blocks
  let a' := (L.filter fun y => decide (w y = w p)).length
  let b' := (L.filter fun y => decide (w y = w q)).length
  let c' := (L.filter fun y => decide (w y = w r)).length
  have lt_of_mem : ∀ y ∈ L, ∀ z ∈ L, w y < w z → y < z := by
    intro y _ z _ h; apply Classical.byContradiction; intro hn; have := hw z y (by omega); omega
  have ab : (L.filter fun y => decide (w y = w p) || decide (w y = w q)).length = a' + b' :=
    len_filter_or L _ _ (fun z _ h => by simp at h; omega)
  have hlen : L.length = a' + b' + c' := by
    have e1 : (L.filter fun y => (decide (w y = w p) || decide (w y = w q)) || decide (w y = w r)) = L :=
      List.filter_eq_self.2 (fun y hy => by have := letL y hy; simp; omega)
    have := len_filter_or L (fun y => decide (w y = w p) || decide (w y = w q)) (fun y => decide (w y = w r))
      (fun z _ h => by simp at h; omega)
    rw [e1, ab] at this; exact this
  have cls : ∀ y ∈ L, PropT.w3 a' b' (idx L y) = if w y = w p then 0 else if w y = w q then 1 else 2 := by
    intro y hy
    simp only [PropT.w3]
    rcases letL y hy with ey | ey | ey
    · have : idx L y < a' := len_filter_lt L _ _ (fun z hz hzy => by
          have := hw z y (by simp at hzy; omega); rcases letL z hz with e' | e' | e' <;> simp <;> omega)
        y hy (by simp [ey]) (by simp)
      rw [if_pos this, if_pos ey]
    · have lo : a' ≤ idx L y := len_filter_le L _ _ (fun z hz hzp => by
          simp at hzp ⊢; exact lt_of_mem z hz y hy (by omega))
      have hi : idx L y < a' + b' := by
        rw [← ab]; exact len_filter_lt L _ _ (fun z hz hzy => by
          have := hw z y (by simp at hzy; omega); rcases letL z hz with e' | e' | e' <;> simp <;> omega)
          y hy (by simp [ey]) (by simp)
      rw [if_neg (by omega), if_pos hi, if_neg (by omega), if_pos ey]
    · have lo : a' + b' ≤ idx L y := by
        rw [← ab]; exact len_filter_le L _ _ (fun z hz hzp => by
          simp at hzp ⊢; rcases hzp with e' | e' <;> exact lt_of_mem z hz y hy (by omega))
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- renumber
  have ha : 1 ≤ a' := List.length_pos.2 (List.ne_nil_of_mem (List.mem_filter.2 ⟨pL, by simp⟩))
  have hb : 1 ≤ b' := List.length_pos.2 (List.ne_nil_of_mem (List.mem_filter.2 ⟨qL, by simp⟩))
  have hc : 1 ≤ c' := List.length_pos.2 (List.ne_nil_of_mem (List.mem_filter.2 ⟨rL, by simp⟩))
  have tb : ∀ U : Tree, lv U = L → PropT.TB a' b' c' (rn L U) := by
    intro U hU
    have := wf_of_lv (rn L U) 0 L.length (by rw [lv_rn, hU, map_idx L pwL])
    exact ⟨this.1, this.2.1, by rw [this.2.2, hlen]; omega⟩
  have subS : ∀ y ∈ lv S, y ∈ L := fun y hy => lS ▸ hy
  have subS' : ∀ y ∈ lv S', y ∈ L := fun y hy => lS' ▸ hy
  -- the renumbered restrictions still differ on the triple
  have shS : sh S p q r = sh T p q r :=
    sh_kill w K p q r ((al p).2 (Or.inl rfl)) ((al q).2 (Or.inr (Or.inl rfl))) ((al r).2 (Or.inr (Or.inr rfl)))
      T S hpw hp hq hr h1 h2 hS
  have shS' : sh S' p q r = sh T' p q r :=
    sh_kill w K p q r ((al p).2 (Or.inl rfl)) ((al q).2 (Or.inr (Or.inl rfl))) ((al r).2 (Or.inr (Or.inr rfl)))
      T' S' (e ▸ hpw) (e ▸ hp) (e ▸ hq) (e ▸ hr) h1 h2 hS'
  have nsig : ¬ SigEq (PropT.w3 a' b') (rn L S) (rn L S') := by
    intro hs
    apply hne
    rw [← shS, ← shS', ← sh_rn L pwL p q r pL qL rL S subS, ← sh_rn L pwL p q r pL qL rL S' subS']
    apply hs
    · rw [mem_rn L pwL S subS p pL, lS]; exact pL
    · rw [mem_rn L pwL S subS q qL, lS]; exact qL
    · rw [mem_rn L pwL S subS r rL, lS]; exact rL
    · exact idx_lt L pwL p pL q qL h1
    · exact idx_lt L pwL q qL r rL h2
    · simp [Distinct, cls p pL, cls q qL, cls r rL, n1, n2, n3]
  have elv : lv (rn L S) = lv (rn L S') := by rw [lv_rn, lv_rn, lS, lS']
  have nreach : ¬ DReach (DNStep (PropT.w3 a' b')) (rn L S) (rn L S') := fun hr' =>
    nsig ((propC_iff _ (PropT.w3_mono a' b') _ _ elv (PropT.pw_wf _ (tb S lS).wf)).1 hr')
  have sep := Profiles.g2_three a' b' c' ha hb hc (rn L S) (rn L S') (tb S lS) (tb S' lS') nreach
  -- pull the Kronecker valuation back to `w`
  let κ := Profiles.kronρ a' b' c'
  let ρ : Nat → O := fun ℓ => if ℓ = w p then κ 0 else if ℓ = w q then κ 1 else if ℓ = w r then κ 2 else one
  refine ⟨ρ, ?_⟩
  have hK : ∀ ℓ, K ℓ = true → ρ ℓ = one := by
    intro ℓ hℓ; simp only [K, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hℓ
    simp only [ρ, if_neg hℓ.1.1, if_neg hℓ.1.2, if_neg hℓ.2]
  have hρ : ∀ U : Tree, (∀ y ∈ lv U, y ∈ L) → ev w ρ U = ev (PropT.w3 a' b') κ (rn L U) := by
    intro U hU
    apply ev_rn L w (PropT.w3 a' b') ρ κ U
    intro y hy
    rw [cls y (hU y hy)]
    simp only [ρ]
    by_cases e1 : w y = w p
    · simp [e1]
    · by_cases e2 : w y = w q
      · simp [e1, e2, n3]
      · have e3 : w y = w r := by rcases letL y (hU y hy) with h | h | h <;> simp_all
        simp [e1, e2, e3, n1, n2]
  rw [kill_ev w K ρ hK T, kill_ev w K ρ hK T', hS, hS']
  simp only [evo]
  rw [hρ S subS, hρ S' subS']
  exact sep

end G2Final
