import Caterpillar.RPrime
import Caterpillar.Words

/-!
# From run-level certificates to trees: G3 at the level of bracketings

A run list `RL : List (L3 × Nat)` describes a word by its runs (letter, positive length). From a run-level
certificate (`Chain`/`Cat`, Proposition E) we build:
* a bracketing `T₀`;
* a position-level caterpillar chain `L` (`PChain`) whose nodes are nodes of `T₀`;
* a Moufang image `T₁` (`Mouf`: left, right or middle Moufang pattern with a repeated single letter)
  that misses one node of `L`.

With Lemma Cat and Lemma R′ this gives `g3_trees`: for every non-interval word over three letters there are
bracketings `T₀ →(Moufang) T₁` in different `D_N`-components.
-/

namespace Caterpillar
open Tree

/-! ## Runs -/

def Runs (w : Word) : Nat → List (L3 × Nat) → Prop
  | _, [] => True
  | o, (c, n) :: rest => 0 < n ∧ (∀ p, o ≤ p → p < o + n → w p = c) ∧ Runs w (o + n) rest

def tot : List (L3 × Nat) → Nat
  | [] => 0
  | (_, n) :: rest => n + tot rest

def lets (RL : List (L3 × Nat)) : List L3 := RL.map Prod.fst

theorem tot_append : ∀ A B : List (L3 × Nat), tot (A ++ B) = tot A + tot B
  | [], B => by simp [tot]
  | (c, n) :: A, B => by
    show n + tot (A ++ B) = n + tot A + tot B
    rw [tot_append A B]; omega

theorem runs_append (w : Word) : ∀ (A B : List (L3 × Nat)) (o : Nat),
    Runs w o (A ++ B) ↔ Runs w o A ∧ Runs w (o + tot A) B
  | [], B, o => by simp [Runs, tot]
  | (c, n) :: A, B, o => by
    show (0 < n ∧ (∀ p, o ≤ p → p < o + n → w p = c) ∧ Runs w (o + n) (A ++ B)) ↔
      (0 < n ∧ (∀ p, o ≤ p → p < o + n → w p = c) ∧ Runs w (o + n) A) ∧ Runs w (o + (n + tot A)) B
    rw [runs_append w A B (o + n), show o + (n + tot A) = o + n + tot A by omega]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem tot_ge_length (w : Word) : ∀ (RL : List (L3 × Nat)) (o : Nat), Runs w o RL → RL.length ≤ tot RL
  | [], _, _ => by simp [tot]
  | (c, n) :: RL, o, ⟨hn, _, hr⟩ => by
    have := tot_ge_length w RL (o + n) hr; simp [tot]; omega

theorem runs_mem (w : Word) : ∀ (RL : List (L3 × Nat)) (o : Nat) (c : L3), Runs w o RL → c ∈ lets RL →
    ∃ p, o ≤ p ∧ p < o + tot RL ∧ w p = c
  | [], _, _, _, h => by simp [lets] at h
  | (d, n) :: RL, o, c, ⟨hn, hd, hr⟩, h => by
    simp only [lets, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨o, Nat.le_refl _, by simp [tot]; omega, hd o (Nat.le_refl _) (by omega)⟩
    · obtain ⟨p, h1, h2, h3⟩ := runs_mem w RL (o + n) c hr h
      exact ⟨p, by omega, by simp [tot]; omega, h3⟩

theorem lets_cons {RL : List (L3 × Nat)} {c : L3} {t : List L3} (h : lets RL = c :: t) :
    ∃ n RL', RL = (c, n) :: RL' ∧ lets RL' = t := by
  match RL, h with
  | (d, n) :: RL', h =>
    simp only [lets, List.map_cons, List.cons.injEq] at h
    exact ⟨n, RL', by rw [h.1], h.2⟩

theorem lets_concat {RL : List (L3 × Nat)} {c : L3} {t : List L3} (h : lets RL = t ++ [c]) :
    ∃ RL' n, RL = RL' ++ [(c, n)] ∧ lets RL' = t := by
  rcases List.eq_nil_or_concat RL with rfl | ⟨RL', ⟨d, n⟩, rfl⟩
  · simp [lets] at h
  · simp only [lets, List.concat_eq_append, List.map_append, List.map_cons, List.map_nil] at h
    have h2 := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨RL', n, by rw [h2.2, List.concat_eq_append], h2.1⟩

theorem cond_witness (w : Word) {a b : L3} {RL : List (L3 × Nat)} {o : Nat} (h : Cond (some a) b (lets RL))
    (hr : Runs w o RL) : a ≠ b ∧ ∃ p, o ≤ p ∧ p ≤ o + tot RL - 1 ∧ w p = third a b := by
  obtain ⟨hab, hm⟩ := h
  obtain ⟨p, h1, h2, h3⟩ := runs_mem w RL o _ hr hm
  exact ⟨hab, p, h1, by omega, h3⟩

/-! ## Combs -/

/-- leaves `o, …, o+n-1` hung in front of `T` (right comb) -/
def combL : Nat → Nat → Tree → Tree
  | _, 0, T => T
  | o, n + 1, T => node (leaf o) (combL (o + 1) n T)

/-- leaves `o, …, o+n-1` hung after `T` (left comb) -/
def combR : Tree → Nat → Nat → Tree
  | T, _, 0 => T
  | T, o, n + 1 => combR (node T (leaf o)) (o + 1) n

theorem combL_lo : ∀ (o n : Nat) (T : Tree), T.lo = o + n → (combL o n T).lo = o
  | o, 0, T, h => by simp [combL] at h ⊢; omega
  | o, n + 1, T, _ => rfl

theorem combL_hi : ∀ (o n : Nat) (T : Tree), (combL o n T).hi = T.hi
  | _, 0, _ => rfl
  | o, n + 1, T => by simp only [combL, hi]; exact combL_hi (o + 1) n T

theorem combL_wf : ∀ (o n : Nat) (T : Tree), T.WF → T.lo = o + n → (combL o n T).WF
  | _, 0, _, h, _ => h
  | o, n + 1, T, h, hl =>
    ⟨trivial, combL_wf (o + 1) n T h (by omega), by rw [combL_lo (o + 1) n T (by omega)]; rfl⟩

theorem combL_sub : ∀ (o n : Nat) (T : Tree) (K : Ival), K ∈ T.subs → K ∈ (combL o n T).subs
  | _, 0, _, _, h => h
  | o, n + 1, T, K, h => by
    simp only [combL]; rw [mem_node]; exact Or.inr (Or.inr (combL_sub (o + 1) n T K h))

theorem combL_extra : ∀ (o n : Nat) (T : Tree) (K : Ival), K ∈ (combL o n T).subs → K ∈ T.subs ∨ K.1 < o + n
  | _, 0, _, _, h => Or.inl h
  | o, n + 1, T, K, h => by
    simp only [combL] at h; rw [mem_node] at h
    rcases h with rfl | h | h
    · right; simp [lo]
    · simp [subs] at h; subst h; right; simp
    · rcases combL_extra (o + 1) n T K h with h | h
      · exact Or.inl h
      · right; omega

theorem combL_snoc : ∀ (o n : Nat) (T : Tree), combL o (n + 1) T = combL o n (node (leaf (o + n)) T)
  | o, 0, T => rfl
  | o, n + 1, T => by
    show node (leaf o) (combL (o + 1) (n + 1) T) = node (leaf o) (combL (o + 1) n (node (leaf (o + (n + 1))) T))
    rw [combL_snoc (o + 1) n T, show o + 1 + n = o + (n + 1) by omega]

theorem combR_lo : ∀ (T : Tree) (o n : Nat), (combR T o n).lo = T.lo
  | _, _, 0 => rfl
  | T, o, n + 1 => by simp only [combR]; rw [combR_lo]; rfl

theorem combR_hi : ∀ (T : Tree) (o n : Nat), T.hi + 1 = o → (combR T o n).hi = T.hi + n
  | T, o, 0, _ => rfl
  | T, o, n + 1, h => by
    simp only [combR]; rw [combR_hi (node T (leaf o)) (o + 1) n (by simp [hi])]; simp [hi]; omega

theorem combR_wf : ∀ (T : Tree) (o n : Nat), T.WF → T.hi + 1 = o → (combR T o n).WF
  | _, _, 0, h, _ => h
  | T, o, n + 1, h, ho => combR_wf (node T (leaf o)) (o + 1) n ⟨h, trivial, by simp [lo]; omega⟩ (by simp [hi])

theorem combR_sub : ∀ (T : Tree) (o n : Nat) (K : Ival), K ∈ T.subs → K ∈ (combR T o n).subs
  | _, _, 0, _, h => h
  | T, o, n + 1, K, h => by
    simp only [combR]; apply combR_sub; rw [mem_node]; exact Or.inr (Or.inl h)

theorem combR_extra : ∀ (T : Tree) (o n : Nat) (K : Ival), K ∈ (combR T o n).subs → K ∈ T.subs ∨ o ≤ K.2
  | _, _, 0, _, h => Or.inl h
  | T, o, n + 1, K, h => by
    simp only [combR] at h
    rcases combR_extra (node T (leaf o)) (o + 1) n K h with h | h
    · rw [mem_node] at h
      rcases h with rfl | h | h
      · right; simp [hi]
      · exact Or.inl h
      · simp [subs] at h; subst h; right; simp
    · right; omega

theorem combR_snoc : ∀ (T : Tree) (o n : Nat), combR T o (n + 1) = node (combR T o n) (leaf (o + n))
  | T, o, 0 => rfl
  | T, o, n + 1 => by
    show combR (node T (leaf o)) (o + 1) (n + 1) = node (combR (node T (leaf o)) (o + 1) n) (leaf (o + (n + 1)))
    rw [combR_snoc (node T (leaf o)) (o + 1) n, show o + 1 + n = o + (n + 1) by omega]

/-- a run of `n ≥ 1` leaves starting at `o`, as a right comb -/
def runTree (o n : Nat) : Tree := combL o (n - 1) (leaf (o + n - 1))

theorem runTree_facts (o n : Nat) (hn : 0 < n) :
    (runTree o n).WF ∧ (runTree o n).lo = o ∧ (runTree o n).hi = o + n - 1 := by
  refine ⟨combL_wf _ _ _ trivial (by simp [lo]; omega), combL_lo _ _ _ (by simp [lo]; omega), ?_⟩
  simp [runTree, combL_hi, hi]

/-! ## Moufang moves on bracketings -/

/-- One application of a Moufang identity (left `x(y(xz)) = ((xy)x)z`, right `((zx)y)x = z(x(yx))`,
middle `x((yz)x) = (xy)(zx)`) whose repeated variable is a single letter. -/
inductive Mouf (w : Word) : Tree → Tree → Prop
  | left (x x' : Nat) (Y C : Tree) : w x = w x' →
      Mouf w (node (leaf x) (node Y (node (leaf x') C))) (node (node (node (leaf x) Y) (leaf x')) C)
  | right (x x' : Nat) (C Y : Tree) : w x = w x' →
      Mouf w (node (node (node C (leaf x)) Y) (leaf x')) (node C (node (leaf x) (node Y (leaf x'))))
  | mid (x x' : Nat) (B C : Tree) : w x = w x' →
      Mouf w (node (leaf x) (node (node B C) (leaf x'))) (node (node (leaf x) B) (node C (leaf x')))
  | inl {l l' : Tree} (r : Tree) : Mouf w l l' → Mouf w (node l r) (node l' r)
  | inr (l : Tree) {r r' : Tree} : Mouf w r r' → Mouf w (node l r) (node l r')

theorem mouf_combL (w : Word) : ∀ (o n : Nat) {T T' : Tree}, Mouf w T T' → Mouf w (combL o n T) (combL o n T')
  | _, 0, _, _, h => h
  | o, n + 1, _, _, h => Mouf.inr _ (mouf_combL w (o + 1) n h)

theorem mouf_combR (w : Word) : ∀ (o n : Nat) {T T' : Tree}, Mouf w T T' → Mouf w (combR T o n) (combR T' o n)
  | _, 0, _, _, h => h
  | o, n + 1, _, _, h => mouf_combR w (o + 1) n (Mouf.inl _ h)

theorem node_of_wide : ∀ T : Tree, T.lo < T.hi → ∃ B C, T = node B C
  | leaf i, h => by simp [lo, hi] at h
  | node B C, _ => ⟨B, C, rfl⟩

/-! ## Chains -/

theorem glue_chain (w : Word) : ∀ {s : List L3} {e : Option L3}, Chain s e → ∀ (a : L3), e = some a →
    ∀ (RL : List (L3 × Nat)) (o : Nat), lets RL = s → Runs w o RL →
    ∃ (T : Tree) (L : List (Ival × L3)), T.WF ∧ T.lo = o ∧ T.hi = o + tot RL - 1 ∧
      (∀ x ∈ L, x.1 ∈ T.subs) ∧
      ∀ P, SSub (o, o + tot RL - 1) P → SideLetter w P (o, o + tot RL - 1) a →
        PChain w P (((o, o + tot RL - 1), a) :: L) := by
  intro s e h
  induction h with
  | bottom a' u v hau hav huv =>
    intro a ha RL o hl hr
    cases ha
    obtain ⟨n1, RL1, rfl, hl1⟩ := lets_cons hl
    obtain ⟨n2, RL2, rfl, hl2⟩ := lets_cons hl1
    have : RL2 = [] := by cases RL2 <;> simp_all [lets]
    subst this
    obtain ⟨hn1, hu, hn2, hv, _⟩ := hr
    refine ⟨runTree o (n1 + n2), [], ?_⟩
    obtain ⟨f1, f2, f3⟩ := runTree_facts o (n1 + n2) (by omega)
    refine ⟨f1, f2, by rw [f3]; simp [tot], by simp, ?_⟩
    intro P hP hs
    refine ⟨hP, hs, o + n1 - 1, u, v, by simp; omega, by simp [tot]; omega, ?_, ?_, hau, hav, huv⟩
    · intro p h1 h2; exact hu p h1 (by omega)
    · intro p h1 h2; exact hv p (by omega) (by simp [tot] at h2; omega)
  | stepL c t e' hlen hc _ ih =>
    intro a ha RL o hl hr
    subst ha
    obtain ⟨n, RL', rfl, hl'⟩ := lets_cons hl
    obtain ⟨hn, hcr, hr'⟩ := hr
    obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := ih c rfl RL' (o + n) hl' hr'
    have hlenRL : 2 ≤ tot RL' := by
      have := tot_ge_length w RL' (o + n) hr'; have : RL'.length = t.length := by rw [← hl']; simp [lets]
      omega
    obtain ⟨hac, p, hp1, hp2, hp3⟩ := cond_witness w (o := o + n) (by rw [hl']; exact hc) hr'
    refine ⟨combL o n T', (((o + n, o + n + tot RL' - 1), c)) :: L', combL_wf o n T' hw (by omega),
      combL_lo o n T' (by omega), by rw [combL_hi, hhi]; simp [tot]; omega, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · apply combL_sub; have := span_mem T'; simp only [span, hlo, hhi] at this; exact this
      · exact combL_sub o n T' _ (hsub x hx)
    · intro P hP hs
      simp only [tot] at hP hs ⊢
      refine ⟨hP, hs, hac, ⟨p, hp1, hp2, hp3⟩, ?_⟩
      apply hP'
      · simp only [SSub]; omega
      · intro q h1 h2 h3; exact hcr q h1 (by simp at h3; omega)
  | stepR c t e' hlen hc _ ih =>
    intro a ha RL o hl hr
    subst ha
    obtain ⟨RL', n, rfl, hl'⟩ := lets_concat hl
    rw [runs_append] at hr
    obtain ⟨hr', hn, hcr, _⟩ := hr
    obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := ih c rfl RL' o hl' hr'
    have hlenRL : 2 ≤ tot RL' := by
      have := tot_ge_length w RL' o hr'; have : RL'.length = t.length := by rw [← hl']; simp [lets]
      omega
    obtain ⟨hac, p, hp1, hp2, hp3⟩ := cond_witness w (o := o) (by rw [hl']; exact hc) hr'
    have htot : tot (RL' ++ [(c, n)]) = tot RL' + n := by rw [tot_append]; simp [tot]
    rw [htot]
    refine ⟨combR T' (o + tot RL') n, (((o, o + tot RL' - 1), c)) :: L', combR_wf T' _ n hw (by omega),
      by rw [combR_lo, hlo], by rw [combR_hi T' _ n (by omega), hhi]; omega, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · apply combR_sub; have := span_mem T'; simp only [span, hlo, hhi] at this; exact this
      · exact combR_sub T' _ n _ (hsub x hx)
    · intro P hP hs
      refine ⟨hP, hs, hac, ⟨p, hp1, hp2, hp3⟩, ?_⟩
      apply hP'
      · simp only [SSub]; omega
      · intro q h1 h2 h3; exact hcr q (by simp at h3; omega) (by simp at h2; omega)
  | stepD pl m e' hlen hc _ ih =>
    intro a ha RL o hl hr
    subst ha
    obtain ⟨n1, RL1, rfl, hl1⟩ := lets_cons hl
    obtain ⟨RM, n2, rfl, hlm⟩ := lets_concat hl1
    obtain ⟨hn1, hc1, hr1⟩ := hr
    rw [runs_append] at hr1
    obtain ⟨hrm, hn2, hc2, _⟩ := hr1
    obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := ih pl rfl RM (o + n1) hlm hrm
    have hlenRL : 2 ≤ tot RM := by
      have := tot_ge_length w RM (o + n1) hrm; have : RM.length = m.length := by rw [← hlm]; simp [lets]
      omega
    obtain ⟨hac, p, hp1, hp2, hp3⟩ := cond_witness w (o := o + n1) (by rw [hlm]; exact hc) hrm
    have htot : tot ((pl, n1) :: (RM ++ [(pl, n2)])) = n1 + tot RM + n2 := by
      simp only [tot]; rw [tot_append]; simp [tot]; omega
    rw [htot]
    have hT2 := combR_wf T' (o + n1 + tot RM) n2 hw (by omega)
    have hT2lo : (combR T' (o + n1 + tot RM) n2).lo = o + n1 := by rw [combR_lo, hlo]
    have hT2hi : (combR T' (o + n1 + tot RM) n2).hi = o + n1 + tot RM + n2 - 1 := by
      rw [combR_hi T' _ n2 (by omega), hhi]; omega
    refine ⟨combL o n1 (combR T' (o + n1 + tot RM) n2), (((o + n1, o + n1 + tot RM - 1), pl)) :: L',
      combL_wf o n1 _ hT2 (by omega), combL_lo o n1 _ (by omega), by rw [combL_hi, hT2hi]; omega, ?_, ?_⟩
    · intro x hx
      apply combL_sub; apply combR_sub
      rcases List.mem_cons.1 hx with rfl | hx
      · have := span_mem T'; simp only [span, hlo, hhi] at this; exact this
      · exact hsub x hx
    · intro P hP hs
      refine ⟨hP, hs, hac, ⟨p, hp1, hp2, hp3⟩, ?_⟩
      apply hP'
      · simp only [SSub]; omega
      · intro q h1 h2 h3
        rcases h3 with h3 | h3
        · exact hc1 q h1 (by simp at h3; omega)
        · exact hc2 q (by simp at h3; omega) (by simp at h2; omega)

/-- Membership in `combL` that avoids the new leaves. -/
theorem not_mem_combL {o n : Nat} {T : Tree} {K : Ival} (h1 : K ∉ T.subs) (h2 : o + n ≤ K.1) :
    K ∉ (combL o n T).subs := fun h => by
  rcases combL_extra o n T K h with h | h
  · exact h1 h
  · omega

theorem not_mem_combR {o n : Nat} {T : Tree} {K : Ival} (h1 : K ∉ T.subs) (h2 : K.2 < o) :
    K ∉ (combR T o n).subs := fun h => by
  rcases combR_extra T o n K h with h | h
  · exact h1 h
  · omega

/-- the span of a well-formed tree is one of its subs, written with `lo`/`hi` -/
theorem lohi_mem (T : Tree) : (T.lo, T.hi) ∈ T.subs := span_mem T

/-- common output of the certificate translation -/
def CatOut (w : Word) (e : Option L3) (o : Nat) (RL : List (L3 × Nat)) : Prop :=
  ∃ (T T1 : Tree) (L : List (Ival × L3)), T.WF ∧ T.lo = o ∧ T.hi = o + tot RL - 1 ∧
    (∀ x ∈ L, x.1 ∈ T.subs) ∧ Mouf w T T1 ∧ (∃ x ∈ L, x.1 ∉ T1.subs) ∧
    (∀ a, e = some a → ∀ P, SSub (o, o + tot RL - 1) P → SideLetter w P (o, o + tot RL - 1) a →
        PChain w P (((o, o + tot RL - 1), a) :: L)) ∧
    (e = none → PChain w (o, o + tot RL - 1) L)

/-- Packaging: a node `J` with the tail chain `Lt` below it. -/
theorem out_of_inner (w : Word) (e : Option L3) (o E : Nat) (J1 : Ival) (c : L3) (Lt : List (Ival × L3))
    (hc : ∀ a, e = some a → a ≠ c ∧ ∃ p, J1.1 ≤ p ∧ p ≤ J1.2 ∧ w p = third a c)
    (hin : PChain w (o, E) ((J1, c) :: Lt)) :
    (∀ a, e = some a → ∀ P, SSub (o, E) P → SideLetter w P (o, E) a → PChain w P (((o, E), a) :: (J1, c) :: Lt)) ∧
    (e = none → PChain w (o, E) ((J1, c) :: Lt)) := by
  refine ⟨?_, fun _ => hin⟩
  intro a ha P hP hs
  obtain ⟨hac, hw⟩ := hc a ha
  exact ⟨hP, hs, hac, hw, hin⟩

theorem cond_gen (w : Word) {e : Option L3} {b : L3} {RL : List (L3 × Nat)} {o : Nat}
    (h : Cond e b (lets RL)) (hr : Runs w o RL) :
    ∀ a, e = some a → a ≠ b ∧ ∃ p, o ≤ p ∧ p ≤ o + tot RL - 1 ∧ w p = third a b := by
  intro a ha; subst ha; exact cond_witness w h hr

theorem glue_cat (w : Word) : ∀ {s : List L3} {e : Option L3}, Cat s e →
    ∀ (RL : List (L3 × Nat)) (o : Nat), lets RL = s → Runs w o RL → CatOut w e o RL := by
  intro s e h
  induction h with
  | passL c t e' hlen hc _ ih =>
    intro RL o hl hr
    unfold CatOut
    obtain ⟨n, RL', rfl, hl'⟩ := lets_cons hl
    obtain ⟨hn, hcr, hr'⟩ := hr
    obtain ⟨T', T1', L', hw, hlo, hhi, hsub, hm, ⟨x, hx, hxm⟩, hP', _⟩ := ih RL' (o + n) hl' hr'
    have hlenRL : 2 ≤ tot RL' := by
      have := tot_ge_length w RL' (o + n) hr'; have : RL'.length = t.length := by rw [← hl']; simp [lets]
      omega
    have hb := subs_bounds T' hw
    simp only [tot]
    refine ⟨combL o n T', combL o n T1', ((o + n, o + n + tot RL' - 1), c) :: L', combL_wf o n T' hw (by omega),
      combL_lo o n T' (by omega), by rw [combL_hi, hhi]; omega, ?_, mouf_combL w o n hm,
      ⟨x, List.mem_cons_of_mem _ hx, not_mem_combL hxm (by have := hb _ (hsub x hx); omega)⟩, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · apply combL_sub; have := lohi_mem T'; rw [hlo, hhi] at this; exact this
      · exact combL_sub o n T' _ (hsub y hy)
    · have hin : PChain w (o, o + (n + tot RL') - 1) (((o + n, o + n + tot RL' - 1), c) :: L') := by
        apply hP' c rfl
        · simp only [SSub]; omega
        · intro q h1 h2 h3; exact hcr q h1 (by simp at h3; omega)
      have hcw := cond_gen w (o := o + n) (by rw [hl']; exact hc) hr'
      exact out_of_inner w e' o _ _ c L' (fun a ha => by
        obtain ⟨h1, p, hp⟩ := hcw a ha; exact ⟨h1, p, hp⟩) hin
  | passR c t e' hlen hc _ ih =>
    intro RL o hl hr
    unfold CatOut
    obtain ⟨RL', n, rfl, hl'⟩ := lets_concat hl
    rw [runs_append] at hr
    obtain ⟨hr', hn, hcr, _⟩ := hr
    obtain ⟨T', T1', L', hw, hlo, hhi, hsub, hm, ⟨x, hx, hxm⟩, hP', _⟩ := ih RL' o hl' hr'
    have hlenRL : 2 ≤ tot RL' := by
      have := tot_ge_length w RL' o hr'; have : RL'.length = t.length := by rw [← hl']; simp [lets]
      omega
    have hb := subs_bounds T' hw
    have htot : tot (RL' ++ [(c, n)]) = tot RL' + n := by rw [tot_append]; simp [tot]
    rw [htot]
    refine ⟨combR T' (o + tot RL') n, combR T1' (o + tot RL') n, ((o, o + tot RL' - 1), c) :: L',
      combR_wf T' _ n hw (by omega), by rw [combR_lo, hlo], by rw [combR_hi T' _ n (by omega), hhi]; omega, ?_,
      mouf_combR w _ n hm,
      ⟨x, List.mem_cons_of_mem _ hx, not_mem_combR hxm (by have := hb _ (hsub x hx); omega)⟩, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · apply combR_sub; have := lohi_mem T'; rw [hlo, hhi] at this; exact this
      · exact combR_sub T' _ n _ (hsub y hy)
    · have hin : PChain w (o, o + (tot RL' + n) - 1) (((o, o + tot RL' - 1), c) :: L') := by
        apply hP' c rfl
        · simp only [SSub]; omega
        · intro q h1 h2 h3; exact hcr q (by simp at h3; omega) (by simp at h2; omega)
      have hcw := cond_gen w (o := o) (by rw [hl']; exact hc) hr'
      exact out_of_inner w e' o _ _ c L' hcw hin
  | passD pl m e' hlen hc _ ih =>
    intro RL o hl hr
    unfold CatOut
    obtain ⟨n1, RL1, rfl, hl1⟩ := lets_cons hl
    obtain ⟨RM, n2, rfl, hlm⟩ := lets_concat hl1
    obtain ⟨hn1, hc1, hr1⟩ := hr
    rw [runs_append] at hr1
    obtain ⟨hrm, hn2, hc2, _⟩ := hr1
    obtain ⟨T', T1', L', hw, hlo, hhi, hsub, hm, ⟨x, hx, hxm⟩, hP', _⟩ := ih RM (o + n1) hlm hrm
    have hlenRL : 2 ≤ tot RM := by
      have := tot_ge_length w RM (o + n1) hrm; have : RM.length = m.length := by rw [← hlm]; simp [lets]
      omega
    have hb := subs_bounds T' hw
    have htot : tot ((pl, n1) :: (RM ++ [(pl, n2)])) = n1 + tot RM + n2 := by
      simp only [tot]; rw [tot_append]; simp [tot]; omega
    rw [htot]
    have hT2 := combR_wf T' (o + n1 + tot RM) n2 hw (by omega)
    have hT2hi : (combR T' (o + n1 + tot RM) n2).hi = o + n1 + tot RM + n2 - 1 := by
      rw [combR_hi T' _ n2 (by omega), hhi]; omega
    have hxb := hb _ (hsub x hx)
    refine ⟨combL o n1 (combR T' (o + n1 + tot RM) n2), combL o n1 (combR T1' (o + n1 + tot RM) n2),
      ((o + n1, o + n1 + tot RM - 1), pl) :: L', combL_wf o n1 _ hT2 (by rw [combR_lo, hlo]),
      combL_lo o n1 _ (by rw [combR_lo, hlo]), by rw [combL_hi, hT2hi]; omega, ?_,
      mouf_combL w o n1 (mouf_combR w _ n2 hm),
      ⟨x, List.mem_cons_of_mem _ hx, not_mem_combL (not_mem_combR hxm (by omega)) (by omega)⟩, ?_⟩
    · intro y hy
      apply combL_sub; apply combR_sub
      rcases List.mem_cons.1 hy with rfl | hy
      · have := lohi_mem T'; rw [hlo, hhi] at this; exact this
      · exact hsub y hy
    · have hin : PChain w (o, o + (n1 + tot RM + n2) - 1) (((o + n1, o + n1 + tot RM - 1), pl) :: L') := by
        apply hP' pl rfl
        · simp only [SSub]; omega
        · intro q h1 h2 h3
          rcases h3 with h3 | h3
          · exact hc1 q h1 (by simp at h3; omega)
          · exact hc2 q (by simp at h3; omega) (by simp at h2; omega)
      have hcw := cond_gen w (o := o + n1) (by rw [hlm]; exact hc) hrm
      exact out_of_inner w e' o _ _ pl L' (fun a ha => by
        obtain ⟨h1, p, hp⟩ := hcw a ha; exact ⟨h1, p, hp⟩) hin
  | moveD pl m e' hlen hc hch =>
    intro RL o hl hr
    unfold CatOut
    obtain ⟨n1, RL1, rfl, hl1⟩ := lets_cons hl
    obtain ⟨RM, n2, rfl, hlm⟩ := lets_concat hl1
    obtain ⟨hn1, hc1, hr1⟩ := hr
    rw [runs_append] at hr1
    obtain ⟨hrm, hn2, hc2, _⟩ := hr1
    obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := glue_chain w hch pl rfl RM (o + n1) hlm hrm
    have hlenRL : 2 ≤ tot RM := by
      have := tot_ge_length w RM (o + n1) hrm; have : RM.length = m.length := by rw [← hlm]; simp [lets]
      omega
    have htot : tot ((pl, n1) :: (RM ++ [(pl, n2)])) = n1 + tot RM + n2 := by
      simp only [tot]; rw [tot_append]; simp [tot]; omega
    rw [htot]
    obtain ⟨B, C, rfl⟩ := node_of_wide T' (by omega)
    obtain ⟨hB, hC, hBC⟩ := hw
    have bB := subs_bounds B hB; have bC := subs_bounds C hC
    have lB := lo_le_hi B hB; have lC := lo_le_hi C hC
    simp only [lo, hi] at hlo hhi
    obtain ⟨xl, hxl⟩ : ∃ v, v = o + n1 - 1 := ⟨_, rfl⟩
    obtain ⟨xr, hxr⟩ : ∃ v, v = o + n1 + tot RM := ⟨_, rfl⟩
    have hM : (node (leaf xl) (node (node B C) (leaf xr))).WF :=
      ⟨trivial, ⟨⟨hB, hC, hBC⟩, trivial, by simp only [hi, lo]; omega⟩, by simp only [lo, hi]; omega⟩
    have hMhi : (node (leaf xl) (node (node B C) (leaf xr))).hi = xr := rfl
    have hMlo : (node (leaf xl) (node (node B C) (leaf xr))).lo = xl := rfl
    have hT2 := combR_wf _ (xr + 1) (n2 - 1) hM (by rw [hMhi])
    have hT2hi := combR_hi _ (xr + 1) (n2 - 1) (by rw [hMhi])
    refine ⟨combL o (n1 - 1) (combR (node (leaf xl) (node (node B C) (leaf xr))) (xr + 1) (n2 - 1)),
      combL o (n1 - 1) (combR (node (node (leaf xl) B) (node C (leaf xr))) (xr + 1) (n2 - 1)),
      ((o + n1, o + n1 + tot RM - 1), pl) :: L',
      combL_wf o (n1 - 1) _ hT2 (by rw [combR_lo, hMlo]; omega), combL_lo o (n1 - 1) _ (by rw [combR_lo, hMlo]; omega),
      by rw [combL_hi, hT2hi, hMhi]; omega, ?_,
      mouf_combL w o (n1 - 1) (mouf_combR w _ (n2 - 1) (Mouf.mid xl xr B C
        (by rw [hc1 xl (by omega) (by omega), hc2 xr (by omega) (by omega)]))), ?_, ?_⟩
    · intro y hy
      apply combL_sub; apply combR_sub
      rw [mem_node]; right; right; rw [mem_node]; right; left
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [mem_node]; left; exact Prod.ext (by simp only; omega) (by simp only; omega)
      · exact hsub y hy
    · refine ⟨_, List.mem_cons_self, ?_⟩
      apply not_mem_combL _ (by simp only; omega)
      apply not_mem_combR _ (by simp only; omega)
      intro h
      rw [mem_node, mem_node, mem_node] at h
      simp only [subs, List.mem_singleton, lo, hi] at h
      rcases h with h | (h | h | h) | (h | h | h)
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := bB _ h; simp only at this; omega
      · have := Prod.mk.inj h; omega
      · have := bC _ h; simp only at this; omega
      · have := Prod.mk.inj h; omega
    · have hin : PChain w (o, o + (n1 + tot RM + n2) - 1) (((o + n1, o + n1 + tot RM - 1), pl) :: L') := by
        apply hP'
        · simp only [SSub]; omega
        · intro q h1 h2 h3
          rcases h3 with h3 | h3
          · exact hc1 q h1 (by simp at h3; omega)
          · exact hc2 q (by simp at h3; omega) (by simp at h2; omega)
      have hcw := cond_gen w (o := o + n1) (by rw [hlm]; exact hc) hrm
      exact out_of_inner w e' o _ _ pl L' (fun a ha => by
        obtain ⟨h1, p, hp⟩ := hcw a ha; exact ⟨h1, p, hp⟩) hin
  | moveL x y t e' hc1 hc2 hcl =>
    intro RL o hl hr
    unfold CatOut
    obtain ⟨n1, RL1, rfl, hl1⟩ := lets_cons hl
    obtain ⟨n2, RL3, rfl, hl3⟩ := lets_cons hl1
    obtain ⟨n3, RT, rfl, hlt⟩ := lets_cons hl3
    have hlt' : RT.map Prod.fst = t := hlt
    obtain ⟨hn1, hx1, hn2, hy2, hn3, hx3, hrt⟩ := hr
    obtain ⟨o2, ho2⟩ : ∃ v, v = o + n1 := ⟨_, rfl⟩
    obtain ⟨o3, ho3⟩ : ∃ v, v = o + n1 + n2 := ⟨_, rfl⟩
    obtain ⟨o4, ho4⟩ : ∃ v, v = o + n1 + n2 + n3 := ⟨_, rfl⟩
    have hrt4 : Runs w o4 RT := by rw [ho4]; exact hrt
    -- the part after the third run, with its chain
    obtain ⟨R, Lr, hR, hRlo, hRhi, hRsub, hRne, hJ2chain⟩ :
        ∃ (R : Tree) (Lr : List (Ival × L3)), R.WF ∧ R.lo = o4 ∧ R.hi = o4 + tot RT - 1 ∧
          (∀ z ∈ Lr, z.1 ∈ R.subs) ∧ 1 ≤ tot RT ∧
          ∀ P, SSub (o3, o4 + tot RT - 1) P → SideLetter w P (o3, o4 + tot RT - 1) y →
            PChain w P (((o3, o4 + tot RT - 1), y) :: Lr) := by
      rcases hcl with ⟨u, v, b, he, hb, hbu, hbv, huv⟩ | ⟨c, t', he, hlen, hc, hch⟩
      · simp only [List.cons.injEq] at he
        obtain ⟨h1, h2⟩ := he
        subst h1; subst h2
        cases hb
        obtain ⟨n4, RT', rfl, hl4⟩ := lets_cons hlt
        have : RT' = [] := by cases RT' <;> simp_all [lets]
        subst this
        obtain ⟨hn4, hv4, _⟩ := hrt4
        obtain ⟨f1, f2, f3⟩ := runTree_facts o4 n4 hn4
        refine ⟨runTree o4 n4, [], f1, f2, by rw [f3]; simp [tot], by simp, by simp [tot]; omega, ?_⟩
        intro P hP hs
        refine ⟨hP, hs, o4 - 1, x, v, by simp only; omega, by simp only [tot]; omega, ?_, ?_, hbu, hbv, huv⟩
        · intro p h1 h2; exact hx3 p (by simp only at h1; omega) (by omega)
        · intro p h1 h2; exact hv4 p (by omega) (by simp only [tot] at h2; omega)
      · simp only [List.cons.injEq] at he
        obtain ⟨h1, h2⟩ := he
        subst h1; subst h2
        obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := glue_chain w hch x rfl RT o4 hlt hrt4
        have hlenRL : 2 ≤ tot RT := by
          have := tot_ge_length w RT o4 hrt4; have : RT.length = t.length := by rw [← hlt']; simp
          omega
        obtain ⟨hyc, p, hp1, hp2, hp3⟩ := cond_witness w (o := o4) (by rw [hlt]; exact hc) hrt4
        refine ⟨T', ((o4, o4 + tot RT - 1), x) :: L', hw, hlo, hhi, ?_, by omega, ?_⟩
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · have := lohi_mem T'; rw [hlo, hhi] at this; exact this
          · exact hsub z hz
        · intro P hP hs
          refine ⟨hP, hs, hyc, ⟨p, hp1, hp2, hp3⟩, ?_⟩
          apply hP'
          · simp only [SSub]; omega
          · intro q h1 h2 h3; exact hx3 q (by simp only at h1; omega) (by simp at h3; omega)
    have bR := subs_bounds R hR
    obtain ⟨k3, rfl⟩ : ∃ k, n3 = k + 1 := ⟨n3 - 1, by omega⟩
    have hC := combL_wf (o3 + 1) k3 R hR (by omega)
    have hClo := combL_lo (o3 + 1) k3 R (by omega)
    have hChi : (combL (o3 + 1) k3 R).hi = o4 + tot RT - 1 := by rw [combL_hi, hRhi]
    have bC := subs_bounds _ hC
    obtain ⟨hY, hYlo, hYhi⟩ := runTree_facts o2 n2 hn2
    have bY := subs_bounds _ hY
    have hJ2 : (node (leaf o3) (combL (o3 + 1) k3 R)).WF := ⟨trivial, hC, by rw [hClo]; rfl⟩
    have hJ1 : (node (runTree o2 n2) (node (leaf o3) (combL (o3 + 1) k3 R))).WF :=
      ⟨hY, hJ2, by simp only [lo]; rw [hYhi]; omega⟩
    have hSite : (node (leaf (o2 - 1)) (node (runTree o2 n2) (node (leaf o3) (combL (o3 + 1) k3 R)))).WF :=
      ⟨trivial, hJ1, by simp only [lo, hi]; rw [hYlo]; omega⟩
    have htot : tot ((x, n1) :: (y, n2) :: (x, k3 + 1) :: RT) = n1 + n2 + (k3 + 1) + tot RT := by
      simp only [tot]; omega
    rw [htot]
    refine ⟨combL o (n1 - 1) (node (leaf (o2 - 1)) (node (runTree o2 n2) (node (leaf o3) (combL (o3 + 1) k3 R)))),
      combL o (n1 - 1) (node (node (node (leaf (o2 - 1)) (runTree o2 n2)) (leaf o3)) (combL (o3 + 1) k3 R)),
      ((o2, o4 + tot RT - 1), x) :: ((o3, o4 + tot RT - 1), y) :: Lr,
      combL_wf o (n1 - 1) _ hSite (by simp only [lo]; omega), combL_lo o (n1 - 1) _ (by simp only [lo]; omega),
      by rw [combL_hi]; simp only [hi]; rw [hChi]; omega, ?_,
      mouf_combL w o (n1 - 1) (Mouf.left (o2 - 1) o3 _ _
        (by rw [hx1 (o2 - 1) (by omega) (by omega), hx3 o3 (by omega) (by omega)])),
      ⟨_, List.mem_cons_self, ?_⟩, ?_⟩
    · intro z hz
      apply combL_sub; rw [mem_node]; right; right
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [mem_node]; left; exact Prod.ext (by simp only; rw [hYlo]) (by simp only [hi]; rw [hChi])
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [mem_node]; right; right; rw [mem_node]; left
        exact Prod.ext (by simp only [lo]) (by simp only; rw [hChi])
      · rw [mem_node]; right; right; rw [mem_node]; right; right; exact combL_sub _ _ _ _ (hRsub z hz)
    · apply not_mem_combL _ (by simp only; omega)
      intro h
      rw [mem_node, mem_node, mem_node] at h
      simp only [subs, List.mem_singleton, lo, hi] at h
      rw [hYhi, hChi] at h
      try simp only [or_assoc] at h
      rcases h with h | h | h | h | h | h | h
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := bY _ h; rw [hYlo] at this; simp only at this; omega
      · have := Prod.mk.inj h; omega
      · have := bC _ h; rw [hClo] at this; simp only at this; omega
    · have hin2 : PChain w (o2, o4 + tot RT - 1) (((o3, o4 + tot RT - 1), y) :: Lr) := by
        apply hJ2chain
        · simp only [SSub]; omega
        · intro q h1 h2 h3; exact hy2 q (by simp only at h1; omega) (by simp only at h3; omega)
      have w2 := cond_witness w (o := o3) (RL := (x, k3 + 1) :: RT)
        (by simp only [lets, List.map_cons]; rw [hlt']; exact hc2)
        ⟨by omega, fun p h1 h2 => hx3 p (by omega) (by omega), by rw [show o3 + (k3 + 1) = o + n1 + n2 + (k3 + 1) by omega]; exact hrt⟩
      obtain ⟨hxy, p, hp1, hp2, hp3⟩ := w2
      have hin1 : PChain w (o, o + (n1 + n2 + (k3 + 1) + tot RT) - 1)
          (((o2, o4 + tot RT - 1), x) :: ((o3, o4 + tot RT - 1), y) :: Lr) := by
        refine ⟨by simp only [SSub]; omega, ?_, hxy, ⟨p, hp1, by simp only [tot] at hp2; omega, hp3⟩, hin2⟩
        intro q h1 h2 h3; exact hx1 q h1 (by simp only at h3; omega)
      have hcw := cond_gen w (o := o2) (RL := (y, n2) :: (x, k3 + 1) :: RT)
        (by simp only [lets, List.map_cons]; rw [hlt']; exact hc1)
        ⟨hn2, fun p h1 h2 => hy2 p (by omega) (by omega), by omega,
          fun p h1 h2 => hx3 p (by omega) (by omega), by rw [show o2 + n2 + (k3 + 1) = o + n1 + n2 + (k3 + 1) by omega]; exact hrt⟩
      exact out_of_inner w e' o _ _ x _ (fun a ha => by
        obtain ⟨h1, p, hp⟩ := hcw a ha; exact ⟨h1, p, hp.1, by simp only [tot] at hp; omega, hp.2.2⟩) hin1
  | moveR x y t e' hc1 hc2 hcr =>
    intro RL o hl hr
    unfold CatOut
    have e1 : lets RL = (t ++ [x, y]) ++ [x] := by rw [hl]; simp
    obtain ⟨RL1, n1, rfl, hl1⟩ := lets_concat e1
    have e2 : lets RL1 = (t ++ [x]) ++ [y] := by rw [hl1]; simp
    obtain ⟨RL2, n2, rfl, hl2⟩ := lets_concat e2
    obtain ⟨RT, n3, rfl, hlt⟩ := lets_concat hl2
    have hrs := hr
    rw [runs_append, runs_append, runs_append] at hr
    simp only [tot_append, tot, Runs] at hr
    obtain ⟨⟨⟨hrt, hn3, hx3, -⟩, hn2, hy2, -⟩, hn1, hx1, -⟩ := hr
    obtain ⟨oa, hoa⟩ : ∃ v, v = o + tot RT := ⟨_, rfl⟩
    obtain ⟨ob, hob⟩ : ∃ v, v = oa + n3 := ⟨_, rfl⟩
    obtain ⟨oc, hoc⟩ : ∃ v, v = ob + n2 := ⟨_, rfl⟩
    have htot : tot (RT ++ [(x, n3)] ++ [(y, n2)] ++ [(x, n1)]) = tot RT + n3 + n2 + n1 := by
      simp only [tot_append, tot]; omega
    rw [htot]
    have hrl2 : Runs w o (RT ++ [(x, n3)]) := by
      rw [runs_append] at hrs; rw [runs_append] at hrs; exact hrs.1.1
    have hrl1 : Runs w o (RT ++ [(x, n3)] ++ [(y, n2)]) := by
      rw [runs_append] at hrs; exact hrs.1
    -- the part before the third-from-last run, with its chain
    obtain ⟨R, Lr, hR, hRlo, hRhi, hRsub, hRne, hJ2chain⟩ :
        ∃ (R : Tree) (Lr : List (Ival × L3)), R.WF ∧ R.lo = o ∧ R.hi = oa - 1 ∧
          (∀ z ∈ Lr, z.1 ∈ R.subs) ∧ 1 ≤ tot RT ∧
          ∀ P, SSub (o, ob - 1) P → SideLetter w P (o, ob - 1) y →
            PChain w P (((o, ob - 1), y) :: Lr) := by
      rcases hcr with ⟨u, v, b, he, hb, hbu, hbv, huv⟩ | ⟨c, t', he, hlen, hc, hch⟩
      · rw [show [u, v] = [u] ++ [v] from rfl] at he
        obtain ⟨h1, h2⟩ := List.append_inj' he rfl
        simp only [List.cons.injEq, and_true] at h2
        subst h1; subst h2
        cases hb
        obtain ⟨n4, RT', rfl, hl4⟩ := lets_cons hlt
        have : RT' = [] := by cases RT' <;> simp_all [lets]
        subst this
        obtain ⟨hn4, hu4, _⟩ := hrt
        obtain ⟨f1, f2, f3⟩ := runTree_facts o n4 hn4
        have h4 : tot [(u, n4)] = n4 := by simp [tot]
        rw [h4] at hoa
        refine ⟨runTree o n4, [], f1, f2, by rw [f3]; omega, by simp, by rw [h4]; omega, ?_⟩
        intro P hP hs
        refine ⟨hP, hs, oa - 1, u, x, by simp only; omega, by simp only; omega, ?_, ?_, hbu, hbv, huv⟩
        · intro p h1 h2; exact hu4 p h1 (by omega)
        · intro p h1 h2; exact hx3 p (by omega) (by simp only at h2; omega)
      · obtain ⟨h1, h2⟩ := List.append_inj' he rfl
        simp only [List.cons.injEq, and_true] at h2
        subst h1; subst h2
        obtain ⟨T', L', hw, hlo, hhi, hsub, hP'⟩ := glue_chain w hch x rfl RT o hlt hrt
        have hlenRL : 2 ≤ tot RT := by
          have := tot_ge_length w RT o hrt; have : RT.length = t.length := by rw [← hlt]; simp [lets]
          omega
        obtain ⟨hyc, p, hp1, hp2, hp3⟩ := cond_witness w (o := o) (by rw [hlt]; exact hc) hrt
        refine ⟨T', ((o, o + tot RT - 1), x) :: L', hw, hlo, by rw [hhi]; omega, ?_, by omega, ?_⟩
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · have := lohi_mem T'; rw [hlo, hhi] at this; exact this
          · exact hsub z hz
        · intro P hP hs
          refine ⟨hP, hs, hyc, ⟨p, hp1, hp2, hp3⟩, ?_⟩
          apply hP'
          · simp only [SSub]; omega
          · intro q h1 h2 h3; exact hx3 q (by simp only at h3; omega) (by simp only at h2; omega)
    have bR := subs_bounds R hR
    obtain ⟨k3, rfl⟩ : ∃ k, n3 = k + 1 := ⟨n3 - 1, by omega⟩
    have hC := combR_wf R oa k3 hR (by omega)
    have hClo : (combR R oa k3).lo = o := by rw [combR_lo, hRlo]
    have hChi : (combR R oa k3).hi = oa - 1 + k3 := by rw [combR_hi R oa k3 (by omega), hRhi]
    have bC := subs_bounds _ hC
    obtain ⟨hY, hYlo, hYhi⟩ := runTree_facts ob n2 hn2
    have bY := subs_bounds _ hY
    have hJ2 : (node (combR R oa k3) (leaf (ob - 1))).WF := ⟨hC, trivial, by simp only [lo]; rw [hChi]; omega⟩
    have hJ1 : (node (node (combR R oa k3) (leaf (ob - 1))) (runTree ob n2)).WF :=
      ⟨hJ2, hY, by rw [hYlo]; simp only [hi]; omega⟩
    have hSite : (node (node (node (combR R oa k3) (leaf (ob - 1))) (runTree ob n2)) (leaf oc)).WF :=
      ⟨hJ1, trivial, by simp only [lo, hi]; rw [hYhi]; omega⟩
    have hSitehi : (node (node (node (combR R oa k3) (leaf (ob - 1))) (runTree ob n2)) (leaf oc)).hi = oc := rfl
    refine ⟨combR (node (node (node (combR R oa k3) (leaf (ob - 1))) (runTree ob n2)) (leaf oc)) (oc + 1) (n1 - 1),
      combR (node (combR R oa k3) (node (leaf (ob - 1)) (node (runTree ob n2) (leaf oc)))) (oc + 1) (n1 - 1),
      ((o, oc - 1), x) :: ((o, ob - 1), y) :: Lr,
      combR_wf _ _ _ hSite (by rw [hSitehi]), by rw [combR_lo]; simp only [lo]; exact hClo,
      by rw [combR_hi _ _ _ (by rw [hSitehi]), hSitehi]; omega, ?_,
      mouf_combR w (oc + 1) (n1 - 1) (Mouf.right (ob - 1) oc _ _
        (by rw [hx3 (ob - 1) (by omega) (by omega), hx1 oc (by omega) (by omega)])),
      ⟨_, List.mem_cons_self, ?_⟩, ?_⟩
    · intro z hz
      apply combR_sub; rw [mem_node]; right; left
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [mem_node]; left
        exact Prod.ext (show o = (combR R oa k3).lo by rw [hClo]) (show oc - 1 = (runTree ob n2).hi by rw [hYhi]; omega)
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [mem_node]; right; left; rw [mem_node]; left
        exact Prod.ext (show o = (combR R oa k3).lo by rw [hClo]) (show ob - 1 = ob - 1 from rfl)
      · rw [mem_node]; right; left; rw [mem_node]; right; left; exact combR_sub _ _ _ _ (hRsub z hz)
    · apply not_mem_combR _ (show oc - 1 < oc + 1 by omega)
      intro h
      rw [mem_node, mem_node, mem_node] at h
      simp only [subs, List.mem_singleton, lo, hi] at h
      rw [hClo, hYlo] at h
      try simp only [or_assoc] at h
      rcases h with h | h | h | h | h | h | h
      · have := Prod.mk.inj h; omega
      · have := bC _ h; rw [hChi] at this; simp only at this; omega
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := Prod.mk.inj h; omega
      · have := bY _ h; rw [hYlo] at this; simp only at this; omega
      · have := Prod.mk.inj h; omega
    · have hin2 : PChain w (o, oc - 1) (((o, ob - 1), y) :: Lr) := by
        apply hJ2chain
        · simp only [SSub]; omega
        · intro q h1 h2 h3; exact hy2 q (by simp only at h3; omega) (by simp only at h2; omega)
      have w2 := cond_witness w (o := o) (RL := RT ++ [(x, k3 + 1)]) (by rw [hl2]; exact hc2) hrl2
      obtain ⟨hxy, p, hp1, hp2, hp3⟩ := w2
      simp only [tot_append, tot] at hp2
      have hin1 : PChain w (o, o + (tot RT + (k3 + 1) + n2 + n1) - 1)
          (((o, oc - 1), x) :: ((o, ob - 1), y) :: Lr) := by
        refine ⟨by simp only [SSub]; omega, ?_, hxy, ⟨p, hp1, by omega, hp3⟩, hin2⟩
        intro q h1 h2 h3; exact hx1 q (by simp only at h3; omega) (by simp only at h2; omega)
      have hcw := cond_gen w (o := o) (RL := RT ++ [(x, k3 + 1)] ++ [(y, n2)]) (by rw [hl1]; exact hc1) hrl1
      exact out_of_inner w e' o _ _ x _ (fun a ha => by
        obtain ⟨h1, p, hp⟩ := hcw a ha; simp only [tot_append, tot] at hp
        exact ⟨h1, p, hp.1, by omega, hp.2.2⟩) hin1

/-! ## Run-length encoding of a word -/

def rle : List L3 → List (L3 × Nat)
  | [] => []
  | a :: t =>
    match rle t with
    | [] => [(a, 1)]
    | (b, k) :: r => if a = b then (b, k + 1) :: r else (a, 1) :: (b, k) :: r

theorem rle_facts : ∀ wl : List L3,
    lets (rle wl) = runSeq wl ∧ tot (rle wl) = wl.length ∧ Runs (fun p => wl.getD p 0) 0 (rle wl)
  | [] => ⟨rfl, rfl, trivial⟩
  | a :: t => by
    obtain ⟨ih1, ih2, ih3⟩ := rle_facts t
    -- shift the run description of `t` by one position
    have shift : ∀ (RL : List (L3 × Nat)) (o : Nat), Runs (fun p => t.getD p 0) o RL →
        Runs (fun p => (a :: t).getD p 0) (o + 1) RL := by
      intro RL
      induction RL with
      | nil => intro _ _; trivial
      | cons hd rest ih =>
        intro o h
        obtain ⟨c, n⟩ := hd
        obtain ⟨hn, hc, hr⟩ := h
        refine ⟨hn, ?_, ?_⟩
        · intro p h1 h2
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          simpa using hc q (by omega) (by omega)
        · rw [show o + 1 + n = o + n + 1 by omega]; exact ih (o + n) hr
    have h3 := shift _ 0 ih3
    simp only [rle, runSeq]
    rcases hr : rle t with _ | ⟨⟨b, k⟩, r⟩
    · rw [hr] at ih1 ih2 h3
      simp only [lets, List.map_nil] at ih1
      rw [← ih1]
      refine ⟨rfl, by simp only [tot] at ih2 ⊢; simp only [List.length_cons]; omega, ⟨by omega, ?_, trivial⟩⟩
      intro p h1 h2
      obtain rfl : p = 0 := by omega
      rfl
    · rw [hr] at ih1 ih2 h3
      simp only [lets, List.map_cons] at ih1
      rw [← ih1]
      obtain ⟨hk, hb, hrest⟩ := h3
      by_cases hab : a = b
      · subst hab
        simp only [ite_true]
        refine ⟨rfl, by simp only [tot] at ih2 ⊢; simp only [List.length_cons]; omega, ⟨by omega, ?_, ?_⟩⟩
        · intro p h1 h2
          rcases Nat.eq_zero_or_pos p with rfl | hp
          · rfl
          · exact hb p (by omega) (by omega)
        · rw [show 0 + (k + 1) = 0 + 1 + k by omega]; exact hrest
      · simp only [hab, ite_false]
        refine ⟨rfl, by simp only [tot] at ih2 ⊢; simp only [List.length_cons]; omega, ⟨by omega, ?_, hk, hb, hrest⟩⟩
        intro p h1 h2
        obtain rfl : p = 0 := by omega
        rfl

/-! ## G3 at the level of bracketings -/

/-- **G3 (bracketing form).** For every word over three letters that uses all three and is not an interval
word, there are bracketings `T₀` and `T₁` such that:
* `T₁` arises from `T₀` by one application of a Moufang identity (repeated variable a single letter);
* `T₀` and `T₁` lie in different `D_N`-components.

The octonion facts are not formalized here. They are: the Moufang identity makes `T₀` and `T₁` equal maps,
and Lemma W (`D_N ⊇` in-class flips) then turns this into a disconnected kernel class. -/
theorem g3_trees (wl : List L3) (h3 : AllThree wl) (hni : ¬ (runSeq wl).Nodup) :
    ∃ T0 T1 : Tree, T0.WF ∧ T0.lo = 0 ∧ T0.hi = wl.length - 1 ∧
      Mouf (fun p => wl.getD p 0) T0 T1 ∧ ¬ Reach (DNStep (fun p => wl.getD p 0)) T0 T1 := by
  obtain ⟨f1, f2, f3⟩ := rle_facts wl
  obtain ⟨T, T1, L, hw, hlo, hhi, hsub, hm, ⟨x, hx, hxm⟩, -, hnone⟩ :=
    glue_cat (fun p => wl.getD p 0) (cat_of_word wl h3 hni) (rle wl) 0 f1 f3
  refine ⟨T, T1, hw, hlo, by rw [hhi, f2]; omega, hm, ?_⟩
  have hspan : T.span = (0, 0 + tot (rle wl) - 1) := by simp only [span, hlo, hhi]
  exact caterpillar_separates _ T T1 hw L (by rw [hspan]; exact hnone rfl) hsub x hx hxm

end Caterpillar
