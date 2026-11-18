import Caterpillar.LemmaCat

/-!
# Lemma R′: self-certifying node sets are constant on `D_N`-components

Bracketings are planar binary trees over positions. A rotation `(AB)C ↔ A(BC)` anywhere in the tree is a
`D_N`-flip when the count matrix of `(A, B, C)` has `det = 0`, i.e. rank ≤ 2, for a word over three
letters. If `S` is self-certifying, every tree reachable from `T₀` by `D_N`-flips contains `S`. The proof
is the first-loss argument.
-/

namespace Caterpillar

inductive Tree
  | leaf (i : Nat)
  | node (l r : Tree)

namespace Tree

def lo : Tree → Nat
  | leaf i => i
  | node l _ => l.lo

def hi : Tree → Nat
  | leaf i => i
  | node _ r => r.hi

def span (t : Tree) : Ival := (t.lo, t.hi)

/-- leaves are consecutive positions -/
def WF : Tree → Prop
  | leaf _ => True
  | node l r => l.WF ∧ r.WF ∧ r.lo = l.hi + 1

/-- spans of all subtrees -/
def subs : Tree → List Ival
  | leaf i => [(i, i)]
  | node l r => (l.lo, r.hi) :: (l.subs ++ r.subs)

theorem lo_le_hi : ∀ t : Tree, t.WF → t.lo ≤ t.hi
  | leaf _, _ => Nat.le_refl _
  | node l r, ⟨hl, hr, he⟩ => by
    have := lo_le_hi l hl; have := lo_le_hi r hr
    simp only [lo, hi]; omega

theorem span_mem : ∀ t : Tree, t.span ∈ t.subs
  | leaf i => by simp [span, subs, lo, hi]
  | node l r => by simp [span, subs, lo, hi]

theorem subs_bounds : ∀ t : Tree, t.WF → ∀ K ∈ t.subs, t.lo ≤ K.1 ∧ K.2 ≤ t.hi ∧ K.1 ≤ K.2
  | leaf i, _, K, hK => by simp [subs] at hK; subst hK; simp [lo, hi]
  | node l r, ⟨hl, hr, he⟩, K, hK => by
    have := lo_le_hi l hl; have := lo_le_hi r hr
    simp only [subs, List.mem_cons, List.mem_append] at hK
    rcases hK with rfl | hK | hK
    · simp only [lo, hi]; omega
    · have := subs_bounds l hl K hK; simp only [lo, hi]; omega
    · have := subs_bounds r hr K hK; simp only [lo, hi]; omega

theorem subs_lam : ∀ t : Tree, t.WF → ∀ X ∈ t.subs, ∀ Y ∈ t.subs, Lam X Y
  | leaf i, _, X, hX, Y, hY => by
    simp [subs] at hX hY; subst hX; subst hY; unfold Lam; simp
  | node l r, ⟨hl, hr, he⟩, X, hX, Y, hY => by
    have bl := subs_bounds l hl; have br := subs_bounds r hr
    have := lo_le_hi l hl; have := lo_le_hi r hr
    simp only [subs, List.mem_cons, List.mem_append] at hX hY
    unfold Lam
    rcases hX with rfl | hX | hX <;> rcases hY with rfl | hY | hY
    · simp
    · have := bl Y hY; omega
    · have := br Y hY; omega
    · have := bl X hX; omega
    · exact subs_lam l hl X hX Y hY
    · have := bl X hX; have := br Y hY; omega
    · have := br X hX; omega
    · have := br X hX; have := bl Y hY; omega
    · exact subs_lam r hr X hX Y hY

theorem mem_node {l r : Tree} {K : Ival} :
    K ∈ (node l r).subs ↔ K = (l.lo, r.hi) ∨ K ∈ l.subs ∨ K ∈ r.subs := by
  simp [subs]

end Tree

open Tree

/-- A rotation, recording the spans of the three moved subtrees. -/
inductive Rot : Tree → Tree → Ival → Ival → Ival → Prop
  | lr (A B C : Tree) : Rot (node (node A B) C) (node A (node B C)) A.span B.span C.span
  | rl (A B C : Tree) : Rot (node A (node B C)) (node (node A B) C) A.span B.span C.span
  | inl {l l' : Tree} (r : Tree) {X Y Z : Ival} : Rot l l' X Y Z → Rot (node l r) (node l' r) X Y Z
  | inr (l : Tree) {r r' : Tree} {X Y Z : Ival} : Rot r r' X Y Z → Rot (node l r) (node l r') X Y Z

/-- What a rotation does to the node set: one span `del` is removed and one span `cre` is added. -/
structure RotFacts (t t' : Tree) (X Y Z : Ival) : Prop where
  wf : t'.WF
  lo : t'.lo = t.lo
  hi : t'.hi = t.hi
  hX : X.1 ≤ X.2
  hY : Y.1 = X.2 + 1 ∧ Y.1 ≤ Y.2
  hZ : Z.1 = Y.2 + 1 ∧ Z.1 ≤ Z.2
  mem : X ∈ t.subs ∧ Y ∈ t.subs ∧ Z ∈ t.subs ∧ (X.1, Z.2) ∈ t.subs
  dc : ∃ del cre : Ival, ((del = (X.1, Y.2) ∧ cre = (Y.1, Z.2)) ∨ (del = (Y.1, Z.2) ∧ cre = (X.1, Y.2))) ∧
        cre ∈ t'.subs ∧ ∀ K ∈ t.subs, K ≠ del → K ∈ t'.subs

theorem rot_facts : ∀ {t t' : Tree} {X Y Z : Ival}, Rot t t' X Y Z → t.WF → RotFacts t t' X Y Z
  | _, _, _, _, _, Rot.lr A B C, ⟨⟨hA, hB, hAB⟩, hC, hBC⟩ => by
    have := lo_le_hi A hA; have := lo_le_hi B hB; have := lo_le_hi C hC
    refine ⟨⟨hA, ⟨hB, hC, ?_⟩, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hi] using hBC
    · simp [lo, hi] at hBC ⊢; omega
    · simpa [span] using lo_le_hi A hA
    · simp [span, lo, hi] at hAB hBC ⊢; omega
    · simp [span, lo, hi] at hAB hBC ⊢; omega
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_node, mem_node]
      · exact Or.inr (Or.inl (Or.inr (Or.inl (span_mem A))))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (span_mem B))))
      · exact Or.inr (Or.inr (span_mem C))
      · exact Or.inl rfl
    · refine ⟨(A.lo, B.hi), (B.lo, C.hi), Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [mem_node, mem_node]; exact Or.inr (Or.inr (Or.inl rfl))
      intro K hK hne
      rw [mem_node, mem_node] at hK
      rw [mem_node, mem_node]
      rcases hK with h | (h | h | h) | h
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  | _, _, _, _, _, Rot.rl A B C, ⟨hA, ⟨hB, hC, hBC⟩, hAB⟩ => by
    have := lo_le_hi A hA; have := lo_le_hi B hB; have := lo_le_hi C hC
    refine ⟨⟨⟨hA, hB, ?_⟩, hC, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lo] using hAB
    · simpa [lo, hi] using hBC
    · simpa [span] using lo_le_hi A hA
    · simp [span, lo, hi] at hAB hBC ⊢; omega
    · simp [span, lo, hi] at hAB hBC ⊢; omega
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_node, mem_node]
      · exact Or.inr (Or.inl (span_mem A))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (span_mem B))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (span_mem C))))
      · exact Or.inl rfl
    · refine ⟨(B.lo, C.hi), (A.lo, B.hi), Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [mem_node, mem_node]; exact Or.inr (Or.inl (Or.inl rfl))
      intro K hK hne
      rw [mem_node, mem_node] at hK
      rw [mem_node, mem_node]
      rcases hK with h | h | (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
      · exact absurd h hne
      · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr h)
  | _, _, _, _, _, Rot.inl r h, ⟨hl, hr, he⟩ => by
    have f := rot_facts h hl
    refine ⟨⟨f.wf, hr, by rw [f.hi]; exact he⟩, by simp [lo, f.lo], rfl, f.hX, f.hY, f.hZ, ?_, ?_⟩
    · obtain ⟨m1, m2, m3, m4⟩ := f.mem
      exact ⟨by simp [subs, m1], by simp [subs, m2], by simp [subs, m3], by simp [subs, m4]⟩
    · obtain ⟨del, cre, hdc, hcre, hK⟩ := f.dc
      refine ⟨del, cre, hdc, by simp [subs, hcre], ?_⟩
      intro K hKm hne
      simp only [subs, List.mem_cons, List.mem_append, lo, f.lo] at hKm ⊢
      rcases hKm with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hK K h hne))
      · exact Or.inr (Or.inr h)
  | _, _, _, _, _, Rot.inr l h, ⟨hl, hr, he⟩ => by
    have f := rot_facts h hr
    refine ⟨⟨hl, f.wf, by rw [f.lo]; exact he⟩, rfl, by simp [hi, f.hi], f.hX, f.hY, f.hZ, ?_, ?_⟩
    · obtain ⟨m1, m2, m3, m4⟩ := f.mem
      exact ⟨by simp [subs, m1], by simp [subs, m2], by simp [subs, m3], by simp [subs, m4]⟩
    · obtain ⟨del, cre, hdc, hcre, hK⟩ := f.dc
      refine ⟨del, cre, hdc, by simp [subs, hcre], ?_⟩
      intro K hKm hne
      simp only [subs, List.mem_cons, List.mem_append, hi, f.hi] at hKm ⊢
      rcases hKm with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (hK K h hne))

/-- a `D_N`-flip: a rotation whose segment triple has `det = 0` (rank ≤ 2 for three letters) -/
def DNStep (w : Word) (t t' : Tree) : Prop :=
  ∃ X Y Z, Rot t t' X Y Z ∧ det3 (cnt w X) (cnt w Y) (cnt w Z) = 0

inductive Reach (R : Tree → Tree → Prop) : Tree → Tree → Prop
  | refl (t : Tree) : Reach R t t
  | tail {t u v : Tree} : Reach R t u → R u v → Reach R t v

/-- **Lemma R′.** If `S ⊆ subs T₀` is self-certifying, every tree reachable from `T₀` by `D_N`-flips
contains `S`. -/
theorem stable_of_reach (w : Word) (S : List Ival) (T0 : Tree) (hwf : T0.WF)
    (hS : ∀ J ∈ S, J ∈ T0.subs) (hcert : SelfCert w T0.span S) :
    ∀ T, Reach (DNStep w) T0 T → T.WF ∧ T.span = T0.span ∧ ∀ J ∈ S, J ∈ T.subs := by
  intro T hr
  induction hr with
  | refl => exact ⟨hwf, rfl, hS⟩
  | @tail u v _ hstep ih =>
    obtain ⟨hwu, hspan, hSu⟩ := ih
    obtain ⟨X, Y, Z, hrot, hdet⟩ := hstep
    have f := rot_facts hrot hwu
    refine ⟨f.wf, by simp [span, f.lo, f.hi]; simpa [span] using hspan, ?_⟩
    obtain ⟨del, cre, hdc, hcre, hkeep⟩ := f.dc
    intro J hJ
    by_cases hJd : J = del
    · exfalso
      subst hJd
      have hb := subs_bounds u hwu
      obtain ⟨m1, m2, m3, m4⟩ := f.mem
      have hXb := hb X m1; have hZb := hb Z m3
      have hlam : ∀ K ∈ S, Lam (X.1, X.2) K ∧ Lam (X.2 + 1, Y.2) K ∧ Lam (Y.2 + 1, Z.2) K ∧ Lam (X.1, Z.2) K := by
        intro K hK
        have hKu := hSu K hK
        have e1 : (X.2 + 1, Y.2) = Y := by rw [← f.hY.1]
        have e2 : (Y.2 + 1, Z.2) = Z := by rw [← f.hZ.1]
        rw [e1, e2]
        exact ⟨subs_lam u hwu _ m1 K hKu, subs_lam u hwu _ m2 K hKu, subs_lam u hwu _ m3 K hKu,
          subs_lam u hwu _ m4 K hKu⟩
      have hcreLam : ∀ K ∈ S, K ≠ J → Lam cre K := fun K hK hne =>
        subs_lam v f.wf _ hcre K (hkeep K (hSu K hK) hne)
      have := hcert J hJ X.1 X.2 Y.2 Z.2 f.hX (by have := f.hY; omega) (by have := f.hZ; omega)
        (by rw [← hspan]; simp [span]; exact hXb.1) (by rw [← hspan]; simp [span]; exact hZb.2.1) hlam
      apply this
      · rcases hdc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨h1.symm, ?_⟩
          intro K hK hne
          have := hcreLam K hK hne
          rw [h2, f.hY.1] at this; exact this
        · refine Or.inr ⟨by rw [h1, f.hY.1], ?_⟩
          intro K hK hne
          have := hcreLam K hK hne
          rw [h2] at this; exact this
      · have e1 : (X.2 + 1, Y.2) = Y := by rw [← f.hY.1]
        have e2 : (Y.2 + 1, Z.2) = Z := by rw [← f.hZ.1]
        rw [e1, e2]; exact hdet
    · exact hkeep J (hSu J hJ) hJd

/-- **Separation.** A tree missing a node of a self-certifying `S ⊆ subs T₀` lies in a different
`D_N`-component from `T₀`. -/
theorem separated (w : Word) (S : List Ival) (T0 T1 : Tree) (hwf : T0.WF)
    (hS : ∀ J ∈ S, J ∈ T0.subs) (hcert : SelfCert w T0.span S) (J : Ival) (hJ : J ∈ S)
    (hmiss : J ∉ T1.subs) : ¬ Reach (DNStep w) T0 T1 :=
  fun hr => hmiss ((stable_of_reach w S T0 hwf hS hcert T1 hr).2.2 J hJ)

/-- **Lemma Cat + Lemma R′.** A caterpillar chain from the root of `T₀` whose nodes are nodes of `T₀`
separates `T₀` from every tree that misses one of them. -/
theorem caterpillar_separates (w : Word) (T0 T1 : Tree) (hwf : T0.WF) (L : List (Ival × L3))
    (hL : PChain w T0.span L) (hS : ∀ x ∈ L, x.1 ∈ T0.subs) (x : Ival × L3) (hx : x ∈ L)
    (hmiss : x.1 ∉ T1.subs) : ¬ Reach (DNStep w) T0 T1 :=
  separated w (L.map Prod.fst) T0 T1 hwf
    (fun J hJ => by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hJ; exact hS y hy)
    (chain_selfCert w T0.span L hL) x.1 (List.mem_map_of_mem _ hx) hmiss

end Caterpillar
