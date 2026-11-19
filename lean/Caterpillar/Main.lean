import Caterpillar.WExist
import Caterpillar.Glue

/-!
# The main theorem, closed

A word is a list `wl` of letters (natural numbers); its bracketings are trees with leaf list
`0, 1, …, n−1`; two bracketings are in one *kernel class* when they are equal octonion maps; a kernel
class is *flip-connected* when any two of its members are joined by flips that keep the map (`KerConn`).

**`main`**: `KerConn (wd wl) wl.length ↔ TwoLetters wl ∨ Interval wl`.

* "if", interval words: renumber the letters by run index (`rk`, monotone) and apply
  `Closure.kernel_flip_connected`; kernel classes transfer along the renumbering (`ker_tr`, `kerflip_tr`).
* "if", two letters: `Closure.kernel_flip_connected_two`.
* "only if": a non-interval pattern `a … b … a` and a third letter `c`; kill every other letter (K);
  read the three-letter subword as a word over `L3`, take the G3 caterpillar pair (`g3_trees`); move it to
  octonion bracketings (`cmouf`, `reach_bridge`, `relab`, `rn_reach`); lift it back (`lift_separates`).
  The lifted pair are equal maps (Moufang, `mouf_ev`) in different `D_N`-components, and by
  `WExist.kerreach_dn` map-preserving flips are `D_N`-flips, so their kernel class is not flip-connected.
-/

namespace MainThm
open Caterpillar (Tree L3 AllThree runSeq)
open Octonion

def wd (wl : List Nat) (p : Nat) : Nat := wl.getD p 0

theorem getD_eq {α : Type} (l : List α) (d : α) {n : Nat} (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- every letter occupies one contiguous run -/
def Interval (wl : List Nat) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → k < wl.length → wd wl i = wd wl k → wd wl j = wd wl i

def TwoLetters (wl : List Nat) : Prop := ∃ a c, ∀ x ∈ wl, x = a ∨ x = c

/-- every kernel class of bracketings of `0, …, n−1` is connected by map-preserving flips -/
def KerConn (w : Nat → Nat) (n : Nat) : Prop :=
  ∀ T T' : Tree, lv T = List.range n → lv T' = List.range n → (∀ ρ : Nat → O, ev w ρ T = ev w ρ T') →
    DReach (Closure.KerFlip w) T T'

/-! ## transfer of kernel classes along letter maps -/

theorem ev_tr (w w' : Nat → Nat) (ρ ρ' : Nat → O) : ∀ T : Tree, (∀ t ∈ lv T, ρ (w t) = ρ' (w' t)) →
    ev w ρ T = ev w' ρ' T
  | .leaf i, h => h i (by simp [lv])
  | .node l r, h => by
    simp only [ev, ev_tr w w' ρ ρ' l (fun t ht => h t (by simp [lv, ht])),
      ev_tr w w' ρ ρ' r (fun t ht => h t (by simp [lv, ht]))]

theorem ker_tr (w w' : Nat → Nat) (n : Nat) (hww : ∀ p q, p < n → q < n → w' p = w' q → w p = w q)
    (T U : Tree) (hT : ∀ t ∈ lv T, t < n) (hU : ∀ t ∈ lv U, t < n) (h : ∀ ρ, ev w' ρ T = ev w' ρ U) :
    ∀ ρ, ev w ρ T = ev w ρ U := by
  intro ρ
  let ρ' : Nat → O := fun m => if hh : ∃ p, p < n ∧ w' p = m then ρ (w (Classical.choose hh)) else zero
  have key : ∀ t, t < n → ρ (w t) = ρ' (w' t) := by
    intro t ht
    have hh : ∃ p, p < n ∧ w' p = w' t := ⟨t, ht, rfl⟩
    show ρ (w t) = dite _ _ _
    rw [dif_pos hh]
    obtain ⟨h1, h2⟩ := Classical.choose_spec hh
    rw [hww _ _ h1 ht h2]
  rw [ev_tr w w' ρ ρ' T (fun t ht => key t (hT t ht)), ev_tr w w' ρ ρ' U (fun t ht => key t (hU t ht)), h ρ']

theorem flip_lv {T U : Tree} (h : Closure.FlipStep T U) : lv T = lv U := by
  cases h with
  | fwd c A B C => exact lv_fill (by simp [lv]) c
  | bwd c A B C => exact lv_fill (by simp [lv]) c

theorem kerflip_tr (w w' : Nat → Nat) (n : Nat) (hww : ∀ p q, p < n → q < n → w' p = w' q → w p = w q)
    {T T' : Tree} (h : DReach (Closure.KerFlip w') T T') (hT : ∀ t ∈ lv T, t < n) :
    DReach (Closure.KerFlip w) T T' := by
  have : (∀ t ∈ lv T', t < n) ∧ DReach (Closure.KerFlip w) T T' := by
    induction h with
    | refl => exact ⟨hT, DReach.refl _⟩
    | tail _ st ih =>
      obtain ⟨hU, r⟩ := ih
      have e := flip_lv st.1
      have hV : ∀ t ∈ lv _, t < n := fun t ht => hU t (by rw [e]; exact ht)
      exact ⟨hV, DReach.tail r ⟨st.1, ker_tr w w' n hww _ _ hU hV st.2⟩⟩
  exact this.2

/-! ## renumbering an interval word by runs -/

def rk (wl : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => rk wl i + (if i + 1 < wl.length ∧ wd wl (i + 1) ≠ wd wl i then 1 else 0)

theorem rk_le (wl : List Nat) (p : Nat) : ∀ d, rk wl p ≤ rk wl (p + d)
  | 0 => Nat.le_refl _
  | d + 1 => by
    have := rk_le wl p d
    show rk wl p ≤ rk wl (p + d + 1)
    simp only [rk]; split <;> omega

theorem rk_mono (wl : List Nat) : MonoW (rk wl) := by
  intro i j h; obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; exact rk_le wl i d

theorem rk_eq_iff (wl : List Nat) (p : Nat) : ∀ d, rk wl p = rk wl (p + d) ↔
    ∀ i, p < i → i ≤ p + d → i < wl.length → wd wl i = wd wl (i - 1)
  | 0 => ⟨fun _ i h1 h2 _ => absurd h2 (by omega), fun _ => rfl⟩
  | d + 1 => by
    have ih := rk_eq_iff wl p d
    have hle := rk_le wl p d
    show rk wl p = rk wl (p + d + 1) ↔ _
    simp only [rk]
    constructor
    · intro h
      split at h
      · omega
      · next hc =>
        have h' : rk wl p = rk wl (p + d) := by omega
        intro i h1 h2 h3
        by_cases hi : i ≤ p + d
        · exact ih.1 h' i h1 hi h3
        · have e : i = p + d + 1 := by omega
          subst e
          rw [Nat.add_sub_cancel]
          exact Classical.byContradiction fun hne => hc ⟨h3, hne⟩
    · intro h
      have h1 := ih.2 (fun i a b c => h i a (by omega) c)
      split
      · next hc => exact absurd (by have := h (p + d + 1) (by omega) (Nat.le_refl _) hc.1; rwa [Nat.add_sub_cancel] at this) hc.2
      · omega

theorem run_const (wl : List Nat) (p q : Nat) (h : ∀ i, p < i → i ≤ q → i < wl.length → wd wl i = wd wl (i - 1))
    (hq : q < wl.length) : ∀ d, p + d ≤ q → wd wl (p + d) = wd wl p
  | 0, _ => rfl
  | d + 1, hd => by
    rw [← run_const wl p q h hq d (by omega), show p + (d + 1) = p + d + 1 by omega]
    have := h (p + d + 1) (by omega) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this

theorem rk_iff (wl : List Nat) (hI : Interval wl) (p q : Nat) (hp : p < wl.length) (hq : q < wl.length) :
    rk wl p = rk wl q ↔ wd wl p = wd wl q := by
  have main : ∀ p q, p ≤ q → q < wl.length → (rk wl p = rk wl q ↔ wd wl p = wd wl q) := by
    intro p q hpq hq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [rk_eq_iff]
    constructor
    · intro h; exact (run_const wl p (p + d) h hq d (Nat.le_refl _)).symm
    · intro he i h1 h2 h3
      rw [hI p i (p + d) (by omega) h2 hq he, hI p (i - 1) (p + d) (by omega) (by omega) hq he]
  rcases Nat.le_total p q with h | h
  · exact main p q h hq
  · rw [eq_comm, @eq_comm _ (wd wl p)]; exact main q p h hp

theorem bnd {n : Nat} {U : Tree} (hU : lv U = List.range n) : ∀ t ∈ lv U, t < n := by
  intro t ht; rw [hU, List.mem_range] at ht; exact ht

theorem kerconn_of_interval (wl : List Nat) (hI : Interval wl) : KerConn (wd wl) wl.length := by
  intro T T' hT hT' h
  have h' : ∀ ρ, ev (rk wl) ρ T = ev (rk wl) ρ T' :=
    ker_tr (rk wl) (wd wl) _ (fun p q hp hq e => (rk_iff wl hI p q hp hq).2 e) T T' (bnd hT) (bnd hT') h
  have r := Closure.kernel_flip_connected (rk wl) (rk_mono wl) T T' (hT.trans hT'.symm)
    (by rw [hT]; exact List.pairwise_lt_range _) h'
  exact kerflip_tr (wd wl) (rk wl) _ (fun p q hp hq e => (rk_iff wl hI p q hp hq).1 e) r (bnd hT)

theorem kerconn_of_two (wl : List Nat) (h2 : TwoLetters wl) : KerConn (wd wl) wl.length := by
  obtain ⟨a, c, hac⟩ := h2
  intro T T' hT hT' _
  refine (Closure.kernel_flip_connected_two (wd wl) a c T T' (hT.trans hT'.symm) ?_).2
  intro t ht
  have ht' := bnd hT t ht
  apply hac
  simp only [wd]; rw [getD_eq _ _ ht']; exact List.getElem_mem ht'

/-! ## run sequences: no repeated run means interval -/

theorem interval_of_nodup : ∀ l : List L3, (runSeq l).Nodup → ∀ i j k, i ≤ j → j ≤ k → k < l.length →
    l.getD i 0 = l.getD k 0 → l.getD j 0 = l.getD i 0
  | [], _, _, _, k, _, _, hk, _ => by simp at hk
  | [a], _, i, j, k, hij, hjk, hk, _ => by
    simp at hk; have : j = 0 := by omega
    have : i = 0 := by omega
    subst_vars; rfl
  | a :: x :: t, hn, i, j, k, hij, hjk, hk, he => by
    obtain ⟨r, hr⟩ := Caterpillar.runSeq_cons_head x t
    have ih := interval_of_nodup (x :: t)
    by_cases hax : a = x
    · subst hax
      have hn' : (runSeq (a :: t)).Nodup := by
        have : runSeq (a :: a :: t) = runSeq (a :: t) := by
          show (match runSeq (a :: t) with | [] => [a] | b :: r => if a = b then b :: r else a :: b :: r) = _
          rw [hr]; simp
        rw [this] at hn; exact hn
      have ih' := ih hn'
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          cases k with
          | zero => omega
          | succ k =>
            simp only [List.getD_cons_succ, List.getD_cons_zero] at he ⊢
            have := ih' 0 j k (by omega) (by omega) (by simp at hk ⊢; omega) (by simpa using he)
            simpa using this
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          cases k with
          | zero => omega
          | succ k =>
            simp only [List.getD_cons_succ] at he ⊢
            exact ih' i j k (by omega) (by omega) (by simp at hk ⊢; omega) he
    · have e : runSeq (a :: x :: t) = a :: runSeq (x :: t) := by
        show (match runSeq (x :: t) with | [] => [a] | b :: r => if a = b then b :: r else a :: b :: r) = _
        rw [hr]; simp [hax]
      rw [e, List.nodup_cons] at hn
      have hna : a ∉ x :: t := fun h => hn.1 ((Caterpillar.mem_runSeq _ a).2 h)
      cases i with
      | zero =>
        cases k with
        | zero => have : j = 0 := by omega
                  subst this; rfl
        | succ k =>
          simp only [List.getD_cons_succ, List.getD_cons_zero] at he
          exfalso; apply hna
          have hk' : k < (x :: t).length := by simp at hk ⊢; omega
          rw [he, getD_eq _ _ hk']; exact List.getElem_mem hk'
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          cases k with
          | zero => omega
          | succ k =>
            simp only [List.getD_cons_succ] at he ⊢
            exact ih hn.2 i j k (by omega) (by omega) (by simp at hk ⊢; omega) he

/-! ## from caterpillar words (letters `L3`, consecutive positions) to octonion bracketings -/

theorem cmouf {w3 : Caterpillar.Word} {T U : Tree} (h : Caterpillar.Mouf w3 T U) :
    Octonion.Mouf (fun p => (w3 p).val) T U := by
  induction h with
  | left x x' Y C h => exact Mouf.left x x' Y C (congrArg Fin.val h)
  | right x x' C Y h => exact Mouf.right x x' C Y (congrArg Fin.val h)
  | mid x x' B C h => exact Mouf.middle x x' B C (congrArg Fin.val h)
  | inl r _ ih => exact Mouf.inL r ih
  | inr l _ ih => exact Mouf.inR l ih

theorem fill_rot_f (A B C : Tree) : ∀ c : Ctx,
    Caterpillar.Rot (fill c (.node (.node A B) C)) (fill c (.node A (.node B C))) A.span B.span C.span
  | .hole => Caterpillar.Rot.lr A B C
  | .inL c R => Caterpillar.Rot.inl R (fill_rot_f A B C c)
  | .inR L c => Caterpillar.Rot.inr L (fill_rot_f A B C c)

theorem fill_rot_b (A B C : Tree) : ∀ c : Ctx,
    Caterpillar.Rot (fill c (.node A (.node B C))) (fill c (.node (.node A B) C)) A.span B.span C.span
  | .hole => Caterpillar.Rot.rl A B C
  | .inL c R => Caterpillar.Rot.inl R (fill_rot_b A B C c)
  | .inR L c => Caterpillar.Rot.inr L (fill_rot_b A B C c)

theorem wf_fill (X : Tree) : ∀ c : Ctx, (fill c X).WF → X.WF
  | .hole, h => h
  | .inL c _, h => by simp only [fill, Caterpillar.Tree.WF] at h; exact wf_fill X c h.1
  | .inR _ c, h => by simp only [fill, Caterpillar.Tree.WF] at h; exact wf_fill X c h.2.1

theorem cnt_wf (w3 : Caterpillar.Word) (ℓ : L3) : ∀ A : Tree, A.WF →
    Octonion.cnt (fun p => (w3 p).val) ℓ.val A = Caterpillar.cnt w3 A.span ℓ
  | .leaf i, _ => by
    simp only [Octonion.cnt, Caterpillar.cnt, Caterpillar.Tree.span, Caterpillar.Tree.lo, Caterpillar.Tree.hi,
      Nat.add_sub_cancel_left, Caterpillar.cntR]
    by_cases h : w3 i = ℓ
    · simp [h]
    · have : (w3 i).val ≠ ℓ.val := fun e => h (Fin.ext e)
      simp [h, this]
  | .node l r, h => by
    obtain ⟨hl, hr, he⟩ := h
    have h1 := cnt_wf w3 ℓ l hl; have h2 := cnt_wf w3 ℓ r hr
    have ll := Caterpillar.Tree.lo_le_hi l hl; have lr := Caterpillar.Tree.lo_le_hi r hr
    simp only [Caterpillar.cnt, Caterpillar.Tree.span, Caterpillar.Tree.lo, Caterpillar.Tree.hi] at h1 h2 ⊢
    simp only [Octonion.cnt, h1, h2]
    rw [show r.hi + 1 - l.lo = (l.hi + 1 - l.lo) + (r.hi + 1 - r.lo) by omega, Caterpillar.cntR_split,
      show l.lo + (l.hi + 1 - l.lo) = r.lo by omega]
    omega

theorem dn_bridge (w3 : Caterpillar.Word) {X Y : Tree} (h : DNStep (fun p => (w3 p).val) X Y) (hX : X.WF) :
    Y.WF ∧ Caterpillar.DNStep w3 X Y := by
  cases h with
  | fwd c A B C hd =>
    have hr := fill_rot_f A B C c
    have hw := wf_fill _ c hX
    simp only [Caterpillar.Tree.WF] at hw
    refine ⟨(Caterpillar.rot_facts hr hX).wf, A.span, B.span, C.span, hr, ?_⟩
    have := hd 0 1 2
    simp only [minor] at this
    simp only [Caterpillar.det3, ← cnt_wf w3 _ A hw.1.1, ← cnt_wf w3 _ B hw.1.2.1, ← cnt_wf w3 _ C hw.2.1]
    exact this
  | bwd c A B C hd =>
    have hr := fill_rot_b A B C c
    have hw := wf_fill _ c hX
    simp only [Caterpillar.Tree.WF] at hw
    refine ⟨(Caterpillar.rot_facts hr hX).wf, A.span, B.span, C.span, hr, ?_⟩
    have := hd 0 1 2
    simp only [minor] at this
    simp only [Caterpillar.det3, ← cnt_wf w3 _ A hw.1, ← cnt_wf w3 _ B hw.2.1.1, ← cnt_wf w3 _ C hw.2.1.2.1]
    exact this

theorem reach_bridge (w3 : Caterpillar.Word) {T U : Tree} (h : DReach (DNStep (fun p => (w3 p).val)) T U)
    (hT : T.WF) : Caterpillar.Reach (Caterpillar.DNStep w3) T U := by
  have : U.WF ∧ Caterpillar.Reach (Caterpillar.DNStep w3) T U := by
    induction h with
    | refl => exact ⟨hT, Caterpillar.Reach.refl _⟩
    | tail _ st ih =>
      obtain ⟨h1, r⟩ := ih
      obtain ⟨h2, s⟩ := dn_bridge w3 st h1
      exact ⟨h2, Caterpillar.Reach.tail r s⟩
  exact this.2

theorem lv_of_wf : ∀ T : Tree, T.WF → lv T = List.range' T.lo (T.hi + 1 - T.lo)
  | .leaf i, _ => by
    simp only [lv, Caterpillar.Tree.lo, Caterpillar.Tree.hi, Nat.add_sub_cancel_left]; rfl
  | .node l r, h => by
    obtain ⟨hl, hr, he⟩ := h
    have ll := Caterpillar.Tree.lo_le_hi l hl; have lr := Caterpillar.Tree.lo_le_hi r hr
    simp only [lv, Caterpillar.Tree.lo, Caterpillar.Tree.hi]
    rw [lv_of_wf l hl, lv_of_wf r hr, show r.lo = l.lo + (l.hi + 1 - l.lo) by omega, List.range'_append_1]
    congr 1; omega

/-! ## renumbering positions -/

def relab (S : List Nat) : Tree → Tree
  | .leaf i => .leaf (S.getD i 0)
  | .node l r => .node (relab S l) (relab S r)

theorem lv_relab (S : List Nat) : ∀ T, lv (relab S T) = (lv T).map (fun i => S.getD i 0)
  | .leaf _ => rfl
  | .node l r => by simp [relab, lv, lv_relab S l, lv_relab S r]

theorem map_getD_range (S : List Nat) : (List.range S.length).map (fun i => S.getD i 0) = S := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact getD_eq _ _ h2

theorem idx_getD (S : List Nat) (hp : S.Pairwise (· < ·)) (i : Nat) (hi : i < S.length) :
    G2Final.idx S (S.getD i 0) = i := by
  have h := List.getElem_of_eq (G2Final.map_idx S hp) (i := i) (by simpa using hi)
  simp only [List.getElem_map, List.getElem_range'] at h
  rw [getD_eq _ _ hi, h]; omega

theorem mem_get (S : List Nat) {t : Nat} (ht : t ∈ S) : ∃ i, i < S.length ∧ S.getD i 0 = t := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ht
  exact ⟨i, hi, by rw [getD_eq _ _ hi, e]⟩

theorem idx_mem (S : List Nat) (hp : S.Pairwise (· < ·)) {t : Nat} (ht : t ∈ S) :
    G2Final.idx S t < S.length ∧ S.getD (G2Final.idx S t) 0 = t := by
  obtain ⟨i, hi, rfl⟩ := mem_get S ht
  rw [idx_getD S hp i hi]; exact ⟨hi, rfl⟩

theorem rn_relab (S : List Nat) (hp : S.Pairwise (· < ·)) : ∀ T : Tree, (∀ i ∈ lv T, i < S.length) →
    G2Final.rn S (relab S T) = T
  | .leaf i, h => by
    simp only [relab, G2Final.rn]; rw [idx_getD S hp i (h i (by simp [lv]))]
  | .node l r, h => by
    simp only [relab, G2Final.rn]
    rw [rn_relab S hp l (fun i hi => h i (by simp [lv, hi])), rn_relab S hp r (fun i hi => h i (by simp [lv, hi]))]

def rnC (S : List Nat) : Ctx → Ctx
  | .hole => .hole
  | .inL c R => .inL (rnC S c) (G2Final.rn S R)
  | .inR L c => .inR (G2Final.rn S L) (rnC S c)

theorem rn_fill (S : List Nat) (X : Tree) : ∀ c, G2Final.rn S (fill c X) = fill (rnC S c) (G2Final.rn S X)
  | .hole => rfl
  | .inL c R => by simp only [fill, G2Final.rn, rnC, rn_fill S X c]
  | .inR L c => by simp only [fill, G2Final.rn, rnC, rn_fill S X c]

theorem cnt_rn (S : List Nat) (w w' : Nat → Nat) (ℓ' : Nat) (P : Prop) [Decidable P] (ℓ : Nat) :
    ∀ X : Tree, (∀ t ∈ lv X, (w' (G2Final.idx S t) = ℓ' ↔ (P ∧ w t = ℓ))) →
      cnt w' ℓ' (G2Final.rn S X) = if P then cnt w ℓ X else 0
  | .leaf t, h => by
    have e := h t (by simp [lv])
    simp only [G2Final.rn, cnt]
    by_cases hP : P <;> by_cases hw : w t = ℓ <;> simp_all
  | .node l r, h => by
    simp only [G2Final.rn, cnt]
    rw [cnt_rn S w w' ℓ' P ℓ l (fun t ht => h t (by simp [lv, ht])),
      cnt_rn S w w' ℓ' P ℓ r (fun t ht => h t (by simp [lv, ht]))]
    by_cases hP : P <;> simp [hP]

theorem dn_tr (w w' : Nat → Nat) (A B C A' B' C' : Tree) (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P]
    (hA : ∀ ℓ', cnt w' ℓ' A' = if P ℓ' then cnt w (f ℓ') A else 0)
    (hB : ∀ ℓ', cnt w' ℓ' B' = if P ℓ' then cnt w (f ℓ') B else 0)
    (hC : ∀ ℓ', cnt w' ℓ' C' = if P ℓ' then cnt w (f ℓ') C else 0)
    (h : DN w A B C) : DN w' A' B' C' := by
  intro p q r
  have hm := h (f p) (f q) (f r)
  simp only [minor] at hm ⊢
  simp only [hA, hB, hC]
  by_cases hp : P p <;> by_cases hq : P q <;> by_cases hr : P r <;> simp only [hp, hq, hr, if_true, if_false] <;>
    first | exact hm | simp

/-! ## three letters `a, b, c` -/

def code (a b : Nat) (ℓ : Nat) : L3 := if ℓ = a then 0 else if ℓ = b then 1 else 2
def dec (a b c : Nat) (ℓ' : Nat) : Nat := if ℓ' = 0 then a else if ℓ' = 1 then b else c
def Kset (a b c : Nat) (ℓ : Nat) : Bool := !(decide (ℓ = a ∨ ℓ = b ∨ ℓ = c))

theorem code_dec (a b c : Nat) (hab : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (x : Nat)
    (hx : x = a ∨ x = b ∨ x = c) (ℓ' : Nat) : (code a b x).val = ℓ' ↔ (ℓ' < 3 ∧ x = dec a b c ℓ') := by
  by_cases h3 : ℓ' < 3
  · rcases (show ℓ' = 0 ∨ ℓ' = 1 ∨ ℓ' = 2 by omega) with rfl | rfl | rfl <;>
      rcases hx with rfl | rfl | rfl <;> simp [code, dec, hab, hca, hcb, Ne.symm hab, Ne.symm hca, Ne.symm hcb]
  · have := (code a b x).isLt
    constructor
    · intro e; omega
    · intro e; omega

theorem code_inj (a b c : Nat) (hab : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (x y : Nat)
    (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) (h : (code a b x).val = (code a b y).val) : x = y := by
  have := (code_dec a b c hab hca hcb x hx _).1 h
  have := (code_dec a b c hab hca hcb y hy _).1 rfl
  omega

theorem mouf_lv {w : Nat → Nat} {T U : Tree} (h : Mouf w T U) : lv T = lv U := by
  induction h with
  | left => simp [lv]
  | right => simp [lv]
  | middle => simp [lv]
  | inL _ _ ih => simp [lv, ih]
  | inR _ _ ih => simp [lv, ih]

/-- **Moufang moves are equal maps.** -/
theorem mouf_ev {w : Nat → Nat} {T U : Tree} (h : Mouf w T U) (ρ : Nat → O) : ev w ρ T = ev w ρ U := by
  induction h with
  | left x x1 Y C hx => simp only [ev, hx]; exact moufang_left _ _ _
  | right x x1 C Y hx => simp only [ev, hx]; exact moufang_right _ _ _
  | middle x x1 B C hx => simp only [ev, hx]; exact (moufang_middle _ _ _).symm
  | inL r _ ih => simp only [ev, ih]
  | inR l _ ih => simp only [ev, ih]

theorem mouf_relab (S : List Nat) (w w3n : Nat → Nat) (m : Nat)
    (hinj : ∀ x y, x < m → y < m → w3n x = w3n y → w (S.getD x 0) = w (S.getD y 0))
    {T U : Tree} (h : Mouf w3n T U) : (∀ t ∈ lv T, t < m) → Mouf w (relab S T) (relab S U) := by
  induction h with
  | left x x1 Y C hx =>
    intro hb; exact Mouf.left _ _ _ _ (hinj x x1 (hb x (by simp [lv])) (hb x1 (by simp [lv])) hx)
  | right x x1 C Y hx =>
    intro hb; exact Mouf.right _ _ _ _ (hinj x x1 (hb x (by simp [lv])) (hb x1 (by simp [lv])) hx)
  | middle x x1 B C hx =>
    intro hb; exact Mouf.middle _ _ _ _ (hinj x x1 (hb x (by simp [lv])) (hb x1 (by simp [lv])) hx)
  | inL r _ ih => intro hb; exact Mouf.inL _ (ih (fun t ht => hb t (by simp [lv, ht])))
  | inR l _ ih => intro hb; exact Mouf.inR _ (ih (fun t ht => hb t (by simp [lv, ht])))

theorem dnstep_lv {w : Nat → Nat} {X Y : Tree} (h : DNStep w X Y) : lv X = lv Y := by
  cases h with
  | fwd c A B C _ => exact lv_fill (by simp [lv]) c
  | bwd c A B C _ => exact lv_fill (by simp [lv]) c

/-- `D_N`-steps on the surviving positions renumber to `D_N`-steps of the three-letter word -/
theorem rn_reach (S : List Nat) (w w3n : Nat → Nat) (f : Nat → Nat)
    (hcnt : ∀ X : Tree, (∀ t ∈ lv X, t ∈ S) → ∀ ℓ', cnt w3n ℓ' (G2Final.rn S X) = if ℓ' < 3 then cnt w (f ℓ') X else 0)
    {T U : Tree} (h : DReach (DNStep w) T U) (hT : ∀ t ∈ lv T, t ∈ S) :
    DReach (DNStep w3n) (G2Final.rn S T) (G2Final.rn S U) := by
  have : lv U = lv T ∧ DReach (DNStep w3n) (G2Final.rn S T) (G2Final.rn S U) := by
    induction h with
    | refl => exact ⟨rfl, DReach.refl _⟩
    | tail _ st ih =>
      obtain ⟨e, r⟩ := ih
      refine ⟨(dnstep_lv st).symm.trans e, DReach.tail r ?_⟩
      have hX : ∀ t ∈ lv _, t ∈ S := fun t ht => hT t (by rw [← e]; exact ht)
      cases st with
      | fwd c A B C hd =>
        have sub := (dnstep_sig.sublist_fill c (.node (.node A B) C)).subset
        have hs : ∀ V : Tree, (∀ t ∈ lv V, t ∈ lv (.node (.node A B) C)) → ∀ t ∈ lv V, t ∈ S :=
          fun V hV t ht => hX t (sub (hV t ht))
        rw [rn_fill, rn_fill]
        exact DNStep.fwd _ _ _ _ (dn_tr w w3n A B C _ _ _ f (· < 3)
          (hcnt A (hs A (fun t ht => by simp [lv, ht]))) (hcnt B (hs B (fun t ht => by simp [lv, ht])))
          (hcnt C (hs C (fun t ht => by simp [lv, ht]))) hd)
      | bwd c A B C hd =>
        have sub := (dnstep_sig.sublist_fill c (.node A (.node B C))).subset
        have hs : ∀ V : Tree, (∀ t ∈ lv V, t ∈ lv (.node A (.node B C))) → ∀ t ∈ lv V, t ∈ S :=
          fun V hV t ht => hX t (sub (hV t ht))
        rw [rn_fill, rn_fill]
        exact DNStep.bwd _ _ _ _ (dn_tr w w3n A B C _ _ _ f (· < 3)
          (hcnt A (hs A (fun t ht => by simp [lv, ht]))) (hcnt B (hs B (fun t ht => by simp [lv, ht])))
          (hcnt C (hs C (fun t ht => by simp [lv, ht]))) hd)
  exact this.2

/-! ## the "only if" direction -/

theorem not_kerconn (wl : List Nat) (h2 : ¬ TwoLetters wl) (hI : ¬ Interval wl) :
    ¬ KerConn (wd wl) wl.length := by
  intro hK
  obtain ⟨i, j, k, hij, hjk, hk, hik, hji⟩ : ∃ i j k, i ≤ j ∧ j ≤ k ∧ k < wl.length ∧
      wd wl i = wd wl k ∧ wd wl j ≠ wd wl i := by
    apply Classical.byContradiction; intro hn; apply hI; intro i j k a b c d
    exact Classical.byContradiction fun e => hn ⟨i, j, k, a, b, c, d, e⟩
  generalize ha : wd wl i = a at hik hji
  generalize hb : wd wl j = b at hji
  obtain ⟨m, hm, hma, hmb⟩ : ∃ m, m < wl.length ∧ wd wl m ≠ a ∧ wd wl m ≠ b := by
    apply Classical.byContradiction; intro hn; apply h2; refine ⟨a, b, ?_⟩; intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hx
    have e : wd wl m = wl[m] := getD_eq _ _ hm
    by_cases h1 : wl[m] = a
    · exact Or.inl h1
    by_cases h1' : wl[m] = b
    · exact Or.inr h1'
    exact absurd ⟨m, hm, by rw [e]; exact h1, by rw [e]; exact h1'⟩ hn
  generalize hc : wd wl m = c at hma hmb
  -- the surviving positions
  let w := wd wl
  let n := wl.length
  let K := Kset a b c
  let S := (List.range n).filter (alive w K)
  have hS : ∀ t, t ∈ S ↔ t < n ∧ (w t = a ∨ w t = b ∨ w t = c) := by
    intro t; simp [S, List.mem_filter, alive, K, Kset]
  have hSp : S.Pairwise (· < ·) := (List.pairwise_lt_range n).sublist (List.filter_sublist _)
  have hiS : i ∈ S := (hS i).2 ⟨by omega, Or.inl ha⟩
  have hjS : j ∈ S := (hS j).2 ⟨by omega, Or.inr (Or.inl hb)⟩
  have hkS : k ∈ S := (hS k).2 ⟨hk, Or.inl hik.symm⟩
  have hmS : m ∈ S := (hS m).2 ⟨hm, Or.inr (Or.inr hc)⟩
  have hij' : i < j := by
    rcases Nat.lt_or_eq_of_le hij with h | h
    · exact h
    · subst h; exact absurd (ha.symm.trans hb) (Ne.symm hji)
  have hjk' : j < k := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · exact h
    · subst h; exact absurd (hb.symm.trans hik.symm) hji
  -- the three-letter word
  let wl3 : List L3 := S.map (fun t => code a b (w t))
  let w3 : Caterpillar.Word := fun p => wl3.getD p 0
  let w3n : Nat → Nat := fun p => (w3 p).val
  have hlen : wl3.length = S.length := List.length_map _ _
  have hw3x : ∀ x, x < S.length → w3 x = code a b (w (S.getD x 0)) := by
    intro x hx
    show wl3.getD x 0 = _
    rw [getD_eq _ _ (by rw [hlen]; exact hx), List.getElem_map, getD_eq _ _ hx]
  have hw3 : ∀ t ∈ S, w3 (G2Final.idx S t) = code a b (w t) := by
    intro t ht; obtain ⟨h1, h2⟩ := idx_mem S hSp ht; rw [hw3x _ h1, h2]
  have hletS : ∀ t ∈ S, w t = a ∨ w t = b ∨ w t = c := fun t ht => ((hS t).1 ht).2
  have h3 : AllThree wl3 := by
    intro c'
    rcases c' with ⟨v, hv⟩
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl
    · exact List.mem_map.2 ⟨i, hiS, by show code a b (wd wl i) = _; rw [ha]; simp [code]⟩
    · exact List.mem_map.2 ⟨j, hjS, by show code a b (wd wl j) = _; rw [hb]; simp [code, hji]⟩
    · exact List.mem_map.2 ⟨m, hmS, by show code a b (wd wl m) = _; rw [hc]; simp [code, hma, hmb]⟩
  have hni : ¬ (runSeq wl3).Nodup := by
    intro hn
    obtain ⟨li, ei⟩ := idx_mem S hSp hiS
    obtain ⟨lk, ek⟩ := idx_mem S hSp hkS
    have := interval_of_nodup wl3 hn (G2Final.idx S i) (G2Final.idx S j) (G2Final.idx S k)
      (Nat.le_of_lt (G2Final.idx_lt S hSp i hiS j hjS hij')) (Nat.le_of_lt (G2Final.idx_lt S hSp j hjS k hkS hjk'))
      (by rw [hlen]; exact lk)
      (by show w3 _ = w3 _; rw [hw3 i hiS, hw3 k hkS]; show code a b (wd wl i) = code a b (wd wl k); rw [ha, ← hik])
    change w3 _ = w3 _ at this
    rw [hw3 j hjS, hw3 i hiS] at this
    change code a b (wd wl j) = code a b (wd wl i) at this
    rw [hb, ha] at this
    simp [code, hji] at this
  -- G3 on the three-letter word
  obtain ⟨T0, T1, hwf, hlo, hhi, hmc, hsepc⟩ := Caterpillar.g3_trees wl3 h3 hni
  have hS3 : 3 ≤ S.length := by
    have := G2Final.idx_lt S hSp j hjS k hkS hjk'
    have := G2Final.idx_lt S hSp i hiS j hjS hij'
    have := (idx_mem S hSp hkS).1
    omega
  have hlv0 : lv T0 = List.range S.length := by
    rw [lv_of_wf T0 hwf, hlo, hhi, hlen, List.range_eq_range']; congr 1; omega
  have hm3 : Mouf w3n T0 T1 := cmouf hmc
  have hsep3 : ¬ DReach (DNStep w3n) T0 T1 := fun r => hsepc (reach_bridge w3 r hwf)
  have hlv1 : lv T1 = List.range S.length := (mouf_lv hm3).symm.trans hlv0
  -- back to the surviving positions of the original word
  have hb0 : ∀ t ∈ lv T0, t < S.length := bnd hlv0
  have hb1 : ∀ t ∈ lv T1, t < S.length := bnd hlv1
  have hinj : ∀ x y, x < S.length → y < S.length → w3n x = w3n y → w (S.getD x 0) = w (S.getD y 0) := by
    intro x y hx hy e
    have hx' : S.getD x 0 ∈ S := by rw [getD_eq _ _ hx]; exact List.getElem_mem hx
    have hy' : S.getD y 0 ∈ S := by rw [getD_eq _ _ hy]; exact List.getElem_mem hy
    have e' : (code a b (w (S.getD x 0))).val = (code a b (w (S.getD y 0))).val := by
      have := e; simp only [w3n] at this; rw [hw3x x hx, hw3x y hy] at this; exact this
    exact code_inj a b c hji hma hmb _ _ (hletS _ hx') (hletS _ hy') e'
  have hm' : Mouf w (relab S T0) (relab S T1) := mouf_relab S w w3n S.length hinj hm3 hb0
  have hlvS : lv (relab S T0) = S := by rw [lv_relab, hlv0, map_getD_range]
  have hlvS1 : lv (relab S T1) = S := by rw [lv_relab, hlv1, map_getD_range]
  have hcnt : ∀ X : Tree, (∀ t ∈ lv X, t ∈ S) → ∀ ℓ', cnt w3n ℓ' (G2Final.rn S X) =
      if ℓ' < 3 then cnt w (dec a b c ℓ') X else 0 := by
    intro X hX ℓ'
    apply cnt_rn
    intro t ht
    have htS := hX t ht
    show (w3 (G2Final.idx S t)).val = ℓ' ↔ _
    rw [hw3 t htS]
    exact code_dec a b c hji hma hmb _ (hletS t htS) ℓ'
  have hsep' : ¬ DReach (DNStep w) (relab S T0) (relab S T1) := by
    intro r
    have := rn_reach S w w3n (dec a b c) hcnt r (fun t ht => by rw [hlvS] at ht; exact ht)
    rw [rn_relab S hSp T0 hb0, rn_relab S hSp T1 hb1] at this
    exact hsep3 this
  -- lift to all positions (K)
  obtain ⟨U0, U1, e0, _, _, hmU, hsepU⟩ := lift_separates w K hm' hsep' (List.range n) hlvS.symm
  have e1 : lv U1 = List.range n := (mouf_lv hmU).symm.trans e0
  exact hsepU (WExist.kerreach_dn w (hK U0 U1 e0 e1 (mouf_ev hmU)))

/-- **Main theorem.** In the octonions every kernel class of bracketings of `wl` is flip-connected iff
`wl` has at most two distinct letters or every letter occupies one contiguous run. -/
theorem main (wl : List Nat) : KerConn (wd wl) wl.length ↔ TwoLetters wl ∨ Interval wl := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    exact not_kerconn wl (fun h2 => hn (Or.inl h2)) (fun hI => hn (Or.inr hI)) h
  · rintro (h | h)
    · exact kerconn_of_two wl h
    · exact kerconn_of_interval wl h

end MainThm
