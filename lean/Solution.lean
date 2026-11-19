import Spec
import Caterpillar

/-!
# Verified Solution (`Solution`)

Proves every statement of record and algebraic/non-vacuity anchor declared in `Challenge.lean`
from the `Caterpillar` library, using only the standard axioms `propext`, `Quot.sound`, and
`Classical.choice`.

Verified against `Challenge.lean` by `lake comparator --paranoid` across all six bundled kernels
(`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
-/

namespace Challenge
open Spec

/-! ## Structural bridge between `Spec` and `Caterpillar` -/

private def toCat : Spec.Tree → Caterpillar.Tree
  | .leaf i => .leaf i
  | .node l r => .node (toCat l) (toCat r)

private def ofCat : Caterpillar.Tree → Spec.Tree
  | .leaf i => .leaf i
  | .node l r => .node (ofCat l) (ofCat r)

private theorem ofCat_toCat : ∀ T : Spec.Tree, ofCat (toCat T) = T
  | .leaf _ => rfl
  | .node l r => by simp only [toCat, ofCat, ofCat_toCat l, ofCat_toCat r]

private theorem toCat_ofCat : ∀ T : Caterpillar.Tree, toCat (ofCat T) = T
  | .leaf _ => rfl
  | .node l r => by simp only [toCat, ofCat, toCat_ofCat l, toCat_ofCat r]

private def toCatCtx : Spec.Ctx → Octonion.Ctx
  | .hole => .hole
  | .inL c r => .inL (toCatCtx c) (toCat r)
  | .inR l c => .inR (toCat l) (toCatCtx c)

private def ofCatCtx : Octonion.Ctx → Spec.Ctx
  | .hole => .hole
  | .inL c r => .inL (ofCatCtx c) (ofCat r)
  | .inR l c => .inR (ofCat l) (ofCatCtx c)

private theorem toCat_fill (S : Spec.Tree) : ∀ c : Spec.Ctx,
    toCat (Spec.fill c S) = Octonion.fill (toCatCtx c) (toCat S)
  | .hole => rfl
  | .inL c r => by simp only [Spec.fill, toCat, Octonion.fill, toCatCtx, toCat_fill S c]
  | .inR l c => by simp only [Spec.fill, toCat, Octonion.fill, toCatCtx, toCat_fill S c]

private theorem ofCat_fill (S : Caterpillar.Tree) : ∀ c : Octonion.Ctx,
    ofCat (Octonion.fill c S) = Spec.fill (ofCatCtx c) (ofCat S)
  | .hole => rfl
  | .inL c r => by simp only [Octonion.fill, ofCat, Spec.fill, ofCatCtx, ofCat_fill S c]
  | .inR l c => by simp only [Octonion.fill, ofCat, Spec.fill, ofCatCtx, ofCat_fill S c]

private theorem lv_toCat : ∀ T : Spec.Tree, Spec.lv T = Octonion.lv (toCat T)
  | .leaf _ => rfl
  | .node l r => by simp only [Spec.lv, Octonion.lv, toCat, lv_toCat l, lv_toCat r]

private theorem lv_ofCat (T : Caterpillar.Tree) : Spec.lv (ofCat T) = Octonion.lv T := by
  rw [lv_toCat, toCat_ofCat]

private theorem ev_toCat (w : Nat → Nat) (ρ : Nat → O) : ∀ T : Spec.Tree,
    Spec.ev w ρ T = Octonion.ev w ρ (toCat T)
  | .leaf _ => rfl
  | .node l r => by
    simp only [Spec.ev, Octonion.ev, toCat, ev_toCat w ρ l, ev_toCat w ρ r]
    rfl

private theorem ev_ofCat (w : Nat → Nat) (ρ : Nat → O) (T : Caterpillar.Tree) :
    Spec.ev w ρ (ofCat T) = Octonion.ev w ρ T := by
  rw [ev_toCat, toCat_ofCat]

private theorem cnt_toCat (w : Nat → Nat) (ℓ : Nat) : ∀ T : Spec.Tree,
    Spec.cnt w ℓ T = Octonion.cnt w ℓ (toCat T)
  | .leaf _ => rfl
  | .node l r => by simp only [Spec.cnt, Octonion.cnt, toCat, cnt_toCat w ℓ l, cnt_toCat w ℓ r]

private theorem minor_toCat (w : Nat → Nat) (A B C : Spec.Tree) (p q r : Nat) :
    Spec.minor w A B C p q r = Octonion.minor w (toCat A) (toCat B) (toCat C) p q r := by
  simp only [Spec.minor, Octonion.minor, cnt_toCat]

private theorem dn_iff_toCat (w : Nat → Nat) (A B C : Spec.Tree) :
    Spec.DN w A B C ↔ Octonion.DN w (toCat A) (toCat B) (toCat C) := by
  simp only [Spec.DN, Octonion.DN, minor_toCat]

private theorem dn_ofCat (w : Nat → Nat) (A B C : Caterpillar.Tree)
    (h : Octonion.DN w A B C) : Spec.DN w (ofCat A) (ofCat B) (ofCat C) := by
  rw [dn_iff_toCat, toCat_ofCat, toCat_ofCat, toCat_ofCat]
  exact h

private theorem flipStep_toCat {T U : Spec.Tree} (h : Spec.FlipStep T U) :
    Closure.FlipStep (toCat T) (toCat U) := by
  cases h with
  | fwd c A B C =>
    rw [toCat_fill, toCat_fill]
    exact Closure.FlipStep.fwd (toCatCtx c) (toCat A) (toCat B) (toCat C)
  | bwd c A B C =>
    rw [toCat_fill, toCat_fill]
    exact Closure.FlipStep.bwd (toCatCtx c) (toCat A) (toCat B) (toCat C)

private theorem flipStep_ofCat {T U : Caterpillar.Tree} (h : Closure.FlipStep T U) :
    Spec.FlipStep (ofCat T) (ofCat U) := by
  cases h with
  | fwd c A B C =>
    rw [ofCat_fill, ofCat_fill]
    exact Spec.FlipStep.fwd (ofCatCtx c) (ofCat A) (ofCat B) (ofCat C)
  | bwd c A B C =>
    rw [ofCat_fill, ofCat_fill]
    exact Spec.FlipStep.bwd (ofCatCtx c) (ofCat A) (ofCat B) (ofCat C)

private theorem kerFlip_toCat {w : Nat → Nat} {T U : Spec.Tree} (h : Spec.KerFlip w T U) :
    Closure.KerFlip w (toCat T) (toCat U) :=
  ⟨flipStep_toCat h.1, fun ρ => by rw [← ev_toCat, ← ev_toCat]; exact h.2 ρ⟩

private theorem kerFlip_ofCat {w : Nat → Nat} {T U : Caterpillar.Tree} (h : Closure.KerFlip w T U) :
    Spec.KerFlip w (ofCat T) (ofCat U) :=
  ⟨flipStep_ofCat h.1, fun ρ => by rw [ev_ofCat, ev_ofCat]; exact h.2 ρ⟩

private theorem reach_toCat {w : Nat → Nat} {T U : Spec.Tree} (h : Spec.DReach (Spec.KerFlip w) T U) :
    Octonion.DReach (Closure.KerFlip w) (toCat T) (toCat U) := by
  induction h with
  | refl => exact Octonion.DReach.refl _
  | tail _ st ih => exact Octonion.DReach.tail ih (kerFlip_toCat st)

private theorem reach_ofCat {w : Nat → Nat} {T U : Caterpillar.Tree}
    (h : Octonion.DReach (Closure.KerFlip w) T U) :
    Spec.DReach (Spec.KerFlip w) (ofCat T) (ofCat U) := by
  induction h with
  | refl => exact Spec.DReach.refl _
  | tail _ st ih => exact Spec.DReach.tail ih (kerFlip_ofCat st)

private theorem dnStep_ofCat {w : Nat → Nat} {T U : Caterpillar.Tree} (h : Octonion.DNStep w T U) :
    Spec.DNStep w (ofCat T) (ofCat U) := by
  cases h with
  | fwd c A B C hd =>
    rw [ofCat_fill, ofCat_fill]
    exact Spec.DNStep.fwd (ofCatCtx c) (ofCat A) (ofCat B) (ofCat C) (dn_ofCat w A B C hd)
  | bwd c A B C hd =>
    rw [ofCat_fill, ofCat_fill]
    exact Spec.DNStep.bwd (ofCatCtx c) (ofCat A) (ofCat B) (ofCat C) (dn_ofCat w A B C hd)

private theorem kerConn_iff (w : Nat → Nat) (n : Nat) :
    Spec.KerConn w n ↔ MainThm.KerConn w n := by
  constructor
  · intro h T T' hT hT' heq
    have r := h (ofCat T) (ofCat T') (by rw [lv_ofCat]; exact hT) (by rw [lv_ofCat]; exact hT')
      (fun ρ => by rw [ev_ofCat, ev_ofCat]; exact heq ρ)
    simpa only [toCat_ofCat] using reach_toCat r
  · intro h T T' hT hT' heq
    have r := h (toCat T) (toCat T') (by rw [← lv_toCat]; exact hT) (by rw [← lv_toCat]; exact hT')
      (fun ρ => by rw [← ev_toCat, ← ev_toCat]; exact heq ρ)
    simpa only [ofCat_toCat] using reach_ofCat r

private theorem rgs_eq : ∀ n : Nat, Spec.rgs n = Count.rgs n
  | 0 => rfl
  | n + 1 => by simp only [Spec.rgs, Count.rgs, rgs_eq n]; rfl

private theorem bell_eq (n : Nat) : Spec.bell n = Count.bell n := by
  simp only [Spec.bell, Count.bell, rgs_eq]

private theorem stirling_eq (n k : Nat) : Spec.stirling n k = Canon.stirling n k := by
  simp only [Spec.stirling, Canon.stirling, rgs_eq]; rfl

private theorem ssum_eq (f : Nat → Nat) : ∀ n : Nat, Spec.ssum f n = Canon.ssum f n
  | 0 => rfl
  | n + 1 => by simp only [Spec.ssum, Canon.ssum, ssum_eq f n]

/-! ## Headline mathematical theorems -/

theorem main (wl : List Nat) :
    KerConn (wd wl) wl.length ↔ TwoLetters wl ∨ Interval wl :=
  (kerConn_iff (wd wl) wl.length).trans (MainThm.main wl)

theorem count_disconnected (m : Nat) :
    ((rgs (m + 1)).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length
      + 2 ^ (m + 1) = bell (m + 1) + (m + 1) := by
  rw [rgs_eq, bell_eq]
  have hf :
      (Count.rgs (m + 1)).filter (fun w => @decide (¬ Spec.KerConn (Spec.wd w) w.length) (Classical.propDecidable _)) =
      (Count.rgs (m + 1)).filter (fun w => @decide (¬ MainThm.KerConn (MainThm.wd w) w.length) (Classical.propDecidable _)) := by
    apply List.filter_congr
    intro w _
    have e : (¬ Spec.KerConn (Spec.wd w) w.length) ↔ (¬ MainThm.KerConn (MainThm.wd w) w.length) :=
      not_congr (kerConn_iff (Spec.wd w) w.length)
    by_cases h : MainThm.KerConn (MainThm.wd w) w.length
    · have h1 : ¬ (¬ Spec.KerConn (Spec.wd w) w.length) := fun hn => hn ((kerConn_iff _ _).2 h)
      have h2 : ¬ (¬ MainThm.KerConn (MainThm.wd w) w.length) := fun hn => hn h
      rw [@decide_eq_false _ (Classical.propDecidable _) h1,
          @decide_eq_false _ (Classical.propDecidable _) h2]
    · have h1 : ¬ Spec.KerConn (Spec.wd w) w.length := e.2 h
      rw [@decide_eq_true _ (Classical.propDecidable _) h1,
          @decide_eq_true _ (Classical.propDecidable _) h]
  rw [hf]
  exact Count.count_disconnected m

theorem canonical (w : List Nat) :
    ∃ v ∈ rgs w.length, Renaming w v ∧ ∀ v' ∈ rgs w.length, Renaming w v' → v' = v := by
  rw [rgs_eq]
  exact Canon.canonical w

theorem rgs_nodup (n : Nat) : (rgs n).Nodup := by
  rw [rgs_eq]
  exact Canon.rgs_nodup n

theorem kerconn_rename (w v : List Nat) (hr : Renaming w v) :
    KerConn (wd w) w.length ↔ KerConn (wd v) v.length := by
  rw [kerConn_iff, kerConn_iff]
  exact Canon.kerconn_rename w v hr

theorem stirling_rec (m k : Nat) :
    stirling (m + 2) (k + 1) = (k + 1) * stirling (m + 1) (k + 1) + 1 * stirling (m + 1) k := by
  rw [stirling_eq, stirling_eq, stirling_eq]
  exact Canon.stirling_rec m k

theorem bell_eq_sum (n : Nat) : bell n = ssum (stirling n) (n + 1) := by
  rw [bell_eq, ssum_eq]
  have hf : Spec.stirling n = Canon.stirling n := funext (stirling_eq n)
  rw [hf]
  exact Canon.bell_eq_sum n

theorem lemmaW_exists (w : Nat → Nat) (A B C : Tree) (h : ¬ DN w A B C) :
    ∃ ρ : Nat → O, (∀ ℓ, ρ ℓ ≠ zero) ∧ assoc (ev w ρ A) (ev w ρ B) (ev w ρ C) ≠ zero := by
  have h' : ¬ Octonion.DN w (toCat A) (toCat B) (toCat C) := fun hd => h ((dn_iff_toCat w A B C).2 hd)
  obtain ⟨ρ, hρ, ha⟩ := WExist.lemmaW_exists w (toCat A) (toCat B) (toCat C) h'
  refine ⟨ρ, hρ, ?_⟩
  rw [ev_toCat, ev_toCat, ev_toCat]
  exact ha

theorem kerflip_dn (w : Nat → Nat) {T U : Tree} (h : KerFlip w T U) : DNStep w T U := by
  have hd := WExist.kerflip_dn w (kerFlip_toCat h)
  simpa only [ofCat_toCat] using dnStep_ofCat hd

/-! ## Algebraic integrity and non-vacuity anchors -/

theorem octonion_unital (a : O) : mul one a = a ∧ mul a one = a :=
  ⟨Octonion.one_mul a, Octonion.mul_one a⟩

theorem octonion_norm_mul (a b : O) : nrm (mul a b) = nrm a * nrm b :=
  Octonion.norm_mul a b

theorem octonion_non_associative : assoc (unit 1) (unit 2) (unit 4) ≠ zero := by
  intro h
  have h7 := congrFun h 7
  have hne : assoc (unit 1) (unit 2) (unit 4) 7 ≠ zero 7 := by decide
  exact hne h7

theorem octonion_moufang (a b c : O) :
    mul a (mul b (mul a c)) = mul (mul (mul a b) a) c ∧
    mul (mul (mul c a) b) a = mul c (mul a (mul b a)) ∧
    mul (mul a b) (mul c a) = mul a (mul (mul b c) a) :=
  ⟨Octonion.moufang_left a b c, Octonion.moufang_right a b c, Octonion.moufang_middle a b c⟩

theorem kerconn_two_letters_example : KerConn (wd [0, 1, 0, 1]) 4 := by
  refine (main [0, 1, 0, 1]).2 (Or.inl ⟨0, 1, ?_⟩)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem kerconn_interval_example : KerConn (wd [0, 0, 1, 2]) 4 := by
  refine (main [0, 0, 1, 2]).2 (Or.inr ?_)
  intro i j k hij hjk hk he
  have hlt : i < 4 ∧ j < 4 ∧ k < 4 := by simp at hk; omega
  rcases hlt with ⟨hi, hj, hk'⟩
  match i, j, k, hi, hj, hk', hij, hjk, he with
  | 0, 0, _, _, _, _, _, _, _ => rfl
  | 0, 1, _, _, _, _, _, _, _ => rfl
  | 0, 2, 2, _, _, _, _, _, he => cases he
  | 0, 2, 3, _, _, _, _, _, he => cases he
  | 0, 3, 3, _, _, _, _, _, he => cases he
  | 1, 1, _, _, _, _, _, _, _ => rfl
  | 1, 2, 2, _, _, _, _, _, he => cases he
  | 1, 2, 3, _, _, _, _, _, he => cases he
  | 1, 3, 3, _, _, _, _, _, he => cases he
  | 2, 2, _, _, _, _, _, _, _ => rfl
  | 2, 3, 3, _, _, _, _, _, he => cases he
  | 3, 3, 3, _, _, _, _, _, _ => rfl

theorem not_kerconn_example : ¬ KerConn (wd [0, 1, 2, 0]) 4 := by
  intro h
  rcases (main [0, 1, 2, 0]).1 h with ⟨a, c, hac⟩ | hI
  · have h0 : 0 = a ∨ 0 = c := hac 0 (by simp)
    have h1 : 1 = a ∨ 1 = c := hac 1 (by simp)
    have h2 : 2 = a ∨ 2 = c := hac 2 (by simp)
    omega
  · have := hI 0 1 3 (by decide) (by decide) (by decide) rfl
    simp [wd] at this

theorem bell_small_values : (List.range 6).map bell = [1, 1, 2, 5, 15, 52] := by
  have hb : Spec.bell = Count.bell := funext bell_eq
  rw [hb]
  exact Count.bell_values

theorem disconnected_count_four_five :
    ((rgs 4).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length = 3 ∧
    ((rgs 5).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length = 25 := by
  have hb := bell_small_values
  have hb4 : bell 4 = 15 := by
    have := congrArg (fun l => l.getD 4 0) hb
    simpa [List.getD] using this
  have hb5 : bell 5 = 52 := by
    have := congrArg (fun l => l.getD 5 0) hb
    simpa [List.getD] using this
  have h4 := count_disconnected 3
  have h5 := count_disconnected 4
  change ((rgs 4).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length + 16 = bell 4 + 4 at h4
  change ((rgs 5).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length + 32 = bell 5 + 5 at h5
  rw [hb4] at h4
  rw [hb5] at h5
  exact ⟨by omega, by omega⟩

end Challenge
