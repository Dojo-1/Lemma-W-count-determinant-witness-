import Caterpillar.Main

/-!
# The count `Bell(n) − 2ⁿ + n`

Words up to renaming of letters are their canonical forms, the restricted growth strings (`rgs n`): the
first letter is `0` and each letter is at most one more than every earlier letter. There are `Bell(n)` of
them (`bell`). Writing `nl w` for (largest letter) + 1:

* two letters ⟺ `nl w ≤ 2` (`two_iff`); interval ⟺ the word is non-decreasing (`interval_iff`);
* appending a letter `c ≤ nl w` doubles the two-letter words and the interval words, and adds exactly one
  word that is both (`extT`, `extI`, `extTI`, `extZ`); so for `n ≥ 1` there are `2ⁿ⁻¹ + 2ⁿ⁻¹ − n = 2ⁿ − n`
  words with ≤ 2 letters or interval (`good_count`);
* **`count_disconnected`**: with `MainThm.main`, the number of canonical words of length `n ≥ 1` with a
  kernel class that is not flip-connected is `Bell(n) − 2ⁿ + n`.
-/

namespace Count
open MainThm

/-- (largest letter) + 1, and `0` for the empty word -/
def nl (w : List Nat) : Nat := w.foldr (fun x m => max (x + 1) m) 0

theorem nl_cons (x : Nat) (t : List Nat) : nl (x :: t) = max (x + 1) (nl t) := rfl

theorem foldr_max (w : List Nat) : ∀ b, w.foldr (fun x m => max (x + 1) m) b = max (nl w) b := by
  induction w with
  | nil => intro b; simp [nl]
  | cons x t ih => intro b; simp only [List.foldr_cons]; rw [ih b, nl_cons, Nat.max_assoc]

theorem nl_append (w : List Nat) (c : Nat) : nl (w ++ [c]) = max (nl w) (c + 1) := by
  show List.foldr _ 0 (w ++ [c]) = _
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.max_zero]; exact foldr_max w (c + 1)

theorem le_iff (w : List Nat) (c : Nat) : (∀ x ∈ w, x ≤ c) ↔ nl w ≤ c + 1 := by
  induction w with
  | nil => simp [nl]
  | cons x t ih =>
    rw [nl_cons, Nat.max_le, ← ih]; simp only [List.mem_cons, forall_eq_or_imp]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem lt_nl (w : List Nat) : ∀ x ∈ w, x < nl w := by
  induction w with
  | nil => simp
  | cons y t ih =>
    intro x hx; rw [nl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · have := Nat.le_max_left (x + 1) (nl t); omega
    · have := Nat.le_max_right (y + 1) (nl t); have := ih x hx; omega

theorem nl_pos (w : List Nat) (hw : w ≠ []) : 1 ≤ nl w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x t => rw [nl_cons]; have := Nat.le_max_left (x + 1) (nl t); omega

/-- one-letter extensions of a canonical word -/
def ext (w : List Nat) : List (List Nat) := (List.range (nl w + 1)).map (fun c => w ++ [c])

/-- restricted growth strings: one canonical word per set partition -/
def rgs : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (rgs n).flatMap ext

def bell (n : Nat) : Nat := (rgs n).length

set_option maxRecDepth 100000 in
theorem bell_values : (List.range 6).map bell = [1, 1, 2, 5, 15, 52] := by decide

theorem mem_rgs_succ (n : Nat) (w : List Nat) :
    w ∈ rgs (n + 1) ↔ ∃ v ∈ rgs n, ∃ c, c < nl v + 1 ∧ w = v ++ [c] := by
  simp only [rgs, List.mem_flatMap, ext, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨v, hv, c, hc, rfl⟩; exact ⟨v, hv, c, hc, rfl⟩
  · rintro ⟨v, hv, c, hc, rfl⟩; exact ⟨v, hv, c, hc, rfl⟩

theorem len_rgs : ∀ n, ∀ w ∈ rgs n, w.length = n
  | 0, w, h => by simp [rgs] at h; subst h; rfl
  | n + 1, w, h => by
    obtain ⟨v, hv, c, _, rfl⟩ := (mem_rgs_succ n w).1 h
    simp [len_rgs n v hv]

/-- canonical: every letter below `nl w` occurs -/
theorem rgs_canon : ∀ n, ∀ w ∈ rgs n, ∀ y < nl w, y ∈ w
  | 0, w, h, y, hy => by simp [rgs] at h; subst h; simp [nl] at hy
  | n + 1, w, h, y, hy => by
    obtain ⟨v, hv, c, hc, rfl⟩ := (mem_rgs_succ n w).1 h
    rw [nl_append] at hy
    by_cases h1 : y < nl v
    · exact List.mem_append_left _ (rgs_canon n v hv y h1)
    · have : y = c := by have := Nat.le_max_left (nl v) (c + 1); have := Nat.le_max_right (nl v) (c + 1)
                         simp only [Nat.max_def] at hy; split at hy <;> omega
      subst this; simp

/-! ## the two properties on canonical words -/

def pT (w : List Nat) : Bool := decide (nl w ≤ 2)
def pI (w : List Nat) : Bool := decide (w.Pairwise (· ≤ ·))
def pZ (w : List Nat) : Bool := decide (nl w = 1)

theorem two_iff (n : Nat) (w : List Nat) (hw : w ∈ rgs n) : TwoLetters w ↔ nl w ≤ 2 := by
  constructor
  · rintro ⟨a, c, h⟩
    apply Classical.byContradiction; intro hn
    have h0 := h 0 (rgs_canon n w hw 0 (by omega))
    have h1 := h 1 (rgs_canon n w hw 1 (by omega))
    have h2 := h 2 (rgs_canon n w hw 2 (by omega))
    omega
  · intro h; refine ⟨0, 1, fun x hx => ?_⟩; have := lt_nl w x hx; omega

theorem getD_app (v : List Nat) (c i : Nat) (hi : i < v.length) : wd (v ++ [c]) i = wd v i := by
  simp only [wd]
  rw [getD_eq _ _ (by simp; omega), getD_eq _ _ hi, List.getElem_append_left hi]

theorem getD_last (v : List Nat) (c : Nat) : wd (v ++ [c]) v.length = c := by
  simp only [wd]; rw [getD_eq _ _ (by simp)]; simp

theorem sorted_get (w : List Nat) (hs : w.Pairwise (· ≤ ·)) (i j : Nat) (hij : i ≤ j) (hj : j < w.length) :
    wd w i ≤ wd w j := by
  simp only [wd]; rw [getD_eq _ _ (by omega), getD_eq _ _ hj]
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact List.pairwise_iff_getElem.1 hs i j (by omega) hj h
  · subst h; exact Nat.le_refl _

theorem interval_iff : ∀ n, ∀ w ∈ rgs n, (Interval w ↔ w.Pairwise (· ≤ ·))
  | 0, w, h => by simp [rgs] at h; subst h; simp [Interval]
  | n + 1, w, h => by
    constructor
    · intro hI
      obtain ⟨v, hv, c, hc, rfl⟩ := (mem_rgs_succ n w).1 h
      have hIv : Interval v := by
        intro i j k hij hjk hk e
        have := hI i j k hij hjk (by simp; omega)
          (by rw [getD_app v c i (by omega), getD_app v c k hk]; exact e)
        rwa [getD_app v c j (by omega), getD_app v c i (by omega)] at this
      have hs := (interval_iff n v hv).1 hIv
      have hall : ∀ x ∈ v, x ≤ c := by
        by_cases hcv : c ∈ v
        · obtain ⟨p, hp, ep⟩ := List.mem_iff_getElem.1 hcv
          have hL : 0 < v.length := by omega
          have e1 := hI p (v.length - 1) v.length (by omega) (by omega) (by simp)
            (by rw [getD_app v c p hp, getD_last]; simp only [wd]; rw [getD_eq _ _ hp, ep])
          rw [getD_app v c _ (by omega), getD_app v c p hp] at e1
          have ec : wd v p = c := by simp only [wd]; rw [getD_eq _ _ hp, ep]
          intro x hx
          obtain ⟨q, hq, eq⟩ := List.mem_iff_getElem.1 hx
          have := sorted_get v hs q (v.length - 1) (by omega) (by omega)
          have ex : wd v q = x := by simp only [wd]; rw [getD_eq _ _ hq, eq]
          omega
        · have : c = nl v := by
            apply Classical.byContradiction; intro hne
            exact hcv (rgs_canon n v hv c (by omega))
          intro x hx; have := lt_nl v x hx; omega
      rw [List.pairwise_append]
      exact ⟨hs, List.pairwise_singleton _ _, fun a ha b hb => by simp at hb; subst hb; exact hall a ha⟩
    · intro hs i j k hij hjk hk e
      have := sorted_get w hs i j hij (by omega)
      have := sorted_get w hs j k hjk hk
      omega

theorem good_iff (n : Nat) (w : List Nat) (hw : w ∈ rgs n) :
    (TwoLetters w ∨ Interval w) ↔ (pT w || pI w) = true := by
  rw [two_iff n w hw, interval_iff n w hw]; simp [pT, pI]

/-! ## counting extensions -/

theorem cnt_le1 : ∀ k, (List.range (k + 2)).countP (fun c => decide (c ≤ 1)) = 2
  | 0 => by decide
  | k + 1 => by
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, List.range_succ, List.countP_append, cnt_le1 k]; simp

theorem cnt_top2 (j : Nat) : (List.range (j + 2)).countP (fun c => decide (j + 1 ≤ c + 1)) = 2 := by
  rw [show j + 2 = (j + 1) + 1 by omega, List.range_succ, List.range_succ, List.countP_append, List.countP_append,
    (List.countP_eq_zero).2 (fun c hc => by simp at hc ⊢; omega)]
  simp

theorem extT (w : List Nat) (hw : w ≠ []) : (ext w).countP pT = if pT w then 2 else 0 := by
  have h1 := nl_pos w hw
  simp only [ext, List.countP_map]
  have : (pT ∘ fun c => w ++ [c]) = fun c => decide (nl w ≤ 2 ∧ c ≤ 1) := by
    funext c; simp only [Function.comp, pT, nl_append, Nat.max_le]; congr 1; apply propext; omega
  rw [this]
  by_cases h : nl w ≤ 2
  · have e : (fun c => decide (nl w ≤ 2 ∧ c ≤ 1)) = fun c => decide (c ≤ 1) := by
      funext c; simp [h]
    rw [e, show nl w + 1 = (nl w - 1) + 2 by omega, cnt_le1]; simp [pT, h]
  · rw [(List.countP_eq_zero).2 (fun c _ => by simp [h])]; simp [pT, h]

theorem pI_app (w : List Nat) (c : Nat) : pI (w ++ [c]) = decide (w.Pairwise (· ≤ ·) ∧ nl w ≤ c + 1) := by
  simp only [pI]; congr 1; apply propext
  rw [List.pairwise_append, ← le_iff]; simp

theorem extI (w : List Nat) (hw : w ≠ []) : (ext w).countP pI = if pI w then 2 else 0 := by
  have h1 := nl_pos w hw
  simp only [ext, List.countP_map]
  have : (pI ∘ fun c => w ++ [c]) = fun c => decide (w.Pairwise (· ≤ ·) ∧ nl w ≤ c + 1) := by
    funext c; exact pI_app w c
  rw [this]
  by_cases h : w.Pairwise (· ≤ ·)
  · have e : (fun c => decide (w.Pairwise (· ≤ ·) ∧ nl w ≤ c + 1)) = fun c => decide ((nl w - 1) + 1 ≤ c + 1) := by
      funext c; simp only [h, true_and]; congr 1; apply propext; omega
    rw [e, show nl w + 1 = (nl w - 1) + 2 by omega, cnt_top2]; simp [pI, h]
  · rw [(List.countP_eq_zero).2 (fun c _ => by simp [h])]; simp [pI, h]

theorem extZ (w : List Nat) (hw : w ≠ []) : (ext w).countP pZ = if pZ w then 1 else 0 := by
  have h1 := nl_pos w hw
  simp only [ext, List.countP_map]
  have : (pZ ∘ fun c => w ++ [c]) = fun c => decide (nl w = 1 ∧ c = 0) := by
    funext c; simp only [Function.comp, pZ, nl_append, Nat.max_def]; congr 1; apply propext; split <;> omega
  rw [this]
  by_cases h : nl w = 1
  · have hz : pZ w = true := by simp [pZ, h]
    rw [hz, h]; decide
  · rw [(List.countP_eq_zero).2 (fun c _ => by simp [h])]; simp [pZ, h]

theorem pZ_TI (w : List Nat) (h : pZ w = true) : pT w = true ∧ pI w = true := by
  simp only [pZ, decide_eq_true_eq] at h
  have h0 : ∀ x ∈ w, x = 0 := fun x hx => by have := lt_nl w x hx; omega
  refine ⟨by simp [pT, h], ?_⟩
  simp only [pI, decide_eq_true_eq]
  clear h
  induction w with
  | nil => exact List.Pairwise.nil
  | cons x t ih =>
    rw [List.pairwise_cons]
    exact ⟨fun y hy => by have := h0 x (by simp); have := h0 y (by simp [hy]); omega,
      ih (fun z hz => h0 z (by simp [hz]))⟩

theorem extTI (w : List Nat) (hw : w ≠ []) :
    (ext w).countP (fun v => pT v && pI v) = (if (pT w && pI w) then 1 else 0) + (if pZ w then 1 else 0) := by
  have h1 := nl_pos w hw
  simp only [ext, List.countP_map]
  have : ((fun v => pT v && pI v) ∘ fun c => w ++ [c]) =
      fun c => decide ((nl w ≤ 2 ∧ c + 1 ≤ 2) ∧ (w.Pairwise (· ≤ ·) ∧ nl w ≤ c + 1)) := by
    funext c
    simp only [Function.comp, pI_app, pT, nl_append, Nat.max_le]
    rw [← Bool.decide_and]
  rw [this]
  by_cases hT : nl w ≤ 2
  · by_cases hI : w.Pairwise (· ≤ ·)
    · have e : (fun c => decide ((nl w ≤ 2 ∧ c + 1 ≤ 2) ∧ (w.Pairwise (· ≤ ·) ∧ nl w ≤ c + 1))) =
          fun c => decide (c + 1 ≤ 2 ∧ nl w ≤ c + 1) := by funext c; simp only [hT, hI, true_and]
      rw [e]
      rcases (show nl w = 1 ∨ nl w = 2 by omega) with h | h
      · rw [h]; simp [pT, pI, pZ, h, hI]; decide
      · rw [h]; simp [pT, pI, pZ, h, hI]; decide
    · rw [(List.countP_eq_zero).2 (fun c _ => by simp [hI])]
      have hz : pZ w = false := by
        cases hz : pZ w
        · rfl
        · exact absurd (by simpa [pI] using (pZ_TI w hz).2) hI
      simp [pT, pI, hI, hz]
  · rw [(List.countP_eq_zero).2 (fun c _ => by simp [hT])]
    have hz : pZ w = false := by
      cases hz : pZ w
      · rfl
      · exact absurd (by simpa [pT] using (pZ_TI w hz).1) hT
    simp [pT, hT, hz]

/-! ## sums over the canonical words -/

theorem countP_flatMap_eq (p : List Nat → Bool) (f : List Nat → List (List Nat)) (g : List Nat → Nat) :
    ∀ l : List (List Nat), (∀ w ∈ l, (f w).countP p = g w) → (l.flatMap f).countP p = (l.map g).sum
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.countP_append, h a (by simp),
      countP_flatMap_eq p f g l (fun w hw => h w (by simp [hw]))]
    simp

theorem sum_eq (g : List Nat → Nat) (q1 q2 : List Nat → Bool) (c1 c2 : Nat) :
    ∀ l : List (List Nat), (∀ w ∈ l, g w = (if q1 w then c1 else 0) + (if q2 w then c2 else 0)) →
      (l.map g).sum = c1 * l.countP q1 + c2 * l.countP q2
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a (by simp), sum_eq g q1 q2 c1 c2 l (fun w hw => h w (by simp [hw])),
      List.countP_cons, List.countP_cons]
    cases q1 a <;> cases q2 a <;> simp [Nat.mul_add] <;> omega

theorem ne_nil (m : Nat) (w : List Nat) (hw : w ∈ rgs (m + 1)) : w ≠ [] := by
  intro e; have := len_rgs (m + 1) w hw; rw [e] at this; simp at this

theorem step (p : List Nat → Bool) (q1 q2 : List Nat → Bool) (c1 c2 m : Nat)
    (h : ∀ w, w ≠ [] → (ext w).countP p = (if q1 w then c1 else 0) + (if q2 w then c2 else 0)) :
    (rgs (m + 2)).countP p = c1 * (rgs (m + 1)).countP q1 + c2 * (rgs (m + 1)).countP q2 := by
  show ((rgs (m + 1)).flatMap ext).countP p = _
  rw [countP_flatMap_eq p ext (fun w => (if q1 w then c1 else 0) + (if q2 w then c2 else 0)) _
    (fun w hw => h w (ne_nil m w hw))]
  exact sum_eq _ q1 q2 c1 c2 _ (fun _ _ => rfl)

theorem closed (m : Nat) : (rgs (m + 1)).countP pT = 2 ^ m ∧ (rgs (m + 1)).countP pI = 2 ^ m ∧
    (rgs (m + 1)).countP pZ = 1 ∧ (rgs (m + 1)).countP (fun v => pT v && pI v) = m + 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨hT, hI, hZ, hTI⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [step pT pT pT 2 0 m (fun w hw => by rw [extT w hw]; simp), hT, Nat.pow_succ]; omega
    · rw [step pI pI pI 2 0 m (fun w hw => by rw [extI w hw]; simp), hI, Nat.pow_succ]; omega
    · rw [step pZ pZ pZ 1 0 m (fun w hw => by rw [extZ w hw]; simp), hZ]
    · rw [step _ (fun v => pT v && pI v) pZ 1 1 m (fun w hw => extTI w hw), hTI, hZ]; omega

theorem countP_or (p q : List Nat → Bool) : ∀ l : List (List Nat),
    l.countP (fun w => p w || q w) + l.countP (fun w => p w && q w) = l.countP p + l.countP q
  | [] => rfl
  | a :: l => by
    have := countP_or p q l
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

/-- `2ⁿ − n` canonical words of length `n ≥ 1` have ≤ 2 letters or are interval words -/
theorem good_count (m : Nat) : (rgs (m + 1)).countP (fun w => pT w || pI w) + (m + 1) = 2 ^ (m + 1) := by
  obtain ⟨hT, hI, _, hTI⟩ := closed m
  have := countP_or pT pI (rgs (m + 1))
  rw [hTI, hT, hI] at this
  rw [Nat.pow_succ]; omega

theorem countP_not (g : List Nat → Bool) : ∀ l : List (List Nat), l.countP g + l.countP (fun a => !g a) = l.length
  | [] => rfl
  | a :: l => by
    have := countP_not g l
    simp only [List.countP_cons, List.length_cons]
    cases g a <;> simp <;> omega

/-- **The count.** Among the `Bell(n)` words of length `n ≥ 1` up to renaming, exactly `Bell(n) − 2ⁿ + n`
have a kernel class of octonion bracketings that is not flip-connected. -/
theorem count_disconnected (m : Nat) :
    ((rgs (m + 1)).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _))).length
      + 2 ^ (m + 1) = bell (m + 1) + (m + 1) := by
  have hf : (rgs (m + 1)).filter (fun w => @decide (¬ KerConn (wd w) w.length) (Classical.propDecidable _)) =
      (rgs (m + 1)).filter (fun w => !(pT w || pI w)) := by
    apply List.filter_congr
    intro w hw
    have e : KerConn (wd w) w.length ↔ (pT w || pI w) = true := (main w).trans (good_iff (m + 1) w hw)
    cases hb : (pT w || pI w)
    · simp only [Bool.not_false]
      apply @decide_eq_true _ (Classical.propDecidable _); intro hK; have := e.1 hK; rw [hb] at this; exact Bool.false_ne_true this
    · simp only [Bool.not_true]
      apply @decide_eq_false _ (Classical.propDecidable _); intro hn; exact hn (e.2 hb)
  rw [hf, ← List.countP_eq_length_filter]
  have h1 := countP_not (fun w => pT w || pI w) (rgs (m + 1))
  have h2 := good_count m
  simp only [bell]; omega

end Count
