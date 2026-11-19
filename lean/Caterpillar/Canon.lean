import Caterpillar.Count

/-!
# Canonical words: `rgs n` is exactly one word per renaming class

* `rgs_nodup`: the restricted growth strings are distinct.
* `canonical`: every word `w` is a renaming (letters relabelled injectively) of exactly one word of
  `rgs w.length`, namely `canon w`, which numbers letters by first occurrence.
* `kerconn_rename`: flip-connectivity of kernel classes is invariant under renaming.

With `Count.count_disconnected`, `bell n` counts the renaming classes of words of length `n`, and
`Bell(n) − 2ⁿ + n` of these classes have a kernel class that is not flip-connected.
-/

namespace Canon
open MainThm Count

/-! ## distinctness -/

theorem rgs_nodup : ∀ n, (rgs n).Nodup
  | 0 => by simp [rgs]
  | n + 1 => by
    show List.Pairwise (· ≠ ·) ((rgs n).flatMap ext)
    rw [List.pairwise_flatMap]
    refine ⟨fun v _ => ?_, (rgs_nodup n).imp ?_⟩
    · simp only [ext]; rw [List.pairwise_map]
      exact List.nodup_range.imp (fun h e => h (by simpa using e))
    · intro a b hab x hx y hy e
      simp only [ext, List.mem_map] at hx hy
      obtain ⟨c, _, rfl⟩ := hx; obtain ⟨d, _, rfl⟩ := hy
      exact hab (by have := congrArg List.dropLast e; simpa using this)

/-! ## first occurrences -/

def step (acc : List Nat) (x : Nat) : List Nat := if x ∈ acc then acc else acc ++ [x]

def firsts (w : List Nat) : List Nat := w.foldl step []

theorem mem_foldl : ∀ (w acc : List Nat) (x : Nat), x ∈ w.foldl step acc ↔ x ∈ acc ∨ x ∈ w
  | [], acc, x => by simp
  | y :: t, acc, x => by
    rw [List.foldl_cons, mem_foldl t _ x]; simp only [step]
    by_cases hy : y ∈ acc
    · simp only [hy, ite_true, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl hy
        · exact Or.inr h
    · simp only [hy, ite_false, List.mem_append, List.mem_cons, or_assoc, List.not_mem_nil, false_or]

theorem mem_firsts (w : List Nat) (x : Nat) : x ∈ firsts w ↔ x ∈ w := by
  simp [firsts, mem_foldl]

theorem nodup_foldl : ∀ (w acc : List Nat), acc.Nodup → (w.foldl step acc).Nodup
  | [], _, h => h
  | y :: t, acc, h => by
    rw [List.foldl_cons]; apply nodup_foldl t; simp only [step]
    split
    · exact h
    · next hy => exact List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun a ha b hb => by
        simp at hb; subst hb; intro e; subst e; exact hy ha⟩

theorem firsts_nodup (w : List Nat) : (firsts w).Nodup := nodup_foldl w [] List.nodup_nil

theorem firsts_snoc (u : List Nat) (c : Nat) : firsts (u ++ [c]) = step (firsts u) c := by
  simp [firsts, List.foldl_append]

theorem mem_tail {x z : Nat} {zs : List Nat} (h : x ∈ z :: zs) (hz : ¬ z = x) : x ∈ zs := by
  rcases List.mem_cons.1 h with h | h
  · exact absurd h.symm hz
  · exact h

/-- position in a list (the length if absent) -/
def pos : List Nat → Nat → Nat
  | [], _ => 0
  | y :: ys, x => if y = x then 0 else pos ys x + 1

theorem pos_app_mem : ∀ (F G : List Nat) (x : Nat), x ∈ F → pos (F ++ G) x = pos F x
  | [], _, _, h => by simp at h
  | y :: ys, G, x, h => by
    show pos (y :: (ys ++ G)) x = pos (y :: ys) x
    simp only [pos]
    split
    · rfl
    · next hy => rw [pos_app_mem ys G x (mem_tail h hy)]

theorem pos_lt : ∀ (F : List Nat) (x : Nat), x ∈ F → pos F x < F.length
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [pos, List.length_cons]; split
    · omega
    · next hy => have := pos_lt ys x (mem_tail h hy); omega

theorem pos_new : ∀ (F : List Nat) (x : Nat), x ∉ F → pos (F ++ [x]) x = F.length
  | [], x, _ => by simp [pos]
  | y :: ys, x, h => by
    show pos (y :: (ys ++ [x])) x = (y :: ys).length
    simp only [pos, List.length_cons]
    have : y ≠ x := fun e => h (by simp [e])
    rw [ite_eq_right this, pos_new ys x (fun h' => h (by simp [h']))]

theorem pos_inj : ∀ (F : List Nat) (x y : Nat), x ∈ F → y ∈ F → pos F x = pos F y → x = y
  | [], _, _, h, _, _ => by simp at h
  | z :: zs, x, y, hx, hy, e => by
    simp only [pos] at e
    by_cases hzx : z = x <;> by_cases hzy : z = y
    · exact hzx.symm.trans hzy
    · rw [ite_eq_left hzx, ite_eq_right hzy] at e; omega
    · rw [ite_eq_right hzx, ite_eq_left hzy] at e; omega
    · rw [ite_eq_right hzx, ite_eq_right hzy] at e
      exact pos_inj zs x y (mem_tail hx hzx) (mem_tail hy hzy) (by omega)

theorem pos_get : ∀ (F : List Nat), F.Nodup → ∀ i (hi : i < F.length), pos F F[i] = i
  | [], _, i, hi => by simp at hi
  | y :: ys, hn, i, hi => by
    rw [List.nodup_cons] at hn
    cases i with
    | zero => simp [pos]
    | succ j =>
      simp only [List.getElem_cons_succ, pos]
      have hj : j < ys.length := by simp at hi; omega
      have : y ≠ ys[j] := fun e => hn.1 (by rw [e]; exact List.getElem_mem hj)
      rw [ite_eq_right this, pos_get ys hn.2 j hj]

/-! ## the canonical form -/

def canon (w : List Nat) : List Nat := w.map (pos (firsts w))

theorem canon_snoc (u : List Nat) (c : Nat) :
    canon (u ++ [c]) = canon u ++ [pos (firsts (u ++ [c])) c] := by
  simp only [canon, List.map_append, List.map_cons, List.map_nil]
  congr 1
  apply List.map_congr_left; intro x hx
  rw [firsts_snoc]; simp only [step]; split
  · rfl
  · exact pos_app_mem _ _ x ((mem_firsts u x).2 hx)

theorem len_le_nl (u : List Nat) : (firsts u).length ≤ nl (canon u) := by
  rcases Nat.eq_zero_or_pos (firsts u).length with h | h
  · omega
  · have hi : (firsts u).length - 1 < (firsts u).length := by omega
    have hm : (firsts u)[(firsts u).length - 1] ∈ u := (mem_firsts u _).1 (List.getElem_mem hi)
    have := lt_nl (canon u) ((firsts u).length - 1)
      (by rw [← pos_get (firsts u) (firsts_nodup u) _ hi]; exact List.mem_map_of_mem hm)
    omega

theorem canon_mem : ∀ n, ∀ w : List Nat, w.length = n → canon w ∈ rgs n
  | 0, w, h => by rw [List.eq_nil_of_length_eq_zero h]; simp [canon, rgs]
  | n + 1, w, h => by
    have hw : w ≠ [] := by intro e; rw [e] at h; simp at h
    obtain ⟨u, c, rfl⟩ : ∃ u c, w = u ++ [c] := ⟨w.dropLast, w.getLast hw, (List.dropLast_concat_getLast hw).symm⟩
    have hu : u.length = n := by simp at h; omega
    rw [mem_rgs_succ]
    refine ⟨canon u, canon_mem n u hu, _, ?_, canon_snoc u c⟩
    have := len_le_nl u
    rw [firsts_snoc]; simp only [step]; split
    · next hc => have := pos_lt _ c hc; omega
    · next hc => rw [pos_new _ c hc]; omega

def Renaming (w v : List Nat) : Prop := ∃ f : Nat → Nat, (∀ x ∈ w, ∀ y ∈ w, f x = f y → x = y) ∧ v = w.map f

theorem canon_renaming (w : List Nat) : Renaming w (canon w) :=
  ⟨pos (firsts w), fun x hx y hy e => pos_inj _ x y ((mem_firsts w x).2 hx) ((mem_firsts w y).2 hy) e, rfl⟩

theorem map_self : ∀ (u : List Nat) (h : Nat → Nat), u.map h = u → ∀ x ∈ u, h x = x
  | [], _, _, x, hx => by simp at hx
  | y :: ys, h, e, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at e
    rcases List.mem_cons.1 hx with rfl | hx
    · exact e.1
    · exact map_self ys h e.2 x hx

/-- two canonical words related by a renaming are equal -/
theorem rgs_rename_eq : ∀ n, ∀ v ∈ rgs n, ∀ v' ∈ rgs n, ∀ h : Nat → Nat,
    (∀ x ∈ v, ∀ y ∈ v, h x = h y → x = y) → v' = v.map h → v' = v
  | 0, v, hv, v', hv', _, _, _ => by simp [rgs] at hv hv'; rw [hv, hv']
  | n + 1, v, hv, v', hv', h, hinj, e => by
    obtain ⟨u, hu, c, hc, rfl⟩ := (mem_rgs_succ n v).1 hv
    obtain ⟨u', hu', c', hc', rfl⟩ := (mem_rgs_succ n v').1 hv'
    rw [List.map_append, List.map_cons, List.map_nil] at e
    have hl : u'.length = (u.map h).length := by rw [List.length_map, len_rgs n u hu, len_rgs n u' hu']
    obtain ⟨e1, e2⟩ := List.append_inj e hl
    simp only [List.cons.injEq, and_true] at e2
    have huu : u' = u := rgs_rename_eq n u hu u' hu' h
      (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])) e1
    subst huu
    have hfix := map_self u' h e1.symm
    have newc : ∀ d, d < nl u' + 1 → d ∉ u' → d = nl u' := by
      intro d hd hn
      apply Classical.byContradiction; intro hne
      exact hn (rgs_canon n u' hu' d (by omega))
    by_cases hcu : c ∈ u'
    · rw [e2, hfix c hcu]
    · have hc0 := newc c hc hcu
      have hc'u : c' ∉ u' := by
        intro hm
        have := hinj c' (by simp [hm]) c (by simp) (by rw [hfix c' hm, ← e2])
        exact hcu (this ▸ hm)
      rw [newc c' hc' hc'u, hc0]

theorem rename_compose (w v v' : List Nat) (h1 : Renaming w v) (h2 : Renaming w v') :
    ∃ h : Nat → Nat, (∀ x ∈ v, ∀ y ∈ v, h x = h y → x = y) ∧ v' = v.map h := by
  obtain ⟨f, hf, rfl⟩ := h1
  obtain ⟨g, hg, rfl⟩ := h2
  let h : Nat → Nat := fun y => if hh : ∃ x, x ∈ w ∧ f x = y then g (Classical.choose hh) else y
  have key : ∀ x ∈ w, h (f x) = g x := by
    intro x hx
    have hh : ∃ x', x' ∈ w ∧ f x' = f x := ⟨x, hx, rfl⟩
    show dite _ _ _ = _
    rw [dite_eq_left hh]
    obtain ⟨m, e⟩ := Classical.choose_spec hh
    rw [hf _ m x hx e]
  refine ⟨h, ?_, ?_⟩
  · intro y1 hy1 y2 hy2 e
    obtain ⟨x1, hx1, rfl⟩ := List.mem_map.1 hy1
    obtain ⟨x2, hx2, rfl⟩ := List.mem_map.1 hy2
    rw [key x1 hx1, key x2 hx2] at e
    rw [hg x1 hx1 x2 hx2 e]
  · rw [List.map_map]; apply List.map_congr_left; intro x hx; exact (key x hx).symm

/-- **Canonical representatives.** Every word is a renaming of exactly one restricted growth string. -/
theorem canonical (w : List Nat) :
    ∃ v ∈ rgs w.length, Renaming w v ∧ ∀ v' ∈ rgs w.length, Renaming w v' → v' = v := by
  refine ⟨canon w, canon_mem _ w rfl, canon_renaming w, ?_⟩
  intro v' hv' hr
  obtain ⟨h, hinj, e⟩ := rename_compose w (canon w) v' (canon_renaming w) hr
  exact rgs_rename_eq _ (canon w) (canon_mem _ w rfl) v' hv' h hinj e

/-! ## renaming keeps flip-connectivity of kernel classes -/

theorem kc_tr (w w' : Nat → Nat) (n : Nat) (h : ∀ p q, p < n → q < n → (w p = w q ↔ w' p = w' q))
    (hK : KerConn w n) : KerConn w' n := by
  intro T T' hT hT' heq
  have e := ker_tr w w' n (fun p q hp hq e => (h p q hp hq).2 e) T T' (bnd hT) (bnd hT') heq
  exact kerflip_tr w' w n (fun p q hp hq e => (h p q hp hq).1 e) (hK T T' hT hT' e) (bnd hT)

theorem kerconn_rename (w v : List Nat) (hr : Renaming w v) :
    KerConn (wd w) w.length ↔ KerConn (wd v) v.length := by
  obtain ⟨f, hf, rfl⟩ := hr
  have hwd : ∀ p, p < w.length → wd (w.map f) p = f (wd w p) := by
    intro p hp; simp only [wd]
    rw [getD_eq _ _ (by simpa using hp), getD_eq _ _ hp, List.getElem_map]
  have hmem : ∀ p, p < w.length → wd w p ∈ w := by
    intro p hp; simp only [wd]; rw [getD_eq _ _ hp]; exact List.getElem_mem hp
  have h : ∀ p q, p < w.length → q < w.length → (wd w p = wd w q ↔ wd (w.map f) p = wd (w.map f) q) := by
    intro p q hp hq; rw [hwd p hp, hwd q hq]
    exact ⟨fun e => by rw [e], fun e => hf _ (hmem p hp) _ (hmem q hq) e⟩
  rw [List.length_map]
  exact ⟨kc_tr _ _ _ h, kc_tr _ _ _ (fun p q hp hq => (h p q hp hq).symm)⟩

/-! ## Stirling numbers of the second kind and the Bell sum -/

/-- canonical words of length `n` with exactly `k` letters (`S(n, k)`) -/
def stirling (n k : Nat) : Nat := (rgs n).countP (fun w => decide (nl w = k))

theorem nl_le_len : ∀ n, ∀ w ∈ rgs n, nl w ≤ n
  | 0, w, h => by simp [rgs] at h; subst h; simp [nl]
  | n + 1, w, h => by
    obtain ⟨v, hv, c, hc, rfl⟩ := (mem_rgs_succ n w).1 h
    have := nl_le_len n v hv
    rw [nl_append, Nat.max_def]; split <;> omega

theorem cnt_lt (t : Nat) : ∀ m, (List.range m).countP (fun c => decide (c < t)) = min m t
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.countP_append, cnt_lt t m]
    by_cases h : m < t <;> simp [h, Nat.min_def] <;> split <;> split <;> omega

theorem cnt_eq (k : Nat) : (List.range (k + 1)).countP (fun c => decide (c = k)) = 1 := by
  rw [List.range_succ, List.countP_append, (List.countP_eq_zero).2 (fun c hc => by simp at hc ⊢; omega)]
  simp

theorem ext_stirling (w : List Nat) (hw : w ≠ []) (k : Nat) :
    (ext w).countP (fun v => decide (nl v = k + 1)) =
      (if decide (nl w = k + 1) then k + 1 else 0) + (if decide (nl w = k) then 1 else 0) := by
  have h0 := nl_pos w hw
  simp only [ext, List.countP_map]
  by_cases h1 : nl w = k + 1
  · have e : ((fun v => decide (nl v = k + 1)) ∘ fun c => w ++ [c]) = fun c => decide (c < k + 1) := by
      funext c; simp only [Function.comp, nl_append, h1, Nat.max_def]; congr 1; apply propext; split <;> omega
    rw [e, cnt_lt, h1]; simp
  · by_cases h2 : nl w = k
    · have e : ((fun v => decide (nl v = k + 1)) ∘ fun c => w ++ [c]) = fun c => decide (c = k) := by
        funext c; simp only [Function.comp, nl_append, h2, Nat.max_def]; congr 1; apply propext; split <;> omega
      rw [e, h2, cnt_eq]; simp
    · rw [(List.countP_eq_zero).2 (fun c hc => by
        simp only [List.mem_range] at hc
        simp only [Function.comp, nl_append, Nat.max_def, decide_eq_true_eq]; split <;> omega)]
      simp [h1, h2]

/-- **The Stirling recurrence** `S(n+1, k+1) = (k+1)·S(n, k+1) + S(n, k)` (for `n ≥ 1`), the recurrence
that counts set partitions by number of blocks. -/
theorem stirling_rec (m k : Nat) :
    stirling (m + 2) (k + 1) = (k + 1) * stirling (m + 1) (k + 1) + 1 * stirling (m + 1) k :=
  Count.step _ (fun w => decide (nl w = k + 1)) (fun w => decide (nl w = k)) (k + 1) 1 m
    (fun w hw => ext_stirling w hw k)

theorem stirling_one (k : Nat) : stirling 1 k = if k = 1 then 1 else 0 := by
  simp only [stirling]; show List.countP _ [[0]] = _
  by_cases h : k = 1 <;> simp [h, nl] <;> omega

def ssum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => ssum f N + f N

theorem ssum_add (f g : Nat → Nat) : ∀ N, ssum (fun k => f k + g k) N = ssum f N + ssum g N
  | 0 => rfl
  | N + 1 => by simp only [ssum, ssum_add f g N]; omega

theorem ssum_zero : ∀ N, ssum (fun _ => 0) N = 0
  | 0 => rfl
  | N + 1 => by simp only [ssum, ssum_zero N]

theorem ssum_ind (j : Nat) : ∀ M, ssum (fun k => if j = k then 1 else 0) M = if j < M then 1 else 0
  | 0 => rfl
  | M + 1 => by
    simp only [ssum, ssum_ind j M]
    by_cases h1 : j < M
    · have : j ≠ M := by omega
      simp [h1, this, show j < M + 1 by omega]
    · by_cases h2 : j = M
      · simp [h2]
      · simp [h1, h2, show ¬ j < M + 1 by omega]

theorem len_ssum (N : Nat) : ∀ l : List (List Nat), (∀ w ∈ l, nl w ≤ N) →
    l.length = ssum (fun k => l.countP (fun w => decide (nl w = k))) (N + 1)
  | [], _ => by simp only [List.countP_nil, List.length_nil]; exact (ssum_zero _).symm
  | a :: l, h => by
    have ih := len_ssum N l (fun w hw => h w (by simp [hw]))
    have ha := h a (by simp)
    simp only [List.countP_cons, decide_eq_true_eq, List.length_cons]
    rw [ssum_add, ssum_ind, ← ih, ite_eq_left (by omega)]

/-- **Bell numbers are sums of Stirling numbers**: `Bell(n) = Σ_{k ≤ n} S(n, k)`. -/
theorem bell_eq_sum (n : Nat) : bell n = ssum (stirling n) (n + 1) :=
  len_ssum n (rgs n) (nl_le_len n)

end Canon
