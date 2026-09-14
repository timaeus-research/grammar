/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoordTaylor

/-!
# Face operators of the smooth engine: the subset formula (consult #116 §3.4–3.5)

Over a list `l` of distinct coordinates, the face operator of a Taylor set `J` applies `T_i^{p_i}`
for `i ∈ J` and `R_i^{p_i}` for `i ∉ J` (`faceOp`). Since `T_i + R_i = 1` coordinatewise,
★ `sum_faceOp`: `G = ∑_{J ⊆ l} faceOp J l G` — the SUBSET FORMULA, proved by list induction
(`Finset.sum_powerset_insert`), with no linearity of the operators needed. Taylor operators and
remainders in different coordinates commute (`coordRem_tayList`, `coordTaylor_remList`), so
`faceOp J l G = T_{l∩J} R_{l∖J} G` (`faceOp_eq`), and the iterated Taylor polynomial is the
finite multi-index sum ★ `tayList_eq_sum`:
`T_l G (v) = ∑_{m ∈ idxL l} (∏_i v_i^{m_i}/m_i!) · ∂^m G (v with the `l`-coordinates zeroed)`,
`idxL l = {m : m_i < p_i for i ∈ l, m_i = 0 otherwise}`. Together: the face-`J` term of a smooth
amplitude is a finite sum of Taylor monomials in the `J`-coordinates times flat remainders
`R_{J^c} ∂^m G` evaluated on the face `{v_J = 0}` — the input of the generic face theorem.
Zero `sorry`/`axiom`.
-/

open Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} (p : Fin d → ℕ)

/-! ### Taylor operators over a list -/

/-- `T_{l₁} ⋯ T_{lₖ} G`. -/
noncomputable def tayList : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => coordTaylor i (p i) (tayList l G)

theorem tayList_nil (G : (Fin d → ℝ) → ℝ) : tayList p [] G = G := rfl

theorem tayList_cons (i : Fin d) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    tayList p (i :: l) G = coordTaylor i (p i) (tayList p l G) := rfl

theorem contDiff_tayList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (l : List (Fin d)) :
    ContDiff ℝ ∞ (tayList p l G) := by
  induction l generalizing G with
  | nil => exact hG
  | cons i l ih => exact contDiff_coordTaylor (ih hG) i (p i)

theorem pdPow_tayList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {j : Fin d} {l : List (Fin d)}
    (hj : j ∉ l) (q : ℕ) : pdPow j q (tayList p l G) = tayList p l (pdPow j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    rw [tayList_cons, pdPow_coordTaylor (contDiff_tayList p hG l) hji, ih hG hjl, tayList_cons]

theorem coordRem_tayList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {j : Fin d}
    {l : List (Fin d)} (hj : j ∉ l) (q : ℕ) :
    coordRem j q (tayList p l G) = tayList p l (coordRem j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    rw [tayList_cons, ← coordTaylor_coordRem_comm (contDiff_tayList p hG l) hji.symm, ih hG hjl,
      tayList_cons]

theorem coordTaylor_remList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {j : Fin d}
    {l : List (Fin d)} (hj : j ∉ l) (q : ℕ) :
    coordTaylor j q (remList p l G) = remList p l (coordTaylor j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    rw [remList_cons, coordTaylor_coordRem_comm (contDiff_remList p hG l) hji, ih hG hjl,
      remList_cons]

/-! ### The face operator and the subset formula -/

/-- The face operator of the Taylor set `J`: `T_i` for `i ∈ J`, `R_i` for `i ∉ J`, over `l`. -/
noncomputable def faceOp (J : Finset (Fin d)) :
    List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G =>
    if i ∈ J then coordTaylor i (p i) (faceOp J l G) else coordRem i (p i) (faceOp J l G)

theorem faceOp_nil (J : Finset (Fin d)) (G : (Fin d → ℝ) → ℝ) : faceOp p J [] G = G := rfl

theorem faceOp_cons_of_mem {J : Finset (Fin d)} {i : Fin d} (hi : i ∈ J) (l : List (Fin d))
    (G : (Fin d → ℝ) → ℝ) : faceOp p J (i :: l) G = coordTaylor i (p i) (faceOp p J l G) := by
  simp [faceOp, hi]

theorem faceOp_cons_of_not_mem {J : Finset (Fin d)} {i : Fin d} (hi : i ∉ J) (l : List (Fin d))
    (G : (Fin d → ℝ) → ℝ) : faceOp p J (i :: l) G = coordRem i (p i) (faceOp p J l G) := by
  simp [faceOp, hi]

theorem contDiff_faceOp {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (J : Finset (Fin d))
    (l : List (Fin d)) : ContDiff ℝ ∞ (faceOp p J l G) := by
  induction l generalizing G with
  | nil => exact hG
  | cons i l ih =>
    by_cases hi : i ∈ J
    · rw [faceOp_cons_of_mem p hi]; exact contDiff_coordTaylor (ih hG) i (p i)
    · rw [faceOp_cons_of_not_mem p hi]; exact contDiff_coordRem (ih hG) i (p i)

/-- The face operator only reads membership of the coordinates in the list. -/
theorem faceOp_congr {J J' : Finset (Fin d)} {l : List (Fin d)}
    (h : ∀ i ∈ l, i ∈ J ↔ i ∈ J') (G : (Fin d → ℝ) → ℝ) : faceOp p J l G = faceOp p J' l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hi := h i (List.mem_cons_self ..)
    have h' : ∀ j ∈ l, j ∈ J ↔ j ∈ J' := fun j hj => h j (List.mem_cons_of_mem i hj)
    by_cases hiJ : i ∈ J
    · rw [faceOp_cons_of_mem p hiJ, faceOp_cons_of_mem p (hi.1 hiJ), ih h']
    · rw [faceOp_cons_of_not_mem p hiJ, faceOp_cons_of_not_mem p (fun h'' => hiJ (hi.2 h'')),
        ih h']

theorem faceOp_insert_of_not_mem {J : Finset (Fin d)} {i : Fin d} {l : List (Fin d)} (hi : i ∉ l)
    (G : (Fin d → ℝ) → ℝ) : faceOp p (insert i J) l G = faceOp p J l G :=
  faceOp_congr p (fun j hj => by
    have : j ≠ i := fun h => hi (h ▸ hj)
    simp [Finset.mem_insert, this]) G

/-- ★ **The subset formula**: `G = ∑_{J ⊆ l} faceOp J l G` for a list of distinct coordinates. -/
theorem sum_faceOp {l : List (Fin d)} (hl : l.Nodup) (G : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) :
    G v = ∑ J ∈ l.toFinset.powerset, faceOp p J l G v := by
  induction l generalizing G v with
  | nil => simp [faceOp_nil]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    have hi' : i ∉ l.toFinset := fun h => hi (List.mem_toFinset.1 h)
    rw [List.toFinset_cons, Finset.sum_powerset_insert hi', ← Finset.sum_add_distrib]
    calc G v = ∑ J ∈ l.toFinset.powerset, faceOp p J l G v := ih hl' G v
      _ = _ := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        have hiJ : i ∉ J := fun h => hi' (Finset.mem_powerset.1 hJ h)
        rw [faceOp_cons_of_not_mem p hiJ, faceOp_cons_of_mem p (Finset.mem_insert_self i J),
          faceOp_insert_of_not_mem p hi, add_comm, coordTaylor_add_coordRem]

/-- `faceOp J l G = T_{l ∩ J} (R_{l ∖ J} G)`. -/
theorem faceOp_eq {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (J : Finset (Fin d))
    {l : List (Fin d)} (hl : l.Nodup) :
    faceOp p J l G = tayList p (l.filter (· ∈ J)) (remList p (l.filter (· ∉ J)) G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    by_cases hiJ : i ∈ J
    · rw [faceOp_cons_of_mem p hiJ, ih hG hl', List.filter_cons_of_pos (by simpa using hiJ),
        List.filter_cons_of_neg (by simpa using hiJ), tayList_cons]
    · rw [faceOp_cons_of_not_mem p hiJ, ih hG hl', List.filter_cons_of_neg (by simpa using hiJ),
        List.filter_cons_of_pos (by simpa using hiJ), remList_cons]
      have hi' : i ∉ l.filter (· ∈ J) := fun h => hi (List.mem_of_mem_filter h)
      rw [coordRem_tayList p (contDiff_remList p hG _) hi']

/-! ### Multi-index expansion of the iterated Taylor polynomial -/

/-- `∂^m = ∏_{i ∈ l} ∂_i^{m_i}` over a list. -/
noncomputable def pdMulti (m : Fin d → ℕ) : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => pdPow i (m i) (pdMulti m l G)

theorem pdMulti_nil (m : Fin d → ℕ) (G : (Fin d → ℝ) → ℝ) : pdMulti m [] G = G := rfl

theorem pdMulti_cons (m : Fin d → ℕ) (i : Fin d) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    pdMulti m (i :: l) G = pdPow i (m i) (pdMulti m l G) := rfl

theorem contDiff_pdMulti {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ)
    (l : List (Fin d)) : ContDiff ℝ ∞ (pdMulti m l G) := by
  induction l generalizing G with
  | nil => exact hG
  | cons i l ih => exact contDiff_pdPow (ih hG) i (m i)

theorem pdPow_pdMulti {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (j : Fin d)
    (q : ℕ) (l : List (Fin d)) : pdPow j q (pdMulti m l G) = pdMulti m l (pdPow j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdPow_comm (contDiff_pdMulti (m := m) hG l), ih hG, pdMulti_cons]

theorem pdMulti_update_of_not_mem {m : Fin d → ℕ} {i : Fin d} {l : List (Fin d)} (hi : i ∉ l)
    (n : ℕ) (G : (Fin d → ℝ) → ℝ) : pdMulti (Function.update m i n) l G = pdMulti m l G := by
  induction l generalizing G with
  | nil => rfl
  | cons j l ih =>
    have hji : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem j h)
    rw [pdMulti_cons, pdMulti_cons, ih hil, Function.update_of_ne hji]

/-- Zero the coordinates in `l`. -/
def zeroL (l : List (Fin d)) (v : Fin d → ℝ) : Fin d → ℝ := fun i => if i ∈ l then 0 else v i

theorem zeroL_nil (v : Fin d → ℝ) : zeroL [] v = v := by
  funext i; simp [zeroL]

theorem zeroL_cons (i : Fin d) (l : List (Fin d)) (v : Fin d → ℝ) :
    zeroL (i :: l) v = zeroL l (Function.update v i 0) := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [zeroL]
  · simp [zeroL, hji]

/-- The multi-indices of the list: `m_i < p_i` for `i ∈ l`, `m_i = 0` otherwise. -/
def idxL (l : List (Fin d)) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ l then Finset.range (p i) else {0}

/-- The Taylor monomial `∏_i v_i^{m_i}/m_i!`. -/
noncomputable def tayMono (m : Fin d → ℕ) (v : Fin d → ℝ) : ℝ :=
  ∏ i, v i ^ m i / (m i).factorial

theorem tayMono_zero (v : Fin d → ℝ) : tayMono 0 v = 1 := by
  simp [tayMono]

theorem idxL_nil : idxL p ([] : List (Fin d)) = {0} := by
  unfold idxL
  simp only [List.not_mem_nil, if_false]
  exact Fintype.piFinset_singleton (fun _ => (0 : ℕ))

theorem mem_idxL_zero {l : List (Fin d)} {m : Fin d → ℕ} (hm : m ∈ idxL p l) {i : Fin d}
    (hi : i ∉ l) : m i = 0 := by
  have := (Fintype.mem_piFinset.1 hm) i
  simpa [hi] using this

/-- `tayMono (m[i := n]) v = v_i^n/n! · tayMono m (v[i := 0])` when `m_i = 0`. -/
theorem tayMono_update {m : Fin d → ℕ} {i : Fin d} (hm : m i = 0) (n : ℕ) (v : Fin d → ℝ) :
    tayMono (Function.update m i n) v =
      v i ^ n / (n.factorial : ℝ) * tayMono m (Function.update v i 0) := by
  unfold tayMono
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j =>
    Function.update v i 0 j ^ m j / (m j).factorial)]
  simp only [Function.update_self, hm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by simpa using hj
  rw [Function.update_of_ne hji, Function.update_of_ne hji]

/-- Splitting the multi-index sum at a coordinate `i ∉ l`. -/
theorem sum_idxL_cons {i : Fin d} {l : List (Fin d)} (hi : i ∉ l) (f : (Fin d → ℕ) → ℝ) :
    ∑ m ∈ idxL p (i :: l), f m =
      ∑ n ∈ Finset.range (p i), ∑ m ∈ idxL p l, f (Function.update m i n) := by
  classical
  set s : Fin d → Finset ℕ := fun j => if j ∈ i :: l then Finset.range (p j) else {0} with hs
  have hsi : s i = Finset.range (p i) := by simp [hs]
  have hupd : Function.update s i {0} = fun j => if j ∈ l then Finset.range (p j) else {0} := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [hi]
    · simp [hs, hji]
  have hmaps : ∀ m ∈ Fintype.piFinset s, m i ∈ Finset.range (p i) := fun m hm => by
    rw [← hsi]; exact (Fintype.mem_piFinset.1 hm) i
  rw [idxL, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← Fintype.piFinset_update_singleton_eq_filter_piFinset_eq s i (hsi ▸ hn), idxL, ← hupd]
  symm
  refine Finset.sum_nbij' (fun m => Function.update m i n) (fun m => Function.update m i 0)
    ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Fintype.mem_piFinset] at hm ⊢
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      have := hm j
      rwa [Function.update_of_ne hji] at this
  · intro m hm
    rw [Fintype.mem_piFinset] at hm ⊢
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      have := hm j
      rwa [Function.update_of_ne hji] at this
  · intro m hm
    have h0 : m i = 0 := by
      have := (Fintype.mem_piFinset.1 hm) i
      simpa using this
    rw [Function.update_idem, ← h0, Function.update_eq_self]
  · intro m hm
    have h0 : m i = n := by
      have := (Fintype.mem_piFinset.1 hm) i
      simpa using this
    rw [Function.update_idem, ← h0, Function.update_eq_self]
  · intro m _; rfl

/-- ★ **The iterated Taylor polynomial as a multi-index sum**:
`T_l G (v) = ∑_{m ∈ idxL l} (∏_i v_i^{m_i}/m_i!) · ∂^m G (v with the l-coordinates zeroed)`. -/
theorem tayList_eq_sum {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {l : List (Fin d)}
    (hl : l.Nodup) (v : Fin d → ℝ) :
    tayList p l G v = ∑ m ∈ idxL p l, tayMono m v * pdMulti m l G (zeroL l v) := by
  induction l generalizing G v with
  | nil => simp [tayList_nil, idxL_nil, tayMono_zero, pdMulti_nil, zeroL_nil]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    rw [tayList_cons, coordTaylor_apply, sum_idxL_cons p hi]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pdPow_tayList p hG hi, ih (contDiff_pdPow hG i n) hl', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h0 : m i = 0 := mem_idxL_zero p hm hi
    rw [tayMono_update h0, pdMulti_cons, pdMulti_update_of_not_mem hi, zeroL_cons,
      Function.update_self, pdPow_pdMulti hG]
    ring

end SmoothEngine

end Grammar
