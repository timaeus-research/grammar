/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensityLeadCoeff

/-!
# The second-top coefficient of the state density (unit 361; Astra #45 unit 2, step 1)

Let `l = min (wᵢ + 1)` with multiplicity `m ≥ 2` and `v = eval (stateDensityRep n w)`.  Unit 226
identified the top coefficient `c_{l,m-1} = (1/(m-1)!) ∏_{wᵢ+1≠l} 1/(wᵢ+1-l)` by an Abelian
argument.  Here the **second-top coefficient** (of `z^{l-1} (-log z)^{m-2}`) is identified by a
second-order Abelian argument:
```
c_{l,m-2} = -(1/(m-2)!) · (∏_{wᵢ+1≠l} 1/(wᵢ+1-l)) · ∑_{wᵢ+1≠l} 1/(wᵢ+1-l)
```
(`stateDensityRep_secondCoeff`).  Both `((s+l)^m M(s) − (m-1)! c_{l,m-1})/(s+l)` computed from the
termwise transform (`list_tendsto₂`) and the difference quotient of the product
`P(s) = ∏_{wᵢ+1≠l} 1/(wᵢ+s+1)` (`product_hasDerivAt`) converge as `s → -l⁺`; the two limits agree.
Coefficients at log degree `≥ expMult` vanish (`stateDensityRep_coeffAt_eq_zero_of_le`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

theorem PowLogRep.coeffAt_eq_zero_of_forall (c : PowLogRep) (μ : ℝ) (j : ℕ)
    (h : ∀ t ∈ c, t.1 = μ → t.2.1 ≠ j) : PowLogRep.coeffAt c μ j = 0 := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    rw [PowLogRep.coeffAt_cons, ih fun u hu => h u (List.mem_cons_of_mem t hu),
      if_neg fun h' => h t (List.mem_cons_self ..) h'.1 h'.2, zero_add]

/-- Coefficients of the state density vanish at log degree `≥ expMult`. -/
theorem stateDensityRep_coeffAt_eq_zero_of_le (n : ℕ) (w : Fin (n + 1) → ℝ) (μ : ℝ) {j : ℕ}
    (hj : expMult w μ ≤ j) : PowLogRep.coeffAt (stateDensityRep n w) μ j = 0 :=
  PowLogRep.coeffAt_eq_zero_of_forall _ μ j fun t ht htμ hjt => by
    have := stateDensityRep_degree_lt n w t ht
    rw [htμ, hjt] at this
    omega

/-! ### The second-order Abelian limits -/

/-- Second-order limit of one term of the termwise Mellin transform. -/
theorem term_tendsto₂ (l : ℝ) (m : ℕ) (hm : 2 ≤ m) (t : ℝ × ℕ × ℝ) (hμ : l ≤ t.1)
    (hdeg : t.1 = l → t.2.1 < m) :
    Tendsto (fun s : ℝ =>
        ((s + l) ^ m * (t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))) -
          (if t.1 = l ∧ t.2.1 = m - 1 then t.2.2 * ((m - 1).factorial : ℝ) else 0)) / (s + l))
      (𝓝[>] (-l))
      (𝓝 (if t.1 = l ∧ t.2.1 = m - 2 then t.2.2 * ((m - 2).factorial : ℝ) else 0)) := by
  obtain ⟨μ, j, c⟩ := t
  simp only at hμ hdeg ⊢
  by_cases hμl : μ = l
  · subst hμl
    have hj : j < m := hdeg rfl
    by_cases hjm : j = m - 1
    · subst hjm
      have hev : ∀ᶠ s in 𝓝[>] (-μ), (0 : ℝ) =
          ((s + μ) ^ m * (c * (((m - 1).factorial : ℝ) / (s + μ) ^ (m - 1 + 1))) -
            (if μ = μ ∧ m - 1 = m - 1 then c * ((m - 1).factorial : ℝ) else 0)) / (s + μ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs0 : s + μ ≠ 0 := by
          have : -μ < s := hs
          linarith
        rw [if_pos ⟨rfl, rfl⟩, show m - 1 + 1 = m by omega]
        field_simp
        ring
      rw [if_neg (show ¬ (μ = μ ∧ m - 1 = m - 2) from fun h => by have := h.2; omega)]
      exact tendsto_const_nhds.congr' hev
    · have hev : ∀ᶠ s in 𝓝[>] (-μ),
          c * (j.factorial : ℝ) * (s + μ) ^ (m - 2 - j) =
            ((s + μ) ^ m * (c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) -
              (if μ = μ ∧ j = m - 1 then c * ((m - 1).factorial : ℝ) else 0)) / (s + μ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs0 : s + μ ≠ 0 := by
          have : -μ < s := hs
          linarith
        rw [if_neg fun h => hjm h.2, sub_zero]
        have hpow : (s + μ) ^ m = (s + μ) ^ (m - 2 - j) * (s + μ) ^ (j + 1) * (s + μ) := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [hpow]
        field_simp
      have hlim := ((tendsto_add_min μ).pow (m - 2 - j)).const_mul (c * (j.factorial : ℝ))
      have key : (if μ = μ ∧ j = m - 2 then c * ((m - 2).factorial : ℝ) else 0) =
          c * (j.factorial : ℝ) * (0 : ℝ) ^ (m - 2 - j) := by
        by_cases hjm2 : j = m - 2
        · subst hjm2
          simp
        · rw [if_neg fun h => hjm2 h.2, zero_pow (by omega), mul_zero]
      rw [key]
      exact hlim.congr' hev
  · have hlt : l < μ := lt_of_le_of_ne hμ (Ne.symm hμl)
    have hne : (-l + μ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by linarith)
    have h1 : Tendsto (fun s : ℝ => (s + l) ^ (m - 1)) (𝓝[>] (-l)) (𝓝 0) := by
      have := (tendsto_add_min l).pow (m - 1)
      rwa [zero_pow (by omega)] at this
    have h2 : Tendsto (fun s : ℝ => c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) (𝓝[>] (-l))
        (𝓝 (c * ((j.factorial : ℝ) / (-l + μ) ^ (j + 1)))) :=
      tendsto_const_nhds.mul
        (tendsto_const_nhds.div ((tendsto_add_const_min l μ).pow (j + 1)) hne)
    rw [if_neg (show ¬ (μ = l ∧ j = m - 2) from fun h => hμl h.1)]
    have hev : ∀ᶠ s in 𝓝[>] (-l),
        (s + l) ^ (m - 1) * (c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) =
          ((s + l) ^ m * (c * ((j.factorial : ℝ) / (s + μ) ^ (j + 1))) -
            (if μ = l ∧ j = m - 1 then c * ((m - 1).factorial : ℝ) else 0)) / (s + l) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s + l ≠ 0 := by
        have : -l < s := hs
        linarith
      rw [if_neg fun h => hμl h.1, sub_zero]
      have hpow : (s + l) ^ m = (s + l) ^ (m - 1) * (s + l) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      field_simp
    simpa using (h1.mul h2).congr' hev

/-- Second-order limit of the termwise Mellin sum: `((s+l)^m M(s) − (m-1)! c_{l,m-1})/(s+l)`
tends to `(m-2)! c_{l,m-2}`. -/
theorem list_tendsto₂ (l : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    ∀ c : PowLogRep, (∀ t ∈ c, l ≤ t.1 ∧ (t.1 = l → t.2.1 < m)) →
      Tendsto (fun s : ℝ => ((s + l) ^ m *
          (c.map fun t => t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))).sum -
          ((m - 1).factorial : ℝ) * PowLogRep.coeffAt c l (m - 1)) / (s + l))
        (𝓝[>] (-l)) (𝓝 (((m - 2).factorial : ℝ) * PowLogRep.coeffAt c l (m - 2))) := by
  intro c
  induction c with
  | nil =>
    intro _
    simp only [List.map_nil, List.sum_nil, mul_zero, PowLogRep.coeffAt_nil, sub_zero, zero_div]
    exact tendsto_const_nhds
  | cons t c ih =>
    intro hc
    have ht := hc t (List.mem_cons_self ..)
    have hrest := ih fun u hu => hc u (List.mem_cons_of_mem t hu)
    have hterm := term_tendsto₂ l m hm t ht.1 ht.2
    have hfun : (fun s : ℝ => ((s + l) ^ m *
        ((t :: c).map fun u => u.2.2 * ((u.2.1.factorial : ℝ) / (s + u.1) ^ (u.2.1 + 1))).sum -
          ((m - 1).factorial : ℝ) * PowLogRep.coeffAt (t :: c) l (m - 1)) / (s + l)) =
        fun s => ((s + l) ^ m * (t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))) -
            (if t.1 = l ∧ t.2.1 = m - 1 then t.2.2 * ((m - 1).factorial : ℝ) else 0)) / (s + l) +
          ((s + l) ^ m *
            (c.map fun u => u.2.2 * ((u.2.1.factorial : ℝ) / (s + u.1) ^ (u.2.1 + 1))).sum -
            ((m - 1).factorial : ℝ) * PowLogRep.coeffAt c l (m - 1)) / (s + l) := by
      funext s
      simp only [List.map_cons, List.sum_cons]
      rw [PowLogRep.coeffAt_cons]
      split_ifs <;> ring
    have hlim : ((m - 2).factorial : ℝ) * PowLogRep.coeffAt (t :: c) l (m - 2) =
        (if t.1 = l ∧ t.2.1 = m - 2 then t.2.2 * ((m - 2).factorial : ℝ) else 0) +
          ((m - 2).factorial : ℝ) * PowLogRep.coeffAt c l (m - 2) := by
      rw [PowLogRep.coeffAt_cons]
      split_ifs <;> ring
    rw [hfun, hlim]
    exact hterm.add hrest

/-- The product `P(s) = ∏_{wᵢ+1≠l} 1/(wᵢ+s+1)` is differentiable at `s = -l`, with derivative
`-P(-l) ∑_{wᵢ+1≠l} 1/(wᵢ+1-l)`. -/
theorem product_hasDerivAt {d : ℕ} (w : Fin d → ℝ) (l : ℝ) :
    HasDerivAt (fun s : ℝ => ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + s + 1))
      (-(∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l)) *
        ∑ i, if w i + 1 = l then (0 : ℝ) else 1 / (w i + 1 - l)) (-l) := by
  have hne : ∀ i, w i + 1 = l ∨ w i + 1 - l ≠ 0 := fun i => by
    by_cases hi : w i + 1 = l
    · exact Or.inl hi
    · exact Or.inr (sub_ne_zero.2 hi)
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasDerivAt (fun s : ℝ => if w i + 1 = l then (1 : ℝ) else 1 / (w i + s + 1))
        (if w i + 1 = l then (0 : ℝ) else -(1 / (w i + 1 - l) ^ 2)) (-l) := by
    intro i _
    by_cases hi : w i + 1 = l
    · simp only [if_pos hi]
      exact hasDerivAt_const _ _
    · simp only [if_neg hi]
      have hne' : w i + -l + 1 ≠ 0 := by
        have := (hne i).resolve_left hi
        intro h0
        exact this (by linarith)
      have h1 : HasDerivAt (fun s : ℝ => w i + s + 1) 1 (-l) := by
        simpa using ((hasDerivAt_id (-l)).const_add (w i)).add_const 1
      have h2 := h1.inv hne'
      have h3 : HasDerivAt (fun s : ℝ => (w i + s + 1)⁻¹) (-(1 / (w i + 1 - l) ^ 2)) (-l) := by
        refine h2.congr_deriv ?_
        rw [show w i + -l + 1 = w i + 1 - l by ring]
        ring
      simpa only [one_div] using h3
  refine (HasDerivAt.fun_finsetProd hf).congr_deriv ?_
  rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : w i + 1 = l
  · simp [hi]
  · have hne' := (hne i).resolve_left hi
    rw [smul_eq_mul, if_neg hi, if_neg hi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      if_neg hi]
    have : ∀ j, (if w j + 1 = l then (1 : ℝ) else 1 / (w j + -l + 1)) =
        if w j + 1 = l then (1 : ℝ) else 1 / (w j + 1 - l) := fun j => by
      congr 2
      ring
    simp only [this]
    field_simp

/-- The product form of `(s+l)^m M(s)` for `s > -l`. -/
theorem product_eq_pow_mul {d : ℕ} (w : Fin d → ℝ) (l : ℝ) {s : ℝ} (hs : -l < s) :
    (∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + s + 1)) =
      (s + l) ^ expMult w l * ∏ i, 1 / (w i + s + 1) := by
  have hs0 : s + l ≠ 0 := by linarith
  have hpow : (s + l) ^ expMult w l = ∏ i, (if w i + 1 = l then s + l else 1) := by
    simp only [expMult]
    rw [← Finset.prod_filter (fun i => w i + 1 = l) (fun _ => s + l), Finset.prod_const]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : w i + 1 = l
  · rw [if_pos hi, if_pos hi, show w i + s + 1 = s + l by linarith]
    field_simp
  · rw [if_neg hi, if_neg hi, one_mul]

/-! ### The second-top coefficient -/

/-- **Second-top coefficient of the state density**: with `l = min (wᵢ+1)` of multiplicity
`m ≥ 2`, `coeffAt v l (m-2) = -(1/(m-2)!) (∏_{wᵢ+1≠l} 1/(wᵢ+1-l)) ∑_{wᵢ+1≠l} 1/(wᵢ+1-l)`. -/
theorem stateDensityRep_secondCoeff (n : ℕ) (w : Fin (n + 1) → ℝ) (l : ℝ) (hl : ∀ i, l ≤ w i + 1)
    (hm : 2 ≤ expMult w l) :
    PowLogRep.coeffAt (stateDensityRep n w) l (expMult w l - 2) =
      -(1 / ((expMult w l - 2).factorial : ℝ)) *
        ((∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l)) *
          ∑ i, if w i + 1 = l then (0 : ℝ) else 1 / (w i + 1 - l)) := by
  have hatt : ∃ i, w i + 1 = l := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < (Finset.univ.filter fun i => w i + 1 = l).card by
      unfold expMult at hm; omega)
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  have hlead := stateDensityRep_leadCoeff n w l hl hatt
  set m := expMult w l with hm_def
  have hc : ∀ t ∈ stateDensityRep n w, l ≤ t.1 ∧ (t.1 = l → t.2.1 < m) := by
    intro t ht
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n w t ht
    refine ⟨by rw [hi]; exact hl i, fun htl => ?_⟩
    have := stateDensityRep_degree_lt n w t ht
    rwa [htl] at this
  have hB := list_tendsto₂ l m hm (stateDensityRep n w) hc
  have hP := product_hasDerivAt w l
  set P : ℝ → ℝ := fun s => ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + s + 1) with hPdef
  have hPl : P (-l) = ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l) := by
    simp only [hPdef]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2
    ring
  have hA : Tendsto (fun s => (P s - P (-l)) / (s + l)) (𝓝[>] (-l))
      (𝓝 (-(∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l)) *
        ∑ i, if w i + 1 = l then (0 : ℝ) else 1 / (w i + 1 - l))) := by
    have := (hasDerivAt_iff_tendsto_slope.1 hP).mono_left
      (nhdsWithin_mono _ fun s (hs : -l < s) => Set.mem_compl_singleton_iff.2 hs.ne')
    refine this.congr' (Eventually.of_forall fun s => ?_)
    rw [slope_def_field, sub_neg_eq_add]
  have heq : (fun s => (P s - P (-l)) / (s + l)) =ᶠ[𝓝[>] (-l)] fun s : ℝ => ((s + l) ^ m *
      ((stateDensityRep n w).map fun t =>
        t.2.2 * ((t.2.1.factorial : ℝ) / (s + t.1) ^ (t.2.1 + 1))).sum -
      ((m - 1).factorial : ℝ) * PowLogRep.coeffAt (stateDensityRep n w) l (m - 1)) / (s + l) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : -l < s := hs
    congr 1
    have hfac : (((m - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hY : ((m - 1).factorial : ℝ) * (1 / ((m - 1).factorial : ℝ) *
        ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l)) =
        ∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l) := by
      field_simp
    rw [hlead, hPl, hY]
    congr 1
    simp only [hPdef]
    rw [product_eq_pow_mul w l hs']
    congr 1
    rw [← mellin_stateDensity n w s (fun i => by linarith [hl i]),
      mellin_eval _ s (fun t ht => ?_)]
    obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n w t ht
    rw [hi]
    linarith [hl i]
  have h := tendsto_nhds_unique_of_eventuallyEq hA hB heq
  have hfac : (((m - 2).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have : PowLogRep.coeffAt (stateDensityRep n w) l (m - 2) =
      (-(∏ i, if w i + 1 = l then (1 : ℝ) else 1 / (w i + 1 - l)) *
        ∑ i, if w i + 1 = l then (0 : ℝ) else 1 / (w i + 1 - l)) / ((m - 2).factorial : ℝ) := by
    rw [h]
    field_simp
  rw [this]
  ring

end Grammar
