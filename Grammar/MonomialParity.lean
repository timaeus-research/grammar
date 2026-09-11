/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialUnitRemoval

/-!
# Parity and sign of a nonnegative monomial chart (Astra #67 unit 2b)

On a hironaka monomial chart the phase reads `K = u · y^e` with a continuous nonvanishing unit `u`
on an open set `W`. Nonnegativity `K ≥ 0` on `W` forces the structure the paper uses without
comment: at a centre `y₀ ∈ W`,

* every coordinate vanishing at the centre carries an **even** exponent
  (`even_exponent_of_nonneg`: flipping the sign of that coordinate at a nearby point with all
  coordinates nonzero would flip the sign of `K`);
* absorbing the coordinates **nonzero at the centre** into the unit gives the reduced unit
  `u' = u · ∏_{y₀_j ≠ 0} y_j^{e_j}` (`reducedUnit`) and the reduced exponent `e' = e|_{y₀_j = 0}`
  (`reducedExp`), with `K = u' · y^{e'}` near the centre, `e'` even, and `u' > 0` on a
  neighbourhood (`reducedUnit_pos`, `eventually_reducedUnit_pos`), analytic when `u` is.

The packaged statement `exists_even_positive_form` is the input of the exact unit removal
(`exists_localNormalForm`): a positive analytic unit and even exponents `2k` supported on the
coordinates vanishing at the centre.

Non-claims: nothing is said about the exceptional set or the Jacobian; the sign analysis is
pointwise at one centre.
-/

open Set Filter Topology Monomialize.Analytic

namespace Grammar

variable {d : ℕ}

/-- The probe point: the coordinates of `y₀` that vanish are replaced by the prescribed values
`s`, the others are kept. -/
noncomputable def probe (y₀ s : Fin d → ℝ) : Fin d → ℝ := fun j => if y₀ j = 0 then s j else y₀ j

theorem probe_ne_zero {y₀ s : Fin d → ℝ} (hs : ∀ j, s j ≠ 0) (j : Fin d) : probe y₀ s j ≠ 0 := by
  unfold probe
  split_ifs with h
  · exact hs j
  · exact h

theorem dist_probe_le {y₀ s : Fin d → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hs : ∀ j, |s j| ≤ ε) :
    dist (probe y₀ s) y₀ ≤ ε := by
  refine dist_pi_le_iff hε |>.2 fun j => ?_
  unfold probe
  split_ifs with h
  · rw [h, Real.dist_eq, sub_zero]; exact hs j
  · simpa using hε

theorem probe_update {y₀ s : Fin d → ℝ} {i : Fin d} (hi : y₀ i = 0) (c : ℝ) :
    probe y₀ (Function.update s i c) = Function.update (probe y₀ s) i c := by
  funext j
  by_cases h : j = i
  · subst h; simp [probe, hi]
  · simp [probe, Function.update_of_ne h]

/-- Flipping the sign of one coordinate multiplies the monomial by `(-1)^{e_i}`. -/
theorem prod_pow_update_neg (y : Fin d → ℝ) (e : Fin d →₀ ℕ) (i : Fin d) :
    ∏ j, Function.update y i (-(y i)) j ^ e j = (-1) ^ e i * ∏ j, y j ^ e j := by
  classical
  have h1 : (fun j => Function.update y i (-(y i)) j ^ e j) =
      Function.update (fun j => y j ^ e j) i ((-(y i)) ^ e i) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : (fun j => y j ^ e j) = Function.update (fun j => y j ^ e j) i (y i ^ e i) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, Finset.prod_update_of_mem (Finset.mem_univ i)]
  conv_rhs => rw [h2, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [neg_pow]
  ring

/-- **Parity.** If `K = u · y^e ≥ 0` on an open set around `y₀` with `u` continuous and nonzero at
`y₀`, every coordinate vanishing at `y₀` has an even exponent. -/
theorem even_exponent_of_nonneg {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
    {e : Fin d →₀ ℕ} (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y)
    {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (hu : ContinuousAt u y₀) (hu0 : u y₀ ≠ 0) {i : Fin d}
    (hi : y₀ i = 0) : Even (e i) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  -- a ball around `y₀` inside `W` on which `u` keeps the sign of `u y₀`
  have hsign : ∃ δ : ℝ, 0 < δ ∧ ∀ y, dist y y₀ < δ → y ∈ W ∧ (0 < u y₀ → 0 < u y) ∧
      (u y₀ < 0 → u y < 0) := by
    have hWn : W ∈ 𝓝 y₀ := hW.mem_nhds hy₀
    rcases lt_or_gt_of_ne hu0 with hneg | hpos
    · have h := hu (Iio_mem_nhds hneg)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hWn h)
      exact ⟨δ, hδ, fun y hy => ⟨(hball hy).1, fun h' => absurd h' (not_lt.2 hneg.le),
        fun _ => (hball hy).2⟩⟩
    · have h := hu (Ioi_mem_nhds hpos)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hWn h)
      exact ⟨δ, hδ, fun y hy => ⟨(hball hy).1, fun _ => (hball hy).2,
        fun h' => absurd h' (not_lt.2 hpos.le)⟩⟩
  obtain ⟨δ, hδ, hball⟩ := hsign
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set s : Fin d → ℝ := fun _ => ε with hs
  set y := probe y₀ s with hy
  set y' := probe y₀ (Function.update s i (-ε)) with hy'
  have hyW : dist y y₀ < δ :=
    lt_of_le_of_lt (dist_probe_le hε0.le fun j => by simp [hs, abs_of_pos hε0]) (by linarith)
  have hy'W : dist y' y₀ < δ := by
    refine lt_of_le_of_lt (dist_probe_le hε0.le fun j => ?_) (by linarith)
    by_cases h : j = i
    · subst h; simp [abs_of_pos hε0]
    · simp [Function.update_of_ne h, hs, abs_of_pos hε0]
  have hy'eq : y' = Function.update y i (-(y i)) := by
    rw [hy', probe_update hi, hy]
    congr 1
    simp [probe, hi, hs]
  -- the monomial at `y` is nonzero, and flips sign at `y'`
  have hm : monomialEval y e ≠ 0 := by
    rw [monomialEval_eq_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (probe_ne_zero (fun _ => hε0.ne') j)
  have hm' : monomialEval y' e = -monomialEval y e := by
    rw [monomialEval_eq_prod, monomialEval_eq_prod, hy'eq, prod_pow_update_neg, hodd.neg_one_pow]
    ring
  have hKy := hK0 y (hball y hyW).1
  have hKy' := hK0 y' (hball y' hy'W).1
  rw [hK y (hball y hyW).1] at hKy
  rw [hK y' (hball y' hy'W).1, hm'] at hKy'
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · have h1 := (hball y hyW).2.2 hneg
    have h2 := (hball y' hy'W).2.2 hneg
    rcases lt_or_gt_of_ne hm with hm1 | hm1
    · nlinarith [mul_pos_of_neg_of_neg h1 hm1]
    · nlinarith [mul_neg_of_neg_of_pos h2 hm1]
  · have h1 := (hball y hyW).2.1 hpos
    have h2 := (hball y' hy'W).2.1 hpos
    rcases lt_or_gt_of_ne hm with hm1 | hm1
    · nlinarith [mul_neg_of_pos_of_neg h1 hm1]
    · nlinarith [mul_pos h2 hm1]

/-! ### The reduced unit and exponent at a centre -/

open scoped Classical in
/-- The reduced unit at the centre `y₀`: the unit times the powers of the coordinates that do not
vanish at the centre. -/
noncomputable def reducedUnit (u : (Fin d → ℝ) → ℝ) (e : Fin d →₀ ℕ) (y₀ y : Fin d → ℝ) : ℝ :=
  u y * ∏ j ∈ Finset.univ.filter (fun j => y₀ j ≠ 0), y j ^ e j

open scoped Classical in
/-- The reduced exponent at the centre `y₀`: the exponent restricted to the coordinates vanishing
at the centre. -/
noncomputable def reducedExp (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) : Fin d →₀ ℕ :=
  e.filter (fun j => y₀ j = 0)

theorem reducedExp_apply_of_eq {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} {j : Fin d} (h : y₀ j = 0) :
    reducedExp e y₀ j = e j := by
  simp [reducedExp, h]

theorem reducedExp_apply_of_ne {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} {j : Fin d} (h : y₀ j ≠ 0) :
    reducedExp e y₀ j = 0 := by
  simp [reducedExp, h]

open scoped Classical in
theorem monomialEval_reducedExp (e : Fin d →₀ ℕ) (y₀ y : Fin d → ℝ) :
    monomialEval y (reducedExp e y₀) = ∏ j ∈ Finset.univ.filter (fun j => y₀ j = 0), y j ^ e j := by
  rw [monomialEval_eq_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : y₀ j = 0
  · simp [reducedExp_apply_of_eq h, h]
  · simp [reducedExp_apply_of_ne h, h]

/-- The reduced form of the monomial: `y^e = (∏_{y₀_j ≠ 0} y_j^{e_j}) · y^{e'}`. -/
theorem reducedUnit_mul_monomialEval (u : (Fin d → ℝ) → ℝ) (e : Fin d →₀ ℕ) (y₀ y : Fin d → ℝ) :
    reducedUnit u e y₀ y * monomialEval y (reducedExp e y₀) = u y * monomialEval y e := by
  classical
  rw [reducedUnit, monomialEval_reducedExp, monomialEval_eq_prod, mul_assoc]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => y₀ j = 0)]
  rw [mul_comm]

theorem continuousAt_reducedUnit {u : (Fin d → ℝ) → ℝ} (e : Fin d →₀ ℕ) {y₀ : Fin d → ℝ}
    (hu : ContinuousAt u y₀) : ContinuousAt (reducedUnit u e y₀) y₀ := by
  classical
  exact hu.mul (continuous_finsetProd _ fun j _ => (continuous_apply j).pow _).continuousAt

theorem continuousOn_reducedUnit {u : (Fin d → ℝ) → ℝ} (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ)
    {W : Set (Fin d → ℝ)} (hu : ContinuousOn u W) : ContinuousOn (reducedUnit u e y₀) W := by
  classical
  exact hu.mul (continuous_finsetProd _ fun j _ => (continuous_apply j).pow _).continuousOn

theorem analyticAt_reducedUnit {u : (Fin d → ℝ) → ℝ} (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ)
    {y : Fin d → ℝ} (hu : AnalyticAt ℝ u y) : AnalyticAt ℝ (reducedUnit u e y₀) y := by
  classical
  have h : AnalyticAt ℝ (∏ j ∈ Finset.univ.filter (fun j => y₀ j ≠ 0),
      fun y : Fin d → ℝ => y j ^ e j) y :=
    Finset.analyticAt_prod _ fun j _ =>
      ((ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt y).pow (e j)
  exact hu.mul (h.congr (Filter.Eventually.of_forall fun z => by simp [Finset.prod_apply]))

theorem reducedUnit_ne_zero {u : (Fin d → ℝ) → ℝ} (e : Fin d →₀ ℕ) {y₀ : Fin d → ℝ}
    (hu0 : u y₀ ≠ 0) : reducedUnit u e y₀ y₀ ≠ 0 := by
  classical
  refine mul_ne_zero hu0 (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_)
  exact (Finset.mem_filter.1 hj).2

/-- The reduced monomial is positive off the coordinate hyperplanes when the exponents are even. -/
theorem monomialEval_reducedExp_pos {e : Fin d →₀ ℕ} {y₀ y : Fin d → ℝ}
    (heven : ∀ j, y₀ j = 0 → Even (e j)) (hy : ∀ j, y j ≠ 0) :
    0 < monomialEval y (reducedExp e y₀) := by
  classical
  rw [monomialEval_reducedExp]
  exact Finset.prod_pos fun j hj => (heven j (Finset.mem_filter.1 hj).2).pow_pos (hy j)

/-- **Sign.** Under the parity hypotheses, the reduced unit is positive at the centre. -/
theorem reducedUnit_pos {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
    {e : Fin d →₀ ℕ} (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y)
    {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (hu : ContinuousAt u y₀) (hu0 : u y₀ ≠ 0) :
    0 < reducedUnit u e y₀ y₀ := by
  have heven : ∀ j, y₀ j = 0 → Even (e j) := fun j hj =>
    even_exponent_of_nonneg hW hK hK0 hy₀ hu hu0 hj
  rcases lt_or_gt_of_ne (reducedUnit_ne_zero e hu0) with hneg | hpos
  · exfalso
    have hc := continuousAt_reducedUnit e hu
    have h := Filter.inter_mem (hW.mem_nhds hy₀) (hc (Iio_mem_nhds hneg))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 h
    set ε : ℝ := δ / 2 with hε
    have hε0 : 0 < ε := by positivity
    set y := probe y₀ (fun _ => ε) with hy
    have hyW : dist y y₀ < δ :=
      lt_of_le_of_lt (dist_probe_le hε0.le fun j => by simp [abs_of_pos hε0]) (by linarith)
    have hyW' := hball hyW
    have hKy := hK0 y hyW'.1
    rw [hK y hyW'.1, ← reducedUnit_mul_monomialEval u e y₀ y] at hKy
    have hmpos : 0 < monomialEval y (reducedExp e y₀) :=
      monomialEval_reducedExp_pos heven (probe_ne_zero fun _ => hε0.ne')
    have hneg' : reducedUnit u e y₀ y < 0 := hyW'.2
    nlinarith [mul_neg_of_neg_of_pos hneg' hmpos]
  · exact hpos

theorem eventually_reducedUnit_pos {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
    {e : Fin d →₀ ℕ} (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y)
    {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (hu : ContinuousAt u y₀) (hu0 : u y₀ ≠ 0) :
    ∀ᶠ y in 𝓝 y₀, 0 < reducedUnit u e y₀ y :=
  (continuousAt_reducedUnit e hu) (Ioi_mem_nhds (reducedUnit_pos hW hK hK0 hy₀ hu hu0))

/-- The half exponents `k = e'/2` of the (even) reduced exponent. -/
noncomputable def halfExp (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) : Fin d →₀ ℕ :=
  (reducedExp e y₀).mapRange (· / 2) (Nat.zero_div 2)

theorem halfExp_apply_of_ne {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} {j : Fin d} (h : y₀ j ≠ 0) :
    halfExp e y₀ j = 0 := by
  simp [halfExp, Finsupp.mapRange_apply, reducedExp_apply_of_ne h]

theorem monomialEval_reducedExp_eq_pow_two_mul {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ}
    (heven : ∀ j, y₀ j = 0 → Even (e j)) (y : Fin d → ℝ) :
    monomialEval y (reducedExp e y₀) = ∏ j, y j ^ (2 * halfExp e y₀ j) := by
  rw [monomialEval_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [halfExp, Finsupp.mapRange_apply]
  by_cases h : y₀ j = 0
  · rw [reducedExp_apply_of_eq h, Nat.two_mul_div_two_of_even (heven j h)]
  · rw [reducedExp_apply_of_ne h]

/-- **The even positive form of a nonnegative monomial chart at a centre.** If `K = u · y^e ≥ 0`
on an open `W ∋ y₀` with `u` analytic and nonvanishing on `W`, then on an open `W' ∋ y₀` inside `W`
the phase is `K = u' · ∏ y_j^{2k_j}` with `u' > 0` analytic on `W'` and `k` supported on the
coordinates vanishing at `y₀`. -/
theorem exists_even_positive_form {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
    {e : Fin d →₀ ℕ} (hu : AnalyticOnNhd ℝ u W) (hu0 : ∀ y ∈ W, u y ≠ 0)
    (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y) {y₀ : Fin d → ℝ}
    (hy₀ : y₀ ∈ W) :
    ∃ W' : Set (Fin d → ℝ), IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ u' : (Fin d → ℝ) → ℝ, AnalyticOnNhd ℝ u' W' ∧ (∀ y ∈ W', 0 < u' y) ∧
        ∃ k : Fin d →₀ ℕ, (∀ j, y₀ j ≠ 0 → k j = 0) ∧
          ∀ y ∈ W', K y = u' y * ∏ j, y j ^ (2 * k j) := by
  have hcont : ContinuousAt u y₀ := (hu y₀ hy₀).continuousAt
  have heven : ∀ j, y₀ j = 0 → Even (e j) := fun j hj =>
    even_exponent_of_nonneg hW hK hK0 hy₀ hcont (hu0 y₀ hy₀) hj
  refine ⟨W ∩ (reducedUnit u e y₀) ⁻¹' Ioi 0, ?_, ⟨hy₀, reducedUnit_pos hW hK hK0 hy₀ hcont
    (hu0 y₀ hy₀)⟩, inter_subset_left, reducedUnit u e y₀, ?_, fun y hy => hy.2, halfExp e y₀,
    fun j hj => halfExp_apply_of_ne hj, fun y hy => ?_⟩
  · exact (continuousOn_reducedUnit e y₀ hu.continuousOn).isOpen_inter_preimage hW isOpen_Ioi
  · exact fun y hy => analyticAt_reducedUnit e y₀ (hu y hy.1)
  · rw [hK y hy.1, ← reducedUnit_mul_monomialEval u e y₀ y,
      monomialEval_reducedExp_eq_pow_two_mul heven]

end Grammar
