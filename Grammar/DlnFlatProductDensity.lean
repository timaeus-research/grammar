/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialBoxBridge
import Grammar.NaiveBayesDensity
import Grammar.CrossingFlatDepth

/-!
# The product of uniforms at general depth: the state density `log^m(1/t)/m!`

The law of the product `t = w₀ ⋯ w_m` of `m + 1` independent uniforms on `(0, 1]` has density
`log^m(1/t)/m!` on `(0, 1]` (examples_slop §2): for every measurable `Ψ ≥ 0`,

  `∫_{(0,1]^{m+1}} Ψ(∏ᵢ wᵢ) dw = ∫_0^1 Ψ(t) log^m(1/t)/m! dt`  (★★★ `lintegral_unitBox_prod`),

by induction on `m` — peel the first coordinate (`lintegral_unitBox_succ`), scale the induction
hypothesis by it (`lintegral_Ioc_mul_left`), interchange (Tonelli) and evaluate the fibre integral
`∫_z^1 log^m(a/z)/(m! a) da = log^{m+1}(1/z)/(m+1)!` (`integral_fibre_log_pow`, fundamental theorem
of calculus).  Consequently the flat-prior partition function of the depth-`(m+1)` deep linear
network on the symmetric box, `2^{m+1} ∫_{(0,1]^{m+1}} e^{−N(∏w)²/2}` by evenness, is the reduced
integral `D_m(N)` of `Grammar.CrossingFlatDepth` (★★★ `depthInt_eq_unitBox`), and the general-depth
expansion `depth_flat_allOrders` is a statement about the model.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- The state density of the product of `m + 1` uniforms on `(0, 1]`: `log^m(1/t)/m!`. -/
noncomputable def prodLogDensity (m : ℕ) (t : ℝ) : ℝ := Real.log (1 / t) ^ m / m.factorial

theorem prodLogDensity_nonneg (m : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ prodLogDensity m t := by
  unfold prodLogDensity
  have : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_one_div one_pos ht.1]; simpa using ht.2)
  positivity

theorem measurable_prodLogDensity (m : ℕ) : Measurable (prodLogDensity m) := by
  unfold prodLogDensity
  fun_prop

theorem measurable_prod_pi (d : ℕ) : Measurable fun w : Fin d → ℝ => ∏ i, w i :=
  Finset.measurable_prod _ fun i _ => measurable_pi_apply i

/-- The fibre integral: `∫_z^1 log^m(a/z)/a da = log^{m+1}(1/z)/(m+1)` for `0 < z ≤ 1`. -/
theorem integral_fibre_log_pow (m : ℕ) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    ∫ a in z..1, Real.log (a / z) ^ m / a = Real.log (1 / z) ^ (m + 1) / (m + 1) := by
  have hz0 : 0 < z := hz.1
  have hderiv : ∀ a ∈ uIcc z 1, HasDerivAt (fun a => Real.log (a / z) ^ (m + 1) / (m + 1))
      (Real.log (a / z) ^ m / a) a := by
    intro a ha
    rw [uIcc_of_le hz.2] at ha
    have ha0 : 0 < a := by linarith [ha.1]
    have h1 : HasDerivAt (fun a => a / z) (1 / z) a := (hasDerivAt_id a).div_const z
    have h2 : HasDerivAt (fun a => Real.log (a / z)) ((1 / z) / (a / z)) a :=
      h1.log (by positivity)
    have h3 := (h2.pow (m + 1)).div_const ((m : ℝ) + 1)
    refine h3.congr_deriv ?_
    push_cast
    field_simp
  have hint : IntervalIntegrable (fun a => Real.log (a / z) ^ m / a) volume z 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hz.2]
    refine ContinuousOn.div (ContinuousOn.pow (Real.continuousOn_log.comp ?_ ?_) m)
      continuousOn_id fun a ha => ne_of_gt (lt_of_lt_of_le hz0 ha.1)
    · exact continuousOn_id.div_const z
    · intro a ha
      exact div_ne_zero (by linarith [ha.1]) hz0.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, div_self hz0.ne', Real.log_one,
    zero_pow (Nat.succ_ne_zero m), zero_div, sub_zero]

/-- The fibre integral in `ℝ≥0∞`, with the `1/m!` normalisation: the density at depth `m + 1`. -/
theorem lintegral_fibre_prodLogDensity (m : ℕ) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ a in Ioc z 1, ENNReal.ofReal (prodLogDensity m (z / a) * a⁻¹) =
      ENNReal.ofReal (prodLogDensity (m + 1) z) := by
  have hz0 : 0 < z := hz.1
  have hpt : ∀ a ∈ Ioc z 1, prodLogDensity m (z / a) * a⁻¹ =
      (1 / m.factorial) * (Real.log (a / z) ^ m / a) := by
    intro a ha
    unfold prodLogDensity
    rw [one_div_div]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc fun a ha => congrArg ENNReal.ofReal (hpt a ha)]
  have hint : IntegrableOn (fun a => (1 / m.factorial : ℝ) * (Real.log (a / z) ^ m / a))
      (Ioc z 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hz.2]
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le hz.2]
    refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.pow
      (Real.continuousOn_log.comp (continuousOn_id.div_const z) fun a ha => ?_) m)
      continuousOn_id fun a ha => ne_of_gt (lt_of_lt_of_le hz0 ha.1))
    exact div_ne_zero (ne_of_gt (lt_of_lt_of_le hz0 ha.1)) hz0.ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
    fun a ha => by
      have ha0 : 0 < a := by linarith [ha.1]
      have : 0 ≤ Real.log (a / z) := Real.log_nonneg (by rw [le_div_iff₀ hz0]; linarith [ha.1])
      positivity)]
  congr 1
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hz.2, integral_fibre_log_pow m hz]
  unfold prodLogDensity
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Scaling the state density by a factor `a ∈ (0, 1]`: `∫_0^1 G(a t) dt = a⁻¹ ∫_0^a G`. -/
theorem lintegral_Ioc_mul_left {G : ℝ → ℝ≥0∞} (hG : Measurable G) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc (0 : ℝ) 1, G (a * t) = ENNReal.ofReal a⁻¹ * ∫⁻ z in Ioc 0 a, G z := by
  have hg : Measurable fun z : ℝ => (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (z / a) * G z :=
    ((measurable_const.indicator measurableSet_Ioc).comp (measurable_id.div_const a)).mul hG
  have h1 : ∫⁻ t in Ioc (0 : ℝ) 1, G (a * t) =
      ∫⁻ t, (fun z => (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (z / a) * G z) (a * t) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun t => ?_
    simp only [indicator, mul_div_cancel_left₀ _ ha.ne', Pi.one_apply]
    split_ifs <;> simp
  rw [h1, ← lintegral_map hg (measurable_const_mul a), Real.map_volume_mul_left ha.ne',
    lintegral_smul_measure, abs_inv, abs_of_pos ha, smul_eq_mul, ← lintegral_indicator
    measurableSet_Ioc]
  congr 1
  refine lintegral_congr fun z => ?_
  simp only [indicator, Pi.one_apply, mem_Ioc]
  have : (0 < z / a ∧ z / a ≤ 1) ↔ (0 < z ∧ z ≤ a) := by
    rw [div_pos_iff_of_pos_right ha, div_le_one ha]
  simp only [this]
  split_ifs <;> simp

/-- ★★★ **The product of `m + 1` uniforms on `(0, 1]` has density `log^m(1/t)/m!`.** -/
theorem lintegral_unitBox_prod (m : ℕ) {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ w in unitBox (m + 1), Ψ (∏ i, w i) =
      ∫⁻ t in Ioc (0 : ℝ) 1, Ψ t * ENNReal.ofReal (prodLogDensity m t) := by
  induction m generalizing Ψ with
  | zero =>
    rw [lintegral_unitBox_succ 0 (fun w => Ψ (∏ i, w i)) (hΨ.comp (measurable_prod_pi 1))]
    simp only [lintegral_unitBox_zero]
    refine setLIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
    simp [prodLogDensity]
  | succ m ih =>
    rw [lintegral_unitBox_succ (m + 1) (fun w => Ψ (∏ i, w i))
      (hΨ.comp (measurable_prod_pi (m + 2)))]
    have hpeel : ∀ a : ℝ, ∫⁻ b in unitBox (m + 1), Ψ (∏ i, (Fin.cons a b : Fin (m + 2) → ℝ) i) =
        ∫⁻ t in Ioc (0 : ℝ) 1, Ψ (a * t) * ENNReal.ofReal (prodLogDensity m t) := by
      intro a
      have := ih (Ψ := fun t => Ψ (a * t)) (hΨ.comp (measurable_const_mul a))
      have e : ∀ b : Fin (m + 1) → ℝ, ∏ i, (Fin.cons a b : Fin (m + 2) → ℝ) i = a * ∏ i, b i := by
        intro b
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        congr 1
      simp_rw [e]
      exact this
    simp_rw [hpeel]
    -- the kernel on the region `0 < z ≤ a ≤ 1`
    set R : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1} with hR
    have hRm : MeasurableSet R :=
      (measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd measurable_fst).inter
          (measurableSet_le measurable_fst measurable_const))
    set K : ℝ × ℝ → ℝ≥0∞ := R.indicator fun p =>
      Ψ p.2 * ENNReal.ofReal (prodLogDensity m (p.2 / p.1) * p.1⁻¹) with hK
    have hKm : Measurable K :=
      (hΨ.comp measurable_snd).mul (((measurable_prodLogDensity m).comp
        (measurable_snd.div measurable_fst)).mul measurable_fst.inv).ennreal_ofReal
        |>.indicator hRm
    -- scale the inner integral by `a`
    have hscale : ∀ a ∈ Ioc (0 : ℝ) 1,
        ∫⁻ t in Ioc (0 : ℝ) 1, Ψ (a * t) * ENNReal.ofReal (prodLogDensity m t) =
          ∫⁻ z, K (a, z) := by
      intro a ha
      have hG : Measurable fun z : ℝ => Ψ z * ENNReal.ofReal (prodLogDensity m (z / a)) :=
        hΨ.mul ((measurable_prodLogDensity m).comp (measurable_id.div_const a)).ennreal_ofReal
      have h1 : ∫⁻ t in Ioc (0 : ℝ) 1, Ψ (a * t) * ENNReal.ofReal (prodLogDensity m t) =
          ∫⁻ t in Ioc (0 : ℝ) 1, (fun z => Ψ z * ENNReal.ofReal (prodLogDensity m (z / a)))
            (a * t) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
        simp only [mul_div_cancel_left₀ _ ha.1.ne']
      rw [h1, lintegral_Ioc_mul_left hG ha.1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun z => ?_
      simp only [hK, hR, indicator, mem_Ioc, mem_ofPred_eq]
      by_cases hz : 0 < z ∧ z ≤ a
      · rw [if_pos hz, if_pos ⟨hz.1, hz.2, ha.2⟩, ENNReal.ofReal_mul (prodLogDensity_nonneg m ⟨by
          rw [div_pos_iff_of_pos_right ha.1]; exact hz.1, by rw [div_le_one ha.1]; exact hz.2⟩)]
        ring
      · rw [if_neg hz, if_neg fun h => hz ⟨h.1, h.2.1⟩]
    rw [setLIntegral_congr_fun measurableSet_Ioc hscale]
    -- the outer integrand vanishes off `(0, 1]`, so integrate over the whole line and swap
    have hKzero : ∀ a z : ℝ, a ∉ Ioc (0 : ℝ) 1 ∨ z ∉ Ioc (0 : ℝ) 1 → K (a, z) = 0 := by
      intro a z h
      simp only [hK, hR, indicator, mem_ofPred_eq]
      rw [if_neg]
      intro hp
      rcases h with h | h
      · exact h ⟨lt_of_lt_of_le hp.1 hp.2.1, hp.2.2⟩
      · exact h ⟨hp.1, hp.2.1.trans hp.2.2⟩
    have houter : ∫⁻ a in Ioc (0 : ℝ) 1, ∫⁻ z, K (a, z) = ∫⁻ a, ∫⁻ z, K (a, z) := by
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun a => ?_
      by_cases ha : a ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ha]
      · rw [indicator_of_notMem ha]
        symm
        simp only [hKzero a _ (Or.inl ha), lintegral_zero]
    have hswap : ∫⁻ a, ∫⁻ z, K (a, z) = ∫⁻ z, ∫⁻ a, K (a, z) :=
      lintegral_lintegral_swap (f := fun a z => K (a, z)) hKm.aemeasurable
    rw [houter, hswap, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hz]
      have e : (fun a => K (a, z)) = fun a => Ψ z * (Icc z 1).indicator
          (fun a => ENNReal.ofReal (prodLogDensity m (z / a) * a⁻¹)) a := by
        funext a
        simp only [hK, hR, indicator, mem_ofPred_eq, mem_Icc]
        by_cases h : z ≤ a ∧ a ≤ 1
        · rw [if_pos ⟨hz.1, h⟩, if_pos h]
        · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]
      have hmeas : Measurable fun a : ℝ => ENNReal.ofReal (prodLogDensity m (z / a) * a⁻¹) :=
        (((measurable_prodLogDensity m).comp (measurable_const.div measurable_id)).mul
          measurable_inv).ennreal_ofReal
      rw [e, lintegral_const_mul _ (hmeas.indicator measurableSet_Icc),
        lintegral_indicator measurableSet_Icc,
        setLIntegral_congr Ioc_ae_eq_Icc.symm, lintegral_fibre_prodLogDensity m hz]
    · rw [indicator_of_notMem hz]
      simp only [hKzero _ z (Or.inr hz), lintegral_zero]

/-! ### The flat-prior partition function of the deep linear network at depth `m + 1` -/

theorem integrableOn_exp_prodLogDensity (m : ℕ) (N : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ 2 / 2) * prodLogDensity m t) (Ioc 0 1) := by
  set δ : ℝ := 1 / (2 * (m + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hmδ : (m : ℝ) * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hcont : Continuous fun t : ℝ => Real.exp (-N * t ^ 2 / 2) := by fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ((integrableOn_rpow_Ioc (c := -(m * δ)) (by linarith)).const_mul
    (M / (δ ^ m * m.factorial))).mono' ?_ ?_
  · exact (hcont.measurable.mul (measurable_prodLogDensity m)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prodLogDensity_nonneg m ht)]
    have h1 : |Real.exp (-N * t ^ 2 / 2)| ≤ M := by
      have := hM t ⟨ht0.le, ht.2⟩
      rwa [Real.norm_eq_abs] at this
    have hlog : Real.log (1 / t) ≤ t ^ (-δ) / δ := by
      rw [one_div, Real.log_inv, ← abs_of_nonneg (neg_nonneg.2 (Real.log_nonpos ht0.le ht.2)),
        abs_neg]
      exact abs_log_le_rpow_div hδpos ht
    have hlog0 : 0 ≤ Real.log (1 / t) :=
      Real.log_nonneg (by rw [le_one_div one_pos ht0]; simpa using ht.2)
    have h2 : prodLogDensity m t ≤ (t ^ (-δ) / δ) ^ m / m.factorial := by
      unfold prodLogDensity
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlog0 hlog m) (by positivity)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
    calc |Real.exp (-N * t ^ 2 / 2)| * prodLogDensity m t
        ≤ M * ((t ^ (-δ) / δ) ^ m / m.factorial) :=
          mul_le_mul h1 h2 (prodLogDensity_nonneg m ht) hM0
      _ = M / (δ ^ m * m.factorial) * t ^ (-(m * δ)) := by
          rw [div_pow, ← Real.rpow_natCast (t ^ (-δ)), ← Real.rpow_mul ht0.le]
          field_simp

/-- ★★★ **The reduced integral is the box integral**: the flat-prior partition function of the
depth-`(m+1)` deep linear network on the positive box is `D_m(N)/2^{m+1}`; on the symmetric box
`[−1,1]^{m+1}` the factor `2^{m+1}` is evenness. -/
theorem depthInt_eq_unitBox (m : ℕ) (N : ℝ) :
    depthInt m N = 2 ^ (m + 1) * ∫ w in unitBox (m + 1), Real.exp (-N * (∏ i, w i) ^ 2 / 2) := by
  have hcont : Continuous fun t : ℝ => Real.exp (-N * t ^ 2 / 2) := by fun_prop
  have hΨ : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-N * t ^ 2 / 2)) :=
    hcont.measurable.ennreal_ofReal
  have hl := lintegral_unitBox_prod m hΨ
  have hbox : IntegrableOn (fun w : Fin (m + 1) → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2))
      (unitBox (m + 1)) := by
    have hc : Continuous fun w : Fin (m + 1) → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2) :=
      hcont.comp (continuous_finsetProd _ fun i _ => continuous_apply i)
    refine (hc.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    exact pi_mono fun _ _ => Ioc_subset_Icc_self
  have h1d := integrableOn_exp_prodLogDensity m N
  rw [← ofReal_integral_eq_lintegral_ofReal hbox (ae_restrict_of_forall_mem
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun _ _ => (Real.exp_pos _).le)] at hl
  have hr : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-N * t ^ 2 / 2)) *
      ENNReal.ofReal (prodLogDensity m t) =
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, Real.exp (-N * t ^ 2 / 2) * prodLogDensity m t) := by
    rw [ofReal_integral_eq_lintegral_ofReal h1d (ae_restrict_of_forall_mem measurableSet_Ioc
      fun t ht => mul_nonneg (Real.exp_pos _).le (prodLogDensity_nonneg m ht))]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hr] at hl
  have hbox0 : 0 ≤ ∫ w in unitBox (m + 1), Real.exp (-N * (∏ i, w i) ^ 2 / 2) :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
      fun _ _ => (Real.exp_pos _).le
  have h1d0 : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, Real.exp (-N * t ^ 2 / 2) * prodLogDensity m t :=
    setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (Real.exp_pos _).le (prodLogDensity_nonneg m ht)
  have heq := (ENNReal.ofReal_eq_ofReal_iff hbox0 h1d0).1 hl
  unfold depthInt
  rw [heq, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  unfold prodLogDensity
  rw [pow_succ]
  ring

end Grammar
