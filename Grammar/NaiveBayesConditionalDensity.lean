/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesFibreMass

/-!
# The conditional density of the covariance given the means

With the support and the fibre mass of DCLX, the naive-Bayes pushforward density is strictly
positive exactly on the punctured interval `(−M₋, M₊) ∖ {0}` (`nbFibreDensity_pos_iff`), the
fibre mass is positive (`nbFibreMass_pos`, indeed `m(λ) ≥ 4(M₊ + M₋)`), and the CONDITIONAL
density `p_λ = ρ(λ, ·)/m(λ)` (`nbConditionalDensity`) is a probability density
(`lintegral_nbConditionalDensity`), so `volume.withDensity p_λ` is a probability measure
(`isProbabilityMeasure_nbConditionalMeasure`).  The unweighted conditional mean is exact:
`∫ z ρ(λ, z) dz = [M₊²(A₊ + 1) − M₋²(A₋ + 1)]/2`, `A± = log(V/M±²)`
(`integral_mul_nbFixedDensity`; antiderivative `z²[(c₁ − L)(c₂ − L) + (c₁ + c₂ − 2L)/2 + ½]`),
hence `E[μ | λ] = [M₊²(A₊ + 1) − M₋²(A₋ + 1)]/(2m(λ))` (`nbConditionalMean`).  This is the
prior conditional mean, NOT the surrogate posterior mean of examples_slop eq. nb_postmu (which
carries the likelihood weight).  Astra round 19, target 1.  Examples_slop §6.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Positivity -/

theorem nbClosed_pos {M V z : ℝ} (hz : 0 < z) (hzM : z < M) (hM2 : M ^ 2 ≤ V) :
    0 < nbClosed M V z := by
  unfold nbClosed
  have hM : 0 < M := hz.trans hzM
  have h1 : 1 < M / z := (one_lt_div hz).2 hzM
  have h2 : 1 < V / (M * z) := by
    rw [one_lt_div (mul_pos hM hz)]; nlinarith
  exact mul_pos two_pos (mul_pos (Real.log_pos h1) (Real.log_pos h2))

section Assemble

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- ★★ The positivity set of the fibre density is the punctured interval `(−M₋, M₊) ∖ {0}`. -/
theorem nbFibreDensity_pos_iff (z : ℝ) :
    0 < nbFibreDensity l₁ l₂ z ↔ -nbMminus l₁ l₂ < z ∧ z < nbMplus l₁ l₂ ∧ z ≠ 0 := by
  have hM := nbMplus_pos h₁ h₁' h₂ h₂'
  have hMm := nbMminus_pos h₁ h₁' h₂ h₂'
  have hM2 := nbMplus_sq_le h₁ h₁' h₂ h₂'
  have hMm2 := nbMminus_sq_le h₁ h₁' h₂ h₂'
  rw [nbFibreDensity_eq_indicator h₁ h₁' h₂ h₂']
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rw [indicator_of_notMem (fun h : z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂) =>
      absurd h.1 (not_lt.2 hz.le)), zero_add]
    constructor
    · intro hpos
      by_contra hne
      have : z ∉ Ioo (-nbMminus l₁ l₂) 0 := fun h => hne ⟨h.1, hz.trans hM, hz.ne⟩
      rw [indicator_of_notMem this] at hpos
      exact lt_irrefl _ hpos
    · rintro ⟨hlo, -, -⟩
      rw [indicator_of_mem (show z ∈ Ioo (-nbMminus l₁ l₂) 0 from ⟨hlo, hz⟩), ENNReal.ofReal_pos]
      exact nbClosed_pos (neg_pos.2 hz) (by linarith) hMm2
  · subst hz
    simp only [ne_eq, not_true_eq_false, and_false, iff_false, not_lt]
    rw [indicator_of_notMem (fun h : (0 : ℝ) ∈ Ioo 0 (nbMplus l₁ l₂) => lt_irrefl _ h.1),
      indicator_of_notMem (fun h : (0 : ℝ) ∈ Ioo (-nbMminus l₁ l₂) 0 => lt_irrefl _ h.2)]
    simp
  · rw [indicator_of_notMem (fun h : z ∈ Ioo (-nbMminus l₁ l₂) 0 =>
      absurd h.2 (not_lt.2 hz.le)), add_zero]
    constructor
    · intro hpos
      by_contra hne
      have : z ∉ Ioo (0 : ℝ) (nbMplus l₁ l₂) := fun h => hne ⟨by linarith, h.2, hz.ne'⟩
      rw [indicator_of_notMem this] at hpos
      exact lt_irrefl _ hpos
    · rintro ⟨-, hhi, -⟩
      rw [indicator_of_mem (show z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂) from ⟨hz, hhi⟩),
        ENNReal.ofReal_pos]
      exact nbClosed_pos hz hhi hM2

/-- `m(λ) ≥ 4(M₊ + M₋) > 0`. -/
theorem nbFibreMass_pos : 0 < nbFibreMass l₁ l₂ := by
  have hM := nbMplus_pos h₁ h₁' h₂ h₂'
  have hMm := nbMminus_pos h₁ h₁' h₂ h₂'
  have hA := Real.log_nonneg ((one_le_div (pow_pos hM 2)).2 (nbMplus_sq_le h₁ h₁' h₂ h₂'))
  have hB := Real.log_nonneg ((one_le_div (pow_pos hMm 2)).2 (nbMminus_sq_le h₁ h₁' h₂ h₂'))
  unfold nbFibreMass
  positivity

end Assemble

/-! ### The conditional density -/

/-- The conditional density of `μ` given `λ`: `p_λ = ρ(λ, ·)/m(λ)`. -/
noncomputable def nbConditionalDensity (l₁ l₂ z : ℝ) : ℝ≥0∞ :=
  nbFibreDensity l₁ l₂ z / ENNReal.ofReal (nbFibreMass l₁ l₂)

/-- The conditional law of `μ` given `λ`. -/
noncomputable def nbConditionalMeasure (l₁ l₂ : ℝ) : Measure ℝ :=
  volume.withDensity (nbConditionalDensity l₁ l₂)

section Conditional

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- ★★ The conditional density integrates to `1`. -/
theorem lintegral_nbConditionalDensity : ∫⁻ z, nbConditionalDensity l₁ l₂ z = 1 := by
  unfold nbConditionalDensity
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ (measurable_nbFibreDensity_right (l₁, l₂)),
    lintegral_nbFibreDensity_eq_mass h₁ h₁' h₂ h₂']
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (nbFibreMass_pos h₁ h₁' h₂ h₂')).ne'
    ENNReal.ofReal_ne_top

/-- ★★ The conditional law is a probability measure. -/
theorem isProbabilityMeasure_nbConditionalMeasure :
    IsProbabilityMeasure (nbConditionalMeasure l₁ l₂) :=
  ⟨by
    rw [nbConditionalMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_nbConditionalDensity h₁ h₁' h₂ h₂']⟩

end Conditional

/-! ### The first moment of the closed piece -/

/-- The antiderivative `z²[(c₁ − L)(c₂ − L) + (c₁ + c₂ − 2L)/2 + ½]` of `z · nbClosed`. -/
theorem hasDerivAt_mul_nbClosed_primitive {M V z : ℝ} (hM : 0 < M) (hV : 0 < V) (hz : 0 < z) :
    HasDerivAt (fun z : ℝ => z ^ 2 * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) / 2 + 1 / 2)) (z * nbClosed M V z) z := by
  have hl := Real.hasDerivAt_log hz.ne'
  have h1 : HasDerivAt (fun z : ℝ => Real.log M - Real.log z) (-z⁻¹) z := hl.const_sub _
  have h2 : HasDerivAt (fun z : ℝ => Real.log (V / M) - Real.log z) (-z⁻¹) z := hl.const_sub _
  have h3 : HasDerivAt (fun z : ℝ => (Real.log M + Real.log (V / M) - 2 * Real.log z) / 2)
      (-(2 * z⁻¹) / 2) z := ((hl.const_mul 2).const_sub _).div_const 2
  have h4 := (((h1.mul h2).add h3).add_const (1 / 2 : ℝ))
  have h5 := (hasDerivAt_pow 2 z).mul h4
  refine h5.congr_deriv ?_
  unfold nbClosed
  rw [Real.log_div hM.ne' hz.ne', show V / (M * z) = V / M / z by rw [div_div],
    Real.log_div (div_pos hV hM).ne' hz.ne']
  simp only [Pi.add_apply, Pi.mul_apply, Nat.cast_ofNat]
  set L := Real.log z with hL
  set c₁ := Real.log M with hc₁
  set c₂ := Real.log (V / M) with hc₂
  field_simp
  ring

theorem tendsto_mul_nbClosed_primitive_zero (M V : ℝ) :
    Tendsto (fun z : ℝ => z ^ 2 * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) / 2 + 1 / 2)) (𝓝[>] 0) (𝓝 0) := by
  have t1 := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  simp only [Real.rpow_one] at t1
  have t0 : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  set c₁ := Real.log M with hc₁
  set c₂ := Real.log (V / M) with hc₂
  -- `z²(K₀ − K₁ L + L²) = K₀ z·z − K₁ z (L z) + (L z)²`
  have := (((t0.mul t0).const_mul (c₁ * c₂ + (c₁ + c₂) / 2 + 1 / 2)).sub
    ((t0.mul t1).const_mul (c₁ + c₂ + 1))).add (t1.mul t1)
  simp only [mul_zero, sub_zero, add_zero] at this
  refine this.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
  simp only
  ring

theorem integrableOn_mul_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntegrableOn (fun z => z * nbClosed M V z) (Ioo 0 M) := by
  refine ((integrableOn_nbClosed hM hM1 hV).norm.const_mul M).mono'
    (measurable_id.mul (measurable_nbClosed M V)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun z hz => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hz.1, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hz.2.le (abs_nonneg _)

/-- ★★ `∫₀^M z · nbClosed M V z dz = M²(log(V/M²) + 1)/2`. -/
theorem integral_mul_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (0 : ℝ) M, z * nbClosed M V z = M ^ 2 * (Real.log (V / M ^ 2) + 1) / 2 := by
  have hint : IntervalIntegrable (fun z => z * nbClosed M V z) volume 0 M := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hM.le]
    exact integrableOn_mul_nbClosed hM hM1 hV
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hM.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hM
      (fun z hz => hasDerivAt_mul_nbClosed_primitive hM hV hz.1) hint
      (tendsto_mul_nbClosed_primitive_zero M V)
      ((hasDerivAt_mul_nbClosed_primitive hM hV hM).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds),
    sub_zero, Real.log_div hV.ne' (pow_pos hM 2).ne', Real.log_pow, Real.log_div hV.ne' hM.ne']
  push_cast
  ring

/-- The reflected first moment: `∫_{−M}^0 z · nbClosed M V (−z) dz = −M²(log(V/M²) + 1)/2`. -/
theorem integral_mul_nbClosed_neg {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (-M) (0 : ℝ), z * nbClosed M V (-z) = -(M ^ 2 * (Real.log (V / M ^ 2) + 1) / 2) := by
  have e : ∀ z : ℝ, z * nbClosed M V (-z) = -((fun x => x * nbClosed M V x) (-z)) := by
    intro z; simp only; ring
  simp_rw [e]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -M ≤ 0),
    intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg
      (f := fun x => x * nbClosed M V x), neg_zero, neg_neg,
    intervalIntegral.integral_of_le hM.le, integral_Ioc_eq_integral_Ioo,
    integral_mul_nbClosed hM hM1 hV]

/-! ### The conditional mean -/

/-- `A± = log(V/M±²)`; the conditional mean `E[μ | λ] = [M₊²(A₊ + 1) − M₋²(A₋ + 1)]/(2m(λ))`. -/
noncomputable def nbConditionalMean (l₁ l₂ : ℝ) : ℝ :=
  (nbMplus l₁ l₂ ^ 2 * (Real.log (nbV l₁ l₂ / nbMplus l₁ l₂ ^ 2) + 1) -
    nbMminus l₁ l₂ ^ 2 * (Real.log (nbV l₁ l₂ / nbMminus l₁ l₂ ^ 2) + 1)) /
    (2 * nbFibreMass l₁ l₂)

section Mean

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- The real fixed-domain density as the sum of the two real closed-form pieces. -/
theorem nbFixedDensity_eq_indicator (z : ℝ) :
    nbFixedDensity ((l₁, l₂), z) =
      (Ioo (0 : ℝ) (nbMplus l₁ l₂)).indicator (nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂)) z +
      (Ioo (-nbMminus l₁ l₂) 0).indicator
        (fun z => nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z)) z := by
  have hM2 := nbMplus_sq_le h₁ h₁' h₂ h₂'
  have hMm2 := nbMminus_sq_le h₁ h₁' h₂ h₂'
  rw [nbFixedDensity_eq_toReal, nbFibreDensity_eq_indicator h₁ h₁' h₂ h₂']
  by_cases hp : z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂)
  · have hn : z ∉ Ioo (-nbMminus l₁ l₂) 0 := fun h => absurd h.2 (not_lt.2 hp.1.le)
    rw [indicator_of_mem hp, indicator_of_mem hp, indicator_of_notMem hn, indicator_of_notMem hn,
      add_zero, add_zero, ENNReal.toReal_ofReal (nbClosed_nonneg hp.1 hp.2.le hM2)]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp, zero_add, zero_add]
    by_cases hn : z ∈ Ioo (-nbMminus l₁ l₂) 0
    · rw [indicator_of_mem hn, indicator_of_mem hn,
        ENNReal.toReal_ofReal (nbClosed_nonneg (neg_pos.2 hn.2) (by linarith [hn.1]) hMm2)]
    · rw [indicator_of_notMem hn, indicator_of_notMem hn, ENNReal.toReal_zero]

/-- ★★★ The first moment of the fibre density:
`∫ z ρ(λ, z) dz = [M₊²(A₊ + 1) − M₋²(A₋ + 1)]/2`. -/
theorem integral_mul_nbFixedDensity :
    ∫ z : ℝ, z * nbFixedDensity ((l₁, l₂), z) =
      (nbMplus l₁ l₂ ^ 2 * (Real.log (nbV l₁ l₂ / nbMplus l₁ l₂ ^ 2) + 1) -
        nbMminus l₁ l₂ ^ 2 * (Real.log (nbV l₁ l₂ / nbMminus l₁ l₂ ^ 2) + 1)) / 2 := by
  have hM := nbMplus_pos h₁ h₁' h₂ h₂'
  have hMm := nbMminus_pos h₁ h₁' h₂ h₂'
  have hV := nbV_pos h₁ h₁' h₂ h₂'
  have hM1 := nbMplus_le_one h₁' h₂ h₂'
  have hMm1 := nbMminus_le_one h₁' h₂ h₂'
  have hiP : Integrable fun z : ℝ =>
      (Ioo (0 : ℝ) (nbMplus l₁ l₂)).indicator
        (fun z => z * nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂) z) z :=
    (integrableOn_mul_nbClosed hM hM1 hV).integrable_indicator measurableSet_Ioo
  have hiM : Integrable fun z : ℝ =>
      (Ioo (-nbMminus l₁ l₂) 0).indicator
        (fun z => z * nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z)) z := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    refine ((integrableOn_nbClosed_neg hMm hMm1 hV).norm.const_mul (nbMminus l₁ l₂)).mono'
      (measurable_id.mul ((measurable_nbClosed _ _).comp measurable_neg)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_neg hz.2, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (by linarith [hz.1]) (abs_nonneg _)
  have e : ∀ z : ℝ, z * nbFixedDensity ((l₁, l₂), z) =
      (Ioo (0 : ℝ) (nbMplus l₁ l₂)).indicator
        (fun z => z * nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂) z) z +
      (Ioo (-nbMminus l₁ l₂) 0).indicator
        (fun z => z * nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z)) z := by
    intro z
    rw [nbFixedDensity_eq_indicator h₁ h₁' h₂ h₂']
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  simp_rw [e]
  rw [integral_add hiP hiM, integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ioo, integral_mul_nbClosed hM hM1 hV,
    integral_mul_nbClosed_neg hMm hMm1 hV]
  ring

/-- ★★ The conditional mean of the covariance given the means, as a real integral. -/
theorem integral_nbConditionalMean :
    (∫ z : ℝ, z * nbFixedDensity ((l₁, l₂), z)) / nbFibreMass l₁ l₂ = nbConditionalMean l₁ l₂ := by
  rw [integral_mul_nbFixedDensity h₁ h₁' h₂ h₂']
  unfold nbConditionalMean
  have := nbFibreMass_pos h₁ h₁' h₂ h₂'
  field_simp

end Mean

end Grammar
