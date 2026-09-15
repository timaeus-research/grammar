/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialStratumMeasure
import Grammar.HeadlineSymmetricPhase
import Grammar.PhasePosterior
import Grammar.HeadlinePhase

/-!
# Regression: the explicit constant of `x²y²`

The abstract theory gives, for `K = x²y²` and a compactly supported smooth prior `φ` supported in
the symmetric box `(-1, 1]²`, the leading stratum measure `ν^{1/2}_2 = c · δ₀` with `c` the RLCT
constant. The symmetric-box headline (Headline XIX at zero phase) evaluates the same limit
explicitly: each of the four orthant sectors contributes `φ(0) · Γ(1/2)/2`, so after the
square-parameter transport `N ↦ √N` the constant is `c = √π · φ(0)`
(`x2y2_coeff_one_eq`). Hence `ν^{1/2}_2 = √π φ(0) δ₀` (`x2y2_measure_eq`) and every insertion
has leading coefficient `√π φ(0) f(0)` (`x2y2_tendsto_normalised`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

section X2Y2

variable (W : TopologicalSpace.Opens (Fin 2 → ℝ)) {prior : (Fin 2 → ℝ) → ℝ}
  (hps : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
  (hpW : tsupport prior ⊆ (W : Set (Fin 2 → ℝ))) (hbox : tsupport prior ⊆ symBox 2)

theorem lamStar_x2y2 : lamStar (equalExp 2 1) = 1 / 2 := by
  unfold lamStar
  rw [kmax_equal]
  norm_num

theorem mstar_x2y2 : mstar (equalExp 2 1) = 2 := mstar_equal 1

theorem ratioExp_x2y2 (i : Fin 2) : ratioExp (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) i = 1 / 2 := by
  simp [ratioExp]

theorem multCount_x2y2 :
    multCount (ratioExp (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)) (1 / 2) = 2 := by
  unfold multCount
  simp [ratioExp_x2y2]

/-- The zero-phase symmetric-box coefficient: each orthant sector contributes `φ(0) √π / 2`. -/
theorem phaseCoeff_x2y2 (σ : Fin 2 → Bool) :
    phaseCoeff (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) 1
      (fun u => phaseSign (fun _ : Fin 2 => 1) σ * (fun _ : Fin 2 → ℝ => (0 : ℝ)) u)
      (fun u => prior (reflect σ u)) = prior 0 * (Real.sqrt Real.pi / 2) := by
  rw [phaseCoeff_equal 1 (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) 1 ratioExp_x2y2]
  have hr : reflect σ (0 : Fin 2 → ℝ) = 0 := by
    funext i
    simp [reflect]
  simp only [mul_zero, hr, Nat.factorial_one, Nat.cast_one, Finset.prod_const_one,
    mul_one, div_one]
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, phaseMoment_zero 1 1 one_pos one_pos]
  rw [show (1 : ℝ) / 2 = 1 / 2 by rfl, Real.Gamma_one_half_eq, Real.one_rpow, mul_one]

include hps hbox in
/-- ★★★ **The symmetric-box headline in the parameter `N`**: with `N ↦ √N` the normalised
partition function of `x²y²` converges to `√π φ(0)`. -/
theorem x2y2_tendsto_headline :
    Tendsto (normalised (1 / 2) 1 (partitionObs (monoPhase (equalExp 2 1)) prior (fun _ => 1)))
      atTop (𝓝 (Real.sqrt Real.pi * prior 0)) := by
  have hT := headline_symmetric_abs_phase_leading 1 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (1 / 2) 1 (by norm_num) one_pos (fun i => (ratioExp_x2y2 i).symm.le)
    ⟨0, ratioExp_x2y2 0⟩ (fun _ => 0) prior continuous_const hps.continuous
  rw [multCount_x2y2] at hT
  simp only [phaseCoeff_x2y2, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul] at hT
  have hsqrt : Tendsto (fun M : ℝ => Real.sqrt M) atTop atTop := by
    have := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    refine this.congr' (Eventually.of_forall fun M => ?_)
    exact (Real.sqrt_eq_rpow M).symm
  have hcomp := (hT.comp hsqrt).div_const (2 : ℝ)
  have hlim : ((2 ^ (1 + 1) : ℕ) : ℝ) * (prior 0 * (Real.sqrt Real.pi / 2)) / 2 =
      Real.sqrt Real.pi * prior 0 := by push_cast; ring
  rw [hlim] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with M hM
  have hM0 : 0 < M := by linarith
  have hlog : 0 < Real.log M := Real.log_pos hM
  have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0.le
  have hsqpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  simp only [Function.comp_apply]
  unfold normalised partitionObs
  have hint : ∫ x in symBox 2, prior x * ((∏ i, |x i| ^ (0 : ℕ)) *
      Real.exp (-(1 * Real.sqrt M ^ 2 * ∏ i, x i ^ (2 * 1)) +
        1 * (Real.sqrt M * ∏ i, x i ^ 1) * 0)) =
      ∫ y, prior y * 1 * Real.exp (-M * monoPhase (equalExp 2 1) y) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)]
    · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [pow_zero, Finset.prod_const_one, one_mul, mul_zero, add_zero, mul_one, hsq,
        monoPhase]
      ring_nf
    · rw [image_eq_zero_of_notMem_tsupport fun h => hy (hbox h), zero_mul]
  rw [hint, Real.log_sqrt hM0.le, show (-(2 * (1 / 2 : ℝ))) = -1 by norm_num,
    Real.rpow_neg hsqpos.le, Real.rpow_one, pow_one]
  have hsqM : Real.sqrt M = M ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow M
  rw [hsqM]
  field_simp

include hps hp0 hpc hpW hbox in
/-- ★★★ **The RLCT constant of `x²y²` is `√π φ(0)`**: `𝒯^U_{1/2,1}[1] = √π φ(0)`. -/
theorem x2y2_coeff_one_eq
    (Y : ResolvedCoreTransport (monomialData (equalExp 2 1) W hps hp0 hpc hpW).R
      (monomialData (equalExp 2 1) W hps hp0 hpc hpW).hKc prior) :
    ((monomialData (equalExp 2 1) W hps hp0 hpc hpW).withF (fun _ => (1 : ℝ))
      contMDiff_const).coeff Y (lamStar (equalExp 2 1)) (2 - 1) = Real.sqrt Real.pi * prior 0 := by
  have hext := isExtremalData_equal 1 W hps hp0 hpc hpW one_pos
  have h1 := (monomialData (equalExp 2 1) W hps hp0 hpc hpW).tendsto_normalised_Z_of_extremalData Y
    hext (G := fun _ => (1 : ℝ)) contMDiff_const
  have h1' : Tendsto (normalised (lamStar (equalExp 2 1)) (2 - 1)
      (partitionObs (monoPhase (equalExp 2 1)) prior (fun _ => (1 : ℝ)))) atTop
      (𝓝 (((monomialData (equalExp 2 1) W hps hp0 hpc hpW).withF (fun _ => (1 : ℝ))
        contMDiff_const).coeff Y (lamStar (equalExp 2 1)) (2 - 1))) := by
    refine h1.congr fun N => ?_
    unfold normalised
    rw [(monomialData (equalExp 2 1) W hps hp0 hpc hpW).Z_one N]
    rfl
  have h2 := x2y2_tendsto_headline hps hbox
  rw [lamStar_x2y2] at h1' ⊢
  exact tendsto_nhds_unique h1' h2

include hbox in
/-- ★★★ **The leading stratum measure of `x²y²` is `√π φ(0) δ₀`.** -/
theorem x2y2_measure_eq (h0W : (0 : Fin 2 → ℝ) ∈ W)
    (Y : ResolvedCoreTransport (monomialData (equalExp 2 1) W hps hp0 hpc hpW).R
      (monomialData (equalExp 2 1) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure 1 W hps hp0 hpc hpW one_pos Y =
      ENNReal.ofReal (Real.sqrt Real.pi * prior 0) •
        Measure.dirac (originX 1 W hps hp0 hpc hpW h0W) := by
  rw [equalMeasure_eq_smul_dirac 1 W hps hp0 hpc hpW one_pos h0W Y,
    x2y2_coeff_one_eq W hps hp0 hpc hpW hbox Y]

include hps hp0 hpc hpW hbox in
/-- ★★★ **Every insertion for `x²y²`**: `N^{1/2}(log N)^{-1} ∫ φ f e^{−N x²y²} → √π φ(0) f(0)`. -/
theorem x2y2_tendsto_normalised (h0W : (0 : Fin 2 → ℝ) ∈ W) {f : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    Tendsto (normalised (1 / 2) 1 (partitionObs (monoPhase (equalExp 2 1)) prior f)) atTop
      (𝓝 (Real.sqrt Real.pi * prior 0 * f 0)) := by
  set Ξ := monomialData (equalExp 2 1) W hps hp0 hpc hpW with hΞ
  obtain ⟨Y⟩ := WatanabeModificationOn.exists_resolvedCoreTransport_of_modification Ξ.R Ξ.hK0
    Ξ.hKc Ξ.prior_smooth.continuous.measurable Ξ.prior_nonneg Ξ.prior_compact Ξ.prior_W
  have hext := isExtremalData_equal 1 W hps hp0 hpc hpW one_pos
  have h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre 2), f (Ξ.R.gv P) = 0 := by
    rw [deepZeroFibre_equal_eq_empty, nhdsSet_empty]
    exact Filter.eventually_bot
  have hlim := Ξ.tendsto_normalised_partitionObs_extremal Y hf hext one_le_dim h0
  have hint : ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y hext one_le_dim) =
      Real.sqrt Real.pi * prior 0 * f 0 := by
    change ∫ x, f (Ξ.R.gv x.1) ∂(equalMeasure 1 W hps hp0 hpc hpW one_pos Y) = _
    rw [x2y2_measure_eq W hps hp0 hpc hpW hbox h0W Y, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (hp0 0)), smul_eq_mul]
    rfl
  rw [hint, lamStar_x2y2] at hlim
  exact hlim

end X2Y2

end SmoothEngine

end Grammar
