/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumMeasureExtremal
import Grammar.SmoothResolvedRLCTPositive

/-!
# Positivity of the leading coefficient with insertion

The orthant lower bound of `SmoothResolvedRLCTPositive` (there for the unit observable) is
generalised to a nonnegative base observable `f`: if `f ∘ π` is positive at a point `P₀` of the
zero fibre where exactly `m*` walls resonate with `λ*` and the prior is positive, then the
`(λ*, m*−1)` coefficient of `f` is strictly positive (`observableCoeff_pos_of_realised`). When
moreover `f ∘ π` vanishes near `D_{m*+1}`, the integral of `f ∘ π` against the extremal stratum
measure is strictly positive (`integral_extremalStratumMeasure_pos`) and the partition function
with insertion has the genuine asymptotic equivalence
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν) N^{−λ*} (log N)^{m*−1}` with a positive constant
(`partitionObs_isEquivalent_of_pos`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

section Chart

variable (E : EvenChartBox Ξ.R)

/-- The Boltzmann integrand with a bounded continuous insertion is integrable. -/
theorem integrable_prior_mul_exp {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun y => Ξ.prior y * f y * Real.exp (-N * Ξ.K y) := by
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn Ξ.prior_compact hf.continuousOn
  refine (Ξ.integrable_prior.const_mul M).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((Ξ.prior_smooth.continuous.mul hf).aestronglyMeasurable).mul
      (Real.measurable_exp.comp (measurable_const.mul Ξ.K_m)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Ξ.prior_nonneg y),
      abs_of_pos (Real.exp_pos _)]
    by_cases hy : y ∈ tsupport Ξ.prior
    · have hK := Ξ.hK0 y (Ξ.prior_W hy)
      have hfy : |f y| ≤ M := by rw [← Real.norm_eq_abs]; exact hM y hy
      have hexp : Real.exp (-N * Ξ.K y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h1 : Ξ.prior y * |f y| ≤ Ξ.prior y * M :=
        mul_le_mul_of_nonneg_left hfy (Ξ.prior_nonneg y)
      calc Ξ.prior y * |f y| * Real.exp (-N * Ξ.K y) ≤ Ξ.prior y * M * 1 :=
            mul_le_mul h1 hexp (Real.exp_pos _).le
              ((mul_nonneg (Ξ.prior_nonneg y) (abs_nonneg _)).trans h1)
        _ = M * Ξ.prior y := by ring
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul, mul_zero]

/-- **The lower bound on the partition function with insertion** by the monomial integral of the
chart. -/
theorem Z_ge_mul_monoBoxIntegral {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y)
    {ε : ℝ} (hε : ε ≤ E.r) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u ∈ orthant d ε,
      c ≤ |E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u)))
    {N : ℝ} (hN : 0 ≤ N) :
    c * monoBoxIntegral E.k E.h ε N ≤
      (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).Z N := by
  rw [Ξ.Z_withF_comp_gv hf N]
  unfold partitionObs
  have hsub := Ξ.orthant_subset_target E hε
  have hcb := Ξ.centeredBox_subset_target E hε
  have hint := Ξ.integrable_prior_mul_exp hf.continuous hN
  have hnn : 0 ≤ᵐ[volume] fun y => Ξ.prior y * f y * Real.exp (-N * Ξ.K y) :=
    Eventually.of_forall fun y =>
      mul_nonneg (mul_nonneg (Ξ.prior_nonneg y) (hf0 y)) (Real.exp_pos _).le
  have hcont : ContinuousOn (fun u => |E.b u| * (∏ j, u j ^ E.h j) *
      (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u) *
        Real.exp (-N * ∏ j, u j ^ (2 * E.k j)))) (centeredBox d ε) := by
    have hb : ContinuousOn E.b (centeredBox d ε) := E.b_analytic.continuousOn.mono hcb
    have hrep : ContinuousOn (watanabeRep Ξ.R.g E.φ) (centeredBox d ε) :=
      E.analyticOnNhd_rep.continuousOn.mono hcb
    have h1 : Continuous fun u : Fin d → ℝ => ∏ j, u j ^ E.h j := by fun_prop
    have h2 : Continuous fun u : Fin d → ℝ => Real.exp (-N * ∏ j, u j ^ (2 * E.k j)) := by
      fun_prop
    exact (hb.abs.mul h1.continuousOn).mul
      (((Ξ.prior_smooth.continuous.comp_continuousOn hrep).mul
        (hf.continuous.comp_continuousOn hrep)).mul h2.continuousOn)
  calc c * monoBoxIntegral E.k E.h ε N
      = ∫ u in orthant d ε, c * ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j))) := by
        rw [monoBoxIntegral_eq_setIntegral, integral_const_mul]
    _ ≤ ∫ u in orthant d ε, |E.b u| * (∏ j, u j ^ E.h j) *
          (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u) *
            Real.exp (-N * Ξ.K (watanabeRep Ξ.R.g E.φ u))) := by
        refine integral_mono_of_nonneg
          (ae_restrict_of_forall_mem (measurableSet_orthant d ε) fun u hu => ?_) ?_
          (ae_restrict_of_forall_mem (measurableSet_orthant d ε) fun u hu => ?_)
        · exact mul_nonneg hc0
            (mul_nonneg (prod_pow_pos_of_mem_orthant hu _).le (Real.exp_pos _).le)
        · refine ((hcont.integrableOn_compact (isCompact_centeredBox d ε)).mono_set
            (orthant_subset_centeredBox le_rfl)).congr_fun ?_ (measurableSet_orthant d ε)
          intro u hu
          simp only
          rw [E.phase_eq u (hsub hu)]
        · beta_reduce
          have hP := prod_pow_pos_of_mem_orthant hu E.h
          have hE := Real.exp_pos (-N * Ξ.K (watanabeRep Ξ.R.g E.φ u))
          rw [E.phase_eq u (hsub hu)] at hE ⊢
          calc c * ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j)))
              ≤ (|E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u))) *
                  ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j))) :=
                mul_le_mul_of_nonneg_right (hc u hu) (mul_pos hP hE).le
            _ = _ := by ring
    _ = ∫ y in watanabeRep Ξ.R.g E.φ '' orthant d ε,
          Ξ.prior y * f y * Real.exp (-N * Ξ.K y) :=
        (Ξ.integral_image_orthant E hε fun y => Ξ.prior y * f y * Real.exp (-N * Ξ.K y)).symm
    _ ≤ ∫ y, Ξ.prior y * f y * Real.exp (-N * Ξ.K y) := setIntegral_le_integral hint hnn

/-- **The positive lower bound of the chart density with insertion** on a small orthant box. -/
theorem exists_orthant_bound_obs {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {P₀ : Ξ.R.U}
    (hP : P₀ ∈ E.φ.source) (hP0 : E.φ P₀ = 0)
    (hpos : 0 < Ξ.prior (Ξ.R.gv P₀) * f (Ξ.R.gv P₀)) :
    ∃ ε c : ℝ, 0 < ε ∧ ε ≤ E.r ∧ 0 < c ∧ ∀ u ∈ orthant d ε,
      c ≤ |E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u)) := by
  set G : (Fin d → ℝ) → ℝ := fun u =>
    |E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u)) with hG
  have h0 : watanabeRep Ξ.R.g E.φ 0 = Ξ.R.gv P₀ := by
    change Ξ.R.gv (E.φ.symm 0) = _
    rw [← hP0, E.φ.left_inv hP]
  have hG0 : 0 < G 0 := by
    simp only [hG]
    rw [h0]
    exact mul_pos (abs_pos.2 (E.b_ne_zero 0 E.zero_mem.1)) hpos
  have hGc : ContinuousAt G 0 := by
    refine ((E.b_analytic 0 E.zero_mem.1).continuousAt.abs).mul ?_
    exact (Ξ.prior_smooth.continuous.continuousAt.comp
      (E.analyticOnNhd_rep 0 E.zero_mem.1).continuousAt).mul
      (hf.continuousAt.comp (E.analyticOnNhd_rep 0 E.zero_mem.1).continuousAt)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hGc.eventually (lt_mem_nhds (half_lt_self hG0)))
  refine ⟨min (δ / 2) E.r, G 0 / 2, lt_min (half_pos hδ) E.r_pos, min_le_right _ _,
    half_pos hG0, fun u hu => ?_⟩
  have hu' : u ∈ Metric.closedBall (0 : Fin d → ℝ) (δ / 2) := by
    rw [closedBall_eq_centeredBox (half_pos hδ).le]
    exact orthant_subset_centeredBox (min_le_left _ _) hu
  exact (hball (Metric.closedBall_subset_ball (half_lt_self hδ) hu')).le

end Chart

/-- ★★★ **Positivity of the leading coefficient with insertion**: if exactly `m* ≥ 1` walls
through a point `P₀` of the zero fibre resonate with `λ*`, the prior is positive at `π(P₀)` and
the nonnegative observable `f` is positive at `π(P₀)`, then `0 < 𝒯^U_{λ*,m*−1}[f ∘ π]`. -/
theorem coeff_comp_gv_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y lam (m - 1) := by
  obtain ⟨E, hEs, hE0⟩ := exists_centeredEvenChartBox Ξ.R Ξ.hK0 (show P₀ ∈ divisor Ξ.R from hP₀.2)
  have hpairs := pairs_eq_pairData Ξ.R Ξ.hK0 E hEs hE0
  have hmem : ∀ j, 0 < E.k j → (E.k j, E.h j) ∈ pairs Ξ.R Ξ.hK0 P₀ := fun j hj => by
    rw [hpairs]
    exact Multiset.mem_map.2 ⟨j, by rw [Finset.mem_val]; exact (mem_active E).2 hj, rfl⟩
  have hlam : ∀ j, 0 < E.k j → 2 * (E.k j : ℝ) * lam ≤ E.h j + 1 := fun j hj =>
    h.1 P₀ hP₀ _ (hmem j hj)
  have hm : (Finset.univ.filter fun j => 0 < E.k j ∧ 2 * (E.k j : ℝ) * lam = E.h j + 1).card = m :=
    (Ξ.resonanceCount_eq_card_of_centered E hEs hE0 hlam).trans hres
  obtain ⟨ε, c, hε, hεr, hc0, hc⟩ :=
    Ξ.exists_orthant_bound_obs E hf.continuous hEs hE0 (mul_pos hprior hfP)
  obtain ⟨C, hC, hlimI⟩ := exists_tendsto_monoBoxIntegral E.k E.h
    (fun _ hj => E.h_eq_zero_of_k_eq_zero hj) hε hlam hm hm1
  have hlimZ := Ξ.tendsto_normalised_Z_of_extremalData Y h (Ξ.contMDiff_comp_gv hf)
  refine lt_of_lt_of_le (mul_pos hc0 hC) (le_of_tendsto_of_tendsto (hlimI.const_mul c) hlimZ ?_)
  filter_upwards [eventually_gt_atTop 1] with N hN
  unfold normalised
  have hpos : 0 ≤ N ^ lam / Real.log N ^ (m - 1) :=
    div_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN.le) _)
  calc c * (N ^ lam / Real.log N ^ (m - 1) * monoBoxIntegral E.k E.h ε N)
      = N ^ lam / Real.log N ^ (m - 1) * (c * monoBoxIntegral E.k E.h ε N) := by ring
    _ ≤ N ^ lam / Real.log N ^ (m - 1) *
          (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).Z N :=
        mul_le_mul_of_nonneg_left
          (Ξ.Z_ge_mul_monoBoxIntegral E hf hf0 hεr hc0.le hc (by linarith)) hpos

/-- ★★★ **Euclidean form**: `0 < C_{λ*,m*−1}(f)`. -/
theorem observableCoeff_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.X Y).observableCoeff lam (m - 1) f hf := by
  rw [← Ξ.coeff_comp_gv Y hf lam (m - 1)]
  exact Ξ.coeff_comp_gv_pos_of_realised Y h hP₀ hprior hres hm1 hf hf0 hfP

/-- ★★★ **The extremal stratum measure has positive integrals**: for a nonnegative base
observable positive at a realiser of the extremal pair with positive prior, and whose pull-back
vanishes near `D_{m*+1}`, `0 < ∫ f ∘ π dν^{λ*}_{m*}`. -/
theorem integral_extremalStratumMeasure_pos {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀))
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    0 < ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) := by
  unfold extremalStratumMeasure
  rw [← Ξ.coeff_withF_eq_integral_stratumMeasure Y hm _ (Ξ.contMDiff_comp_gv hf) h0]
  exact Ξ.coeff_comp_gv_pos_of_realised Y h hP₀ hprior hres hm hf hf0 hfP

/-- ★★★ **The leading asymptotic with insertion, with a positive constant**:
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν^{λ*}_{m*}) N^{−λ*} (log N)^{m*−1}` and the constant is
strictly positive. -/
theorem partitionObs_isEquivalent_of_pos {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀))
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    0 < ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) ∧
      (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
        fun N => (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)) *
          (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  have hpos := Ξ.integral_extremalStratumMeasure_pos Y h hm hP₀ hprior hres hf hf0 hfP h0
  exact ⟨hpos, Ξ.partitionObs_isEquivalent_extremal Y hf h hm h0 hpos.ne'⟩

end ResolvedData

end SmoothEngine

end Grammar
