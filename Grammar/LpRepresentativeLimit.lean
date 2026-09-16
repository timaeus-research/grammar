/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Representatives of `Lᵖ` limits and of `Lᵖ`-valued derivatives

* `ae_eq_of_tendsto_Lp_of_tendsto_ae`: if `F n → Flim` in `Lᵖ(μ)` and representatives `f n` of the
  `F n` converge a.e. to `flim`, then `flim` represents `Flim` (convergence in measure and a.e.
  convergent subsequences).
* `ae_fderiv_eq_of_representative`: if `G : ℝ^d → Lᵖ(μ)` is differentiable on an open set `U`, and
  `g x` is a samplewise representative (`g · u` represents `G u` for every `u ∈ U`) that is
  differentiable in `u` with derivative `dg x u`, then `dg · u v` represents the `Lᵖ`-derivative
  `fderiv ℝ G u v` (difference quotients along a deterministic sequence).

These are the measure-theoretic inputs for synchronising samplewise derivative representatives of an
`Lˢ`-valued analytic kernel (grey-book bridge, Stage B, consult #150 Lemma A).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Grammar

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An `Lᵖ` limit of classes with a.e.-convergent representatives is represented by the pointwise
limit. -/
theorem ae_eq_of_tendsto_Lp_of_tendsto_ae {f : ℕ → E → ℝ} {F : ℕ → Lp ℝ p μ} {Flim : Lp ℝ p μ}
    {flim : E → ℝ} (hrep : ∀ n, f n =ᵐ[μ] F n) (hLp : Tendsto F atTop (𝓝 Flim))
    (hpt : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (flim x))) : flim =ᵐ[μ] Flim := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hnorm : Tendsto (fun n => ‖F n - Flim‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hLp
  have hsn : Tendsto (fun n => eLpNorm ((F n : E → ℝ) - (Flim : E → ℝ)) p μ) atTop (𝓝 0) := by
    have h1 : ∀ n, eLpNorm ((F n : E → ℝ) - (Flim : E → ℝ)) p μ =
        eLpNorm (F n - Flim : Lp ℝ p μ) p μ :=
      fun n => (eLpNorm_congr_ae (Lp.coeFn_sub (F n) Flim)).symm
    have h2 := (ENNReal.tendsto_toReal_iff (fun n => Lp.eLpNorm_ne_top (F n - Flim))
      ENNReal.zero_ne_top).1 (by simpa [Lp.norm_def] using hnorm)
    simpa [h1] using h2
  have hmeas : TendstoInMeasure μ (fun n => (F n : E → ℝ)) atTop Flim :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 (fun n => Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) hsn
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  filter_upwards [hae, hpt, ae_all_iff.2 hrep] with x hx1 hx2 hx3
  have h : Tendsto (fun i => f (ns i) x) atTop (𝓝 (flim x)) := hx2.comp hns.tendsto_atTop
  have heq : (fun i => f (ns i) x) = fun i => F (ns i) x := funext fun i => hx3 (ns i)
  rw [heq] at h
  exact tendsto_nhds_unique h hx1

/-- **A samplewise first derivative represents the `Lᵖ` derivative.** -/
theorem ae_fderiv_eq_of_representative {d : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {G : (Fin d → ℝ) → Lp ℝ p μ} (hG : DifferentiableOn ℝ G U) {g : E → (Fin d → ℝ) → ℝ}
    {dg : E → (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ} (hg_rep : ∀ u ∈ U, (fun x => g x u) =ᵐ[μ] G u)
    (hg_deriv : ∀ x, ∀ u ∈ U, HasFDerivAt (g x) (dg x u) u) :
    ∀ u ∈ U, ∀ v : Fin d → ℝ, (fun x => dg x u v) =ᵐ[μ] fderiv ℝ G u v := by
  intro u hu v
  have hGd : HasFDerivAt G (fderiv ℝ G u) u :=
    (hG.differentiableAt (hU.mem_nhds hu)).hasFDerivAt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, u + ((n : ℝ) + 1)⁻¹ • v ∈ U := by
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht : Tendsto (fun n : ℕ => u + ((n : ℝ) + 1)⁻¹ • v) atTop (𝓝 (u + (0 : ℝ) • v)) :=
      tendsto_const_nhds.add (Filter.Tendsto.smul_const h0 v)
    rw [zero_smul, add_zero] at ht
    exact Filter.eventually_atTop.1 (ht.eventually (hU.mem_nhds hu))
  set c : ℕ → ℝ := fun n => ((n + N : ℕ) : ℝ) + 1 with hcdef
  have hcn : ∀ n, 0 ≤ c n := fun n => by positivity
  have hc' : Tendsto c atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)).atTop_add tendsto_const_nhds
  have hc : Tendsto (fun n => ‖c n‖) atTop atTop :=
    hc'.congr fun n => (Real.norm_of_nonneg (hcn n)).symm
  have hmem : ∀ n, u + (c n)⁻¹ • v ∈ U := fun n => hN (n + N) (Nat.le_add_left N n)
  have hF := hGd.lim v hc
  refine ae_eq_of_tendsto_Lp_of_tendsto_ae
    (f := fun n x => c n * (g x (u + (c n)⁻¹ • v) - g x u))
    (F := fun n => c n • (G (u + (c n)⁻¹ • v) - G u)) ?_ hF ?_
  · intro n
    filter_upwards [hg_rep _ (hmem n), hg_rep u hu,
      Lp.coeFn_smul (c n) (G (u + (c n)⁻¹ • v) - G u),
      Lp.coeFn_sub (G (u + (c n)⁻¹ • v)) (G u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h3 h4
    rw [h3, h4, h1, h2]
  · exact Filter.Eventually.of_forall fun x => by
      simpa [smul_eq_mul] using (hg_deriv x u hu).lim v hc

end Grammar
