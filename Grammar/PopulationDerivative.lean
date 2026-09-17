/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalGeneral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The population partition function: derivative in `N` and decay

`Z(N) = ∫_{(0,1]^d} η v^h e^{−N v^{2k}} dv` is differentiable in `N` with
`Z'(N) = −∫ v^{2k} η v^h e^{−N v^{2k}} dv` (differentiation under the integral over the compact
cube, `hasDerivAt_empIntegral_zero`), and `Z(N) → 0` as `N → ∞` (dominated convergence,
`tendsto_empIntegral_zero_atTop`).  These are the two inputs that let the coefficients of the
amplitude `v^{2k} η` at exponent `μ + 1` be read off those of `η` at `μ` by integrating the cutoff
expansion.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The population integral in explicit form. -/
theorem empIntegral_zero_eq (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral η (fun _ => 0) h k N =
      ∫ v in SmoothEngine.box (Fin d) 1,
        η v * mono h v * Real.exp (-N * mono (fun i => 2 * k i) v) := by
  rw [empIntegral_eq]
  refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
  simp

theorem mono_le_one_of_mem_box {b : ℝ} (hb : b ≤ 1) {v : Fin d → ℝ}
    (hv : v ∈ SmoothEngine.box (Fin d) b) (a : Fin d → ℕ) : mono a v ≤ 1 := by
  unfold mono
  refine Finset.prod_le_one (fun i _ => pow_nonneg (hv i (Set.mem_univ i)).1.le _) fun i _ => ?_
  exact pow_le_one₀ (hv i (Set.mem_univ i)).1.le ((hv i (Set.mem_univ i)).2.trans hb)

theorem mono_pos_of_mem_box {b : ℝ} {v : Fin d → ℝ} (hv : v ∈ SmoothEngine.box (Fin d) b)
    (a : Fin d → ℕ) : 0 < mono a v :=
  mono_pos a fun i => (hv i (Set.mem_univ i)).1

/-- A continuous function is integrable on the cube. -/
theorem integrableOn_box_one_of_continuous {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f (SmoothEngine.box (Fin d) 1) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBox 1)).mono_set
    (box_subset_closedBox 1)

/-- ★ **Differentiation under the integral**: `Z'(N) = −∫ v^{2k} η v^h e^{−N v^{2k}} dv`. -/
theorem hasDerivAt_empIntegral_zero (hη : ContDiff ℝ ∞ η) (h k : Fin d → ℕ) (N₀ : ℝ) :
    HasDerivAt (empIntegral η (fun _ => 0) h k)
      (-(empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k N₀)) N₀ := by
  have hηc : Continuous η := hη.continuous
  have hmc : ∀ a : Fin d → ℕ, Continuous (mono a) := fun a => continuous_mono a
  set m : (Fin d → ℝ) → ℝ := (mono fun i => 2 * k i) with hm
  -- the integrand and its `N`-derivative
  set F : ℝ → (Fin d → ℝ) → ℝ := (fun N v => η v * mono h v * Real.exp (-N * m v)) with hF
  set F' : ℝ → (Fin d → ℝ) → ℝ :=
    (fun N v => η v * mono h v * (Real.exp (-N * m v) * (-1 * m v))) with hF'
  have hFc : ∀ N, Continuous (F N) := fun N => by
    simp only [hF]
    fun_prop
  have hF'c : ∀ N, Continuous (F' N) := fun N => by
    simp only [hF']
    fun_prop
  have hZ : empIntegral η (fun _ => 0) h k = fun N => ∫ v in SmoothEngine.box (Fin d) 1, F N v :=
    funext fun N => empIntegral_zero_eq η h k N
  set bound : (Fin d → ℝ) → ℝ := (fun v => |η v| * Real.exp (|N₀| + 1)) with hbound
  have hbc : Continuous bound := by
    simp only [hbound]
    fun_prop
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (SmoothEngine.box (Fin d) 1)) (F := F) (F' := F') (x₀ := N₀)
    (bound := bound) (Metric.ball_mem_nhds N₀ one_pos)
    (Eventually.of_forall fun N => (hFc N).aestronglyMeasurable)
    (integrableOn_box_one_of_continuous (hFc N₀)) (hF'c N₀).aestronglyMeasurable ?_
    (integrableOn_box_one_of_continuous hbc) ?_
  · rw [hZ]
    refine hder.2.congr_deriv ?_
    rw [empIntegral_zero_eq, ← integral_neg]
    refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
    simp only [hF', hm]
    ring
  · refine (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun v hv N hN => ?_)
    have hm1 : m v ≤ 1 := mono_le_one_of_mem_box le_rfl hv _
    have hm0 : 0 < m v := mono_pos_of_mem_box hv _
    have hh1 : mono h v ≤ 1 := mono_le_one_of_mem_box le_rfl hv h
    have hh0 : 0 ≤ mono h v := (mono_pos_of_mem_box hv h).le
    have hN : |N| ≤ |N₀| + 1 := by
      have := mem_ball_iff_norm.1 hN
      rw [Real.norm_eq_abs] at this
      have := abs_sub_abs_le_abs_sub N N₀
      linarith
    have hexp : Real.exp (-N * m v) ≤ Real.exp (|N₀| + 1) := by
      rw [Real.exp_le_exp]
      have h1 : -N * m v ≤ |N| * m v := by
        have := neg_abs_le N
        nlinarith
      have h2 : |N| * m v ≤ (|N₀| + 1) * 1 := mul_le_mul hN hm1 hm0.le (by positivity)
      linarith
    simp only [hF', hbound, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hh0, abs_of_pos (Real.exp_pos _),
      abs_mul, abs_neg, abs_one, one_mul, abs_of_pos hm0]
    calc |η v| * mono h v * (Real.exp (-N * m v) * m v)
        ≤ |η v| * 1 * (Real.exp (|N₀| + 1) * 1) := by gcongr
      _ = |η v| * Real.exp (|N₀| + 1) := by ring
  · refine Eventually.of_forall fun v N _ => ?_
    simp only [hF, hF']
    exact (((hasDerivAt_id N).neg.mul_const (m v)).exp).const_mul (η v * mono h v)

/-- The population integral is continuous in `N`. -/
theorem continuous_empIntegral_zero (hη : ContDiff ℝ ∞ η) (h k : Fin d → ℕ) :
    Continuous (empIntegral η (fun _ => 0) h k) :=
  continuous_iff_continuousAt.2 fun N => (hasDerivAt_empIntegral_zero hη h k N).continuousAt

/-- ★ **Decay**: `Z(N) → 0` as `N → ∞` (dominated convergence; `v^{2k} > 0` on the open cube). -/
theorem tendsto_empIntegral_zero_atTop (hη : ContDiff ℝ ∞ η) (h k : Fin d → ℕ) :
    Tendsto (empIntegral η (fun _ => 0) h k) atTop (𝓝 0) := by
  have hηc : Continuous η := hη.continuous
  have hmc : ∀ a : Fin d → ℕ, Continuous (mono a) := fun a => continuous_mono a
  set m : (Fin d → ℝ) → ℝ := (mono fun i => 2 * k i) with hm
  set F : ℝ → (Fin d → ℝ) → ℝ := (fun N v => η v * mono h v * Real.exp (-N * m v)) with hF
  have hFc : ∀ N, Continuous (F N) := fun N => by
    simp only [hF]
    fun_prop
  have hZ : empIntegral η (fun _ => 0) h k = fun N => ∫ v in SmoothEngine.box (Fin d) 1, F N v :=
    funext fun N => empIntegral_zero_eq η h k N
  set bound : (Fin d → ℝ) → ℝ := (fun v => |η v| * |mono h v|) with hbound
  have hbc : Continuous bound := by
    simp only [hbound]
    fun_prop
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (SmoothEngine.box (Fin d) 1)) (F := F) (f := fun _ => (0 : ℝ)) bound
    (Eventually.of_forall fun N => (hFc N).aestronglyMeasurable) ?_
    (integrableOn_box_one_of_continuous hbc) ?_
  · rw [hZ]
    simpa using hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    refine (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun v hv => ?_)
    have hm0 : 0 < m v := mono_pos_of_mem_box hv _
    have hexp : Real.exp (-N * m v) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    simp only [hF, hbound, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |η v| * |mono h v| * Real.exp (-N * m v) ≤ |η v| * |mono h v| * 1 := by gcongr
      _ = |η v| * |mono h v| := mul_one _
  · refine (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun v hv => ?_)
    have hm0 : 0 < m v := mono_pos_of_mem_box hv _
    have h1 : Tendsto (fun N : ℝ => -N * m v) atTop atBot := by
      have := (tendsto_id (α := ℝ)).atTop_mul_const' hm0
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr fun N => ?_
      simp [neg_mul]
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (η v * mono h v)
    simp only [mul_zero] at h2
    exact h2

end Grammar
