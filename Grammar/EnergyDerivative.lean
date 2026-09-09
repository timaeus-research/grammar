/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationBounded

/-!
# The exact energy identity `𝒵_N[K∘π] = −(1/β) d/dN 𝒵_N[1]` (Programme Q, N2, unit 313)

For an amplitude `η` continuous on `ℝ^{n+1}` (only its values on the unit box enter) the population
integral
`𝒵(N) = ∫ η u^h e^{-βN u^{2k}} du` is differentiable in `N > 0` with
```
𝒵'(N) = −β ∫ (u^{2k} η) u^h e^{-βN u^{2k}} du = −β 𝒵_K(N),
```
where `𝒵_K` inserts the energy `K∘π = u^{2k}` (`hasDerivAt_popIntegral`; differentiation under the
integral, dominated on the neighbourhood `|N − N₀| < N₀/2` by `β |η| u^h u^{2k}`, since the
exponential factor is at most one for `N > 0`). Hence `𝒵_K(N) = −(1/β) 𝒵'(N)`
(`energy_eq_neg_deriv`), the paper's `𝒵_n[K] = −𝒵_n'(n)` at `β = 1`. This is an identity of
integrals at every `N > 0`, obtained from the integrands; it is not, and must not be, used to
differentiate an asymptotic expansion. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Differentiation under the population integral**: `d/dN ∫ η u^h e^{-βN u^{2k}} =
−β ∫ (u^{2k} η) u^h e^{-βN u^{2k}}` at every `N₀ > 0`. -/
theorem hasDerivAt_popIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    HasDerivAt (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η)
      (-β * origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u))
      N₀ := by
  set c : (Fin (n + 1) → ℝ) → ℝ := fun x => ∏ i, x i ^ (2 * k i) with hc
  set a : (Fin (n + 1) → ℝ) → ℝ := fun x => η x * ∏ i, x i ^ h i with ha
  have hcc : Continuous c := continuous_prod_pow _
  have hac : Continuous a := hηc.mul (continuous_prod_pow _)
  set G : ℝ → (Fin (n + 1) → ℝ) → ℝ := fun N x => a x * Real.exp (-(β * N * c x)) with hG
  set G' : ℝ → (Fin (n + 1) → ℝ) → ℝ :=
    fun N x => a x * (Real.exp (-(β * N * c x)) * (-(β * c x))) with hG'
  have hGc : ∀ N, Continuous (G N) := fun N =>
    hac.mul (Real.continuous_exp.comp ((continuous_const.mul hcc).neg))
  have hG'c : ∀ N, Continuous (G' N) := fun N =>
    hac.mul ((Real.continuous_exp.comp ((continuous_const.mul hcc).neg)).mul
      (continuous_const.mul hcc).neg)
  -- the integrals in terms of `G`, `G'`
  have hZ : ∀ N, origPhaseIntegral n h k β N 1 (fun _ => 0) η =
      ∫ x in unitBox (n + 1), G N x := by
    intro N
    rw [origPhaseIntegral_population_eq_weight]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => ?_
    simp only [hG, ha, popWeight]
    ring
  have hZK : origPhaseIntegral n h k β N₀ 1 (fun _ => 0)
      (fun u => (∏ i, u i ^ (2 * k i)) * η u) = ∫ x in unitBox (n + 1), (-β)⁻¹ * G' N₀ x := by
    rw [origPhaseIntegral_population_eq_weight]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => ?_
    simp only [hG', ha, hc, popWeight]
    field_simp
  -- differentiation under the integral
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (unitBox (n + 1))) (F := G) (F' := G') (x₀ := N₀)
    (s := Metric.ball N₀ (N₀ / 2)) (bound := fun x => |a x| * (β * c x))
    (Metric.ball_mem_nhds _ (by positivity))
    (Eventually.of_forall fun N => (hGc N).aestronglyMeasurable)
    (integrableOn_unitBox_of_continuous _ (hGc N₀)) (hG'c N₀).aestronglyMeasurable ?_
    (integrableOn_unitBox_of_continuous _ (hac.abs.mul (continuous_const.mul hcc))) ?_
  · simp_rw [hZ]
    rw [hZK, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.2 hβ.ne'), one_mul]
    exact key.2
  · -- the dominating bound on the neighbourhood
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun x hx N hN => ?_
    have hc0 : 0 ≤ c x := Finset.prod_nonneg fun i _ => pow_nonneg (Set.mem_univ_pi.1 hx i).1.le _
    have hNpos : 0 < N := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hN
      linarith [hN.1]
    have hexp : Real.exp (-(β * N * c x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ β * N * c x := by positivity
      linarith
    simp only [hG', Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ β * c x)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_of_le_one_left (by positivity) hexp
  · -- pointwise differentiability in `N`
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun x _ N _ => ?_
    have hd := (((hasDerivAt_id N).const_mul (-(β * c x))).exp).const_mul (a x)
    refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [hG', id, mul_one]
      ring_nf
    · change a x * Real.exp (-(β * y * c x)) = a x * Real.exp (-(β * c x) * id y)
      congr 2
      simp only [id]
      ring

/-- The derivative of the population integral is `−β` times the energy insertion. -/
theorem deriv_popIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    deriv (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) N₀ =
      -β * origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u) :=
  (hasDerivAt_popIntegral n h k hβ η hηc hN₀).deriv

/-- **The exact energy identity** `𝒵_N[K∘π] = −(1/β) 𝒵_N'[1]` for `N > 0`. -/
theorem energy_eq_neg_deriv (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u) =
      -(1 / β) * deriv (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) N₀ := by
  rw [deriv_popIntegral n h k hβ η hηc hN₀]
  field_simp

end Grammar
