/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measured localisation of a Laplace-type integral

The measure-theoretic content of Steps 1–3 of the paper's expansion argument, separated from the
resolution geometry.  A `LocalisationData` packages a resolved measure `μ` (prior and Jacobian
absorbed), a nonnegative measurable phase `K` and an integrable observable `F`, so that the
population integral is `Z(N) = ∫ F e^{−NK} dμ`.

* `localisation_bound`: the integral over the complement of the sublevel set `{K < δ}` is
  `O(e^{−δN})`: `|Z(N) − Z_{<δ}(N)| ≤ (∫|F|) e^{−δN}` for `N ≥ 0`.
* `FiniteSublevelPartition`: finitely many measurable `ρ_i ≥ 0` with `∑ ρ_i = 1` a.e. on the
  sublevel set; `Zsublevel_eq_sum` splits `Z_{<δ}` into the per-piece integrals `∫ ρ_i F e^{−NK}`.
* `Z_eq_of_map`: the pullback to a resolved space is an equality of integrals given the measure
  transport certificate `Measure.map π μ_U = μ_X` — no injectivity of `π` is needed.
* `tendsto_mul_exp_of_exp_bound`: an exponential tail bound `|E N| ≤ C e^{−δN}` gives the
  little-o form `E N e^{εN} → 0` used by the assembly theorems, for every `ε < δ`.

Non-claims: no resolution of singularities, no construction of the partition of unity.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- A resolved Laplace-type integral: measure, phase, observable, and a localisation level. -/
structure LocalisationData (U : Type*) [MeasurableSpace U] where
  /-- the resolved measure (prior and Jacobian absorbed) -/
  μ : Measure U
  /-- the pulled-back phase `K ∘ π` -/
  phase : U → ℝ
  /-- the pulled-back observable -/
  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- The sublevel set `U_δ = {K < δ}`. -/
def sublevel : Set U := {z | D.phase z < D.δ}

theorem measurableSet_sublevel : MeasurableSet D.sublevel :=
  measurableSet_lt D.phase_measurable measurable_const

/-- The integrand `F e^{−NK}`. -/
noncomputable def integrand (N : ℝ) (z : U) : ℝ := D.obs z * Real.exp (-N * D.phase z)

/-- The population integral `Z(N) = ∫ F e^{−NK} dμ`. -/
noncomputable def Z (N : ℝ) : ℝ := ∫ z, D.integrand N z ∂D.μ

/-- The localised integral `Z_{<δ}(N) = ∫_{K<δ} F e^{−NK} dμ`. -/
noncomputable def Zsublevel (N : ℝ) : ℝ := ∫ z in D.sublevel, D.integrand N z ∂D.μ

theorem aestronglyMeasurable_integrand (N : ℝ) :
    AEStronglyMeasurable (D.integrand N) D.μ :=
  D.obs_integrable.aestronglyMeasurable.mul
    (measurable_const.mul D.phase_measurable).exp.aestronglyMeasurable

theorem abs_integrand_le {N : ℝ} (hN : 0 ≤ N) : ∀ᵐ z ∂D.μ, ‖D.integrand N z‖ ≤ ‖D.obs z‖ := by
  filter_upwards [D.phase_nonneg] with z hz
  unfold integrand
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.exp_le_one_iff.2 (by nlinarith))

theorem integrable_integrand {N : ℝ} (hN : 0 ≤ N) : Integrable (D.integrand N) D.μ :=
  Integrable.mono' D.obs_integrable.norm (D.aestronglyMeasurable_integrand N)
    (D.abs_integrand_le hN)

/-- **Exponential localisation**: the contribution of `{K ≥ δ}` is at most `(∫|F|) e^{−δN}`. -/
theorem localisation_bound {N : ℝ} (hN : 0 ≤ N) :
    |D.Z N - D.Zsublevel N| ≤ (∫ z, |D.obs z| ∂D.μ) * Real.exp (-D.δ * N) := by
  have hint := D.integrable_integrand hN
  have hsplit : D.Z N - D.Zsublevel N = ∫ z in D.sublevelᶜ, D.integrand N z ∂D.μ := by
    unfold Z Zsublevel
    rw [← integral_add_compl D.measurableSet_sublevel hint]
    ring
  rw [hsplit, ← Real.norm_eq_abs]
  have hbound : ∀ᵐ z ∂(D.μ.restrict D.sublevelᶜ),
      ‖D.integrand N z‖ ≤ |D.obs z| * Real.exp (-D.δ * N) := by
    rw [ae_restrict_iff' D.measurableSet_sublevel.compl]
    refine Eventually.of_forall fun z hz => ?_
    have hz' : D.δ ≤ D.phase z := not_lt.1 hz
    unfold integrand
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    nlinarith
  refine (norm_integral_le_of_norm_le (D.obs_integrable.norm.mul_const _ |>.restrict) hbound).trans
    ?_
  rw [integral_mul_const]
  gcongr
  exact setIntegral_le_integral D.obs_integrable.norm (Eventually.of_forall fun z => abs_nonneg _)

/-- Finitely many measurable weights, nonnegative and summing to `1` a.e. on the sublevel set. -/
structure FiniteSublevelPartition (ι : Type*) [Fintype ι] where
  ρ : ι → U → ℝ
  measurable_ρ : ∀ i, Measurable (ρ i)
  nonneg_ρ : ∀ i, ∀ᵐ z ∂D.μ, 0 ≤ ρ i z
  sum_eq_one : ∀ᵐ z ∂D.μ.restrict D.sublevel, ∑ i, ρ i z = 1

namespace FiniteSublevelPartition

variable {D} {ι : Type*} [Fintype ι] (P : D.FiniteSublevelPartition ι)

/-- The per-piece integral `∫_{K<δ} ρ_i F e^{−NK} dμ`. -/
noncomputable def piece (i : ι) (N : ℝ) : ℝ :=
  ∫ z in D.sublevel, P.ρ i z * D.integrand N z ∂D.μ

theorem ρ_le_one (i : ι) : ∀ᵐ z ∂D.μ.restrict D.sublevel, P.ρ i z ≤ 1 := by
  have hnn : ∀ᵐ z ∂D.μ.restrict D.sublevel, ∀ j, 0 ≤ P.ρ j z :=
    ae_all_iff.2 fun j => ae_restrict_of_ae (P.nonneg_ρ j)
  filter_upwards [P.sum_eq_one, hnn] with z hs hn
  calc P.ρ i z ≤ ∑ j, P.ρ j z := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    _ = 1 := hs

theorem integrable_piece (i : ι) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun z => P.ρ i z * D.integrand N z) (D.μ.restrict D.sublevel) := by
  refine Integrable.mono' (D.integrable_integrand hN).norm.restrict
    ((P.measurable_ρ i).aestronglyMeasurable.mul
      (D.aestronglyMeasurable_integrand N).restrict) ?_
  filter_upwards [P.ρ_le_one i, ae_restrict_of_ae (P.nonneg_ρ i)] with z h1 h0
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- **The finite decomposition of the localised integral**: `Z_{<δ} = ∑_i ∫ ρ_i F e^{−NK}`. -/
theorem Zsublevel_eq_sum {N : ℝ} (hN : 0 ≤ N) : D.Zsublevel N = ∑ i, P.piece i N := by
  unfold Zsublevel piece
  rw [← integral_finsetSum _ fun i _ => P.integrable_piece i hN]
  refine integral_congr_ae ?_
  filter_upwards [P.sum_eq_one] with z hz
  rw [← Finset.sum_mul, hz, one_mul]

end FiniteSublevelPartition

end LocalisationData

/-! ### Pullback along a measure-transporting map -/

/-- **Pullback to the resolved space**: if `π` transports the resolved measure onto the original
one, the original Laplace integral equals the resolved one for the pulled-back phase and
observable. No injectivity of `π` is required. -/
theorem integral_exp_eq_of_map {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    {μX : Measure X} {μU : Measure U} {π : U → X} (hπ : Measurable π) (hmap : μU.map π = μX)
    {K F : X → ℝ} (hK : Measurable K) (hF : AEStronglyMeasurable F μX) (N : ℝ) :
    ∫ x, F x * Real.exp (-N * K x) ∂μX = ∫ z, F (π z) * Real.exp (-N * K (π z)) ∂μU := by
  rw [← hmap] at hF ⊢
  exact integral_map hπ.aemeasurable (hF.mul (measurable_const.mul hK).exp.aestronglyMeasurable)

/-! ### From an exponential tail bound to the assembly hypothesis -/

/-- An exponential tail bound `|E N| ≤ C e^{−δN}` (for `N ≥ 0`) gives `E N e^{εN} → 0` for every
`ε < δ` — the little-o hypothesis of the finite-chart assembly theorems. -/
theorem tendsto_mul_exp_of_exp_bound {E : ℝ → ℝ} {C δ : ℝ}
    (hE : ∀ N, 0 ≤ N → |E N| ≤ C * Real.exp (-δ * N)) {ε : ℝ} (hεδ : ε < δ) :
    Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0) := by
  have hrate : Tendsto (fun N : ℝ => C * Real.exp (-(δ - ε) * N)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(δ - ε) < 0))).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ hrate
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |E N| * Real.exp (ε * N) ≤ C * Real.exp (-δ * N) * Real.exp (ε * N) :=
        mul_le_mul_of_nonneg_right (hE N hN) (Real.exp_pos _).le
    _ = C * Real.exp (-(δ - ε) * N) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

end Grammar

namespace Grammar

/-- The export with `ε = δ/2`: an exponential tail bound at level `δ` gives the little-o hypothesis
at level `δ/2`. -/
theorem tendsto_mul_exp_half_of_exp_bound {E : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ N, 0 ≤ N → |E N| ≤ C * Real.exp (-δ * N)) :
    Tendsto (fun N => E N * Real.exp (δ / 2 * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound hE (by linarith)

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- The tail `Z − Z_{<δ}` of a localisation datum satisfies the assembly hypothesis at `δ/2`. -/
theorem tail_tendsto : Tendsto (fun N => (D.Z N - D.Zsublevel N) * Real.exp (D.δ / 2 * N))
    atTop (𝓝 0) :=
  tendsto_mul_exp_half_of_exp_bound D.δ_pos fun _ hN => D.localisation_bound hN

end LocalisationData

end Grammar
