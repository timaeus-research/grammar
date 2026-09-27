/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.LogSquareDensityPolar

/-!
# Averaging the fibre polar dictionary over the base

The naive Bayes polar distributions of `Grammar.LogSquareDensityPolar` are fixed-fibre statements
(fixed means `λ`).  Passing to the model integrates the fibre continuations over `λ`:
if for each `λ` the fibre transform continues as `2φ_λ(0)·logSqRat(ℓ_λ, c_λ, s) + H_λ(s)` with `H_λ`
holomorphic on `Re s < 1`, then under joint measurability and an integrable domination of the
derivatives (locally uniform in `s`) the averaged transform continues as

  `polarPart 2 ā (½) + H̄(s)`,   `ā_q = ∫ a_q(λ) dν`,   `H̄(s) = ∫ H_λ(s) dν` holomorphic,

so the averaged polar distributions are the averages of the fibre ones:
`C̄_{½,3} = −∫φ_λ(0)`, `C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`
(★★★ `averaged_logSq_polar`).  The analytic engine is the holomorphy of parametric integrals
under derivative domination (★★ `differentiableOn_integral_of_deriv_dominated`, from Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the measurability of `λ ↦ (H_λ)'(s)`
obtained as a limit of difference quotients, `aestronglyMeasurable_deriv_family`).  Verifying the
domination for the actual naive Bayes envelope `M_±(λ)` is the separate geometric step
(examples_slop §6; Astra round-4 target 3).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}

/-- Measurability of `λ ↦ (H_λ)'(s₀)` from the measurability of `λ ↦ H_λ(s)`: the derivative is the
limit of difference quotients along `t_n = ε/(n+2)`. -/
theorem aestronglyMeasurable_deriv_family {H : Λ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {s₀ : ℂ}
    (hs₀ : s₀ ∈ U) (hmeas : ∀ s ∈ U, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableAt ℂ (H l) s₀) :
    AEStronglyMeasurable (fun l => deriv (H l) s₀) ν := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀
  set t : ℕ → ℂ := fun n => ((ε / (n + 2) : ℝ) : ℂ) with ht
  have htpos : ∀ n : ℕ, 0 < ε / ((n : ℝ) + 2) := fun n => by positivity
  have htlt : ∀ n : ℕ, ε / ((n : ℝ) + 2) < ε := fun n => by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htmem : ∀ n, s₀ + t n ∈ U := fun n => hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ht]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)]
    exact htlt n)
  have htend : Tendsto t atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    · exact Eventually.of_forall fun n => by
        rw [ht]; simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (htpos n).ne'
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n l => (t n)⁻¹ • (H l (s₀ + t n) - H l s₀)) ?_ ?_
  · intro n
    exact ((hmeas _ (htmem n)).sub (hmeas s₀ hs₀)).const_smul ((t n)⁻¹)
  · filter_upwards [hdiff] with l hl
    exact (hasDerivAt_iff_tendsto_slope_zero.1 hl.hasDerivAt).comp htend

/-- ★★ **Holomorphy of a parametric integral under derivative domination.** -/
theorem differentiableOn_integral_of_deriv_dominated {H : Λ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ s ∈ U, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableOn ℂ (H l) U)
    (hint : ∀ s ∈ U, Integrable (fun l => H l s) ν)
    (hdom : ∀ s₀ ∈ U, ∃ ε > 0, Metric.ball s₀ ε ⊆ U ∧ ∃ B : Λ → ℝ, Integrable B ν ∧
      ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball s₀ ε, ‖deriv (H l) s‖ ≤ B l) :
    DifferentiableOn ℂ (fun s => ∫ l, H l s ∂ν) U := by
  intro s₀ hs₀
  obtain ⟨ε, hε, hball, B, hB, hbound⟩ := hdom s₀ hs₀
  have hdiff' : ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball s₀ ε, HasDerivAt (H l) (deriv (H l) s) s := by
    filter_upwards [hdiff] with l hl
    intro s hs
    exact (hl.differentiableAt (hU.mem_nhds (hball hs))).hasDerivAt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s l => H l s) (F' := fun s l => deriv (H l) s) (bound := B)
    (s := Metric.ball s₀ ε) (Metric.ball_mem_nhds s₀ hε)
    (Filter.eventually_of_mem (hU.mem_nhds hs₀) fun s hs => hmeas s hs)
    (hint s₀ hs₀)
    (aestronglyMeasurable_deriv_family hU hs₀ hmeas
      (hdiff.mono fun l hl => hl.differentiableAt (hU.mem_nhds hs₀)))
    hbound hB hdiff'
  exact key.2.differentiableAt.differentiableWithinAt

/-! ### Averaging the log-square fibre dictionary -/

/-- The averaged polar coefficients `ā_q = ∫ a_q(λ) dν`. -/
noncomputable def logSqAvgA (φ₀ ℓ c : Λ → ℝ) (ν : Measure Λ) : ℕ → ℂ := fun q =>
  ∫ l, logSqA (ℓ l) (c l) (2 * φ₀ l) q ∂ν

theorem integrable_polarPart_logSqA {φ₀ ℓ c : Λ → ℝ}
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν) (s : ℂ) :
    Integrable (fun l => polarPart 2 (logSqA (ℓ l) (c l) (2 * φ₀ l)) (1 / 2 : ℂ) s) ν := by
  unfold polarPart
  refine integrable_finsetSum _ fun q hq => ?_
  exact (hcoef q (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hq)).div_const _

/-- The integral of the fibre polar parts is the polar part of the averaged coefficients. -/
theorem integral_polarPart_logSqA {φ₀ ℓ c : Λ → ℝ}
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν) (s : ℂ) :
    ∫ l, polarPart 2 (logSqA (ℓ l) (c l) (2 * φ₀ l)) (1 / 2 : ℂ) s ∂ν =
      polarPart 2 (logSqAvgA φ₀ ℓ c ν) (1 / 2 : ℂ) s := by
  unfold polarPart logSqAvgA
  rw [integral_finsetSum _ fun q hq =>
    (hcoef q (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hq)).div_const _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_div]

/-- ★★★ **The averaged polar distributions**: if each fibre continuation is
`2φ_λ(0)·logSqRat(ℓ_λ, c_λ, s) + H_λ(s)` with `H_λ` holomorphic on `Re s < 1`, dominated as above,
then the averaged continuation has the principal part `polarPart 2 ā (½)` with `ā_q = ∫ a_q(λ) dν`:
`C̄_{½,3} = −∫φ_λ(0)`, `C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`. -/
theorem averaged_logSq_polar {φ₀ ℓ c : Λ → ℝ} {H : Λ → ℂ → ℂ}
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν)
    (hmeas : ∀ s ∈ {s : ℂ | s.re < 1}, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableOn ℂ (H l) {s : ℂ | s.re < 1})
    (hint : ∀ s ∈ {s : ℂ | s.re < 1}, Integrable (fun l => H l s) ν)
    (hdom : ∀ s₀ ∈ {s : ℂ | s.re < 1}, ∃ ε > 0, Metric.ball s₀ ε ⊆ {s : ℂ | s.re < 1} ∧
      ∃ B : Λ → ℝ, Integrable B ν ∧ ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball s₀ ε, ‖deriv (H l) s‖ ≤ B l) :
    (fun s => (∫ l, (((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s) ∂ν) -
      polarPart 2 (logSqAvgA φ₀ ℓ c ν) (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hopen : IsOpen {s : ℂ | s.re < 1} := isOpen_re_lt 1
  have hmem : (1 / 2 : ℂ) ∈ {s : ℂ | s.re < 1} := by
    change (1 / 2 : ℂ).re < 1; norm_num
  have hHol := differentiableOn_integral_of_deriv_dominated hopen hmeas hdiff hint hdom
  have hcont : ContinuousAt (fun s => ∫ l, H l s ∂ν) (1 / 2) :=
    (hHol.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have hO : (fun s => ∫ l, H l s ∂ν) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  have hU : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s ∈ {s : ℂ | s.re < 1} :=
    eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hmem)
  filter_upwards [hU, self_mem_nhdsWithin] with s hs hs'
  have hs2 : s ≠ 1 / 2 := hs'
  -- the pointwise identity on the strip
  have hpt : ∀ l, ((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s =
      polarPart 2 (logSqA (ℓ l) (c l) (2 * φ₀ l)) (1 / 2 : ℂ) s + H l s := fun l => by
    rw [← logSqRat_eq_polarPart (ℓ l) (c l) (2 * φ₀ l) hs2]
  simp_rw [hpt]
  rw [integral_add (integrable_polarPart_logSqA hcoef s) (hint s hs),
    integral_polarPart_logSqA hcoef s]
  ring

end Grammar
