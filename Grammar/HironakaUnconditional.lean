import Grammar.ExponentComparison
import Monomialize.Analytic.BM89.QInduction

/-!
# The population Laplace exponent pair, unconditionally

`timaeus-research/hironaka` (now pinned at `eb9b6ca`) proves Bierstone–Milman's Theorem 3.2 in
chart form for every dimension, `Q_all (n) : Q n` (`Monomialize/Analytic/BM89/QInduction.lean`,
axiom-clean). The grammar theorems that took `Q n` as an explicit hypothesis are therefore
unconditional:

* `laplaceTheta_of_analyticOnNhd_nonneg`: for `K` real-analytic on an open set containing a zero
  `w`, not identically zero near `w`, `K ≥ 0` near `w`, there are `λ ∈ ℚ_{>0}`, `1 ≤ θ ≤ n`,
  `r₀ > 0` with `∫_{closedBall w r} e^{−NK} dx ≍ N^{−λ}(log N)^{θ−1}` for every `0 < r ≤ r₀`;
* `exists_exponentPair`: any certified population core theorem `A_n Z^pop(n) → L₀ > 0` on such a
  cube has `λ = λ_H` and `m − 1 = θ_H − 1`;
* `tendstoInMeasure_log_div_log_of_analyticOnNhd_nonneg`: the empirical exponent statement
  `log Z_n^{emp}/log n → −λ_H` in probability, with `λ_H` the population pair of the analytic
  nonnegative phase, given the certified core limit of the population integral and the empirical
  distributional limit.

Non-claims: the certified chart presentation (charts, adapted partition of unity, exact normal
form) and the remainder estimates remain external; `Q_all` is consumed as a theorem of the
dependency, not re-proved here.
-/

open MeasureTheory Filter Topology

namespace Grammar

/-- **The population Laplace exponent pair of a real-analytic nonnegative phase**, with hironaka's
`Q n` discharged by `Q_all`. -/
theorem laplaceTheta_of_analyticOnNhd_nonneg {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U) (h0 : K w = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lam : ℚ) (theta : ℕ) (r₀ : ℝ), 0 < lam ∧ 1 ≤ theta ∧ theta ≤ n ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        LaplaceTheta ((volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall w r)) K
          (lam : ℝ) (theta - 1) :=
  laplaceTheta_of_analyticOnNhd_nonneg_of_Q (Monomialize.Analytic.Q_all n) hU hK hw h0 hne hK0

/-- **Exponent identification, unconditionally**: for a real-analytic nonnegative phase there is a
pair `(λ_H, θ_H)` such that on every small closed cube any certified population core theorem
`A_n Z^pop(n) → L₀ > 0` has `λ = λ_H` and `m − 1 = θ_H − 1`. -/
theorem exists_exponentPair {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U) (h0 : K w = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lamH : ℚ) (thetaH : ℕ) (r₀ : ℝ), 0 < lamH ∧ 1 ≤ thetaH ∧ thetaH ≤ n ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (lam : ℝ) (m : ℕ) (L₀ : ℝ), 0 < L₀ →
        Tendsto (fun k : ℕ => scaleA lam m k *
          ∫ x in Metric.closedBall w r, Real.exp (-(k : ℝ) * K x)) atTop (𝓝 L₀) →
        lam = lamH ∧ m - 1 = thetaH - 1 :=
  exists_exponentPair_of_Q (Monomialize.Analytic.Q_all n) hU hK hw h0 hne hK0

/-- **The empirical exponent of a real-analytic nonnegative phase**: on every small closed cube
around a zero of `K`, if the population integral has a certified core limit `A_n Z^pop(n) → L₀ > 0`
at the pair `(λ, m)` and the scaled empirical evidence converges in distribution to an almost
surely positive limit at the same pair, then `log Z_n^{emp}/log n → −λ_H` in probability, `λ_H`
the population exponent of `K` at `w`. -/
theorem tendstoInMeasure_log_div_log_of_analyticOnNhd_nonneg {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U)
    (h0 : K w = 0) (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lamH : ℚ) (r₀ : ℝ), 0 < lamH ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (lam : ℝ) (m : ℕ) (L₀ : ℝ), 0 < L₀ →
        Tendsto (fun k : ℕ => scaleA lam m k *
          ∫ x in Metric.closedBall w r, Real.exp (-(k : ℝ) * K x)) atTop (𝓝 L₀) →
        ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
          {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
          {Z : ℕ → Ω → ℝ} {L : Ω' → ℝ},
          TendstoInDistribution (fun k ω => scaleA lam m k * Z k ω) atTop L (fun _ => μ) μ' →
          (∀ k ω, 0 < Z k ω) → (∀ᵐ ω ∂μ', 0 < L ω) →
          TendstoInMeasure μ (fun k ω => Real.log (Z k ω) / Real.log k) atTop
            (fun _ => -(lamH : ℝ)) := by
  obtain ⟨lamH, thetaH, r₀, hlam, -, -, hr₀, hpair⟩ := exists_exponentPair hU hK hw h0 hne hK0
  refine ⟨lamH, r₀, hlam, hr₀, fun r hr hrle lam m L₀ hL hconv => ?_⟩
  intro Ω _ μ _ Ω' _ μ' _ Z L hdist hZpos hLpos
  exact tendstoInMeasure_log_div_log_of_population_comparison m
    (hpair r hr hrle lam m L₀ hL hconv).1 hdist hZpos hLpos

end Grammar
