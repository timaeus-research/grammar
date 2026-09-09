/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingCoeff

/-!
# The first-candidate term of the population expansion (Astra #37 Theorem A(c), unit 297)

Collecting P1–P2 at chart level on the unit box: for `η` continuous with a holomorphic extension
on a polydisc of radius `R > 1` (real-part agreement on the box), `λ = min_i (hᵢ+1)/(2kᵢ)`, `m`
its multiplicity, `A = amplitudeCoeff h k λ β η` the face functional,

* there are no terms at exponents below `λ` (`population_coeff_eq_zero_of_lt`: candidates are
  `≥ λ`, and coefficients vanish off the candidate set);
* at exponent `λ` there are no terms of log degree above `m − 1` among the expansion's log
  degrees `0, …, n`, and the `(λ, m−1)` coefficient is `A` (P1);
* if `A ≠ 0` the population integral is asymptotically equivalent to `A N^{-λ}(log N)^{m−1}`
  (`population_isEquivalent`, directly from Headline VIII).

`population_firstCandidate` packages these. If `A = 0` nothing is asserted about the actual
leading term: the next nonzero coefficient may sit at the same exponent with a smaller log degree.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- Coefficients of a candidate-supported system vanish below the minimal ratio. -/
theorem population_coeff_eq_zero_of_lt {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    {C : ℝ → ℕ → ℝ} (hvan : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {μ : ℝ} (hμ : μ < l) (j : ℕ) : C μ j = 0 :=
  hvan μ j fun hc => absurd (le_of_candidateExp h k hk hmin hc) (not_le.2 hμ)

/-- **Asymptotic equivalence of the population integral** with its first-candidate term when the
face functional is nonzero: `∫ η u^h e^{-βN u^{2k}} ~ A N^{-λ}(log N)^{m−1}`. -/
theorem population_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) (hA : amplitudeCoeff h k l β η ≠ 0) :
    (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop]
      fun N => amplitudeCoeff h k l β η *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hT := amplitude_tendsto n h k hk l β hl hβ hmin hatt η hηc
  have hT' : Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) / amplitudeCoeff h k l β η)
      atTop (𝓝 (amplitudeCoeff h k l β η / amplitudeCoeff h k l β η)) := by
    refine (hT.congr' (Eventually.of_forall fun N => ?_)).div_const _
    simp only [origPhaseIntegral_population_one]
  rw [div_self hA] at hT'
  refine isEquivalent_of_tendsto_one (hT'.congr' (Eventually.of_forall fun N => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- **Theorem A(c) at chart level (`b = 1`)**: the population Taylor tree has no terms below
`λ`, none at `λ` above log degree `m − 1` (among the degrees `0, …, n`), its `(λ, m−1)`
coefficient is the face functional
`A`, and when `A ≠ 0` the integral is asymptotically `A N^{-λ}(log N)^{m−1}`. -/
theorem population_firstCandidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β 1 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
      (∀ μ, μ < l → ∀ j, C μ j = 0) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η ∧
      (amplitudeCoeff h k l β η ≠ 0 →
        (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop]
          fun N => amplitudeCoeff h k l β η *
            (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) := by
  obtain ⟨C, hC, hI, hzero, hlead⟩ := population_leadingCoeff n h k hk β hβ hR hFη hη hηc hmin hatt
  exact ⟨C, hC, hI, fun μ hμ j => population_coeff_eq_zero_of_lt h k hk hC.vanish hmin hμ j,
    hzero, hlead, fun hA => population_isEquivalent n h k hk β hβ hmin hatt η hηc hA⟩

end Grammar
