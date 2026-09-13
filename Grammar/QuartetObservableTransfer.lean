/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FiniteQuartetTransfer

/-!
# Expected quartet coefficients from an `L¹` observable-transfer certificate
(CCCLV; companion note, consult #106 Rank 2)

The honest statistical interface for the expected-error coefficients: let `B_{n,j}` be the actual
scaled model observables and `𝓠_j(g_n)` the four Bayes combinations of the finite-resolution
quartet at the empirical phase vector. If `𝔼|B_{n,j} − 𝓠_j(g_n)| → 0` (`L¹` observable transfer)
and the empirical phase vectors converge in distribution to the Gaussian vector with uniform
moments, then `𝔼B_{n,j} → (λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν)_j` with `ν = 𝔼H(G)/2`
(★★ `tendsto_integral_of_L1_transfer` for one observable, ★★★ `expected_quartet_of_L1_transfer`
for the four). The residual must be `o_{L¹}(1)`: an `o_P(1)` residual would need a separate uniform
integrability certificate for the actual `B_{n,j}` (not supplied here). The identification of the
`B_{n,j}` with a statistical model's error coefficients, and the predictive remainder, are the
model-facing inputs (Ranks 2–3 of #106).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace Grammar

section L1Transfer

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}

/-- ★★ **`L¹` transfer of expectations**: if `𝔼|B_n − Q_n| → 0` and `𝔼Q_n → L`, then `𝔼B_n → L`. -/
theorem tendsto_integral_of_L1_transfer {B Q : ∀ n, Ω n → ℝ} {L : ℝ}
    (hBint : ∀ n, Integrable (B n) (μ n)) (hQint : ∀ n, Integrable (Q n) (μ n))
    (hL1 : Tendsto (fun n => ∫ ω, |B n ω - Q n ω| ∂μ n) atTop (𝓝 0))
    (hQ : Tendsto (fun n => ∫ ω, Q n ω ∂μ n) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, B n ω ∂μ n) atTop (𝓝 L) := by
  have hdiff : Tendsto (fun n => ∫ ω, B n ω ∂μ n - ∫ ω, Q n ω ∂μ n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hL1
    rw [← integral_sub (hBint n) (hQint n), Real.norm_eq_abs]
    exact (abs_integral_le_integral_abs).trans (le_of_eq rfl)
  have := hdiff.add hQ
  simpa using this

end L1Transfer

section Endpoint

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {m k : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}
  (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
  {g : ∀ n, Ω n → Fin m → ℝ} {G : Ω' → Fin m → ℝ}
  (hg : TendstoInDistribution g atTop G μ μ') (hmom : UniformMoments μ g)
  (A : Matrix (Fin m) (Fin (k + 1)) ℝ) (hG : μ'.map G = gaussianVector A) {c : ℝ}
  (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c)

/-- The four Bayes combinations of the finite-resolution quartet at a phase vector. -/
noncomputable def bayesCombination (β lam : ℝ) (ρ : Fin m → ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) : Fin 4 → (Fin m → ℝ) → ℝ
  | 0 => fun z => quartetM2 β lam ρ z
  | 1 => fun z => quartetM2 β lam ρ z - quartetH β lam ρ z
  | 2 => fun z => quartetM2 β lam ρ z - quartetV β lam ρ b c z / 2
  | 3 => fun z => quartetM2 β lam ρ z - quartetH β lam ρ z - quartetV β lam ρ b c z / 2

/-- The four Bayes values `λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν`. -/
noncomputable def bayesValue (β lam ν : ℝ) : Fin 4 → ℝ
  | 0 => lam / β + ν
  | 1 => lam / β - ν
  | 2 => (lam - ν) / β + ν
  | 3 => (lam - ν) / β - ν

include hβ hlam hρ hg hmom hG hc in
/-- ★★★ **Expected quartet coefficients from `L¹` observable transfer**: for actual scaled
observables `B_{n,j}` with `𝔼|B_{n,j} − 𝓠_j(g_n)| → 0`, `𝔼B_{n,j} → bayesValue β λ ν j`,
`ν = 𝔼H(G)/2`. -/
theorem expected_quartet_of_L1_transfer {B : Fin 4 → ∀ n, Ω n → ℝ}
    (hBint : ∀ j n, Integrable (B j n) (μ n))
    (hL1 : ∀ j, Tendsto (fun n => ∫ ω, |B j n ω -
      bayesCombination β lam ρ (A * A.transpose) c j (g n ω)| ∂μ n) atTop (𝓝 0)) (j : Fin 4) :
    Tendsto (fun n => ∫ ω, B j n ω ∂μ n) atTop
      (𝓝 (bayesValue β lam ((∫ z, quartetH β lam ρ z ∂gaussianVector A) / 2) j)) := by
  have hQ := tendsto_integral_bayes_quartet hβ hlam hρ hg hmom A hG hc
  -- integrability of the quartet combinations along the sequence
  have hcM2 : Continuous (quartetM2 β lam ρ) :=
    continuous_finsetSum _ fun i _ => continuous_quartetR hβ hlam hρ i
  have hbM2 := polyBoundedPi_quartetM2 hβ hlam hρ
  have hcH := continuous_quartetH hβ hlam hρ
  have hbH := polyBoundedPi_quartetH hβ hlam hρ
  have hcV := continuous_quartetV hβ hlam hρ (A * A.transpose) c
  have hbV := polyBoundedPi_quartetV hβ hlam hρ (A * A.transpose) c
  have hint : ∀ (F : (Fin m → ℝ) → ℝ), Continuous F → PolyBoundedPi F →
      ∀ n, Integrable (fun ω => F (g n ω)) (μ n) := fun F hF hFb n => by
    obtain ⟨C, kk, hCk⟩ := hFb
    obtain ⟨M, hM⟩ := hmom kk
    have hC : 0 ≤ C := by
      have := hCk 0
      have hpos : (0 : ℝ) < (1 + ‖(0 : Fin m → ℝ)‖) ^ kk := by positivity
      nlinarith [abs_nonneg (F 0)]
    refine (((integrable_const (1 : ℝ)).add (hM n).1).const_mul (C * 2 ^ kk)).mono'
      ((hF.measurable.comp_aemeasurable (hg.forall_aemeasurable n)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    calc |F (g n ω)| ≤ C * (1 + ‖g n ω‖) ^ kk := hCk _
      _ ≤ C * (2 ^ kk * (1 + ‖g n ω‖ ^ kk)) := by gcongr; exact one_add_pow_le (norm_nonneg _) kk
      _ = C * 2 ^ kk * (1 + ‖g n ω‖ ^ kk) := by ring
  have hV2 : PolyBoundedPi fun z => quartetV β lam ρ (A * A.transpose) c z / 2 := by
    have e : (fun z => quartetV β lam ρ (A * A.transpose) c z / 2) =
        fun z => (1 / 2) * quartetV β lam ρ (A * A.transpose) c z := funext fun z => by ring
    rw [e]
    exact hbV.const_mul _
  fin_cases j
  · exact tendsto_integral_of_L1_transfer (hBint 0) (hint _ hcM2 hbM2) (hL1 0) hQ.1
  · exact tendsto_integral_of_L1_transfer (hBint 1) (hint _ (hcM2.sub hcH) (hbM2.sub hbH)) (hL1 1)
      hQ.2.1
  · exact tendsto_integral_of_L1_transfer (hBint 2) (hint _ (hcM2.sub (hcV.div_const 2))
      (hbM2.sub hV2)) (hL1 2) hQ.2.2.1
  · exact tendsto_integral_of_L1_transfer (hBint 3) (hint _ ((hcM2.sub hcH).sub (hcV.div_const 2))
      ((hbM2.sub hbH).sub hV2)) (hL1 3) hQ.2.2.2

end Endpoint

end Grammar
