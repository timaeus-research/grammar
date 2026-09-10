/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SampleDatum

/-!
# The stochastic expansion at the sample datum

`thm:strataempiricalexpansion` at chart level with the data premise discharged: for an i.i.d. sample
whose chart Taylor coefficients satisfy the chart moment certificate, the canonical coefficients
`C_{μ,j}` of the chart integral at the sample datum converge in distribution to those at a
translate of the `ℓ¹` Gaussian limit, and the ordered normalised remainders
`(Z_N(x_n) − ∑_{(μ,j)<(μ',j')} C_{μ,j} N^{−μ} log^j N) / (N^{−μ'} log^{j'} N)` at any scale sequence
`N_n → ∞` converge in distribution to the corresponding limiting coefficients
(`sample_stochastic_expansion`).  The limit law is the law `ν` produced by the `ℓ¹` CLT, translated
by the amplitude datum; its finite coordinate marginals are centred Gaussians with the covariance
of the sample coefficients.

Non-claims: the chart moment certificate is a hypothesis (not derived from Hypothesis I for the
resolved chart function); the sample size in the CLT is the sequence index `n : ℕ`, while the scale
`N_n` of the expansion is any real sequence tending to infinity (the paper takes `N = n`); single
chart; no joint-chart statement.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {n : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily (n + 1))
  (hc : ∀ x, AbsSummableAt (c x) b) (X : ℕ → Ω → 𝓧)

theorem measurable_sampleDatum (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace (n + 1)) (i : ℕ) : Measurable (sampleDatum b hb c hc P X A i) :=
  (continuous_add_const A).measurable.comp (measurable_empiricalSum
    (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
    (measurable_sampleObs b hb c hc X hcm hXm) i)

/-- **The stochastic expansion at the sample datum** (`thm:strataempiricalexpansion`, chart level,
data premise discharged): under an i.i.d. sampling law and the chart moment certificate there is a
law `ν` on the data space such that (i) the sample data converge in distribution to `x ↦ x + A`
under `ν`; (ii) every finite vector of canonical coefficients at the sample datum converges in
distribution to the coefficients at `x + A`; (iii) for every finite family of admissible targets
and every scale sequence `N_i → ∞`, the ordered normalised remainders converge in distribution to
the corresponding limiting coefficients; (iv) the finite coordinate marginals of `ν` are the
centred Gaussians with the covariance of the sample coefficients. -/
theorem sample_stochastic_expansion (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace (n + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      TendstoInDistribution (sampleDatum b hb c hc P X A) atTop (fun x => x + A) (fun _ => P)
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      (∀ {m : ℕ} (F : Fin m → ℝ × ℕ),
        TendstoInDistribution (fun i => dataCoeffVec n h k β b F ∘ sampleDatum b hb c hc P X A i)
          atTop (dataCoeffVec n h k β b F ∘ fun x => x + A) (fun _ => P)
          (ν : Measure (L1Seq (DataIdx (n + 1))))) ∧
      (∀ {m : ℕ} (F : Fin m → ℝ × ℕ),
        (∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n) →
        ∀ (Nseq : ℕ → ℝ), (∀ i, 0 ≤ Nseq i) → Tendsto Nseq atTop atTop →
        TendstoInDistribution
          (fun i ω => orderedRemainderVec n h k β b F (sampleDatum b hb c hc P X A i ω) (Nseq i))
          atTop (fun x => dataCoeffVec n h k β b F (x + A)) (fun _ => P)
          (ν : Measure (L1Seq (DataIdx (n + 1))))) ∧
      ∀ F : Finset (DataIdx (n + 1)), (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P := by
  obtain ⟨ν, hν, hmarg, -⟩ :=
    sampleDatum_tendstoInDistribution b hb c hc P X hcm hXm hXind hXid hc2 hsum A
  refine ⟨ν, hν, fun F => ?_, fun F hF Nseq hN0 hN => ?_, hmarg⟩
  · exact tendstoInDistribution_dataCoeffVec n h k hk β hβ hb F _ _ hν
  · exact tendstoInDistribution_orderedRemainderVec n h k hk β hβ hb F hF _
      (measurable_sampleDatum P b hb c hc X hcm hXm hc2 hsum A) _ hν Nseq hN0 hN

end Grammar
