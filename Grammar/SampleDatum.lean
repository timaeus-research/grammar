/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1SeqCLT
import Grammar.StochasticTaylorTreeJoint

/-!
# The sample datum and the stochastic expansion with the data premise discharged

The random Taylor datum of an i.i.d. sample.  Each sample point `x` carries a coefficient family
`c x : (Fin d → ℕ) → ℝ` (the Taylor coefficients at the chart origin of the resolved fluctuation
`a(x, ·)`), absolutely summable at the box radius `b`; its **phase observation** is the data-space
element with phase coordinates `c_γ(x) b^{|γ|}` and zero amplitude (`phaseObs`).  The **sample
datum** is the normalised centred empirical sum of the phase observations plus a fixed amplitude
datum `A` (`sampleDatum`): its phase coordinates are the paper's `ξ_n` Taylor coefficients
`n^{−1/2} ∑_{i<n} (c_γ(X_i) − E c_γ(X)) b^{|γ|}` (`xiCoord_sampleDatum`) and its amplitude
coordinates are those of `A` (`etaCoord_sampleDatum`).

Under the **chart moment certificate** — coordinates in `L²` and summable weighted `L²` norms
`∑_γ b^{|γ|} ‖c_γ(X)‖_{L²} < ∞`, implied by a Cauchy envelope `‖c_γ(X)‖_{L²} ≤ M R^{−|γ|}` with
`b < R` (`summable_of_cauchy_envelope`) — the sample datum converges in distribution on the data
space to a translate of the `ℓ¹` Gaussian limit (`sampleDatum_tendstoInDistribution`), and the
stochastic Taylor tree applies: the canonical coefficients and the ordered normalised remainders of
the chart integral at the sample datum converge in distribution (`sample_coeffVec_tendsto`,
`sample_orderedRemainderVec_tendsto`) — `thm:strataempiricalexpansion` at chart level with the
data premise discharged from an i.i.d. sampling law and the certificate.

Non-claims: the certificate is not derived from the paper's Hypothesis I for the resolved chart
function; pointwise absolute summability of the sample coefficients is assumed; single chart (the
joint-chart statement is a finite disjoint union of coordinate indices, not treated here).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {d : ℕ} {𝓧 : Type*} (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)

/-- The phase observation of a sample point: phase coordinates `c_γ(x) b^{|γ|}`, zero amplitude. -/
noncomputable def phaseObs (x : 𝓧) : L1Seq (DataIdx d) :=
  ofFamilies b hb (c x) 0 (hc x) (absSummableAt_zero b)

theorem phaseObs_inl (x : 𝓧) (γ : Fin d → ℕ) :
    phaseObs b hb c hc x (Sum.inl γ) = c x γ * b ^ (∑ i, γ i) := rfl

theorem phaseObs_inr (x : 𝓧) (γ : Fin d → ℕ) : phaseObs b hb c hc x (Sum.inr γ) = 0 := by
  change (0 : CoeffFamily d) γ * b ^ (∑ i, γ i) = 0
  simp

variable [MeasurableSpace 𝓧]

theorem measurable_phaseObs (hcm : ∀ γ, Measurable fun x => c x γ) :
    Measurable (phaseObs b hb c hc) := by
  refine measurable_of_coords fun j => ?_
  rcases j with γ | γ
  · simp only [phaseObs_inl]
    exact (hcm γ).mul_const _
  · simp only [phaseObs_inr]
    exact measurable_const

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → 𝓧)

/-- The i.i.d. phase observations `Y_i = phaseObs (X_i)`. -/
noncomputable def sampleObs (i : ℕ) (ω : Ω) : L1Seq (DataIdx d) := phaseObs b hb c hc (X i ω)

/-- The sample datum: the empirical fluctuation datum plus the fixed amplitude datum `A`. -/
noncomputable def sampleDatum (A : DataSpace d) (n : ℕ) (ω : Ω) : DataSpace d :=
  empiricalSum (sampleObs b hb c hc X) P n ω + A

omit [MeasurableSpace 𝓧] in
theorem coordL2_sampleObs_inl (γ : Fin d → ℕ) :
    coordL2 P (sampleObs b hb c hc X 0) (Sum.inl γ) =
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P) := by
  unfold coordL2 sampleObs
  simp only [phaseObs_inl, mul_pow]
  rw [integral_mul_const, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (pow_pos hb _).le, mul_comm]

omit [MeasurableSpace 𝓧] in
theorem coordL2_sampleObs_inr (γ : Fin d → ℕ) :
    coordL2 P (sampleObs b hb c hc X 0) (Sum.inr γ) = 0 := by
  unfold coordL2 sampleObs
  simp [phaseObs_inr]

theorem iIndepFun_sampleObs (hcm : ∀ γ, Measurable fun x => c x γ) (hXind : iIndepFun X P) :
    iIndepFun (sampleObs b hb c hc X) P :=
  hXind.comp (fun _ => phaseObs b hb c hc) fun _ => measurable_phaseObs b hb c hc hcm

theorem identDistrib_sampleObs (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) (i : ℕ) :
    IdentDistrib (sampleObs b hb c hc X i) (sampleObs b hb c hc X 0) P P :=
  (hXid i).comp (measurable_phaseObs b hb c hc hcm)

theorem measurable_sampleObs (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (i : ℕ) : Measurable (sampleObs b hb c hc X i) :=
  (measurable_phaseObs b hb c hc hcm).comp (hXm i)

variable [IsProbabilityMeasure P]

/-- **The chart moment certificate** gives the moment hypothesis of the `ℓ¹` CLT. -/
theorem summableCoordL2_sampleObs (hcm : ∀ γ, Measurable fun x => c x γ) (hX0 : Measurable (X 0))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P)) :
    SummableCoordL2 P (sampleObs b hb c hc X 0) where
  measurable := (measurable_phaseObs b hb c hc hcm).comp hX0
  memLp_coord := fun j => by
    rcases j with γ | γ
    · simp only [sampleObs, phaseObs_inl]
      exact (hc2 γ).mul_const _
    · simp only [sampleObs, phaseObs_inr]
      exact memLp_const _
  summable := by
    refine Summable.sum _ ?_ ?_
    · refine hsum.congr fun γ => ?_
      simp [Function.comp, coordL2_sampleObs_inl]
    · refine summable_zero.congr fun γ => ?_
      simp [Function.comp, coordL2_sampleObs_inr]

omit [MeasurableSpace 𝓧] [IsProbabilityMeasure P] in
include hb in
/-- A Cauchy envelope `‖c_γ(X)‖_{L²} ≤ M R^{−|γ|}` with `b < R` gives the certificate. -/
theorem summable_of_cauchy_envelope {R M : ℝ} (hR : 0 < R) (hbR : b < R)
    (henv : ∀ γ : Fin d → ℕ, Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P) ≤ M * R⁻¹ ^ (∑ i, γ i)) :
    Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P) := by
  have hgeom := (summable_prodGeom d (q := fun _ => b / R) (fun _ => (div_pos hb hR).le)
    (fun _ => (div_lt_one hR).2 hbR)).mul_left M
  refine Summable.of_nonneg_of_le
    (fun γ => mul_nonneg (pow_nonneg hb.le _) (Real.sqrt_nonneg _)) (fun γ => ?_) hgeom
  calc b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P)
      ≤ b ^ (∑ i, γ i) * (M * R⁻¹ ^ (∑ i, γ i)) :=
        mul_le_mul_of_nonneg_left (henv γ) (pow_nonneg hb.le _)
    _ = M * ∏ i, (b / R) ^ γ i := by
        rw [Finset.prod_pow_eq_pow_sum, div_pow, div_eq_mul_inv, inv_pow]; ring

/-- The phase coordinates of the sample datum are the empirical Taylor coefficients `ξ_n`. -/
theorem xiCoord_sampleDatum (hcm : ∀ γ, Measurable fun x => c x γ) (hX0 : Measurable (X 0))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace d) (n : ℕ) (ω : Ω) (γ : Fin d → ℕ) :
    xiCoord (sampleDatum b hb c hc P X A n ω) γ =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        (c (X i ω) γ - ∫ ω, c (X 0 ω) γ ∂P) * b ^ (∑ i, γ i) + xiCoord A γ := by
  have hint := integrable_of_summableCoordL2 P
    (summableCoordL2_sampleObs b hb c hc P X hcm hX0 hc2 hsum)
  unfold xiCoord sampleDatum
  rw [lp.coeFn_add, Pi.add_apply, empiricalSum_apply hint]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sampleObs, phaseObs_inl]
  rw [integral_mul_const]
  ring

/-- The amplitude coordinates of the sample datum are those of `A`. -/
theorem etaCoord_sampleDatum (hcm : ∀ γ, Measurable fun x => c x γ) (hX0 : Measurable (X 0))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace d) (n : ℕ) (ω : Ω) :
    etaCoord (sampleDatum b hb c hc P X A n ω) = etaCoord A := by
  have hint := integrable_of_summableCoordL2 P
    (summableCoordL2_sampleObs b hb c hc P X hcm hX0 hc2 hsum)
  funext γ
  unfold etaCoord sampleDatum
  rw [lp.coeFn_add, Pi.add_apply, empiricalSum_apply hint]
  simp [sampleObs, phaseObs_inr]

/-- **The sample datum converges in distribution on the data space**: to the translate by `A` of
the `ℓ¹` Gaussian limit `ν` of the phase observations. -/
theorem sampleDatum_tendstoInDistribution (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace d) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx d)),
      TendstoInDistribution (sampleDatum b hb c hc P X A) atTop (fun x => x + A) (fun _ => P)
        (ν : Measure (L1Seq (DataIdx d))) ∧
      (∀ F : Finset (DataIdx d), (ν : Measure (L1Seq (DataIdx d))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      ∀ F : Finset (DataIdx d), ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx d))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F) := by
  obtain ⟨ν, hν, hmarg, htails⟩ := clt_l1
    (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
    (iIndepFun_sampleObs b hb c hc P X hcm hXind) (identDistrib_sampleObs b hb c hc P X hcm hXid)
    (measurable_sampleObs b hb c hc X hcm hXm)
  refine ⟨ν, ?_, hmarg, htails⟩
  exact hν.continuous_comp (continuous_add_const A)

end Sample

end Grammar
