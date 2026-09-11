import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Grammar.EffectiveTemperature

/-!
# Closure endpoints for the empirical chain (Astra #66 units 3 and 5)

Two interface obligations identified by Astra's closure audit, and one publication-facing endpoint.

* **Banach `L²` from the coordinate certificate.** The `ℓ¹` CLT certificate `∑_j ‖Y_j‖_{L²} < ∞`
  implies `Y ∈ L²(P; ℓ¹)`: finite-sum Minkowski on the truncations
  (`eLpNorm_truncate_le`) and Fatou along an exhaustion (`eLpNorm_lim_le_liminf_eLpNorm`) give
  `‖‖Y‖_{ℓ¹}‖_{L²} ≤ ∑_j ‖Y_j‖_{L²}` (`eLpNorm_le_tsum_coordL2`, `memLp_two_of_summableCoordL2`).
  The Banach `L²` hypothesis of the sub-Gaussian first-moment theorems is therefore not an
  additional assumption on the sampling law (`memLp_two_sampleObs_of_certificate`).
* **The tail certificate reaches the first-moment theorem.** The scaled-core limit of CLXII is
  restated with the `ℓ¹` limit's tail certificate `htail` exposed
  (`tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail`), so the Gaussian measure
  delivered by the annealed assembly is the one the first-moment identification needs — no
  identification of two existential witnesses.
* **The endpoint** (`annealed_sampleDatum_single_identified`): for one certified box chart and
  i.i.d. samples with the coordinate certificate, a uniform full-box sub-Gaussian proxy `κ`
  (`p > 1`, `pβκ < 2`), a zero-phase amplitude datum and `E|A_n Rem_n| → 0`, there is one
  probability measure `ν` on the data space with Gaussian finite coordinate marginals and the tail
  certificate such that `E[A_n(Z_n(D_n) + Rem_n)] → E_ν[C^b_{λ₀,m₀−1}(Z + A)]` **and** this limit
  equals the covariance-modified face integral; with a.e. constant face variance `v₀` it is the
  zero-phase population coefficient at `β(1 − βv₀/2)`
  (`annealed_sampleDatum_single_effectiveTemperature`). Since `βκ < 2` already yields a `p > 1`
  with `pβκ < 2` (`exists_p_gt_one_of_lt_two`), the `p`-hypothesis is not an extra numerical
  restriction (`annealed_sampleDatum_single_identified_of_lt_two`).

Non-claims: the model interfaces of CLXXXI (coefficient evaluation, population mean, loss
factorisation), the external remainder, and the sub-Gaussian proxy remain hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

/-! ### Banach `L²` from the coordinate certificate -/

section BanachL2

variable {ι : Type*} [Countable ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [Countable ι] [DecidableEq ι] [IsProbabilityMeasure P] in
/-- The `L²` seminorm of a coordinate is the coordinate `L²` norm of the certificate. -/
theorem eLpNorm_coord_eq {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (j : ι) :
    eLpNorm (fun ω => Y ω j) 2 P = ENNReal.ofReal (coordL2 P Y j) := by
  rw [(hY.memLp_coord j).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [coordL2, Real.sqrt_eq_rpow, one_div]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [sq_abs]

/-- Finite-sum Minkowski: `‖‖T_F Y‖‖_{L²} ≤ ∑_{j ∈ F} ‖Y_j‖_{L²}`. -/
theorem eLpNorm_truncate_le {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (F : Finset ι) :
    eLpNorm (fun ω => truncate F (Y ω)) 2 P ≤ ∑ j ∈ F, ENNReal.ofReal (coordL2 P Y j) := by
  have e : (fun ω => truncate F (Y ω)) = ∑ j ∈ F, fun ω => singleCLM (j : ι) (Y ω j) := by
    funext ω
    simp [truncate, Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le (fun j _ => ?_) (by norm_num)).trans (Finset.sum_le_sum fun j _ => ?_)
  · exact ((singleCLM j).continuous.measurable.comp
      (SummableCoordL2.coord_measurable P hY j)).aestronglyMeasurable
  · rw [← eLpNorm_coord_eq hY j]
    refine le_of_eq (eLpNorm_congr_norm_ae (Eventually.of_forall fun ω => ?_))
    simp [singleCLM, lp.norm_single]

omit [DecidableEq ι] in
/-- **Banach `L²` from the coordinate certificate**: `‖‖Y‖_{ℓ¹}‖_{L²} ≤ ∑_j ‖Y_j‖_{L²}`
(Minkowski on the truncations and Fatou along an exhaustion). -/
theorem eLpNorm_le_tsum_coordL2 {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
    eLpNorm Y 2 P ≤ ENNReal.ofReal (∑' j, coordL2 P Y j) := by
  classical
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  have hlim := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := P) (p := 2)
    (f := fun k ω => truncate (F k) (Y ω))
    (fun k => ((truncate (F k)).continuous.measurable.comp hY.measurable).aestronglyMeasurable) Y
    (Eventually.of_forall fun ω => tendsto_truncate hF hcov (Y ω))
  refine hlim.trans
    (Filter.liminf_le_of_frequently_le' (Eventually.of_forall fun k => ?_).frequently)
  refine (eLpNorm_truncate_le hY (F k)).trans ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => coordL2_nonneg P Y j) hY.summable]
  exact ENNReal.sum_le_tsum _

omit [DecidableEq ι] in
/-- The coordinate certificate gives `Y ∈ L²(P; ℓ¹)`. -/
theorem memLp_two_of_summableCoordL2 {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
    MemLp Y 2 P :=
  ⟨hY.measurable.aestronglyMeasurable,
    (eLpNorm_le_tsum_coordL2 hY).trans_lt ENNReal.ofReal_lt_top⟩

end BanachL2

/-- `βκ < 2` yields a `p > 1` with `pβκ < 2`: the `p`-hypothesis of the annealed theorems is no
extra numerical restriction. -/
theorem exists_p_gt_one_of_lt_two {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2) :
    ∃ p : ℝ, 1 < p ∧ p * s < 2 := by
  refine ⟨1 + (2 - s) / (2 * (s + 1)), ?_, ?_⟩
  · have : 0 < (2 - s) / (2 * (s + 1)) := div_pos (by linarith) (by positivity)
    linarith
  · have h1 : (2 - s) / (2 * (s + 1)) * s ≤ (2 - s) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-! ### The endpoint -/

section Endpoint

variable {n : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b)
  (c : 𝓧 → CoeffFamily (n + 1)) (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)
variable (h k : Fin (n + 1) → ℕ)

/-- The coordinate certificate gives the phase observations in `L²(P; ℓ¹)`. -/
theorem memLp_two_sampleObs_of_certificate (hcm : ∀ γ, Measurable fun x => c x γ)
    (hX0 : Measurable (X 0)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P)) :
    MemLp (sampleObs b hb c hc X 0) 2 P :=
  memLp_two_of_summableCoordL2 (summableCoordL2_sampleObs b hb c hc P X hcm hX0 hc2 hsum)

/-- **The field limit for the sample datum with the tail certificate exposed**: the `ℓ¹`
Gaussian limit `ν` of CLXII carries both the Gaussian finite coordinate marginals and the tail
bound `∫‖x − T_F x‖dν ≤ ∑_{j∉F} σ_j`. -/
theorem tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace (n + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      (∀ F : Finset (DataIdx (n + 1)),
        ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
          ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F)) ∧
      TendstoInDistribution (fun i ω => scaleA (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k)) i *
          dataBoxIntegral n h k β i b (sampleDatum b hb c hc P X A i ω)) atTop
        (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)) (fun _ => P)
        (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
  obtain ⟨ν, hν, hmarg, htail⟩ :=
    sampleDatum_tendstoInDistribution b hb c hc P X hcm hXm hXind hXid hc2 hsum A
  refine ⟨ν, hmarg, htail, ?_⟩
  have hmin := minRatio_le h k
  have hatt := exists_ratioExp_eq_minRatio h k
  have hμ : ∃ m' : ℕ, minRatio h k = (m' : ℝ) / latticeQ k := exists_latticeQ_eq n h k hk hatt
  have hj : multCount (ratioExp h k) (minRatio h k) - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) (minRatio h k)
    omega
  have hR := tendstoInDistribution_orderedRemainder n h k hk β hβ hb hμ hj
    (sampleDatum b hb c hc P X A) (measurable_sampleDatum P b hb c hc X hcm hXm hc2 hsum A)
    (fun x => x + A) hν (fun i : ℕ => (i : ℝ)) (fun i => Nat.cast_nonneg i)
    tendsto_natCast_atTop_atTop
  refine tendstoInDistribution_congr_eventually hR ?_ fun i => ?_
  · filter_upwards [eventually_ge_atTop 2] with i hi
    funext ω
    exact (scaleA_mul_dataBoxIntegral_eq_orderedRemainder n h k hk hβ hb hmin hatt _ hi).symm
  · exact ((measurable_dataBoxIntegral n h k hβ.le (Nat.cast_nonneg i) hb).comp
      (measurable_sampleDatum P b hb c hc X hcm hXm hc2 hsum A i)).aemeasurable.const_mul _

/-- **The single-chart annealed sample-datum theorem, identified (the endpoint)**: one measure
`ν` on the data space with Gaussian finite coordinate marginals and the tail certificate, such
that `E[A_n(Z_n(D_n) + Rem_n)] → E_ν[C^b_{λ₀,m₀−1}(Z + A)]` and
`E_ν[C^b_{λ₀,m₀−1}(Z + A)] = b^{|h|+d} c^{−λ₀} K_face (Γ(λ₀)/2) ∫ η_A(π u)
(β(1 − βσ²(π u)/2))^{−λ₀} w(u) du / 2^{m₀−1}`. Hypotheses: i.i.d. samples with the coordinate
certificate, a uniform full-box sub-Gaussian proxy `κ` with `p > 1`, `pβκ < 2`, a zero-phase
amplitude datum of amplitude mass `≤ M`, and `E|A_n Rem_n| → 0`. -/
theorem annealed_sampleDatum_single_identified (hk : ∀ i, 0 < k i)
    {β p M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * κ < 2) (hM : 0 ≤ M)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      (∀ F : Finset (DataIdx (n + 1)),
        ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
          ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F)) ∧
      Integrable (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
          (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
        (𝓝 (∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
            ∂(ν : Measure (L1Seq (DataIdx (n + 1)))))) ∧
      ∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
          ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-(minRatio h k)) *
          (1 / (((multCount (ratioExp h k) (minRatio h k) - 1).factorial : ℝ) *
              ∏ i, if ratioExp h k i = minRatio h k then (k i : ℝ) else 1) *
            (∫ u in unitBox (n + 1), faceWeight h k (minRatio h k) (dataAmplitude A) u *
              (Real.Gamma (minRatio h k) * (β * (1 - β * phaseVar b hb c hc P X
                (cubeClamp (faceProj h k (minRatio h k) u)) / 2)) ^ (-(minRatio h k)) / 2)) /
            2 ^ (multCount (ratioExp h k) (minRatio h k) - 1)) := by
  obtain ⟨ν, hmarg, htail, hcore⟩ := tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail
    b hb c hc P X h k hk hβ hcm hXm hXind hXid hc2 hsum A
  have hint : Integrable (sampleObs b hb c hc X 0) P :=
    integrable_of_summableCoordL2 P (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
  have hM2 : MemLp (sampleObs b hb c hc X 0) 2 P :=
    memLp_two_sampleObs_of_certificate b hb c hc P X hcm (hXm 0) hc2 hsum
  have hβκ : β * κ < 2 := by
    have h0 : 0 ≤ β * κ := mul_nonneg hβ.le κ.2
    have : β * κ ≤ p * β * κ := by nlinarith
    linarith
  have e : ∀ m ω, coreSum n (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) β (fun m => (m : ℝ))
      (fun _ m => sampleDatum b hb c hc P X A m) m ω =
      dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) := fun m ω => by
    simp [coreSum]
  have hcore' : TendstoInDistribution (fun m ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
        coreSum n (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) β (fun m => (m : ℝ))
          (fun _ m => sampleDatum b hb c hc P X A m) m ω) atTop
      (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1)) (fun _ => P)
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
    simpa only [e] using hcore
  obtain ⟨hint', htend⟩ := tendsto_integral_scaled_assembly_sampleDatum_subgaussian P X n
    (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) (fun _ => hk) hβ hp hpc hM (fun _ => hb)
    (fun _ => Or.inr ⟨rfl, le_rfl⟩) (fun _ => c) (fun _ => hc) (fun _ => hcm) hXm hXind hXid
    (fun _ => hint) (fun _ => hκ) (fun _ => A) (fun _ => hA) (fun _ => hAM) hcore' hRint hrem
  have hid := integral_dataBoxCoeff_leading_eq_subgaussian n h k hk hβ hb (minRatio_le h k)
    (exists_ratioExp_eq_minRatio h k) c hc P X hcm hXm hc2 hsum hM2 hκ hβκ hmarg htail A hA
  refine ⟨ν, hmarg, htail, hint', ?_, hid.2⟩
  simpa only [e] using htend

/-- **The endpoint at constant face variance**: under the hypotheses of
`annealed_sampleDatum_single_identified`, if `σ²(π u) = v₀` for almost every `u` in the box
(`βv₀ < 2`), the annealed limit is the zero-phase population coefficient at the effective
temperature `β(1 − βv₀/2)`. -/
theorem annealed_sampleDatum_single_effectiveTemperature (hk : ∀ i, 0 < k i)
    {β p M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * κ < 2) (hM : 0 ≤ M)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0))
    {v₀ : ℝ} (hv₀ : β * v₀ < 2)
    (hconst : ∀ᵐ u ∂volume, u ∈ unitBox (n + 1) →
      phaseVar b hb c hc P X (cubeClamp (faceProj h k (minRatio h k) u)) = v₀) :
    Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
        (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
      (𝓝 (dataBoxCoeff n h k (β * (1 - β * v₀ / 2)) b A (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))) := by
  obtain ⟨ν, hmarg, htail, -, htend, -⟩ := annealed_sampleDatum_single_identified b hb c hc P X
    h k hk hβ hp hpc hM hcm hXm hXind hXid hc2 hsum hκ A hA hAM hRint hrem
  have hM2 : MemLp (sampleObs b hb c hc X 0) 2 P :=
    memLp_two_sampleObs_of_certificate b hb c hc P X hcm (hXm 0) hc2 hsum
  have hβκ : β * κ < 2 := by
    have h0 : 0 ≤ β * κ := mul_nonneg hβ.le κ.2
    have : β * κ ≤ p * β * κ := by nlinarith
    linarith
  rw [integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance n h k hk hβ hb
    (minRatio_le h k) (exists_ratioExp_eq_minRatio h k) c hc P X hcm hXm hc2 hsum hM2 hκ hβκ
    hmarg htail A hA hv₀ hconst] at htend
  exact htend

/-- The endpoint with `βκ < 2` alone: the `p` of the `L^p` argument is chosen internally. -/
theorem annealed_sampleDatum_single_identified_of_lt_two (hk : ∀ i, 0 < k i)
    {β M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hβκ : β * κ < 2) (hM : 0 ≤ M)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      Integrable (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
          (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
        (𝓝 (∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
            ∂(ν : Measure (L1Seq (DataIdx (n + 1)))))) ∧
      ∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
          ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-(minRatio h k)) *
          (1 / (((multCount (ratioExp h k) (minRatio h k) - 1).factorial : ℝ) *
              ∏ i, if ratioExp h k i = minRatio h k then (k i : ℝ) else 1) *
            (∫ u in unitBox (n + 1), faceWeight h k (minRatio h k) (dataAmplitude A) u *
              (Real.Gamma (minRatio h k) * (β * (1 - β * phaseVar b hb c hc P X
                (cubeClamp (faceProj h k (minRatio h k) u)) / 2)) ^ (-(minRatio h k)) / 2)) /
            2 ^ (multCount (ratioExp h k) (minRatio h k) - 1)) := by
  obtain ⟨p, hp, hpc⟩ := exists_p_gt_one_of_lt_two (mul_nonneg hβ.le κ.2) hβκ
  obtain ⟨ν, -, -, hint, htend, hid⟩ := annealed_sampleDatum_single_identified b hb c hc P X h k
    hk hβ hp (by rw [mul_assoc]; exact hpc) hM hcm hXm hXind hXid hc2 hsum hκ A hA hAM hRint hrem
  exact ⟨ν, hint, htend, hid⟩

end Endpoint

end Grammar
