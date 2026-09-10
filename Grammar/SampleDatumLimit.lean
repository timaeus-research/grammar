import Grammar.SampleDatumMGF
import Grammar.UniformSpatialTwoTerm
import Grammar.StochasticTaylorTree

/-!
# The scaled sample-datum core converges in distribution; the single-chart annealed theorem

At the leading pair `(λ₀, m₀−1)` of a box chart (`λ₀ = min_i (h_i+1)/(2k_i)`, `m₀` its
multiplicity) every predecessor coefficient of the ordered normalised remainder vanishes
(`dataBoxCoeff_eq_zero_of_multCount_lt`, `predSum_leading`), so the ordered remainder is exactly
the scaled core `A_N Z_N(x) = Z_N(x)/(N^{−λ₀}(log N)^{m₀−1})` (`orderedRemainder_leading`,
`scaleA_mul_dataBoxIntegral_eq_orderedRemainder`). The stochastic Taylor tree (Headline XXXV, one
chart) therefore gives **the field limit for the sample datum**: `A_n Z_n(sampleDatum_n) ⇒
C_{λ₀,m₀−1}(Z + A)` with `Z ~ ν` the `ℓ¹` Gaussian limit of the phase observations
(`tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum`) — the deterministic remainder is
controlled uniformly on data balls and the sample data are tight in `ℓ¹`, so the growth `√n` of
their norm is immaterial.

Combined with Hoeffding (CLXI) and the population bound (CLX), this yields **the single-chart
annealed sample-datum theorem** (`tendsto_integral_scaled_sampleDatum_single`): for i.i.d.
samples with bounded chart phase observations and the `ℓ¹` CLT certificate,
`E[A_n(Z_n(sampleDatum_n) + Rem_n)] → E_ν[C_{λ₀,m₀−1}(Z + A)]` whenever `E|A_n Rem_n| → 0`, with
`p > 1`, `pβM₀² < 2`. The limiting coefficient is integrable under `ν`.

Non-claims: the identification of `E_ν[C_{λ₀,m₀−1}(Z + A)]` with a Gaussian compact-base
functional expectation is not made here; several charts require joint convergence of the chart
data (the stacked sample datum) and are not assembled here.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Grammar

open CoeffFamily

section Deterministic

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)

include hk hβ hb hmin hatt in
/-- At the leading exponent the coefficients above degree `m₀ − 1` vanish (general box radius). -/
theorem dataBoxCoeff_eq_zero_of_multCount_lt (x : DataSpace (n + 1)) {j : ℕ}
    (hj : multCount (ratioExp h k) l - 1 < j) : dataBoxCoeff n h k β b x l j = 0 := by
  rw [dataBoxCoeff_eq n h k β hb x l j]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  rw [Finset.mem_Ico] at hq
  have hqn : q ≤ n := by omega
  have h0 : familySpectralCoeff n h k β (xiCoord x) (etaCoord x) l q = 0 := by
    rw [← dataBoxCoeff_one n h k β x l hqn]
    exact (dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).1 q (by omega)
  rw [h0, zero_mul, zero_mul]

include hk hβ hb hmin hatt in
/-- **The predecessor sum at the leading pair vanishes.** -/
theorem predSum_leading (x : DataSpace (n + 1)) (N : ℝ) :
    predSum n h k β b x l (multCount (ratioExp h k) l - 1) N = 0 := by
  classical
  unfold predSum
  refine Finset.sum_eq_zero fun p hp => ?_
  unfold predSet at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hprec⟩ := hp
  unfold expTerm
  rcases hprec with hlt | ⟨heq, hgt⟩
  · rw [dataBoxCoeff_eq_zero_of_lt_min n h k hk β hβ hb x hmin hlt, zero_mul]
  · rw [heq, dataBoxCoeff_eq_zero_of_multCount_lt n h k hk hβ hb hmin hatt x hgt, zero_mul]

include hk hβ hb hmin hatt in
/-- The ordered remainder at the leading pair is the scaled core. -/
theorem orderedRemainder_leading (x : DataSpace (n + 1)) (N : ℝ) :
    orderedRemainder n h k β b x l (multCount (ratioExp h k) l - 1) N =
      dataBoxIntegral n h k β N b x /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  unfold orderedRemainder
  rw [predSum_leading n h k hk hβ hb hmin hatt, sub_zero]

include hk hβ hb hmin hatt in
/-- `A_N Z_N(x)` is the ordered remainder at the leading pair, for `N ≥ 2`. -/
theorem scaleA_mul_dataBoxIntegral_eq_orderedRemainder (x : DataSpace (n + 1)) {N : ℕ}
    (hN : 2 ≤ N) :
    scaleA l (multCount (ratioExp h k) l) N * dataBoxIntegral n h k β N b x =
      orderedRemainder n h k β b x l (multCount (ratioExp h k) l - 1) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [orderedRemainder_leading n h k hk hβ hb hmin hatt, scaleA_of_two_le l _ hN,
    Real.rpow_neg hN0.le]
  have h1 : (N : ℝ) ^ l ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have h2 : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ (log_nat_pos hN).ne'
  field_simp

end Deterministic

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- Convergence in distribution along `atTop` is insensitive to finitely many initial terms. -/
theorem tendstoInDistribution_congr_eventually {X X' : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) μ') (hXX' : ∀ᶠ i in atTop, X i = X' i)
    (hX'm : ∀ i, AEMeasurable (X' i) μ) : TendstoInDistribution X' atTop Z (fun _ => μ) μ' :=
  ⟨hX'm, h.aemeasurable_limit, h.tendsto.congr' (hXX'.mono fun _ hi =>
    Subtype.ext (congrArg (fun f : Ω → ℝ => Measure.map f μ) hi))⟩

end Probability

section Sample

variable {n : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b)
  (c : 𝓧 → CoeffFamily (n + 1)) (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)
variable (h k : Fin (n + 1) → ℕ)

/-- **The field limit for the sample datum**: `A_n Z_n(sampleDatum_n) ⇒ C_{λ₀,m₀−1}(Z + A)`
with `Z ~ ν` the `ℓ¹` Gaussian limit of the phase observations, at the chart's own leading pair. -/
theorem tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace (n + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      TendstoInDistribution (fun i ω => scaleA (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k)) i *
          dataBoxIntegral n h k β i b (sampleDatum b hb c hc P X A i ω)) atTop
        (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)) (fun _ => P)
        (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
  obtain ⟨ν, hν, hmarg, -⟩ :=
    sampleDatum_tendstoInDistribution b hb c hc P X hcm hXm hXind hXid hc2 hsum A
  refine ⟨ν, hmarg, ?_⟩
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

/-- **The single-chart annealed sample-datum theorem**: for i.i.d. samples with bounded chart
phase observations (`‖phaseObs(X_i)‖_{ℓ¹} ≤ M₀`, `pβM₀² < 2`, `p > 1`), the `ℓ¹` CLT certificate,
a zero-phase amplitude datum of amplitude mass `≤ M`, and `E|A_n Rem_n| → 0`,
`E[A_n(Z_n(sampleDatum_n) + Rem_n)] → E_ν[C_{λ₀,m₀−1}(Z + A)]`, the limiting coefficient being
integrable under the `ℓ¹` Gaussian limit `ν`. -/
theorem tendsto_integral_scaled_sampleDatum_single (hk : ∀ i, 0 < k i) {β p M M₀ : ℝ}
    (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * M₀ ^ 2 < 2) (hM : 0 ≤ M) (hM0 : 0 ≤ M₀)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hobs : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      Integrable (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
          (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
        (𝓝 (∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
            ∂(ν : Measure (L1Seq (DataIdx (n + 1)))))) := by
  obtain ⟨ν, hmarg, hcore⟩ := tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum b hb c hc P
    X h k hk hβ hcm hXm hXind hXid hc2 hsum A
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
  obtain ⟨hint, htend⟩ := tendsto_integral_scaled_assembly_sampleDatum P n (fun _ : Fin 1 => h)
    (fun _ => k) (fun _ => b) X (fun _ => hk) hβ hp hpc hM hM0 (fun _ => hb)
    (fun _ => Or.inr ⟨rfl, le_rfl⟩) (fun _ => c) (fun _ => hc) (fun _ => hcm) hXm hXind hXid
    (fun _ => hobs) (fun _ => A) (fun _ => hA) (fun _ => hAM) hcore' hRint hrem
  refine ⟨ν, hmarg, hint, ?_⟩
  simpa only [e] using htend

end Sample

end Grammar
