import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Grammar.SamplingCompatibility
import Grammar.AnnealedRemainder
import Grammar.LeadingCoeffGaussianMoment

/-!
# Uniform sub-Gaussian empirical phase bounds (Astra #62 unit 3)

The full-box exponential-moment bound of the sample phase field was obtained in `SampleDatumMGF`
for **bounded** phase observations by Hoeffding's lemma (proxy `M₀²`). Here the boundedness is
replaced by the scalar, full-box **sub-Gaussian hypothesis** on the centred phase evaluations of
a single observation: with `Q_u = ξ_{Y₀}(u) − E ξ_{Y₀}(u)`,

  `E e^{tQ_u} ≤ e^{κt²/2}` for all `t ∈ ℝ` and all `u ∈ [0,1]^d`   (`UniformSubgaussianPhase κ`).

* The normalised centred empirical phase `ξ_n(u) = n^{−1/2}∑_{i<n} Q_u(X_i)` has the **same**
  proxy `κ` for every `n > 0` (`hasSubgaussianMGF_empiricalPhase`: Mathlib's
  `HasSubgaussianMGF.sum_of_iIndepFun` and `const_mul`, with `((√n)⁻¹)² · nκ = κ`), hence the
  full-box exponential-moment bound `E e^{tξ_n(u)} ≤ e^{κt²/2}` uniformly in `n` and `u`
  (`lintegral_exp_phase_sampleDatum_le_of_subgaussian`) — the hypothesis form of the certified-core
  expectation assembly.
* **The sharp variance bound** `Var[Q] ≤ κ` for a sub-Gaussian variable
  (`variance_le_of_hasSubgaussianMGF`: `x² ≤ e^{tx} + e^{−tx} − 2` over `t²`, the two-sided MGF
  bound, and `t → 0⁺`), so the face variances satisfy `σ²(v) ≤ κ`
  (`phaseVar_le_of_uniformSubgaussian`) — the threshold `βκ < 2` of the Gaussian first moment is
  the advertised one.
* Bounded observations satisfy the hypothesis with `κ = M₀²` (Hoeffding,
  `uniformSubgaussianPhase_of_bounded`), so the bounded theory is the special case.

Non-claims: no sub-Gaussian bound for the `ℓ¹` norm of the observations; no `ℓ¹` CLT from the scalar
evaluation bounds (the coordinate certificate stays); no independence across face points; the
external remainder hypothesis of the annealed theorem is untouched.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Grammar

open CoeffFamily

section Basic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `y² ≤ e^y + e^{−y} − 2`, from `|y/2| ≤ sinh |y/2|`. -/
theorem sq_le_exp_add_exp_neg_sub_two (y : ℝ) : y ^ 2 ≤ Real.exp y + Real.exp (-y) - 2 := by
  have hs : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    rw [sq_le_sq, Real.abs_sinh]
    exact Real.self_le_sinh_iff.2 (abs_nonneg _)
  rw [Real.sinh_eq] at hs
  have h1 : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (-(y / 2)) * Real.exp (-(y / 2)) = Real.exp (-y) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [hs, h1, h2, h3]

/-- A sub-Gaussian bound with proxy `c` is one with any larger proxy. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.of_le_proxy {X : Ω → ℝ} {c c' : ℝ≥0}
    (h : HasSubgaussianMGF X c P) (hcc : c ≤ c') : HasSubgaussianMGF X c' P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.2 (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcc) (sq_nonneg t)) two_pos.le))

/-- **The sharp variance bound of a sub-Gaussian variable**: `Var[X] ≤ E[X²] ≤ c`. -/
theorem variance_le_of_hasSubgaussianMGF [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c P) : Var[X; P] ≤ c := by
  have hX2 : MemLp X 2 P := h.memLp 2
  have hX2i : Integrable (fun ω => X ω ^ 2) P := (memLp_two_iff_integrable_sq hX2.1).1 hX2
  have key : ∀ t : ℝ, 0 < t → ∫ ω, X ω ^ 2 ∂P ≤ c * Real.exp (c * t ^ 2 / 2) := by
    intro t ht
    have hint1 : Integrable (fun ω => Real.exp (t * X ω)) P := h.integrable_exp_mul t
    have hint2 : Integrable (fun ω => Real.exp (-t * X ω)) P := h.integrable_exp_mul (-t)
    have hpt : ∀ ω, X ω ^ 2 ≤ (Real.exp (t * X ω) + Real.exp (-t * X ω) - 2) / t ^ 2 := by
      intro ω
      rw [le_div_iff₀ (by positivity), neg_mul]
      calc X ω ^ 2 * t ^ 2 = (t * X ω) ^ 2 := by ring
        _ ≤ _ := sq_le_exp_add_exp_neg_sub_two (t * X ω)
    have h1 : ∫ ω, X ω ^ 2 ∂P ≤
        ∫ ω, (Real.exp (t * X ω) + Real.exp (-t * X ω) - 2) / t ^ 2 ∂P :=
      integral_mono hX2i (((hint1.add hint2).sub (integrable_const 2)).div_const _) hpt
    have hi12 : Integrable (fun ω => Real.exp (t * X ω) + Real.exp (-t * X ω)) P :=
      hint1.add hint2
    rw [integral_div, integral_sub hi12 (integrable_const _), integral_add hint1 hint2,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h1
    have hm1 : ∫ ω, Real.exp (t * X ω) ∂P ≤ Real.exp (c * t ^ 2 / 2) := h.mgf_le t
    have hm2 : ∫ ω, Real.exp (-t * X ω) ∂P ≤ Real.exp (c * t ^ 2 / 2) := by
      have := h.mgf_le (-t)
      rwa [neg_sq] at this
    have hs : Real.exp (c * t ^ 2 / 2) - 1 ≤ c * t ^ 2 / 2 * Real.exp (c * t ^ 2 / 2) := by
      have h0 := Real.add_one_le_exp (-(c * t ^ 2 / 2))
      have hpos := Real.exp_pos (c * t ^ 2 / 2)
      have hmul : Real.exp (-(c * t ^ 2 / 2)) * Real.exp (c * t ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith
    have ht2 : 0 < t ^ 2 := by positivity
    calc ∫ ω, X ω ^ 2 ∂P
        ≤ (∫ ω, Real.exp (t * X ω) ∂P + ∫ ω, Real.exp (-t * X ω) ∂P - 2) / t ^ 2 := h1
      _ ≤ (2 * Real.exp (c * t ^ 2 / 2) - 2) / t ^ 2 := by
          gcongr
          linarith
      _ ≤ c * Real.exp (c * t ^ 2 / 2) := by
          rw [div_le_iff₀ ht2]
          nlinarith [hs]
  have hV : Var[X; P] ≤ ∫ ω, X ω ^ 2 ∂P := by
    rw [variance_eq_sub hX2]
    simp only [Pi.pow_apply]
    linarith [sq_nonneg (∫ ω, X ω ∂P)]
  have hc : Tendsto (fun t : ℝ => (c : ℝ) * Real.exp (c * t ^ 2 / 2)) (𝓝 0)
      (𝓝 ((c : ℝ) * Real.exp (c * (0 : ℝ) ^ 2 / 2))) :=
    (by fun_prop : Continuous fun t : ℝ => (c : ℝ) * Real.exp (c * t ^ 2 / 2)).tendsto 0
  have hlim : Tendsto (fun t : ℝ => (c : ℝ) * Real.exp (c * t ^ 2 / 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (c : ℝ)) := by
    simpa using hc.mono_left nhdsWithin_le_nhds
  exact hV.trans (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => key t ht))

end Basic

section Sample

variable {d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

/-- The centred phase evaluation of the `i`-th observation,
`Q_u(X_i) = ξ_{Y_i}(u) − E ξ_{Y₀}(u)`. -/
noncomputable def centredPhaseObs (u : Fin d → ℝ) (hu : u ∈ closedCube d) (i : ℕ) (ω : Ω) : ℝ :=
  phaseEvalCLM u hu (sampleObs b hb c hc X i ω) -
    ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω') ∂P

/-- **The uniform full-box sub-Gaussian hypothesis**: `E e^{tQ_u} ≤ e^{κt²/2}` for every `t` and
every `u` in the closed unit cube. -/
def UniformSubgaussianPhase (κ : ℝ≥0) : Prop :=
  ∀ (u : Fin d → ℝ) (hu : u ∈ closedCube d),
    HasSubgaussianMGF (centredPhaseObs b hb c hc P X u hu 0) κ P

/-- **Bounded observations are uniformly sub-Gaussian with proxy `M₀²`** (Hoeffding's lemma). -/
theorem uniformSubgaussianPhase_of_bounded (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {M₀ : ℝ} (hM0 : 0 ≤ M₀) (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) :
    UniformSubgaussianPhase b hb c hc P X ⟨M₀ ^ 2, sq_nonneg _⟩ := by
  intro u hu
  have hmeas : AEMeasurable (fun ω => phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω)) P :=
    ((phaseEvalCLM u hu).continuous.measurable.comp
      (measurable_sampleObs b hb c hc X hcm hXm 0)).aemeasurable
  have hIcc : ∀ᵐ ω ∂P, phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω) ∈ Icc (-M₀) M₀ :=
    Filter.Eventually.of_forall fun ω =>
      abs_le.1 ((abs_phaseEvalCLM_le u hu _).trans (hM (X 0 ω)))
  have h := hasSubgaussianMGF_of_mem_Icc hmeas hIcc
  unfold centredPhaseObs
  refine ⟨h.integrable_exp_mul, fun t => ?_⟩
  change mgf _ P t ≤ Real.exp (M₀ ^ 2 * t ^ 2 / 2)
  refine (h.mgf_le t).trans (le_of_eq ?_)
  congr 1
  push_cast
  rw [Real.norm_eq_abs, sub_neg_eq_add, ← two_mul, abs_mul, abs_two, abs_of_nonneg hM0]
  ring

omit [IsProbabilityMeasure P] in
/-- **The normalised centred empirical phase has the same sub-Gaussian proxy**: for `n > 0`,
`ξ_n(u) = n^{−1/2}∑_{i<n} Q_u(X_i)` is sub-Gaussian with proxy `κ`. -/
theorem hasSubgaussianMGF_empiricalPhase (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) {n : ℕ} (hn : 0 < n) (u : Fin d → ℝ)
    (hu : u ∈ closedCube d) :
    HasSubgaussianMGF (fun ω => evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u) κ P := by
  have e : (fun ω => evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u) =
      fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, centredPhaseObs b hb c hc P X u hu i ω := by
    funext ω
    exact phaseEval_sampleDatum_of_integrable b hb c hc P X hint A hA n ω hu
  rw [e]
  have hi : ∀ i, HasSubgaussianMGF (centredPhaseObs b hb c hc P X u hu i) κ P := fun i =>
    (hκ u hu).congr_identDistrib (((identDistrib_sampleObs b hb c hc P X hcm hXid i).comp
      ((phaseEvalCLM u hu).continuous.measurable.sub_const _)).symm)
  have hind : iIndepFun (fun i => centredPhaseObs b hb c hc P X u hu i) P :=
    (iIndepFun_sampleObs b hb c hc P X hcm hXind).comp
      (fun _ x => phaseEvalCLM u hu x - ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω') ∂P)
      fun _ => (phaseEvalCLM u hu).continuous.measurable.sub_const _
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind (c := fun _ => κ) (s := Finset.range n)
    fun i _ => hi i
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun t => ?_, fun t => ?_⟩
  · refine (hsum.integrable_exp_mul (t * (Real.sqrt n)⁻¹)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [mul_assoc]
  · rw [mgf_const_mul]
    refine (hsum.mgf_le _).trans (le_of_eq ?_)
    congr 1
    push_cast
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt hn'.le]
    field_simp

/-- **The full-box exponential-moment bound for the sample datum under the sub-Gaussian
hypothesis**: `E e^{tξ_n(u)} ≤ e^{κt²/2}` for every `n`, every `u ∈ [0,1]^d` and every `t`. -/
theorem lintegral_exp_phase_sampleDatum_le_of_subgaussian (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ) {u : Fin d → ℝ} (hu : u ∈ closedCube d)
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u)) ∂P ≤
      ENNReal.ofReal (Real.exp (κ * t ^ 2 / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp_rw [phaseEval_sampleDatum_of_integrable b hb c hc P X hint A hA 0 _ hu]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, one_mul]
    exact ENNReal.one_le_ofReal.2 (Real.one_le_exp (by positivity))
  · exact lintegral_ofReal_exp_le_of_hasSubgaussianMGF
      (hasSubgaussianMGF_empiricalPhase b hb c hc P X hcm hXind hXid hκ hint A hA hn u hu) t

/-- **The face variances are bounded by the proxy**: `σ²(v) = Var[ξ_{Y₀}(v)] ≤ κ`. -/
theorem phaseVar_le_of_uniformSubgaussian (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {κ : ℝ≥0} (hκ : UniformSubgaussianPhase b hb c hc P X κ)
    {v : Fin d → ℝ} (hv : v ∈ closedCube d) : phaseVar b hb c hc P X v ≤ κ := by
  have h := variance_le_of_hasSubgaussianMGF (hκ v hv)
  unfold centredPhaseObs at h
  have hm : AEStronglyMeasurable (fun ω => phaseEvalCLM v hv (sampleObs b hb c hc X 0 ω)) P :=
    ((phaseEvalCLM v hv).continuous.measurable.comp
      (measurable_sampleObs b hb c hc X hcm hXm 0)).aestronglyMeasurable
  rw [variance_sub_const hm] at h
  unfold phaseVar
  exact h

end Sample

end Grammar
