import Grammar.SampleDatumMGF
import Grammar.SamplingIdentity
import Grammar.AnalyticCertificate

/-!
# Sampling/core compatibility: the sample datum realises the paper's `ξ_n` exactly

Astra #62 unit 1 (the release gate of the companion note). The sample datum
`sampleDatum A n ω = n^{−1/2} ∑_{i<n} (Y_i − E Y_0) + A` of i.i.d. phase observations
`Y_i = phaseObs (X_i)` is compared, **before any limit or expectation**, with the sampling identity
of `SamplingIdentity.lean`: in the standard form `f(x,v) = φ(v) a(x,v)`, `E a(X,v) = φ(v)`,

* evaluation commutes with the Bochner mean (`phaseEvalCLM_integral`);
* **exact centred evaluation**: for a zero-phase amplitude datum `A`,
  `ξ_n(u) = n^{−1/2} ∑_{i<n} (ξ_{Y_i}(u) − E ξ_{Y_0}(u))` (`phaseEval_sampleDatum_of_integrable`,
  only integrability of the observations is needed);
* **amplitude unchanged**: `η(sampleDatum) = η(A)` (`etaCoord_sampleDatum_of_integrable`);
* **the sign**: when the coefficient family `c x` is the Taylor family of `−a(x,·)` at the box
  point `b·u` (`evalF (c x) (b•u) = −a x (b•u)`) and `E a(X,b·u) = φ(b·u)`, the phase of the
  sample datum is `ξ_n(u) = −ζ_n(b·u)`, *minus* the centred empirical process of the coefficient
  (`evalF_xiCoord_sampleDatum_eq_neg_zetaEmp`), and the sampling exponent is the standard-integral
  exponent at the sample datum with `N = n`:
  `−β ∑_{i<n} f(X_i,b·u) = −βnφ² + β√n φ ξ_n(u)` (`sampling_exponent_eq_sampleDatum_phase`);
* **the certified box core**: in the monomial chart `φ(v) = v^k` the sampling integrand
  `e^{−β ∑_i f(X_i,v)}` is the phase factor of the box integrand at the sample datum
  (`exp_sampling_exponent_eq_core_factor`), so the certified core `Z(n; sampleDatum)` **is** the
  sampling integral `∫_{(0,b]^d} η_A(v) v^h e^{−β ∑_i f(X_i,v)} dv`
  (`dataBoxIntegral_sampleDatum_eq_sampling`).

The convention is therefore: `phaseObs` represents `−a` (equivalently `log p − log q`), the sample
phase is the paper's `ξ_n = −ζ_n`, and the population mean is carried by the deterministic
exponent `−βnφ²`, not by the amplitude datum `A` (which has zero phase). Non-claims: the
identification of an abstract coefficient family with a model's Taylor coefficients is the
hypothesis `hca`; nothing probabilistic is used beyond integrability.
-/

open MeasureTheory ProbabilityTheory Set

namespace Grammar

open CoeffFamily

section Evaluation

variable {d : ℕ}

/-- **Evaluation commutes with the Bochner mean.** -/
theorem phaseEvalCLM_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DataSpace d} (hY : Integrable Y P) (u : Fin d → ℝ) (hu : u ∈ closedCube d) :
    phaseEvalCLM u hu (∫ ω, Y ω ∂P) = ∫ ω, phaseEvalCLM u hu (Y ω) ∂P :=
  ((phaseEvalCLM u hu).integral_comp_comm hY).symm

/-- The two phase-evaluation functionals coincide. -/
theorem phaseEvalCLM_eq_phaseEval (u : Fin d → ℝ) (hu : u ∈ closedCube d) :
    phaseEvalCLM u hu = phaseEval hu := by
  ext x
  rw [phaseEvalCLM_apply, phaseEval_apply]
  rfl

variable {𝓧 : Type*} (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d) (hc : ∀ x, AbsSummableAt (c x) b)

/-- The phase evaluation of a phase observation is the coefficient family at the box point. -/
theorem phaseEvalCLM_phaseObs (x : 𝓧) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    phaseEvalCLM u hu (phaseObs b hb c hc x) = evalF (c x) (b • u) := by
  rw [phaseEvalCLM_eq_phaseEval, phaseEval_phaseObs]

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → 𝓧)

/-- **Amplitude unchanged** (integrable observations): the amplitude coordinates of the sample
datum are those of `A`. -/
theorem etaCoord_sampleDatum_of_integrable (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (n : ℕ) (ω : Ω) :
    etaCoord (sampleDatum b hb c hc P X A n ω) = etaCoord A := by
  funext γ
  unfold etaCoord sampleDatum
  rw [lp.coeFn_add, Pi.add_apply, empiricalSum_apply hint]
  simp [sampleObs, phaseObs_inr]

/-- **Exact centred evaluation** (integrable observations): for a zero-phase amplitude datum,
`ξ_n(u) = n^{−1/2} ∑_{i<n} (ξ_{Y_i}(u) − E ξ_{Y_0}(u))`. -/
theorem phaseEval_sampleDatum_of_integrable (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ) (ω : Ω) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) :
    evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (phaseEvalCLM u hu (sampleObs b hb c hc X i ω) -
        ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω') ∂P) := by
  rw [← phaseEvalCLM_apply u hu]
  unfold sampleDatum empiricalSum
  rw [map_add, map_smul, map_sum, phaseEvalCLM_apply u hu A, hA, evalF_zero, add_zero,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, ← ContinuousLinearMap.integral_comp_comm _ hint]

/-! ### The standard form: `ξ_n = −ζ_n` -/

variable (a : 𝓧 → (Fin d → ℝ) → ℝ) (φ : (Fin d → ℝ) → ℝ)

/-- **The sign of the fluctuation at the sample datum**: if `c x` is the Taylor family of
`−a(x,·)` at the box point `b·u` and `E a(X,b·u) = φ(b·u)`, then the phase of the sample datum is
`ξ_n(u) = −ζ_n(b·u)`, minus the centred empirical process of the coefficient. -/
theorem evalF_xiCoord_sampleDatum_eq_neg_zetaEmp (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ) (ω : Ω) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) (hca : ∀ x, evalF (c x) (b • u) = -a x (b • u))
    (hφ : ∫ ω', a (X 0 ω') (b • u) ∂P = φ (b • u)) :
    evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u =
      -zetaEmp n (fun i => a (X i ω) (b • u)) (φ (b • u)) := by
  rw [phaseEval_sampleDatum_of_integrable b hb c hc P X hint A hA n ω hu]
  unfold zetaEmp
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω') ∂P = -φ (b • u) := by
    rw [← hφ, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
    simp only [sampleObs, phaseEvalCLM_phaseObs, hca]
  rw [h0]
  simp only [sampleObs, phaseEvalCLM_phaseObs, hca]
  ring

/-- **`N = n` at the sample datum**: the sampling exponent `−β ∑_{i<n} φ a(X_i)` is the
standard-integral exponent `−βnφ² + β√n φ ξ_n(u)` evaluated at the phase of the sample datum. -/
theorem sampling_exponent_eq_sampleDatum_phase (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) {n : ℕ} (hn : 0 < n) (ω : Ω) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) (hca : ∀ x, evalF (c x) (b • u) = -a x (b • u))
    (hφ : ∫ ω', a (X 0 ω') (b • u) ∂P = φ (b • u)) (β : ℝ) :
    -β * ∑ i ∈ Finset.range n, φ (b • u) * a (X i ω) (b • u) =
      -β * n * φ (b • u) ^ 2 +
        β * Real.sqrt n * φ (b • u) * evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u := by
  rw [evalF_xiCoord_sampleDatum_eq_neg_zetaEmp b hb c hc P X a φ hint A hA n ω hu hca hφ]
  exact sampling_exponent_eq n hn _ _ β

end Evaluation

/-! ### The certified box core is the sampling integral -/

section Core

variable {n : ℕ} {𝓧 : Type*} (b : ℝ) (hb : 0 < b)
  (c : 𝓧 → CoeffFamily (n + 1)) (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → 𝓧)
  (a : 𝓧 → (Fin (n + 1) → ℝ) → ℝ)

include hb in
/-- The box phase family evaluated at a box point is the phase of the datum at the unit point. -/
theorem evalF_toXi_eq (x : DataSpace (n + 1)) (v : Fin (n + 1) → ℝ) :
    evalF (toXi b x) v = evalF (xiCoord x) (b⁻¹ • v) := by
  rw [← scale_toXi hb.ne' x, evalF_scale, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]

theorem toEta_sampleDatum_of_integrable (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace (n + 1)) (m : ℕ) (ω : Ω) :
    toEta b (sampleDatum b hb c hc P X A m ω) = toEta b A := by
  have h := etaCoord_sampleDatum_of_integrable b hb c hc P X hint A m ω
  funext γ
  simp only [toEta]
  rw [show sampleDatum b hb c hc P X A m ω (Sum.inr γ) = A (Sum.inr γ) from congrFun h γ]

/-- **Sampling/core compatibility (the release gate)**: in the monomial chart `φ(v) = v^k`, at
every box point `v ∈ (0,b]^d`, the sampling integrand `e^{−β ∑_{i<n} v^k a(X_i,v)}` is the phase
factor `e^{−βN v^{2k} + β√N v^k ξ(v)}` of the box integrand at the sample datum with `N = n`. -/
theorem exp_sampling_exponent_eq_core_factor (k : Fin (n + 1) → ℕ)
    (hint : Integrable (sampleObs b hb c hc X 0) P) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    {m : ℕ} (hm : 0 < m) (ω : Ω) {v : Fin (n + 1) → ℝ} (hv : v ∈ piBox (n + 1) (Ioc 0 b))
    (hca : ∀ x, evalF (c x) v = -a x v) (hφ : ∫ ω', a (X 0 ω') v ∂P = ∏ i, v i ^ k i) (β : ℝ) :
    Real.exp (-β * ∑ i ∈ Finset.range m, (∏ i, v i ^ k i) * a (X i ω) v) =
      Real.exp (-(β * m * ∏ i, v i ^ (2 * k i)) + β * (Real.sqrt m * ∏ i, v i ^ k i) *
        evalF (toXi b (sampleDatum b hb c hc P X A m ω)) v) := by
  set u : Fin (n + 1) → ℝ := b⁻¹ • v with hu_def
  have hbu : b • u = v := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  have hu : u ∈ closedCube (n + 1) := by
    refine unitBox_subset_closedCube _ ((smul_mem_piBox_Ioc_iff hb u).1 ?_)
    rwa [hbu]
  have hsq : ∏ i, v i ^ (2 * k i) = (∏ i, v i ^ k i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  rw [evalF_toXi_eq b hb, ← hu_def, hsq]
  congr 1
  have h := sampling_exponent_eq_sampleDatum_phase b hb c hc P X a (fun w => ∏ i, w i ^ k i) hint
    A hA hm ω hu (by rw [hbu]; exact hca) (by rw [hbu]; exact hφ) β
  rw [hbu] at h
  rw [h]
  ring

/-- **The certified core at the sample datum is the sampling integral**: for `0 < m` samples,
`Z(m; sampleDatum) = ∫_{(0,b]^d} η_A(v) v^h e^{−β ∑_{i<m} f(X_i,v)} dv` with
`f(x,v) = v^k a(x,v)`. -/
theorem dataBoxIntegral_sampleDatum_eq_sampling (h k : Fin (n + 1) → ℕ)
    (hint : Integrable (sampleObs b hb c hc X 0) P) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    {m : ℕ} (hm : 0 < m) (ω : Ω)
    (hca : ∀ x, ∀ v ∈ piBox (n + 1) (Ioc 0 b), evalF (c x) v = -a x v)
    (hφ : ∀ v ∈ piBox (n + 1) (Ioc 0 b), ∫ ω', a (X 0 ω') v ∂P = ∏ i, v i ^ k i) (β : ℝ) :
    dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) =
      ∫ v in piBox (n + 1) (Ioc 0 b), evalF (toEta b A) v * (∏ i, v i ^ h i) *
        Real.exp (-β * ∑ i ∈ Finset.range m, (∏ i, v i ^ k i) * a (X i ω) v) := by
  unfold dataBoxIntegral familyPhaseIntegralBox
  rw [toEta_sampleDatum_of_integrable b hb c hc P X hint A m ω]
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun v hv => ?_
  rw [exp_sampling_exponent_eq_core_factor b hb c hc P X a k hint A hA hm ω hv (fun x => hca x v hv)
    (hφ v hv) β]

end Core

end Grammar
