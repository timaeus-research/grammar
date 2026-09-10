import Grammar.CompactBaseFinite

/-!
# Compact base II (part 2): the Gaussian identities on the compact base

Passing to the limit along a mass-preserving quantisation sequence `ρₙ = ρ ∘ qₙ⁻¹` (dominated
convergence in `ω`, with the partition-independent bounds of `CompactBaseQuantise`/`Kernel` and the
second sup-norm moment of the field), the finite identities of `CompactBaseFinite` become
identities for the compact base itself. For a Gaussian field `G` with kernel `𝒞` on a nonempty
compact metric base with finite `ρ ≠ 0`:

* **`E H_ρ(G) = β E V_ρ(G)`** (`GaussianField.integral_compactH_eq`);
* **the integrated covariance interpolation**
  `E log D_ρ(G) = log D_ρ(0) + (β²/2) ∫₀¹ E V_ρ(√t G) dt`
  (`GaussianField.integral_log_compactD_eq`), with `D_ρ(0) = ρ(K) β^{−λ} Γ(λ)`;
* **`E log D_ρ(G) ≥ log D_ρ(0)`** (`GaussianField.log_compactD_zero_le_integral`).

The convergence lemmas (`tendsto_integral_compactH_map`, `tendsto_integral_compactV_map`,
`tendsto_integral_log_compactD_map`) hold for any random continuous function with measurable
evaluations and `E‖g‖²_∞ < ∞`; the Gaussian law enters only through the finite identities.
Non-claims: no Gaussian process is constructed, no Fernique theorem, and finite-dimensional
Gaussianity is not claimed to imply the second sup-norm moment.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Limits

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (𝒞 : PSDKernel K) {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → C(K, ℝ))
  {q : ℕ → K → K} {ε : ℕ → ℝ}

omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [IsFiniteMeasure ρ] in
theorem map_quantise_ne_zero {q : K → K} (hq : Measurable q) (hρ : ρ ≠ 0) : ρ.map q ≠ 0 := by
  intro h
  apply hρ
  have := map_quantise_univ ρ hq
  rw [h, Measure.coe_zero, Pi.zero_apply] at this
  exact Measure.measure_univ_eq_zero.1 this.symm

omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [IsFiniteMeasure ρ] in
theorem map_quantise_real_univ {q : K → K} (hq : Measurable q) :
    (ρ.map q).real univ = ρ.real univ := by
  simp only [measureReal_def, map_quantise_univ ρ hq]

omit [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
/-- The diagonal of a continuous kernel on a compact base is bounded. -/
theorem PSDKernel.exists_diag_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, 𝒞.C x x ≤ c := by
  set f : C(K, ℝ) := ⟨fun x => 𝒞.C x x, 𝒞.continuous_diag⟩
  exact ⟨‖f‖, norm_nonneg f, fun x => (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm x)⟩

omit [Nonempty K] [MeasurableSpace K] [BorelSpace K] in
/-- Dominating functions of the form `C (1 + ‖g‖²)` are integrable. -/
theorem integrable_const_mul_one_add_sq (hsq : Integrable (fun ω => ‖g ω‖ ^ 2) P) (C : ℝ) :
    Integrable (fun ω => C * (1 + ‖g ω‖ ^ 2)) P :=
  ((integrable_const (1 : ℝ)).add hsq).const_mul C

/-! ### Measurability of the quantised quantities -/

omit [Nonempty K] in
theorem measurable_compactD_map (hβ : 0 < β) (hlam : 0 < lam)
    (hg : ∀ x, Measurable fun ω => g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω => compactD β lam (ρ.map (q n)) (g ω) := by
  have : (fun ω => compactD β lam (ρ.map (q n)) (g ω)) = fun ω =>
      quartetD β lam (atomWt ρ (hfin n)) (fun i => g ω (atomPt ρ (hfin n) i)) :=
    funext fun ω => compactD_map_eq ρ hβ hlam (g ω) (hq n) (hfin n)
  rw [this]
  exact (continuous_quartetD hβ hlam).measurable.comp (measurable_pi_lambda _ fun i => hg _)

omit [Nonempty K] in
theorem measurable_log_compactD_map (hβ : 0 < β) (hlam : 0 < lam)
    (hg : ∀ x, Measurable fun ω => g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω => Real.log (compactD β lam (ρ.map (q n)) (g ω)) :=
  Real.measurable_log.comp (measurable_compactD_map ρ g hβ hlam hg hq hfin n)

omit [Nonempty K] in
theorem measurable_compactH_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (hg : ∀ x, Measurable fun ω => g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω => compactH β lam (ρ.map (q n)) (g ω) := by
  have := nonempty_atoms ρ (hq n) (hfin n) hρ
  have : (fun ω => compactH β lam (ρ.map (q n)) (g ω)) = fun ω =>
      quartetH β lam (atomWt ρ (hfin n)) (fun i => g ω (atomPt ρ (hfin n) i)) :=
    funext fun ω => compactH_map_eq ρ hβ hlam (g ω) (hq n) (hfin n)
  rw [this]
  exact (continuous_quartetH hβ hlam (atomWt_pos ρ (hfin n))).measurable.comp
    (measurable_pi_lambda _ fun i => hg _)

omit [Nonempty K] in
theorem measurable_compactV_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (hg : ∀ x, Measurable fun ω => g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω => compactV (ρ.map (q n)) β lam 𝒞 (g ω) := by
  have := nonempty_atoms ρ (hq n) (hfin n) hρ
  have : (fun ω => compactV (ρ.map (q n)) β lam 𝒞 (g ω)) = fun ω =>
      quartetVgen β lam (atomWt ρ (hfin n)) (𝒞.kernelMatrix (atomPt ρ (hfin n)))
        (fun i => g ω (atomPt ρ (hfin n) i)) :=
    funext fun ω => compactV_map_eq ρ hβ hlam 𝒞 (g ω) (hq n) (hfin n) hρ
  rw [this]
  exact (continuous_quartetVgen hβ hlam (atomWt_pos ρ (hfin n)) _).measurable.comp
    (measurable_pi_lambda _ fun i => hg _)

/-! ### Dominated convergence along the quantisation sequence -/

variable (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (hg : ∀ x, Measurable fun ω => g ω x)
  (hsq : Integrable (fun ω => ‖g ω‖ ^ 2) P) (hq : ∀ n, Measurable (q n))
  (hfin : ∀ n, (Set.range (q n)).Finite) (hε : Tendsto ε atTop (𝓝 0))
  (hqε : ∀ n x, dist x (q n x) < ε n)
include hβ hlam hρ hg hsq hq hfin hε hqε

omit [Nonempty K] in
/-- **`E H_{ρₙ}(g) → E H_ρ(g)`.** -/
theorem tendsto_integral_compactH_map :
    Tendsto (fun n => ∫ ω, compactH β lam (ρ.map (q n)) (g ω) ∂P) atTop
      (𝓝 (∫ ω, compactH β lam ρ (g ω) ∂P)) := by
  have hB : 0 ≤ Real.sqrt (2 * lam / β) := Real.sqrt_nonneg _
  refine tendsto_integral_of_dominated_convergence
    (fun ω => (Real.sqrt (2 * lam / β) + 1 / 2) * (1 + ‖g ω‖ ^ 2))
    (fun n => (measurable_compactH_map ρ g hβ hlam hρ hg hq hfin n).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P g hsq _)
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => tendsto_compactH_map ρ hβ hlam hρ (g ω) hq hε hqε)
  rw [Real.norm_eq_abs]
  refine (abs_compactH_le (ρ.map (q n)) hβ hlam (g ω) (map_quantise_ne_zero ρ (hq n) hρ)
    le_rfl).trans ?_
  nlinarith [norm_nonneg (g ω), sq_nonneg (‖g ω‖ - 1)]

omit [MeasurableSpace Ω] hg hsq hfin hε hqε in
theorem abs_compactV_map_le {c : ℝ} (hc : ∀ x, 𝒞.C x x ≤ c) (n : ℕ) (ω : Ω) :
    |compactV (ρ.map (q n)) β lam 𝒞 (g ω)| ≤ c * (2 * lam / β + ‖g ω‖ ^ 2 / 4) := by
  have h0 := compactV_nonneg (ρ.map (q n)) hβ hlam 𝒞 (g ω) (map_quantise_ne_zero ρ (hq n) hρ)
  rw [abs_of_nonneg h0]
  exact compactV_le (ρ.map (q n)) hβ hlam 𝒞 (g ω) (map_quantise_ne_zero ρ (hq n) hρ) hc le_rfl

/-- **`E V_{ρₙ}(g) → E V_ρ(g)`.** -/
theorem tendsto_integral_compactV_map :
    Tendsto (fun n => ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (g ω) ∂P) atTop
      (𝓝 (∫ ω, compactV ρ β lam 𝒞 (g ω) ∂P)) := by
  obtain ⟨c, hc0, hc⟩ := 𝒞.exists_diag_bound
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  refine tendsto_integral_of_dominated_convergence
    (fun ω => (c * (2 * lam / β + 1 / 4)) * (1 + ‖g ω‖ ^ 2))
    (fun n => (measurable_compactV_map ρ 𝒞 g hβ hlam hρ hg hq hfin n).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P g hsq _)
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => tendsto_compactV_map ρ hβ hlam 𝒞 (g ω) hρ hq hε hqε)
  rw [Real.norm_eq_abs]
  refine (abs_compactV_map_le ρ 𝒞 g hβ hlam hρ hq hc n ω).trans ?_
  nlinarith [norm_nonneg (g ω), sq_nonneg ‖g ω‖, mul_nonneg hc0 hB,
    mul_nonneg hc0 (sq_nonneg ‖g ω‖)]

omit [Nonempty K] in
/-- **`E log D_{ρₙ}(g) → E log D_ρ(g)`.** -/
theorem tendsto_integral_log_compactD_map :
    Tendsto (fun n => ∫ ω, Real.log (compactD β lam (ρ.map (q n)) (g ω)) ∂P) atTop
      (𝓝 (∫ ω, Real.log (compactD β lam ρ (g ω)) ∂P)) := by
  set C₀ : ℝ := |Real.log (ρ.real univ)| +
    (|Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)| + 2 * β + |Real.log lam|) with hC₀
  refine tendsto_integral_of_dominated_convergence
    (fun ω => (C₀ + lam + (β / 2 + lam)) * (1 + ‖g ω‖ ^ 2))
    (fun n => (measurable_log_compactD_map ρ g hβ hlam hg hq hfin n).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P g hsq _)
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω =>
      tendsto_log_compactD_map ρ hβ hlam hρ (g ω) hq hε hqε)
  rw [Real.norm_eq_abs]
  have h := abs_log_compactD_le (ρ.map (q n)) hβ hlam (map_quantise_ne_zero ρ (hq n) hρ) (g ω)
    (norm_nonneg _) le_rfl
  rw [map_quantise_real_univ ρ (hq n)] at h
  refine h.trans ?_
  rw [← hC₀]
  nlinarith [norm_nonneg (g ω), sq_nonneg (‖g ω‖ - 1), mul_nonneg hβ.le (sq_nonneg ‖g ω‖),
    abs_nonneg (Real.log (ρ.real univ)),
    abs_nonneg (Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)), abs_nonneg (Real.log lam)]

end Limits

/-! ### The identities on the compact base -/

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (hρ : ρ ≠ 0) {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (Γ : GaussianField 𝒞 P)

omit [Nonempty K] [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- The scaled field `√s G` has measurable evaluations. -/
theorem measurable_eval_smul (s : ℝ) (x : K) :
    Measurable fun ω => (Real.sqrt s • Γ.G ω : C(K, ℝ)) x := by
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  exact (Γ.measurable_eval x).const_mul _

omit [Nonempty K] [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- The scaled field `√s G` has a finite second sup-norm moment. -/
theorem integrable_sq_norm_smul (s : ℝ) :
    Integrable (fun ω => ‖(Real.sqrt s • Γ.G ω : C(K, ℝ))‖ ^ 2) P := by
  refine (Γ.integrable_sq_norm.const_mul (Real.sqrt s ^ 2)).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

include hβ hlam hρ

/-- **Gaussian integration by parts on the compact base**: `E H_ρ(G) = β E V_ρ(G)`. -/
theorem integral_compactH_eq :
    ∫ ω, compactH β lam ρ (Γ.G ω) ∂P = β * ∫ ω, compactV ρ β lam 𝒞 (Γ.G ω) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := exists_quantisation_seq (K := K)
  have h1 := tendsto_integral_compactH_map ρ P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin tendsto_one_div_add_atTop_nhds_zero_nat hqε
  have h2 := (tendsto_integral_compactV_map ρ 𝒞 P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin tendsto_one_div_add_atTop_nhds_zero_nat hqε).const_mul β
  exact tendsto_nhds_unique h1 (h2.congr fun n =>
    (Γ.integral_compactH_map_eq ρ hβ hlam hρ (hq n) (hfin n)).symm)

/-- **The integrated covariance interpolation on the compact base**:
`E log D_ρ(G) = log D_ρ(0) + (β²/2) ∫₀¹ E V_ρ(√s G) ds`. -/
theorem integral_log_compactD_eq :
    ∫ ω, Real.log (compactD β lam ρ (Γ.G ω)) ∂P =
      Real.log (β ^ (-lam) * Real.Gamma lam * ρ.real univ) +
        ∫ s in (0 : ℝ)..1, β ^ 2 / 2 *
          ∫ ω, compactV ρ β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := exists_quantisation_seq (K := K)
  have hε := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨c, hc0, hc⟩ := 𝒞.exists_diag_bound
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  -- the left side converges
  have hL := tendsto_integral_log_compactD_map ρ P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin hε hqε
  -- the interval integrals converge
  have hM2 : 0 ≤ ∫ ω, ‖Γ.G ω‖ ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hR : Tendsto (fun n => ∫ s in (0 : ℝ)..1, β ^ 2 / 2 *
      ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P) atTop
      (𝓝 (∫ s in (0 : ℝ)..1, β ^ 2 / 2 *
        ∫ ω, compactV ρ β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => β ^ 2 / 2 * (c * (2 * lam / β + (∫ ω, ‖Γ.G ω‖ ^ 2 ∂P) / 4)))
      (Filter.Eventually.of_forall fun n => ?_) (Filter.Eventually.of_forall fun n => ?_)
      intervalIntegrable_const (Filter.Eventually.of_forall fun s _ => ?_)
    · -- measurability in `s`: continuity on `[0,1]`
      have hcont := (Γ.continuousOn_integral_compactV_map_smul ρ hβ hlam hρ (hq n) (hfin n))
      have := ((continuousOn_const (c := β ^ 2 / 2)).mul hcont).aestronglyMeasurable
        (μ := volume) measurableSet_Icc
      exact this.mono_measure (Measure.restrict_mono
        (by rw [Set.uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self) le_rfl)
    · -- the uniform bound
      refine Filter.Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le zero_le_one] at hs
      have hs1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs.2
      have hV0 : ∀ ω, 0 ≤ compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) :=
        fun ω => compactV_nonneg (ρ.map (q n)) hβ hlam 𝒞 _ (map_quantise_ne_zero ρ (hq n) hρ)
      have hVle : ∀ ω, compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ≤
          c * (2 * lam / β + ‖Γ.G ω‖ ^ 2 / 4) := by
        intro ω
        refine compactV_le (ρ.map (q n)) hβ hlam 𝒞 _ (map_quantise_ne_zero ρ (hq n) hρ) hc ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
        exact mul_le_of_le_one_left (norm_nonneg _) hs1
      have hint : Integrable (fun ω => compactV (ρ.map (q n)) β lam 𝒞
          (Real.sqrt s • Γ.G ω : C(K, ℝ))) P :=
        Integrable.mono' (((integrable_const (2 * lam / β)).add
          (Γ.integrable_sq_norm.div_const 4)).const_mul c)
          (measurable_compactV_map ρ 𝒞 _ hβ hlam hρ (Γ.measurable_eval_smul s) hq hfin
            n).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hV0 ω)]; exact hVle ω)
      have hI : ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P ≤
          c * (2 * lam / β + (∫ ω, ‖Γ.G ω‖ ^ 2 ∂P) / 4) := by
        calc ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P
            ≤ ∫ ω, c * (2 * lam / β + ‖Γ.G ω‖ ^ 2 / 4) ∂P :=
              integral_mono hint (((integrable_const (2 * lam / β)).add
                (Γ.integrable_sq_norm.div_const 4)).const_mul c) hVle
          _ = c * (2 * lam / β + (∫ ω, ‖Γ.G ω‖ ^ 2 ∂P) / 4) := by
              rw [integral_const_mul, integral_add (integrable_const _)
                (Γ.integrable_sq_norm.div_const 4), integral_const, integral_div, probReal_univ,
                one_smul]
      have hI0 : 0 ≤ ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P :=
        integral_nonneg hV0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hI0)]
      exact mul_le_mul_of_nonneg_left hI (by positivity)
    · -- pointwise convergence in `s`
      exact (tendsto_integral_compactV_map ρ 𝒞 P _ hβ hlam hρ (Γ.measurable_eval_smul s)
        (Γ.integrable_sq_norm_smul s) hq hfin hε hqε).const_mul _
  refine tendsto_nhds_unique hL ?_
  refine (tendsto_const_nhds.add hR).congr fun n => ?_
  exact (Γ.integral_log_compactD_map_eq ρ hβ hlam hρ (hq n) (hfin n)).symm

/-- **`E log D_ρ(G) ≥ log D_ρ(0)`** on the compact base. -/
theorem log_compactD_zero_le_integral :
    Real.log (β ^ (-lam) * Real.Gamma lam * ρ.real univ) ≤
      ∫ ω, Real.log (compactD β lam ρ (Γ.G ω)) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := exists_quantisation_seq (K := K)
  exact ge_of_tendsto' (tendsto_integral_log_compactD_map ρ P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin tendsto_one_div_add_atTop_nhds_zero_nat hqε) fun n =>
    Γ.log_compactD_zero_le_integral_map ρ hβ hlam hρ (hq n) (hfin n)

end GaussianField

end Grammar
