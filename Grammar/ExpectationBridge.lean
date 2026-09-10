import Grammar.GaussianDenominator
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# From convergence in distribution to convergence of expectations

Convergence in distribution `X_n ⇒ Z` does not give `E X_n → E Z`; a uniform moment bound does.
This file proves the clipping lemma

* if `X_n ⇒ Z` (`TendstoInDistribution`, the laws possibly living on different spaces) and
  `sup_n E|X_n|^p ≤ M` for some `p > 1`, then `Z` is integrable and `E X_n → E Z`
  (`tendsto_integral_of_tendstoInDistribution_of_moment`),

by the clipping `T_R(x) = max(−R, min(x, R))`: weak convergence handles `E T_R(X_n) → E T_R(Z)`,
the moment bound gives `E|X_n − T_R(X_n)| ≤ M R^{1−p}`, and the same bound passes to `Z`
through bounded truncations of `|x|^p`. Conversely, if `X_n ≥ 0`, `X_n ⇒ Z` and `E₊ Z = +∞`, then
`E₊ X_n → +∞` (`tendsto_lintegral_top_of_tendstoInDistribution`): no uniform integrability is
possible above the threshold.

Applied to the Gaussian-limit denominator `D(G)` of the quartet: if the scaled empirical
denominators converge in distribution to `D(G)` with a uniform `p`-th moment bound, then their
expectations converge to `Γ(λ)(βδ)^{−λ} ∑ᵢ ρᵢ` (`δ = 1 − βc/2 > 0`); at `βc ≥ 2` their
`E₊` diverge (`tendsto_integral_quartetD_of_tendstoInDistribution`,
`tendsto_lintegral_top_of_tendstoInDistribution_quartetD`). Scalar convergence in distribution
suffices; no coupling is needed. The law-level uniform-integrability version (laws on `ℝ`,
`UniformIntegrableLaws`) is `integrable_and_tendsto_integral_of_uniformIntegrable` in
`Grammar.UniformIntegrability`; the moment version here is the one that is easy to instantiate.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Bounded continuous truncations -/

/-- The clipping map `T_R(x) = max(−R, min(x, R))` as a bounded continuous function. -/
noncomputable def clipR (R : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max (-R) (min x R))
    (by fun_prop) |R| fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(neg_le_neg (le_abs_self R)).trans (le_max_left _ _),
        max_le (neg_le_abs R) ((min_le_right x R).trans (le_abs_self R))⟩

theorem clipR_apply (R x : ℝ) : clipR R x = max (-R) (min x R) := rfl

theorem clipR_of_abs_le {R x : ℝ} (h : |x| ≤ R) : clipR R x = x := by
  rw [abs_le] at h
  rw [clipR_apply, min_eq_left h.2, max_eq_right h.1]

/-- `|x − T_R(x)| ≤ |x|^p / R^{p−1}` for `R > 0`, `p ≥ 1`. -/
theorem abs_sub_clipR_le {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) (x : ℝ) :
    |x - clipR R x| ≤ |x| ^ p / R ^ (p - 1) := by
  rcases le_or_gt |x| R with h | h
  · rw [clipR_of_abs_le h, sub_self, abs_zero]
    positivity
  · have hx0 : 0 < |x| := lt_trans hR h
    have h1 : |x - clipR R x| ≤ |x| := by
      rw [clipR_apply]
      rcases le_or_gt 0 x with hx | hx
      · have hxR : R < x := by rwa [abs_of_nonneg hx] at h
        rw [min_eq_right hxR.le, max_eq_right (by linarith), abs_of_nonneg (by linarith),
          abs_of_nonneg hx]
        linarith
      · have hxR : x < -R := by
          rw [abs_of_neg hx] at h
          linarith
        rw [min_eq_left (by linarith), max_eq_left hxR.le, abs_of_nonpos (by linarith),
          abs_of_neg hx]
        linarith
    have h2 : |x| ≤ |x| ^ p / R ^ (p - 1) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hR _)]
      calc |x| * R ^ (p - 1) ≤ |x| * |x| ^ (p - 1) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le h.le (by linarith)) hx0.le
        _ = |x| ^ p := by
            have h3 := Real.rpow_add hx0 1 (p - 1)
            rw [Real.rpow_one, show (1 : ℝ) + (p - 1) = p by ring] at h3
            rw [h3]
    exact h1.trans h2

/-- The truncation `min(|x|^p, N)` as a bounded continuous function (`p ≥ 0`). -/
noncomputable def truncPowBCF (p : ℝ) (hp : 0 ≤ p) (N : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (|x| ^ p) N)
    ((continuous_abs.rpow_const fun _ => Or.inr hp).min continuous_const) N fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg _) _)
        (Nat.cast_nonneg _))]
      exact min_le_right _ _

theorem truncPowBCF_apply (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (x : ℝ) :
    truncPowBCF p hp N x = min (|x| ^ p) N := rfl

/-- The truncation `min(max(x, 0), N)` as a bounded continuous function. -/
noncomputable def truncPosBCF (N : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (max x 0) N) (by fun_prop) N
    fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg _))]
      exact min_le_right _ _

theorem truncPosBCF_apply (N : ℕ) (x : ℝ) : truncPosBCF N x = min (max x 0) N := rfl

/-! ### Weak convergence on the original spaces -/

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {X : ∀ n, Ω n → ℝ} {Z : Ω' → ℝ}

/-- Convergence in distribution tested against a bounded continuous function, written on the
original probability spaces. -/
theorem tendsto_integral_bcf_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ ω, f (X n ω) ∂μ n) atTop (𝓝 (∫ ω, f (Z ω) ∂μ')) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hX.tendsto) f
  simp only [ProbabilityMeasure.coe_mk] at h
  have hf : ∀ ν : Measure ℝ, AEStronglyMeasurable f ν := fun ν =>
    f.continuous.measurable.aestronglyMeasurable
  rw [integral_map hX.aemeasurable_limit (hf _)] at h
  exact h.congr fun n => integral_map (hX.forall_aemeasurable n) (hf _)

theorem integrable_bcf_comp {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Y : α → ℝ} (hY : AEMeasurable Y ν)
    (f : BoundedContinuousFunction ℝ ℝ) : Integrable (fun a => f (Y a)) ν :=
  Integrable.of_bound (f.continuous.measurable.comp_aemeasurable hY).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun a => f.norm_coe_le_norm (Y a))

/-! ### The moment bound passes to the limit -/

theorem integrable_of_integrable_rpow_abs {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Y : α → ℝ} (hY : AEStronglyMeasurable Y ν) {p : ℝ} (hp : 1 ≤ p)
    (h : Integrable (fun a => |Y a| ^ p) ν) : Integrable Y ν := by
  have hI : Integrable (fun a => |Y a| ^ p + 1) ν := h.add (integrable_const 1)
  refine hI.mono' hY (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]
  rcases le_or_gt |Y a| 1 with h1 | h1
  · have := Real.rpow_nonneg (abs_nonneg (Y a)) p
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1.le hp
    rw [Real.rpow_one] at this
    linarith

/-- If `X_n ⇒ Z` and `E|X_n|^p ≤ M` for all `n`, then `|Z|^p` is integrable with `E|Z|^p ≤ M`. -/
theorem integrable_rpow_abs_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
    {p M : ℝ} (hp : 1 ≤ p) (hint : ∀ n, Integrable (fun ω => |X n ω| ^ p) (μ n))
    (hM : ∀ n, ∫ ω, |X n ω| ^ p ∂μ n ≤ M) :
    Integrable (fun ω => |Z ω| ^ p) μ' ∧ ∫ ω, |Z ω| ^ p ∂μ' ≤ M := by
  have hp0 : 0 ≤ p := by linarith
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0)
  have hnn : ∀ (N : ℕ) (x : ℝ), 0 ≤ min (|x| ^ p) N := fun N x =>
    le_min (Real.rpow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _)
  -- `E min(|Z|^p, N) ≤ M` for every `N`
  have hZN : ∀ N : ℕ, ∫ ω, min (|Z ω| ^ p) N ∂μ' ≤ M := by
    intro N
    refine le_of_tendsto' (tendsto_integral_bcf_of_tendstoInDistribution hX (truncPowBCF p hp0 N))
      fun n => ?_
    calc ∫ ω, truncPowBCF p hp0 N (X n ω) ∂μ n ≤ ∫ ω, |X n ω| ^ p ∂μ n :=
          integral_mono (integrable_bcf_comp (hX.forall_aemeasurable n) _) (hint n)
            fun ω => min_le_left _ _
      _ ≤ M := hM n
  have hsup : ∀ x : ℝ, ⨆ N : ℕ, ENNReal.ofReal (min (|x| ^ p) N) = ENNReal.ofReal (|x| ^ p) := by
    intro x
    apply le_antisymm
    · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · refine le_iSup_of_le ⌈|x| ^ p⌉₊ ?_
      rw [min_eq_left (Nat.le_ceil _)]
  have hZlin : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ' ≤ ENNReal.ofReal M := by
    simp_rw [← hsup]
    have hmeas : ∀ N : ℕ, AEMeasurable (fun ω => ENNReal.ofReal (min (|Z ω| ^ p) N)) μ' :=
      fun N => (Measurable.ennreal_ofReal ((continuous_abs.rpow_const fun _ => Or.inr hp0).min
        continuous_const).measurable).comp_aemeasurable hX.aemeasurable_limit
    rw [lintegral_iSup' hmeas (Filter.Eventually.of_forall fun ω a b hab =>
        ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hab)))]
    refine iSup_le fun N => ?_
    have hZint : Integrable (fun ω => min (|Z ω| ^ p) N) μ' :=
      integrable_bcf_comp hX.aemeasurable_limit (truncPowBCF p hp0 N)
    rw [← ofReal_integral_eq_lintegral_ofReal hZint (Filter.Eventually.of_forall fun ω => hnn N _)]
    exact ENNReal.ofReal_le_ofReal (hZN N)
  have hZm : AEStronglyMeasurable (fun ω => |Z ω| ^ p) μ' :=
    ((continuous_abs.rpow_const fun _ => Or.inr hp0).measurable.comp_aemeasurable
      hX.aemeasurable_limit).aestronglyMeasurable
  have hZfin : HasFiniteIntegral (fun ω => |Z ω| ^ p) μ' := by
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    exact lt_of_le_of_lt hZlin ENNReal.ofReal_lt_top
  refine ⟨⟨hZm, hZfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg (abs_nonneg _) _) hZm, ← ENNReal.toReal_ofReal hM0]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hZlin

/-! ### The clipping estimate for expectations -/

theorem abs_integral_sub_clipR_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (Y : α → ℝ) (hY : Integrable Y ν) {p M : ℝ} (hp : 1 ≤ p)
    (hYp : Integrable (fun a => |Y a| ^ p) ν) (hYM : ∫ a, |Y a| ^ p ∂ν ≤ M) {R : ℝ} (hR : 0 < R) :
    |∫ a, Y a ∂ν - ∫ a, clipR R (Y a) ∂ν| ≤ M / R ^ (p - 1) := by
  have hcl : Integrable (fun a => clipR R (Y a)) ν := integrable_bcf_comp hY.aemeasurable _
  rw [← integral_sub hY hcl]
  calc |∫ a, Y a - clipR R (Y a) ∂ν| ≤ ∫ a, |Y a - clipR R (Y a)| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ a, |Y a| ^ p / R ^ (p - 1) ∂ν :=
        integral_mono (hY.sub hcl).abs (hYp.div_const _) fun a => abs_sub_clipR_le hR hp _
    _ = (∫ a, |Y a| ^ p ∂ν) / R ^ (p - 1) := integral_div _ _
    _ ≤ M / R ^ (p - 1) := div_le_div_of_nonneg_right hYM (Real.rpow_pos_of_pos hR _).le

/-- **Convergence of expectations from convergence in distribution and a uniform moment bound.**
If `X_n ⇒ Z` and `E|X_n|^p ≤ M` for all `n` with `p > 1`, then `Z` is integrable and
`E X_n → E Z`. -/
theorem tendsto_integral_of_tendstoInDistribution_of_moment
    (hX : TendstoInDistribution X atTop Z μ μ') {p M : ℝ} (hp : 1 < p)
    (hint : ∀ n, Integrable (fun ω => |X n ω| ^ p) (μ n))
    (hM : ∀ n, ∫ ω, |X n ω| ^ p ∂μ n ≤ M) :
    Integrable Z μ' ∧ Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 (∫ ω, Z ω ∂μ')) := by
  obtain ⟨hZp, hZM⟩ := integrable_rpow_abs_of_tendstoInDistribution hX hp.le hint hM
  have hZint : Integrable Z μ' :=
    integrable_of_integrable_rpow_abs hX.aemeasurable_limit.aestronglyMeasurable hp.le hZp
  have hXint : ∀ n, Integrable (X n) (μ n) := fun n =>
    integrable_of_integrable_rpow_abs (hX.forall_aemeasurable n).aestronglyMeasurable hp.le (hint n)
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0)
  refine ⟨hZint, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR0, hRM⟩ : ∃ R : ℝ, 0 < R ∧ M / R ^ (p - 1) < ε / 4 := by
    have hbase : 0 < 4 * M / ε + 1 := by
      have := div_nonneg (by linarith : (0 : ℝ) ≤ 4 * M) hε.le
      linarith
    refine ⟨(4 * M / ε + 1) ^ (p - 1)⁻¹, Real.rpow_pos_of_pos hbase _, ?_⟩
    rw [Real.rpow_inv_rpow hbase.le (by linarith : p - 1 ≠ 0), div_lt_iff₀ hbase,
      show ε / 4 * (4 * M / ε + 1) = M + ε / 4 by field_simp]
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_bcf_of_tendstoInDistribution hX (clipR R)) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := abs_integral_sub_clipR_le (μ n) (X n) (hXint n) hp.le (hint n) (hM n) hR0
  have h2 := abs_integral_sub_clipR_le μ' Z hZint hp.le hZp hZM hR0
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  rw [abs_sub_comm] at h2
  calc |∫ ω, X n ω ∂μ n - ∫ ω, Z ω ∂μ'|
      = |(∫ ω, X n ω ∂μ n - ∫ ω, clipR R (X n ω) ∂μ n) +
          (∫ ω, clipR R (X n ω) ∂μ n - ∫ ω, clipR R (Z ω) ∂μ') +
          (∫ ω, clipR R (Z ω) ∂μ' - ∫ ω, Z ω ∂μ')| := by
        congr 1
        ring
    _ ≤ |∫ ω, X n ω ∂μ n - ∫ ω, clipR R (X n ω) ∂μ n| +
          |∫ ω, clipR R (X n ω) ∂μ n - ∫ ω, clipR R (Z ω) ∂μ'| +
          |∫ ω, clipR R (Z ω) ∂μ' - ∫ ω, Z ω ∂μ'| := abs_add_three _ _ _
    _ < ε := by linarith

/-! ### Divergence transfers -/

/-- **No uniform integrability above threshold**: if `X_n ≥ 0`, `X_n ⇒ Z ≥ 0` and `E₊ Z = +∞`,
then `E₊ X_n → +∞`. -/
theorem tendsto_lintegral_top_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
    (hnn : ∀ n ω, 0 ≤ X n ω) (hZnn : ∀ ω, 0 ≤ Z ω)
    (hZ : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ' = ⊤) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ n) atTop (𝓝 ⊤) := by
  refine ENNReal.tendsto_nhds_top fun K => ?_
  have hsup : ∀ x : ℝ, 0 ≤ x → ⨆ N : ℕ, ENNReal.ofReal (min (max x 0) N) = ENNReal.ofReal x := by
    intro x hx
    rw [max_eq_left hx]
    apply le_antisymm
    · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · refine le_iSup_of_le ⌈x⌉₊ ?_
      rw [min_eq_left (Nat.le_ceil _)]
  have hZsup : ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (min (max (Z ω) 0) N) ∂μ' = ⊤ := by
    have hmeas : ∀ N : ℕ, AEMeasurable (fun ω => ENNReal.ofReal (min (max (Z ω) 0) N)) μ' :=
      fun N => (Measurable.ennreal_ofReal ((continuous_id.max continuous_const).min
        continuous_const).measurable).comp_aemeasurable hX.aemeasurable_limit
    rw [← lintegral_iSup' hmeas (Filter.Eventually.of_forall fun ω a b hab =>
        ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hab))), ← hZ]
    exact lintegral_congr fun ω => hsup _ (hZnn ω)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (K : ℝ≥0∞) < ∫⁻ ω, ENNReal.ofReal (min (max (Z ω) 0) N) ∂μ' := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact absurd hZsup (ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (iSup_le h))
  have hZint : Integrable (fun ω => truncPosBCF N (Z ω)) μ' :=
    integrable_bcf_comp hX.aemeasurable_limit _
  have hKZ : (K : ℝ) < ∫ ω, truncPosBCF N (Z ω) ∂μ' := by
    have hpos : 0 ≤ ∫ ω, truncPosBCF N (Z ω) ∂μ' :=
      integral_nonneg fun ω => le_min (le_max_right _ _) (Nat.cast_nonneg _)
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ofReal_integral_eq_lintegral_ofReal hZint
        (Filter.Eventually.of_forall fun ω => le_min (le_max_right _ _) (Nat.cast_nonneg _))]
    exact hN
  have hev := (tendsto_integral_bcf_of_tendstoInDistribution hX (truncPosBCF N)).eventually
    (lt_mem_nhds hKZ)
  refine hev.mono fun n hn => ?_
  have hXint : Integrable (fun ω => truncPosBCF N (X n ω)) (μ n) :=
    integrable_bcf_comp (hX.forall_aemeasurable n) _
  calc (K : ℝ≥0∞) = ENNReal.ofReal K := (ENNReal.ofReal_natCast K).symm
    _ < ENNReal.ofReal (∫ ω, truncPosBCF N (X n ω) ∂μ n) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg _)).2 hn
    _ = ∫⁻ ω, ENNReal.ofReal (truncPosBCF N (X n ω)) ∂μ n :=
        ofReal_integral_eq_lintegral_ofReal hXint
          (Filter.Eventually.of_forall fun ω => le_min (le_max_right _ _) (Nat.cast_nonneg _))
    _ ≤ ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ n :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          ((min_le_left _ _).trans (le_of_eq (max_eq_left (hnn n ω))))

/-! ### The Gaussian-limit denominator -/

variable {m k : ℕ} (A : Matrix (Fin m) (Fin (k + 1)) ℝ) {β lam : ℝ}

/-- **Expected denominators converge below threshold**: if the scaled empirical denominators
`X_n` converge in distribution to `D(G)` with a uniform `p`-th moment bound, `p > 1`, then
`E X_n → Γ(λ)(βδ)^{−λ} ∑ᵢ ρᵢ`. -/
theorem tendsto_integral_quartetD_of_tendstoInDistribution (hβ : 0 < β) (hlam : 0 < lam)
    (ρ : Fin m → ℝ) {c : ℝ} (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c)
    (hδ : 0 < 1 - β * c / 2)
    (hX : TendstoInDistribution X atTop (quartetD β lam ρ) μ (gaussianVector A)) {p M : ℝ}
    (hp : 1 < p) (hint : ∀ n, Integrable (fun ω => |X n ω| ^ p) (μ n))
    (hM : ∀ n, ∫ ω, |X n ω| ^ p ∂μ n ≤ M) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop
      (𝓝 (Real.Gamma lam * (β * (1 - β * c / 2)) ^ (-lam) * ∑ i, ρ i)) := by
  have h := (tendsto_integral_of_tendstoInDistribution_of_moment hX hp hint hM).2
  rwa [(integral_quartetD A hβ hlam ρ hc hδ).2] at h

/-- **Expected denominators diverge at and above threshold**: if `X_n ≥ 0` converge in
distribution to `D(G)` and `βc ≥ 2`, then `E₊ X_n → +∞`; in particular no uniform moment bound
of any order `p > 1` can hold. -/
theorem tendsto_lintegral_top_of_tendstoInDistribution_quartetD (hβ : 0 < β) (hlam : 0 < lam)
    {ρ : Fin m → ℝ} (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (h2 : 2 ≤ β * c)
    (hnn : ∀ n ω, 0 ≤ X n ω)
    (hX : TendstoInDistribution X atTop (quartetD β lam ρ) μ (gaussianVector A)) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ n) atTop (𝓝 ⊤) :=
  tendsto_lintegral_top_of_tendstoInDistribution hX hnn (fun g => (quartetD_pos hβ hlam hρ g).le)
    (lintegral_quartetD_eq_top A hβ hlam hρ hc h2)

end Grammar
