/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartExpansion

/-!
# Finite chart assembly of the Taylor tree (Stage S14 — deterministic)

Unit 283 (Astra #34 / review v29). Finitely many charts `I : Fin M`, each with its own normal
dimension `n I + 1`, exponents `h I, k I`, box radius `b I`, compact tangential space `K I` and
finite measure `ν I`. The **joint tangential data** is the dependent product
`JointData K n = ∀ I, C(K I, DataSpace (n I + 1))` (sup norm over charts, Borel σ-algebra; a type
synonym so that the Borel structure is the one used, not the product σ-algebra). The **global
integral** is `𝒵^{glob}(N; x) = ∑_I 𝒵^I(N; x_I)` and the **global coefficients** are
`C^{glob}_{μ,j}(x) = ∑_I 𝒞^I_{μ,j}(x_I)` on the common lattice `Q = ∏_I Q_I` with the common degree
bound `D = max_I n_I`; charts contribute zero off their own lattice and above their own degree
(support theorems of unit 282 — the padding is a theorem, not a convention).

Results: the global cutoff bound uniform on joint balls (`gCutoff_bound`), the ballwise bound on
the global coefficients (`abs_gCoeff_le`), continuity/measurability of the global functionals, and
the **uniform convergence of the global ordered normalised remainder** on joint data balls
(`tendstoUniformlyOn_gRemainder`), for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ D` — including
targets that lie on no single chart's lattice or exceed a chart's degree, handled by the abstract
estimate of unit 281 (every chart is expanded through the common cutoff `L = μ + 1`, the
predecessors are subtracted globally, and the non-target terms vanish). The paper's spectrum
`Λ^*` is a subset of the common lattice; nothing is claimed about which coefficients are nonzero
(chart contributions may cancel).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

/-! ### Abstract equalities for refinement and padding -/

theorem absSpectralSum_refine_eq {Q Q' D : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (hQQ : Q ∣ Q')
    {c : ℝ → ℕ → ℝ} (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (L N : ℝ) :
    absSpectralSum Q' D c L N = absSpectralSum Q D c L N := by
  unfold absSpectralSum
  symm
  refine Finset.sum_subset (latticeBelow_subset_of_dvd hQ hQ' hQQ L) fun μ hμ' hμ => ?_
  have hzero : ∀ j, c μ j = 0 := by
    refine hc μ fun m hm => hμ ?_
    exact (mem_latticeBelow_iff hQ).2 ⟨⟨m, hm⟩, lt_of_mem_latticeBelow hQ' hμ'⟩
  simp [hzero]

theorem absSpectralSum_pad_eq {Q D D' : ℕ} (hD : D ≤ D') {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ j, D < j → c μ j = 0) (L N : ℝ) :
    absSpectralSum Q D' c L N = absSpectralSum Q D c L N := by
  unfold absSpectralSum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  symm
  refine Finset.sum_subset (fun j hj => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))) fun j _ hj => ?_
  have hDj : D < j := by
    by_contra hcon
    exact hj (Finset.mem_range.2 (by omega))
  simp [hc μ j hDj]

theorem absSpectralSum_add (Q D : ℕ) (c₁ c₂ : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => c₁ μ j + c₂ μ j) L N =
      absSpectralSum Q D c₁ L N + absSpectralSum Q D c₂ L N := by
  unfold absSpectralSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem absSpectralSum_sum {ι : Type*} (s : Finset ι) (Q D : ℕ) (c : ι → ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => ∑ i ∈ s, c i μ j) L N =
      ∑ i ∈ s, absSpectralSum Q D (c i) L N := by
  induction s using Finset.induction_on with
  | empty => simp [absSpectralSum]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [absSpectralSum_add, ih]

/-! ### Charts and joint tangential data -/

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ}

/-- The joint tangential data of finitely many charts (a type synonym carrying the sup norm and
the Borel σ-algebra). -/
def JointData (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] (n : Fin M → ℕ) :=
  ∀ I, TangentialData (K I) (n I + 1)

noncomputable instance : NormedAddCommGroup (JointData K n) :=
  inferInstanceAs (NormedAddCommGroup (∀ I, TangentialData (K I) (n I + 1)))

noncomputable instance : MeasurableSpace (JointData K n) := borel (JointData K n)
instance : BorelSpace (JointData K n) := ⟨rfl⟩

/-- The chart component of a joint datum. -/
def JointData.chart (x : JointData K n) (I : Fin M) : TangentialData (K I) (n I + 1) := x I

theorem continuous_chart (I : Fin M) : Continuous fun x : JointData K n => x.chart I :=
  continuous_apply (A := fun I => TangentialData (K I) (n I + 1)) I

theorem norm_chart_le (x : JointData K n) (I : Fin M) : ‖x.chart I‖ ≤ ‖x‖ :=
  norm_le_pi_norm (f := (x : ∀ I, TangentialData (K I) (n I + 1))) I

theorem norm_chart_sub_le (x y : JointData K n) (I : Fin M) :
    ‖x.chart I - y.chart I‖ ≤ ‖x - y‖ :=
  norm_le_pi_norm (f := ((x - y : JointData K n) : ∀ I, TangentialData (K I) (n I + 1))) I

variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The common lattice denominator `Q = ∏_I Q_I`. -/
def commonQ (k : (I : Fin M) → Fin (n I + 1) → ℕ) : ℕ := ∏ I, latticeQ (k I)

theorem commonQ_pos (hk : ∀ I i, 0 < k I i) : 0 < commonQ k :=
  Finset.prod_pos fun I _ => latticeQ_pos (k I) (hk I)

theorem latticeQ_dvd_commonQ (I : Fin M) : latticeQ (k I) ∣ commonQ k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ I)

/-- The common log-degree bound `D = max_I n_I`. -/
def commonD (n : Fin M → ℕ) : ℕ := Finset.univ.sup n

theorem le_commonD (I : Fin M) : n I ≤ commonD n := Finset.le_sup (Finset.mem_univ I)

/-- The global integral `∑_I 𝒵^I(N; x_I)`. -/
noncomputable def gInt (x : JointData K n) (N : ℝ) : ℝ :=
  ∑ I, tanIntegral (ν I) (n I) (h I) (k I) β N (b I) (x.chart I)

/-- The global coefficients `∑_I 𝒞^I_{μ,j}(x_I)`. -/
noncomputable def gCoeff (x : JointData K n) (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ I, tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j

/-- The global ordered normalised remainder. -/
noncomputable def gRemainder (x : JointData K n) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  abstractRemainder (commonQ k) (commonD n) (gInt ν h k β b x) (gCoeff ν h k β b x) μ j N

theorem continuous_gCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ : ℝ)
    (j : ℕ) : Continuous fun x : JointData K n => gCoeff ν h k β b x μ j := by
  unfold gCoeff
  exact continuous_finset_sum _ fun I _ =>
    (continuous_tanCoeff (ν I) (n I) (h I) (k I) (hk I) β hβ (hb I) μ j).comp (continuous_chart I)

theorem measurable_gInt (hβ : 0 < β) (hb : ∀ I, 0 < b I) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : JointData K n => gInt ν h k β b x N := by
  unfold gInt
  exact Finset.measurable_sum _ fun I _ =>
    ((continuous_tanIntegral (ν I) (n I) (h I) (k I) hβ.le hN (hb I)).comp
      (continuous_chart I)).measurable

theorem measurable_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ : ℝ)
    (j : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : JointData K n => gRemainder ν h k β b x μ j N := by
  unfold gRemainder abstractRemainder absPredSum absTerm
  refine Measurable.div_const (Measurable.sub (measurable_gInt ν h k β b hβ hb hN) ?_) _
  exact Finset.measurable_sum _ fun p _ =>
    ((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).mul_const _

/-! ### The global cutoff bound, uniform on joint balls -/

/-- The global cutoff constant on the joint ball of radius `R`. -/
noncomputable def gCutoffConst (L R : ℝ) : ℝ :=
  ∑ I, chartCutoffConst (ν I) (n I) (h I) (k I) β (b I) L R

/-- **The global cutoff bound**: for `‖x‖ ≤ R`, `N ≥ 1` and `N b_I^{2|k_I|} ≥ 1` for every chart,
`|𝒵^{glob}(N;x) − ∑_{Λ^Q_L} N^{-μ} ∑_{j≤D} C^{glob}_{μ,j}(x)(log N)^j| ≤ gCutoffConst L R ·
N^{-L}(1+log N)^D`. -/
theorem gCutoff_bound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {L : ℝ}
    (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) :
    |gInt ν h k β b x N -
        absSpectralSum (commonQ k) (commonD n) (gCoeff ν h k β b x) L N| ≤
      gCutoffConst ν h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ (commonD n)) := by
  have hQ := commonQ_pos k hk
  unfold gInt gCoeff gCutoffConst
  rw [absSpectralSum_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  -- reduce the chart's sum on the common lattice/degree to its own
  have hI := hk I
  have hsupp1 : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ (k I)) → ∀ j,
      tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 := fun μ hμ j =>
    tanCoeff_eq_zero_of_not_lattice (ν I) (n I) (h I) (k I) hI β hβ (hb I) _ hμ j
  have hsupp2 : ∀ μ j, n I < j → tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 :=
    fun μ j hj => tanCoeff_eq_zero_of_lt (ν I) (n I) (h I) (k I) β (b I) _ μ hj
  rw [absSpectralSum_refine_eq (latticeQ_pos (k I) hI) hQ (latticeQ_dvd_commonQ k I) hsupp1,
    absSpectralSum_pad_eq (le_commonD I) hsupp2]
  have hchart := tanCutoff_bound_N (ν I) (n I) (h I) (k I) hI β hβ hL (hb I) hN (hN' I)
    ((norm_chart_le x I).trans hx)
  refine hchart.trans ?_
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have h1 : (1 + Real.log N) ^ (n I) ≤ (1 + Real.log N) ^ (commonD n) :=
    pow_le_pow_right₀ hlog (le_commonD I)
  have hC0 := chartCutoffConst_nonneg (ν I) (n I) (h I) (k I) β hβ (hb I) L
    ((norm_nonneg x).trans hx)
  have hr : 0 ≤ N ^ (-L) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hC0

/-! ### Bounds on the global coefficients -/

theorem abs_tanCoeff_le {K' : Type*} [TopologicalSpace K'] [CompactSpace K'] [T2Space K']
    [MeasurableSpace K'] [OpensMeasurableSpace K'] (ν' : Measure K') [IsFiniteMeasure ν'] (n' : ℕ)
    (h' k' : Fin (n' + 1) → ℕ) (hk' : ∀ i, 0 < k' i) (hβ : 0 < β) {b' : ℝ} (hb' : 0 < b')
    {R : ℝ} {x : TangentialData K' (n' + 1)} (hx : ‖x‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |tanCoeff ν' n' h' k' β b' x μ j| ≤ (ν' univ).toReal * coeffBallBound n' h' k' β b' μ j R := by
  unfold tanCoeff
  have hbound : ∀ v,
      ‖dataBoxCoeff n' h' k' β b' (x v) μ j‖ ≤ coeffBallBound n' h' k' β b' μ j R := by
    intro v
    rw [Real.norm_eq_abs]
    exact abs_dataBoxCoeff_le_ballBound n' h' k' hk' β hβ hb' μ j ((norm_tan_apply_le x v).trans hx)
  have := norm_integral_le_of_norm_le_const (μ := ν') (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The ballwise bound on a global coefficient. -/
noncomputable def gCoeffBound (R μ : ℝ) (j : ℕ) : ℝ :=
  ∑ I, ((ν I) univ).toReal * coeffBallBound (n I) (h I) (k I) β (b I) μ j R

theorem abs_gCoeff_le (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |gCoeff ν h k β b x μ j| ≤ gCoeffBound ν h k β b R μ j := by
  unfold gCoeff gCoeffBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  exact abs_tanCoeff_le β (ν I) (n I) (h I) (k I) (hk I) hβ (hb I) ((norm_chart_le x I).trans hx)
    μ j

/-- The uniform bound on all global coefficients of the index set below `μ + 1`. -/
noncomputable def gIndexBound (R μ : ℝ) : ℝ :=
  ∑ p ∈ indexSet (commonD n) (commonQ k) (μ + 1), gCoeffBound ν h k β b R p.1 p.2

theorem gCoeffBound_nonneg (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    (hR : 0 ≤ R) (μ : ℝ) (j : ℕ) : 0 ≤ gCoeffBound ν h k β b R μ j := by
  have h0 : ‖(0 : JointData K n)‖ ≤ R := by simpa using hR
  exact (abs_nonneg _).trans (abs_gCoeff_le ν h k β b hk hβ hb h0 μ j)

theorem abs_gCoeff_le_indexBound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    (hR : 0 ≤ R) {x : JointData K n} (hx : ‖x‖ ≤ R) {μ : ℝ} {p : ℝ × ℕ}
    (hp : p ∈ indexSet (commonD n) (commonQ k) (μ + 1)) :
    |gCoeff ν h k β b x p.1 p.2| ≤ gIndexBound ν h k β b R μ :=
  (abs_gCoeff_le ν h k β b hk hβ hb hx p.1 p.2).trans
    (Finset.single_le_sum (fun q _ => gCoeffBound_nonneg ν h k β b hk hβ hb hR q.1 q.2) hp)

/-! ### The global ordered remainder, uniformly on joint balls -/

/-- **The global majorant estimate**: for `‖x‖ ≤ R`, `N ≥ e`, `N b_I^{2|k_I|} ≥ 1` for all charts,
`|R^{glob}_N(x) − C^{glob}_{μ,j}(x)| ≤ gCutoffConst(μ+1, R)·N^{-(μ+1)}(1+log N)^D/N^{-μ} +
gIndexBound(R, μ)·∑_{rest} termMajorant`. -/
theorem abs_gRemainder_sub_le (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) {N : ℝ} (hNe : Real.exp 1 ≤ N)
    (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) :
    |gRemainder ν h k β b x μ j N - gCoeff ν h k β b x μ j| ≤
      gCutoffConst ν h k β b (μ + 1) R *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ (commonD n) / N ^ (-μ)) +
        gIndexBound ν h k β b R μ *
          ∑ p ∈ restSet (commonD n) (commonQ k) μ j, termMajorant (commonD n) μ p N := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have hN1 : 1 ≤ N := le_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hNe
  have hμ0 : 0 ≤ μ := by obtain ⟨m, hm⟩ := hμ; rw [hm]; positivity
  exact abs_abstractRemainder_sub_le (commonQ_pos k hk) hμ hj hNe
    (gCutoff_bound ν h k β b hk hβ hb (by linarith) hN1 hN' hx)
    fun p hp => abs_gCoeff_le_indexBound ν h k β b hk hβ hb hR0 hx hp

/-- **Global ordered normalised remainders converge uniformly on joint data balls.** -/
theorem tendstoUniformlyOn_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => gRemainder ν h k β b x μ j N)
      (fun x => gCoeff ν h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := tendsto_abstract_majorant (commonQ k) (commonD n) μ j
    (gCutoffConst ν h k β b (μ + 1) R) (gIndexBound ν h k β b R μ)
  have hev := hmaj.eventually (gt_mem_nhds hε)
  have hthr : ∀ᶠ N : ℝ in atTop, ∀ I, 1 ≤ boxScale (k I) (b I) N := by
    rw [Filter.eventually_all]
    intro I
    have hc0 : 0 < (b I) ^ (2 * ∑ i, k I i) := by have := hb I; positivity
    filter_upwards [eventually_ge_atTop (1 / (b I) ^ (2 * ∑ i, k I i))] with N hN
    unfold boxScale
    rwa [div_le_iff₀ hc0] at hN
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), hthr] with N hNε hNe hN' x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_gRemainder_sub_le ν h k β b hk hβ hb hμ hj hx' hNe hN') hNε

end Grammar
