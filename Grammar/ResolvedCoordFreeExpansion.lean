/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedMomentRepresentation
import Grammar.ChartCoefficientTensors

/-!
# The coordinate-free expansion theorem (CCCIII)

Unit 7 of the coordinate-free programme (`tide-log/plan_coordinate_free_expansion.md`): the
target statement `HasCoordFreeExpansion` of CCXCIX is proved from a resolved certificate (CCC)
together with a **coefficient certificate** (`CoefficientCertificate`): along every chart the
density factor has a `b`-weighted ℓ¹ Taylor family `cc`, the observable's Taylor family
`jetFamily (φ∘π∘Φ_s∘e_s)` is `b`-weighted ℓ¹, and the chart's amplitude datum is their Cauchy
product (`datum_eq`, the analytic content of `amplitude_eq`).

* `chartTensor J s r q` — the chart coefficient tensor (CCCII) transported to the normal space
  `N_s` along the frame; `chartTensor_pair`: its pairing with the normal differential
  `D^r_⊥(φ∘π)(s)` is the box pairing with `D^r(φ∘π∘Φ_s∘e_s)(0)`.
* `dataBoxCoeff_eq_tsum` — **the per-point identity**: the paper's canonical coefficient of the
  chart datum at `s` is `∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{J,r,q}(s)⟩`.
* `stratumMeasure I` — the stratum density `ν_I`: the sum over the charts presenting `S_I` of the
  pushforwards of their base measures; `field` — the moment coefficient field
  `B_{I,r,q}(s) = ∑_J (dν_J/dν_I)(s) · B_{J,r,q}(s)` (Radon–Nikodym weights, so that the
  charts' contributions add up to a single stratum integral without any disjointness hypothesis).
* ★★ `expansionCoefficient_eq_gCoeff` — the coordinate-free expansion coefficients are the
  library's assembled canonical coefficients `gCoeff`.
* ★★★ `hasCoordFreeExpansion` — **THE COORDINATE-FREE EXPANSION**: for the original integral
  `∫_W φ ϕ e^{−nK}` and every cutoff `A`,
  `∫_W φ ϕ e^{−nK} − ∑_{(α,j) : α < max(A+1,1)} n^{−α}(log n)^j
      ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,α,j}(s)⟩ dν_I(s) = o(n^{−A})`.
  The statement mentions only the strata of the exceptional divisor, the normal differentials,
  the moment-tensor coefficient fields, the stratum densities and `π`; the charts live inside
  the certificates.

Non-claims: the certificates are hypotheses (their production from a monomial atlas is the
remaining geometric work); the coefficient fields are canonical only through the certificate
(the stratum densities and the tensor fields are determined jointly, as in the paper).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)}
  {K ϕ φ : (Fin d → ℝ) → ℝ}

namespace ResolvedCertificate

variable (C : ResolvedCertificate R D W K ϕ φ)

/-- **A coefficient certificate**: along every chart, a `b`-weighted ℓ¹ **factorisation family**
`cc` (the intended reading is the Taylor family of the density factor `c(s, ·)`, but the
certificate only asks for the factorisation below), the `b`-weighted ℓ¹ summability of the
observable's Taylor family, and the identification of the chart's amplitude datum with the
Cauchy product `cc ⋆ jetFamily`. -/
structure CoefficientCertificate where
  /-- The factorisation family at the base point `s` (intended: the Taylor family of `c(s, ·)`). -/
  cc : ∀ J, ↥(C.base J) → CoeffFamily (C.n J + 1)
  cc_abs : ∀ J s, AbsSummableAt (cc J s) (C.adapted.b J)
  /-- The observable's Taylor family on the box is `b`-weighted ℓ¹. -/
  jet_abs : ∀ J s,
    AbsSummableAt (jetFamily (C.n J) ((C.adapted.chart J).obsFibre s)) (C.adapted.b J)
  /-- The amplitude datum is the Cauchy product of the density family and the observable's
  Taylor family. -/
  datum_eq : ∀ J s, toEta (C.adapted.b J) ((C.adapted.chart J).x s) =
    CoeffFamily.conv (cc J s) (jetFamily (C.n J) ((C.adapted.chart J).obsFibre s))

/-! ### Stratum measures -/

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem b_eq (J : Fin C.M) : C.adapted.b J = (C.adapted.chart J).b := rfl

omit [MeasurableSpace A] [BorelSpace A] in
theorem measurableSet_base (J : Fin C.M) : MeasurableSet (C.base J) :=
  (C.isCompact_base J).isClosed.measurableSet

omit [MeasurableSpace A] [BorelSpace A] in
theorem measurableEmbedding_val (J : Fin C.M) :
    MeasurableEmbedding (Subtype.val : ↥(C.base J) → R.Stratum (C.strat J)) :=
  MeasurableEmbedding.subtype_coe (C.measurableSet_base J)

/-- The pushforward of the chart base measure to its stratum. -/
noncomputable def pushedMeasure (J : Fin C.M) : Measure (R.Stratum (C.strat J)) :=
  (C.adapted.ν J).map Subtype.val

instance (J : Fin C.M) : IsFiniteMeasure (C.pushedMeasure J) := Measure.isFiniteMeasure_map _ _

/-- Transport of a measure along an identification of strata. -/
def transportMeasure {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (μ : Measure (R.Stratum (C.strat J))) : Measure (R.Stratum I) := by
  subst hJ
  exact μ

/-- Transport of a function along an identification of strata. -/
def transportFun {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (f : R.Stratum (C.strat J) → ℝ) : R.Stratum I → ℝ := by
  subst hJ
  exact f

/-- The point of `S_{strat J}` underlying a point of `S_I`, `strat J = I`. -/
def ofStratum {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) (s : R.Stratum I) :
    R.Stratum (C.strat J) := ⟨s.1, hJ ▸ s.2⟩

/-- Transport of a tensor field along an identification of strata. -/
def transportTensor {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) (r : ℕ)
    (T : ∀ s : R.Stratum (C.strat J), MomentTensor (D.N (C.strat J) s) r) :
    ∀ s : R.Stratum I, MomentTensor (D.N I s) r := by
  subst hJ
  exact T

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem transportFun_apply {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (f : R.Stratum (C.strat J) → ℝ) (s : R.Stratum I) :
    C.transportFun hJ f s = f (C.ofStratum hJ s) := by
  subst hJ
  rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem transportTensor_pair {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) (r : ℕ)
    (T : ∀ s : R.Stratum (C.strat J), MomentTensor (D.N (C.strat J) s) r) (s : R.Stratum I) :
    (C.transportTensor hJ r T s).pair (D.normalDifferential φ I s r) =
      (T (C.ofStratum hJ s)).pair (D.normalDifferential φ (C.strat J) (C.ofStratum hJ s) r) := by
  subst hJ
  rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem integral_transport {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (f : R.Stratum (C.strat J) → ℝ) (μ : Measure (R.Stratum (C.strat J))) :
    ∫ s, C.transportFun hJ f s ∂C.transportMeasure hJ μ = ∫ s, f s ∂μ := by
  subst hJ
  rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem integrable_transport_iff {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (f : R.Stratum (C.strat J) → ℝ) (μ : Measure (R.Stratum (C.strat J))) :
    Integrable (C.transportFun hJ f) (C.transportMeasure hJ μ) ↔ Integrable f μ := by
  subst hJ
  exact Iff.rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem transportMeasure_univ {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (μ : Measure (R.Stratum (C.strat J))) : C.transportMeasure hJ μ univ = μ univ := by
  subst hJ
  rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem isFiniteMeasure_transportMeasure {J : Fin C.M} {I : Finset R.Component}
    (hJ : C.strat J = I) (μ : Measure (R.Stratum (C.strat J))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.transportMeasure hJ μ) :=
  ⟨by rw [C.transportMeasure_univ]; exact measure_lt_top _ _⟩

/-- **The stratum density** `ν_I`: the sum over the charts presenting `S_I` of the pushforwards
of their base measures. -/
noncomputable def stratumMeasure (I : Finset R.Component) : Measure (R.Stratum I) :=
  ∑ J, if hJ : C.strat J = I then C.transportMeasure hJ (C.pushedMeasure J) else 0

instance (I : Finset R.Component) : IsFiniteMeasure (C.stratumMeasure I) := by
  refine ⟨?_⟩
  unfold stratumMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J _ => ?_
  split_ifs with hJ
  · rw [C.transportMeasure_univ]
    exact measure_lt_top _ _
  · simp

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem pushed_le {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) :
    C.transportMeasure hJ (C.pushedMeasure J) ≤ C.stratumMeasure I := by
  have := Finset.single_le_sum
    (f := fun J' => if hJ' : C.strat J' = I then C.transportMeasure hJ' (C.pushedMeasure J') else 0)
    (fun J' _ => Measure.zero_le _) (Finset.mem_univ J)
  simp only [dif_pos hJ] at this
  unfold ResolvedCertificate.stratumMeasure
  exact this

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem pushed_ac {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) :
    C.transportMeasure hJ (C.pushedMeasure J) ≪ C.stratumMeasure I :=
  Measure.absolutelyContinuous_of_le (C.pushed_le hJ)

/-- The Radon–Nikodym weight `dν_J/dν_I` of a chart in its stratum density. -/
noncomputable def weight {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (s : R.Stratum I) : ℝ :=
  ((C.transportMeasure hJ (C.pushedMeasure J)).rnDeriv (C.stratumMeasure I) s).toReal

/-! ### The coefficient tensors on the strata -/

namespace CoefficientCertificate

variable {C} (Cc : C.CoefficientCertificate)

/-- The chart coefficient tensor at a base point, transported to the normal space along the
frame. -/
noncomputable def chartTensor (J : Fin C.M) (s : ↥(C.base J)) (r : ℕ) (q : PowerLogIndex) :
    MomentTensor (D.N (C.strat J) s.1) r :=
  (chartMomentCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J) q.exponent
    q.logDegree (Cc.cc J s) r).pushFrame
    (C.frame J s : (Fin (C.n J + 1) → ℝ) →L[ℝ] D.N (C.strat J) s.1)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- **Frame covariance of the coefficient tensors**: the pairing with the normal differential is
the box pairing with the normal jet of the fibre observable. -/
theorem chartTensor_pair (J : Fin C.M) (s : ↥(C.base J)) (r : ℕ) (q : PowerLogIndex) :
    (Cc.chartTensor J s r q).pair (D.normalDifferential φ (C.strat J) s.1 r) =
      chartMomentCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J) q.exponent
        q.logDegree (Cc.cc J s) r (normalJet ((C.adapted.chart J).obsFibre s) r) := by
  unfold chartTensor
  rw [MomentTensor.pushFrame_pair]
  unfold MomentTensor.pair
  congr 1
  have h := rawNormalJet_comp_equiv (D.N (C.strat J)) (D.Φ (C.strat J)) (φ ∘ R.π) s.1
    (C.frame J s) r
  have hfun : (fun v : Fin (C.n J + 1) → ℝ => (φ ∘ R.π) (D.Φ (C.strat J) s.1 (C.frame J s v))) =
      (C.adapted.chart J).obsFibre s := by
    funext v
    rw [C.obsFibre_eq]
    rfl
  rw [hfun] at h
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential
  exact h.symm

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- **The per-point identity**: the canonical coefficient of the chart datum at `s` is the
normal-order series of the pairings of the normal differentials with the coefficient tensors. -/
theorem hasSum_chartTensor_pair (J : Fin C.M) (s : ↥(C.base J)) (q : PowerLogIndex) :
    HasSum (fun r : ℕ => (r.factorial : ℝ)⁻¹ *
        (Cc.chartTensor J s r q).pair (D.normalDifferential φ (C.strat J) s.1 r))
      (dataBoxCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
        ((C.adapted.chart J).x s) q.exponent q.logDegree) := by
  unfold dataBoxCoeff
  rw [toXi_eq_zero ((C.adapted.chart J).fluct_zero s), Cc.datum_eq J s]
  have h := hasSum_inv_factorial_mul_chartMomentCoeff (C.n J) (C.adapted.h J) (C.adapted.k J)
    C.β (C.adapted.b J) q.exponent q.logDegree (C.adapted.k_pos J) C.β_pos (C.adapted.b_pos J)
    (Cc.cc_abs J s) (Cc.jet_abs J s)
  refine h.congr_fun fun r => ?_
  rw [Cc.chartTensor_pair]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem dataBoxCoeff_eq_tsum (J : Fin C.M) (s : ↥(C.base J)) (q : PowerLogIndex) :
    dataBoxCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
        ((C.adapted.chart J).x s) q.exponent q.logDegree =
      ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
        (Cc.chartTensor J s r q).pair (D.normalDifferential φ (C.strat J) s.1 r) :=
  (Cc.hasSum_chartTensor_pair J s q).tsum_eq.symm

open Classical in
/-- The chart coefficient tensor extended by zero off the compact base. -/
noncomputable def chartTensorExt (J : Fin C.M) (s : R.Stratum (C.strat J)) (r : ℕ)
    (q : PowerLogIndex) : MomentTensor (D.N (C.strat J) s) r :=
  if hs : s ∈ C.base J then Cc.chartTensor J ⟨s, hs⟩ r q else 0

/-- The normal-order series of a chart at a point of its stratum. -/
noncomputable def chartSeries (J : Fin C.M) (q : PowerLogIndex) (s : R.Stratum (C.strat J)) : ℝ :=
  ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
    (Cc.chartTensorExt J s r q).pair (D.normalDifferential φ (C.strat J) s r)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem summable_chartTensorExt_pair (J : Fin C.M) (s : R.Stratum (C.strat J)) (q : PowerLogIndex) :
    Summable fun r : ℕ => (r.factorial : ℝ)⁻¹ *
      (Cc.chartTensorExt J s r q).pair (D.normalDifferential φ (C.strat J) s r) := by
  by_cases hs : s ∈ C.base J
  · have := (Cc.hasSum_chartTensor_pair J ⟨s, hs⟩ q).summable
    refine this.congr fun r => ?_
    unfold chartTensorExt
    rw [dif_pos hs]
  · refine (summable_zero : Summable fun _ : ℕ => (0 : ℝ)).congr fun r => ?_
    unfold chartTensorExt
    rw [dif_neg hs]
    change (0 : ℝ) = (r.factorial : ℝ)⁻¹ * (0 : MomentTensor (D.N (C.strat J) s) r) _
    rw [zero_apply, mul_zero]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem chartSeries_val (J : Fin C.M) (q : PowerLogIndex) (s : ↥(C.base J)) :
    Cc.chartSeries J q s.1 = dataBoxCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β
      (C.adapted.b J) ((C.adapted.chart J).x s) q.exponent q.logDegree := by
  rw [Cc.dataBoxCoeff_eq_tsum]
  unfold chartSeries
  refine tsum_congr fun r => ?_
  unfold chartTensorExt
  rw [dif_pos s.2]

omit [MeasurableSpace A] [BorelSpace A] in
theorem integrable_chartSeries (J : Fin C.M) (q : PowerLogIndex) :
    Integrable (Cc.chartSeries J q) (C.pushedMeasure J) := by
  unfold ResolvedCertificate.pushedMeasure
  rw [(C.measurableEmbedding_val J).integrable_map_iff]
  have heq : Cc.chartSeries J q ∘ (Subtype.val : ↥(C.base J) → R.Stratum (C.strat J)) =
      fun s => dataBoxCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
        ((C.adapted.chart J).x s) q.exponent q.logDegree :=
    funext fun s => Cc.chartSeries_val J q s
  rw [heq]
  exact integrable_dataBoxCoeff_tan (C.adapted.ν J) (C.n J) (C.adapted.h J) (C.adapted.k J)
    (C.adapted.k_pos J) C.β C.β_pos (C.adapted.b_pos J) _ _ _

omit [MeasurableSpace A] [BorelSpace A] in
/-- The chart integral of the normal-order series is the chart's integrated canonical
coefficient. -/
theorem integral_chartSeries (J : Fin C.M) (q : PowerLogIndex) :
    ∫ s, Cc.chartSeries J q s ∂C.pushedMeasure J =
      tanCoeff (C.adapted.ν J) (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
        (C.adapted.x.chart J) q.exponent q.logDegree := by
  unfold ResolvedCertificate.pushedMeasure
  rw [(C.measurableEmbedding_val J).integral_map]
  unfold tanCoeff
  exact integral_congr_ae (Eventually.of_forall fun s => Cc.chartSeries_val J q s)

/-- **The moment coefficient field** `B_{I,r,q}(s) = ∑_J (dν_J/dν_I)(s) · B_{J,r,q}(s)`. -/
noncomputable def field : D.MomentCoefficientField := fun I r q s =>
  ∑ J, if hJ : C.strat J = I then
    C.weight hJ s • C.transportTensor hJ r (fun s' => Cc.chartTensorExt J s' r q) s else 0

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The normal-order series of the field is the weighted sum of the chart series. -/
theorem tsum_field_pair (I : Finset R.Component) (q : PowerLogIndex) (s : R.Stratum I) :
    ∑' r : ℕ, (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r) =
      ∑ J, if hJ : C.strat J = I then C.weight hJ s * C.transportFun hJ (Cc.chartSeries J q) s
        else 0 := by
  have hterm : ∀ r : ℕ, (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)
      = ∑ J, if hJ : C.strat J = I then C.weight hJ s * ((r.factorial : ℝ)⁻¹ *
          (Cc.chartTensorExt J (C.ofStratum hJ s) r q).pair
            (D.normalDifferential φ (C.strat J) (C.ofStratum hJ s) r)) else 0 := by
    intro r
    unfold field MomentTensor.pair
    rw [sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    split_ifs with hJ
    · rw [smul_apply, smul_eq_mul]
      have := C.transportTensor_pair hJ r (fun s' => Cc.chartTensorExt J s' r q) s
      unfold MomentTensor.pair at this
      rw [this]
      ring
    · rw [zero_apply, mul_zero]
  rw [tsum_congr hterm, Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun J _ => ?_
    split_ifs with hJ
    · rw [tsum_mul_left, C.transportFun_apply]
      rfl
    · exact tsum_zero
  · intro J _
    split_ifs with hJ
    · exact (Cc.summable_chartTensorExt_pair J (C.ofStratum hJ s) q).mul_left _
    · exact summable_zero

omit [MeasurableSpace A] [BorelSpace A] in
theorem integrable_weight_mul (I : Finset R.Component) (q : PowerLogIndex) (J : Fin C.M)
    (hJ : C.strat J = I) :
    Integrable (fun s => C.weight hJ s * C.transportFun hJ (Cc.chartSeries J q) s)
      (C.stratumMeasure I) := by
  have := C.isFiniteMeasure_transportMeasure hJ (C.pushedMeasure J)
  have := (integrable_rnDeriv_smul_iff (C.pushed_ac hJ)
    (f := C.transportFun hJ (Cc.chartSeries J q))).2
    ((C.integrable_transport_iff hJ _ _).2 (Cc.integrable_chartSeries J q))
  simpa [ResolvedCertificate.weight, smul_eq_mul] using this

omit [MeasurableSpace A] [BorelSpace A] in
theorem integral_weight_mul (I : Finset R.Component) (q : PowerLogIndex) (J : Fin C.M)
    (hJ : C.strat J = I) :
    ∫ s, C.weight hJ s * C.transportFun hJ (Cc.chartSeries J q) s ∂C.stratumMeasure I =
      tanCoeff (C.adapted.ν J) (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
        (C.adapted.x.chart J) q.exponent q.logDegree := by
  have := C.isFiniteMeasure_transportMeasure hJ (C.pushedMeasure J)
  have := integral_rnDeriv_smul (C.pushed_ac hJ) (f := C.transportFun hJ (Cc.chartSeries J q))
  simp only [smul_eq_mul] at this
  unfold ResolvedCertificate.weight
  rw [this, C.integral_transport, Cc.integral_chartSeries]

omit [MeasurableSpace A] [BorelSpace A] in
/-- ★★ **The coordinate-free expansion coefficients are the assembled canonical coefficients.** -/
theorem expansionCoefficient_eq_gCoeff (q : PowerLogIndex) :
    D.expansionCoefficient C.stratumMeasure Cc.field φ q =
      gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x q.exponent
        q.logDegree := by
  unfold ResolvedNormalData.expansionCoefficient gCoeff
  have hI : ∀ I : Finset R.Component,
      ∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)
        ∂C.stratumMeasure I =
      ∑ J, if hJ : C.strat J = I then tanCoeff (C.adapted.ν J) (C.n J) (C.adapted.h J)
        (C.adapted.k J) C.β (C.adapted.b J) (C.adapted.x.chart J) q.exponent q.logDegree
        else 0 := by
    intro I
    simp_rw [Cc.tsum_field_pair I q]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs with hJ
      · exact Cc.integral_weight_mul I q J hJ
      · exact integral_zero _ _
    · intro J _
      split_ifs with hJ
      · exact Cc.integrable_weight_mul I q J hJ
      · exact integrable_zero _ _ _
  simp_rw [hI]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  exact Fintype.sum_dite_eq (C.strat J) fun I _ => tanCoeff (C.adapted.ν J) (C.n J)
    (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J) (C.adapted.x.chart J) q.exponent
    q.logDegree

end CoefficientCertificate

end ResolvedCertificate

/-! ### The spectrum and the little-o bookkeeping -/

/-- Power–log indices from pairs. -/
def PowerLogIndex.ofPair : ℝ × ℕ ↪ PowerLogIndex where
  toFun p := ⟨p.1, p.2⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨c, e⟩ h
    simp only [PowerLogIndex.mk.injEq] at h
    exact Prod.ext h.1 h.2

/-- The cutoff exponent `max (A+1) 1`. -/
noncomputable def cutoffExponent (A : ℝ) : ℝ := max (A + 1) 1

/-- **The spectrum below the cutoff**: the lattice points `α ∈ Q⁻¹ℕ`, `α < max(A+1,1)`, with all
log degrees `j ≤ D`. -/
noncomputable def spectrumBelow (Q Dg : ℕ) (A : ℝ) : Finset PowerLogIndex :=
  (latticeBelow Q (cutoffExponent A) ×ˢ Finset.range (Dg + 1)).map PowerLogIndex.ofPair

theorem sum_spectrumBelow (Q Dg : ℕ) (A : ℝ) (c : ℝ → ℕ → ℝ) (N : ℝ) :
    ∑ q ∈ spectrumBelow Q Dg A, c q.exponent q.logDegree * q.scale N =
      absSpectralSum Q Dg c (cutoffExponent A) N := by
  unfold spectrumBelow absSpectralSum
  rw [Finset.sum_map, Finset.sum_product]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold PowerLogIndex.scale
  change c μ j * (N ^ (-μ) * Real.log N ^ j) = N ^ (-μ) * (c μ j * Real.log N ^ j)
  ring

/-- `(1 + log n)^D = o(n)`. -/
theorem isLittleO_one_add_log_pow_id (Dg : ℕ) :
    (fun n : ℝ => (1 + Real.log n) ^ Dg) =o[atTop] fun n : ℝ => n := by
  have h1 : (fun n : ℝ => (1 + Real.log n) ^ Dg) =O[atTop] fun n => Real.log n ^ Dg := by
    refine IsBigO.of_bound (2 ^ Dg) ?_
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith), ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) Dg
  exact h1.trans_isLittleO Real.isLittleO_pow_log_id_atTop

/-- `n^{−(A+1)} (1 + log n)^D = o(n^{−A})`. -/
theorem isLittleO_rpow_mul_one_add_log_pow (A : ℝ) (Dg : ℕ) :
    (fun n : ℝ => n ^ (-(A + 1)) * (1 + Real.log n) ^ Dg) =o[atTop] fun n : ℝ => n ^ (-A) := by
  have h := (isBigO_refl (fun n : ℝ => n ^ (-(A + 1))) atTop).mul_isLittleO
    (isLittleO_one_add_log_pow_id Dg)
  refine h.trans_isBigO (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [one_mul, ← Real.rpow_add_one hn.ne']
  rw [show -(A + 1) + 1 = -A by ring]

/-- The remainder scale at a cutoff `L ≥ A + 1` is `o(n^{−A})`. -/
theorem isLittleO_rpow_cutoff_mul (A : ℝ) (Dg : ℕ) :
    (fun n : ℝ => n ^ (-cutoffExponent A) * (1 + Real.log n) ^ Dg) =o[atTop]
      fun n : ℝ => n ^ (-A) := by
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) (isLittleO_rpow_mul_one_add_log_pow A Dg)
  filter_upwards [eventually_ge_atTop (Real.exp 0)] with n hn
  have hn1 : 1 ≤ n := by rwa [Real.exp_zero] at hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log n)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
  unfold cutoffExponent
  have := le_max_left (A + 1) 1
  linarith

/-! ### The theorem -/

namespace ResolvedCertificate.CoefficientCertificate

variable {C : ResolvedCertificate R D W K ϕ φ} (Cc : C.CoefficientCertificate)

omit [MeasurableSpace A] [BorelSpace A] in
/-- ★★★ **THE COORDINATE-FREE EXPANSION** of the original integral `∫_W φ ϕ e^{−nK}`: for every
cutoff `A`, with the stratum densities `ν_I` and the moment coefficient fields `B_{I,r,α,j}`
determined by the certificates,
`∫_W φ ϕ e^{−nK} − ∑_{(α,j), α < max(A+1,1), j ≤ D} n^{−α}(log n)^j
  ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,α,j}(s)⟩ dν_I(s) = o(n^{−A})`.
The coefficient formula uses only the strata of the exceptional divisor, the normal differentials
(chosen normal jets), the coefficient tensor fields, the stratum densities and `π`; the charts enter
the certificates and the construction of `(ν_I, B_{I,r,α,j})`. Independence of the individual fields
from the chart choices is NOT asserted (only the assembled scalar coefficients are candidates for
asymptotic uniqueness), and this is the expansion of the unnormalised integral. -/
theorem hasCoordFreeExpansion (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
    (hφ : Measurable φ) :
    D.HasCoordFreeExpansion C.stratumMeasure Cc.field
      (spectrumBelow (commonQ C.adapted.k) (commonD C.n)) W K ϕ φ := by
  intro Ac
  have hcut : 0 < cutoffExponent Ac := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Kc, hKc⟩ := C.cutoffExpansion_globalLaplace hK hϕ hϕ0 hφ (cutoffExponent Ac) hcut
  have hsum : ∀ n : ℝ, ∑ q ∈ spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac,
      D.expansionCoefficient C.stratumMeasure Cc.field φ q * q.scale n =
      absSpectralSum (commonQ C.adapted.k) (commonD C.n)
        (gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x)
        (cutoffExponent Ac) n := by
    intro n
    rw [← sum_spectrumBelow]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Cc.expansionCoefficient_eq_gCoeff]
  simp_rw [hsum]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound Kc ?_)
    (isLittleO_rpow_cutoff_mul Ac (commonD C.n))
  filter_upwards [hKc, eventually_ge_atTop (Real.exp 0)] with n hn hn1
  have hn1' : 1 ≤ n := by rwa [Real.exp_zero] at hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))]
  exact hn

end ResolvedCertificate.CoefficientCertificate

end Grammar
