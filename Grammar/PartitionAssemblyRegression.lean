/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableNoActiveAssembly
import Grammar.VariableUnitSquareExample

/-!
# A two-chart partition regression (CCLXXII)

`K(x) = x²` on `[−1, 1]`, covered by two overlapping identity charts `[−1, 1]` and `[−1/2, 1/2]`
(both centred at the divisor point `0`), with the supplied partition of unity
`ψ₂ = ½·bump` (a continuous bump equal to `1` on `[−1/4, 1/4]` and `0` off `(−1/2, 1/2)`) and
`ψ₁ = 1 − ψ₂`, relatively subordinate to the chart images. Through the hact-free partition assembly
(CCLXIX):

* each chart carries the pair `(1/2, 0)` and the coefficient `√π · ψ_i(0) = √π/2`
  (`chartCoeff'_eq`), so the two weighted coefficients sum to `√π` (`partitionCoeff'_eq`) — the
  coefficient of the unpartitioned integral (CCXLIX's `√π` for `y₀²y₁²` is the two-dimensional
  analogue; here `∫_{−1}^{1} e^{−N x²} dx ~ √π N^{−1/2}`);
* ★ `integral_isEquivalent`: `∫_{[−1,1]} e^{−N x²} dx ~ √π · N^{−1/2}`, obtained by summing the two
  one-chart certificates with priors `ψ₁`, `ψ₂` — the genuine supplied-partition theorem exercised
  end to end (consult #84 unit 5).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace TwoChartExample

/-! ### The one-dimensional identity chart on `[−b, b]` -/

/-- The interval `[−b, b]` in `Fin 1 → ℝ`. -/
def interval (b : ℝ) : Set (Fin 1 → ℝ) := Set.pi univ fun _ => Icc (-b) b

theorem isCompact_interval (b : ℝ) : IsCompact (interval b) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem mem_interval {b : ℝ} {x : Fin 1 → ℝ} : x ∈ interval b ↔ |x 0| ≤ b := by
  unfold interval
  simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor
  · intro h
    exact ⟨(h 0).1, (h 0).2⟩
  · intro h j
    rw [Subsingleton.elim j 0]
    exact ⟨h.1, h.2⟩

/-- The identity chart on `[−b, b]`. -/
def chart (b : ℝ) : ResolutionChart 1 where
  dom := interval b
  dom_compact := isCompact_interval b
  φ := id
  U := univ
  U_open := isOpen_univ
  dom_subset := subset_univ _
  smooth := contDiffOn_id
  E := ∅
  E_subset := empty_subset _
  E_closed := isClosed_empty
  E_null := measure_empty
  inj := injOn_id _

/-- The exponent `2`. -/
noncomputable def e2 : Fin 1 →₀ ℕ := Finsupp.single 0 2

theorem e2_apply (j : Fin 1) : e2 j = 2 := by
  rw [Subsingleton.elim j 0]
  exact Finsupp.single_eq_same

theorem e2_support : e2.support = Finset.univ := by
  ext j
  simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true, e2_apply]
  norm_num

/-- The phase `K(x) = x²`. -/
noncomputable def K (y : Fin 1 → ℝ) : ℝ := monomialEval y e2

theorem K_eq (y : Fin 1 → ℝ) : K y = y 0 ^ 2 := by
  unfold K monomialEval e2
  exact Finsupp.prod_single_index (pow_zero _)

theorem K_nonneg (y : Fin 1 → ℝ) : 0 ≤ K y := by
  rw [K_eq]
  positivity

theorem continuous_K : Continuous K := by
  have : K = fun y => y 0 ^ 2 := funext K_eq
  rw [this]
  fun_prop

theorem hK : Measurable K := continuous_K.measurable

theorem det_id_eq (y : Fin 1 → ℝ) : (fderiv ℝ (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y).det = 1 := by
  rw [fderiv_id]
  exact LinearMap.det_id

theorem interval_eq_productDom (b : ℝ) :
    interval b = productDom e2.support ({0} : Set (Fin 1 → ℝ)) b := by
  ext y
  rw [mem_interval]
  simp only [productDom, e2_support, Set.mem_ofPred_eq, Finset.mem_univ, mem_singleton_iff,
    true_implies]
  constructor
  · intro hy
    refine ⟨funext fun j => zeroOn_apply_of_mem _ (Finset.mem_univ j) y, fun j => ?_⟩
    rw [Subsingleton.elim j 0]
    exact hy
  · rintro ⟨-, hy⟩
    exact hy 0

theorem isMonomialChart (b : ℝ) :
    IsMonomialChart K (chart b).φ (chart b).dom e2 0 univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_id
  injOn := injOn_id _
  exists_unit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change K y = 1 * monomialEval y e2
    rw [one_mul]
    rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change (fderiv ℝ (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y).det = 1 * monomialEval y 0
    rw [det_id_eq, monomialEval_zero, one_mul]⟩

/-- **The one-chart variable-unit package of `[−b, b]`.** -/
noncomputable def package (b : ℝ) (hb : 0 < b) :
    ProductMonomialChartVar (ResolutionCover.ofChart (chart b)) () K where
  e := e2
  h := 0
  W := univ
  W_open := isOpen_univ
  dom_subset := subset_univ _
  monomial := isMonomialChart b
  u := fun _ => 1
  u_cont := continuousOn_const
  u_ne := fun _ _ => one_ne_zero
  phase_eq := fun y _ => by
    change K y = 1 * monomialEval y e2
    rw [one_mul]
    rfl
  v := fun _ => 1
  v_cont := continuousOn_const
  det_eq := fun y _ => by
    change (fderiv ℝ (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) y).det = 1 * monomialEval y 0
    rw [det_id_eq, monomialEval_zero, one_mul]
  T := {0}
  T_compact := isCompact_singleton
  T_nonempty := singleton_nonempty _
  T_zero := fun x hx j _ => by rw [mem_singleton_iff.1 hx]; rfl
  b := b
  b_pos := hb
  dom_eq := interval_eq_productDom b
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ (chart b) hy

/-! ### The coefficient of one chart with a general prior -/

section OneChart

variable (b : ℝ) (hb : 0 < b) (q : TubeWeight 1)

/-- The one-chart family. -/
noncomputable abbrev Qs :
    ∀ i : Unit, ProductMonomialChartVar (ResolutionCover.ofChart (chart b)) i K :=
  fun _ => package b hb

theorem e_eq : (Qs b hb ()).e = e2 := rfl

theorem h_eq : (Qs b hb ()).h = 0 := rfl

theorem ratio_eq (j : Fin 1) : (Qs b hb ()).ratio j = 1 / 2 := by
  change ((((0 : Fin 1 →₀ ℕ) j : ℕ) : ℝ) + 1) / ((e2 j : ℕ) : ℝ) = 1 / 2
  rw [e2_apply]
  simp

theorem zero_mem_support : (0 : Fin 1) ∈ (Qs b hb ()).e.support := by
  rw [e_eq, e2_support]
  exact Finset.mem_univ _

theorem isActive : (Qs b hb ()).IsActive := ⟨0, zero_mem_support b hb⟩

theorem hact : ((ResolutionCover.ofChart (chart b)).activeCoordsV (Qs b hb)).Nonempty :=
  ⟨⟨(), 0⟩, (ResolutionCover.ofChart (chart b)).mem_activeCoordsV (Qs b hb) (zero_mem_support b hb)⟩

theorem coverLamV_eq :
    (ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb) = 1 / 2 := by
  unfold ResolutionCover.coverLamV
  refine le_antisymm ((Finset.inf'_le _ ((ResolutionCover.ofChart (chart b)).mem_activeCoordsV
    (Qs b hb) (zero_mem_support b hb))).trans_eq (ratio_eq b hb 0))
    (Finset.le_inf' _ _ fun x _ => ?_)
  obtain ⟨i, j⟩ := x
  exact (ratio_eq b hb j).ge

theorem minimalSet_eq :
    (Qs b hb ()).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb)) =
      Finset.univ := by
  unfold ProductMonomialChartVar.minimalSet
  rw [coverLamV_eq, e_eq, e2_support]
  exact Finset.filter_true_of_mem fun j _ => ratio_eq b hb j

theorem coverDegV_eq : (ResolutionCover.ofChart (chart b)).coverDegV (Qs b hb) (hact b hb) = 0 := by
  unfold ResolutionCover.coverDegV
  rw [coverLamV_eq]
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Qs b hb i).e.support,
      (Qs b hb i).ratio j = 1 / 2) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨0, zero_mem_support b hb, ratio_eq b hb 0⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hall : ((Qs b hb default).e.support.filter fun j => (Qs b hb default).ratio j = 1 / 2) =
      Finset.univ := by
    rw [e_eq, e2_support]
    exact Finset.filter_true_of_mem fun j _ => ratio_eq b hb j
  rw [hall, Finset.card_univ, Fintype.card_fin]

theorem univ_subset_support : (Finset.univ : Finset (Fin 1)) ⊆ (Qs b hb ()).e.support := by
  rw [e_eq, e2_support]

instance : IsEmpty (Fin (1 - ((Finset.univ : Finset (Fin 1)).card - 1 + 1))) :=
  inferInstanceAs (IsEmpty (Fin 0))

theorem planeSplit_univ_zero (z : Fin (1 - ((Finset.univ : Finset (Fin 1)).card - 1 + 1)) → ℝ) :
    planeSplit (stratumSplit (Finset.univ : Finset (Fin 1)) Finset.univ_nonempty) (z, 0) = 0 := by
  funext j
  obtain ⟨a, ha⟩ := exists_inr_of_mem Finset.univ Finset.univ_nonempty (Finset.mem_univ j)
  rw [ha, planeSplit_stratum_inr]
  rfl

theorem tangentialMonomial_univ_h
    (z : Fin (1 - ((Finset.univ : Finset (Fin 1)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 1)) Finset.univ_nonempty
      (Qs b hb ()).h z = 1 := by
  unfold tangentialMonomial
  rw [h_eq, Finsupp.support_zero, Finset.filter_empty, Finset.prod_empty]

theorem tangentialMonomial_univ_e
    (z : Fin (1 - ((Finset.univ : Finset (Fin 1)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 1)) Finset.univ_nonempty
      (Qs b hb ()).e z = 1 := by
  unfold tangentialMonomial
  rw [Finset.filter_eq_empty_iff.2 fun j _ hj => hj (Finset.mem_univ j), Finset.prod_empty]

include hb in
theorem zero_mem_interval : (0 : Fin 1 → ℝ) ∈ interval b := by
  rw [mem_interval]
  simp only [Pi.zero_apply, abs_zero]
  exact hb.le

theorem zero_mem_pieceFootSet : (0 : Fin 1 → ℝ) ∈ (Qs b hb ()).pieceFootSet Finset.univ := by
  refine ⟨?_, fun _ _ => rfl, fun j _ hj => absurd (Finset.mem_univ j) hj⟩
  change zeroOn (Qs b hb ()).e.support (0 : Fin 1 → ℝ) ∈ ({0} : Set (Fin 1 → ℝ))
  rw [mem_singleton_iff]
  funext j
  by_cases hj : j ∈ (Qs b hb ()).e.support
  · exact zeroOn_apply_of_mem _ hj _
  · exact zeroOn_apply_of_notMem _ hj _

variable (hq0 : 0 < q.w 0) (ε : ℝ) (hε : 0 < ε) (hεb' : ε ≤ b)

include hq0 in
theorem dominantFace_eq_univ :
    (Qs b hb ()).dominantFace (fun i => (Qs b hb i).e.support) ε Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) q = univ := by
  refine eq_univ_of_forall fun z => ?_
  refine ⟨fun j _ hj => absurd (Finset.mem_univ j) hj, ?_, one_pos, ?_, one_pos, one_ne_zero, ?_⟩
  · rw [planeSplit_univ_zero]
    exact zero_mem_interval b hb
  · rw [planeSplit_univ_zero]
    exact hq0
  · rw [tangentialMonomial_univ_h]
    exact one_ne_zero

theorem volume_univ_base :
    (volume : Measure (Fin (1 - ((Finset.univ : Finset (Fin 1)).card - 1 + 1)) → ℝ)) univ = 1 := by
  rw [volume_pi]
  exact Measure.pi_empty_univ _

include hq0 in
theorem volume_dominantFace :
    0 < volume ((Qs b hb ()).dominantFace (fun i => (Qs b hb i).e.support) ε Finset.univ
      Finset.univ_nonempty (fun _ => (1 : ℝ)) q) := by
  rw [dominantFace_eq_univ b hb q hq0 ε, volume_univ_base]
  exact zero_lt_one

include hεb' in
theorem hεb : ∀ i, ε ≤ (Qs b hb i).b := fun _ => hεb'

theorem hFc : ∀ i, ContinuousOn (fun y => (fun _ : Fin 1 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart (chart b)).chart i).φ y)) (Qs b hb i).W :=
  fun _ => continuousOn_const

theorem hFm : Measurable fun _ : Fin 1 → ℝ => (1 : ℝ) := measurable_const

theorem hF : Integrable (fun x => (fun _ : Fin 1 → ℝ => (1 : ℝ)) x * q.w x)
    (volume.restrict (⋃ i, (ResolutionCover.ofChart (chart b)).image i)) := by
  rw [ResolutionCover.ofChart_iUnion_image]
  change Integrable _ (volume.restrict (id '' interval b))
  rw [Set.image_id]
  refine (Measure.integrableOn_of_bounded (isCompact_interval b).measure_lt_top.ne
    (M := q.bound) ?_ ?_)
  · exact (measurable_const.mul q.measurable).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (q.nonneg x)]
    exact q.le_bound x

variable (hqc : ∀ i, ContinuousOn (fun y => q.w (((ResolutionCover.ofChart (chart b)).chart i).φ y))
  (Qs b hb i).W)

theorem card_minimalSet :
    ((Qs b hb ()).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb)
      (hact b hb))).card = 1 := by
  rw [minimalSet_eq, Finset.card_univ, Fintype.card_fin]

theorem prod_minimalSet :
    ∏ j ∈ (Qs b hb ()).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb)
      (hact b hb)), 1 / ((Qs b hb ()).e j : ℝ) = 1 / 2 := by
  rw [minimalSet_eq, e_eq]
  simp only [e2_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

include hq0 hεb' in
/-- The face integral over the zero-dimensional base is the prior at the origin. -/
theorem integral_face_eq (I : Finset (Fin 1)) (hI : I = Finset.univ)
    (hIsub : I ⊆ (Qs b hb ()).e.support) (hne : I.Nonempty) :
    ∫ z in ((Qs b hb ()).pieceDensity (D := fun i => (Qs b hb i).e.support) hε (hεb b hb ε hεb' ())
        rfl I hIsub hne q).base,
      ((Qs b hb ()).pieceDensity (D := fun i => (Qs b hb i).e.support) hε (hεb b hb ε hεb' ()) rfl
        I hIsub hne q).beta z *
        (scalarPhase I hne (Qs b hb ()).u (Qs b hb ()).e z ^
            (-((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb))) *
          (ResolutionCover.ofChart (chart b)).pieceAmp () I hne (Qs b hb ()).h (Qs b hb ()).v
            (F := fun _ => (1 : ℝ)) (p := q) z 0) = q.w 0 := by
  subst hI
  have hbase : ((Qs b hb ()).pieceDensity (D := fun i => (Qs b hb i).e.support) hε
      (hεb b hb ε hεb' ()) rfl Finset.univ hIsub hne q).base = univ :=
    eq_univ_of_forall fun z => (Qs b hb ()).mem_pieceDensity_base_of_mem_dominantFace hε
      (hεb b hb ε hεb' ()) rfl Finset.univ hIsub hne q
      (by rw [dominantFace_eq_univ b hb q hq0 ε]; exact mem_univ z)
  have hone : ∀ z, ((Qs b hb ()).pieceDensity (D := fun i => (Qs b hb i).e.support) hε
      (hεb b hb ε hεb' ()) rfl Finset.univ hIsub hne q).beta z *
        (scalarPhase Finset.univ hne (Qs b hb ()).u (Qs b hb ()).e z ^
            (-((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb))) *
          (ResolutionCover.ofChart (chart b)).pieceAmp () Finset.univ hne (Qs b hb ()).h
            (Qs b hb ()).v (F := fun _ => (1 : ℝ)) (p := q) z 0) = q.w 0 := fun z => by
    rw [ProductMonomialChartVar.pieceDensity_beta, planeSplit_univ_zero,
      Set.indicator_of_mem (zero_mem_pieceFootSet b hb)]
    unfold scalarPhase tangentialUnit ResolutionCover.pieceAmp
    rw [tangentialMonomial_univ_e, tangentialMonomial_univ_h, planeSplit_univ_zero]
    change (1 : ℝ) * ((1 * 1) ^ (-((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb)
      (hact b hb))) * (|(1 : ℝ)| * |(1 : ℝ)| * q.w 0 * 1)) = q.w 0
    simp
  rw [setIntegral_congr_fun (hbase ▸ MeasurableSet.univ) fun z _ => hone z, hbase,
    Measure.restrict_univ, integral_const, measureReal_def, volume_univ_base]
  simp

theorem card_minimalSet_eq_succ :
    ((Qs b hb ()).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb)
      (hact b hb))).card =
      (ResolutionCover.ofChart (chart b)).coverDegV (Qs b hb) (hact b hb) + 1 := by
  rw [card_minimalSet, coverDegV_eq]

include hq0 hεb' in
/-- **The coefficient of the chart `[−b, b]` with prior `q` is `√π · q(0)`** (any cutoff `ε ≤ b`).
-/
theorem productCoeffV_eq :
    (ResolutionCover.ofChart (chart b)).productCoeffV (Qs b hb) K_nonneg hε (hεb b hb ε hεb')
      (hFc b hb) hqc hFm (hF b q) hK
      ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb))
      ((ResolutionCover.ofChart (chart b)).coverDegV (Qs b hb) (hact b hb)) =
      Real.sqrt Real.pi * q.w 0 := by
  have hsupp : ∀ i, ((Qs b hb i).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb)
      (hact b hb))).card = (ResolutionCover.ofChart (chart b)).coverDegV (Qs b hb) (hact b hb) + 1 →
      (Qs b hb i).minimalSet ((ResolutionCover.ofChart (chart b)).coverLamV (Qs b hb) (hact b hb)) =
        (Qs b hb i).e.support := by
    intro i _
    cases i
    rw [minimalSet_eq, e_eq, e2_support]
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart (chart b)).productCoeffV_extremal_eq_sum_minimal (Qs b hb)
    (hact b hb) K_nonneg hε (hεb b hb ε hεb') (hFc b hb) hqc hFm (hF b q) hK hsupp, hsum,
    dif_pos (card_minimalSet_eq_succ b hb)]
  rw [integral_face_eq b hb q hq0 ε hε hεb' _ (minimalSet_eq b hb), card_minimalSet,
    prod_minimalSet, coverLamV_eq, Real.Gamma_one_half_eq]
  norm_num [Nat.factorial]
  ring

end OneChart

/-! ### The two-chart cover and the partition -/

/-- The radii of the two charts. -/
noncomputable def rad : Fin 2 → ℝ := ![1, 1 / 2]

theorem rad_pos (i : Fin 2) : 0 < rad i := by
  fin_cases i <;> norm_num [rad]

/-- **The two-chart cover** `[−1, 1] ∪ [−1/2, 1/2]`. -/
noncomputable def R : ResolutionCover 1 (Fin 2) := ⟨fun i => chart (rad i)⟩

/-- The one-chart packages of the two charts. -/
noncomputable def Ps :
    ∀ i : Fin 2, ProductMonomialChartVar (ResolutionCover.ofChart (R.chart i)) () K :=
  fun i => package (rad i) (rad_pos i)

/-- The bump `ramp(−1/2, 1/4)(s) · ramp(−1/2, 1/4)(−s)`: `1` on `[−1/4, 1/4]`, `0` off
`(−1/2, 1/2)`. -/
noncomputable def bump (s : ℝ) : ℝ := ramp (-(1 / 2)) (1 / 4) s * ramp (-(1 / 2)) (1 / 4) (-s)

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s := mul_nonneg (ramp_nonneg _ _ _) (ramp_nonneg _ _ _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)

theorem continuous_bump : Continuous bump :=
  (continuous_ramp _ _).mul ((continuous_ramp _ _).comp continuous_neg)

theorem bump_zero : bump 0 = 1 := by
  unfold bump
  rw [neg_zero, ramp_eq_one_of_le (by norm_num) (by norm_num), one_mul]

theorem bump_eq_zero {s : ℝ} (hs : 1 / 2 ≤ |s|) : bump s = 0 := by
  unfold bump
  rcases le_abs'.1 hs with h | h
  · rw [ramp_eq_zero_of_le (by norm_num) (by linarith), zero_mul]
  · rw [ramp_eq_zero_of_le (c := -(1 / 2)) (s := -s) (by norm_num) (by linarith), mul_zero]

/-- The partition members: `ψ₁ = 1 − ½ bump`, `ψ₂ = ½ bump`. -/
noncomputable def ψ : Fin 2 → (Fin 1 → ℝ) → ℝ :=
  ![fun x => 1 - bump (x 0) / 2, fun x => bump (x 0) / 2]

theorem ψ_zero (x : Fin 1 → ℝ) : ψ 0 x = 1 - bump (x 0) / 2 := rfl

theorem ψ_one (x : Fin 1 → ℝ) : ψ 1 x = bump (x 0) / 2 := rfl

theorem ψ_nonneg (i : Fin 2) (x : Fin 1 → ℝ) : 0 ≤ ψ i x := by
  fin_cases i
  · change 0 ≤ 1 - bump (x 0) / 2
    linarith [bump_le_one (x 0)]
  · change 0 ≤ bump (x 0) / 2
    linarith [bump_nonneg (x 0)]

theorem ψ_le_one (i : Fin 2) (x : Fin 1 → ℝ) : ψ i x ≤ 1 := by
  fin_cases i
  · change 1 - bump (x 0) / 2 ≤ 1
    linarith [bump_nonneg (x 0)]
  · change bump (x 0) / 2 ≤ 1
    linarith [bump_le_one (x 0)]

theorem measurable_ψ (i : Fin 2) : Measurable (ψ i) := by
  fin_cases i
  · exact (continuous_const.sub
      ((continuous_bump.comp (continuous_apply 0)).div_const 2)).measurable
  · exact ((continuous_bump.comp (continuous_apply 0)).div_const 2).measurable

theorem sum_ψ (x : Fin 1 → ℝ) : ∑ i, ψ i x = 1 := by
  rw [Fin.sum_univ_two, ψ_zero, ψ_one]
  ring

theorem image_eq (i : Fin 2) : R.image i = interval (rad i) := by
  unfold ResolutionCover.image
  change id '' interval (rad i) = _
  rw [Set.image_id]

/-- Relative subordination: `ψ₂` vanishes off `[−1/2, 1/2]`. -/
theorem ψ_subord (i : Fin 2) (x : Fin 1 → ℝ) (_ : x ∈ ⋃ j, R.image j) (hx : x ∉ R.image i) :
    ψ i x = 0 := by
  rw [image_eq, mem_interval] at hx
  fin_cases i
  · exfalso
    apply hx
    obtain ⟨j, hxj⟩ := mem_iUnion.1 ‹x ∈ ⋃ j, R.image j›
    rw [image_eq, mem_interval] at hxj
    have hj : rad j ≤ 1 := by fin_cases j <;> norm_num [rad]
    change |x 0| ≤ 1
    exact hxj.trans hj
  · change bump (x 0) / 2 = 0
    rw [bump_eq_zero (not_le.1 hx).le, zero_div]

theorem continuous_ψ (i : Fin 2) : Continuous (ψ i) := by
  fin_cases i
  · exact continuous_const.sub ((continuous_bump.comp (continuous_apply 0)).div_const 2)
  · exact (continuous_bump.comp (continuous_apply 0)).div_const 2

/-- **The supplied partition of unity.** -/
noncomputable def P : SubordinatePartition R :=
  SubordinatePartition.ofPartition ψ measurable_ψ ψ_nonneg 1 ψ_le_one (fun x _ => sum_ψ x)
    fun i x hx hxi => ψ_subord i x hx hxi

theorem P_ψ : P.ψ = ψ := rfl

/-- The constant prior on `Fin 1 → ℝ`. -/
def one1 : TubeWeight 1 := ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩

theorem one1_w (x : Fin 1 → ℝ) : one1.w x = 1 := rfl

theorem Ps_b (i : Fin 2) : (Ps i).b = rad i := rfl

theorem Ps_W (i : Fin 2) : (Ps i).W = univ := rfl

theorem half_le_rad (i : Fin 2) : (1 / 2 : ℝ) ≤ rad i := by
  fin_cases i <;> norm_num [rad]

theorem hεbR : ∀ i, (1 / 2 : ℝ) ≤ (Ps i).b := fun i => half_le_rad i

theorem hpcR : ∀ i, ContinuousOn (fun y => one1.w ((R.chart i).φ y)) (Ps i).W :=
  fun _ => continuousOn_const

theorem hψR : ∀ i, ContinuousOn (fun y => P.ψ i ((R.chart i).φ y)) (Ps i).W :=
  fun i => (continuous_ψ i).continuousOn

theorem hFcR : ∀ i, ContinuousOn (fun y => (fun _ : Fin 1 → ℝ => (1 : ℝ)) ((R.chart i).φ y))
    (Ps i).W :=
  fun _ => continuousOn_const

theorem iUnion_image_eq : ⋃ i, R.image i = interval 1 := by
  refine subset_antisymm (iUnion_subset fun j => ?_) ?_
  · rw [image_eq]
    intro x hx
    rw [mem_interval] at hx ⊢
    exact hx.trans (by fin_cases j <;> norm_num [rad])
  · intro x hx
    exact mem_iUnion.2 ⟨0, by rw [image_eq]; exact hx⟩

theorem hFR : Integrable (fun x => (fun _ : Fin 1 → ℝ => (1 : ℝ)) x * one1.w x)
    (volume.restrict (⋃ i, R.image i)) := by
  rw [iUnion_image_eq]
  exact (integrableOn_const (C := (1 : ℝ)) (isCompact_interval 1).measure_lt_top.ne).congr
    (Eventually.of_forall fun x => by simp [one1_w])

theorem Ps_isActive (i : Fin 2) : (Ps i).IsActive := isActive (rad i) (rad_pos i)

theorem activeCharts_eq : R.activeCharts Ps = Finset.univ := by
  classical
  exact Finset.filter_true_of_mem fun i _ => Ps_isActive i

theorem hne : (R.activeCharts Ps).Nonempty := ⟨0, (R.mem_activeCharts Ps).2 (Ps_isActive 0)⟩

theorem chartLam'_eq (i : Fin 2) : R.chartLam' Ps i = 1 / 2 := by
  rw [R.chartLam'_of_active Ps (Ps_isActive i)]
  exact coverLamV_eq (rad i) (rad_pos i)

theorem chartDeg'_eq (i : Fin 2) : R.chartDeg' Ps i = 0 := by
  rw [R.chartDeg'_of_active Ps (Ps_isActive i)]
  exact coverDegV_eq (rad i) (rad_pos i)

theorem partitionLam'_eq : R.partitionLam' Ps hne = 1 / 2 := by
  unfold ResolutionCover.partitionLam' extremalExponent
  refine le_antisymm ((Finset.inf'_le _ ((R.mem_activeCharts Ps).2 (Ps_isActive 0))).trans_eq
    (chartLam'_eq 0)) (Finset.le_inf' _ _ fun i _ => (chartLam'_eq i).ge)

theorem partitionDeg'_eq : R.partitionDeg' Ps hne = 0 := by
  unfold ResolutionCover.partitionDeg' extremalDegree
  exact le_antisymm (Finset.sup'_le _ _ fun i _ => (chartDeg'_eq i).le) (Nat.zero_le _)

theorem tiedCharts'_eq : R.tiedCharts' Ps hne = Finset.univ := by
  classical
  unfold ResolutionCover.tiedCharts'
  rw [activeCharts_eq]
  exact Finset.filter_true_of_mem fun i _ =>
    ⟨(chartLam'_eq i).trans partitionLam'_eq.symm, (chartDeg'_eq i).trans partitionDeg'_eq.symm⟩

theorem ψ_at_zero (i : Fin 2) : ψ i 0 = 1 / 2 := by
  fin_cases i
  · change 1 - bump ((0 : Fin 1 → ℝ) 0) / 2 = 1 / 2
    rw [Pi.zero_apply, bump_zero]
    norm_num
  · change bump ((0 : Fin 1 → ℝ) 0) / 2 = 1 / 2
    rw [Pi.zero_apply, bump_zero]

/-- **Each chart contributes `√π · ψ_i(0) = √π/2`.** -/
theorem chartCoeff'_eq (i : Fin 2) :
    R.chartCoeff' Ps P K_nonneg (by norm_num : (0 : ℝ) < 1 / 2) hεbR hpcR hψR hK hFcR
      measurable_const hFR i = Real.sqrt Real.pi / 2 := by
  unfold ResolutionCover.chartCoeff'
  rw [dif_pos (Ps_isActive i), chartLam'_eq, chartDeg'_eq]
  have hψ0 : P.ψ i 0 = 1 / 2 := ψ_at_zero i
  have hq0 : 0 < (one1.mulPartition P i).w 0 := by
    rw [TubeWeight.mulPartition_w, one1_w, one_mul, hψ0]
    norm_num
  have h := productCoeffV_eq (rad i) (rad_pos i) (one1.mulPartition P i) hq0 (1 / 2) (by norm_num)
    (half_le_rad i) (fun _ => continuousOn_const.mul (continuous_ψ i).continuousOn)
  rw [coverLamV_eq, coverDegV_eq, TubeWeight.mulPartition_w, one1_w, one_mul, hψ0] at h
  rw [show Real.sqrt Real.pi / 2 = Real.sqrt Real.pi * (1 / 2) by ring]
  exact h

/-- **The two weighted coefficients sum to `√π`**, the coefficient of the unpartitioned integral. -/
theorem partitionCoeff'_eq :
    R.partitionCoeff' Ps P K_nonneg (by norm_num : (0 : ℝ) < 1 / 2) hεbR hpcR hψR hK hFcR
      measurable_const hFR hne = Real.sqrt Real.pi := by
  unfold ResolutionCover.partitionCoeff'
  rw [tiedCharts'_eq, Fin.sum_univ_two, chartCoeff'_eq, chartCoeff'_eq]
  ring

/-- ★ **The two-chart partition regression**: `∫_{[−1,1]} e^{−N x²} dx ~ √π · N^{−1/2}`, obtained by
summing the one-chart certificates with priors `ψ₁`, `ψ₂`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ x in interval 1, Real.exp (-N * x 0 ^ 2)) ~[atTop]
      fun N => Real.sqrt Real.pi * N ^ (-(1 / 2 : ℝ)) := by
  have hc : 0 < R.partitionCoeff' Ps P K_nonneg (by norm_num : (0 : ℝ) < 1 / 2) hεbR hpcR hψR hK
      hFcR measurable_const hFR hne := by
    rw [partitionCoeff'_eq]
    exact Real.sqrt_pos.2 Real.pi_pos
  have h := (R.hasLeadingTerm_boltzmannIntegral_of_partition' Ps P K_nonneg
    (by norm_num : (0 : ℝ) < 1 / 2) hεbR hpcR hψR hK hFcR measurable_const hFR
    hne).isEquivalent hc.ne'
  rw [partitionCoeff'_eq, partitionLam'_eq, partitionDeg'_eq] at h
  have hZ : R.boltzmannIntegral (fun _ => (1 : ℝ)) K one1 =
      fun N : ℝ => ∫ x in interval 1, Real.exp (-N * x 0 ^ 2) := by
    funext N
    rw [ResolutionCover.boltzmannIntegral_eq, iUnion_image_eq]
    refine setIntegral_congr_fun (isCompact_interval 1).isClosed.measurableSet fun x _ => ?_
    rw [one1_w, K_eq]
    ring
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end TwoChartExample

end Grammar
