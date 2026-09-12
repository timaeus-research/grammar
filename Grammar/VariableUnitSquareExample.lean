/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartVarPosterior
import Grammar.OneChartProductExample

/-!
# The square example with a unit depending on all coordinates (CCLXII)

`K(y) = (1 + y₀² + y₁²) y₀² y₁²` on `[−1,1]²` through the variable-unit product-chart theorem:
the phase unit `1 + y₀² + y₁²` depends on both coordinates, which are both normal for the unique
tied stratum `{0, 1}`, so the package `ProductMonomialChart` (normal-independent unit) does not
apply while `ProductMonomialChartVar` does. The extremal pair is `(1/2, 1)`, the stratum `{0,1}` is
all-minimal, and the coefficient is the frozen-unit formula with `u(0) = 1`:
★ `∫_{[−1,1]²} e^{−N (1+y₀²+y₁²) y₀² y₁²} dy ~ √π · N^{−1/2} · log N` — the same constant as for
`y₀² y₁²` (CCXLIX): in the all-minimal case only the value of the unit on the stratum enters.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

namespace VarSquareExample

/-- The unit `1 + y₀² + y₁²`. -/
def unit (y : Fin 2 → ℝ) : ℝ := 1 + y 0 ^ 2 + y 1 ^ 2

theorem unit_pos (y : Fin 2 → ℝ) : 0 < unit y := by
  unfold unit
  positivity

theorem continuous_unit : Continuous unit := by
  unfold unit
  fun_prop

theorem unit_zero : unit 0 = 1 := by simp [unit]

/-- The phase `K(y) = (1 + y₀² + y₁²) y₀² y₁²`. -/
noncomputable def K (y : Fin 2 → ℝ) : ℝ := unit y * monomialEval y SquareExample.expo

theorem K_eq (y : Fin 2 → ℝ) : K y = (1 + y 0 ^ 2 + y 1 ^ 2) * (y 0 ^ 2 * y 1 ^ 2) := by
  unfold K
  rw [← SquareExample.K_eq]
  rfl

theorem K_nonneg (y : Fin 2 → ℝ) : 0 ≤ K y := by
  rw [K_eq]
  positivity

theorem continuous_K : Continuous K := by
  have : K = fun y => (1 + y 0 ^ 2 + y 1 ^ 2) * (y 0 ^ 2 * y 1 ^ 2) := funext K_eq
  rw [this]
  fun_prop

/-- The monomial-chart certificate of the identity chart for `K`. -/
theorem isMonomialChart :
    IsMonomialChart K SquareExample.chart.φ SquareExample.chart.dom SquareExample.expo 0 univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_id
  injOn := injOn_id _
  exists_unit := ⟨unit, continuous_unit.continuousOn, fun y _ => (unit_pos y).ne', fun _ _ => rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [SquareExample.det_id_eq, monomialEval_zero, one_mul]⟩

/-- **The variable-unit product-chart package.** -/
noncomputable def package :
    ProductMonomialChartVar (ResolutionCover.ofChart SquareExample.chart) () K where
  e := SquareExample.expo
  h := 0
  W := univ
  W_open := isOpen_univ
  dom_subset := subset_univ _
  monomial := isMonomialChart
  u := unit
  u_cont := continuous_unit.continuousOn
  u_ne := fun y _ => (unit_pos y).ne'
  phase_eq := fun _ _ => rfl
  v := fun _ => 1
  v_cont := continuousOn_const
  det_eq := fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [SquareExample.det_id_eq, monomialEval_zero, one_mul]
  T := {0}
  T_compact := isCompact_singleton
  T_nonempty := singleton_nonempty _
  T_zero := fun x hx j _ => by rw [mem_singleton_iff.1 hx]; rfl
  b := 1
  b_pos := one_pos
  dom_eq := SquareExample.box_eq_productDom
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ SquareExample.chart hy

/-- The cover with the single chart, as a family. -/
noncomputable def Qs :
    ∀ i : Unit, ProductMonomialChartVar (ResolutionCover.ofChart SquareExample.chart) i K :=
  fun _ => package

theorem e_eq : (Qs ()).e = SquareExample.expo := rfl

theorem h_eq : (Qs ()).h = 0 := rfl

theorem ratio_eq (j : Fin 2) : (Qs ()).ratio j = 1 / 2 := by
  change ((((0 : Fin 2 →₀ ℕ) j : ℕ) : ℝ) + 1) / ((SquareExample.expo j : ℕ) : ℝ) = 1 / 2
  rw [SquareExample.expo_apply]
  simp

theorem zero_mem_support : (0 : Fin 2) ∈ (Qs ()).e.support := by
  rw [e_eq, SquareExample.expo_support]
  exact Finset.mem_univ _

theorem hact : ((ResolutionCover.ofChart SquareExample.chart).activeCoordsV Qs).Nonempty :=
  ⟨⟨(), 0⟩, (ResolutionCover.ofChart SquareExample.chart).mem_activeCoordsV Qs zero_mem_support⟩

theorem coverLamV_eq : (ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact = 1 / 2 := by
  unfold ResolutionCover.coverLamV
  refine le_antisymm ((Finset.inf'_le _
    ((ResolutionCover.ofChart SquareExample.chart).mem_activeCoordsV Qs zero_mem_support)).trans_eq
      (ratio_eq 0)) (Finset.le_inf' _ _ fun x _ => ?_)
  obtain ⟨i, j⟩ := x
  exact (ratio_eq j).ge

theorem coverDegV_eq : (ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact = 1 := by
  unfold ResolutionCover.coverDegV
  rw [coverLamV_eq]
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Qs i).e.support,
      (Qs i).ratio j = 1 / 2) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨0, zero_mem_support, ratio_eq 0⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hall : ((Qs default).e.support.filter fun j => (Qs default).ratio j = 1 / 2) =
      Finset.univ := by
    rw [e_eq, SquareExample.expo_support]
    exact Finset.filter_true_of_mem fun j _ => ratio_eq j
  rw [hall, Finset.card_univ, Fintype.card_fin]

theorem minimalSet_eq :
    (Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact) =
      Finset.univ := by
  unfold ProductMonomialChartVar.minimalSet
  rw [coverLamV_eq, e_eq, SquareExample.expo_support]
  exact Finset.filter_true_of_mem fun j _ => ratio_eq j

theorem univ_subset_support : (Finset.univ : Finset (Fin 2)) ⊆ (Qs ()).e.support := by
  rw [e_eq, SquareExample.expo_support]

/-! #### The dominant face and the face integral -/

theorem tangentialMonomial_univ_h
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Qs ()).h z = 1 := by
  unfold tangentialMonomial
  rw [h_eq, Finsupp.support_zero, Finset.filter_empty, Finset.prod_empty]

theorem tangentialMonomial_univ_e
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Qs ()).e z = 1 := by
  unfold tangentialMonomial
  rw [Finset.filter_eq_empty_iff.2 fun j _ hj => hj (Finset.mem_univ j), Finset.prod_empty]

theorem zero_mem_pieceFootSet : (0 : Fin 2 → ℝ) ∈ (Qs ()).pieceFootSet Finset.univ := by
  refine ⟨?_, fun _ _ => rfl, fun j _ hj => absurd (Finset.mem_univ j) hj⟩
  change zeroOn (Qs ()).e.support (0 : Fin 2 → ℝ) ∈ ({0} : Set (Fin 2 → ℝ))
  rw [mem_singleton_iff]
  funext j
  by_cases hj : j ∈ (Qs ()).e.support
  · exact zeroOn_apply_of_mem _ hj _
  · exact zeroOn_apply_of_notMem _ hj _

/-- **The dominant face is the whole (zero-dimensional) base.** -/
theorem dominantFace_eq_univ :
    (Qs ()).dominantFace (fun i => (Qs i).e.support) 1 Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) SquareExample.one = univ := by
  refine eq_univ_of_forall fun z => ?_
  refine ⟨fun j _ hj => absurd (Finset.mem_univ j) hj, ?_, one_pos, one_pos, one_pos, one_ne_zero,
    ?_⟩
  · rw [SquareExample.planeSplit_univ_zero]
    exact SquareExample.zero_mem_box
  · rw [tangentialMonomial_univ_h]
    exact one_ne_zero

theorem volume_dominantFace :
    0 < volume ((Qs ()).dominantFace (fun i => (Qs i).e.support) 1 Finset.univ
      Finset.univ_nonempty (fun _ => (1 : ℝ)) SquareExample.one) := by
  rw [dominantFace_eq_univ, SquareExample.volume_univ_base]
  exact zero_lt_one

/-! #### The analytic hypotheses for `F = 1`, `p = one` -/

theorem hK0 : ∀ x, 0 ≤ K x := K_nonneg

theorem hK : Measurable K := continuous_K.measurable

theorem hεb : ∀ i, (1 : ℝ) ≤ (Qs i).b := fun _ => le_rfl

theorem hFc : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart SquareExample.chart).chart i).φ y)) (Qs i).W :=
  fun _ => continuousOn_const

theorem hpc : ∀ i, ContinuousOn (fun y => SquareExample.one.w
    (((ResolutionCover.ofChart SquareExample.chart).chart i).φ y)) (Qs i).W :=
  fun _ => continuousOn_const

/-! #### The coefficient -/

theorem card_minimalSet :
    ((Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)).card =
      2 := by
  rw [minimalSet_eq, Finset.card_univ, Fintype.card_fin]

theorem prod_minimalSet :
    ∏ j ∈ (Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact),
      1 / ((Qs ()).e j : ℝ) = 1 / 4 := by
  rw [minimalSet_eq, e_eq]
  simp only [SquareExample.expo_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- The face integral over the zero-dimensional base is `1`: the unit at the origin is `1`. -/
theorem integral_face_eq_one (I : Finset (Fin 2)) (hI : I = Finset.univ)
    (hIsub : I ⊆ (Qs ()).e.support) (hne : I.Nonempty) :
    ∫ z in ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl I hIsub hne
        SquareExample.one).base,
      ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl I hIsub hne
        SquareExample.one).beta z *
        (scalarPhase I hne (Qs ()).u (Qs ()).e z ^
            (-((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)) *
          (ResolutionCover.ofChart SquareExample.chart).pieceAmp () I hne (Qs ()).h (Qs ()).v
            (F := fun _ => (1 : ℝ)) (p := SquareExample.one) z 0) = 1 := by
  subst hI
  have hbase : ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl
      Finset.univ hIsub hne SquareExample.one).base = univ :=
    eq_univ_of_forall fun z => (Qs ()).mem_pieceDensity_base_of_mem_dominantFace one_pos (hεb ())
      rfl Finset.univ hIsub hne SquareExample.one (by rw [dominantFace_eq_univ]; exact mem_univ z)
  have hone : ∀ z, ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl
      Finset.univ hIsub hne SquareExample.one).beta z *
        (scalarPhase Finset.univ hne (Qs ()).u (Qs ()).e z ^
            (-((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)) *
          (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ hne (Qs ()).h
            (Qs ()).v (F := fun _ => (1 : ℝ)) (p := SquareExample.one) z 0) = 1 := fun z => by
    rw [ProductMonomialChartVar.pieceDensity_beta, SquareExample.planeSplit_univ_zero,
      Set.indicator_of_mem zero_mem_pieceFootSet]
    unfold scalarPhase tangentialUnit ResolutionCover.pieceAmp
    rw [tangentialMonomial_univ_e, tangentialMonomial_univ_h, SquareExample.planeSplit_univ_zero]
    change (1 : ℝ) * ((unit 0 * 1) ^
      (-((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)) *
      (|(1 : ℝ)| * |(1 : ℝ)| * 1 * 1)) = 1
    rw [unit_zero]
    simp
  rw [setIntegral_congr_fun (hbase ▸ MeasurableSet.univ) fun z _ => hone z, hbase,
    Measure.restrict_univ, integral_const, measureReal_def, SquareExample.volume_univ_base]
  simp

theorem card_minimalSet_eq_succ :
    ((Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)).card =
      (ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact + 1 := by
  rw [card_minimalSet, coverDegV_eq]

/-- **The leading coefficient is `√π`** — as for `y₀² y₁²`: only the unit at the stratum enters. -/
theorem productCoeffV_eq_sqrt_pi :
    (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs hK0 one_pos hεb hFc hpc
      SquareExample.hFm SquareExample.hF hK
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) = Real.sqrt Real.pi := by
  have hsupp : ∀ i, ((Qs i).minimalSet
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)).card =
      (ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact + 1 →
      (Qs i).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact) =
        (Qs i).e.support := by
    intro i _
    cases i
    rw [minimalSet_eq, e_eq, SquareExample.expo_support]
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart SquareExample.chart).productCoeffV_extremal_eq_sum_minimal Qs hact
    hK0 one_pos hεb hFc hpc SquareExample.hFm SquareExample.hF hK hsupp, hsum,
    dif_pos card_minimalSet_eq_succ]
  rw [integral_face_eq_one _ minimalSet_eq, card_minimalSet, prod_minimalSet, coverLamV_eq,
    Real.Gamma_one_half_eq]
  norm_num [Nat.factorial]
  ring

/-- ★ **The all-coordinate-unit regression**:
`∫_{[−1,1]²} e^{−N (1+y₀²+y₁²) y₀² y₁²} dy ~ √π · N^{−1/2} · log N` — through the product-chart
theorem for units depending on all coordinates; the constant is that of `y₀² y₁²`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in SquareExample.box, Real.exp (-N * K y)) ~[atTop]
      fun N => Real.sqrt Real.pi * (N ^ (-(1 / 2 : ℝ)) * Real.log N) := by
  have h := ((ResolutionCover.ofChart
      SquareExample.chart).boltzmannIntegral_isEquivalent_of_productChartsV_extremal
    Qs hK0 one_pos hεb hFc hpc SquareExample.hFm SquareExample.hF hK hact (fun _ => zero_le_one)
    (fun _ => zero_le_one) (fun _ _ => zero_le_one) () Finset.univ univ_subset_support
    Finset.univ_nonempty (fun j _ => (ratio_eq j).trans coverLamV_eq.symm)
    (by rw [Finset.card_univ, Fintype.card_fin, coverDegV_eq]) volume_dominantFace).2
  rw [productCoeffV_eq_sqrt_pi, coverLamV_eq, coverDegV_eq] at h
  have hZ : (ResolutionCover.ofChart SquareExample.chart).boltzmannIntegral (fun _ => (1 : ℝ)) K
      SquareExample.one = fun N => ∫ y in SquareExample.box, Real.exp (-N * K y) := by
    funext N
    rw [ResolutionCover.boltzmannIntegral_eq, ResolutionCover.ofChart_iUnion_image]
    change ∫ y in id '' SquareExample.box, (1 : ℝ) * SquareExample.one.w y * Real.exp (-N * K y) = _
    rw [Set.image_id]
    simp only [SquareExample.one_w, one_mul]
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end VarSquareExample

end Grammar
