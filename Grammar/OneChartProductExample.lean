/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartTiedStrata

/-!
# One-chart covers and the regression example `∫_{[−1,1]²} e^{−N x²y²} ~ √π N^{−1/2} log N`

Unit 5 of consult #79 (`tide-log/gpt6_bigpicture_v79.md`).

* **One-chart covers.** For the cover `ofChart C` of a single chart the counting weight is `1` on
  the image (`ofChart_weight_eq_one`), so the cover-weight factorisation of `ProductMonomialChart`
  holds with `r = 1` and the package reduces to the geometric data alone
  (`ProductMonomialChart.ofUnit`).
* **The square example.** For the identity chart on the square `[−1,1]²`, the phase
  `K(y) = y₀² y₁²` (exponents `e = (2,2)`, Jacobian exponents `h = 0`, units `u = v = 1`, inactive
  base `T = {0}`, radius `b = 1`) is a centred product monomial chart (`SquareExample.package`);
  the extremal pair is `(λ*, k*) = (1/2, 1)` (`coverLam_eq`, `coverDeg_eq`), the minimal set is
  everything, the dominant face is the whole (zero-dimensional) base of mass one
  (`volume_dominantFace`), and the all-minimal formula evaluates to
  `c = 2² · Γ(1/2)/1! · (1/2)(1/2) · 1 = √π` (`productCoeffD_eq_sqrt_pi`). Hence
  ★ `SquareExample.integral_isEquivalent`:
  `∫_{[−1,1]²} e^{−N y₀² y₁²} dy ~ √π · N^{−1/2} · log N` — the normalisation test of the whole
  chain (reflection factor `2^{|I|}`, the Gamma/factorial constant, the `∏ 1/e_j`, and the face
  integral over a point).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### One-chart covers -/

namespace ResolutionCover

variable {d : ℕ}

/-- The one-chart cover of a chart. -/
def ofChart (C : ResolutionChart d) : ResolutionCover d Unit := ⟨fun _ => C⟩

theorem ofChart_iUnion_image (C : ResolutionChart d) :
    ⋃ i, (ofChart C).image i = C.φ '' C.dom := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

/-- The counting weight of a one-chart cover is `1` on the image. -/
theorem ofChart_weight_eq_one (C : ResolutionChart d) {x : Fin d → ℝ} (hx : x ∈ C.φ '' C.dom) :
    (ofChart C).weight () x = 1 := by
  unfold ResolutionCover.weight coverWeight
  rw [Fintype.sum_unique]
  change (C.φ '' C.dom).indicator (fun _ => (1 : ℝ)) x /
    (C.φ '' C.dom).indicator (fun _ => (1 : ℝ)) x = 1
  rw [Set.indicator_of_mem hx, div_one]

theorem ofChart_weight_Φ (C : ResolutionChart d) {y : Fin d → ℝ} (hy : y ∈ C.dom) :
    (ofChart C).weight () (C.Φ y) = 1 :=
  ofChart_weight_eq_one C ⟨y, hy, (C.Φ_eqOn hy).symm⟩

end ResolutionCover

/-- **A product monomial chart for a one-chart cover from the geometric data alone**: the
cover-weight factor is `r = 1`. -/
def ProductMonomialChart.ofUnit {d : ℕ} (C : ResolutionChart d) {K : (Fin d → ℝ) → ℝ}
    (e h : Fin d →₀ ℕ) (W : Set (Fin d → ℝ)) (W_open : IsOpen W) (dom_subset : C.dom ⊆ W)
    (monomial : IsMonomialChart K C.φ C.dom e h W) (u : (Fin d → ℝ) → ℝ) (u_cont : ContinuousOn u W)
    (u_ne : ∀ y ∈ W, u y ≠ 0) (phase_eq : ∀ y ∈ W, K (C.φ y) = u y * monomialEval y e)
    (v : (Fin d → ℝ) → ℝ) (v_cont : ContinuousOn v W)
    (det_eq : ∀ y ∈ W, (fderiv ℝ C.φ y).det = v y * monomialEval y h) (T : Set (Fin d → ℝ))
    (T_compact : IsCompact T) (T_nonempty : T.Nonempty) (T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0)
    (b : ℝ) (b_pos : 0 < b) (dom_eq : C.dom = productDom e.support T b)
    (unit_indep : ∀ y ∈ C.dom, u y = u (zeroOn e.support y)) :
    ProductMonomialChart (ResolutionCover.ofChart C) () K where
  e := e
  h := h
  W := W
  W_open := W_open
  dom_subset := dom_subset
  monomial := monomial
  u := u
  u_cont := u_cont
  u_ne := u_ne
  phase_eq := phase_eq
  v := v
  v_cont := v_cont
  det_eq := det_eq
  T := T
  T_compact := T_compact
  T_nonempty := T_nonempty
  T_zero := T_zero
  b := b
  b_pos := b_pos
  dom_eq := dom_eq
  unit_indep := unit_indep
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ C hy

/-! ### The square example -/

namespace SquareExample

/-- The closed square `[−1,1]²`. -/
def box : Set (Fin 2 → ℝ) := Set.pi univ fun _ => Icc (-1 : ℝ) 1

theorem isCompact_box : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc

theorem zero_mem_box : (0 : Fin 2 → ℝ) ∈ box := fun _ _ => ⟨by norm_num, by norm_num⟩

/-- The identity chart on the square. -/
def chart : ResolutionChart 2 where
  dom := box
  dom_compact := isCompact_box
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

/-- The exponents `(2, 2)`. -/
noncomputable def expo : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 2

theorem expo_apply (j : Fin 2) : expo j = 2 := rfl

theorem expo_support : expo.support = Finset.univ := by
  ext j
  simp [Finsupp.mem_support_iff, expo_apply]

/-- The phase `K(y) = y₀² y₁²`. -/
noncomputable def K (y : Fin 2 → ℝ) : ℝ := monomialEval y expo

theorem K_eq (y : Fin 2 → ℝ) : K y = y 0 ^ 2 * y 1 ^ 2 := by
  unfold K monomialEval
  rw [Finsupp.prod, expo_support, Fin.prod_univ_two, expo_apply, expo_apply]

theorem K_nonneg (y : Fin 2 → ℝ) : 0 ≤ K y := by
  rw [K_eq]
  positivity

theorem continuous_K : Continuous K := by
  have : K = fun y => y 0 ^ 2 * y 1 ^ 2 := funext K_eq
  rw [this]
  fun_prop

/-- The unit weight. -/
def one : TubeWeight 2 := ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩

@[simp] theorem one_w (x : Fin 2 → ℝ) : one.w x = 1 := rfl

theorem box_eq_productDom : box = productDom expo.support ({0} : Set (Fin 2 → ℝ)) 1 := by
  ext y
  simp only [box, productDom, expo_support, Set.mem_pi, mem_univ, true_implies, mem_Icc,
    Set.mem_ofPred_eq, Finset.mem_univ, mem_singleton_iff, abs_le]
  constructor
  · intro hy
    exact ⟨funext fun j => zeroOn_apply_of_mem _ (Finset.mem_univ j) y, fun j => hy j⟩
  · rintro ⟨-, hy⟩ j
    exact hy j

theorem det_id_eq (y : Fin 2 → ℝ) : (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 := by
  rw [fderiv_id]
  exact LinearMap.det_id

/-- The monomial-chart certificate of the identity chart. -/
theorem isMonomialChart : IsMonomialChart K chart.φ chart.dom expo 0 univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_id
  injOn := injOn_id _
  exists_unit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change K y = 1 * monomialEval y expo
    rw [one_mul]
    rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [det_id_eq, monomialEval_zero, one_mul]⟩

/-- **The product-chart package of the square example.** -/
noncomputable def package : ProductMonomialChart (ResolutionCover.ofChart chart) () K :=
  ProductMonomialChart.ofUnit chart expo 0 univ isOpen_univ (subset_univ _) isMonomialChart
    (fun _ => 1) continuousOn_const (fun _ _ => one_ne_zero)
    (fun y _ => by
      change K y = 1 * monomialEval y expo
      rw [one_mul]
      rfl)
    (fun _ => 1) continuousOn_const
    (fun y _ => by
      change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
      rw [det_id_eq, monomialEval_zero, one_mul])
    {0} isCompact_singleton (singleton_nonempty _)
    (fun x hx j _ => by rw [mem_singleton_iff.1 hx]; rfl)
    1 one_pos box_eq_productDom (fun _ _ => rfl)

/-- The cover with the single chart, as a family. -/
noncomputable def Ps : ∀ i : Unit, ProductMonomialChart (ResolutionCover.ofChart chart) i K :=
  fun _ => package

theorem ratio_eq (j : Fin 2) : (Ps ()).ratio j = 1 / 2 := by
  change ((((0 : Fin 2 →₀ ℕ) j : ℕ) : ℝ) + 1) / ((expo j : ℕ) : ℝ) = 1 / 2
  rw [expo_apply]
  simp

theorem hact : ((ResolutionCover.ofChart chart).activeCoords Ps).Nonempty :=
  ⟨⟨(), 0⟩, (ResolutionCover.ofChart chart).mem_activeCoords Ps
    (by rw [show (Ps ()).e = expo from rfl, expo_support]; exact Finset.mem_univ _)⟩

theorem coverLam_eq : (ResolutionCover.ofChart chart).coverLam Ps hact = 1 / 2 := by
  unfold ResolutionCover.coverLam
  have h0 : (0 : Fin 2) ∈ (Ps ()).e.support := by
    rw [show (Ps ()).e = expo from rfl, expo_support]; exact Finset.mem_univ _
  refine le_antisymm ((Finset.inf'_le _ ((ResolutionCover.ofChart chart).mem_activeCoords Ps
    h0)).trans_eq (ratio_eq 0)) (Finset.le_inf' _ _ fun x _ => ?_)
  obtain ⟨i, j⟩ := x
  exact (ratio_eq j).ge

theorem coverDeg_eq : (ResolutionCover.ofChart chart).coverDeg Ps hact = 1 := by
  unfold ResolutionCover.coverDeg
  rw [coverLam_eq]
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Ps i).e.support, (Ps i).ratio j = 1 / 2) =
      Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨0, by
      rw [show (Ps i).e = expo from rfl, expo_support]; exact Finset.mem_univ _, ratio_eq 0⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hall : ((Ps default).e.support.filter fun j => (Ps default).ratio j = 1 / 2) =
      Finset.univ := by
    rw [show (Ps default).e = expo from rfl, expo_support]
    exact Finset.filter_true_of_mem fun j _ => ratio_eq j
  rw [hall, Finset.card_univ, Fintype.card_fin]

theorem minimalSet_eq :
    (Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact) = Finset.univ := by
  unfold ProductMonomialChart.minimalSet
  rw [coverLam_eq, show (Ps ()).e = expo from rfl, expo_support]
  exact Finset.filter_true_of_mem fun j _ => ratio_eq j

/-! #### The dominant face and the face integral -/

theorem planeSplit_univ_zero (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    planeSplit (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty) (z, 0) = 0 := by
  funext j
  obtain ⟨a, ha⟩ := exists_inr_of_mem Finset.univ Finset.univ_nonempty (Finset.mem_univ j)
  rw [ha, planeSplit_stratum_inr]
  rfl

theorem univ_subset_support : (Finset.univ : Finset (Fin 2)) ⊆ (Ps ()).e.support := by
  rw [show (Ps ()).e = expo from rfl, expo_support]

theorem tangentialMonomial_univ_h
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Ps ()).h z = 1 := by
  unfold tangentialMonomial
  rw [show (Ps ()).h = 0 from rfl, Finsupp.support_zero, Finset.filter_empty, Finset.prod_empty]

theorem tangentialMonomial_univ_e
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Ps ()).e z = 1 := by
  unfold tangentialMonomial
  rw [Finset.filter_eq_empty_iff.2 fun j _ hj => hj (Finset.mem_univ j), Finset.prod_empty]

theorem zero_mem_pieceFootSet : (0 : Fin 2 → ℝ) ∈ (Ps ()).pieceFootSet Finset.univ := by
  refine ⟨?_, fun _ _ => rfl, fun j _ hj => absurd (Finset.mem_univ j) hj⟩
  change zeroOn (Ps ()).e.support (0 : Fin 2 → ℝ) ∈ ({0} : Set (Fin 2 → ℝ))
  rw [mem_singleton_iff]
  funext j
  by_cases hj : j ∈ (Ps ()).e.support
  · exact zeroOn_apply_of_mem _ hj _
  · exact zeroOn_apply_of_notMem _ hj _

/-- **The dominant face of the square example is the whole (zero-dimensional) base.** -/
theorem dominantFace_eq_univ :
    (Ps ()).dominantFace (fun i => (Ps i).e.support) 1 Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) one = univ := by
  refine eq_univ_of_forall fun z => ?_
  refine ⟨fun j _ hj => absurd (Finset.mem_univ j) hj, ?_, one_pos, one_pos, one_pos, one_ne_zero,
    ?_⟩
  · rw [planeSplit_univ_zero]
    exact zero_mem_box
  · rw [tangentialMonomial_univ_h]
    exact one_ne_zero

instance : IsEmpty (Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1))) :=
  inferInstanceAs (IsEmpty (Fin 0))

theorem volume_univ_base :
    (volume : Measure (Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)) univ = 1 := by
  rw [volume_pi]
  exact Measure.pi_empty_univ _

theorem volume_dominantFace :
    0 < volume ((Ps ()).dominantFace (fun i => (Ps i).e.support) 1 Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) one) := by
  rw [dominantFace_eq_univ, volume_univ_base]
  exact zero_lt_one

/-! #### The analytic hypotheses for `F = 1`, `p = one` -/

theorem hK0 : ∀ x, 0 ≤ K x := K_nonneg

theorem hK : Measurable K := continuous_K.measurable

theorem hεb : ∀ i, (1 : ℝ) ≤ (Ps i).b := fun _ => le_rfl

theorem hFc : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart chart).chart i).φ y)) (Ps i).W :=
  fun _ => continuousOn_const

theorem hpc : ∀ i, ContinuousOn (fun y => one.w (((ResolutionCover.ofChart chart).chart i).φ y))
    (Ps i).W :=
  fun _ => continuousOn_const

theorem hFm : Measurable fun _ : Fin 2 → ℝ => (1 : ℝ) := measurable_const

theorem hF : Integrable (fun x => (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * one.w x)
    (volume.restrict (⋃ i, (ResolutionCover.ofChart chart).image i)) := by
  rw [ResolutionCover.ofChart_iUnion_image]
  change Integrable _ (volume.restrict (id '' box))
  rw [Set.image_id]
  exact (integrableOn_const (C := (1 : ℝ)) isCompact_box.measure_lt_top.ne).congr
    (Eventually.of_forall fun x => by simp)

/-! #### The coefficient -/

theorem card_minimalSet :
    ((Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact)).card = 2 := by
  rw [minimalSet_eq, Finset.card_univ, Fintype.card_fin]

theorem prod_minimalSet :
    ∏ j ∈ (Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact),
      1 / ((Ps ()).e j : ℝ) = 1 / 4 := by
  rw [minimalSet_eq, show (Ps ()).e = expo from rfl]
  simp only [expo_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- The face integral over the zero-dimensional base is `1`. -/
theorem integral_face_eq_one (I : Finset (Fin 2)) (hI : I = Finset.univ)
    (hIsub : I ⊆ (Ps ()).e.support) (hne : I.Nonempty) :
    ∫ z in ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb ()) rfl I hIsub hne
        one).base,
      ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb ()) rfl I hIsub hne
        one).beta z *
        (scalarPhase I hne (Ps ()).u (Ps ()).e z ^
            (-((ResolutionCover.ofChart chart).coverLam Ps hact)) *
          (ResolutionCover.ofChart chart).pieceAmp () I hne (Ps ()).h (Ps ()).v
            (F := fun _ => (1 : ℝ)) (p := one) z 0) = 1 := by
  subst hI
  have hbase : ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb ()) rfl
      Finset.univ hIsub hne one).base = univ :=
    eq_univ_of_forall fun z => (Ps ()).mem_pieceDensity_base_of_mem_dominantFace one_pos (hεb ())
      rfl Finset.univ hIsub hne one (by rw [dominantFace_eq_univ]; exact mem_univ z)
  have hone : ∀ z, ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb ()) rfl
      Finset.univ hIsub hne one).beta z *
        (scalarPhase Finset.univ hne (Ps ()).u (Ps ()).e z ^
            (-((ResolutionCover.ofChart chart).coverLam Ps hact)) *
          (ResolutionCover.ofChart chart).pieceAmp () Finset.univ hne (Ps ()).h (Ps ()).v
            (F := fun _ => (1 : ℝ)) (p := one) z 0) = 1 := fun z => by
    rw [ProductMonomialChart.pieceDensity_beta, planeSplit_univ_zero,
      Set.indicator_of_mem zero_mem_pieceFootSet]
    unfold scalarPhase tangentialUnit ResolutionCover.pieceAmp
    rw [tangentialMonomial_univ_e, tangentialMonomial_univ_h, planeSplit_univ_zero]
    change (1 : ℝ) * ((1 * 1) ^ (-((ResolutionCover.ofChart chart).coverLam Ps hact)) *
      (|(1 : ℝ)| * |(1 : ℝ)| * 1 * 1)) = 1
    simp
  rw [setIntegral_congr_fun (hbase ▸ MeasurableSet.univ) fun z _ => hone z, hbase,
    Measure.restrict_univ, integral_const, measureReal_def, volume_univ_base]
  simp

theorem card_minimalSet_eq_succ :
    ((Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact)).card =
      (ResolutionCover.ofChart chart).coverDeg Ps hact + 1 := by
  rw [card_minimalSet, coverDeg_eq]

/-- **The leading coefficient of the square example is `√π`.** -/
theorem productCoeffD_eq_sqrt_pi :
    (ResolutionCover.ofChart chart).productCoeffD Ps hK0 one_pos hεb hFc hpc hFm hF hK
      ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) = Real.sqrt Real.pi := by
  have hsupp : ∀ i, ((Ps i).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact)).card =
      (ResolutionCover.ofChart chart).coverDeg Ps hact + 1 →
      (Ps i).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact) = (Ps i).e.support := by
    intro i _
    cases i
    rw [minimalSet_eq, show (Ps ()).e = expo from rfl, expo_support]
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart chart).productCoeffD_extremal_eq_sum_minimal Ps hact hK0 one_pos hεb
    hFc hpc hFm hF hK hsupp, hsum, dif_pos card_minimalSet_eq_succ]
  rw [integral_face_eq_one _ minimalSet_eq, card_minimalSet, prod_minimalSet, coverLam_eq,
    Real.Gamma_one_half_eq]
  norm_num [Nat.factorial]
  ring

/-- ★ **The regression example**: `∫_{[−1,1]²} e^{−N y₀² y₁²} dy ~ √π · N^{−1/2} · log N`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in box, Real.exp (-N * K y)) ~[atTop]
      fun N => Real.sqrt Real.pi * (N ^ (-(1 / 2 : ℝ)) * Real.log N) := by
  have h := ((ResolutionCover.ofChart
      chart).boltzmannIntegral_isEquivalent_of_productCharts_extremal
    Ps hK0 one_pos hεb hFc hpc hFm hF hK hact (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ _ => zero_le_one) () Finset.univ univ_subset_support Finset.univ_nonempty
    (fun j _ => (ratio_eq j).trans coverLam_eq.symm)
    (by rw [Finset.card_univ, Fintype.card_fin, coverDeg_eq]) volume_dominantFace).2
  rw [productCoeffD_eq_sqrt_pi, coverLam_eq, coverDeg_eq] at h
  have hZ : (ResolutionCover.ofChart chart).boltzmannIntegral (fun _ => (1 : ℝ)) K one =
      fun N => ∫ y in box, Real.exp (-N * K y) := by
    funext N
    rw [ResolutionCover.boltzmannIntegral_eq, ResolutionCover.ofChart_iUnion_image]
    change ∫ y in id '' box, (1 : ℝ) * one.w y * Real.exp (-N * K y) = _
    rw [Set.image_id]
    simp only [one_w, one_mul]
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end SquareExample

end Grammar
