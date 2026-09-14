/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothBridgeConsumer
import Monomialize.Transport.DomainCoreTransport

/-!
# The grammar-side consumer of a normalised domain core transport (consult #120 §6.4, Target B)

From hironaka's Target B interface `NormalisedDomainCoreTransport d K prior Wdom` — finitely many
charts `ψ_i` on boxes `[−a_i,a_i]^d`, analytic on open neighbourhoods `V_i`, with the phase in
exact normalised monomial form `K ∘ ψ_i = c_i ∏ u^{2k_i}`, Jacobian `b_i ∏ u^{h_i}`, smooth weights
`ω_i`, a set of SELECTED ORTHANTS `sectors_i` per chart, a tail measure with a phase gap and the
exact transport `∑_i (ψ_i)_*(sector sources) + tail = (vol|_{Wdom})·prior` — together with a
smooth nonnegative prior and a smooth observable on a COMPACT domain `Wdom`, we build the
`SmoothCoreDecomposition` of the localisation datum `((vol|_{Wdom})·prior, K, obs)`: one smooth
core presentation per chart and SELECTED orthant (the sector `box ∩ ⋃_{σ ∈ sectors_i} orthant_σ`
splits, up to the null walls, into the disjoint orthant boxes of the selected signs), with the
CONSTANT phase unit `c_i`, the transport density `ω_i |b_i| prior∘ψ_i` and the amplitude
`ω_i |b_i| prior∘ψ_i obs∘ψ_i`, both extended from `V_i` to globally smooth functions, and the
transport's tail as the tail. The phase is nonnegative a.e. for the prior measure on the domain
WITHOUT a global hypothesis (the monomial on the cores, the gap on the tail). Hence ★★★
`hasSmoothCoordFreeExpansion`: the partition function with insertions `∫_{Wdom} prior·obs·e^{−NK}`
has the smooth coordinate-free expansion with INTRINSIC coefficients (`coeff_eq_of_transports`).
The regression is the identity chart on the positive orthant of a box (`ofMonomialHalfBox`): the
half-box `[−a,a]^d ∩ {y ≥ 0}` with the monomial phase, one selected orthant and no tail; in
`d = 1` this is `∫_0^a prior·obs·e^{−N c y^{2k}}` with no logarithms. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

/-- **Domain bridge inputs**: a normalised domain core transport of a smooth nonnegative prior
over a compact domain, a measurable phase and a smooth observable. -/
structure DomainBridgeInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the integration domain -/
  Wdom : Set (Fin d → ℝ)
  Wdom_compact : IsCompact Wdom
  /-- the normalised core transport of the prior-weighted volume of the domain -/
  T : NormalisedDomainCoreTransport d K prior Wdom
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : DomainBridgeInputs d)

namespace DomainBridgeInputs

/-! ### The localisation datum -/

theorem Wdom_m : MeasurableSet X.Wdom := X.Wdom_compact.isClosed.measurableSet

/-- The prior measure `(vol|_{Wdom})·prior` of the domain. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  (volume.restrict X.Wdom).withDensity fun y => ENNReal.ofReal (X.prior y)

theorem prior_m : Measurable X.prior := X.prior_smooth.continuous.measurable

theorem obs_int : Integrable X.obs X.priorMeasure :=
  SheetAssembly.integrable_of_continuous_of_subset_compact X.prior_smooth.continuous
    X.obs_smooth.continuous X.Wdom_compact subset_rfl X.Wdom_m

/-- The sector of chart `i`: the box intersected with the selected orthants. -/
def sector (i : X.T.ι) : Set (Fin d → ℝ) :=
  centeredBox d (X.T.a i) ∩ selectedOrthants (X.T.sectors i)

theorem measurableSet_box (i : X.T.ι) : MeasurableSet (centeredBox d (X.T.a i)) :=
  (isCompact_centeredBox d (X.T.a i)).isClosed.measurableSet

theorem measurableSet_sector (i : X.T.ι) : MeasurableSet (X.sector i) :=
  (X.measurableSet_box i).inter (measurableSet_selectedOrthants _)

/-- The phase is nonnegative a.e. on every transported sector source: it is the monomial there. -/
theorem K_nonneg_core (i : X.T.ι) :
    ∀ᵐ y ∂((sectorSource (X.T.ψ i) (X.T.ω i) (X.T.a i) (X.T.sectors i) X.prior).map (X.T.ψ i)),
      0 ≤ X.K y := by
  rw [ae_map_iff (X.T.ψ_measurable i).aemeasurable (measurableSet_le measurable_const X.K_m)]
  unfold sectorSource
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  refine (ae_restrict_mem (X.measurableSet_sector i)).mono fun u hu => ?_
  change 0 ≤ X.K (X.T.ψ i u)
  rw [X.T.phase_eq i u (X.T.box_subset_V i hu.1)]
  exact mul_nonneg (X.T.phaseConst_pos i).le
    (Finset.prod_nonneg fun j _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

/-- ★ **The phase is nonnegative a.e. for the prior measure of the domain**, from the transport
alone: the monomial on the cores, above the gap on the tail. -/
theorem K_nonneg : ∀ᵐ y ∂X.priorMeasure, 0 ≤ X.K y := by
  unfold priorMeasure
  rw [← X.T.transport, ae_add_measure_iff, ← Measure.sum_fintype,
    Measure.ae_sum_iff' (measurableSet_le measurable_const X.K_m)]
  exact ⟨fun i => X.K_nonneg_core i, X.T.tail_gap.mono fun y hy => X.T.δ_pos.le.trans hy⟩

/-- The localisation datum `((vol|_{Wdom})·prior, K, obs)`. -/
noncomputable def D : LocalisationData (Fin d → ℝ) where
  μ := X.priorMeasure
  phase := X.K
  obs := X.obs
  phase_measurable := X.K_m
  phase_nonneg := X.K_nonneg
  obs_integrable := X.obs_int
  δ := X.T.δ
  δ_pos := X.T.δ_pos

theorem D_μ : X.D.μ = X.priorMeasure := rfl
theorem D_phase : X.D.phase = X.K := rfl
theorem D_obs : X.D.obs = X.obs := rfl

/-! ### The chart densities, extended to globally smooth functions -/

theorem box_eq (i : X.T.ι) : centeredBox d (X.T.a i) = piBox d (Icc (-(X.T.a i)) (X.T.a i)) :=
  centeredBox_eq_pi d (X.T.a i)

/-- The local nonnegative density factor `ω · |b| · prior ∘ ψ` of chart `i`, smooth on `V i`. -/
noncomputable def ρloc (i : X.T.ι) (u : Fin d → ℝ) : ℝ :=
  X.T.ω i u * |X.T.jacUnit i u| * X.prior (X.T.ψ i u)

theorem ρloc_nonneg (i : X.T.ι) (u : Fin d → ℝ) : 0 ≤ X.ρloc i u :=
  mul_nonneg (mul_nonneg (X.T.ω_nonneg i u) (abs_nonneg _)) (X.prior_nonneg _)

theorem contDiffOn_ψ (i : X.T.ι) : ContDiffOn ℝ ∞ (X.T.ψ i) (X.T.V i) :=
  (X.T.ψ_analytic i).contDiffOn_of_completeSpace

theorem contDiffOn_ρloc (i : X.T.ι) : ContDiffOn ℝ ∞ (X.ρloc i) (X.T.V i) :=
  ((X.T.ω_smoothOn i).mul
    ((X.T.jacUnit_analytic i).contDiffOn_of_completeSpace.abs (X.T.jacUnit_ne_zero i))).mul
    (X.prior_smooth.comp_contDiffOn (X.contDiffOn_ψ i))

/-- The local amplitude `ω · |b| · prior ∘ ψ · obs ∘ ψ` of chart `i`, smooth on `V i`. -/
noncomputable def Gloc (i : X.T.ι) (u : Fin d → ℝ) : ℝ := X.ρloc i u * X.obs (X.T.ψ i u)

theorem contDiffOn_Gloc (i : X.T.ι) : ContDiffOn ℝ ∞ (X.Gloc i) (X.T.V i) :=
  (X.contDiffOn_ρloc i).mul (X.obs_smooth.comp_contDiffOn (X.contDiffOn_ψ i))

theorem exists_ρf (i : X.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (X.ρloc i) (centeredBox d (X.T.a i)) ∧ ∀ x, 0 ≤ g x := by
  obtain ⟨g, hg, heq, hnn⟩ := exists_contDiff_eqOn_of_contDiffOn (X.T.V_open i)
    (isCompact_centeredBox d (X.T.a i)).isClosed (X.T.box_subset_V i) (X.contDiffOn_ρloc i)
  exact ⟨g, hg, heq, hnn fun x _ => X.ρloc_nonneg i x⟩

/-- The globally smooth nonnegative transport density of chart `i`, equal to `ω · |b| · prior ∘ ψ`
on the box. -/
noncomputable def ρf (i : X.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (X.exists_ρf i)

theorem contDiff_ρf (i : X.T.ι) : ContDiff ℝ ∞ (X.ρf i) := (Classical.choose_spec (X.exists_ρf i)).1

theorem ρf_eq (i : X.T.ι) {u : Fin d → ℝ} (hu : u ∈ centeredBox d (X.T.a i)) :
    X.ρf i u = X.ρloc i u := (Classical.choose_spec (X.exists_ρf i)).2.1 hu

theorem ρf_nonneg (i : X.T.ι) (u : Fin d → ℝ) : 0 ≤ X.ρf i u :=
  (Classical.choose_spec (X.exists_ρf i)).2.2 u

theorem measurable_ρf (i : X.T.ι) : Measurable (X.ρf i) := (X.contDiff_ρf i).continuous.measurable

theorem exists_G (i : X.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (X.Gloc i) (centeredBox d (X.T.a i)) := by
  obtain ⟨g, hg, heq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (X.T.V_open i)
    (isCompact_centeredBox d (X.T.a i)).isClosed (X.T.box_subset_V i) (X.contDiffOn_Gloc i)
  exact ⟨g, hg, heq⟩

/-- The globally smooth amplitude of chart `i`, equal to `ω · |b| · prior ∘ ψ · obs ∘ ψ` on the
box. -/
noncomputable def G (i : X.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (X.exists_G i)

theorem contDiff_G (i : X.T.ι) : ContDiff ℝ ∞ (X.G i) := (Classical.choose_spec (X.exists_G i)).1

theorem G_eq (i : X.T.ι) {u : Fin d → ℝ} (hu : u ∈ centeredBox d (X.T.a i)) :
    X.G i u = X.Gloc i u := (Classical.choose_spec (X.exists_G i)).2 hu

/-! ### The sector sources as weighted sector measures, split over the selected orthants -/

/-- The sector source of chart `i` is the sector measure with density `|u|^h · ρf`. -/
theorem sectorSource_eq (i : X.T.ι) :
    sectorSource (X.T.ψ i) (X.T.ω i) (X.T.a i) (X.T.sectors i) X.prior =
      (volume.restrict (X.sector i)).withDensity fun u =>
        ENNReal.ofReal (NormalisedBox.wgt (X.T.h i) u * X.ρf i u) := by
  unfold sectorSource
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq,
    ae_restrict_iff' ((X.measurableSet_box i).inter (measurableSet_selectedOrthants _))]
  refine Eventually.of_forall fun u hu => ?_
  rw [absDet, X.T.jac_eq i u (X.T.box_subset_V i hu.1), abs_mul, Finset.abs_prod,
    ← ENNReal.ofReal_mul (mul_nonneg (X.prior_nonneg _) (X.T.ω_nonneg i u)), X.ρf_eq i hu.1]
  simp only [abs_pow]
  unfold ρloc NormalisedBox.wgt
  congr 1
  ring

/-- The orthant box of a sign is, up to the null walls, the centred box intersected with the open
orthant. -/
theorem orthantBox_ae_eq (σ : WaterFilling.CoordSign d) (a : ℝ) :
    (WaterFilling.orthantBox σ a : Set (Fin d → ℝ)) =ᵐ[volume]
      (centeredBox d a ∩ openOrthant σ : Set (Fin d → ℝ)) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun y hy => ?_) walls_null
    obtain ⟨hy1, hy2⟩ := hy
    have hdom : y ∈ centeredBox d a := by
      rw [centeredBox_eq_pi]
      exact WaterFilling.orthantBox_subset σ a hy1
    have hno : y ∉ openOrthant σ := fun h => hy2 ⟨hdom, h⟩
    unfold openOrthant at hno
    rw [mem_ofPred_eq] at hno
    push Not at hno
    obtain ⟨j, hj⟩ := hno
    refine ⟨j, ?_⟩
    have h0 : 0 ≤ WaterFilling.sgn σ j * y j := ((WaterFilling.mem_orthantBox.1 hy1) j).1
    have h1 : WaterFilling.sgn σ j * y j = 0 := le_antisymm hj h0
    exact (mul_eq_zero.1 h1).resolve_left (WaterFilling.sgn_ne_zero σ j)
  · have hsub : centeredBox d a ∩ openOrthant σ ⊆ WaterFilling.orthantBox σ a := by
      intro y hy
      rw [WaterFilling.mem_orthantBox]
      intro j
      have hpos : 0 < WaterFilling.sgn σ j * y j := hy.2 j
      refine ⟨hpos.le, ?_⟩
      have : |WaterFilling.sgn σ j * y j| ≤ a := by
        rw [abs_mul, WaterFilling.abs_sgn, one_mul]
        exact hy.1 j
      exact (le_abs_self _).trans this
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- The restriction to the sector is the sum of the restrictions to the selected orthant boxes. -/
theorem restrict_sector_eq (i : X.T.ι) :
    volume.restrict (X.sector i) =
      ∑ σ ∈ X.T.sectors i,
        volume.restrict (WaterFilling.orthantBox σ (X.T.a i) : Set (Fin d → ℝ)) := by
  unfold sector selectedOrthants
  rw [inter_iUnion₂]
  rw [Measure.restrict_biUnion_finset (fun σ _ τ _ hστ => (openOrthant_disjoint hστ).mono
    inter_subset_right inter_subset_right)
    (fun σ => (X.measurableSet_box i).inter (measurableSet_openOrthant σ))]
  rw [Measure.sum_fintype, Finset.sum_coe_sort (X.T.sectors i) fun σ =>
    volume.restrict (centeredBox d (X.T.a i) ∩ openOrthant σ)]
  exact Finset.sum_congr rfl fun σ _ =>
    (Measure.restrict_congr_set (orthantBox_ae_eq σ (X.T.a i))).symm

/-! ### Charts, active sets and pieces -/

/-- The active set of chart `i`. -/
def act (i : X.T.ι) : Finset (Fin d) := Finset.univ.filter fun j => 0 < X.T.k i j

theorem mem_act {i : X.T.ι} {j : Fin d} : j ∈ X.act i ↔ 0 < X.T.k i j := by
  simp [act]

theorem k_eq_zero_of_not_mem_act {i : X.T.ι} {j : Fin d} (hj : j ∉ X.act i) : X.T.k i j = 0 := by
  rw [mem_act] at hj
  omega

/-- The pieces: a chart and one of its SELECTED orthants. -/
abbrev PIdx : Type := Σ i : X.T.ι, ↥(X.T.sectors i)

/-- The core measure of a piece: the weighted orthant-box measure pushed along the chart. -/
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2.1 (X.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (X.T.h p.1) w * X.ρf p.1 w)).map (X.T.ψ p.1)

/-- The pieces of a chart exhaust its transported sector source. -/
theorem sum_coreMeasure_chart (i : X.T.ι) :
    ∑ σ : ↥(X.T.sectors i), X.coreMeasure ⟨i, σ⟩ =
      (sectorSource (X.T.ψ i) (X.T.ω i) (X.T.a i) (X.T.sectors i) X.prior).map (X.T.ψ i) := by
  unfold coreMeasure
  rw [← SmoothSheetInputs.map_finset_sum' _ _ (X.T.ψ_measurable i), X.sectorSource_eq,
    X.restrict_sector_eq i, ← Finset.sum_coe_sort (X.T.sectors i) fun σ =>
      volume.restrict (WaterFilling.orthantBox σ (X.T.a i) : Set (Fin d → ℝ)),
    ← Measure.sum_fintype fun σ : ↥(X.T.sectors i) =>
      volume.restrict (WaterFilling.orthantBox σ.1 (X.T.a i) : Set (Fin d → ℝ)),
    withDensity_sum, Measure.sum_fintype]

/-- ★ **The pieces and the tail exhaust the prior measure of the domain** (the transport
identity). -/
theorem sum_coreMeasure : ∑ p : X.PIdx, X.coreMeasure p + X.T.tail = X.priorMeasure := by
  unfold priorMeasure
  rw [Fintype.sum_sigma, ← X.T.transport]
  congr 1
  exact Finset.sum_congr rfl fun i _ => X.sum_coreMeasure_chart i

/-- The number of active coordinates of a piece. -/
noncomputable def da (p : X.PIdx) : ℕ := Fintype.card {j // inJ (X.act p.1) j}

theorem da_le (p : X.PIdx) : X.da p ≤ d := by
  have := Fintype.card_subtype_le (inJ (X.act p.1))
  rwa [Fintype.card_fin] at this

/-- The enumeration of the active coordinates. -/
noncomputable def eqv (p : X.PIdx) : Fin (X.da p) ≃ {j // inJ (X.act p.1) j} :=
  (Fintype.equivFin _).symm

/-- The reflected inactive coordinates of a base point. -/
def sc (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) : {j // ¬ inJ (X.act p.1) j} → ℝ :=
  fun j => WaterFilling.sgn p.2.1 j.1 * s.1 j

theorem continuous_sc (p : X.PIdx) : Continuous (X.sc p) :=
  continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- The chart coordinate of a piece: reflected active coordinates `v`, reflected inactive
coordinates `s`. -/
noncomputable def Tm (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    Fin d → ℝ :=
  affineMap (X.eqv p) p.2.1 (X.sc p s) v

theorem Tm_eq_refl_glueE (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    X.Tm p s v = WaterFilling.refl p.2.1 (glueE (X.act p.1) (X.T.a p.1) (X.eqv p) s v) := by
  funext j
  rw [WaterFilling.refl_apply]
  by_cases hj : j ∈ X.act p.1
  · rw [Tm, affineMap_apply_of_mem _ _ _ _ hj]
    unfold glueE
    rw [glue_apply_of_mem _ _ _ hj]
  · rw [Tm, affineMap_apply_of_not_mem _ _ _ _ hj, glueE_apply_inactive _ _ _ _ _ hj]
    rfl

/-- For active coordinates in `[0,a]` the chart coordinate lies in the orthant box. -/
theorem Tm_mem_orthantBox (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a p.1)) :
    X.Tm p s v ∈ WaterFilling.orthantBox p.2.1 (X.T.a p.1) := by
  rw [Tm_eq_refl_glueE, WaterFilling.mem_orthantBox]
  intro j
  rw [WaterFilling.refl_apply, ← mul_assoc, WaterFilling.sgn_mul_self, one_mul]
  by_cases hj : j ∈ X.act p.1
  · unfold glueE
    rw [glue_apply_of_mem _ _ _ hj]
    exact hv _
  · rw [glueE_apply_inactive _ _ _ _ _ hj]
    exact ⟨Base_val_nonneg _ _ s _, Base_val_le _ _ s _⟩

theorem Tm_mem_box (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a p.1)) : X.Tm p s v ∈ centeredBox d (X.T.a p.1) := by
  rw [X.box_eq p.1]
  exact WaterFilling.orthantBox_subset _ _ (X.Tm_mem_orthantBox p s hv)

theorem Tm_mem_V (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a p.1)) : X.Tm p s v ∈ X.T.V p.1 :=
  X.T.box_subset_V p.1 (X.Tm_mem_box p s hv)

theorem continuous_Tm (p : X.PIdx) :
    Continuous fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) => X.Tm p z.1 z.2 :=
  (continuous_affineMap_pair (X.eqv p) p.2.1).comp
    ((X.continuous_sc p).comp continuous_fst |>.prodMk continuous_snd)

/-- The monomial phase at the chart coordinate is the active monomial. -/
theorem prod_Tm_pow (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    ∏ j, X.Tm p s v j ^ (2 * X.T.k p.1 j) = mono (fun j => 2 * X.T.k p.1 (X.eqv p j).1) v := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ (X.act p.1))]
  have h2 : ∏ j : {j // ¬ inJ (X.act p.1) j}, X.Tm p s v j ^ (2 * X.T.k p.1 j) = 1 :=
    Finset.prod_eq_one fun j _ => by
      rw [X.k_eq_zero_of_not_mem_act j.2]; simp
  rw [h2, mul_one, mono, ← Equiv.prod_comp (X.eqv p)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Tm, affineMap_apply_face, mul_pow, pow_mul, pow_mul, sq, WaterFilling.sgn_mul_self, one_pow,
    one_mul]

/-! ### The smooth core presentation of a piece -/

/-- The amplitude family of a piece: the pull-back of the extended amplitude along the chart
coordinate. -/
noncomputable def amp (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) (X.T.a p.1)) (X.da p) (X.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2.1 (X.contDiff_G p.1)
    (X.T.a p.1)

/-- The active phase exponents of a piece. -/
noncomputable def kA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.T.k p.1 (X.eqv p j).1

/-- The active Jacobian exponents of a piece. -/
noncomputable def hA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.T.h p.1 (X.eqv p j).1

theorem kA_pos (p : X.PIdx) (j : Fin (X.da p)) : 0 < X.kA p j := (X.mem_act).1 (X.eqv p j).2

/-- ★★ **The smooth core presentation of a piece**: constant phase unit `c_i`, transport density
`ρf`, amplitude `G`. -/
noncomputable def piecePresentation (p : X.PIdx) :
    SmoothCorePresentation X.D (X.coreMeasure p) (Base (X.act p.1) (X.T.a p.1)) (X.da p) where
  ν := baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)
  h := X.hA p
  k := X.kA p
  k_pos := X.kA_pos p
  b := (X.T.a p.1)
  b_pos := X.T.a_pos p.1
  βf _ := X.T.phaseConst p.1
  β_cont := continuous_const
  β_pos _ := X.T.phaseConst_pos p.1
  Φ z := X.T.ψ p.1 (X.Tm p z.1 z.2)
  measurable_Φ := (X.T.ψ_measurable p.1).comp (X.continuous_Tm p).measurable
  ρ z := X.ρf p.1 (X.Tm p z.1 z.2)
  measurable_ρ := ((X.contDiff_ρf p.1).continuous.comp (X.continuous_Tm p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => X.ρf_nonneg p.1 _
  amp := X.amp p
  amplitude_eq := by
    refine (ae_snd_mem_box' (X.act p.1) (X.T.a p.1)
      (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (X.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change X.G p.1 (X.Tm p z.1 z.2) = X.ρf p.1 (X.Tm p z.1 z.2) * X.obs (X.T.ψ p.1 (X.Tm p z.1 z.2))
    rw [X.G_eq p.1 (X.Tm_mem_box p z.1 hv), X.ρf_eq p.1 (X.Tm_mem_box p z.1 hv)]
    rfl
  phase_normal := by
    refine (ae_snd_mem_box' (X.act p.1) (X.T.a p.1)
      (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (X.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change X.K (X.T.ψ p.1 (X.Tm p z.1 z.2)) = _
    rw [X.T.phase_eq p.1 _ (X.Tm_mem_V p z.1 hv), X.prod_Tm_pow]
    rfl
  transport := by
    have hΦ : (fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) =>
        X.T.ψ p.1 (X.Tm p z.1 z.2)) =
        (X.T.ψ p.1 ∘ WaterFilling.refl p.2.1) ∘ glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [X.Tm_eq_refl_glueE]
    have hρ : (fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) =>
        ((mono (X.hA p) z.2 * X.ρf p.1 (X.Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => X.T.h p.1 (X.eqv p j).1) z.2 *
          X.ρf p.1 (WaterFilling.refl p.2.1 (glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) z))) := by
      funext z
      rw [X.Tm_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((X.T.ψ_measurable p.1).comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (X.T.ψ_measurable p.1) (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ (X.measurable_ρf p.1), ChartCollar.map_refl_pieceMeasure]
    rfl

/-! ### The smooth core decomposition -/

/-- The enumeration of the pieces. -/
noncomputable def en : Fin (Fintype.card X.PIdx) ≃ X.PIdx := (Fintype.equivFin _).symm

/-- ★★★ **The smooth core decomposition of the population integral over the domain**: one smooth
core presentation per chart and selected orthant, the transport's tail as the tail. -/
noncomputable def decomp : SmoothCoreDecomposition X.D (Fintype.card X.PIdx)
    (fun I => Base (X.act (X.en I).1) (X.T.a (X.en I).1)) (fun I => X.da (X.en I)) where
  core I := X.coreMeasure (X.en I)
  tail := X.T.tail
  measure_eq := by
    rw [X.D_μ, ← X.sum_coreMeasure]
    congr 1
    exact (Equiv.sum_comp X.en X.coreMeasure).symm
  δ₀ := X.T.δ
  δ₀_pos := X.T.δ_pos
  gap := X.T.tail_gap
  chart I := X.piecePresentation (X.en I)

/-- The logarithmic degree is at most `d − 1`. -/
theorem commonD_le : X.decomp.commonD ≤ d - 1 :=
  Finset.sup_le fun I _ => Nat.sub_le_sub_right (X.da_le (X.en I)) 1

/-! ### The population integral is the partition function with insertions on the domain -/

theorem Z_eq_globalLaplace (N : ℝ) :
    X.D.Z N = globalLaplace X.Wdom X.K (fun y => X.prior y * X.obs y) N := by
  unfold LocalisationData.Z LocalisationData.integrand globalLaplace
  rw [X.D_μ, X.D_obs, X.D_phase, priorMeasure]
  have hdens : (fun y => ENNReal.ofReal (X.prior y)) =
      fun y => ((X.prior y).toNNReal : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul X.prior_m.real_toNNReal]
  refine setIntegral_congr_fun X.Wdom_m fun y _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left (X.prior_nonneg y), smul_eq_mul]
  ring

theorem Z_eq (N : ℝ) :
    X.D.Z N = ∫ y in X.Wdom, X.prior y * X.obs y * Real.exp (-N * X.K y) :=
  X.Z_eq_globalLaplace N

/-- ★★★ **The smooth coordinate-free expansion of the partition function with insertions on the
domain**, from a normalised domain core transport: for every `A`,
`∫_{Wdom} prior·obs·e^{−NK} − ∑_{exponent ≤ A} coeff · N^{−α}(log N)^j = o(N^{−A})`, on the
lattice `commonQ⁻¹ℕ` with logarithmic degree `≤ commonD ≤ d − 1`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace X.Wdom X.K fun y => X.prior y * X.obs y)
      X.decomp.coeff X.decomp.commonQ X.decomp.commonD := by
  have h := X.decomp.hasSmoothCoordFreeExpansion
  have hZ : X.D.Z = globalLaplace X.Wdom X.K fun y => X.prior y * X.obs y :=
    funext X.Z_eq_globalLaplace
  rwa [hZ] at h

/-- The expansion in the set-integral form. -/
theorem hasSmoothCoordFreeExpansion_setIntegral :
    HasSmoothCoordFreeExpansion
      (fun N => ∫ y in X.Wdom, X.prior y * X.obs y * Real.exp (-N * X.K y))
      X.decomp.coeff X.decomp.commonQ X.decomp.commonD :=
  X.hasSmoothCoordFreeExpansion

/-- The scalar expansion certificate of the partition function with insertions on the domain. -/
noncomputable def certificate :
    SmoothExpansionCertificate (globalLaplace X.Wdom X.K fun y => X.prior y * X.obs y) where
  Q := X.decomp.commonQ
  Q_pos := X.decomp.commonQ_pos
  D := X.decomp.commonD
  coeff := X.decomp.coeff
  coeff_support := X.decomp.toCertificate.coeff_support
  expansion := by
    have h := X.decomp.cutoffExpansion
    have hZ : X.D.Z = globalLaplace X.Wdom X.K fun y => X.prior y * X.obs y :=
      funext X.Z_eq_globalLaplace
    rwa [hZ] at h

/-- ★★ **Intrinsic coefficients**: two domain bridge inputs for the same domain, phase, prior and
observable (different transports) have the same coefficients. -/
theorem coeff_eq_of_inputs {Y : DomainBridgeInputs d} (hW : X.Wdom = Y.Wdom) (hK : X.K = Y.K)
    (hprior : X.prior = Y.prior) (hobs : X.obs = Y.obs) (μ : ℝ) (q : ℕ) :
    X.decomp.coeff μ q = Y.decomp.coeff μ q := by
  have hZ : (globalLaplace X.Wdom X.K fun y => X.prior y * X.obs y) =
      globalLaplace Y.Wdom Y.K fun y => Y.prior y * Y.obs y := by
    rw [hW, hK, hprior, hobs]
  exact SmoothExpansionCertificate.coeff_eq X.certificate
    { Q := Y.decomp.commonQ, Q_pos := Y.decomp.commonQ_pos, D := Y.decomp.commonD,
      coeff := Y.decomp.coeff, coeff_support := Y.decomp.toCertificate.coeff_support,
      expansion := by rw [hZ]; exact Y.certificate.expansion } μ q

end DomainBridgeInputs

/-! ### The unbundled interface -/

variable {K prior obs : (Fin d → ℝ) → ℝ} {Wdom : Set (Fin d → ℝ)}

/-- Domain bridge inputs from a normalised domain core transport and the smoothness data. -/
noncomputable def DomainBridgeInputs.ofTransport
    (T : NormalisedDomainCoreTransport d K prior Wdom) (hW : IsCompact Wdom) (hK : Measurable K)
    (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y) (hobs : ContDiff ℝ ∞ obs) :
    DomainBridgeInputs d :=
  ⟨K, prior, obs, Wdom, hW, T, hK, hprior, hprior0, hobs⟩

/-- ★★★ **The partition function with insertions of a normalised domain core transport has the
smooth coordinate-free expansion.** -/
theorem _root_.Monomialize.VolumeScaling.NormalisedDomainCoreTransport.hasSmoothCoordFreeExpansion
    (T : NormalisedDomainCoreTransport d K prior Wdom) (hW : IsCompact Wdom) (hK : Measurable K)
    (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion (fun N => ∫ y in Wdom, prior y * obs y * Real.exp (-N * K y))
      (DomainBridgeInputs.ofTransport T hW hK hprior hprior0 hobs).decomp.coeff
      (DomainBridgeInputs.ofTransport T hW hK hprior hprior0 hobs).decomp.commonQ
      (DomainBridgeInputs.ofTransport T hW hK hprior hprior0 hobs).decomp.commonD :=
  (DomainBridgeInputs.ofTransport T hW hK hprior hprior0
    hobs).hasSmoothCoordFreeExpansion_setIntegral

/-- ★★ **Presentation independence**: two normalised domain core transports of the same prior over
the same domain for the same phase give the same coefficients. -/
theorem DomainBridgeInputs.coeff_eq_of_transports
    (T T' : NormalisedDomainCoreTransport d K prior Wdom) (hW : IsCompact Wdom) (hK : Measurable K)
    (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y) (hobs : ContDiff ℝ ∞ obs) (μ : ℝ)
    (q : ℕ) :
    (DomainBridgeInputs.ofTransport T hW hK hprior hprior0 hobs).decomp.coeff μ q =
      (DomainBridgeInputs.ofTransport T' hW hK hprior hprior0 hobs).decomp.coeff μ q :=
  DomainBridgeInputs.coeff_eq_of_inputs
    (DomainBridgeInputs.ofTransport T hW hK hprior hprior0 hobs)
    (Y := DomainBridgeInputs.ofTransport T' hW hK hprior hprior0 hobs) rfl rfl rfl rfl μ q

/-! ### Regression: the identity chart on the positive orthant of a box -/

/-- The half-box: the centred box intersected with the closed positive orthant. -/
def halfBox (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) := centeredBox d a ∩ {y | ∀ j, 0 ≤ y j}

theorem isClosed_nonnegOrthant (d : ℕ) : IsClosed {y : Fin d → ℝ | ∀ j, 0 ≤ y j} := by
  rw [ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)

theorem isCompact_halfBox (d : ℕ) (a : ℝ) : IsCompact (halfBox d a) :=
  (isCompact_centeredBox d a).inter_right (isClosed_nonnegOrthant d)

/-- The open positive orthant is the orthant of the all-`true` sign. -/
theorem openOrthant_true : openOrthant (fun _ => true : CoordSign d) = {y | ∀ j, 0 < y j} := by
  ext y
  simp [openOrthant, Monomialize.VolumeScaling.sgn]

/-- The open positive orthant of the box is, up to the null walls, the half-box. -/
theorem box_inter_selectedOrthants_ae_eq (a : ℝ) :
    (centeredBox d a ∩ selectedOrthants {(fun _ => true : CoordSign d)} : Set (Fin d → ℝ))
      =ᵐ[volume] (halfBox d a : Set (Fin d → ℝ)) := by
  unfold selectedOrthants halfBox
  rw [Finset.set_biUnion_singleton, openOrthant_true, ae_eq_set]
  constructor
  · have hsub : centeredBox d a ∩ {y : Fin d → ℝ | ∀ j, 0 < y j} ⊆
        centeredBox d a ∩ {y | ∀ j, 0 ≤ y j} :=
      fun y hy => mem_inter hy.1 fun j => (hy.2 j).le
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  · refine measure_mono_null (fun y hy => ?_) walls_null
    have hno : ¬ ∀ j, 0 < y j := fun h => hy.2 ⟨hy.1.1, h⟩
    push Not at hno
    obtain ⟨j, hj⟩ := hno
    exact ⟨j, le_antisymm hj (hy.1.2 j)⟩

/-- The identity chart on the positive orthant of `[−a,a]^d` for the monomial phase `c ∏ u^{2k}`:
one selected orthant, no tail (with gap `1`, vacuous). -/
noncomputable def _root_.Monomialize.VolumeScaling.NormalisedDomainCoreTransport.ofMonomialHalfBox
    (k : Fin d → ℕ) (hk : ∃ j, 0 < k j) {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a)
    (prior : (Fin d → ℝ) → ℝ) :
    NormalisedDomainCoreTransport d (fun u => c * ∏ j, u j ^ (2 * k j)) prior (halfBox d a) where
  ι := Unit
  a _ := a
  a_pos _ := ha
  ψ _ := id
  V _ := univ
  V_open _ := isOpen_univ
  box_subset_V _ := subset_univ _
  ψ_measurable _ := measurable_id
  ψ_analytic _ := analyticOnNhd_id
  k _ := k
  k_active _ := hk
  phaseConst _ := c
  phaseConst_pos _ := hc
  phase_eq _ _ _ := rfl
  h _ _ := 0
  jacUnit _ _ := 1
  jacUnit_analytic _ := analyticOnNhd_const
  jacUnit_ne_zero _ _ _ := one_ne_zero
  jac_eq _ u _ := by simp [det_clm_id]
  «ω» _ _ := 1
  ω_measurable _ := measurable_const
  ω_smoothOn _ := contDiffOn_const
  ω_nonneg _ _ := zero_le_one
  ω_le_one _ _ := le_rfl
  sectors _ := {fun _ => true}
  tail := 0
  δ := 1
  δ_pos := one_pos
  tail_gap := by simp
  transport := by
    simp only [Finset.univ_unique, Finset.sum_singleton, add_zero, sectorSource, Measure.map_id,
      absDet, id, fderiv_id, det_clm_id, abs_one, ENNReal.ofReal_one, mul_one]
    congr 1
    exact Measure.restrict_congr_set (box_inter_selectedOrthants_ae_eq a)

/-- The domain bridge inputs of the identity chart on the half-box with a monomial phase. -/
noncomputable def DomainBridgeInputs.ofMonomialHalfBox (k : Fin d → ℕ) (hk : ∃ j, 0 < k j) {c : ℝ}
    (hc : 0 < c) {a : ℝ} (ha : 0 < a) (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y)
    (hobs : ContDiff ℝ ∞ obs) : DomainBridgeInputs d :=
  DomainBridgeInputs.ofTransport (NormalisedDomainCoreTransport.ofMonomialHalfBox k hk hc ha prior)
    (isCompact_halfBox d a) (measurable_monomialPhase k c) hprior hprior0 hobs

/-- ★ **Regression**: `∫_{[−a,a]^d ∩ {y ≥ 0}} prior·obs·e^{−N c ∏y^{2k}}` has the smooth
coordinate-free expansion, through the domain consumer with ONE selected orthant. -/
theorem DomainBridgeInputs.halfBox_hasSmoothCoordFreeExpansion (k : Fin d → ℕ) (hk : ∃ j, 0 < k j)
    {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (hprior : ContDiff ℝ ∞ prior)
    (hprior0 : ∀ y, 0 ≤ prior y) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion
      (fun N => ∫ y in halfBox d a, prior y * obs y * Real.exp (-N * (c * ∏ j, y j ^ (2 * k j))))
      (DomainBridgeInputs.ofMonomialHalfBox k hk hc ha hprior hprior0 hobs).decomp.coeff
      (DomainBridgeInputs.ofMonomialHalfBox k hk hc ha hprior hprior0 hobs).decomp.commonQ
      (DomainBridgeInputs.ofMonomialHalfBox k hk hc ha hprior hprior0 hobs).decomp.commonD :=
  (DomainBridgeInputs.ofMonomialHalfBox k hk hc ha hprior hprior0
    hobs).hasSmoothCoordFreeExpansion_setIntegral

/-- In one dimension the expansion has no logarithms beyond degree `0`. -/
theorem DomainBridgeInputs.commonD_eq_zero_of_dim_one (X : DomainBridgeInputs 1) :
    X.decomp.commonD = 0 :=
  Nat.le_zero.1 X.commonD_le

/-- In one dimension the half-box is the interval `[0,a]`. -/
theorem halfBox_one (a : ℝ) : halfBox 1 a = {y : Fin 1 → ℝ | y 0 ∈ Icc 0 a} := by
  ext y
  simp only [halfBox, centeredBox, mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_one, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (le_abs_self _).trans h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [abs_of_nonneg h1]; exact h2, h1⟩

/-- ★ **The half-line even monomial**: `∫_0^a prior·obs·e^{−N c y^{2k}}` has the smooth
coordinate-free expansion WITHOUT logarithms (a pure power series on the lattice). -/
theorem DomainBridgeInputs.halfLine_hasSmoothCoordFreeExpansion {prior obs : (Fin 1 → ℝ) → ℝ}
    (k : ℕ) (hk : 0 < k) {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (hprior : ContDiff ℝ ∞ prior)
    (hprior0 : ∀ y, 0 ≤ prior y) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion
      (fun N => ∫ y in {y : Fin 1 → ℝ | y 0 ∈ Icc 0 a},
        prior y * obs y * Real.exp (-N * (c * y 0 ^ (2 * k))))
      (DomainBridgeInputs.ofMonomialHalfBox (fun _ => k) ⟨0, hk⟩ hc ha hprior hprior0
        hobs).decomp.coeff
      (DomainBridgeInputs.ofMonomialHalfBox (fun _ => k) ⟨0, hk⟩ hc ha hprior hprior0
        hobs).decomp.commonQ 0 := by
  have h := DomainBridgeInputs.halfBox_hasSmoothCoordFreeExpansion (fun _ : Fin 1 => k) ⟨0, hk⟩ hc
    ha hprior hprior0 hobs
  rw [DomainBridgeInputs.commonD_eq_zero_of_dim_one, halfBox_one] at h
  simpa only [Fin.prod_univ_one] using h

end SmoothEngine

end Grammar
