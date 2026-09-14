/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetPieces
import Grammar.SmoothExtension
import Grammar.SheetAssembly
import Monomialize.Transport.NormalisedCoreTransport

/-!
# The grammar-side consumer of a normalised core transport (consult #119, Unit 3)

From hironaka's resolution-bridge output `NormalisedCoreTransport d K prior` — finitely many
charts `ψ_i` on the common box `[−a,a]^d`, analytic on open neighbourhoods `V_i`, with the phase
in exact normalised monomial form `K ∘ ψ_i = c_i ∏ u^{2k_i}`, Jacobian `b_i ∏ u^{h_i}`, smooth
weights `ω_i`, a tail measure with a phase gap and the exact transport
`∑_i (ψ_i)_*(core sources) + tail = vol·prior` — and a smooth compactly supported nonnegative
prior and a smooth observable, we build the `SmoothCoreDecomposition` of the localisation datum
`(vol·prior, K, obs)` on ALL of `ℝ^d`: one smooth core presentation per chart and orthant, with
the CONSTANT phase unit `c_i`, the transport density `ω_i |b_i| prior∘ψ_i` and the amplitude
`ω_i |b_i| prior∘ψ_i obs∘ψ_i`, both extended from `V_i` to globally smooth functions
(`exists_contDiff_eqOn_of_contDiffOn`), and the transport's tail as the tail. The phase is
nonnegative a.e. for the prior measure WITHOUT a global hypothesis: on the cores it is the monomial,
on the tail it exceeds the gap. Hence ★★★ `hasSmoothCoordFreeExpansion`: the partition function
with insertions `∫ prior·obs·e^{−NK}` has the smooth coordinate-free expansion, with INTRINSIC
coefficients (`coeff_eq_of_transports`: independent of the transport). The no-tail monomial
instance is the regression `monomial_hasSmoothCoordFreeExpansion`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

/-- **Bridge inputs**: a normalised core transport of a smooth compactly supported nonnegative
prior, a measurable phase and a smooth observable. -/
structure BridgeInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

theorem prior_m : Measurable X.prior := X.prior_smooth.continuous.measurable

/-- The prior measure lives on the compact support of the prior. -/
theorem priorMeasure_eq_restrict : X.priorMeasure =
    (volume.restrict (tsupport X.prior)).withDensity fun y => ENNReal.ofReal (X.prior y) := by
  unfold priorMeasure
  rw [← withDensity_indicator (isClosed_tsupport _).measurableSet]
  congr 1
  funext y
  by_cases hy : y ∈ tsupport X.prior
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, ENNReal.ofReal_zero]

theorem obs_int : Integrable X.obs X.priorMeasure := by
  rw [priorMeasure_eq_restrict]
  exact SheetAssembly.integrable_of_continuous_of_subset_compact X.prior_smooth.continuous
    X.obs_smooth.continuous X.prior_compact subset_rfl (isClosed_tsupport _).measurableSet

/-- The phase is nonnegative a.e. on every transported core: it is the monomial there. -/
theorem K_nonneg_core (i : X.T.ι) :
    ∀ᵐ y ∂((coreSource (X.T.ψ i) (X.T.ω i) (X.T.a i) X.prior).map (X.T.ψ i)), 0 ≤ X.K y := by
  rw [ae_map_iff (X.T.ψ_measurable i).aemeasurable (measurableSet_le measurable_const X.K_m)]
  unfold coreSource
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  refine (ae_restrict_mem (X.T.measurableSet_box i)).mono fun u hu => ?_
  change 0 ≤ X.K (X.T.ψ i u)
  rw [X.T.phase_eq i u (X.T.box_subset_V i hu)]
  exact mul_nonneg (X.T.phaseConst_pos i).le
    (Finset.prod_nonneg fun j _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

/-- ★ **The phase is nonnegative a.e. for the prior measure**, from the transport alone: the
monomial on the cores, above the gap on the tail. -/
theorem K_nonneg : ∀ᵐ y ∂X.priorMeasure, 0 ≤ X.K y := by
  unfold priorMeasure
  rw [← X.T.transport, ae_add_measure_iff, ← Measure.sum_fintype,
    Measure.ae_sum_iff' (measurableSet_le measurable_const X.K_m)]
  exact ⟨fun i => X.K_nonneg_core i, X.T.tail_gap.mono fun y hy => X.T.δ_pos.le.trans hy⟩

/-- The localisation datum `(vol·prior, K, obs)`. -/
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

/-! ### The core sources as weighted box measures, split over the orthants -/

/-- The core source of chart `i` is the box measure with density `|u|^h · ρf`. -/
theorem coreSource_eq (i : X.T.ι) : coreSource (X.T.ψ i) (X.T.ω i) (X.T.a i) X.prior =
    (volume.restrict (centeredBox d (X.T.a i))).withDensity fun u =>
      ENNReal.ofReal (NormalisedBox.wgt (X.T.h i) u * X.ρf i u) := by
  unfold coreSource
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (X.T.measurableSet_box i)]
  refine Eventually.of_forall fun u hu => ?_
  rw [absDet, X.T.jac_eq i u (X.T.box_subset_V i hu), abs_mul, Finset.abs_prod,
    ← ENNReal.ofReal_mul (mul_nonneg (X.prior_nonneg _) (X.T.ω_nonneg i u)), X.ρf_eq i hu]
  simp only [abs_pow]
  unfold ρloc NormalisedBox.wgt
  congr 1
  ring

/-- The signed box is, up to the null walls, the disjoint union of the orthant boxes. -/
theorem restrict_signedBox_eq (a : ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (piBox d (Icc (-a) a)) =
      ∑ σ : WaterFilling.CoordSign d, volume.restrict (WaterFilling.orthantBox σ a) := by
  rw [WaterFilling.signedBox_eq_iUnion a, Measure.restrict_iUnion_ae ?_
    (fun σ => (WaterFilling.measurableSet_orthantBox σ a).nullMeasurableSet), Measure.sum_fintype]
  intro σ τ hστ
  refine measure_mono_null (fun w hw => ?_) walls_null
  by_contra hw0
  have hne : ∀ j, w j ≠ 0 := fun j hj => hw0 ⟨j, hj⟩
  exact hστ ((WaterFilling.eq_signOf_of_mem_orthantBox hne hw.1).trans
    (WaterFilling.eq_signOf_of_mem_orthantBox hne hw.2).symm)

/-! ### Charts, active sets and pieces -/

/-- The active set of chart `i`. -/
def act (i : X.T.ι) : Finset (Fin d) := Finset.univ.filter fun j => 0 < X.T.k i j

theorem mem_act {i : X.T.ι} {j : Fin d} : j ∈ X.act i ↔ 0 < X.T.k i j := by
  simp [act]

theorem k_eq_zero_of_not_mem_act {i : X.T.ι} {j : Fin d} (hj : j ∉ X.act i) : X.T.k i j = 0 := by
  rw [mem_act] at hj
  omega

/-- The pieces: a chart and an orthant (all orthants are selected). -/
abbrev PIdx : Type := Σ _ : X.T.ι, WaterFilling.CoordSign d

/-- The core measure of a piece: the weighted orthant-box measure pushed along the chart. -/
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (X.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (X.T.h p.1) w * X.ρf p.1 w)).map (X.T.ψ p.1)

/-- The pieces of a chart exhaust its transported core source. -/
theorem sum_coreMeasure_chart (i : X.T.ι) :
    ∑ σ : WaterFilling.CoordSign d, X.coreMeasure ⟨i, σ⟩ =
      (coreSource (X.T.ψ i) (X.T.ω i) (X.T.a i) X.prior).map (X.T.ψ i) := by
  unfold coreMeasure
  rw [← SmoothSheetInputs.map_finset_sum' _ _ (X.T.ψ_measurable i), X.coreSource_eq, X.box_eq i,
    restrict_signedBox_eq, ← Measure.sum_fintype fun σ : WaterFilling.CoordSign d =>
      volume.restrict (WaterFilling.orthantBox σ (X.T.a i)), withDensity_sum, Measure.sum_fintype]

/-- ★ **The pieces and the tail exhaust the prior measure** (the transport identity). -/
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
  fun j => WaterFilling.sgn p.2 j.1 * s.1 j

theorem continuous_sc (p : X.PIdx) : Continuous (X.sc p) :=
  continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- The chart coordinate of a piece: reflected active coordinates `v`, reflected inactive
coordinates `s`. -/
noncomputable def Tm (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    Fin d → ℝ :=
  affineMap (X.eqv p) p.2 (X.sc p s) v

theorem Tm_eq_refl_glueE (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    X.Tm p s v = WaterFilling.refl p.2 (glueE (X.act p.1) (X.T.a p.1) (X.eqv p) s v) := by
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
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a p.1)) : X.Tm p s v ∈ WaterFilling.orthantBox p.2 (X.T.a p.1) := by
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
  (continuous_affineMap_pair (X.eqv p) p.2).comp
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
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2 (X.contDiff_G p.1) (X.T.a p.1)

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
        (X.T.ψ p.1 ∘ WaterFilling.refl p.2) ∘ glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [X.Tm_eq_refl_glueE]
    have hρ : (fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) =>
        ((mono (X.hA p) z.2 * X.ρf p.1 (X.Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => X.T.h p.1 (X.eqv p j).1) z.2 *
          X.ρf p.1 (WaterFilling.refl p.2 (glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) z))) := by
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

/-- ★★★ **The smooth core decomposition of the population integral**: one smooth core presentation
per chart and orthant, the transport's tail as the tail. -/
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

/-! ### The population integral is the partition function with insertions -/

theorem Z_eq (N : ℝ) : X.D.Z N = ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y) := by
  unfold LocalisationData.Z LocalisationData.integrand
  rw [X.D_μ, X.D_obs, X.D_phase, priorMeasure]
  have hdens : (fun y => ENNReal.ofReal (X.prior y)) =
      fun y => ((X.prior y).toNNReal : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul X.prior_m.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left (X.prior_nonneg y), smul_eq_mul]
  ring

theorem Z_eq_globalLaplace (N : ℝ) :
    X.D.Z N = globalLaplace univ X.K (fun y => X.prior y * X.obs y) N := by
  rw [X.Z_eq]
  unfold globalLaplace
  rw [Measure.restrict_univ]

/-- ★★★ **The smooth coordinate-free expansion of the partition function with insertions**, from a
normalised core transport: for every `A`,
`∫ prior·obs·e^{−NK} − ∑_{exponent ≤ A} coeff · N^{−α}(log N)^j = o(N^{−A})`, on the lattice
`commonQ⁻¹ℕ` with logarithmic degree `≤ commonD ≤ d − 1`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (fun N => ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y))
      X.decomp.coeff X.decomp.commonQ X.decomp.commonD := by
  have h := X.decomp.hasSmoothCoordFreeExpansion
  have hZ : X.D.Z = fun N => ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y) := funext X.Z_eq
  rwa [hZ] at h

/-- The expansion in the `globalLaplace` form over `univ`. -/
theorem hasSmoothCoordFreeExpansion_globalLaplace :
    HasSmoothCoordFreeExpansion (globalLaplace univ X.K fun y => X.prior y * X.obs y)
      X.decomp.coeff X.decomp.commonQ X.decomp.commonD := by
  have h := X.decomp.hasSmoothCoordFreeExpansion
  have hZ : X.D.Z = globalLaplace univ X.K fun y => X.prior y * X.obs y :=
    funext X.Z_eq_globalLaplace
  rwa [hZ] at h

/-- The scalar expansion certificate of the partition function with insertions. -/
noncomputable def certificate :
    SmoothExpansionCertificate fun N => ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y) where
  Q := X.decomp.commonQ
  Q_pos := X.decomp.commonQ_pos
  D := X.decomp.commonD
  coeff := X.decomp.coeff
  coeff_support := X.decomp.toCertificate.coeff_support
  expansion := by
    have h := X.decomp.cutoffExpansion
    have hZ : X.D.Z = fun N => ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y) := funext X.Z_eq
    rwa [hZ] at h

/-- ★★ **Intrinsic coefficients**: two bridge inputs for the same phase, prior and observable
(different transports) have the same coefficients. -/
theorem coeff_eq_of_inputs {Y : BridgeInputs d} (hK : X.K = Y.K) (hprior : X.prior = Y.prior)
    (hobs : X.obs = Y.obs) (μ : ℝ) (q : ℕ) : X.decomp.coeff μ q = Y.decomp.coeff μ q := by
  have hZ : (fun N => ∫ y, X.prior y * X.obs y * Real.exp (-N * X.K y)) =
      fun N => ∫ y, Y.prior y * Y.obs y * Real.exp (-N * Y.K y) := by
    rw [hK, hprior, hobs]
  exact SmoothExpansionCertificate.coeff_eq X.certificate
    { Q := Y.decomp.commonQ, Q_pos := Y.decomp.commonQ_pos, D := Y.decomp.commonD,
      coeff := Y.decomp.coeff, coeff_support := Y.decomp.toCertificate.coeff_support,
      expansion := by rw [hZ]; exact Y.certificate.expansion } μ q

end BridgeInputs

/-! ### The unbundled interface -/

variable {K prior obs : (Fin d → ℝ) → ℝ}

/-- Bridge inputs from a normalised core transport and the smoothness data. -/
noncomputable def BridgeInputs.ofTransport (T : NormalisedCoreTransport d K prior)
    (hK : Measurable K) (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hobs : ContDiff ℝ ∞ obs) : BridgeInputs d :=
  ⟨K, prior, obs, T, hK, hprior, hprior0, hpc, hobs⟩

/-- ★★★ **The partition function with insertions of a normalised core transport has the smooth
coordinate-free expansion.** -/
theorem _root_.Monomialize.VolumeScaling.NormalisedCoreTransport.hasSmoothCoordFreeExpansion
    (T : NormalisedCoreTransport d K prior) (hK : Measurable K) (hprior : ContDiff ℝ ∞ prior)
    (hprior0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y))
      (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).decomp.coeff
      (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).decomp.commonQ
      (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).decomp.commonD :=
  (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).hasSmoothCoordFreeExpansion

/-- ★★ **Presentation independence**: two normalised core transports of the same prior for the same
phase give the same coefficients. -/
theorem BridgeInputs.coeff_eq_of_transports (T T' : NormalisedCoreTransport d K prior)
    (hK : Measurable K) (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hobs : ContDiff ℝ ∞ obs) (μ : ℝ) (q : ℕ) :
    (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).decomp.coeff μ q =
      (BridgeInputs.ofTransport T' hK hprior hprior0 hpc hobs).decomp.coeff μ q :=
  BridgeInputs.coeff_eq_of_inputs (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs)
    (Y := BridgeInputs.ofTransport T' hK hprior hprior0 hpc hobs) rfl rfl rfl μ q

/-! ### Regression: the no-tail monomial instance -/

theorem measurable_monomialPhase (k : Fin d → ℕ) (c : ℝ) :
    Measurable fun u : Fin d → ℝ => c * ∏ j, u j ^ (2 * k j) :=
  (continuous_const.mul (continuous_finsetProd _ fun j _ =>
    (continuous_apply j).pow _)).measurable

/-- The bridge inputs of the identity chart on a monomial phase with a prior supported in the
box. -/
noncomputable def BridgeInputs.ofMonomial (k : Fin d → ℕ) (hk : ∃ j, 0 < k j) {c : ℝ} (hc : 0 < c)
    {a : ℝ} (ha : 0 < a) (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y)
    (hsupp : ∀ y, y ∉ centeredBox d a → prior y = 0) (hobs : ContDiff ℝ ∞ obs) : BridgeInputs d :=
  BridgeInputs.ofTransport (NormalisedCoreTransport.ofMonomialNoTail k hk hc ha hsupp)
    (measurable_monomialPhase k c) hprior hprior0
    (HasCompactSupport.intro (isCompact_centeredBox d a) hsupp) hobs

/-- ★ **Regression**: `∫ prior·obs·e^{−N c ∏u^{2k}}` for a prior supported in the box has the smooth
coordinate-free expansion. -/
theorem BridgeInputs.monomial_hasSmoothCoordFreeExpansion (k : Fin d → ℕ) (hk : ∃ j, 0 < k j)
    {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (hprior : ContDiff ℝ ∞ prior)
    (hprior0 : ∀ y, 0 ≤ prior y) (hsupp : ∀ y, y ∉ centeredBox d a → prior y = 0)
    (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion
      (fun N => ∫ y, prior y * obs y * Real.exp (-N * (c * ∏ j, y j ^ (2 * k j))))
      (BridgeInputs.ofMonomial k hk hc ha hprior hprior0 hsupp hobs).decomp.coeff
      (BridgeInputs.ofMonomial k hk hc ha hprior hprior0 hsupp hobs).decomp.commonQ
      (BridgeInputs.ofMonomial k hk hc ha hprior hprior0 hsupp hobs).decomp.commonD :=
  (BridgeInputs.ofMonomial k hk hc ha hprior hprior0 hsupp hobs).hasSmoothCoordFreeExpansion

/-- In one dimension the expansion has no logarithms beyond degree `0`. -/
theorem BridgeInputs.commonD_eq_zero_of_dim_one (X : BridgeInputs 1) : X.decomp.commonD = 0 :=
  Nat.le_zero.1 X.commonD_le

end SmoothEngine

end Grammar
