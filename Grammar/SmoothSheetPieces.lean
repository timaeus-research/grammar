/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetTransport
import Grammar.SmoothAffineFamily
import Grammar.SmoothCoreCertificate
import Monomialize.Transport.DomainSectorAtlas
import Monomialize.Transport.WeightedSectorAtlas

/-!
# Smooth sheet inputs and the smooth core presentation of a chart piece (U6b.3, consult #117 §7)

`SmoothSheetInputs d`: a weighted domain atlas with symmetric chart boxes `[−a,a]^d`, SMOOTH chart
data (charts, weights, `|Jacobian unit|`, prior, observable — globally `C^∞` in this first version)
and a TANGENTIAL phase unit; NO stratum-adapted weight hypotheses (`ω_indep`, `ω_contOn`) and NO
holomorphic packets. For every chart `i` and selected orthant `σ` the chart PIECE is the reflected
orthant box; its active coordinates (`kᵢⱼ > 0`) are enumerated by `e`, its inactive coordinates
form the compact base `Base (act i) a`, and the chart coordinate is the affine map `T s v`.
★★ `piecePresentation`: the piece is a `SmoothCorePresentation` of the localisation datum
`(vol|_W)·prior, K, obs` onto the core measure `((vol|_{orthant box})·|w|^h ω|j| prior∘φ).map φ`:
the nonnegative transport density is `ω · |j| · prior∘φ`, the phase unit `β(s) = u(T s 0)`, the
amplitude family the pull-back of the smooth `ω·|j|·prior∘φ·obs∘φ` along `T`
(`SmoothAmplitudeFamily.ofAffine`), and the transport is `map_glueE'_pieceMeasure` followed by the
orthant reflection. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

/-- **Smooth sheet inputs**: a weighted domain atlas with symmetric boxes, smooth chart data and a
tangential phase unit. -/
structure SmoothSheetInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  K_m : Measurable K
  /-- the resolved set of the atlas -/
  Ω : Set (Fin d → ℝ)
  /-- the weighted domain atlas -/
  A : WeightedDomainAtlas d K Ω
  /-- the half side of the chart boxes -/
  a : ℝ
  ha : 0 < a
  lo_eq : ∀ i j, A.lo i j = -a
  hi_eq : ∀ i j, A.hi i j = a
  /-- the phase is nonnegative on the domain -/
  K_nonneg : ∀ w ∈ A.W, 0 ≤ K w
  /-- the prior and the observable -/
  prior : (Fin d → ℝ) → ℝ
  obs : (Fin d → ℝ) → ℝ
  prior_nonneg : ∀ w, 0 ≤ prior w
  prior_smooth : ContDiff ℝ ∞ prior
  obs_smooth : ContDiff ℝ ∞ obs
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  /-- smooth chart data -/
  φ_smooth : ∀ i, ContDiff ℝ ∞ (A.φ i)
  ω_smooth : ∀ i, ContDiff ℝ ∞ (A.ω i)
  jacAbs_smooth : ∀ i, ContDiff ℝ ∞ fun y => |A.jacUnit i y|
  /-- the phase unit is tangential: it does not depend on the active coordinates -/
  hu_tan : ∀ i (w w' : Fin d → ℝ), (∀ j, ¬ 0 < A.k i j → w j = w' j) →
    A.phaseUnit i w = A.phaseUnit i w'

variable {d : ℕ} (X : SmoothSheetInputs d)

namespace SmoothSheetInputs

/-! ### The localisation datum -/

/-- The prior measure on the domain. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  (volume.restrict X.A.W).withDensity fun w => ENNReal.ofReal (X.prior w)

theorem prior_m : Measurable X.prior := X.prior_smooth.continuous.measurable

theorem obs_m : Measurable X.obs := X.obs_smooth.continuous.measurable

/-- The localisation datum `((vol|_W)·prior, K, obs)`. -/
noncomputable def D : LocalisationData (Fin d → ℝ) where
  μ := X.priorMeasure
  phase := X.K
  obs := X.obs
  phase_measurable := X.K_m
  phase_nonneg := by
    have h1 : ∀ᵐ w ∂(volume.restrict X.A.W), 0 ≤ X.K w :=
      (ae_restrict_mem X.A.measurableSet_W).mono fun w hw => X.K_nonneg w hw
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  obs_integrable := X.obs_int
  δ := 1
  δ_pos := one_pos

theorem D_μ : X.D.μ = X.priorMeasure := rfl
theorem D_phase : X.D.phase = X.K := rfl
theorem D_obs : X.D.obs = X.obs := rfl

/-! ### Charts, active sets and pieces -/

theorem dom_eq (i : X.A.ι) : X.A.dom i = piBox d (Icc (-X.a) X.a) := by
  rw [X.A.dom_eq]
  simp only [X.lo_eq, X.hi_eq]
  rfl

/-- The active set of chart `i`. -/
def act (i : X.A.ι) : Finset (Fin d) := Finset.univ.filter fun j => 0 < X.A.k i j

theorem mem_act {i : X.A.ι} {j : Fin d} : j ∈ X.act i ↔ 0 < X.A.k i j := by
  simp [act]

theorem k_eq_zero_of_not_mem_act {i : X.A.ι} {j : Fin d} (hj : j ∉ X.act i) : X.A.k i j = 0 := by
  rw [mem_act] at hj
  omega

/-- The pieces: a chart and a selected orthant. -/
abbrev PIdx : Type := Σ i : X.A.ι, ↥(X.A.signs i)

/-- The nonnegative density factor `ω · |j| · prior ∘ φ` of chart `i`. -/
noncomputable def ϕf (i : X.A.ι) (y : Fin d → ℝ) : ℝ :=
  X.A.ω i y * |X.A.jacUnit i y| * X.prior (X.A.φ i y)

theorem ϕf_nonneg (i : X.A.ι) (y : Fin d → ℝ) : 0 ≤ X.ϕf i y :=
  mul_nonneg (mul_nonneg (X.A.ω_nonneg i y) (abs_nonneg _)) (X.prior_nonneg _)

theorem contDiff_ϕf (i : X.A.ι) : ContDiff ℝ ∞ (X.ϕf i) :=
  ((X.ω_smooth i).mul (X.jacAbs_smooth i)).mul (X.prior_smooth.comp (X.φ_smooth i))

theorem measurable_ϕf (i : X.A.ι) : Measurable (X.ϕf i) :=
  (X.contDiff_ϕf i).continuous.measurable

/-- The full smooth amplitude `ω · |j| · prior ∘ φ · obs ∘ φ` of chart `i`. -/
noncomputable def G (i : X.A.ι) (y : Fin d → ℝ) : ℝ := X.ϕf i y * X.obs (X.A.φ i y)

theorem contDiff_G (i : X.A.ι) : ContDiff ℝ ∞ (X.G i) :=
  (X.contDiff_ϕf i).mul (X.obs_smooth.comp (X.φ_smooth i))

/-- The core measure of a piece: the weighted orthant-box measure pushed along the chart. -/
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2.1 X.a)).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (X.A.h p.1) w * X.ϕf p.1 w)).map (X.A.φ p.1)

/-- The number of active coordinates of a piece. -/
noncomputable def da (p : X.PIdx) : ℕ := Fintype.card {j // inJ (X.act p.1) j}

/-- The enumeration of the active coordinates. -/
noncomputable def eqv (p : X.PIdx) : Fin (X.da p) ≃ {j // inJ (X.act p.1) j} :=
  (Fintype.equivFin _).symm

/-- The reflected inactive coordinates of a base point. -/
def sc (p : X.PIdx) (s : Base (X.act p.1) X.a) : {j // ¬ inJ (X.act p.1) j} → ℝ :=
  fun j => WaterFilling.sgn p.2.1 j.1 * s.1 j

theorem continuous_sc (p : X.PIdx) : Continuous (X.sc p) :=
  continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- The chart coordinate of a piece: reflected active coordinates `v`, reflected inactive
coordinates `s`. -/
noncomputable def T (p : X.PIdx) (s : Base (X.act p.1) X.a) (v : Fin (X.da p) → ℝ) : Fin d → ℝ :=
  affineMap (X.eqv p) p.2.1 (X.sc p s) v

theorem T_eq_refl_glueE (p : X.PIdx) (s : Base (X.act p.1) X.a) (v : Fin (X.da p) → ℝ) :
    X.T p s v = WaterFilling.refl p.2.1 (glueE (X.act p.1) X.a (X.eqv p) s v) := by
  funext j
  rw [WaterFilling.refl_apply]
  by_cases hj : j ∈ X.act p.1
  · rw [T, affineMap_apply_of_mem _ _ _ _ hj]
    unfold glueE
    rw [glue_apply_of_mem _ _ _ hj]
  · rw [T, affineMap_apply_of_not_mem _ _ _ _ hj, glueE_apply_inactive _ _ _ _ _ hj]
    rfl

/-- For active coordinates in `[0,a]` the chart coordinate lies in the orthant box. -/
theorem T_mem_orthantBox (p : X.PIdx) (s : Base (X.act p.1) X.a) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 X.a) : X.T p s v ∈ WaterFilling.orthantBox p.2.1 X.a := by
  rw [T_eq_refl_glueE, WaterFilling.mem_orthantBox]
  intro j
  rw [WaterFilling.refl_apply, ← mul_assoc, WaterFilling.sgn_mul_self, one_mul]
  by_cases hj : j ∈ X.act p.1
  · unfold glueE
    rw [glue_apply_of_mem _ _ _ hj]
    exact hv _
  · rw [glueE_apply_inactive _ _ _ _ _ hj]
    exact ⟨Base_val_nonneg _ _ s _, Base_val_le _ _ s _⟩

theorem T_mem_V (p : X.PIdx) (s : Base (X.act p.1) X.a) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 X.a) : X.T p s v ∈ X.A.V p.1 := by
  refine X.A.dom_subset_V p.1 ?_
  rw [X.dom_eq]
  exact WaterFilling.orthantBox_subset _ _ (X.T_mem_orthantBox p s hv)

theorem zero_mem_Icc (j : Fin (X.da p)) : (0 : Fin (X.da p) → ℝ) j ∈ Icc 0 X.a :=
  ⟨le_rfl, X.ha.le⟩

theorem continuous_T (p : X.PIdx) :
    Continuous fun z : Base (X.act p.1) X.a × (Fin (X.da p) → ℝ) => X.T p z.1 z.2 :=
  (continuous_affineMap_pair (X.eqv p) p.2.1).comp
    ((X.continuous_sc p).comp continuous_fst |>.prodMk continuous_snd)

/-- The tangential phase unit of a piece, as a function on the base. -/
noncomputable def βf (p : X.PIdx) (s : Base (X.act p.1) X.a) : ℝ := X.A.phaseUnit p.1 (X.T p s 0)

theorem continuous_βf (p : X.PIdx) : Continuous (X.βf p) :=
  (X.A.phaseUnit_analytic p.1).continuousOn.comp_continuous
    ((X.continuous_T p).comp (continuous_id.prodMk continuous_const))
    fun s => X.T_mem_V p s (X.zero_mem_Icc)

theorem βf_pos (p : X.PIdx) (s : Base (X.act p.1) X.a) : 0 < X.βf p s :=
  X.A.phaseUnit_pos p.1 _ (X.T_mem_V p s (X.zero_mem_Icc))

/-- The phase unit at the chart coordinate is the tangential unit of the base point. -/
theorem phaseUnit_T (p : X.PIdx) (s : Base (X.act p.1) X.a) (v : Fin (X.da p) → ℝ) :
    X.A.phaseUnit p.1 (X.T p s v) = X.βf p s := by
  unfold βf
  refine X.hu_tan p.1 _ _ fun j hj => ?_
  have hj' : j ∉ X.act p.1 := fun h => hj ((X.mem_act).1 h)
  rw [T, T, affineMap_apply_of_not_mem _ _ _ _ hj', affineMap_apply_of_not_mem _ _ _ _ hj']

/-- The monomial phase at the chart coordinate is the active monomial. -/
theorem prod_T_pow (p : X.PIdx) (s : Base (X.act p.1) X.a) (v : Fin (X.da p) → ℝ) :
    ∏ j, X.T p s v j ^ (2 * X.A.k p.1 j) = mono (fun j => 2 * X.A.k p.1 (X.eqv p j).1) v := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ (X.act p.1))]
  have h2 : ∏ j : {j // ¬ inJ (X.act p.1) j}, X.T p s v j ^ (2 * X.A.k p.1 j) = 1 :=
    Finset.prod_eq_one fun j _ => by
      rw [X.k_eq_zero_of_not_mem_act j.2]; simp
  rw [h2, mul_one, mono, ← Equiv.prod_comp (X.eqv p)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [T, affineMap_apply_face, mul_pow, pow_mul, pow_mul, sq, WaterFilling.sgn_mul_self, one_pow,
    one_mul]

/-! ### The smooth core presentation of a piece -/

/-- The base map is continuous, so the pulled-back amplitude is a smooth amplitude family. -/
noncomputable def amp (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) X.a) (X.da p) X.a :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2.1 (X.contDiff_G p.1) X.a

theorem amp_apply (p : X.PIdx) (s : Base (X.act p.1) X.a) (v : Fin (X.da p) → ℝ) :
    X.amp p s v = X.G p.1 (X.T p s v) := rfl

/-- The active phase exponents of a piece. -/
noncomputable def kA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.A.k p.1 (X.eqv p j).1

/-- The active Jacobian exponents of a piece. -/
noncomputable def hA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.A.h p.1 (X.eqv p j).1

theorem kA_pos (p : X.PIdx) (j : Fin (X.da p)) : 0 < X.kA p j :=
  (X.mem_act).1 (X.eqv p j).2

/-- ★★ **The smooth core presentation of a chart piece.** -/
noncomputable def piecePresentation (p : X.PIdx) :
    SmoothCorePresentation X.D (X.coreMeasure p) (Base (X.act p.1) X.a) (X.da p) where
  ν := baseMeasure (X.act p.1) X.a (X.A.h p.1)
  h := X.hA p
  k := X.kA p
  k_pos := X.kA_pos p
  b := X.a
  b_pos := X.ha
  βf := X.βf p
  β_cont := X.continuous_βf p
  β_pos := X.βf_pos p
  Φ z := X.A.φ p.1 (X.T p z.1 z.2)
  measurable_Φ := ((X.φ_smooth p.1).continuous.comp (X.continuous_T p)).measurable
  ρ z := X.ϕf p.1 (X.T p z.1 z.2)
  measurable_ρ := ((X.contDiff_ϕf p.1).continuous.comp (X.continuous_T p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => X.ϕf_nonneg p.1 _
  amp := X.amp p
  amplitude_eq := Eventually.of_forall fun z => rfl
  phase_normal := by
    refine (ae_snd_mem_box' (X.act p.1) X.a (baseMeasure (X.act p.1) X.a (X.A.h p.1))).mono
      fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 X.a := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change X.K (X.A.φ p.1 (X.T p z.1 z.2)) = _
    rw [X.A.phase_eq p.1 _ (X.T_mem_V p z.1 hv), X.phaseUnit_T, X.prod_T_pow]
    rfl
  transport := by
    have hΦ : (fun z : Base (X.act p.1) X.a × (Fin (X.da p) → ℝ) => X.A.φ p.1 (X.T p z.1 z.2)) =
        (X.A.φ p.1 ∘ WaterFilling.refl p.2.1) ∘ glueE' (X.act p.1) X.a (X.eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [X.T_eq_refl_glueE]
    have hρ : (fun z : Base (X.act p.1) X.a × (Fin (X.da p) → ℝ) =>
        ((mono (X.hA p) z.2 * X.ϕf p.1 (X.T p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => X.A.h p.1 (X.eqv p j).1) z.2 *
          X.ϕf p.1 (WaterFilling.refl p.2.1 (glueE' (X.act p.1) X.a (X.eqv p) z))) := by
      funext z
      rw [X.T_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((X.φ_smooth p.1).continuous.measurable.comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (X.φ_smooth p.1).continuous.measurable (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ (X.measurable_ϕf p.1), ChartCollar.map_refl_pieceMeasure]
    rfl

end SmoothSheetInputs

end SmoothEngine

end Grammar
