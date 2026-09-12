/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateResolvedGeometry
import Grammar.AnalyticSeriesFamily
import Grammar.CoreNormalMomentRepresentation
import Grammar.CoordFreeExpansionCompletion

/-!
# Certificates from series data on the coordinate box (CCCXVIII)

Consult #95 unit 2, the first **producer**: for the coordinate model in dimension `n+1` with the
monomial phase `K = ∏ u_i^{2k_i}`, on the box `W = [0,b]^{n+1}`, and for a prior `ϕ` and an
observable `φ` given by `b'`-weighted ℓ¹ coefficient families (`b < b'`) with `ϕ ≥ 0` on the box,
both certificates of the coordinate-free expansion theorem are CONSTRUCTED — not assumed:

* the prior and the observable are realised globally by clamping the coordinates into
  `[-r, r]`, `b < r < b'` (`evalFClamp`): globally continuous, equal to the series on the box,
  analytic at `0` with the symmetric-monomial series on the ball of radius `r`;
* `locData` (prior-weighted Lebesgue measure on the box), the single core `core` at the deepest
  stratum (Dirac base, normal box `(0,b]^{n+1}`, `Φ(s,u) = u`, density `c(s,u) = ϕ(u)`,
  `h = 0`, exponents `k`, amplitude datum `fϕ ⋆ fφ`), with the exact transport identity
  (`withDensity_map_of_embedding`), the core decomposition with a NULL tail (`W ∖ (0,b]^{n+1}` lies
  in the coordinate hyperplanes), the normal-moment presentation from `polySeriesD fφ`;
* `certificate : ResolvedCertificate geometry normalData W K ϕ φ` and
  `coeffCertificate` (density family `fϕ`, `jetFamily φ = fφ` by `jetFamily_evalFClamp`);
* ★★★ `hasCoordFreeExpansion_box`: the coordinate-free expansion of `∫_{[0,b]^{n+1}} φ ϕ e^{−nK}`
  with spectrum `{(α, j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ n}`, `Q = 2∏k_i`, for EVERY such pair of series.

Non-claims: a positive rectangle with one chart; general regions and positive-dimensional
strata need the collar decomposition (consult #95 §3B); the certificates are hand-assembled from
the coordinate model, not from a resolution produced by the hironaka interface.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

/-! ### Clamping -/

section Clamp

variable {d : ℕ}

/-- Coordinatewise clamping into `[-r, r]`. -/
noncomputable def clamp (r : ℝ) (hr : 0 ≤ r) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (Set.projIcc (-r) r (by linarith) (u i) : ℝ)

theorem continuous_clamp (r : ℝ) (hr : 0 ≤ r) : Continuous (clamp (d := d) r hr) :=
  continuous_pi fun i => (continuous_subtype_val.comp continuous_projIcc).comp (continuous_apply i)

theorem clamp_eq_self {r : ℝ} (hr : 0 ≤ r) {u : Fin d → ℝ} (hu : ∀ i, |u i| ≤ r) :
    clamp r hr u = u := by
  funext i
  unfold clamp
  rw [Set.projIcc_of_mem _ ⟨by linarith [(abs_le.1 (hu i)).1], (abs_le.1 (hu i)).2⟩]

theorem abs_clamp_le {r : ℝ} (hr : 0 ≤ r) (u : Fin d → ℝ) (i : Fin d) : |clamp r hr u i| ≤ r := by
  unfold clamp
  have h := (Set.projIcc (-r) r (by linarith) (u i)).2
  exact abs_le.2 ⟨h.1, h.2⟩

theorem norm_clamp_le {r : ℝ} (hr : 0 ≤ r) (u : Fin d → ℝ) : ‖clamp r hr u‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg (x := clamp r hr u) hr).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_clamp_le hr u i

/-- The clamped series function `evalF f ∘ clamp r`. -/
noncomputable def evalFClamp (f : CoeffFamily d) (r : ℝ) (hr : 0 ≤ r) : (Fin d → ℝ) → ℝ :=
  fun u => evalF f (clamp r hr u)

theorem evalFClamp_eq (f : CoeffFamily d) {r : ℝ} (hr : 0 ≤ r) {u : Fin d → ℝ}
    (hu : ∀ i, |u i| ≤ r) : evalFClamp f r hr u = evalF f u := by
  unfold evalFClamp
  rw [clamp_eq_self hr hu]

variable (f : CoeffFamily d) {b' : ℝ} (hb' : 0 < b') (hf : AbsSummableAt f b') {r : ℝ}
  (hr : 0 < r) (hrb' : r < b')
include hb' hf hr hrb'

theorem continuous_evalFClamp : Continuous (evalFClamp f r hr.le) := by
  have hc : ContinuousOn (evalF f) (Metric.eball 0 (ENNReal.ofReal b')) :=
    (hasFPowerSeriesOnBall_evalF f hb' hf).continuousOn
  refine hc.comp_continuous (continuous_clamp r hr.le) fun u => ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hb').2 (lt_of_le_of_lt (norm_clamp_le hr.le u) hrb')

theorem hasFPowerSeriesOnBall_evalFClamp :
    HasFPowerSeriesOnBall (evalFClamp f r hr.le) (polySeriesD f) 0 (ENNReal.ofReal r) := by
  have h := (hasFPowerSeriesOnBall_evalF f hb' hf).mono (ENNReal.ofReal_pos.2 hr)
    (ENNReal.ofReal_le_ofReal hrb'.le)
  refine h.congr fun u hu => ?_
  have hnorm : ‖u‖ < r := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hu
    exact (ENNReal.ofReal_lt_ofReal_iff hr).1 hu
  rw [evalFClamp_eq f hr.le fun i => ?_]
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm u i).trans hnorm.le

/-- The clamped function is bounded. -/
theorem exists_bound_evalFClamp : ∃ C, ∀ u, |evalFClamp f r hr.le u| ≤ C := by
  have hK : IsCompact (piBox d (Icc (-r) r)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc : ContinuousOn (evalF f) (piBox d (Icc (-r) r)) :=
    (continuous_evalFClamp f hb' hf hr hrb').continuousOn.congr fun u hu => by
      unfold evalFClamp
      rw [clamp_eq_self hr.le fun i => abs_le.2 ⟨(hu i (mem_univ i)).1, (hu i (mem_univ i)).2⟩]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨C, fun u => ?_⟩
  have hmem : clamp r hr.le u ∈ piBox d (Icc (-r) r) := fun i _ =>
    abs_le.1 (abs_clamp_le hr.le u i)
  have := hC _ hmem
  rwa [Real.norm_eq_abs] at this

end Clamp

theorem jetFamily_evalFClamp {n : ℕ} (f : CoeffFamily (n + 1)) {b' : ℝ} (hb' : 0 < b')
    (hf : AbsSummableAt f b') {r : ℝ} (hr : 0 < r) (hrb' : r < b') :
    jetFamily n (evalFClamp f r hr.le) = f := by
  rw [jetFamily_eq_monoFamily (hasFPowerSeriesOnBall_evalFClamp f hb' hf hr hrb'),
    monoFamily_polySeriesD]

theorem AbsSummableAt.mono {d : ℕ} {f : CoeffFamily d} {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hf : AbsSummableAt f b') : AbsSummableAt f b :=
  Summable.of_nonneg_of_le (fun γ => by positivity)
    (fun γ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbb _) (abs_nonneg _)) hf

/-- Densities and pushforwards along a measurable embedding commute. -/
theorem withDensity_map_of_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {e : α → β} (he : MeasurableEmbedding e) (μ : Measure α) (g : β → ℝ≥0∞) :
    (μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e := by
  ext s hs
  rw [withDensity_apply _ hs, he.map_apply, withDensity_apply _ (he.measurable hs),
    Measure.restrict_map he.measurable hs, he.lintegral_map]
  rfl

/-! ### The data -/

namespace SeriesBox

open CoordModel

variable (n : ℕ) (k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (fϕ fφ : CoeffFamily (n + 1))
  (b b' : ℝ) (hb : 0 < b) (hbb' : b < b') (hϕ : AbsSummableAt fϕ b') (hφ : AbsSummableAt fφ b')

/-- The clamp radius `(b + b')/2`. -/
noncomputable def rmid : ℝ := (b + b') / 2

include hb hbb' in
omit hk hϕ hφ in
theorem rmid_pos : 0 < rmid b b' := by unfold rmid; linarith
include hbb' in
omit hk hϕ hφ in
theorem b_lt_rmid : b < rmid b b' := by unfold rmid; linarith
include hbb' in
omit hk hϕ hφ in
theorem rmid_lt : rmid b b' < b' := by unfold rmid; linarith

/-- The observable `φ = evalF fφ` (clamped). -/
noncomputable def obs : (Fin (n + 1) → ℝ) → ℝ :=
  evalFClamp fφ (rmid b b') (rmid_pos b b' hb hbb').le

/-- The prior `ϕ = max (evalF fϕ) 0` (clamped, nonnegative). -/
noncomputable def prior : (Fin (n + 1) → ℝ) → ℝ :=
  fun u => max (evalFClamp fϕ (rmid b b') (rmid_pos b b' hb hbb').le u) 0

/-- The Jacobian orders of the identity resolution. -/
def hh : Fin (n + 1) → ℕ := fun _ => 0

/-- The region `W = [0,b]^{n+1}`. -/
def region : Set (Fin (n + 1) → ℝ) := piBox (n + 1) (Icc 0 b)

/-- The normal box `(0,b]^{n+1}`. -/
def box : Set (Fin (n + 1) → ℝ) := piBox (n + 1) (Ioc 0 b)

omit hk hb hbb' hϕ hφ in
theorem mem_region {w : Fin (n + 1) → ℝ} : w ∈ region n b ↔ ∀ i, 0 ≤ w i ∧ w i ≤ b := by
  simp only [region, piBox, Set.mem_univ_pi, Set.mem_Icc]

omit hk hb hbb' hϕ hφ in
theorem mem_box {w : Fin (n + 1) → ℝ} : w ∈ box n b ↔ ∀ i, 0 < w i ∧ w i ≤ b := by
  simp only [box, piBox, Set.mem_univ_pi, Set.mem_Ioc]

omit hk hb hbb' hϕ hφ in
theorem box_subset_region : box n b ⊆ region n b := fun _ hw =>
  (mem_region n b).2 fun i => ⟨((mem_box n b).1 hw i).1.le, ((mem_box n b).1 hw i).2⟩

omit hk hb hbb' hϕ hφ in
theorem isCompact_region : IsCompact (region n b) := isCompact_univ_pi fun _ => isCompact_Icc

omit hk hb hbb' hϕ hφ in
theorem measurableSet_region : MeasurableSet (region n b) :=
  measurableSet_piBox _ _ measurableSet_Icc

omit hk hb hbb' hϕ hφ in
theorem measurableSet_box : MeasurableSet (box n b) := measurableSet_piBox _ _ measurableSet_Ioc

omit hk hb hbb' hϕ hφ in
theorem volume_region_diff_box : volume (region n b \ box n b) = 0 := by
  refine measure_mono_null (fun w hw => ?_)
    (measure_iUnion_null fun i : Fin (n + 1) => Measure.pi_hyperplane (fun _ => volume) i (0 : ℝ))
  obtain ⟨hin, hnot⟩ := hw
  rw [mem_region] at hin
  rw [mem_box] at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  change w i = 0
  by_contra hne
  exact absurd (hi (lt_of_le_of_ne (hin i).1 (Ne.symm hne))) (not_lt.2 (hin i).2)

include hbb' in
omit hk hb hϕ hφ in
theorem abs_le_rmid_of_mem_region {w : Fin (n + 1) → ℝ} (hw : w ∈ region n b) (i : Fin (n + 1)) :
    |w i| ≤ rmid b b' := by
  have h := (mem_region n b).1 hw i
  rw [abs_le]
  constructor <;> linarith [b_lt_rmid b b' hbb']

omit hk hϕ in
theorem obs_eq_of_mem_region {w : Fin (n + 1) → ℝ} (hw : w ∈ region n b) :
    obs n fφ b b' hb hbb' w = evalF fφ w :=
  evalFClamp_eq fφ _ (abs_le_rmid_of_mem_region n b b' hbb' hw)

variable (hϕ0 : ∀ w ∈ region n b, 0 ≤ evalF fϕ w)

include hϕ0 in
omit hk hφ hϕ in
theorem prior_eq_of_mem_region {w : Fin (n + 1) → ℝ} (hw : w ∈ region n b) :
    prior n fϕ b b' hb hbb' w = evalF fϕ w := by
  unfold prior
  rw [evalFClamp_eq fϕ _ (abs_le_rmid_of_mem_region n b b' hbb' hw), max_eq_left (hϕ0 w hw)]

omit hk hϕ hφ hϕ0 in
theorem prior_nonneg (w : Fin (n + 1) → ℝ) : 0 ≤ prior n fϕ b b' hb hbb' w := le_max_right _ _

include hφ in
omit hk hϕ hϕ0 in
theorem continuous_obs : Continuous (obs n fφ b b' hb hbb') :=
  continuous_evalFClamp fφ (by linarith) hφ (rmid_pos b b' hb hbb') (rmid_lt b b' hbb')

include hϕ in
omit hk hφ hϕ0 in
theorem continuous_prior : Continuous (prior n fϕ b b' hb hbb') :=
  (continuous_evalFClamp fϕ (by linarith) hϕ (rmid_pos b b' hb hbb')
    (rmid_lt b b' hbb')).max continuous_const

include hφ in
omit hk hϕ hϕ0 in
theorem hasFPowerSeriesOnBall_obs :
    HasFPowerSeriesOnBall (obs n fφ b b' hb hbb') (polySeriesD fφ) 0
      (ENNReal.ofReal (rmid b b')) :=
  hasFPowerSeriesOnBall_evalFClamp fφ (by linarith) hφ (rmid_pos b b' hb hbb')
    (rmid_lt b b' hbb')

include hφ in
omit hk hϕ hϕ0 in
theorem jetFamily_obs : jetFamily n (obs n fφ b b' hb hbb') = fφ :=
  jetFamily_evalFClamp fφ (by linarith) hφ (rmid_pos b b' hb hbb') (rmid_lt b b' hbb')

include hϕ in
omit hk hφ hϕ0 in
theorem exists_bound_prior : ∃ C, ∀ w, prior n fϕ b b' hb hbb' w ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_evalFClamp fϕ (by linarith) hϕ (rmid_pos b b' hb hbb')
    (rmid_lt b b' hbb')
  refine ⟨max C 0, fun w => ?_⟩
  unfold prior
  exact max_le_max (le_abs_self _ |>.trans (hC w)) le_rfl

/-! ### The localisation datum -/

/-- The geometry: `ℝ^{n+1}` with the coordinate hyperplanes, orders `k`, `h = 0`. -/
noncomputable abbrev geometry : ResolvedGeometry (n + 1) (Fin (n + 1) → ℝ) :=
  CoordModel.geometry (n + 1) k (hh n) hk

/-- The normal data. -/
noncomputable abbrev normalData : ResolvedNormalData (geometry n k hk) (Amb (n + 1)) :=
  CoordModel.normalData (n + 1) k (hh n) hk

/-- The phase `∏ u_i^{2k_i}`. -/
abbrev phase : (Fin (n + 1) → ℝ) → ℝ := CoordModel.phase (n + 1) k

include hϕ hφ in
omit hk in
/-- The localisation datum: prior-weighted Lebesgue measure on the box, phase `∏ u^{2k}`,
observable `φ`. -/
noncomputable def locData : LocalisationData (Fin (n + 1) → ℝ) where
  μ := (volume.restrict (region n b)).withDensity fun w =>
    ENNReal.ofReal (prior n fϕ b b' hb hbb' w)
  phase := phase n k
  obs := obs n fφ b b' hb hbb'
  phase_measurable := measurable_phase (n + 1) k
  phase_nonneg := Eventually.of_forall (phase_nonneg (n + 1) k)
  obs_integrable := by
    have hm : Measurable fun w => ENNReal.ofReal (prior n fϕ b b' hb hbb' w) :=
      (continuous_prior n fϕ b b' hb hbb' hϕ).measurable.ennreal_ofReal
    refine (integrable_withDensity_iff_integrable_smul' hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2 ?_
    have heq : (fun w => (ENNReal.ofReal (prior n fϕ b b' hb hbb' w)).toReal •
        obs n fφ b b' hb hbb' w) =
        fun w => prior n fϕ b b' hb hbb' w * obs n fφ b b' hb hbb' w := by
      funext w
      rw [ENNReal.toReal_ofReal (prior_nonneg n fϕ b b' hb hbb' w), smul_eq_mul]
    rw [heq]
    exact ((continuous_prior n fϕ b b' hb hbb' hϕ).mul
      (continuous_obs n fφ b b' hb hbb' hφ)).continuousOn.integrableOn_compact
      (isCompact_region n b)
  δ := 1
  δ_pos := one_pos

/-- The base of the chart: the deepest stratum point. -/
abbrev Base := ↥(Set.univ : Set ((geometry n k hk).Stratum Finset.univ))

/-- The base point. -/
def basePt : Base n k hk := ⟨origin (n + 1) k (hh n) hk, trivial⟩

omit hk hb hbb' hϕ hφ in
theorem absSummableAt_zero' (b : ℝ) : AbsSummableAt (0 : CoeffFamily (n + 1)) b :=
  summable_of_ne_finset_zero (s := ∅) fun _ _ => by simp

include hϕ hφ in
omit hk in
/-- The amplitude datum `fϕ ⋆ fφ`. -/
noncomputable def datum : DataSpace (n + 1) :=
  ofFamilies b hb 0 (CoeffFamily.conv fϕ fφ) (absSummableAt_zero' n b)
    (AbsSummableAt.conv hb.le (AbsSummableAt.mono hb.le hbb'.le hϕ)
      (AbsSummableAt.mono hb.le hbb'.le hφ))

include hϕ hφ hϕ0 in
/-- **The single core at the deepest stratum**: Dirac base, normal box `(0,b]^{n+1}`, `Φ(s,u) = u`,
density `ϕ`, `h = 0`, exponents `k`, amplitude datum `fϕ ⋆ fφ`. -/
noncomputable def core :
    CorePresentation (locData n k fϕ fφ b b' hb hbb' hϕ hφ)
      ((locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)) (Base n k hk) n 1 where
  ν := Measure.dirac (basePt n k hk)
  isFiniteMeasure_ν := inferInstance
  h := hh n
  k := k
  k_pos := hk
  b := b
  b_pos := hb
  Φ := Prod.snd
  measurable_Φ := measurable_snd
  c := fun p => prior n fϕ b b' hb hbb' p.2
  measurable_c := (continuous_prior n fϕ b b' hb hbb' hϕ).measurable.comp measurable_snd
  nonneg_c := Eventually.of_forall fun p => prior_nonneg n fϕ b b' hb hbb' p.2
  x := ContinuousMap.const _ (datum n fϕ fφ b b' hb hbb' hϕ hφ)
  transport := by
    have hd : (fun p : Base n k hk × (Fin (n + 1) → ℝ) =>
        ((chartDensity (hh n) (fun p => prior n fϕ b b' hb hbb' p.2) p).toNNReal : ℝ≥0∞)) =
        fun p => ENNReal.ofReal (prior n fϕ b b' hb hbb' p.2) := by
      funext p
      simp [chartDensity, hh, ENNReal.ofReal]
    rw [hd]
    unfold chartMeasure
    rw [Measure.dirac_prod, withDensity_map_of_embedding (measurableEmbedding_prodMk_left
      (basePt n k hk)), Measure.map_map measurable_snd measurable_prodMk_left]
    have hid : (Prod.snd ∘ Prod.mk (basePt n k hk) : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) = id :=
      rfl
    rw [hid, Measure.map_id]
    change _ = ((volume.restrict (region n b)).withDensity fun w =>
      ENNReal.ofReal (prior n fϕ b b' hb hbb' w)).restrict (box n b)
    rw [restrict_withDensity (measurableSet_box n b),
      Measure.restrict_restrict (measurableSet_box n b),
      Set.inter_eq_left.2 (box_subset_region n b)]
    rfl
  phase_normal := Eventually.of_forall fun p => (one_mul _).symm
  amplitude_eq := by
    filter_upwards [ae_snd_mem_box (Measure.dirac (basePt n k hk)) n b] with p hp
    rw [ContinuousMap.const_apply]
    change evalF (toEta b (datum n fϕ fφ b b' hb hbb' hϕ hφ)) p.2 =
      prior n fϕ b b' hb hbb' p.2 * obs n fφ b b' hb hbb' p.2
    unfold datum
    rw [toEta_ofFamilies]
    have hbox := (mem_box n b).1 hp
    have hreg : p.2 ∈ region n b := box_subset_region n b hp
    rw [evalF_conv_of_absSummableAt hb (AbsSummableAt.mono hb.le hbb'.le hϕ)
      (AbsSummableAt.mono hb.le hbb'.le hφ) fun i => ⟨(hbox i).1.le, (hbox i).2⟩,
      prior_eq_of_mem_region n fϕ b b' hb hbb' hϕ0 hreg,
      obs_eq_of_mem_region n fφ b b' hb hbb' hreg]
  fluct_zero := fun _ => by
    rw [ContinuousMap.const_apply]
    funext γ
    have h := congrFun (toXi_ofFamilies b hb 0 (CoeffFamily.conv fϕ fφ) (absSummableAt_zero' n b)
      (AbsSummableAt.conv hb.le (AbsSummableAt.mono hb.le hbb'.le hϕ)
        (AbsSummableAt.mono hb.le hbb'.le hφ))) γ
    simp only [toXi, Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff', hb.ne', false_and,
      or_false] at h
    exact h

include hϕ hφ in
/-- The tail `μ|_{(0,b]^{n+1}ᶜ}` is null: the region differs from the box by the coordinate
hyperplanes. -/
theorem restrict_box_compl_eq_zero :
    (locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)ᶜ = 0 := by
  rw [Measure.restrict_eq_zero]
  change ((volume.restrict (region n b)).withDensity fun w =>
    ENNReal.ofReal (prior n fϕ b b' hb hbb' w)) (box n b)ᶜ = 0
  have h0 : volume.restrict ((box n b)ᶜ ∩ region n b) = 0 :=
    Measure.restrict_eq_zero.2 (measure_mono_null
      (fun w (hw : w ∈ (box n b)ᶜ ∩ region n b) => (⟨hw.2, hw.1⟩ : w ∈ region n b \ box n b))
      (volume_region_diff_box n b))
  rw [withDensity_apply _ (measurableSet_box n b).compl,
    Measure.restrict_restrict (measurableSet_box n b).compl, h0, lintegral_zero_measure]

include hϕ hφ hϕ0 in
/-- **The core decomposition**: one core, null tail. -/
noncomputable def coreDecomposition :
    AnalyticCoreDecomposition (locData n k fϕ fφ b b' hb hbb' hϕ hφ) 1 (fun _ => Base n k hk)
      (fun _ => n) 1 where
  core := fun _ => (locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)
  tail := (locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)ᶜ
  measure_eq := by
    rw [Fin.sum_univ_one]
    exact (Measure.restrict_add_restrict_compl (μ := (locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ)
      (measurableSet_box n b)).symm
  δ₀ := 1
  δ₀_pos := one_pos
  gap := by
    rw [restrict_box_compl_eq_zero n k fϕ fφ b b' hb hbb' hϕ hφ, ae_zero]
    exact Filter.eventually_bot
  chart := fun _ => core n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0

include hϕ hφ hϕ0 in
/-- The normal-moment presentation from the observable's series. -/
noncomputable def presentation :
    CoreNormalMomentPresentation (core n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0) where
  p := fun _ => polySeriesD fφ
  R := fun _ => ENNReal.ofReal (rmid b b')
  analytic := fun _ => hasFPowerSeriesOnBall_obs n fφ b b' hb hbb' hφ
  radius := fun _ => (ENNReal.ofReal_lt_ofReal_iff (rmid_pos b b' hb hbb')).2 (b_lt_rmid b b' hbb')
  cBound := (exists_bound_prior n fϕ b b' hb hbb' hϕ).choose
  c_le := fun q => (exists_bound_prior n fϕ b b' hb hbb' hϕ).choose_spec q.2

/-! ### The certificates -/

include hϕ hφ hϕ0 in
/-- ★★ **The resolved certificate from series data on the coordinate box.** -/
noncomputable def certificate :
    ResolvedCertificate (geometry n k hk) (normalData n k hk) (region n b) (phase n k)
      (prior n fϕ b b' hb hbb') (obs n fφ b b' hb hbb') where
  L := locData n k fϕ fφ b b' hb hbb' hϕ hφ
  obs_eq := rfl
  phase_eq := rfl
  transport := by
    change Measure.map id _ = _
    rw [Measure.map_id]
    rfl
  M := 1
  n := fun _ => n
  strat := fun _ => Finset.univ
  base := fun _ => Set.univ
  isCompact_base := fun _ => isCompact_univ
  β := 1
  β_pos := one_pos
  cores := coreDecomposition n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0
  T := fun _ => presentation n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0
  frame := fun _ _ => frameUniv (n + 1)
  Φ_eq := fun _ s u => by
    change u = (normalData n k hk).Φ Finset.univ s.1 (frameUniv (n + 1) u)
    rw [Stratum_univ_eq (n + 1) k (hh n) hk s.1, Φ_frameUniv_origin]

include hϕ hφ hϕ0 in
/-- ★★ **The coefficient certificate from series data**: density family `fϕ`, Taylor family
`fφ`. -/
noncomputable def coeffCertificate :
    (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).CoefficientCertificate where
  cc := fun _ _ => fϕ
  cc_abs := fun _ _ => AbsSummableAt.mono hb.le hbb'.le hϕ
  jet_abs := fun _ _ => by
    change AbsSummableAt (jetFamily n (obs n fφ b b' hb hbb')) b
    rw [jetFamily_obs n fφ b b' hb hbb' hφ]
    exact AbsSummableAt.mono hb.le hbb'.le hφ
  datum_eq := fun _ _ => by
    change toEta b (datum n fϕ fφ b b' hb hbb' hϕ hφ) =
      CoeffFamily.conv fϕ (jetFamily n (obs n fφ b b' hb hbb'))
    unfold datum
    rw [toEta_ofFamilies, jetFamily_obs n fφ b b' hb hbb' hφ]

include hϕ hφ hϕ0 in
theorem commonQ_certificate :
    commonQ (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).cores.k = latticeQ k := by
  change ∏ _ : Fin 1, latticeQ k = latticeQ k
  simp

include hϕ hφ hϕ0 in
theorem commonD_certificate :
    commonD (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).n = n := by
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => n) = n
  simp

include hϕ hφ hϕ0 in
/-- ★★★ **The coordinate-free expansion from series data on the coordinate box**: for every
`b'`-weighted ℓ¹ prior family (nonnegative on the box) and observable family, with `b < b'`,
`∫_{[0,b]^{n+1}} φ ϕ e^{−N ∏ u^{2k}} du` has the coordinate-free expansion with spectrum
`{(α, j) : α ∈ (2∏k_i)⁻¹ℕ, α ≤ A, j ≤ n}`. -/
theorem hasCoordFreeExpansion_box :
    (normalData n k hk).HasCoordFreeExpansion
      (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).stratumMeasure
      (coeffCertificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).field
      (spectrumLe (latticeQ k) n) (region n b) (phase n k) (prior n fϕ b b' hb hbb')
      (obs n fφ b b' hb hbb') := by
  have h := (coeffCertificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).hasCoordFreeExpansion_le
    (measurable_phase (n + 1) k) (continuous_prior n fϕ b b' hb hbb' hϕ).measurable
    (prior_nonneg n fϕ b b' hb hbb') (continuous_obs n fφ b b' hb hbb' hφ).measurable
  rwa [commonQ_certificate, commonD_certificate] at h

include hϕ0 in
omit hk hϕ hφ in
/-- On the box the integrand is the genuine series `evalF fφ · evalF fϕ`. -/
theorem globalLaplace_region_eq (N : ℝ) :
    globalLaplace (region n b) (phase n k)
      (fun w => obs n fφ b b' hb hbb' w * prior n fϕ b b' hb hbb' w) N =
      ∫ w in region n b, evalF fφ w * evalF fϕ w * Real.exp (-N * ∏ i, w i ^ (2 * k i)) := by
  unfold globalLaplace
  refine setIntegral_congr_fun (measurableSet_region n b) fun w hw => ?_
  simp only
  rw [obs_eq_of_mem_region n fφ b b' hb hbb' hw, prior_eq_of_mem_region n fϕ b b' hb hbb' hϕ0 hw]
  rfl

end SeriesBox

end Grammar
