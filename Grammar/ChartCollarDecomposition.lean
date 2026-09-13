/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartCollar
import Grammar.WeightedNormalisedBoxCore

/-!
# The collar decomposition of a chart with a tangential unit and Jacobian weight (unit E, part 1)

The measure-theoretic assembly of the chart collar (CCCLXXI) on the chart model
(CCCXLIII): for every nonempty `I ⊆ A` (indexed by `Finset ↥A`) the base `B_I` is lifted into
the stratum `S_I` of the chart geometry (`baseStratum`, compact), the weighted core data
(`WData` of E2) is assembled with the unit-corrected widths and the normalisation identity of
CCCLXXI, the cores are the weighted normalised box cores `wcore` for the weighted prior
`∏|y_i|^{h_i} · ϕ` and the phase `u · ∏_{i∈A} y_i^{2k_i}`, the thresholds are null, the core images
are a.e.-disjoint and cover `{K < δ}` up to a null set, so `μ = Σ_I μ|_{C_I} + tail` with `K ≥ δ`
on the tail (`collar`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace ChartCollar

open NormalisedBox WaterFilling CoordModel CoeffFamily

variable {d : ℕ} (A : Finset (Fin d)) (k h : Fin d → ℕ) (hkA : ∀ i ∈ A, 0 < k i)
  (hk0 : ∀ i, i ∉ A → k i = 0) (u : (Fin d → ℝ) → ℝ) (a δ : ℝ)

/-! ### The index set and the ambient index sets -/

/-- The nonempty subsets of the active set. -/
abbrev Idx (A : Finset (Fin d)) := {I : Finset ↥A // I.Nonempty}

/-- The ambient index set of a core index. -/
noncomputable def amb (I : Idx A) : Finset (Fin d) := ChartModel.amb d A I.1

theorem amb_subset (I : Idx A) : amb A I ⊆ A := fun _ hj => ((ChartModel.mem_amb d A).1 hj).1

theorem amb_nonempty (I : Idx A) : (amb A I).Nonempty := by
  obtain ⟨i, hi⟩ := I.2
  exact ⟨i.1, (ChartModel.mem_amb d A).2 ⟨i.2, hi⟩⟩

theorem card_amb (I : Idx A) : (amb A I).card = I.1.card := ChartModel.card_amb d A I.1

theorem mem_amb_iff (I : Idx A) (i : ↥A) : i.1 ∈ amb A I ↔ i ∈ I.1 := by
  rw [amb, ChartModel.mem_amb]
  constructor
  · rintro ⟨_, hi⟩
    exact hi
  · intro hi
    exact ⟨i.2, hi⟩

include hk0 in
/-- The coordinate phase with orders vanishing off `A` is the active monomial. -/
theorem coordPhase_eq_monoPhase (y : Fin d → ℝ) :
    CoordModel.phase d k y = ChartModel.monoPhase d A k y := by
  unfold CoordModel.phase ChartModel.monoPhase
  refine (Finset.prod_subset (Finset.subset_univ A) fun j _ hj => ?_).symm
  rw [hk0 j hj, mul_zero, pow_zero]

/-! ### The bases inside the strata -/

/-- The base of the stratum `I`: the stratum points whose tangential coordinates lie in `B_I`. -/
noncomputable def baseStratum (I : Idx A) : Set ((ChartModel.geometry d A k h hkA).Stratum I.1) :=
  {s | tan (amb A I) s.1 ∈ baseSet A k u (amb A I) a δ}

/-- The base type. -/
abbrev KI (I : Idx A) := ↥(baseStratum A k h hkA u a δ I)

/-- The tangential coordinates of a base point. -/
noncomputable def eI (I : Idx A) : KI A k h hkA u a δ I → (Tan (amb A I) → ℝ) :=
  fun s => tan (amb A I) s.1.1

theorem continuous_eI (I : Idx A) : Continuous (eI A k h hkA u a δ I) :=
  (continuous_pi fun j => (continuous_apply j.1)).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- On the stratum `I` the coordinates in `amb I` vanish. -/
theorem stratum_coord_zero {I : Idx A} (s : (ChartModel.geometry d A k h hkA).Stratum I.1)
    {j : Fin d} (hj : j ∈ amb A I) : (s : Fin d → ℝ) j = 0 := by
  have hjA : j ∈ A := amb_subset A I hj
  exact ((ChartModel.mem_stratumSet_iff d A k h hkA I.1 s.1).1 s.2 ⟨j, hjA⟩).2
    ((mem_amb_iff A I ⟨j, hjA⟩).1 hj)

theorem eI_injective (I : Idx A) : Function.Injective (eI A k h hkA u a δ I) := by
  intro s s' hss'
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ amb A I
  · rw [stratum_coord_zero A k h hkA s.1 hj, stratum_coord_zero A k h hkA s'.1 hj]
  · exact congrFun hss' ⟨j, hj⟩

variable (hδ : 0 < δ)

include hkA hδ in
theorem liftPoint_mem_stratum (I : Idx A) {t : Tan (amb A I) → ℝ}
    (ht : t ∈ baseSet A k u (amb A I) a δ) :
    liftPoint (amb A I) t ∈ (ChartModel.geometry d A k h hkA).stratumSet I.1 := by
  rw [ChartModel.mem_stratumSet_iff]
  intro i
  rw [liftPoint_apply, ← mem_amb_iff A I i]
  by_cases hi : i.1 ∈ amb A I
  · simp [hi]
  · rw [dif_neg hi]
    exact ⟨fun h0 => absurd h0 (pos_of_mem_baseSet A k u (amb A I) a δ hkA
      (amb_nonempty A I) hδ ht ⟨i.1, hi⟩ i.2).ne', fun h0 => absurd h0 hi⟩

include hδ in
/-- The lift of the base `B_I` into the stratum. -/
noncomputable def liftBase (I : Idx A) (t : ↥(baseSet A k u (amb A I) a δ)) :
    KI A k h hkA u a δ I :=
  ⟨⟨liftPoint (amb A I) t.1, liftPoint_mem_stratum A k h hkA u a δ hδ I t.2⟩, by
    change tan (amb A I) (liftPoint (amb A I) t.1) ∈ baseSet A k u (amb A I) a δ
    rw [tan_liftPoint]
    exact t.2⟩

include hδ in
theorem continuous_liftBase (I : Idx A) : Continuous (liftBase A k h hkA u a δ hδ I) :=
  (((continuous_liftPoint (amb A I)).comp continuous_subtype_val).subtype_mk _).subtype_mk _

include hδ in
theorem eI_liftBase (I : Idx A) (t : ↥(baseSet A k u (amb A I) a δ)) :
    eI A k h hkA u a δ I (liftBase A k h hkA u a δ hδ I t) = t.1 :=
  tan_liftPoint (amb A I) t.1

include hδ in
theorem range_eI (I : Idx A) : range (eI A k h hkA u a δ I) = baseSet A k u (amb A I) a δ := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact s.2
  · intro ht
    exact ⟨liftBase A k h hkA u a δ hδ I ⟨t, ht⟩, eI_liftBase A k h hkA u a δ hδ I ⟨t, ht⟩⟩

include hδ in
theorem surjective_liftBase (I : Idx A) : Function.Surjective (liftBase A k h hkA u a δ hδ I) := by
  intro s
  refine ⟨⟨eI A k h hkA u a δ I s, s.2⟩, eI_injective A k h hkA u a δ I ?_⟩
  rw [eI_liftBase]

variable (hu_cont : Continuous u)

include hδ hu_cont in
/-- The bases are compact. -/
theorem compactSpace_KI (I : Idx A) : CompactSpace (KI A k h hkA u a δ I) := by
  have : CompactSpace ↥(baseSet A k u (amb A I) a δ) :=
    isCompact_iff_compactSpace.1 (isCompact_baseSet A k u (amb A I) a δ hu_cont)
  refine ⟨?_⟩
  rw [← (surjective_liftBase A k h hkA u a δ hδ I).range_eq]
  exact isCompact_range (continuous_liftBase A k h hkA u a δ hδ I)

include hδ hu_cont in
theorem isCompact_baseStratum (I : Idx A) : IsCompact (baseStratum A k h hkA u a δ I) :=
  isCompact_iff_compactSpace.2 (compactSpace_KI A k h hkA u a δ hδ hu_cont I)

/-! ### Box coordinates -/

/-- The normal dimension minus one. -/
abbrev nI (I : Idx A) : ℕ := I.1.card - 1

/-- Box coordinates ↔ normal coordinates of the stratum `I`. -/
noncomputable def σI (I : Idx A) : Fin (nI A I + 1) ≃ Nrm (amb A I) :=
  (finCongr (by rw [Nat.sub_add_cancel I.2.card_pos, card_amb])).trans
    (Finset.equivFin (amb A I)).symm

/-! ### The weighted core data -/

variable (ϕ φ : (Fin d → ℝ) → ℝ)

/-- The local normal-series input at the stratum `I`: uniform series families over the base in the
normalised normal variables, at radius `2b_I`, agreeing with the prior on the normal box and with
the observable on the ball. -/
structure FaceSeries (I : Idx A) where
  Fϕ : UniformSeriesFamily (KI A k h hkA u a δ I) (nI A I + 1) (2 * side k (amb A I) δ)
  Fφ : UniformSeriesFamily (KI A k h hkA u a δ I) (nI A I + 1) (2 * side k (amb A I) δ)
  hϕ_eq : ∀ s, ∀ v ∈ NormalisedBox.box (ι := Fin (nI A I + 1)) (side k (amb A I) δ),
    ϕ (Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v)) =
      evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (nI A I + 1) → ℝ), ‖v‖ < 2 * side k (amb A I) δ →
    φ (Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v)) =
      evalF (Fφ.f s) v

variable (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 < a)
  (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))

include hk0 hδ hu_cont hc hu_lb ha hδa in
/-- The weighted core data of the stratum `I` from its face series: the unit-corrected widths,
`β = 1`, side `b_I`. -/
noncomputable def toWData {I : Idx A} (F : FaceSeries A k h hkA u a δ ϕ φ I) :
    WData k (amb A I) (nI A I) (KI A k h hkA u a δ I) (piBox d (Icc 0 a)) ϕ φ where
  σ := σI A I
  e := eI A k h hkA u a δ I
  he := continuous_eI A k h hkA u a δ I
  he_inj := eI_injective A k h hkA u a δ I
  lamT := lamT k u (amb A I) δ
  hlamT := measurable_lamT k u (amb A I) δ hu_cont
  hlam_cont := by
    rw [range_eI A k h hkA u a δ hδ I]
    exact continuousOn_lamT A k u (amb A I) a δ hu_cont hkA hk0 (amb_nonempty A I) hδ hc hu_lb
      ha.le
  hpos := fun t ht j => lamT_pos_of_mem_baseSet A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) hδ
    hc hu_lb ha.le ((range_eI A k h hkA u a δ hδ I) ▸ ht) j
  unit := uT u (amb A I)
  β := 1
  hnorm := fun t ht => unit_mul_prod_lamT A k u (amb A I) a δ hkA hk0 (amb_nonempty A I)
    (amb_subset A I) hδ hc hu_lb ha.le ((range_eI A k h hkA u a δ hδ I) ▸ ht)
  b := side k (amb A I) δ
  b' := 2 * side k (amb A I) δ
  hb := side_pos k (amb A I) δ hδ
  hbb' := by linarith [side_pos k (amb A I) δ hδ]
  hW := image_subset_box A k u (amb A I) a δ (eI A k h hkA u a δ I)
    (range_eI A k h hkA u a δ hδ I) hδ hkA hk0 (amb_nonempty A I) (amb_subset A I) hc hu_lb ha hδa
  Fϕ := F.Fϕ
  Fφ := F.Fφ
  hϕ_eq := F.hϕ_eq
  hφ_eq := F.hφ_eq

/-! ### The localisation datum -/

variable (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
  (hφint : Integrable φ ((volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt h w * ϕ w)))

include hu_cont hc hu_lb hφint in
/-- The localisation datum: the weighted prior measure on the box, the chart phase with the unit,
the observable. -/
noncomputable def locData : LocalisationData (Fin d → ℝ) where
  μ := (volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt h w * ϕ w)
  phase := ChartModel.phase d A k u
  obs := φ
  phase_measurable := hu_cont.measurable.mul (ChartModel.measurable_monoPhase d A k)
  phase_nonneg := by
    have h1 : ∀ᵐ y ∂((volume.restrict (piBox d (Icc 0 a))).withDensity
        fun w => ENNReal.ofReal (wgt h w * ϕ w)), y ∈ piBox d (Icc 0 a) :=
      mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
        (mem_ae_iff.1 (ae_restrict_mem (measurableSet_W a))))
    exact h1.mono fun y hy => mul_nonneg (hc.le.trans (hu_lb y hy))
      (ChartModel.monoPhase_nonneg d A k y)
  obs_integrable := hφint
  δ := 1
  δ_pos := one_pos

include hk0 hu_cont hc hu_lb hφint hu_tan in
theorem locData_phase (I : Idx A) (y : Fin d → ℝ) :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).phase y =
      uT u (amb A I) (tan (amb A I) y) * CoordModel.phase d k y := by
  change ChartModel.phase d A k u y = _
  rw [uT_tan A u (amb A I) (amb_subset A I) hu_tan, coordPhase_eq_monoPhase A k hk0]
  rfl

include hkA in
theorem hkI (I : Idx A) : ∀ j : Nrm (amb A I), 0 < k j.1 := fun j => hkA j.1 (amb_subset A I j.2)

variable (F : ∀ I : Idx A, FaceSeries A k h hkA u a δ ϕ φ I)

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
/-- The weighted core of the stratum `I`. -/
noncomputable def stratumCore (I : Idx A) :
    CorePresentation (locData A k h u a hu_cont ϕ φ hc hu_lb hφint)
      ((locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ.restrict
        (image (amb A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (side k (amb A I) δ)))
      (KI A k h hkA u a δ I) (nI A I) 1 := by
  haveI := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact NormalisedBox.wcore (hkI A k hkA I) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint)
    (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa (F I)) (h := h) rfl
    (locData_phase A k h hk0 u a hu_cont ϕ φ hu_tan hc hu_lb hφint I) rfl

/-! ### The core images, the thresholds and the tail -/

/-- The core image of the stratum `I`. -/
noncomputable def imageSet (I : Idx A) : Set (Fin d → ℝ) :=
  image (amb A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (side k (amb A I) δ)

/-- The threshold set of the normal coordinate `i` of the stratum `I`. -/
noncomputable def thresholdSet (I : Idx A) (i : Nrm (amb A I)) : Set (Fin d → ℝ) :=
  {w | (split (amb A I) w).1 i = ell k u (amb A I) δ (split (amb A I) w).2 i}

include hu_cont in
theorem measurableSet_thresholdSet (I : Idx A) (i : Nrm (amb A I)) :
    MeasurableSet (thresholdSet A k u δ I i) :=
  measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_fst.comp
    (split (amb A I)).measurable))
    ((measurable_ell k u (amb A I) δ hu_cont i).comp (measurable_snd.comp
      (split (amb A I)).measurable))

include hδ hu_cont in
theorem measurableEmbedding_e (I : Idx A) : MeasurableEmbedding (eI A k h hkA u a δ I) := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact NormalisedBox.measurableEmbedding_e (amb A I) _ (continuous_eI A k h hkA u a δ I)
    (eI_injective A k h hkA u a δ I)

include hδ hu_cont in
theorem measurableSet_imageSet (I : Idx A) : MeasurableSet (imageSet A k h hkA u a δ I) :=
  measurableSet_image (amb A I) (side k (amb A I) δ)
    (measurableEmbedding_e A k h hkA u a δ hδ hu_cont I) (measurable_lamT k u (amb A I) δ hu_cont)

include hδ in
theorem mem_imageSet_iff (I : Idx A) (w : Fin d → ℝ) :
    w ∈ imageSet A k h hkA u a δ I ↔ tan (amb A I) w ∈ baseSet A k u (amb A I) a δ ∧
      ∀ i : Nrm (amb A I), 0 < w i.1 ∧ w i.1 ≤ ell k u (amb A I) δ (tan (amb A I) w) i :=
  mem_image_iff A k u (amb A I) a δ _ (range_eI A k h hkA u a δ hδ I) hδ w

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F in
/-- The thresholds are `μ`-null. -/
theorem measure_image_inter_threshold (I : Idx A) (i : Nrm (amb A I)) :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ
      (imageSet A k h hkA u a δ I ∩ thresholdSet A k u δ I i) = 0 := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  set C := stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F I
  have htr := C.transport
  unfold imageSet
  rw [inter_comm, ← Measure.restrict_apply (measurableSet_thresholdSet A k u δ hu_cont I i),
    ← htr, Measure.map_apply C.measurable_Φ (measurableSet_thresholdSet A k u δ hu_cont I i)]
  refine (withDensity_absolutelyContinuous _ _) (measure_mono_null
    (t := {p | p.2 ((σI A I).symm i) = side k (amb A I) δ}) ?_ ?_)
  · rintro ⟨s, v⟩ hp
    change (split (amb A I) (Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ)
      (s, v))).1 i = ell k u (amb A I) δ (split (amb A I) (Φ (amb A I) (σI A I)
        (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v))).2 i at hp
    rw [split_Φ] at hp
    change lamT k u (amb A I) δ (eI A k h hkA u a δ I s) i * v ((σI A I).symm i) =
      ell k u (amb A I) δ (eI A k h hkA u a δ I s) i at hp
    rw [← lamT_mul_side k u (amb A I) δ hδ] at hp
    have hl : 0 < lamT k u (amb A I) δ (eI A k h hkA u a δ I s) i :=
      lamT_pos_of_mem_baseSet A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) hδ hc hu_lb ha.le
        s.2 i
    exact mul_left_cancel₀ hl.ne' hp
  · change chartMeasure (baseMeasure (amb A I) (eI A k h hkA u a δ I)) (nI A I)
      (side k (amb A I) δ) _ = 0
    rw [chartMeasure, show {p : KI A k h hkA u a δ I × (Fin (nI A I + 1) → ℝ) |
        p.2 ((σI A I).symm i) = side k (amb A I) δ} =
        univ ×ˢ {v | v ((σI A I).symm i) = side k (amb A I) δ} from by
          ext p
          simp [mem_prod], Measure.prod_prod]
    have h0 : (volume : Measure (Fin (nI A I + 1) → ℝ))
        {v | v ((σI A I).symm i) = side k (amb A I) δ} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hres : (volume.restrict (piBox (nI A I + 1) (Ioc 0 (side k (amb A I) δ))))
        {v | v ((σI A I).symm i) = side k (amb A I) δ} = 0 :=
      le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans h0.le) zero_le
    rw [hres, mul_zero]

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F in
/-- ★ **The core images are `μ`-a.e. disjoint.** -/
theorem aeDisjoint_image {I J : Idx A} (hIJ : I ≠ J) :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ
      (imageSet A k h hkA u a δ I ∩ imageSet A k h hkA u a δ J) = 0 := by
  refine measure_mono_null (t := (⋃ i, imageSet A k h hkA u a δ I ∩ thresholdSet A k u δ I i) ∪
    ⋃ i, imageSet A k h hkA u a δ J ∩ thresholdSet A k u δ J i) ?_
    (measure_union_null (measure_iUnion_null fun i =>
      measure_image_inter_threshold A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm
        hϕ0 hφint F I i)
      (measure_iUnion_null fun i =>
      measure_image_inter_threshold A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm
        hϕ0 hφint F J i))
  rintro w ⟨hwI, hwJ⟩
  have hIJ' : amb A I ≠ amb A J := fun heq => hIJ (Subtype.ext (by
    ext i
    rw [← mem_amb_iff A I i, ← mem_amb_iff A J i, heq]))
  rcases disjoint_or_threshold A k u a δ hkA hk0 hδ hu_tan hc hu_lb ha.le (amb_nonempty A I)
    (amb_subset A I) (amb_nonempty A J) (amb_subset A J) hIJ'
    ((mem_imageSet_iff A k h hkA u a δ hδ I w).1 hwI)
    ((mem_imageSet_iff A k h hkA u a δ hδ J w).1 hwJ) with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl (mem_iUnion.2 ⟨i, hwI, hi⟩)
  · exact Or.inr (mem_iUnion.2 ⟨i, hwJ, hi⟩)

/-- The number of cores. -/
abbrev numCores (A : Finset (Fin d)) : ℕ := Fintype.card (Idx A)

/-- The indexing of the cores. -/
noncomputable def coreIdx : Fin (numCores A) ≃ Idx A := (Fintype.equivFin (Idx A)).symm

/-- The union of the core images. -/
noncomputable def collarUnion : Set (Fin d → ℝ) :=
  ⋃ i : Fin (numCores A), imageSet A k h hkA u a δ (coreIdx A i)

include hδ hu_cont in
theorem measurableSet_collarUnion : MeasurableSet (collarUnion A k h hkA u a δ) :=
  MeasurableSet.iUnion fun i => measurableSet_imageSet A k h hkA u a δ hδ hu_cont (coreIdx A i)

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F in
theorem restrict_collarUnion :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ.restrict (collarUnion A k h hkA u a δ) =
      ∑ i : Fin (numCores A), (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ.restrict
        (imageSet A k h hkA u a δ (coreIdx A i)) := by
  rw [collarUnion, Measure.restrict_iUnion_ae, Measure.sum_fintype]
  · intro i j hij
    exact aeDisjoint_image A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint
      F (fun heq => hij ((coreIdx A).injective heq))
  · exact fun i =>
      (measurableSet_imageSet A k h hkA u a δ hδ hu_cont (coreIdx A i)).nullMeasurableSet

include hu_cont hc hu_lb hφint in
theorem measure_compl_W :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ (piBox d (Icc 0 a))ᶜ = 0 := by
  change ((volume.restrict (piBox d (Icc 0 a))).withDensity _) _ = 0
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply' (measurableSet_W a), compl_inter_self, measure_empty]

include hu_cont hc hu_lb hφint in
theorem measure_hyperplane (i : Fin d) :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ {w | w i = 0} = 0 := by
  change ((volume.restrict (piBox d (Icc 0 a))).withDensity _) _ = 0
  refine (withDensity_absolutelyContinuous _ _) (measure_mono_null (fun _ hw => hw) ?_)
  exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans
    (Measure.pi_hyperplane _ i 0).le) zero_le

include hkA hk0 hδ hu_cont hu_tan hc hu_lb in
/-- ★ **The tail lies in `{K ≥ δ}` up to a `μ`-null set** (covering by the active cores). -/
theorem measure_compl_inter_sublevel (hA : A.Nonempty) :
    (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ
      ((collarUnion A k h hkA u a δ)ᶜ ∩ {w | ChartModel.phase d A k u w < δ}) = 0 := by
  refine measure_mono_null (t := (piBox d (Icc 0 a))ᶜ ∪ ⋃ i ∈ A, {w | w i = 0}) ?_
    (measure_union_null (measure_compl_W A k h u a hu_cont ϕ φ hc hu_lb hφint)
      (measure_biUnion_null_iff A.countable_toSet |>.2 fun i _ =>
        measure_hyperplane A k h u a hu_cont ϕ φ hc hu_lb hφint i))
  rintro w ⟨hwc, hK⟩
  by_contra hcon
  simp only [mem_union, mem_iUnion, not_or, not_exists, mem_compl_iff, not_not,
    mem_ofPred_eq] at hcon
  have hw : w ∈ piBox d (Icc 0 a) := hcon.1
  have hpos : ∀ i ∈ A, 0 < w i := fun i hi =>
    lt_of_le_of_ne (hw i (mem_univ _)).1 fun h0 => hcon.2 i hi h0.symm
  obtain ⟨I, hIne, hIA, hbase, hnrm⟩ :=
    covering A k u a δ hkA hk0 hA hu_tan hc hu_lb hw hpos hK
  -- `I` as a nonempty subset of `↥A`
  set I' : Finset ↥A := (Finset.univ.filter fun i : ↥A => i.1 ∈ I) with hI'
  have hamb : amb A ⟨I', ?_⟩ = I := by
    ext j
    rw [amb, ChartModel.mem_amb]
    constructor
    · rintro ⟨hjA, hj⟩
      exact (Finset.mem_filter.1 hj).2
    · intro hj
      exact ⟨hIA hj, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
  · obtain ⟨i, hi⟩ := hIne
    exact ⟨⟨i, hIA hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  · refine hwc (mem_iUnion.2 ⟨(coreIdx A).symm ⟨I', by
      obtain ⟨i, hi⟩ := hIne
      exact ⟨⟨i, hIA hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩⟩, ?_⟩)
    rw [Equiv.apply_symm_apply, mem_imageSet_iff A k h hkA u a δ hδ]
    rw [hamb]
    exact ⟨hbase, hnrm⟩

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
/-- ★★ **The collar decomposition of the chart**: `μ = Σ_I μ|_{C_I} + tail` with the phase `≥ δ`
a.e. on the tail; every core is a weighted normalised box core. -/
noncomputable def collar (hA : A.Nonempty) :
    AnalyticCoreDecomposition (locData A k h u a hu_cont ϕ φ hc hu_lb hφint) (numCores A)
      (fun i => KI A k h hkA u a δ (coreIdx A i)) (fun i => nI A (coreIdx A i)) 1 where
  core := fun i => (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ.restrict
    (imageSet A k h hkA u a δ (coreIdx A i))
  tail := (locData A k h u a hu_cont ϕ φ hc hu_lb hφint).μ.restrict
    (collarUnion A k h hkA u a δ)ᶜ
  measure_eq := by
    rw [← restrict_collarUnion A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0
      hφint F, Measure.restrict_add_restrict_compl (measurableSet_collarUnion A k h hkA u a δ hδ
        hu_cont)]
  δ₀ := δ
  δ₀_pos := hδ
  gap := by
    rw [ae_restrict_iff' (measurableSet_collarUnion A k h hkA u a δ hδ hu_cont).compl, ae_iff]
    refine measure_mono_null (fun w hw => ?_)
      (measure_compl_inter_sublevel A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb hφint hA)
    rw [mem_ofPred_eq, Classical.not_imp, not_le] at hw
    exact ⟨hw.1, hw.2⟩
  chart := fun i => stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0
    hφint F (coreIdx A i)

end ChartCollar

end Grammar
