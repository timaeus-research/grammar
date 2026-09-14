/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceMonomial
import Grammar.SmoothAmplitudeFamily
import Grammar.ChartPieces

/-!
# Transport of a chart piece onto the smooth chart measure (consult #117 §7, U6b transport)

For a chart with active set `J` (enumerated by `e : Fin da ≃ J`), the positive box `[0,a]^d`
splits as the compact INACTIVE base `Base J a = [0,a]^{J^c}` times the active box `(0,a]^{da}`
(`glueE`), a measurable embedding carrying Lebesgue measure to Lebesgue measure
(`map_glueE_prod`), and the piece measure `(vol|_{[0,a]^d})·|w|^h ϕ(refl σ w)` is the transport of
the smooth chart measure `(vol_{base}·s^{h_{J^c}}) ⊗ (vol|_{(0,a]^{da}})` with density
`v^{h_J} · ϕ(refl σ (glue s v))` (★ `map_glueE_pieceMeasure`) — the shape of the `transport` field
of a `SmoothCorePresentation`. Also `MeasurableEmbedding.map_withDensity_comp`: densities transport
along measurable embeddings. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SmoothEngine

/-! ### Densities transport along measurable embeddings -/

theorem _root_.MeasurableEmbedding.map_withDensity_comp {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {T : α → β} (hT : MeasurableEmbedding T) (μ : Measure α)
    (f : β → ℝ≥0∞) : (μ.withDensity fun x => f (T x)).map T = (μ.map T).withDensity f := by
  ext s hs
  rw [hT.map_apply, withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, hT.lintegral_map, ← lintegral_indicator (hT.measurable hs)]
  rfl

/-! ### The compact inactive base -/

variable {d : ℕ} (J : Finset (Fin d)) (a : ℝ)

/-- The closed inactive box `[0,a]^{J^c}`. -/
def baseBox : Set ({i // ¬ inJ J i} → ℝ) := Set.pi univ fun _ => Icc 0 a

theorem isCompact_baseBox : IsCompact (baseBox J a) := isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_baseBox : MeasurableSet (baseBox J a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The base of a chart piece: the closed inactive box as a compact type. -/
abbrev Base : Type := ↥(baseBox J a)

instance : CompactSpace (Base J a) := isCompact_iff_compactSpace.1 (isCompact_baseBox J a)

theorem Base_val_nonneg (s : Base J a) (j : {i // ¬ inJ J i}) : 0 ≤ s.1 j :=
  (s.2 j (Set.mem_univ j)).1

theorem Base_val_le (s : Base J a) (j : {i // ¬ inJ J i}) : s.1 j ≤ a :=
  (s.2 j (Set.mem_univ j)).2

theorem measurableEmbedding_Base_val :
    MeasurableEmbedding (Subtype.val : Base J a → {i // ¬ inJ J i} → ℝ) :=
  MeasurableEmbedding.subtype_coe (measurableSet_baseBox J a)

/-- Lebesgue measure on the base. -/
noncomputable def baseVol : Measure (Base J a) :=
  Measure.comap (Subtype.val : Base J a → {i // ¬ inJ J i} → ℝ) volume

theorem map_val_baseVol : (baseVol J a).map Subtype.val = volume.restrict (baseBox J a) :=
  map_comap_subtype_coe (measurableSet_baseBox J a) volume

instance : IsFiniteMeasure (baseVol J a) := by
  refine ⟨?_⟩
  unfold baseVol
  rw [(measurableEmbedding_Base_val J a).comap_apply, Set.image_univ, Subtype.range_coe]
  exact (isCompact_baseBox J a).measure_lt_top

/-! ### Gluing the base and the active box -/

variable {da : ℕ} (e : Fin da ≃ {i // inJ J i})

/-- The glued chart coordinate: active coordinates `v ∘ e.symm`, inactive coordinates `s`. -/
def glueE (s : Base J a) (v : Fin da → ℝ) : Fin d → ℝ := glue J (fun i => v (e.symm i)) s.1

/-- The glued coordinate as a map on the product. -/
def glueE' : Base J a × (Fin da → ℝ) → (Fin d → ℝ) := fun z => glueE J a e z.1 z.2

theorem glueE_apply_active (s : Base J a) (v : Fin da → ℝ) (j : Fin da) :
    glueE J a e s v (e j).1 = v j := by
  unfold glueE
  rw [glue_apply_of_mem J _ _ (e j).2]
  simp

theorem glueE_apply_inactive (s : Base J a) (v : Fin da → ℝ) {i : Fin d} (hi : i ∉ J) :
    glueE J a e s v i = s.1 ⟨i, hi⟩ := by
  unfold glueE
  rw [glue_apply_of_not_mem J _ _ hi]

/-- The reindexing of the active coordinates. -/
noncomputable def activeEquiv : (Fin da → ℝ) ≃ᵐ ({i // inJ J i} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) e

theorem activeEquiv_apply (v : Fin da → ℝ) (i : {i // inJ J i}) :
    activeEquiv J e v i = v (e.symm i) := by
  unfold activeEquiv
  conv_lhs => rw [← e.apply_symm_apply i]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]

/-- `glueE'` as a composition of measurable embeddings. -/
theorem glueE'_eq : glueE' J a e =
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm ∘
      Prod.swap ∘ Prod.map (Subtype.val : Base J a → _) (activeEquiv J e) := by
  funext z
  change glue J (fun i => z.2 (e.symm i)) z.1.1 = glue J (activeEquiv J e z.2) z.1.1
  congr 1
  funext i
  rw [activeEquiv_apply]

theorem measurableEmbedding_glueE' : MeasurableEmbedding (glueE' J a e) := by
  rw [glueE'_eq]
  have hswap : MeasurableEmbedding
      (Prod.swap : ({i // ¬ inJ J i} → ℝ) × ({i // inJ J i} → ℝ) → _) :=
    (MeasurableEquiv.prodComm (α := {i // ¬ inJ J i} → ℝ)
      (β := {i // inJ J i} → ℝ)).measurableEmbedding
  have hprod : MeasurableEmbedding (Prod.map (Subtype.val : Base J a → _) (activeEquiv J e)) :=
    (measurableEmbedding_Base_val J a).prodMap (MeasurableEquiv.measurableEmbedding _)
  exact (MeasurableEquiv.measurableEmbedding _).comp (hswap.comp hprod)

theorem continuous_glueE' : Continuous (glueE' J a e) := by
  unfold glueE' glueE
  exact (continuous_glue J).comp (Continuous.prodMk
    (continuous_pi fun i => (continuous_apply (e.symm i)).comp continuous_snd)
    (continuous_subtype_val.comp continuous_fst))

/-! ### Lebesgue measure is transported to Lebesgue measure -/

/-- The mixed box: active coordinates in `(0,a]`, inactive coordinates in `[0,a]`. -/
def mixedBox : Set (Fin d → ℝ) :=
  {w | (∀ i, inJ J i → w i ∈ Ioc 0 a) ∧ ∀ i, ¬ inJ J i → w i ∈ Icc 0 a}

theorem preimage_mixedBox :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm ⁻¹' mixedBox J a =
      box {i // inJ J i} a ×ˢ baseBox J a := by
  ext ⟨u, w⟩
  simp only [Set.mem_preimage, Set.mem_prod, mixedBox, Set.mem_ofPred_eq, box, baseBox,
    Set.mem_univ_pi]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h1 i.1 i.2; rwa [← glue, glue_apply_subtype] at this
    · have := h2 i.1 i.2; rwa [← glue, glue_apply_subtype'] at this
  · rintro ⟨hu, hw⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · change glue J u w i ∈ Ioc 0 a; rw [glue_apply_of_mem J u w hi]; exact hu ⟨i, hi⟩
    · change glue J u w i ∈ Icc 0 a; rw [glue_apply_of_not_mem J u w hi]; exact hw ⟨i, hi⟩

theorem box_subset_mixedBox : box (Fin d) a ⊆ mixedBox J a := fun _ hw =>
  ⟨fun i _ => hw i (Set.mem_univ i), fun i _ => Ioc_subset_Icc_self (hw i (Set.mem_univ i))⟩

theorem mixedBox_subset_Icc : mixedBox J a ⊆ piBox d (Icc 0 a) := fun _ hw i _ => by
  by_cases hi : inJ J i
  · exact Ioc_subset_Icc_self (hw.1 i hi)
  · exact hw.2 i hi

theorem restrict_mixedBox : (volume : Measure (Fin d → ℝ)).restrict (mixedBox J a) =
    volume.restrict (piBox d (Icc 0 a)) := by
  refine le_antisymm (Measure.restrict_mono (mixedBox_subset_Icc J a) le_rfl) ?_
  have h := restrict_box_eq_restrict_Icc (ι := Fin d) a
  change volume.restrict (Set.pi univ fun _ => Icc 0 a) ≤ _
  rw [← h]
  exact Measure.restrict_mono (box_subset_mixedBox J a) le_rfl

theorem preimage_activeEquiv_box :
    activeEquiv J e ⁻¹' box {i // inJ J i} a = box (Fin da) a := by
  unfold activeEquiv
  rw [box, box, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_preimage_univ_pi]

theorem map_activeEquiv_restrict :
    (volume.restrict (box (Fin da) a)).map (activeEquiv J e) =
      volume.restrict (box {i // inJ J i} a) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : {i // inJ J i} => ℝ) e
  have := hmp.restrict_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (box {i // inJ J i} a)
  have hpre := preimage_activeEquiv_box J a e
  unfold activeEquiv at hpre ⊢
  rw [hpre] at this
  exact this.map_eq

/-- ★ **Lebesgue measure is transported to Lebesgue measure**: the glued image of
`vol_{base} ⊗ vol|_{(0,a]^{da}}` is `vol|_{[0,a]^d}`. -/
theorem map_glueE'_prod :
    ((baseVol J a).prod (volume.restrict (box (Fin da) a))).map (glueE' J a e) =
      volume.restrict (piBox d (Icc 0 a)) := by
  have hval := (measurableEmbedding_Base_val J a).measurable
  have hact := (activeEquiv J e).measurable
  rw [glueE'_eq, ← Measure.map_map (MeasurableEquiv.measurable _)
    (measurable_swap.comp (hval.prodMap hact)),
    ← Measure.map_map measurable_swap (hval.prodMap hact),
    ← Measure.map_prod_map _ _ hval hact, map_val_baseVol, map_activeEquiv_restrict,
    Measure.prod_swap, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hmp := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm
  have := (hmp.restrict_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (mixedBox J a)).map_eq
  rw [preimage_mixedBox] at this
  rw [this, restrict_mixedBox]

/-! ### The piece measure as a transported smooth chart measure -/

/-- The inactive Jacobian weight `∏_{j ∉ J} s_j^{h_j}` on the base. -/
noncomputable def baseWeight (h : Fin d → ℕ) (s : Base J a) : ℝ :=
  ∏ j : {i // ¬ inJ J i}, s.1 j ^ h j.1

theorem baseWeight_nonneg (h : Fin d → ℕ) (s : Base J a) : 0 ≤ baseWeight J a h s :=
  Finset.prod_nonneg fun j _ => pow_nonneg (Base_val_nonneg J a s j) _

theorem measurable_baseWeight (h : Fin d → ℕ) : Measurable (baseWeight J a h) := by
  unfold baseWeight
  exact Finset.measurable_prod _ fun j _ =>
    ((measurable_pi_apply j).comp (measurableEmbedding_Base_val J a).measurable).pow_const (h j.1)

theorem continuous_baseWeight (h : Fin d → ℕ) : Continuous (baseWeight J a h) := by
  unfold baseWeight
  exact continuous_finsetProd _ fun j _ =>
    ((continuous_apply j).comp continuous_subtype_val).pow (h j.1)

/-- The base measure of a chart piece: Lebesgue measure with the inactive Jacobian weight. -/
noncomputable def baseMeasure (h : Fin d → ℕ) : Measure (Base J a) :=
  (baseVol J a).withDensity fun s => ENNReal.ofReal (baseWeight J a h s)

instance (h : Fin d → ℕ) : IsFiniteMeasure (baseMeasure J a h) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Base J a)).exists_bound_of_continuousOn
    (continuous_baseWeight J a h).continuousOn
  refine ⟨?_⟩
  unfold baseMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ s, ENNReal.ofReal (baseWeight J a h s) ∂baseVol J a
      ≤ ∫⁻ _, ENNReal.ofReal B ∂baseVol J a :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal
          ((le_abs_self _).trans (by have := hB s (Set.mem_univ s); rwa [Real.norm_eq_abs] at this))
    _ = ENNReal.ofReal B * baseVol J a univ := lintegral_const _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The Jacobian monomial splits into the inactive base weight and the active monomial. -/
theorem wgt_glueE (h : Fin d → ℕ) (s : Base J a) {v : Fin da → ℝ} (hv : v ∈ box (Fin da) a) :
    NormalisedBox.wgt h (glueE J a e s v) =
      baseWeight J a h s * mono (fun j => h (e j).1) v := by
  unfold NormalisedBox.wgt baseWeight mono
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ J), mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [glueE_apply_inactive J a e s v j.2, abs_of_nonneg (Base_val_nonneg J a s j)]
  · rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [glueE_apply_active, abs_of_pos (pos_of_mem_box hv j)]

/-- Almost every point of the smooth chart measure has its active coordinates in the box. -/
theorem ae_snd_mem_box' (ν : Measure (Base J a)) [SFinite ν] :
    ∀ᵐ z ∂(ν.prod (volume.restrict (box (Fin da) a))), z.2 ∈ box (Fin da) a := by
  rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict]
  exact (ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_box a))).mono fun z hz => hz.2

/-- ★ **The piece measure is the transport of the smooth chart measure**:
`(vol_{base}·s^{h_{J^c}}) ⊗ vol|_{(0,a]^{da}}` with density `v^{h_J} · ϕ(refl σ (glue s v))`,
pushed along `glueE`, is `(vol|_{[0,a]^d})·|w|^h·ϕ(refl σ w)`. -/
theorem map_glueE'_pieceMeasure (h : Fin d → ℕ) {ϕ : (Fin d → ℝ) → ℝ} (hϕ : Measurable ϕ)
    (σ : WaterFilling.CoordSign d) :
    (((baseMeasure J a h).prod (volume.restrict (box (Fin da) a))).withDensity fun z =>
      ENNReal.ofReal (mono (fun j => h (e j).1) z.2 *
        ϕ (WaterFilling.refl σ (glueE' J a e z)))).map (glueE' J a e) =
      ChartCollar.pieceMeasure h a ϕ σ := by
  have hm1 : Measurable fun s : Base J a => ENNReal.ofReal (baseWeight J a h s) :=
    ENNReal.measurable_ofReal.comp (measurable_baseWeight J a h)
  have hm2 : Measurable fun z : Base J a × (Fin da → ℝ) =>
      ENNReal.ofReal (mono (fun j => h (e j).1) z.2 * ϕ (WaterFilling.refl σ (glueE' J a e z))) :=
    ENNReal.measurable_ofReal.comp (((measurable_mono _).comp measurable_snd).mul
      (hϕ.comp ((WaterFilling.measurable_refl σ).comp
        (measurableEmbedding_glueE' J a e).measurable)))
  have hm1' : Measurable fun z : Base J a × (Fin da → ℝ) =>
      ENNReal.ofReal (baseWeight J a h z.1) := hm1.comp measurable_fst
  unfold baseMeasure
  rw [prod_withDensity_left hm1, ← withDensity_mul _ hm1' hm2]
  have hae : ((fun z : Base J a × (Fin da → ℝ) => ENNReal.ofReal (baseWeight J a h z.1)) *
      fun z => ENNReal.ofReal (mono (fun j => h (e j).1) z.2 *
        ϕ (WaterFilling.refl σ (glueE' J a e z))))
      =ᵐ[(baseVol J a).prod (volume.restrict (box (Fin da) a))]
      fun z => ENNReal.ofReal (NormalisedBox.wgt h (glueE' J a e z) *
        ϕ (WaterFilling.refl σ (glueE' J a e z))) := by
    refine (ae_snd_mem_box' J a (baseVol J a)).mono fun z hz => ?_
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (baseWeight_nonneg J a h z.1)]
    congr 1
    change baseWeight J a h z.1 * (mono (fun j => h (e j).1) z.2 *
      ϕ (WaterFilling.refl σ (glueE J a e z.1 z.2))) =
      NormalisedBox.wgt h (glueE J a e z.1 z.2) * ϕ (WaterFilling.refl σ (glueE J a e z.1 z.2))
    rw [wgt_glueE J a e h z.1 hz]
    ring
  rw [withDensity_congr_ae hae, (measurableEmbedding_glueE' J a e).map_withDensity_comp _
    (fun w => ENNReal.ofReal (NormalisedBox.wgt h w * ϕ (WaterFilling.refl σ w))),
    map_glueE'_prod]
  rfl

end SmoothEngine

end Grammar
