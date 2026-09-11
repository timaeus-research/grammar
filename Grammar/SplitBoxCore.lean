/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StripBoxExpansion
import Grammar.ExactNormalTiling

/-!
# Positive box charts along a splitting, and the abstract core tiling (towards the chart theorem)

For the chart-level theorem the chart is an endomorphism `Ψ` of the ambient space `Fin d → ℝ`
(the resolution chart composed with the strip normalisation and a reflection), and the positive
box lives in the ambient space as `prodToPi σ '' (A × (0,b]^{n+1})` along a splitting
`σ : Fin t ⊕ Fin (n+1) ≃ Fin d` of the coordinates into tangential and normal ones. A
**split box chart** (`SplitBoxChart`) records such a chart with its Jacobian factorisation
`|det DΨ| = u^h · jac` on the box, the exact phase and an amplitude datum, and it exactly presents
the Lebesgue measure on the image of the box (`SplitBoxChart.exists_corePresentation`) — the
change of variables on `Fin d → ℝ` after carrying the chart measure along the volume-preserving
`prodToPi σ` (no determinant of the reindexing is ever needed).

To assemble such charts into a decomposition, the tiling interface is abstracted: a **core piece**
(`CorePiece`) is a compact base type, a normal dimension, a measurable image and a core presentation
of the Lebesgue measure on it; a **core tiling** (`CoreTiling`: pieces inside the region, pairwise
a.e.-disjoint, phase gap off the union) is an analytic core decomposition
(`CoreTiling.hasAnalyticCoreDecomposition`, `CoreTiling.cutoffExpansion`). Split box charts
(`SplitBoxChart.toCorePiece`) and the product-coordinate tiling pieces (`TilingPiece.toCorePiece`)
are core pieces.

Non-claims: no chart-level expansion yet; the reflections along a splitting come next.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {t n d : ℕ}

/-! ### Split box charts -/

/-- The positive box along the splitting `σ`. -/
def splitPosBox (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) (A : Set (Fin t → ℝ)) (b : ℝ) :
    Set (Fin d → ℝ) :=
  prodToPi σ '' (A ×ˢ piBox (n + 1) (Ioc 0 b))

theorem measurableSet_splitPosBox (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) {A : Set (Fin t → ℝ)}
    (hA : MeasurableSet A) (b : ℝ) : MeasurableSet (splitPosBox σ A b) :=
  (prodToPi σ).measurableEmbedding.measurableSet_image.2
    (hA.prod (measurableSet_piBox _ _ measurableSet_Ioc))

/-- **A positive box chart along the splitting `σ`** on the ambient space `Fin d → ℝ`. -/
structure SplitBoxChart (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) (D : LocalisationData (Fin d → ℝ))
    (A : Set (Fin t → ℝ)) (b β : ℝ) where
  /-- the Jacobian exponents -/
  h : Fin (n + 1) → ℕ
  /-- the phase exponents -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the chart -/
  Ψ : (Fin d → ℝ) → (Fin d → ℝ)
  /-- an open neighbourhood of the box on which the chart is `C¹` -/
  V : Set (Fin d → ℝ)
  V_open : IsOpen V
  box_subset : splitPosBox σ A b ⊆ V
  contDiffOn : ContDiffOn ℝ 1 Ψ V
  /-- the null exceptional set of the box off which the chart is injective -/
  N₀ : Set (Fin d → ℝ)
  N₀_meas : MeasurableSet N₀
  N₀_null : volume N₀ = 0
  injOn : InjOn Ψ (splitPosBox σ A b \ N₀)
  /-- the Jacobian unit -/
  jac : (Fin d → ℝ) → ℝ
  measurable_jac : Measurable jac
  jac_nonneg : ∀ y ∈ splitPosBox σ A b, 0 ≤ jac y
  det_eq : ∀ p ∈ A ×ˢ piBox (n + 1) (Ioc 0 b),
    |(fderiv ℝ Ψ (prodToPi σ p)).det| = (∏ i, p.2 i ^ h i) * jac (prodToPi σ p)
  phase_eq : ∀ p ∈ A ×ˢ piBox (n + 1) (Ioc 0 b),
    D.phase (Ψ (prodToPi σ p)) = β * ∏ i, p.2 i ^ (2 * k i)
  /-- the tangential datum realising the amplitude `jac · F∘Ψ` -/
  amp : TangentialData A (n + 1)
  amp_xi : ∀ v, xiCoord (amp v) = 0
  amp_eq : ∀ (v : A), ∀ u ∈ piBox (n + 1) (Ioc 0 b),
    evalF (toEta b (amp v)) u = jac (prodToPi σ (v.1, u)) * D.obs (Ψ (prodToPi σ (v.1, u)))

namespace SplitBoxChart

variable {σ : Fin t ⊕ Fin (n + 1) ≃ Fin d} {D : LocalisationData (Fin d → ℝ)}
  {A : Set (Fin t → ℝ)} {b β : ℝ} (C : SplitBoxChart σ D A b β)

/-- **The core presentation of a split box chart** (data: base measure `comap Subtype.val volume`
on `A`, exponents `C.h`, `C.k`, box side `b`, chart `Ψ ∘ prodToPi` extended by zero, density
`C.jac`, tangential datum `C.amp`). -/
noncomputable def corePresentation (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    CorePresentation D (volume.restrict (C.Ψ '' splitPosBox σ A b)) A n β := by
  classical
  set S₀ := A ×ˢ piBox (n + 1) (Ioc 0 b) with hS₀
  have hS₀m : MeasurableSet S₀ := hA.prod (measurableSet_piBox _ _ measurableSet_Ioc)
  set S := splitPosBox σ A b with hS
  have hSm : MeasurableSet S := measurableSet_splitPosBox σ hA b
  -- the base measure
  set ν : Measure A := Measure.comap Subtype.val volume with hν
  have hemb : MeasurableEmbedding (Subtype.val : A → Fin t → ℝ) :=
    MeasurableEmbedding.subtype_coe hA
  have hνfin : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.comap_apply _ Subtype.val_injective
      (fun s hs => hemb.measurableSet_image.2 hs) _ MeasurableSet.univ, image_univ,
      Subtype.range_coe]
    exact hAfin⟩
  -- the embedding of the parameter space into the ambient space
  set ι : A × (Fin (n + 1) → ℝ) → (Fin t → ℝ) × (Fin (n + 1) → ℝ) := fun p => (p.1.1, p.2)
    with hι
  have hιm : Measurable ι := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hιeq : ι = Prod.map (Subtype.val : A → Fin t → ℝ) id := by
    funext p
    rfl
  set j : A × (Fin (n + 1) → ℝ) → (Fin d → ℝ) := (prodToPi σ) ∘ ι with hj
  have hjm : Measurable j := (prodToPi σ).measurable.comp hιm
  have hmem : ∀ p : A × (Fin (n + 1) → ℝ), p.2 ∈ piBox (n + 1) (Ioc 0 b) → ι p ∈ S₀ :=
    fun p hp => ⟨p.1.2, hp⟩
  have hmemS : ∀ p : A × (Fin (n + 1) → ℝ), p.2 ∈ piBox (n + 1) (Ioc 0 b) → j p ∈ S :=
    fun p hp => ⟨ι p, hmem p hp, rfl⟩
  -- the measurable extension of the chart
  set Ψ' := S.piecewise C.Ψ 0 with hΨ'
  have hΨ'eq : EqOn Ψ' C.Ψ S := fun q hq => piecewise_eq_of_mem _ _ _ hq
  have hcont : ContinuousOn C.Ψ S := C.contDiffOn.continuousOn.mono C.box_subset
  have hΨ'm : Measurable Ψ' := by
    refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
    · have h : S.domRestrict Ψ' = S.domRestrict C.Ψ := funext fun q => hΨ'eq q.2
      rw [h]
      exact (continuousOn_iff_continuous_domRestrict.1 hcont).measurable
    · have h : Sᶜ.domRestrict Ψ' = fun _ => (0 : Fin d → ℝ) :=
        funext fun q => piecewise_eq_of_notMem _ _ _ q.2
      rw [h]
      exact measurable_const
  -- the chart measure is the Lebesgue measure of the box
  have hmapι : (chartMeasure ν n b).map ι = volume.restrict S₀ := by
    unfold chartMeasure
    rw [hιeq, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id, hν,
      hemb.map_comap, Subtype.range_coe, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hmapj : (chartMeasure ν n b).map j = volume.restrict S := by
    rw [hj, ← Measure.map_map (prodToPi σ).measurable hιm, hmapι, hS, splitPosBox,
      ← measurePreserving_prodToPi.map_eq, MeasurableEquiv.restrict_map,
      Set.preimage_image_eq _ (prodToPi σ).injective]
  -- the density
  set g : (Fin d → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal ((∏ i, y (nIdx σ i) ^ C.h i) * C.jac y) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp ((Finset.measurable_prod _ fun i _ =>
      (measurable_pi_apply (nIdx σ i)).pow_const _).mul C.measurable_jac)
  have hdens : (fun p : A × (Fin (n + 1) → ℝ) =>
      ((chartDensity C.h (fun p => C.jac (j p)) p).toNNReal : ℝ≥0∞)) = fun p => g (j p) := by
    funext p
    simp only [hg, hj, chartDensity, Function.comp, prodToPi_apply_nIdx]
    rfl
  have hderiv : ∀ y ∈ S, HasFDerivWithinAt C.Ψ (fderiv ℝ C.Ψ y) S y := fun y hy =>
    (((C.contDiffOn.differentiableOn one_ne_zero) y (C.box_subset hy)).differentiableAt
      (C.V_open.mem_nhds (C.box_subset hy))).hasFDerivAt.hasFDerivWithinAt
  have hgdet : g =ᵐ[volume.restrict S] fun y => ENNReal.ofReal |(fderiv ℝ C.Ψ y).det| := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
    refine Eventually.of_forall fun y hy => ?_
    obtain ⟨p, hp, rfl⟩ := hy
    simp only [hg]
    rw [C.det_eq p hp]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [prodToPi_apply_nIdx]
  have hΨ'ae : Ψ' =ᵐ[(volume.restrict S).withDensity g] C.Ψ := by
    refine (withDensity_absolutelyContinuous _ _).ae_eq ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
    exact Eventually.of_forall fun y hy => hΨ'eq hy
  -- the null exceptional set: the box and its image are unchanged up to null sets
  set S' := S \ C.N₀ with hS'
  have hS'm : MeasurableSet S' := hSm.diff C.N₀_meas
  have hSS' : volume.restrict S = volume.restrict S' :=
    (Measure.restrict_congr_set
      ((sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right C.N₀_null)))).symm
  have himg : volume.restrict (C.Ψ '' S) = volume.restrict (C.Ψ '' S') := by
    refine Measure.restrict_congr_set ?_
    have hdec : C.Ψ '' S = C.Ψ '' S' ∪ C.Ψ '' (S ∩ C.N₀) := by
      rw [← image_union, hS', sdiff_union_inter]
    have hnull : volume (C.Ψ '' (S ∩ C.N₀)) = 0 := by
      refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
        (measure_mono_null inter_subset_right C.N₀_null)
      exact ((C.contDiffOn.differentiableOn one_ne_zero).mono
        (inter_subset_left.trans C.box_subset))
    rw [hdec]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 hnull)
  have hderiv' : ∀ y ∈ S', HasFDerivWithinAt C.Ψ (fderiv ℝ C.Ψ y) S' y := fun y hy =>
    (hderiv y hy.1).mono sdiff_subset
  have htransport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity C.h (fun p => C.jac (j p)) p).toNNReal : ℝ≥0∞)).map (Ψ' ∘ j) =
      volume.restrict (C.Ψ '' S) := by
    rw [hdens, ← Measure.map_map hΨ'm hjm, map_withDensity_comp _ hjm hgm, hmapj,
      Measure.map_congr hΨ'ae, withDensity_congr_ae hgdet, hSS', himg]
    exact map_withDensity_abs_det_fderiv_eq_addHaar volume hS'm.nullMeasurableSet hderiv' C.injOn
  refine ⟨ν, C.h, C.k, C.k_pos, b, hb, Ψ' ∘ j, hΨ'm.comp hjm, fun p => C.jac (j p),
    C.measurable_jac.comp hjm, ?_, C.amp, htransport, ?_, ?_, C.amp_xi⟩
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    exact C.jac_nonneg _ (hmemS p hp)
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    change D.phase (Ψ' (j p)) = _
    rw [hΨ'eq (hmemS p hp)]
    exact C.phase_eq _ (hmem p hp)
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    change evalF (toEta b (C.amp p.1)) p.2 = C.jac (j p) * D.obs (Ψ' (j p))
    rw [hΨ'eq (hmemS p hp)]
    exact C.amp_eq p.1 p.2 hp

theorem corePresentation_h (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    (C.corePresentation hA hAfin hb).h = C.h := rfl

theorem corePresentation_k (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    (C.corePresentation hA hAfin hb).k = C.k := rfl

theorem corePresentation_b (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    (C.corePresentation hA hAfin hb).b = b := rfl

theorem corePresentation_x (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    (C.corePresentation hA hAfin hb).x = C.amp := rfl

theorem corePresentation_ν (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    (C.corePresentation hA hAfin hb).ν = Measure.comap Subtype.val volume := rfl

/-- **The core presentation of a split box chart** (existence form). -/
theorem exists_corePresentation (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    Nonempty (CorePresentation D (volume.restrict (C.Ψ '' splitPosBox σ A b)) A n β) :=
  ⟨C.corePresentation hA hAfin hb⟩

end SplitBoxChart

/-! ### Abstract core pieces and core tilings -/

variable {U : Type*} [MeasureSpace U]

/-- **A core piece**: a compact base, a normal dimension, a measurable image, and a core
presentation of the Lebesgue measure on the image. -/
structure CorePiece (D : LocalisationData U) (β : ℝ) where
  /-- the base type -/
  K : Type
  [instTop : TopologicalSpace K]
  [instMeas : MeasurableSpace K]
  [instCompact : CompactSpace K]
  [instT2 : T2Space K]
  [instOpens : OpensMeasurableSpace K]
  /-- the normal dimension minus one -/
  n : ℕ
  /-- the image -/
  image : Set U
  nullMeasurableSet_image : NullMeasurableSet image volume
  /-- the core presentation -/
  pres : CorePresentation D (volume.restrict image) K n β

attribute [instance] CorePiece.instTop CorePiece.instMeas CorePiece.instCompact CorePiece.instT2
  CorePiece.instOpens

/-- A product-coordinate tiling piece is a core piece. -/
noncomputable def TilingPiece.toCorePiece {D : LocalisationData U} {β : ℝ} (P : TilingPiece D β) :
    CorePiece D β where
  K := P.A
  instCompact := isCompact_iff_compactSpace.1 P.A_compact
  n := P.n
  image := P.image
  nullMeasurableSet_image := P.measurableSet_image.nullMeasurableSet
  pres := P.exists_corePresentation.some

/-- A split box chart over a compact base is a core piece. -/
noncomputable def SplitBoxChart.toCorePiece {σ : Fin t ⊕ Fin (n + 1) ≃ Fin d}
    {D : LocalisationData (Fin d → ℝ)} {A : Set (Fin t → ℝ)} {b β : ℝ}
    (C : SplitBoxChart σ D A b β) (hA : IsCompact A) (hb : 0 < b) : CorePiece D β where
  K := A
  instCompact := isCompact_iff_compactSpace.1 hA
  n := n
  image := C.Ψ '' splitPosBox σ A b
  nullMeasurableSet_image := by
    have hSm : MeasurableSet (splitPosBox σ A b) :=
      measurableSet_splitPosBox σ hA.isClosed.measurableSet b
    have hdec : C.Ψ '' splitPosBox σ A b =
        C.Ψ '' (splitPosBox σ A b \ C.N₀) ∪ C.Ψ '' (splitPosBox σ A b ∩ C.N₀) := by
      rw [← image_union, sdiff_union_inter]
    rw [hdec]
    refine NullMeasurableSet.union ?_ (NullMeasurableSet.of_null ?_)
    · exact ((hSm.diff C.N₀_meas).image_of_continuousOn_injOn
        (C.contDiffOn.continuousOn.mono (sdiff_subset.trans C.box_subset))
        C.injOn).nullMeasurableSet
    · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
        (measure_mono_null inter_subset_right C.N₀_null)
      exact ((C.contDiffOn.differentiableOn one_ne_zero).mono
        (inter_subset_left.trans C.box_subset))
  pres := C.corePresentation hA.isClosed.measurableSet hA.measure_lt_top hb

/-- **A core tiling**: finitely many core pieces inside the region, pairwise disjoint up to null
sets, with a positive phase gap off their union. -/
structure CoreTiling (D : LocalisationData U) (β : ℝ) where
  /-- the integration region -/
  Ω : Set U
  μ_eq : D.μ = volume.restrict Ω
  /-- the number of pieces -/
  M : ℕ
  /-- the pieces -/
  piece : Fin M → CorePiece D β
  image_subset : ∀ I, (piece I).image ⊆ Ω
  aedisjoint : ∀ I J, I ≠ J → volume ((piece I).image ∩ (piece J).image) = 0
  /-- the phase gap off the pieces -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂D.μ, z ∉ ⋃ I, (piece I).image → δ₀ ≤ D.phase z

namespace CoreTiling

variable {D : LocalisationData U} {β : ℝ}

theorem restrict_iUnion_image_eq (T : CoreTiling D β) :
    (volume.restrict T.Ω).restrict (⋃ I, (T.piece I).image) =
      ∑ I, volume.restrict (T.piece I).image := by
  classical
  have hmeas : ∀ I, NullMeasurableSet (T.piece I).image volume := fun I =>
    (T.piece I).nullMeasurableSet_image
  have hU : NullMeasurableSet (⋃ I, (T.piece I).image) volume := NullMeasurableSet.iUnion hmeas
  have hsub : (⋃ I, (T.piece I).image) ⊆ T.Ω := iUnion_subset T.image_subset
  rw [Measure.restrict_restrict₀
      (hU.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)),
    inter_eq_left.2 hsub,
    Measure.restrict_iUnion_ae (fun I J hIJ => T.aedisjoint I J hIJ) hmeas, Measure.sum_fintype]

/-- The measurable hull of the union of the piece images. -/
def measurableUnion (T : CoreTiling D β) : Set U := toMeasurable volume (⋃ I, (T.piece I).image)

theorem measurableSet_measurableUnion (T : CoreTiling D β) : MeasurableSet T.measurableUnion :=
  measurableSet_toMeasurable _ _

theorem subset_measurableUnion (T : CoreTiling D β) :
    (⋃ I, (T.piece I).image) ⊆ T.measurableUnion :=
  subset_toMeasurable _ _

theorem measurableUnion_ae_eq (T : CoreTiling D β) :
    T.measurableUnion =ᵐ[volume] ⋃ I, (T.piece I).image :=
  (NullMeasurableSet.iUnion fun I => (T.piece I).nullMeasurableSet_image).toMeasurable_ae_eq

/-- **The analytic core decomposition of a core tiling** (data): the cores are the Lebesgue
measures of the piece images, the tail is the Lebesgue measure of the region off the measurable
hull of the union of the pieces. -/
noncomputable def toAnalyticCoreDecomposition (T : CoreTiling D β) :
    AnalyticCoreDecomposition D T.M (fun I => (T.piece I).K) (fun I => (T.piece I).n) β where
  core I := volume.restrict (T.piece I).image
  tail := volume.restrict (T.Ω \ T.measurableUnion)
  measure_eq := by
    classical
    have hU := T.measurableSet_measurableUnion
    have h1 : (volume.restrict T.Ω).restrict T.measurableUnion =
        (volume.restrict T.Ω).restrict (⋃ I, (T.piece I).image) :=
      Measure.restrict_congr_set (ae_restrict_of_ae T.measurableUnion_ae_eq)
    have h2 : (volume.restrict T.Ω).restrict T.measurableUnionᶜ =
        volume.restrict (T.Ω \ T.measurableUnion) := by
      rw [Measure.restrict_restrict hU.compl, sdiff_eq, inter_comm]
    rw [T.μ_eq, ← T.restrict_iUnion_image_eq, ← h1, ← h2]
    exact (Measure.restrict_add_restrict_compl hU).symm
  δ₀ := T.δ₀
  δ₀_pos := T.δ₀_pos
  gap := by
    classical
    have hU := T.measurableSet_measurableUnion
    have h2 : (volume.restrict T.Ω).restrict T.measurableUnionᶜ =
        volume.restrict (T.Ω \ T.measurableUnion) := by
      rw [Measure.restrict_restrict hU.compl, sdiff_eq, inter_comm]
    rw [← h2, ← T.μ_eq, ae_restrict_iff' hU.compl]
    filter_upwards [T.gap] with z hz hzc
    exact hz fun hzU => hzc (T.subset_measurableUnion hzU)
  chart I := (T.piece I).pres

theorem toAnalyticCoreDecomposition_h (T : CoreTiling D β) (I : Fin T.M) :
    T.toAnalyticCoreDecomposition.h I = (T.piece I).pres.h := rfl

theorem toAnalyticCoreDecomposition_k (T : CoreTiling D β) (I : Fin T.M) :
    T.toAnalyticCoreDecomposition.k I = (T.piece I).pres.k := rfl

theorem toAnalyticCoreDecomposition_b (T : CoreTiling D β) (I : Fin T.M) :
    T.toAnalyticCoreDecomposition.b I = (T.piece I).pres.b := rfl

theorem toAnalyticCoreDecomposition_x (T : CoreTiling D β) (I : Fin T.M) :
    T.toAnalyticCoreDecomposition.x I = (T.piece I).pres.x := rfl

theorem toAnalyticCoreDecomposition_ν (T : CoreTiling D β) (I : Fin T.M) :
    T.toAnalyticCoreDecomposition.ν I = (T.piece I).pres.ν := rfl

/-- **The bridge**: a core tiling is an analytic core decomposition. -/
theorem hasAnalyticCoreDecomposition (T : CoreTiling D β) : HasAnalyticCoreDecomposition D β :=
  ⟨T.M, fun I => (T.piece I).K, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun I => (T.piece I).n, ⟨T.toAnalyticCoreDecomposition⟩⟩

/-- **The population expansion from a core tiling.** -/
theorem cutoffExpansion (T : CoreTiling D β) (hβ : 0 < β) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧ CutoffExpansion Q Dg D.Z c :=
  cutoffExpansion_of_hasAnalyticCoreDecomposition hβ T.hasAnalyticCoreDecomposition

end CoreTiling

end Grammar
