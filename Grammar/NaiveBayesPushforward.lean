/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayes
import Grammar.NaiveBayesClosedForm

/-!
# The pushforward of the naive Bayes prior along the moment coordinates

End-to-end: the uniform prior on the cube `[0,1]⁵` of parameters `(t, (a₁, b₁), (a₂, b₂))`,
pushed forward along the observable moments `(λ₁, λ₂, μ)` (the two means and the covariance),
is the measure with density `nbFibreDensity λ₁ λ₂ μ` on `(0,1)² × ℝ`
(★★★ `lintegral_nbBox_moments`):

  `∫_{[0,1]⁵} Ψ(λ₁(θ), λ₂(θ), μ(θ)) dθ = ∫_{(0,1)²} ∫_ℝ Ψ(λ, z) · nbFibreDensity(λ, z) dz dλ`,

and by `nbFibreDensity_closed_pos/neg` that density is `2 log(M±/|z|) log(V/(M±|z|))` on
`0 < |z| < M±`.  The proof composes the measure-preserving moment map
(`measurePreserving_nbMomentMap`), a measure-preserving reordering of the coordinates
`(t, (λ₁, η₁), (λ₂, η₂)) ↦ ((λ₁, λ₂), (t, (η₁, η₂)))` built from `prodAssoc`/`prodComm`, Tonelli,
and the identification of the slice of the image at fixed means with the region `nbRegion`
(up to the null slices `t ∈ {0, 1}`).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- Reordering `(t, (λ₁, η₁), (λ₂, η₂)) ↦ ((λ₁, λ₂), (t, (η₁, η₂)))`. -/
def nbReorder (ζ : NBParam) : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) :=
  ((ζ.2.1.1, ζ.2.2.1), (ζ.1, (ζ.2.1.2, ζ.2.2.2)))

/-- The inverse reordering. -/
def nbReorderInv (ω : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) : NBParam :=
  (ω.2.1, (ω.1.1, ω.2.2.1), (ω.1.2, ω.2.2.2))

@[simp] theorem nbReorderInv_nbReorder (ζ : NBParam) : nbReorderInv (nbReorder ζ) = ζ := rfl
@[simp] theorem nbReorder_nbReorderInv (ω : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) :
    nbReorder (nbReorderInv ω) = ω := rfl

theorem measurable_nbReorder : Measurable nbReorder := by unfold nbReorder; fun_prop
theorem measurable_nbReorderInv : Measurable nbReorderInv := by unfold nbReorderInv; fun_prop

/-- The interchange `((a, b), (c, d)) ↦ ((a, c), (b, d))` preserves the product measure. -/
theorem measurePreserving_interchange :
    MeasurePreserving (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      volume volume := by
  -- ((a,b),(c,d)) → (a,(b,(c,d))) → (a,((b,c),d)) → (a,((c,b),d)) → (a,(c,(b,d))) → ((a,c),(b,d))
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ℝ × ℝ × ℝ × ℝ)
      volume volume := volume_preserving_prodAssoc
  have h2 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc.symm :
      ℝ × ℝ × ℝ ≃ᵐ (ℝ × ℝ) × ℝ)) (volume : Measure (ℝ × ℝ × ℝ × ℝ)) volume :=
    (MeasurePreserving.id _).prod volume_preserving_prodAssoc.symm
  have h3 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) id))
      (volume : Measure (ℝ × (ℝ × ℝ) × ℝ)) volume :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_swap.prod (MeasurePreserving.id _))
  have h4 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc :
      (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)) (volume : Measure (ℝ × (ℝ × ℝ) × ℝ)) volume :=
    (MeasurePreserving.id _).prod volume_preserving_prodAssoc
  have h5 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : ℝ × ℝ × ℝ × ℝ ≃ᵐ (ℝ × ℝ) × ℝ × ℝ)
      volume volume := volume_preserving_prodAssoc.symm
  have := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert this using 1
  funext p
  rfl

/-- The reordering preserves Lebesgue measure. -/
theorem measurePreserving_nbReorder : MeasurePreserving nbReorder volume volume := by
  -- (t, P) → (P, t) → (interchange P, t) → ((L, H), t) → (L, (H, t)) → (L, (t, H))
  have h1 : MeasurePreserving (Prod.swap : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)
      volume volume := Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (id : ℝ → ℝ))
      (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ)) volume :=
    measurePreserving_interchange.prod (MeasurePreserving.id _)
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) × ℝ) volume volume :=
    volume_preserving_prodAssoc
  have h4 : MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ)
      (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ))) (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ) × ℝ)) volume :=
    (MeasurePreserving.id _).prod Measure.measurePreserving_swap
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext p
  rfl

/-- For `t ∈ (0,1)` the constraints `λ − tη ∈ [0,1]`, `λ + (1 − t)η ∈ [0,1]` on the edge effect
are `η ∈ [−nbLo λ t, nbHi λ t]`. -/
theorem nb_slice_iff {l t η : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (l - t * η ∈ Icc (0 : ℝ) 1 ∧ l + (1 - t) * η ∈ Icc (0 : ℝ) 1) ↔
      η ∈ Icc (-nbLo l t) (nbHi l t) := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  simp only [mem_Icc, nbLo, nbHi]
  rw [neg_le, le_min_iff, le_min_iff, le_div_iff₀ ht1, le_div_iff₀ ht0, le_div_iff₀ ht1,
    le_div_iff₀ ht0]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The image of the cube under the moment map, as a set. -/
def nbImage : Set NBParam := nbMomentInv ⁻¹' nbBox

theorem measurableSet_nbImage : MeasurableSet nbImage :=
  measurableSet_nbBox.preimage measurable_nbMomentInv

/-- The slice of the image at fixed means `L ∈ (0,1)²`, in the coordinates `(t, (η₁, η₂))`. -/
def nbSlice (L : ℝ × ℝ) : Set (ℝ × (ℝ × ℝ)) := {q | nbReorderInv (L, q) ∈ nbImage}

theorem nbSlice_inter_Ioo (L : ℝ × ℝ) :
    nbSlice L ∩ {q | q.1 ∈ Ioo (0 : ℝ) 1} = nbRegion L.1 L.2 := by
  ext ⟨t, η₁, η₂⟩
  simp only [nbSlice, nbImage, nbReorderInv, nbMomentInv, nbBox, nbRegion, mem_inter_iff,
    mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc]
  constructor
  · rintro ⟨⟨-, ⟨h1, h2⟩, ⟨h3, h4⟩⟩, ht⟩
    exact ⟨ht, (nb_slice_iff ht).mp ⟨h1, h2⟩, (nb_slice_iff ht).mp ⟨h3, h4⟩⟩
  · rintro ⟨ht, h1, h2⟩
    exact ⟨⟨⟨ht.1.le, ht.2.le⟩, (nb_slice_iff ht).mpr h1, (nb_slice_iff ht).mpr h2⟩, ht⟩

theorem nbSlice_subset (L : ℝ × ℝ) : nbSlice L ⊆ {q | q.1 ∈ Icc (0 : ℝ) 1} := by
  rintro ⟨t, η₁, η₂⟩ h
  simp only [nbSlice, nbImage, nbReorderInv, nbMomentInv, nbBox, mem_ofPred_eq, mem_preimage,
    mem_prod] at h
  exact h.1

/-- The slices `t ∈ {0, 1}` are null. -/
theorem volume_boundary_slices :
    volume ({q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (0 : ℝ) 1} \ {q | q.1 ∈ Ioo (0 : ℝ) 1}) = 0 := by
  have hsub : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (0 : ℝ) 1} \ {q | q.1 ∈ Ioo (0 : ℝ) 1} ⊆
      ({0, 1} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    rintro ⟨t, η⟩ ⟨h1, h2⟩
    simp only [mem_ofPred_eq, mem_Icc] at h1
    simp only [mem_ofPred_eq, mem_Ioo, not_and, not_lt] at h2
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true]
    rcases eq_or_lt_of_le h1.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (le_antisymm h1.2 (h2 h))
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite _).measure_zero volume, zero_mul]

/-- The slice at interior means agrees with the region up to a null set. -/
theorem nbSlice_ae_eq (L : ℝ × ℝ) : nbSlice L =ᵐ[volume] nbRegion L.1 L.2 := by
  rw [← nbSlice_inter_Ioo]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩)
  · refine measure_mono_null ?_ volume_boundary_slices
    rintro q ⟨hq, hq'⟩
    exact ⟨nbSlice_subset L hq, fun h => hq' ⟨hq, h⟩⟩
  · rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty]

/-- ★★★ The pushforward of the uniform prior on the cube along the moment coordinates
`(λ₁, λ₂, μ)` has density `nbFibreDensity` on `(0,1)² × ℝ`. -/
theorem lintegral_nbBox_moments {Ψ : ℝ × ℝ × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ θ in nbBox, Ψ (nbMean₁ θ, nbMean₂ θ, nbCov θ) =
      ∫⁻ l in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∫⁻ z, Ψ (l.1, l.2, z) * nbFibreDensity l.1 l.2 z := by
  -- the integrand in the moment-map coordinates, and after reordering
  set F : NBParam → ℝ≥0∞ := fun ζ => Ψ (ζ.2.1.1, ζ.2.2.1, ζ.1 * (1 - ζ.1) * ζ.2.1.2 * ζ.2.2.2)
    with hFdef
  set G : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) → ℝ≥0∞ := fun ω =>
    (nbReorderInv ⁻¹' nbImage).indicator
      (fun ω => Ψ (ω.1.1, ω.1.2, ω.2.1 * (1 - ω.2.1) * ω.2.2.1 * ω.2.2.2)) ω with hGdef
  have hF : Measurable F := by
    refine hΨ.comp ?_
    fun_prop
  have hG : Measurable G := by
    refine Measurable.indicator (hΨ.comp (by fun_prop)) ?_
    exact measurableSet_nbImage.preimage measurable_nbReorderInv
  have hpre : MeasurableSet (nbReorderInv ⁻¹' nbImage) :=
    measurableSet_nbImage.preimage measurable_nbReorderInv
  calc ∫⁻ θ in nbBox, Ψ (nbMean₁ θ, nbMean₂ θ, nbCov θ)
      = ∫⁻ θ in nbBox, F (nbMomentMap θ) := rfl
    _ = ∫⁻ ζ in nbMomentMap '' nbBox, F ζ :=
        (measurePreserving_nbMomentMap.restrict_image_emb nbMomentEquiv.measurableEmbedding
          nbBox).lintegral_comp hF
    _ = ∫⁻ ζ, G (nbReorder ζ) := by
        rw [nbMomentMap_image_nbBox]
        change ∫⁻ ζ in nbImage, F ζ = _
        rw [← lintegral_indicator measurableSet_nbImage]
        rfl
    _ = ∫⁻ ω, G ω := measurePreserving_nbReorder.lintegral_comp hG
    _ = ∫⁻ L, ∫⁻ q, G (L, q) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hG.aemeasurable]
    _ = ∫⁻ L, (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1).indicator
          (fun L => ∫⁻ z, Ψ (L.1, L.2, z) * nbFibreDensity L.1 L.2 z) L := by
        refine lintegral_congr_ae ?_
        have hnull : volume ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \
            (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) = 0 := by
          have hsub : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ⊆
              (({0, 1} : Set ℝ) ×ˢ (univ : Set ℝ)) ∪ ((univ : Set ℝ) ×ˢ ({0, 1} : Set ℝ)) := by
            rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, h⟩
            simp only [mem_prod, mem_Ioo, not_and_or, not_lt] at h
            simp only [mem_Icc] at hx hy
            simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true,
              true_and]
            rcases h with (h | h) | (h | h)
            · exact Or.inl (Or.inl (le_antisymm h hx.1))
            · exact Or.inl (Or.inr (le_antisymm hx.2 h))
            · exact Or.inr (Or.inl (le_antisymm h hy.1))
            · exact Or.inr (Or.inr (le_antisymm hy.2 h))
          refine measure_mono_null hsub (measure_union_null ?_ ?_)
          · rw [Measure.volume_eq_prod, Measure.prod_prod,
              (Set.toFinite _).measure_zero volume, zero_mul]
          · rw [Measure.volume_eq_prod, Measure.prod_prod,
              (Set.toFinite ({0, 1} : Set ℝ)).measure_zero volume, mul_zero]
        have hae : ∀ᵐ L : ℝ × ℝ ∂volume,
            L ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∨ L ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
          rw [ae_iff]
          refine measure_mono_null ?_ hnull
          intro L hL
          simp only [mem_ofPred_eq, not_or, not_not] at hL
          exact ⟨hL.2, hL.1⟩
        filter_upwards [hae] with L hL
        have hGq : ∀ q, G (L, q) = (nbSlice L).indicator
            (fun q : ℝ × (ℝ × ℝ) => Ψ (L.1, L.2, q.1 * (1 - q.1) * q.2.1 * q.2.2)) q :=
          fun q => rfl
        simp_rw [hGq]
        rcases hL with hL | hL
        · rw [indicator_of_mem hL]
          have hsm : MeasurableSet (nbSlice L) :=
            measurableSet_nbImage.preimage (measurable_nbReorderInv.comp
              (measurable_const.prodMk measurable_id))
          have hΨL : Measurable fun z => Ψ (L.1, L.2, z) := hΨ.comp (by fun_prop)
          rw [lintegral_indicator hsm, Measure.restrict_congr_set (nbSlice_ae_eq L),
            lintegral_nbRegion hL.1.1 hL.1.2 hL.2.1 hL.2.2 hΨL]
        · rw [indicator_of_notMem
            (fun h => hL (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self h))]
          refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun q => ?_)
          rw [Pi.zero_apply]
          refine indicator_of_notMem (fun hq => hL ?_) _
          obtain ⟨t, η₁, η₂⟩ := q
          simp only [nbSlice, nbImage, nbReorderInv, nbMomentInv, nbBox, mem_ofPred_eq,
            mem_preimage, mem_prod, mem_Icc] at hq
          obtain ⟨⟨ht0, ht1⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩ := hq
          simp only [mem_prod, mem_Icc]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
    _ = _ := lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) _

end Grammar
