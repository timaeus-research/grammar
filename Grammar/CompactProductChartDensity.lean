/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ScalarChartNormalForm

/-!
# Compact bases and product-domain allocations for adapted piece densities

Unit 2 of consult #77 (`tide-log/gpt6_bigpicture_v77.md`): the geometric interface that the bridge
CCXXXIII needs — a COMPACT base. The fibre-constant constructor of CCXXVIII has as base the whole
foot-condition set, which is closed (`isClosed_footCondition`) but unbounded; compactness of the
chart domain does not make it compact. Two devices repair this:

* **base restriction** (`AdaptedProductDensity.restrictBase`): an adapted density whose represented
  density vanishes a.e. off the fibres over a measurable set `T` is again adapted with base
  `base ∩ T` (same weight, box and amplitude);
* **the tangential carrier** of the compact chart domain (`tangentialCarrier`,
  `isCompact_tangentialCarrier`): the static chart density vanishes off the fibres over it
  (`boltzmannChartDensity_eq_zero_of_notMem_carrier`), so restricting the fibre-constant density
  to the carrier gives an adapted density with a **compact base**
  (`compactFibreConstantDensity`, `compactFibreConstantDensity_base_compact`).

And the fibre-constant hypothesis itself is discharged by **product geometry**
(`fibreConstant_of_product`): if on the piece the chart domain is fibre-saturated
(`y ∈ dom ↔ foot y ∈ T'`) and the cover weight is fibre-constant (`ρ_i(Φ_i y) = ρ_T(foot y)`), the
allocation `1_dom·(ρ_i∘Φ_i)` equals `(1_{T'} ρ_T) ∘ foot` on the piece — pointwise, hence a.e.

Non-claims: product geometry is a HYPOTHESIS (a compact domain and one chart with `ρ ≡ 1` do not
by themselves give fibre constancy — the domain indicator can still vary along fibres); the
normal-form identities of CCXXXIII are supplied separately (CCXXXVI).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### The foot condition is closed -/

theorem isClosed_footCondition {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (I : Finset (Fin d)) :
    IsClosed (footCondition D (ε := ε) I) := by
  have h : footCondition D (ε := ε) I =
      ⋂ j ∈ (D : Set (Fin d)), {v : Fin d → ℝ | j ∉ I → ε ≤ |v j|} := by
    ext v
    simp only [footCondition, mem_ofPred_eq, mem_iInter, Finset.mem_coe, not_lt]
  rw [h]
  refine isClosed_biInter fun j _ => ?_
  by_cases hj : j ∈ I
  · simp only [hj, not_true_eq_false, false_implies, ofPred_true]
    exact isClosed_univ
  · simp only [hj, not_false_eq_true, true_implies]
    exact isClosed_le continuous_const (continuous_abs.comp (continuous_apply j))

/-! ### Base restriction -/

section Restrict

variable {d m r : ℕ} {τ : Fin d ≃ Fin m ⊕ Fin r} {w : (Fin d → ℝ) → ℝ} {piece : Set (Fin d → ℝ)}

/-- **Base restriction**: if the represented density vanishes a.e. off the fibres over `T`, the
adapted density with base `base ∩ T` represents the same density. -/
def AdaptedProductDensity.restrictBase (Ad : AdaptedProductDensity τ w piece)
    (T : Set (Fin (d - r) → ℝ)) (hT : MeasurableSet T)
    (hw : ∀ q : (Fin (d - r) → ℝ) × (Fin r → ℝ), q.1 ∉ T → piece.indicator w (planeSplit τ q) = 0) :
    AdaptedProductDensity τ w piece where
  base := Ad.base ∩ T
  measurableSet_base := Ad.measurableSet_base.inter hT
  normalBox := Ad.normalBox
  measurableSet_normalBox := Ad.measurableSet_normalBox
  beta := Ad.beta
  amp := Ad.amp
  density_ae := by
    refine Ad.density_ae.mono fun q hq => ?_
    beta_reduce at hq ⊢
    by_cases hqT : q.1 ∈ T
    · have : (Ad.base ∩ T).indicator Ad.beta q.1 = Ad.base.indicator Ad.beta q.1 := by
        by_cases hb : q.1 ∈ Ad.base
        · rw [indicator_of_mem hb, indicator_of_mem (Set.mem_inter hb hqT)]
        · rw [indicator_of_notMem hb,
            indicator_of_notMem fun h : q.1 ∈ Ad.base ∩ T => hb (Set.mem_of_mem_inter_left h)]
      rw [hq, this]
    · rw [indicator_of_notMem fun h : q.1 ∈ Ad.base ∩ T => hqT h.2, zero_mul, hw q hqT]

@[simp] theorem AdaptedProductDensity.restrictBase_base (Ad : AdaptedProductDensity τ w piece)
    (T : Set (Fin (d - r) → ℝ)) (hT : MeasurableSet T) (hw) :
    (Ad.restrictBase T hT hw).base = Ad.base ∩ T := rfl

@[simp] theorem AdaptedProductDensity.restrictBase_beta (Ad : AdaptedProductDensity τ w piece)
    (T : Set (Fin (d - r) → ℝ)) (hT : MeasurableSet T) (hw) :
    (Ad.restrictBase T hT hw).beta = Ad.beta := rfl

@[simp] theorem AdaptedProductDensity.restrictBase_amp (Ad : AdaptedProductDensity τ w piece)
    (T : Set (Fin (d - r) → ℝ)) (hT : MeasurableSet T) (hw) :
    (Ad.restrictBase T hT hw).amp = Ad.amp := rfl

@[simp] theorem AdaptedProductDensity.restrictBase_normalBox (Ad : AdaptedProductDensity τ w piece)
    (T : Set (Fin (d - r) → ℝ)) (hT : MeasurableSet T) (hw) :
    (Ad.restrictBase T hT hw).normalBox = Ad.normalBox := rfl

end Restrict

/-! ### The tangential carrier of a compact domain -/

section Carrier

variable {d m r : ℕ} (τ : Fin d ≃ Fin m ⊕ Fin r)

/-- The tangential projection of a set: the `z`-coordinates of its points. -/
def tangentialCarrier (C : Set (Fin d → ℝ)) : Set (Fin (d - r) → ℝ) :=
  (fun y => ((planeSplit τ).symm y).1) '' C

theorem isCompact_tangentialCarrier {C : Set (Fin d → ℝ)} (hC : IsCompact C) :
    IsCompact (tangentialCarrier τ C) :=
  hC.image (continuous_fst.comp (planeSplit τ).symm.continuous)

theorem mem_tangentialCarrier_of_mem {C : Set (Fin d → ℝ)} {z : Fin (d - r) → ℝ} {n : Fin r → ℝ}
    (hy : planeSplit τ (z, n) ∈ C) : z ∈ tangentialCarrier τ C :=
  ⟨planeSplit τ (z, n), hy, by simp⟩

theorem measurableSet_tangentialCarrier {C : Set (Fin d → ℝ)} (hC : IsCompact C) :
    MeasurableSet (tangentialCarrier τ C) :=
  (isCompact_tangentialCarrier τ hC).isClosed.measurableSet

end Carrier

/-! ### The compact-base fibre-constant density of a chart piece -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hI : I ⊆ D i)
  (hne : I.Nonempty) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)

/-- The static chart density vanishes off the fibres over the tangential carrier of the domain. -/
theorem boltzmannChartDensity_eq_zero_of_notMem_carrier
    (q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ))
    (hq : q.1 ∉ tangentialCarrier (stratumSplit I hne) (R.chart i).dom) :
    (sizePiece (D i) ε I).indicator (R.boltzmannChartDensity i 0 K p)
      (planeSplit (stratumSplit I hne) q) = 0 := by
  rw [Set.indicator_apply_eq_zero (f := R.boltzmannChartDensity i 0 K p)]
  intro _
  unfold boltzmannChartDensity
  apply Set.indicator_of_notMem
  intro hdom
  apply hq
  obtain ⟨z, n⟩ := q
  exact mem_tangentialCarrier_of_mem _ hdom

include hε hI in
/-- **The compact-base fibre-constant density**: the fibre-constant adapted density of CCXXVIII
restricted to the tangential carrier of the chart domain. -/
noncomputable def compactFibreConstantDensity (β : (Fin d → ℝ) → ℝ)
    (hfc : (fun y => (sizePiece (D i) ε I).indicator (R.allocation i) y) =ᵐ[volume]
      fun y => (sizePiece (D i) ε I).indicator (fun y => β (planeFoot (stratumSplit I hne) y)) y) :
    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I) :=
  (R.adaptedProductDensity_of_fibreConstant i D hε I hI hne K p β hfc).restrictBase
    (tangentialCarrier (stratumSplit I hne) (R.chart i).dom)
    (measurableSet_tangentialCarrier _ (R.chart i).dom_compact)
    (fun q hq => R.boltzmannChartDensity_eq_zero_of_notMem_carrier i D I hne K p q hq)

include hε hI in
/-- Its base is compact. -/
theorem compactFibreConstantDensity_base_compact (β : (Fin d → ℝ) → ℝ) (hfc) :
    IsCompact (R.compactFibreConstantDensity i D hε I hI hne K p β hfc).base := by
  unfold compactFibreConstantDensity
  rw [AdaptedProductDensity.restrictBase_base]
  refine IsCompact.inter_left (isCompact_tangentialCarrier _ (R.chart i).dom_compact) ?_
  exact (isClosed_footCondition (D i) I).preimage
    ((planeSplit (stratumSplit I hne)).continuous.comp (continuous_id.prodMk continuous_const))

include hε hI in
theorem compactFibreConstantDensity_normalBox (β : (Fin d → ℝ) → ℝ) (hfc) :
    (R.compactFibreConstantDensity i D hε I hI hne K p β hfc).normalBox = Metric.ball 0 ε := rfl

include hε hI in
theorem compactFibreConstantDensity_beta (β : (Fin d → ℝ) → ℝ) (hfc) :
    (R.compactFibreConstantDensity i D hε I hI hne K p β hfc).beta =
      fun z => β (planeSplit (stratumSplit I hne) (z, 0)) := rfl

include hε hI in
theorem compactFibreConstantDensity_amp (β : (Fin d → ℝ) → ℝ) (hfc) :
    (R.compactFibreConstantDensity i D hε I hI hne K p β hfc).amp = fun z n =>
      (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
        p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) := rfl

/-! ### Product geometry gives fibre constancy -/

/-- **Fibre constancy from product geometry**: if on the piece the chart domain is fibre-saturated
(`y ∈ dom ↔ foot y ∈ T'`) and the cover weight is fibre-constant (`ρ_i(Φ_i y) = ρ_T(foot y)` on
`piece ∩ dom`), the allocation equals `(1_{T'} ρ_T) ∘ foot` on the piece. -/
theorem fibreConstant_of_product (T' : Set (Fin d → ℝ)) (ρT : (Fin d → ℝ) → ℝ)
    (hdom : ∀ y ∈ sizePiece (D i) ε I,
      y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
    (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
      R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y)) :
    (fun y => (sizePiece (D i) ε I).indicator (R.allocation i) y) =ᵐ[volume]
      fun y => (sizePiece (D i) ε I).indicator
        (fun y => T'.indicator ρT (planeFoot (stratumSplit I hne) y)) y := by
  refine Eventually.of_forall fun y => ?_
  beta_reduce
  by_cases hy : y ∈ sizePiece (D i) ε I
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    unfold allocation
    by_cases hdom' : y ∈ (R.chart i).dom
    · rw [indicator_of_mem hdom', indicator_of_mem ((hdom y hy).1 hdom'), hρ y hy hdom']
    · rw [indicator_of_notMem hdom', indicator_of_notMem fun h => hdom' ((hdom y hy).2 h)]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

end ResolutionCover

end Grammar
