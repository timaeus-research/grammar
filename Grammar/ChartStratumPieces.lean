/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordPlaneStratum
import Grammar.CentredChart

/-!
# The coordinate-size stratification of a chart (resolved-space programme, modules 4–5)

In a chart with divisor coordinates `D` (the coordinates with positive phase exponent), a point
`y` is assigned to the stratum `I(y) = {j ∈ D : |y_j| < ε}`. This file provides:

* the **measurable pieces** `sizePiece D ε I = {y : ∀ j ∈ D, |y_j| < ε ↔ j ∈ I}` — measurable,
  pairwise disjoint, exhausting `ℝ^d` over `I ⊆ D` (`measurableSet_sizePiece`,
  `disjoint_sizePiece`, `iUnion_sizePiece`), so that any weighted integral is the finite sum of
  its piece integrals (`integral_eq_sum_sizePiece`);
* for a nonempty `I ⊆ D`, the **coordinate splitting** `stratumSplit I` with normal coordinates
  `I` (from `splittingOf`), the coordinate plane `P_I` and its foot (`planeFoot_apply_of_mem`,
  `planeFoot_apply_of_notMem`), and the **containment of the piece in the `ε`-tube of `P_I`**
  (`sizePiece_subset_tube`), fibre-saturated: on the tube, `y ∈ sizePiece D ε I` iff the foot
  satisfies `|v_j| ≥ ε` for the other divisor coordinates (`mem_sizePiece_iff_of_mem_tube`);
* **the per chart–stratum formula** (`integral_sizePiece_eq_integral_condContraction`): with the
  chart weight `w` (cover weight, Jacobian unit, prior, phase) and the paper's fibre power-series
  hypotheses, `∫_{piece I} w F dy = ∫_{piece I} w · (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(foot_I y) dy`;
* **the stratification of a weighted chart integral** (`integral_eq_sum_condContraction_pieces`):
  `∫ w F = ∑_{∅ ≠ I ⊆ D} ∫_{piece I} w · cs_I(F)∘foot_I + ∫_{piece ∅} w F`, exact, the last term
  being the integral away from the divisor.

Non-claims: the pieces are measurable, not open, and depend on `ε`; the `I = ∅` term is not
estimated (exponentially small under a positive lower bound of the phase); the radius/domination
hypotheses are the paper's.
-/

open scoped Manifold ContDiff Matrix ENNReal
open Set Function StrucDual.Geometry TopologicalSpace MeasureTheory Filter

namespace Grammar

section Pieces

variable {d : ℕ} (D : Finset (Fin d)) (ε : ℝ)

/-- **The coordinate-size piece** of stratum `I`: the divisor coordinates smaller than `ε` are
exactly those in `I`. -/
def sizePiece (I : Finset (Fin d)) : Set (Fin d → ℝ) :=
  {y | ∀ j ∈ D, (|y j| < ε ↔ j ∈ I)}

theorem measurableSet_sizePiece (I : Finset (Fin d)) : MeasurableSet (sizePiece D ε I) := by
  classical
  have h : sizePiece D ε I = ⋂ j ∈ D,
      (if j ∈ I then {y : Fin d → ℝ | |y j| < ε} else {y : Fin d → ℝ | |y j| < ε}ᶜ) := by
    ext y
    simp only [sizePiece, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall₂_congr fun j _ => ?_
    by_cases hj : j ∈ I
    · simp [hj]
    · simp [hj]
  rw [h]
  refine Finset.measurableSet_biInter D fun j _ => ?_
  have hm : MeasurableSet {y : Fin d → ℝ | |y j| < ε} :=
    measurableSet_lt (continuous_abs.comp (continuous_apply j)).measurable measurable_const
  split_ifs
  · exact hm
  · exact hm.compl

theorem disjoint_sizePiece {I I' : Finset (Fin d)} (hI : I ⊆ D) (hI' : I' ⊆ D) (h : I ≠ I') :
    Disjoint (sizePiece D ε I) (sizePiece D ε I') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  apply h
  ext j
  by_cases hj : j ∈ D
  · rw [← hy j hj, ← hy' j hj]
  · exact ⟨fun h => absurd (hI h) hj, fun h => absurd (hI' h) hj⟩

theorem mem_sizePiece_filter (y : Fin d → ℝ) : y ∈ sizePiece D ε (D.filter fun j => |y j| < ε) := by
  intro j hj
  simp [Finset.mem_filter, hj]

theorem iUnion_sizePiece : ⋃ I ∈ D.powerset, sizePiece D ε I = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨_, Finset.mem_powerset.2 (Finset.filter_subset _
    _),
    mem_sizePiece_filter D ε y⟩

/-- **A weighted integral is the finite sum of its piece integrals.** -/
theorem integral_eq_sum_sizePiece {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) :
    ∫ y, f y = ∑ I ∈ D.powerset, ∫ y in sizePiece D ε I, f y := by
  classical
  have hcover : (⋃ I : ↥D.powerset, sizePiece D ε I.1) = univ := by
    rw [← iUnion_sizePiece D ε]
    ext y
    simp only [mem_iUnion, Subtype.exists, exists_prop]
  have hdisj : Pairwise (Disjoint on fun I : ↥D.powerset => sizePiece D ε I.1) := by
    intro I I' hII'
    exact disjoint_sizePiece D ε (Finset.mem_powerset.1 I.2) (Finset.mem_powerset.1 I'.2)
      fun h => hII' (Subtype.ext h)
  have h := integral_iUnion (μ := volume) (fun I : ↥D.powerset => measurableSet_sizePiece D ε I.1)
    hdisj (f := f) (by rw [hcover]; exact hf.integrableOn)
  rw [hcover, Measure.restrict_univ] at h
  rw [h, tsum_fintype]
  exact (Finset.sum_coe_sort D.powerset fun I => ∫ y in sizePiece D ε I, f y)

end Pieces

section Split

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty)

theorem card_compl_eq : Fintype.card {j : Fin d // j ∉ I} = d - I.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

include hne in
theorem card_eq_succ : Fintype.card ↥I = I.card - 1 + 1 := by
  rw [Fintype.card_coe, Nat.sub_add_cancel (Finset.card_pos.2 hne)]

/-- **The coordinate splitting of stratum `I`**: normal coordinates `I`, tangential `Iᶜ`. -/
noncomputable def stratumSplit : Fin d ≃ Fin (d - I.card) ⊕ Fin (I.card - 1 + 1) :=
  (splittingOf I (card_compl_eq I) (card_eq_succ I hne)).symm

theorem stratumSplit_symm_inr_mem (j : Fin (I.card - 1 + 1)) :
    (stratumSplit I hne).symm (Sum.inr j) ∈ I :=
  nIdx_splittingOf_mem I (card_compl_eq I) (card_eq_succ I hne) j

theorem stratumSplit_symm_inl_notMem (i : Fin (d - I.card)) :
    (stratumSplit I hne).symm (Sum.inl i) ∉ I :=
  tIdx_splittingOf_notMem I (card_compl_eq I) (card_eq_succ I hne) i

theorem exists_inr_of_mem {k : Fin d} (hk : k ∈ I) :
    ∃ j, k = (stratumSplit I hne).symm (Sum.inr j) := by
  rcases h : stratumSplit I hne k with i | j
  · exfalso
    have : k = (stratumSplit I hne).symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
    exact stratumSplit_symm_inl_notMem I hne i (this ▸ hk)
  · exact ⟨j, by rw [← h, Equiv.symm_apply_apply]⟩

/-- The foot of `P_I` zeroes the coordinates in `I` and keeps the others. -/
theorem planeFoot_apply_of_mem {k : Fin d} (hk : k ∈ I) (y : Fin d → ℝ) :
    planeFoot (stratumSplit I hne) y k = 0 := by
  obtain ⟨j, rfl⟩ := exists_inr_of_mem I hne hk
  rw [planeFoot_apply, coordCLE_apply_inr]
  rfl

theorem planeFoot_apply_of_notMem {k : Fin d} (hk : k ∉ I) (y : Fin d → ℝ) :
    planeFoot (stratumSplit I hne) y k = y k := by
  rcases h : stratumSplit I hne k with i | j
  · have hk' : k = (stratumSplit I hne).symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
    rw [hk', planeFoot_apply, coordCLE_apply_inl, coordCLE_symm_apply_fst]
  · exfalso
    have : k = (stratumSplit I hne).symm (Sum.inr j) := by rw [← h, Equiv.symm_apply_apply]
    exact hk (this ▸ stratumSplit_symm_inr_mem I hne j)

theorem zero_mem_coordPlane : (0 : Fin d → ℝ) ∈ coordPlane (stratumSplit I hne) := fun _ => rfl

/-- The tube condition of `P_I` is the size condition on the coordinates in `I`. -/
theorem norm_sub_planeFoot_lt_iff {ε : ℝ} (hε : 0 < ε) (y : Fin d → ℝ) :
    ‖y - planeFoot (stratumSplit I hne) y‖ < ε ↔ ∀ k ∈ I, |y k| < ε := by
  rw [sub_planeFoot, norm_coordCLE, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _),
    pi_norm_lt_iff hε]
  constructor
  · intro h k hk
    obtain ⟨j, rfl⟩ := exists_inr_of_mem I hne hk
    have := h j
    rwa [coordCLE_symm_apply_snd, Real.norm_eq_abs] at this
  · intro h j
    rw [coordCLE_symm_apply_snd, Real.norm_eq_abs]
    exact h _ (stratumSplit_symm_inr_mem I hne j)

end Split

section Containment

variable {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hI : I ⊆ D)
  (hne : I.Nonempty)

include hI in
/-- **The piece lies in the `ε`-tube of its plane.** -/
theorem sizePiece_subset_tube :
    sizePiece D ε I ⊆ (coordPlaneTube (stratumSplit I hne) ε hε).U := by
  intro y hy
  change ‖y - planeFoot (stratumSplit I hne) y‖ < ε
  rw [norm_sub_planeFoot_lt_iff I hne hε]
  intro k hk
  exact (hy k (hI hk)).2 hk

/-- The complementary size condition on the foot. -/
def footCondition : Set (Fin d → ℝ) := {v | ∀ j ∈ D, j ∉ I → ¬ |v j| < ε}

/-- **The piece is fibre-saturated on the tube**: on the `ε`-tube of `P_I`, membership in the piece
is a condition on the foot. -/
theorem mem_sizePiece_iff_of_mem_tube {y : Fin d → ℝ}
    (hy : y ∈ (coordPlaneTube (stratumSplit I hne) ε hε).U) :
    y ∈ sizePiece D ε I ↔ planeFoot (stratumSplit I hne) y ∈ footCondition D (ε := ε) I := by
  have hsmall : ∀ k ∈ I, |y k| < ε := (norm_sub_planeFoot_lt_iff I hne hε y).1 hy
  constructor
  · intro h j hj hjI
    rw [planeFoot_apply_of_notMem I hne hjI]
    exact fun hlt => hjI ((h j hj).1 hlt)
  · intro h j hj
    constructor
    · intro hlt
      by_contra hjI
      exact h j hj hjI (by rwa [planeFoot_apply_of_notMem I hne hjI])
    · exact hsmall j

end Containment

section Formula

variable {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hI : I ⊆ D)
  (hne : I.Nonempty) (wt : TubeWeight d)

/-- The tube and chart data of stratum `I`. -/
noncomputable abbrev stratumTube :=
  (coordPlaneTube (stratumSplit I hne) ε hε).toNormalTubularChart

noncomputable abbrev stratumChart :=
  coordPlaneChart (stratumSplit I hne) (zero_mem_coordPlane I hne)

include hI in
/-- **The per chart–stratum formula**: on the piece of stratum `I`, with the chart weight in the
fibre measures and the paper's fibre power-series hypotheses,
`∫_{piece I} w F dy = ∫_{piece I} w · (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(foot_I y) dy`. -/
theorem integral_sizePiece_eq_integral_condContraction {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn (fun y => wt.w y * F y) (sizePiece D ε I))
    {q : (Fin (d - (I.card - 1 + 1)) → ℝ) → FormalMultilinearSeries ℝ (Fin (I.card - 1 + 1) → ℝ) ℝ}
    {Rad : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ≥0∞}
    (hq : ∀ z, HasFPowerSeriesOnBall (fun n => F (planeSplit (stratumSplit I hne) (z, n))) (q z) 0
      (Rad z))
    (hη : ∀ z, ∀ᵐ n ∂fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
      wt)
      z, n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad z))
    (hdom : ∀ z, Summable fun k => ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
      (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt) z) :
    ∫ y in sizePiece D ε I, wt.w y * F y =
      ∫ y in sizePiece D ε I, wt.w y * condContractionSeries (stratumTube hε I hne)
        (stratumChart I hne) wt F (planeFoot (stratumSplit I hne) y) := by
  have hmeas := measurableSet_sizePiece D ε I
  have hsub : sizePiece D ε I ⊆ {y | ‖y - planeFoot (stratumSplit I hne) y‖ < ε} :=
    sizePiece_subset_tube D hε I hI hne
  set wt' := wt.restrict (sizePiece D ε I) hmeas with hwt'
  have hsP : ∀ y ∈ (stratumTube hε I hne).U,
      y ∈ sizePiece D ε I ↔ (stratumTube hε I hne).proj y ∈ footCondition D (ε := ε) I :=
    fun y hy => mem_sizePiece_iff_of_mem_tube D hε I hne hy
  have hfib : ∀ z, fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt')
      z = fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt) z ∨
      fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt') z = 0 := by
    intro z
    by_cases hz : (stratumChart I hne).emb z ∈ footCondition D (ε := ε) I
    · exact Or.inl (fibreMeasure_restrict_of_mem _ _ wt _ hmeas _ hsP hz)
    · exact Or.inr (fibreMeasure_restrict_of_notMem _ _ wt _ hmeas _ hsP hz)
  have hη' : ∀ z, ∀ᵐ n ∂fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
      wt') z, n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad z) := by
    intro z
    rcases hfib z with h | h
    · rw [h]; exact hη z
    · rw [h, ae_zero]; exact Filter.eventually_bot
  have hdom' : ∀ z, Summable fun k => ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
      (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt') z := by
    intro z
    rcases hfib z with h | h
    · rw [h]; exact hdom z
    · rw [h]; simp only [integral_zero_measure, mul_zero]; exact summable_zero
  have hF' : IntegrableOn (fun y => wt'.w y * F y)
      {y | ‖y - planeFoot (stratumSplit I hne) y‖ < ε} := by
    refine (((integrable_indicator_iff hmeas).2 hF).integrableOn).congr_fun (fun y _ => ?_)
      (coordPlaneTube (stratumSplit I hne) ε hε).isOpen_U.measurableSet
    rw [hwt', TubeWeight.restrict_w]
    exact indicator_mul_left _ _ _
  have h := integral_coordPlaneTube_eq_integral_condContraction (stratumSplit I hne)
    (zero_mem_coordPlane I hne) ε hε wt' hF' hq hη' hdom'
  have h1 : ∫ y in sizePiece D ε I, wt.w y * F y =
      ∫ y in {y | ‖y - planeFoot (stratumSplit I hne) y‖ < ε}, wt'.w y * F y := by
    have : ∀ y, wt'.w y * F y = (sizePiece D ε I).indicator (fun y => wt.w y * F y) y :=
      fun y => by rw [hwt', TubeWeight.restrict_w, indicator_mul_left]
    simp_rw [this]
    rw [setIntegral_indicator hmeas, inter_eq_right.2 hsub]
  have h2 : ∫ y in {y | ‖y - planeFoot (stratumSplit I hne) y‖ < ε}, wt'.w y *
      condContractionSeries (stratumTube hε I hne) (stratumChart I hne) wt' F
        (planeFoot (stratumSplit I hne) y) =
      ∫ y in sizePiece D ε I, wt.w y * condContractionSeries (stratumTube hε I hne)
        (stratumChart I hne) wt F (planeFoot (stratumSplit I hne) y) := by
    have : ∀ y, wt'.w y * condContractionSeries (stratumTube hε I hne) (stratumChart I hne) wt' F
        (planeFoot (stratumSplit I hne) y) = (sizePiece D ε I).indicator
        (fun y => wt.w y * condContractionSeries (stratumTube hε I hne) (stratumChart I hne) wt' F
          (planeFoot (stratumSplit I hne) y)) y :=
      fun y => by rw [hwt', TubeWeight.restrict_w, indicator_mul_left]
    simp_rw [this]
    rw [setIntegral_indicator hmeas, inter_eq_right.2 hsub]
    refine setIntegral_congr_fun hmeas fun y hy => ?_
    rw [hwt', condContractionSeries_restrict _ (stratumChart I hne) wt _ hmeas _ hsP F
      (show planeFoot (stratumSplit I hne) y ∈ footCondition D (ε := ε) I from
        (hsP y (hsub hy)).1 hy)]
  rw [h1, h, h2]

end Formula

section Stratification

variable {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (wt : TubeWeight d)

/-- **The stratification of a weighted chart integral**: exactly, over the nonempty strata `I ⊆ D`
plus the piece away from the divisor (each nonempty-stratum term is then expanded by
`integral_sizePiece_eq_integral_condContraction`). -/
theorem integral_eq_sum_pieces_nonempty_add {F : (Fin d → ℝ) → ℝ}
    (hF : Integrable (fun y => wt.w y * F y)) :
    ∫ y, wt.w y * F y =
      (∑ I ∈ D.powerset.filter (fun I => I.Nonempty), ∫ y in sizePiece D ε I, wt.w y * F y) +
        ∫ y in sizePiece D ε ∅, wt.w y * F y := by
  classical
  rw [integral_eq_sum_sizePiece D ε hF,
    ← Finset.sum_filter_add_sum_filter_not D.powerset (fun I => I.Nonempty)]
  have h0 : ∑ I ∈ D.powerset.filter (fun I => ¬ I.Nonempty),
      (∫ y in sizePiece D ε I, wt.w y * F y) = ∫ y in sizePiece D ε ∅, wt.w y * F y :=
    Finset.sum_eq_single (∅ : Finset (Fin d))
      (fun I hI hne => absurd (Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hI).2) hne)
      (fun h => absurd (Finset.mem_filter.2 ⟨Finset.empty_mem_powerset D,
        Finset.not_nonempty_empty⟩) h)
  rw [h0]

end Stratification

end Grammar
