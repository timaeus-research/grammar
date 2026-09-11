/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LogRatioSymmetricMoments

/-!
# Product chart geometry and the hypothesis package for the end-to-end theorem

Unit 1 of consult #78 (`tide-log/gpt6_bigpicture_v78.md`): the geometry of a **centred product
chart** — a chart domain `productDom J T b = {y | P_J y ∈ T ∧ ∀ j ∈ J, |y_j| ≤ b}`, with `P_J`
the zeroing of the active divisor coordinates `J`, `T` a compact set of inactive vectors and `b` the
normal radius — and the lemmas that discharge, uniformly in the stratum `I ⊆ J`, the
product-geometry
hypotheses of the piece constructor CCXXXVIII:

* the foot of stratum `I` is the zeroing `P_I` (`planeFoot_eq_zeroOn`), `P_J ∘ P_I = P_J`
  (`zeroOn_zeroOn`), and `P_I` maps the domain to itself (`zeroOn_mem_productDom`);
* the domain is compact (`isCompact_productDom`);
* **the foot set** `T'_I = {x | P_J x ∈ T ∧ x_I = 0 ∧ |x_j| ≤ b (j ∈ J∖I)}` is closed
  (`isClosed_footSet`) and, for `ε ≤ b`, the domain is **fibre-saturated on the piece**:
  `y ∈ dom ↔ foot_I y ∈ T'_I` for `y ∈ sizePiece J ε I` (`mem_productDom_iff_foot_mem_footSet`);
* a unit independent of ALL active coordinates is independent of the normal coordinates of every
  stratum (`unit_indep_piece`), and a cover weight factoring through `P_J` is fibre-constant on
  every piece (`weight_factor_piece`);
* a nonempty `T` supplies a point of the domain vanishing on every stratum (`exists_zeroPoint`).

The **hypothesis package** `ProductMonomialChart R i K` bundles a monomial chart in product form
with a normal-independent unit and a cover weight factoring through the inactive coordinates. The
weight factorisation is a FIELD: it is determined by the cover images and is not implied by the
product shape of a single domain (overlaps can make it depend on active coordinates).

Non-claims: no atlas is built here (unit 2); the conventions: a cell's asymptotic pair is
`(lam, mult − 1)` — `mult` is the number of minimisers, not the log degree.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

section Zero

variable {d : ℕ} (J : Finset (Fin d))

/-- Zeroing the coordinates in `J`. -/
def zeroOn (y : Fin d → ℝ) : Fin d → ℝ := fun j => if j ∈ J then 0 else y j

theorem zeroOn_apply_of_mem {j : Fin d} (hj : j ∈ J) (y : Fin d → ℝ) : zeroOn J y j = 0 :=
  if_pos hj

theorem zeroOn_apply_of_notMem {j : Fin d} (hj : j ∉ J) (y : Fin d → ℝ) : zeroOn J y j = y j :=
  if_neg hj

theorem continuous_zeroOn : Continuous (zeroOn J) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j ∈ J
  · simp only [zeroOn, hj, if_true]
    exact continuous_const
  · simp only [zeroOn, hj, if_false]
    exact continuous_apply j

theorem zeroOn_zeroOn {I : Finset (Fin d)} (hIJ : I ⊆ J) (y : Fin d → ℝ) :
    zeroOn J (zeroOn I y) = zeroOn J y := by
  funext j
  by_cases hj : j ∈ J
  · rw [zeroOn_apply_of_mem J hj, zeroOn_apply_of_mem J hj]
  · rw [zeroOn_apply_of_notMem J hj, zeroOn_apply_of_notMem J hj,
      zeroOn_apply_of_notMem I fun h => hj (hIJ h)]

theorem zeroOn_of_forall_eq_zero {y : Fin d → ℝ} (hy : ∀ j ∈ J, y j = 0) : zeroOn J y = y := by
  funext j
  by_cases hj : j ∈ J
  · rw [zeroOn_apply_of_mem J hj, hy j hj]
  · rw [zeroOn_apply_of_notMem J hj]

/-- The foot of stratum `I` is the zeroing of the coordinates in `I`. -/
theorem planeFoot_eq_zeroOn (I : Finset (Fin d)) (hne : I.Nonempty) (y : Fin d → ℝ) :
    planeFoot (stratumSplit I hne) y = zeroOn I y := by
  funext k
  by_cases hk : k ∈ I
  · rw [planeFoot_apply_of_mem I hne hk, zeroOn_apply_of_mem I hk]
  · rw [planeFoot_apply_of_notMem I hne hk, zeroOn_apply_of_notMem I hk]

end Zero

/-! ### The centred product domain -/

section ProductDom

variable {d : ℕ} (J : Finset (Fin d)) (T : Set (Fin d → ℝ)) (b : ℝ)

/-- **The centred product domain** `{y | P_J y ∈ T ∧ ∀ j ∈ J, |y_j| ≤ b}`. -/
def productDom : Set (Fin d → ℝ) := {y | zeroOn J y ∈ T ∧ ∀ j ∈ J, |y j| ≤ b}

theorem productDom_eq :
    productDom J T b = zeroOn J ⁻¹' T ∩ ⋂ j ∈ (J : Set (Fin d)), {y : Fin d → ℝ | |y j| ≤ b} := by
  ext y
  simp only [productDom, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, Finset.mem_coe]

theorem isClosed_productDom (hT : IsClosed T) : IsClosed (productDom J T b) := by
  rw [productDom_eq]
  refine (hT.preimage (continuous_zeroOn J)).inter (isClosed_biInter fun j _ => ?_)
  exact isClosed_le (continuous_abs.comp (continuous_apply j)) continuous_const

theorem isCompact_productDom (hT : IsCompact T) (hb : 0 ≤ b) : IsCompact (productDom J T b) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_productDom J T b hT.isClosed) ?_
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hT.isBounded
  refine isBounded_iff_forall_norm_le.2 ⟨max C b, fun y hy => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_right hb)).2 fun j => ?_
  by_cases hj : j ∈ J
  · rw [Real.norm_eq_abs]
    exact (hy.2 j hj).trans (le_max_right _ _)
  · have h1 : ‖zeroOn J y j‖ ≤ ‖zeroOn J y‖ := norm_le_pi_norm _ j
    rw [zeroOn_apply_of_notMem J hj] at h1
    exact h1.trans ((hC _ hy.1).trans (le_max_left _ _))

theorem zeroOn_mem_productDom {y : Fin d → ℝ} (hy : y ∈ productDom J T b) {I : Finset (Fin d)}
    (hIJ : I ⊆ J) : zeroOn I y ∈ productDom J T b := by
  refine ⟨by rw [zeroOn_zeroOn J hIJ]; exact hy.1, fun j hj => ?_⟩
  by_cases hjI : j ∈ I
  · rw [zeroOn_apply_of_mem I hjI, abs_zero]
    exact (abs_nonneg _).trans (hy.2 j hj)
  · rw [zeroOn_apply_of_notMem I hjI]
    exact hy.2 j hj

/-- **The foot set of stratum `I`**: `P_J x ∈ T`, `x_I = 0`, `|x_j| ≤ b` on `J ∖ I`. -/
def footSet (I : Finset (Fin d)) : Set (Fin d → ℝ) :=
  {x | zeroOn J x ∈ T ∧ (∀ j ∈ I, x j = 0) ∧ ∀ j ∈ J, j ∉ I → |x j| ≤ b}

theorem isClosed_footSet (hT : IsClosed T) (I : Finset (Fin d)) : IsClosed (footSet J T b I) := by
  have h : footSet J T b I = zeroOn J ⁻¹' T ∩
      ((⋂ j ∈ (I : Set (Fin d)), {x : Fin d → ℝ | x j = 0}) ∩
        ⋂ j ∈ (J : Set (Fin d)), {x : Fin d → ℝ | j ∉ I → |x j| ≤ b}) := by
    ext x
    simp only [footSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, Finset.mem_coe]
  rw [h]
  refine (hT.preimage (continuous_zeroOn J)).inter (IsClosed.inter ?_ ?_)
  · exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
  · refine isClosed_biInter fun j _ => ?_
    by_cases hj : j ∈ I
    · simp only [hj, not_true_eq_false, false_implies, ofPred_true]
      exact isClosed_univ
    · simp only [hj, not_false_eq_true, true_implies]
      exact isClosed_le (continuous_abs.comp (continuous_apply j)) continuous_const

/-- **Fibre saturation on the piece**: for `ε ≤ b` and `y` in the size piece of stratum `I`,
`y ∈ dom ↔ foot_I y ∈ T'_I`. -/
theorem mem_productDom_iff_foot_mem_footSet (I : Finset (Fin d)) (hne : I.Nonempty) (hIJ : I ⊆ J)
    {ε : ℝ} (hεb : ε ≤ b) {y : Fin d → ℝ} (hy : y ∈ sizePiece J ε I) :
    y ∈ productDom J T b ↔ planeFoot (stratumSplit I hne) y ∈ footSet J T b I := by
  rw [planeFoot_eq_zeroOn]
  constructor
  · intro h
    refine ⟨by rw [zeroOn_zeroOn J hIJ]; exact h.1, fun j hj => zeroOn_apply_of_mem I hj y,
      fun j hj hjI => ?_⟩
    rw [zeroOn_apply_of_notMem I hjI]
    exact h.2 j hj
  · intro h
    refine ⟨by rw [← zeroOn_zeroOn J hIJ]; exact h.1, fun j hj => ?_⟩
    by_cases hjI : j ∈ I
    · exact ((hy j hj).2 hjI).le.trans hεb
    · have := h.2.2 j hj hjI
      rwa [zeroOn_apply_of_notMem I hjI] at this

/-- A unit independent of all active coordinates is independent of the normal coordinates of every
stratum. -/
theorem unit_indep_piece (u : (Fin d → ℝ) → ℝ)
    (hind : ∀ y ∈ productDom J T b, u y = u (zeroOn J y)) (I : Finset (Fin d)) (hne : I.Nonempty)
    (hIJ : I ⊆ J) {y : Fin d → ℝ} (hy : y ∈ productDom J T b) :
    u y = u (planeFoot (stratumSplit I hne) y) := by
  rw [planeFoot_eq_zeroOn, hind y hy, hind _ (zeroOn_mem_productDom J T b hy hIJ),
    zeroOn_zeroOn J hIJ]

/-- A weight factoring through the inactive coordinates is fibre-constant on every piece. -/
theorem weight_factor_piece (w r : (Fin d → ℝ) → ℝ)
    (hw : ∀ y ∈ productDom J T b, w y = r (zeroOn J y)) (I : Finset (Fin d)) (hne : I.Nonempty)
    (hIJ : I ⊆ J) {y : Fin d → ℝ} (hy : y ∈ productDom J T b) :
    w y = r (zeroOn J (planeFoot (stratumSplit I hne) y)) := by
  rw [planeFoot_eq_zeroOn, zeroOn_zeroOn J hIJ, hw y hy]

/-- A nonempty inactive base supplies a point of the domain vanishing on every stratum. -/
theorem exists_zeroPoint (hT : T.Nonempty) (hTJ : ∀ x ∈ T, ∀ j ∈ J, x j = 0) (hb : 0 ≤ b) :
    ∃ y₀ ∈ productDom J T b, ∀ j ∈ J, y₀ j = 0 := by
  obtain ⟨x, hx⟩ := hT
  refine ⟨x, ⟨?_, fun j hj => ?_⟩, hTJ x hx⟩
  · rw [zeroOn_of_forall_eq_zero J (hTJ x hx)]
    exact hx
  · rw [hTJ x hx j hj, abs_zero]
    exact hb

end ProductDom

/-! ### The hypothesis package -/

/-- **A centred product monomial chart with compatible cover weight**: chart `i` of the cover `R` is
monomial for the phase `K` on an open `W ⊇ dom`, its domain is the product `productDom J T b` over a
compact inactive base `T` (vectors vanishing on the active set `J = supp e`), its phase unit is
independent of the active coordinates, and its cover weight factors through the inactive
coordinates (a field: not implied by the product shape). -/
structure ProductMonomialChart {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
    (K : (Fin d → ℝ) → ℝ) where
  /-- The phase exponents. -/
  e : Fin d →₀ ℕ
  /-- The Jacobian exponents. -/
  h : Fin d →₀ ℕ
  /-- The open monomial neighbourhood of the domain. -/
  W : Set (Fin d → ℝ)
  W_open : IsOpen W
  dom_subset : (R.chart i).dom ⊆ W
  /-- The phase unit. -/
  u : (Fin d → ℝ) → ℝ
  u_cont : ContinuousOn u W
  u_ne : ∀ y ∈ W, u y ≠ 0
  phase_eq : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e
  /-- The Jacobian unit. -/
  v : (Fin d → ℝ) → ℝ
  v_cont : ContinuousOn v W
  det_eq : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h
  /-- The compact inactive base. -/
  T : Set (Fin d → ℝ)
  T_compact : IsCompact T
  T_nonempty : T.Nonempty
  T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  /-- The normal radius. -/
  b : ℝ
  b_pos : 0 < b
  dom_eq : (R.chart i).dom = productDom e.support T b
  unit_indep : ∀ y ∈ (R.chart i).dom, u y = u (zeroOn e.support y)
  /-- The inactive factor of the cover weight. -/
  r : (Fin d → ℝ) → ℝ
  r_meas : Measurable r
  /-- A bound of the weight factor. -/
  Cr : ℝ
  r_bound : ∀ x, |r x| ≤ Cr
  weight_eq : ∀ y ∈ (R.chart i).dom, R.weight i ((R.chart i).Φ y) = r (zeroOn e.support y)

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K)

theorem dom_compact' : IsCompact (R.chart i).dom := (R.chart i).dom_compact

/-- The normal-form ratio `(h_j+1)/e_j` of an active coordinate. -/
noncomputable def ratio (j : Fin d) : ℝ := ((P.h j : ℝ) + 1) / (P.e j : ℝ)

/-- The geometric exponent of stratum `I`: `min_{j ∈ I} (h_j+1)/e_j`. -/
noncomputable def pieceLam (I : Finset (Fin d)) (hne : I.Nonempty) : ℝ := I.inf' hne P.ratio

/-- The geometric multiplicity of stratum `I`: `#{j ∈ I : (h_j+1)/e_j = pieceLam}`. -/
noncomputable def pieceMult (I : Finset (Fin d)) (hne : I.Nonempty) : ℕ :=
  (I.filter fun j => P.ratio j = P.pieceLam I hne).card

end ProductMonomialChart

end Grammar
