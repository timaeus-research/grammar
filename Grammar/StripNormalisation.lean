/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialParity
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact-strip normalisation of the unit-removal rescaling (Astra #68 unit 3)

The unit-removal map `T = rescale i ρ`, `T(y) = y + (ρ(y) − 1) y_i e_i`, is one analytic map on the
whole chart; its fibre over a base point `y'` (`y'_i = 0`) is the one-variable map
`s ↦ s · ρ(y' + s e_i)` (`fibreMap`), whose derivative is the Jacobian `ρ + y_i ∂_i ρ`
(`hasDerivAt_fibreMap`, `det_rescaleDerivAt`). On a compact strip `|y_i| ≤ b₀` over a compact
base, positivity of `ρ` makes this derivative positive for `b₀` small, so `T` is injective by
fibrewise monotonicity — **no inverse function theorem is needed for injectivity**
(`exists_stripNormalisation`): there is an open strip `S ⊇ cylinder i Q₀ (b₀/2)` inside the
analyticity domain on which `T` is injective with positive Jacobian, whose image is open and
contains the cylinder `cylinder i Q₀ b` of positive height, and on which the inverse `invFunOn T S`
is analytic (the local analytic inverses of the inverse function theorem agree with the global
inverse by injectivity).

Non-claims: nothing is said about the region `|y_i| > b₀` of the chart (Astra #68: shrink rather
than solve the outer region); no phase or measure statement — those are `exact_normal_form` and the
transport units.
-/

open Set Filter Topology Metric

namespace Grammar

variable {d : ℕ}

/-! ### Bases and cylinders -/

/-- The base projection: the `i`-th coordinate set to zero. -/
def baseProj (i : Fin d) (y : Fin d → ℝ) : Fin d → ℝ := Function.update y i 0

theorem continuous_baseProj (i : Fin d) : Continuous (baseProj i) :=
  continuous_id.update i continuous_const

theorem baseProj_update (i : Fin d) (y : Fin d → ℝ) (s : ℝ) :
    baseProj i (Function.update y i s) = baseProj i y := by
  simp [baseProj, Function.update_idem]

theorem baseProj_baseProj (i : Fin d) (y : Fin d → ℝ) : baseProj i (baseProj i y) = baseProj i y :=
  baseProj_update i y 0

theorem baseProj_apply_self (i : Fin d) (y : Fin d → ℝ) : baseProj i y i = 0 := by
  simp [baseProj]

theorem update_baseProj (i : Fin d) (y : Fin d → ℝ) :
    Function.update (baseProj i y) i (y i) = y := by
  rw [baseProj, Function.update_idem, Function.update_eq_self]

theorem update_baseProj_eq (i : Fin d) (y : Fin d → ℝ) (s : ℝ) :
    Function.update (baseProj i y) i s = Function.update y i s := by
  rw [baseProj, Function.update_idem]

theorem baseProj_of_apply_eq_zero {i : Fin d} {y : Fin d → ℝ} (h : y i = 0) : baseProj i y = y := by
  rw [baseProj]
  conv_lhs => rw [show (0 : ℝ) = y i from h.symm]
  exact Function.update_eq_self i y

theorem dist_update_baseProj_le (i : Fin d) (y : Fin d → ℝ) (s : ℝ) :
    dist (Function.update y i s) (baseProj i y) ≤ |s| := by
  refine (dist_pi_le_iff (abs_nonneg s)).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [baseProj]
  · simp [baseProj, Function.update_of_ne h]

/-- The closed cylinder of half-height `b` over the base set `Q₀`. -/
def cylinder (i : Fin d) (Q₀ : Set (Fin d → ℝ)) (b : ℝ) : Set (Fin d → ℝ) :=
  {y | baseProj i y ∈ Q₀ ∧ |y i| ≤ b}

/-- The open cylinder of half-height `b` over the base set `U₀`. -/
def openCylinder (i : Fin d) (U₀ : Set (Fin d → ℝ)) (b : ℝ) : Set (Fin d → ℝ) :=
  {y | baseProj i y ∈ U₀ ∧ |y i| < b}

theorem isOpen_openCylinder (i : Fin d) {U₀ : Set (Fin d → ℝ)} (hU : IsOpen U₀) (b : ℝ) :
    IsOpen (openCylinder i U₀ b) := by
  change IsOpen (baseProj i ⁻¹' U₀ ∩ {y | |y i| < b})
  exact (hU.preimage (continuous_baseProj i)).inter
    (isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const)

theorem cylinder_eq_image (i : Fin d) {Q₀ : Set (Fin d → ℝ)} (hQ₀ : ∀ y ∈ Q₀, y i = 0) (b : ℝ) :
    cylinder i Q₀ b =
      (fun p : (Fin d → ℝ) × ℝ => Function.update p.1 i p.2) '' (Q₀ ×ˢ Icc (-b) b) := by
  ext y
  constructor
  · rintro ⟨hb, hy⟩
    exact ⟨(baseProj i y, y i), ⟨hb, abs_le.1 hy⟩, update_baseProj i y⟩
  · rintro ⟨⟨y', s⟩, ⟨hy', hs⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only
      rw [baseProj_update, baseProj_of_apply_eq_zero (hQ₀ y' hy')]
      exact hy'
    · simpa [abs_le] using hs

theorem isCompact_cylinder (i : Fin d) {Q₀ : Set (Fin d → ℝ)} (hQ : IsCompact Q₀)
    (hQ₀ : ∀ y ∈ Q₀, y i = 0) (b : ℝ) : IsCompact (cylinder i Q₀ b) := by
  rw [cylinder_eq_image i hQ₀ b]
  exact (hQ.prod isCompact_Icc).image (continuous_fst.update i continuous_snd)

/-! ### The fibre maps of the rescaling -/

/-- The fibre map of the rescaling over a base point: `s ↦ s · r(y' + s e_i)`. -/
def fibreMap (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y' : Fin d → ℝ) (s : ℝ) : ℝ :=
  s * r (Function.update y' i s)

theorem rescale_eq_update_fibreMap (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    rescale i r y = Function.update y i (fibreMap i r (baseProj i y) (y i)) := by
  unfold rescale fibreMap
  rw [update_baseProj]

theorem hasDerivAt_fibreMap {i : Fin d} {r : (Fin d → ℝ) → ℝ} {r' : (Fin d → ℝ) →L[ℝ] ℝ}
    {y' : Fin d → ℝ} {s : ℝ} (hr : HasFDerivAt r r' (Function.update y' i s)) :
    HasDerivAt (fibreMap i r y') (r (Function.update y' i s) + s * r' (Pi.single i 1)) s := by
  have h1 : HasDerivAt (fun t => r (Function.update y' i t)) (r' (Pi.single i 1)) s :=
    hr.comp_hasDerivAt s (hasDerivAt_update y' i s)
  have h2 : HasDerivAt (fun t : ℝ => t * r (Function.update y' i t))
      (1 * r (Function.update y' i s) + s * r' (Pi.single i 1)) s := (hasDerivAt_id s).mul h1
  rw [one_mul] at h2
  exact h2

theorem strictMonoOn_fibreMap {i : Fin d} {r : (Fin d → ℝ) → ℝ} {y' : Fin d → ℝ} {b₀ : ℝ}
    (hr : ∀ s ∈ Icc (-b₀) b₀, DifferentiableAt ℝ r (Function.update y' i s))
    (hpos : ∀ s ∈ Icc (-b₀) b₀,
      0 < r (Function.update y' i s) + s * fderiv ℝ r (Function.update y' i s) (Pi.single i 1)) :
    StrictMonoOn (fibreMap i r y') (Icc (-b₀) b₀) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro s hs
    exact (hasDerivAt_fibreMap (hr s hs).hasFDerivAt).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hs' := Ioo_subset_Icc_self hs
    rw [(hasDerivAt_fibreMap (hr s hs').hasFDerivAt).deriv]
    exact hpos s hs'

/-! ### The differential of the rescaling at a general point -/

/-- The differential of the rescaling at a general point: `v ↦ v + e_i ((c − 1) v_i + ℓ v)`. -/
noncomputable def rescaleDerivAt (i : Fin d) (c : ℝ) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.id ℝ _ +
    (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).comp
      ((c - 1) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) + ℓ)

theorem rescaleDerivAt_apply (i : Fin d) (c : ℝ) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ)
    (j : Fin d) : rescaleDerivAt i c ℓ v j = if j = i then c * v j + ℓ v else v j := by
  unfold rescaleDerivAt
  by_cases h : j = i
  · subst h; simp; ring
  · simp [h]

/-- **The derivative of the rescaling** at any point: `D(rescale i r)(y) = rescaleDerivAt i (r y)
(y_i Dr(y))`. -/
theorem hasFDerivAt_rescale (i : Fin d) {r : (Fin d → ℝ) → ℝ} {r' : (Fin d → ℝ) →L[ℝ] ℝ}
    {y : Fin d → ℝ} (hr : HasFDerivAt r r' y) :
    HasFDerivAt (rescale i r) (rescaleDerivAt i (r y) (y i • r')) y := by
  have e : rescale i r = fun y => y + (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
      ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y * (r y - 1)) := by
    funext y
    rw [rescale_eq]
    rfl
  rw [e]
  have hmul : HasFDerivAt (fun y => (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y *
      (r y - 1)) ((r y - 1) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) + y i • r') y := by
    have h := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul (hr.sub_const 1)
    rw [add_comm] at h
    exact h
  exact (hasFDerivAt_id y).add
    (((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).hasFDerivAt).comp y hmul)

/-- **The Jacobian of the rescaling**: `det D(rescale i r)(y) = r(y) + y_i ∂_i r(y)`. -/
theorem det_rescaleDerivAt (i : Fin d) (c : ℝ) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) :
    (rescaleDerivAt i c ℓ).det = c + ℓ (Pi.single i 1) := by
  classical
  unfold ContinuousLinearMap.det
  rw [← LinearMap.det_toMatrix']
  have hmat : LinearMap.toMatrix'
      ((rescaleDerivAt i c ℓ : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
      1 + Matrix.replicateCol Unit (Pi.single i (1 : ℝ)) *
        Matrix.replicateRow Unit (fun k => (c - 1) * (Pi.single i (1 : ℝ) : Fin d → ℝ) k +
          ℓ (Pi.single k 1)) := by
    ext j k
    rw [LinearMap.toMatrix'_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, ContinuousLinearMap.coe_coe, rescaleDerivAt_apply]
    by_cases hj : j = i
    · subst hj
      by_cases hk : j = k
      · subst hk; simp; ring
      · simp [hk, Ne.symm hk]
    · simp [hj, Pi.single_apply]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single]
  simp only [Pi.single_eq_same, mul_one]
  ring

/-- The differential of the rescaling as a continuous linear equivalence, when its determinant is
nonzero. -/
noncomputable def rescaleDerivEquiv (i : Fin d) (c : ℝ) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ)
    (h : c + ℓ (Pi.single i 1) ≠ 0) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  (LinearEquiv.ofIsUnitDet (f := ((rescaleDerivAt i c ℓ : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) (v := Pi.basisFun ℝ (Fin d)) (v' := Pi.basisFun ℝ (Fin d))
    (by
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.det_toMatrix', isUnit_iff_ne_zero]
      have := det_rescaleDerivAt i c ℓ
      unfold ContinuousLinearMap.det at this
      rw [this]
      exact h)).toContinuousLinearEquiv

theorem coe_rescaleDerivEquiv (i : Fin d) (c : ℝ) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ)
    (h : c + ℓ (Pi.single i 1) ≠ 0) :
    (rescaleDerivEquiv i c ℓ h : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) = rescaleDerivAt i c ℓ := by
  ext v
  rfl

/-! ### The strip normalisation theorem -/

/-- **Compact-strip normalisation.** Let `ρ` be analytic and positive on an open `V` and
`Q₀ ⊆ V` a compact base set (`y_i = 0` on `Q₀`). Then there are heights `b₀, b > 0` and an open
strip `S` with `cylinder i Q₀ (b₀/2) ⊆ S ⊆ V` on which the rescaling `T = rescale i ρ` is
injective with positive Jacobian `ρ + y_i ∂_i ρ`, whose image `T '' S` is open and contains the
cylinder `cylinder i Q₀ b`, and on which the inverse `invFunOn T S` is analytic at every point of
the image. -/
theorem exists_stripNormalisation {i : Fin d} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : AnalyticOnNhd ℝ ρ V) (hρpos : ∀ y ∈ V, 0 < ρ y)
    {Q₀ : Set (Fin d → ℝ)} (hQ₀ : IsCompact Q₀) (hQ₀V : Q₀ ⊆ V) (hQ₀i : ∀ y ∈ Q₀, y i = 0) :
    ∃ (b₀ b : ℝ) (S : Set (Fin d → ℝ)), 0 < b₀ ∧ 0 < b ∧ IsOpen S ∧ S ⊆ V ∧
      cylinder i Q₀ (b₀ / 2) ⊆ S ∧ InjOn (rescale i ρ) S ∧
      (∀ y ∈ S, 0 < ρ y + y i * fderiv ℝ ρ y (Pi.single i 1)) ∧
      IsOpen (rescale i ρ '' S) ∧ cylinder i Q₀ b ⊆ rescale i ρ '' S ∧
      ∀ z ∈ rescale i ρ '' S, AnalyticAt ℝ (Function.invFunOn (rescale i ρ) S) z := by
  classical
  rcases Q₀.eq_empty_or_nonempty with hemp | hne
  · subst hemp
    refine ⟨1, 1, ∅, one_pos, one_pos, isOpen_empty, empty_subset _, fun y hy => hy.1.elim,
      injOn_empty _, fun y hy => hy.elim, by simp, fun y hy => hy.1.elim, fun z hz => ?_⟩
    simp at hz
  -- Step 1: a thickening of the base inside `V`
  obtain ⟨δ, hδ, hδV⟩ := hQ₀.exists_cthickening_subset_open hV hQ₀V
  set C := cthickening (δ / 2) Q₀ with hC
  have hCcpt : IsCompact C := hQ₀.cthickening
  have hCV : C ⊆ V := (cthickening_mono (by linarith) Q₀).trans hδV
  -- Step 2: uniform bounds on `C`
  have hρcont : ContinuousOn ρ C := hρ.continuousOn.mono hCV
  have hdcont : ContinuousOn (fun y => fderiv ℝ ρ y (Pi.single i 1)) C := fun y hy =>
    ((hρ y (hCV hy)).fderiv.continuousAt.clm_apply continuousAt_const).continuousWithinAt
  obtain ⟨M, hM⟩ := hCcpt.exists_bound_of_continuousOn hdcont
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMd : ∀ y ∈ C, |fderiv ℝ ρ y (Pi.single i 1)| ≤ M' := fun y hy => by
    have := hM y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨y₀, hy₀C, hmin⟩ :=
    hCcpt.exists_isMinOn (hne.mono (self_subset_cthickening _)) hρcont
  set ρmin := ρ y₀ with hρmin_def
  have hρmin : 0 < ρmin := hρpos y₀ (hCV hy₀C)
  have hρge : ∀ y ∈ C, ρmin ≤ ρ y := fun y hy => (isMinOn_iff.1 hmin) y hy
  -- Step 3: the height
  set b₀ := min (δ / 4) (ρmin / (2 * (M' + 1))) with hb₀
  have hb₀pos : 0 < b₀ := lt_min (by linarith) (by positivity)
  have hb₀δ : b₀ ≤ δ / 4 := min_le_left _ _
  have hb₀M : b₀ * M' ≤ ρmin / 2 := by
    have h1 : b₀ ≤ ρmin / (2 * (M' + 1)) := min_le_right _ _
    have h2 : ρmin / (2 * (M' + 1)) * (M' + 1) = ρmin / 2 := by field_simp
    calc b₀ * M' ≤ b₀ * (M' + 1) := mul_le_mul_of_nonneg_left (by linarith) hb₀pos.le
      _ ≤ ρmin / (2 * (M' + 1)) * (M' + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ρmin / 2 := h2
  -- Step 4: the strip
  set U₀ := thickening (δ / 4) Q₀ with hU₀
  set S := openCylinder i U₀ b₀ with hS
  have hSopen : IsOpen S := isOpen_openCylinder i isOpen_thickening b₀
  have hfibC : ∀ y ∈ S, ∀ s : ℝ, |s| ≤ b₀ → Function.update y i s ∈ C := by
    intro y hy s hs
    obtain ⟨z, hz, hdist⟩ := mem_thickening_iff.1 hy.1
    have h1 : dist (Function.update y i s) (baseProj i y) ≤ |s| := dist_update_baseProj_le i y s
    have h2 : dist (Function.update y i s) z ≤ δ / 2 := by
      calc dist (Function.update y i s) z
          ≤ dist (Function.update y i s) (baseProj i y) + dist (baseProj i y) z :=
            dist_triangle _ _ _
        _ ≤ |s| + δ / 4 := add_le_add h1 hdist.le
        _ ≤ b₀ + δ / 4 := by linarith
        _ ≤ δ / 2 := by linarith
    exact mem_cthickening_of_dist_le _ _ _ _ hz h2
  have hSC : S ⊆ C := fun y hy => by
    have := hfibC y hy (y i) hy.2.le
    rwa [Function.update_eq_self] at this
  have hSV : S ⊆ V := hSC.trans hCV
  -- Step 5: the Jacobian is positive on the strip
  have hjac : ∀ y ∈ C, |y i| ≤ b₀ → 0 < ρ y + y i * fderiv ℝ ρ y (Pi.single i 1) := by
    intro y hy hyi
    have h1 := hρge y hy
    have h2 := hMd y hy
    have h3 : |y i * fderiv ℝ ρ y (Pi.single i 1)| ≤ b₀ * M' := by
      rw [abs_mul]
      exact mul_le_mul hyi h2 (abs_nonneg _) hb₀pos.le
    have h4 := (abs_le.1 h3).1
    linarith
  have hmono : ∀ y ∈ S, StrictMonoOn (fibreMap i ρ (baseProj i y)) (Icc (-b₀) b₀) := by
    intro y hy
    have hfib : ∀ s ∈ Icc (-b₀) b₀, Function.update (baseProj i y) i s ∈ C := by
      intro s hs
      rw [update_baseProj_eq]
      exact hfibC y hy s (abs_le.2 hs)
    refine strictMonoOn_fibreMap (fun s hs => (hρ _ (hCV (hfib s hs))).differentiableAt)
      (fun s hs => ?_)
    have := hjac _ (hfib s hs) (by rw [Function.update_self]; exact abs_le.2 hs)
    simpa using this
  -- Step 6: injectivity by fibrewise monotonicity
  have hinj : InjOn (rescale i ρ) S := by
    intro y₁ hy₁ y₂ hy₂ heq
    have hbase : baseProj i y₁ = baseProj i y₂ := by
      have := congrArg (baseProj i) heq
      rwa [rescale_eq_update_fibreMap, rescale_eq_update_fibreMap, baseProj_update,
        baseProj_update] at this
    have hfib : fibreMap i ρ (baseProj i y₁) (y₁ i) = fibreMap i ρ (baseProj i y₁) (y₂ i) := by
      have := congrFun heq i
      rw [rescale_eq_update_fibreMap, rescale_eq_update_fibreMap] at this
      simp only [Function.update_self] at this
      rw [← hbase] at this
      exact this
    have h1 : y₁ i ∈ Icc (-b₀) b₀ := abs_le.1 hy₁.2.le
    have h2 : y₂ i ∈ Icc (-b₀) b₀ := abs_le.1 hy₂.2.le
    have hi := (hmono y₁ hy₁).injOn h1 h2 hfib
    rw [← update_baseProj i y₁, ← update_baseProj i y₂, hbase, hi]
  -- Step 7: the inverse function theorem at each strip point
  have hIFT : ∀ y ∈ S, ∃ ψ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ),
      y ∈ ψ.source ∧ (∀ w, ψ w = rescale i ρ w) ∧ AnalyticAt ℝ ψ.symm (rescale i ρ y) := by
    intro y hy
    have hyV := hSV hy
    have hdet : ρ y + (y i • fderiv ℝ ρ y) (Pi.single i 1) ≠ 0 := by
      have := hjac y (hSC hy) hy.2.le
      change ρ y + y i • fderiv ℝ ρ y (Pi.single i 1) ≠ 0
      rw [smul_eq_mul]
      exact this.ne'
    have hderiv : HasFDerivAt (rescale i ρ)
        (rescaleDerivEquiv i (ρ y) (y i • fderiv ℝ ρ y) hdet :
          (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) y := by
      rw [coe_rescaleDerivEquiv]
      exact hasFDerivAt_rescale i (hρ y hyV).differentiableAt.hasFDerivAt
    have hT : AnalyticAt ℝ (rescale i ρ) y := analyticAt_rescale i (hρ y hyV)
    have hstrict : HasStrictFDerivAt (rescale i ρ)
        (rescaleDerivEquiv i (ρ y) (y i • fderiv ℝ ρ y) hdet :
          (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) y := by
      have := hT.hasStrictFDerivAt
      rwa [hderiv.fderiv] at this
    set ψ := hstrict.toOpenPartialHomeomorph (rescale i ρ) with hψ
    have hcoe : ∀ w, ψ w = rescale i ρ w := fun w => rfl
    have hmem : y ∈ ψ.source := hstrict.mem_toOpenPartialHomeomorph_source
    obtain ⟨p, hp⟩ := hT
    have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ (Fin d → ℝ) (Fin d → ℝ)).symm
        (rescaleDerivEquiv i (ρ y) (y i • fderiv ℝ ρ y) hdet) := by
      have h1 := hp.fderiv_eq
      rw [hderiv.fderiv] at h1
      rw [h1]
      simp
    have hpψ : HasFPowerSeriesAt ψ p y := hp
    have hsymm := ψ.hasFPowerSeriesAt_symm hmem hpψ hp1
    exact ⟨ψ, hmem, hcoe, hsymm.analyticAt⟩
  -- Step 8: the image is open
  have himg : IsOpen (rescale i ρ '' S) := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨ψ, hmem, hcoe, -⟩ := hIFT y hy
    refine ⟨ψ '' (ψ.source ∩ S), ?_,
      ψ.isOpen_image_of_subset_source (ψ.open_source.inter hSopen) inter_subset_left,
      ⟨y, ⟨hmem, hy⟩, hcoe y⟩⟩
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, hv.2, (hcoe v).symm⟩
  -- Step 9: the inverse is analytic on the image
  have hinvan : ∀ z ∈ rescale i ρ '' S, AnalyticAt ℝ (Function.invFunOn (rescale i ρ) S) z := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨ψ, hmem, hcoe, hsymm⟩ := hIFT y hy
    refine hsymm.congr ?_
    have hz : rescale i ρ y ∈ ψ.target := by rw [← hcoe y]; exact ψ.map_source hmem
    have hcont : ContinuousAt ψ.symm (rescale i ρ y) := ψ.continuousAt_symm hz
    have hsy : ψ.symm (rescale i ρ y) = y := by rw [← hcoe y]; exact ψ.left_inv hmem
    have hnhd : ∀ᶠ w in 𝓝 (rescale i ρ y), ψ.symm w ∈ ψ.source ∩ S := by
      have hopen : IsOpen (ψ.source ∩ S) := ψ.open_source.inter hSopen
      have : ψ.symm (rescale i ρ y) ∈ ψ.source ∩ S := by rw [hsy]; exact ⟨hmem, hy⟩
      exact hcont (hopen.mem_nhds this)
    have htgt : ∀ᶠ w in 𝓝 (rescale i ρ y), w ∈ ψ.target := ψ.open_target.mem_nhds hz
    filter_upwards [hnhd, htgt] with w hw hwt
    have hTw : rescale i ρ (ψ.symm w) = w := by rw [← hcoe]; exact ψ.right_inv hwt
    have hex : ∃ a ∈ S, rescale i ρ a = w := ⟨ψ.symm w, hw.2, hTw⟩
    exact (hinj (Function.invFunOn_mem hex) hw.2 ((Function.invFunOn_eq hex).trans hTw.symm)).symm
  -- Step 10: the output cylinder lies in the image
  set b := b₀ / 2 * ρmin with hb
  have hbpos : 0 < b := by positivity
  have hcyl : cylinder i Q₀ b ⊆ rescale i ρ '' S := by
    rintro z ⟨hzb, hzi⟩
    have hz'S : ∀ s : ℝ, |s| < b₀ → Function.update (baseProj i z) i s ∈ S := fun s hs =>
      ⟨by rw [baseProj_update, baseProj_baseProj]
          exact self_subset_thickening (by linarith) Q₀ hzb, by simpa using hs⟩
    have hz'S0 : baseProj i z ∈ S := by
      have := hz'S 0 (by simpa using hb₀pos)
      rw [update_baseProj_eq] at this
      exact this
    have hcontf : ContinuousOn (fibreMap i ρ (baseProj i z)) (Icc (-(b₀ / 2)) (b₀ / 2)) := by
      intro s hs
      have hsb : |s| ≤ b₀ := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      exact (hasDerivAt_fibreMap ((hρ _ (hCV (hfibC _ hz'S0 s hsb))).differentiableAt.hasFDerivAt
        )).continuousAt.continuousWithinAt
    have hlo : fibreMap i ρ (baseProj i z) (-(b₀ / 2)) ≤ -b := by
      have hρ' := hρge _ (hfibC _ hz'S0 (-(b₀ / 2))
        (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))
      simp only [fibreMap, hb]
      nlinarith
    have hhi : b ≤ fibreMap i ρ (baseProj i z) (b₀ / 2) := by
      have hρ' := hρge _ (hfibC _ hz'S0 (b₀ / 2) (by rw [abs_of_pos (by positivity)]; linarith))
      simp only [fibreMap, hb]
      nlinarith
    have hmem : z i ∈ Icc (fibreMap i ρ (baseProj i z) (-(b₀ / 2)))
        (fibreMap i ρ (baseProj i z) (b₀ / 2)) :=
      ⟨by linarith [(abs_le.1 hzi).1], by linarith [(abs_le.1 hzi).2]⟩
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by linarith) hcontf hmem
    refine ⟨Function.update (baseProj i z) i s,
      hz'S s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]), ?_⟩
    rw [rescale_eq_update_fibreMap, baseProj_update, Function.update_self, Function.update_idem,
      baseProj_baseProj, hfs]
    exact update_baseProj i z
  refine ⟨b₀, b, S, hb₀pos, hbpos, hSopen, hSV, ?_, hinj, fun y hy => hjac y (hSC hy) hy.2.le,
    himg, hcyl, hinvan⟩
  intro y hy
  exact ⟨self_subset_thickening (by linarith) Q₀ hy.1, by linarith [hy.2]⟩

end Grammar
