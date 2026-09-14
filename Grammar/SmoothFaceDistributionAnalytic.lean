/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceFunctionalBound
import Grammar.ProductJetDistribution
import Grammar.ParametricCoordinateDerivative

/-!
# The chart-face distributions (consult #124 §4–§5, units C5c/C5d — analytic part)

The chart-face functional
`faceFunctional X P J a μ q u = ∫_s renormFunctional (ρfam P s) … (cyl J u s) dν`
of CDXXII is, for smooth `u` on the face space `PieceFaceSpace X P J = BaseSpace × TangSpace`:

* **linear** (`faceFunctional_add`, `faceFunctional_smul`): the base integrand is continuous in `s`
  (`continuous_renormFunctional_cyl`, through the amplitude family `cylFam` of the cylinder
  extensions, built from the parametric derivative infrastructure CDXXI), hence integrable on the
  compact base, and the renormalised functional is linear pointwise;
* **of finite tangential order** (`abs_faceFunctional_le`): `|faceFunctional u| ≤ faceConst · M`
  whenever the tangential derivatives `∂^r_w u (s, w)` of orders `r ≤ faceOrder = Σ_j p_j` are
  bounded by `M` on the closed face box `baseBox × [0,a]^K` (`TangentialJetBound`); no base
  derivatives are needed. This is the quantitative bound CDXXIII on the renormalised functional
  applied to the
  cylinder extension, whose mixed derivatives are tangential derivatives of `u` (`rectBound_cyl`);
* **local** (`faceFunctional_eq_zero_of_eqOn_zero`): it vanishes on functions vanishing on a
  neighbourhood of the closed face box.

Hence the **chart-face distribution** `faceDistribution X P J a μ q : 𝓓'(PieceFaceSpace X P J, ℝ)`
(through `Distribution.ofTangentialJetBound`, CDXIX), equal to the face functional on test functions
(`faceDistribution_apply`), with `dsupport ⊆ baseBox ×ˢ [0,a]^K` and compact support. Together with
the reconstruction `coeffDistribution_eq_sum_faceFunctional` (CDXXII) this is Theorem C in its
chart-face form: the intrinsic coefficient distribution is a finite sum of finite-order chart-face
distributions paired with the normal jets of the observable restricted to the chart-local strata.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The tangential projection is a contraction -/

theorem norm_tangProj_le_one (J : Finset (Fin d)) : ‖tangProj J‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun k => ?_
  rw [tangProj_apply]
  exact norm_le_pi_norm v k.1

theorem prod_norm_tangProj_le_one (J : Finset (Fin d)) (n : ℕ) :
    ∏ _j : Fin n, ‖tangProj J‖ ≤ 1 :=
  Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_tangProj_le_one J

/-- The renormalised functional of the zero function vanishes. -/
theorem renormFunctional_zero {h k p : Fin d → ℕ} {β b μ : ℝ} {D : (Fin d → ℝ) → ℝ}
    (hD : ContDiff ℝ ∞ D) (hb : 0 < b) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) (a : Fin d → ℕ)
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (q : ℕ) :
    renormFunctional D h k p β b J a μ q (fun _ => (0 : ℝ)) = 0 := by
  have h0 := renormFunctional_add_smul (β := β) hD contDiff_const contDiff_const hb hp0 J a hμ q
    (U₁ := fun _ => (0 : ℝ)) (U₂ := fun _ => (0 : ℝ)) 0 0
  have hfun : (fun v : Fin d → ℝ => (0 : ℝ) * (fun _ => (0 : ℝ)) v + 0 * (fun _ => (0 : ℝ)) v) =
      fun _ => (0 : ℝ) := by funext v; ring
  rw [hfun] at h0
  rw [h0]; ring

namespace BridgeInputs

variable (X : BridgeInputs d)

/-! ### The cylinder family over the base -/

/-- The joint function `(s, v) ↦ u (s, tangProj v)` on the ambient base times the active box. -/
noncomputable def cylJoint (P : X.PIdx) (J : Finset (Fin (X.da P))) (u : X.PieceFaceSpace P J → ℝ) :
    X.BaseSpace P × (Fin (X.da P) → ℝ) → ℝ :=
  fun z => u (z.1, tangProj J z.2)

theorem contDiff_cylJoint (P : X.PIdx) (J : Finset (Fin (X.da P)))
    {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (X.cylJoint P J u) :=
  hu.comp (contDiff_fst.prodMk ((tangProj J).contDiff.comp contDiff_snd))

/-- The cylinder extensions of `u` over the compact base, as a smooth amplitude family. -/
noncomputable def cylFam (P : X.PIdx) (J : Finset (Fin (X.da P))) {u : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    SmoothAmplitudeFamily (Base (X.act P.1) (X.T.a P.1)) (X.da P) (X.T.a P.1) :=
  SmoothAmplitudeFamily.ofSlice (σ := fun s : Base (X.act P.1) (X.T.a P.1) => s.1)
    continuous_subtype_val (X.contDiff_cylJoint P J hu) (X.T.a P.1)

theorem cylFam_apply (P : X.PIdx) (J : Finset (Fin (X.da P))) {u : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) (s : Base (X.act P.1) (X.T.a P.1)) :
    X.cylFam P J hu s = cyl J u s.1 := rfl

theorem pieceDepth_pos (P : X.PIdx) (μ : ℝ) (j : Fin (X.da P)) : 0 < X.pieceDepth P μ j :=
  depthOf_pos (X.kA_pos P) (L₀_le_cutoffOf _ μ) j

theorem pieceDepth_convergence (P : X.PIdx) (μ : ℝ) (j : Fin (X.da P)) :
    ((2 * X.kA P j : ℕ) : ℝ) * μ < X.pieceDepth P μ j + X.hA P j + 1 :=
  two_k_mul_lt_of_le (depthOf_add (X.kA_pos P) (L₀_le_cutoffOf _ μ)) (lt_cutoffOf _ μ).le j

/-- ★ **Parameter continuity** of the renormalised functionals of the cylinder extensions. -/
theorem continuous_renormFunctional_cyl (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    Continuous fun s : Base (X.act P.1) (X.T.a P.1) =>
      renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
        (X.T.a P.1) J a μ q (cyl J u s.1) := by
  unfold renormFunctional
  refine continuous_finsetSum _ fun m hm => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_const.mul continuous_const).mul ?_)
  have hm' : m ∈ idxL (X.pieceDepth P μ) (lJ J) := (Finset.mem_filter.1 hm).1
  have hma : m - a ∈ idxL (X.pieceDepth P μ) (lJ J) := mem_idxL_of_le hm' fun i => Nat.sub_le _ _
  have heq : ∀ s : Base (X.act P.1) (X.T.a P.1),
      (fun v => pdMulti (m - a) (lJ J) (X.ρfam P s) v * cyl J u s.1 v) =
        (((X.ρfam P).pdMulti (m - a)).mul (X.cylFam P J hu)) s := fun s => by
    rw [SmoothAmplitudeFamily.mul_apply, SmoothAmplitudeFamily.pdMulti_apply,
      pdMulti_lJ_eq_finRange hma ((X.ρfam P).smooth s)]
    rfl
  simp only [heq]
  exact SmoothAmplitudeFamily.continuous_faceCoeffInt_family _ (X.T.a_pos P.1)
    (X.pieceDepth_pos P μ) J (zero_mem_idxL _ (X.pieceDepth_pos P μ) (lJ J))
    (X.pieceDepth_convergence P μ) (j - q)

theorem integrable_renormFunctional_cyl (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    Integrable (fun s : Base (X.act P.1) (X.T.a P.1) =>
      renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
        (X.T.a P.1) J a μ q (cyl J u s.1))
      (baseMeasure (X.act P.1) (X.T.a P.1) (X.T.h P.1)) :=
  integrable_of_continuous_compactSpace _ (X.continuous_renormFunctional_cyl P J a μ q hu)

/-! ### Linearity -/

/-- ★ **Additivity** of the chart-face functional. -/
theorem faceFunctional_add (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) {u u' : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu' : ContDiff ℝ ∞ u') :
    X.faceFunctional P J a μ q (fun z => u z + u' z) =
      X.faceFunctional P J a μ q u + X.faceFunctional P J a μ q u' := by
  unfold faceFunctional
  rw [← integral_add (X.integrable_renormFunctional_cyl P J a μ q hu)
    (X.integrable_renormFunctional_cyl P J a μ q hu')]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have h := renormFunctional_add_smul (β := X.T.phaseConst P.1) ((X.ρfam P).smooth s)
    (contDiff_cyl (B := X.BaseSpace P) J hu s.1) (contDiff_cyl (B := X.BaseSpace P) J hu' s.1)
    (X.T.a_pos P.1) (X.pieceDepth_pos P μ) J a
    (X.pieceDepth_convergence P μ) q 1 1
  have hfun : cyl J (fun z => u z + u' z) s.1 =
      fun v => 1 * cyl J u s.1 v + 1 * cyl J u' s.1 v := by
    funext v; simp only [cyl_apply]; ring
  simp only [one_mul] at h
  beta_reduce
  rw [hfun]
  simpa using h

/-- ★ **Homogeneity** of the chart-face functional. -/
theorem faceFunctional_smul (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    X.faceFunctional P J a μ q (fun z => c * u z) = c * X.faceFunctional P J a μ q u := by
  unfold faceFunctional
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have h := renormFunctional_add_smul (β := X.T.phaseConst P.1) ((X.ρfam P).smooth s)
    (contDiff_cyl (B := X.BaseSpace P) J hu s.1) (contDiff_cyl (B := X.BaseSpace P) J hu s.1)
    (X.T.a_pos P.1) (X.pieceDepth_pos P μ) J a
    (X.pieceDepth_convergence P μ) q c 0
  have hfun : cyl J (fun z => c * u z) s.1 = fun v => c * cyl J u s.1 v + 0 * cyl J u s.1 v := by
    funext v; simp only [cyl_apply]; ring
  beta_reduce
  rw [hfun, h, zero_mul, add_zero]

/-! ### The tangential finite-order bound -/

/-- The tangential order of the chart-face functionals of a piece: the total canonical depth. -/
noncomputable def faceOrder (P : X.PIdx) (μ : ℝ) : ℕ := ∑ j, X.pieceDepth P μ j

/-- The closed tangential box `[0,a]^K`. -/
noncomputable def tangBox (P : X.PIdx) (J : Finset (Fin (X.da P))) : Set ({k // ¬ inJ J k} → ℝ) :=
  Set.pi univ fun _ => Icc 0 (X.T.a P.1)

theorem isCompact_tangBox (P : X.PIdx) (J : Finset (Fin (X.da P))) : IsCompact (X.tangBox P J) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- The closed face box `baseBox × [0,a]^K`. -/
noncomputable def faceBox (P : X.PIdx) (J : Finset (Fin (X.da P))) : Set (X.PieceFaceSpace P J) :=
  baseBox (X.act P.1) (X.T.a P.1) ×ˢ X.tangBox P J

theorem isCompact_faceBox (P : X.PIdx) (J : Finset (Fin (X.da P))) : IsCompact (X.faceBox P J) :=
  (isCompact_baseBox _ _).prod (X.isCompact_tangBox P J)

theorem tangProj_mem_tangBox (P : X.PIdx) (J : Finset (Fin (X.da P))) {v : Fin (X.da P) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a P.1)) : tangProj J v ∈ X.tangBox P J :=
  fun k _ => by rw [tangProj_apply]; exact hv k.1

/-- ★ The cylinder extension of a tangentially jet-bounded function has the engine's rectangular
bound (its mixed derivatives are tangential derivatives of the slices). -/
theorem rectBound_cyl (P : X.PIdx) (J : Finset (Fin (X.da P))) (μ : ℝ)
    {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u) {M : ℝ}
    (hT : TangentialJetBound (X.faceOrder P μ) (baseBox (X.act P.1) (X.T.a P.1)) (X.tangBox P J)
      u M) (s : Base (X.act P.1) (X.T.a P.1)) :
    RectBound (cyl J u s.1) (X.pieceDepth P μ) (X.T.a P.1) M := by
  intro β hβ v hv
  have hslice : ContDiff ℝ ∞ fun w => u (s.1, w) := contDiff_slice hu s.1
  have hcomp : cyl J u s.1 = (fun w => u (s.1, w)) ∘ (tangProj J) := rfl
  rw [hcomp]
  refine (abs_pdMulti_finRange_le_norm_iteratedFDeriv (hslice.comp (tangProj J).contDiff) β
    v).trans ?_
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (tangProj J) hslice v (mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ (∑ i, β i) (fun w => u (s.1, w)) (tangProj J v)‖ *
        ∏ _j : Fin (∑ i, β i), ‖tangProj J‖
      ≤ ‖iteratedFDeriv ℝ (∑ i, β i) (fun w => u (s.1, w)) (tangProj J v)‖ * 1 :=
        mul_le_mul_of_nonneg_left (prod_norm_tangProj_le_one J _) (norm_nonneg _)
    _ ≤ M := by
        rw [mul_one]
        exact hT s.1 s.2 _ (Finset.sum_le_sum fun j _ => hβ j) _ (X.tangProj_mem_tangBox P J hv)

theorem exists_densityBound2 (P : X.PIdx) (μ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, RectBound (X.ρfam P s) (fun j => 2 * X.pieceDepth P μ j) (X.T.a P.1) M :=
  (X.ρfam P).exists_uniform_rect_bound _

/-- The uniform doubled-depth bound of the density family. -/
noncomputable def densityBound2 (P : X.PIdx) (μ : ℝ) : ℝ :=
  Classical.choose (X.exists_densityBound2 P μ)

theorem densityBound2_nonneg (P : X.PIdx) (μ : ℝ) : 0 ≤ X.densityBound2 P μ :=
  (Classical.choose_spec (X.exists_densityBound2 P μ)).1

theorem rectBound_ρfam2 (P : X.PIdx) (μ : ℝ) (s : Base (X.act P.1) (X.T.a P.1)) :
    RectBound (X.ρfam P s) (fun j => 2 * X.pieceDepth P μ j) (X.T.a P.1) (X.densityBound2 P μ) :=
  (Classical.choose_spec (X.exists_densityBound2 P μ)).2 s

/-- The bound constant of the chart-face functional. -/
noncomputable def faceConst (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  renormConst (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1) (X.T.a P.1) J a μ q *
    (2 ^ X.faceOrder P μ * X.densityBound2 P μ) *
      (baseMeasure (X.act P.1) (X.T.a P.1) (X.T.h P.1)).real univ

theorem faceConst_nonneg (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ) (μ : ℝ)
    (q : ℕ) : 0 ≤ X.faceConst P J a μ q :=
  mul_nonneg (mul_nonneg (renormConst_nonneg _ _ _ _ _ _ _ _ _)
    (mul_nonneg (pow_nonneg (by norm_num) _) (X.densityBound2_nonneg P μ))) measureReal_nonneg

/-- ★★ **The tangential finite-order bound** on the chart-face functional. -/
theorem abs_faceFunctional_le (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u) {M : ℝ}
    (hT : TangentialJetBound (X.faceOrder P μ) (baseBox (X.act P.1) (X.T.a P.1)) (X.tangBox P J)
      u M) :
    |X.faceFunctional P J a μ q u| ≤ X.faceConst P J a μ q * M := by
  unfold faceFunctional faceConst
  rw [← Real.norm_eq_abs]
  have hpt : ∀ s : Base (X.act P.1) (X.T.a P.1),
      ‖renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
        (X.T.a P.1) J a μ q (cyl J u s.1)‖ ≤
      renormConst (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1) (X.T.a P.1) J a μ q *
        (2 ^ X.faceOrder P μ * X.densityBound2 P μ * M) := fun s => by
    rw [Real.norm_eq_abs]
    exact abs_renormFunctional_le ((X.ρfam P).smooth s) (contDiff_cyl (B := X.BaseSpace P) J hu s.1)
      (X.T.a_pos P.1) (X.pieceDepth_pos P μ) (canonical_convergence (X.kA_pos P) (X.hA P) μ) J a q
      (X.rectBound_ρfam2 P μ s) (X.rectBound_cyl P J μ hu hT s)
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hpt)).trans (le_of_eq ?_)
  ring

/-! ### Locality -/

/-- ★ **Locality**: the chart-face functional vanishes on functions vanishing near the closed face
box. -/
theorem faceFunctional_eq_zero_of_eqOn_zero (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u)
    {U : Set (X.PieceFaceSpace P J)} (hUo : IsOpen U) (hKU : X.faceBox P J ⊆ U)
    (h0 : EqOn u 0 U) : X.faceFunctional P J a μ q u = 0 := by
  unfold faceFunctional
  refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
  have hW : IsOpen ((fun v : Fin (X.da P) → ℝ => (s.1, tangProj J v)) ⁻¹' U) :=
    hUo.preimage (continuous_const.prodMk (tangProj J).continuous)
  have heq : EqOn (cyl J u s.1) (fun _ => (0 : ℝ))
      ((fun v : Fin (X.da P) → ℝ => (s.1, tangProj J v)) ⁻¹' U) := fun v hv => h0 hv
  have hjet : ∀ α : Fin (X.da P) → ℕ, (∀ i, α i ≤ X.pieceDepth P μ i) →
      ∀ v : Fin (X.da P) → ℝ, (∀ i, v i ∈ Icc 0 (X.T.a P.1)) → (∀ i ∈ J, v i = 0) →
      pdMulti α (lK J) (cyl J u s.1) v = pdMulti α (lK J) (fun _ => (0 : ℝ)) v := fun α _ v hv _ =>
    pdMulti_eqOn_of_isOpen hW heq α (lK J) (hKU ⟨s.2, X.tangProj_mem_tangBox P J hv⟩)
  change renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
    (X.T.a P.1) J a μ q (cyl J u s.1) = 0
  rw [renormFunctional_congr ((X.ρfam P).smooth s) (contDiff_cyl (B := X.BaseSpace P) J hu s.1)
    contDiff_const (X.T.a_pos P.1) J a q hjet]
  exact renormFunctional_zero ((X.ρfam P).smooth s) (X.T.a_pos P.1) (X.pieceDepth_pos P μ) J a
    (X.pieceDepth_convergence P μ) q

/-! ### The chart-face distribution -/

/-- ★★★ **The chart-face distribution** of a piece, a face and a normal multi-index. -/
noncomputable def faceDistribution (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) : 𝓓'((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ) :=
  Distribution.ofTangentialJetBound (X.faceOrder P μ) (baseBox (X.act P.1) (X.T.a P.1))
    (X.tangBox P J) (X.faceConst P J a μ q) (fun f => X.faceFunctional P J a μ q f)
    (fun f g => X.faceFunctional_add P J a μ q f.contDiff g.contDiff)
    (fun c f => X.faceFunctional_smul P J a μ q f.contDiff c)
    (fun f _ _ hT => X.abs_faceFunctional_le P J a μ q f.contDiff hT)

theorem faceDistribution_apply (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) (f : 𝓓((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ)) :
    X.faceDistribution P J a μ q f = X.faceFunctional P J a μ q f := rfl

/-- ★★ **Finite tangential order** of the chart-face distribution. -/
theorem faceDistribution_bound (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) (f : 𝓓((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ)) {M : ℝ}
    (hT : TangentialJetBound (X.faceOrder P μ) (baseBox (X.act P.1) (X.T.a P.1)) (X.tangBox P J)
      f M) :
    |X.faceDistribution P J a μ q f| ≤ X.faceConst P J a μ q * M :=
  X.abs_faceFunctional_le P J a μ q f.contDiff hT

/-- ★★ **Support**: the chart-face distribution is supported in the closed face box. -/
theorem dsupport_faceDistribution_subset (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) :
    Distribution.dsupport (X.faceDistribution P J a μ q) ⊆ X.faceBox P J :=
  Distribution.dsupport_subset_of_forall_eqOn_zero (X.isCompact_faceBox P J).isClosed
    fun f ⟨_, hUo, hKU, h0⟩ => X.faceFunctional_eq_zero_of_eqOn_zero P J a μ q f.contDiff hUo hKU h0

theorem isCompact_dsupport_faceDistribution (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) :
    IsCompact (Distribution.dsupport (X.faceDistribution P J a μ q)) :=
  Distribution.isCompact_dsupport_of_forall_eqOn_zero (X.isCompact_faceBox P J)
    fun f ⟨_, hUo, hKU, h0⟩ => X.faceFunctional_eq_zero_of_eqOn_zero P J a μ q f.contDiff hUo hKU h0

end BridgeInputs

end SmoothEngine

end Grammar
