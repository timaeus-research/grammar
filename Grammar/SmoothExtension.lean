/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetProducer

/-!
# Smooth extension: neighbourhood smoothness suffices (consult #117 §8, optional refinement)

The smooth producer `SmoothSheetInputs.hasSmoothCoordFreeExpansion` asks for a GLOBALLY smooth
prior and observable. Here we remove that: by the smooth Urysohn lemma on a finite-dimensional
space (`exists_contDiff_zero_one_nhds`, from Mathlib's manifold partition of unity), a function
smooth on an open set `U` agrees on any closed `C ⊆ U` with a globally smooth function
(`exists_contDiff_eqOn_of_contDiffOn`), preserving nonnegativity. `SmoothSheetNhdsInputs` packages
the producer's inputs with prior and observable smooth only on an open neighbourhood of the closed
domain `W`; `toInputs` extends them, and since the partition function only sees values on `W`,
★★ `hasSmoothCoordFreeExpansion` gives the smooth coordinate-free expansion of the ORIGINAL
`∫_W prior·obs·e^{−NK}`, with the same intrinsic coefficients (`coeff_eq_of_inputs`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling

namespace Grammar

section Urysohn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth Urysohn on a finite-dimensional space: a smooth `χ : E → [0,1]` vanishing near the
closed set `s` and equal to `1` near the closed set `t`, for disjoint `s, t`. -/
theorem exists_contDiff_zero_one_nhds {s t : Set E} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ᶠ x in 𝓝ˢ s, χ x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, χ x = 1) ∧
      ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨f, h0, h1, h01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E) (n := (⊤ : ℕ∞)) hs ht hd
  exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, h0, h1, h01⟩

open Classical in
/-- Smooth extension: a function smooth on an open set `U` agrees on a closed `C ⊆ U` with a
globally smooth function; if it is nonnegative on `U`, the extension is nonnegative everywhere. -/
theorem exists_contDiff_eqOn_of_contDiffOn {f : E → ℝ} {U C : Set E} (hU : IsOpen U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ EqOn g f C ∧ ((∀ x ∈ U, 0 ≤ f x) → ∀ x, 0 ≤ g x) := by
  obtain ⟨χ, hχ, h0, h1, h01⟩ := exists_contDiff_zero_one_nhds (E := E) hU.isClosed_compl hC
    (disjoint_compl_left_iff_subset.mpr hCU)
  obtain ⟨V, hVo, hVU, hV0⟩ := eventually_nhdsSet_iff_exists.mp h0
  refine ⟨fun x => if x ∈ U then χ x * f x else 0, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · have hcongr : (fun y => if y ∈ U then χ y * f y else 0) =ᶠ[𝓝 x] fun y => χ y * f y :=
        eventually_of_mem (hU.mem_nhds hx) fun y hy => by simp [hy]
      exact ((hχ.contDiffAt).mul ((hf x hx).contDiffAt (hU.mem_nhds hx))).congr_of_eventuallyEq
        hcongr
    · have hcongr : (fun y => if y ∈ U then χ y * f y else 0) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        eventually_of_mem (hVo.mem_nhds (hVU hx)) fun y hy => by
          by_cases hyU : y ∈ U
          · simp [hyU, hV0 y hy]
          · simp [hyU]
      exact contDiffAt_const.congr_of_eventuallyEq hcongr
  · intro x hx
    have h1x := (eventually_nhdsSet_iff_forall.mp h1) x hx
    simp only [hCU hx, if_true, h1x.self_of_nhds, one_mul]
  · intro hf0 x
    by_cases hx : x ∈ U
    · simp only [hx, if_true]
      exact mul_nonneg (h01 x).1 (hf0 x hx)
    · simp [hx]

end Urysohn

namespace SmoothEngine

/-- The producer's inputs with the prior and the observable smooth only on an open neighbourhood
`U` of the closed domain `W` (and the prior nonnegative only on `U`). -/
structure SmoothSheetNhdsInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  K_m : Measurable K
  /-- the resolved set of the atlas -/
  Ω : Set (Fin d → ℝ)
  /-- the weighted domain atlas -/
  A : WeightedDomainAtlas d K Ω
  /-- the half side of the chart boxes -/
  a : ℝ
  ha : 0 < a
  lo_eq : ∀ i j, A.lo i j = -a
  hi_eq : ∀ i j, A.hi i j = a
  /-- the phase is nonnegative on the domain -/
  K_nonneg : ∀ w ∈ A.W, 0 ≤ K w
  /-- an open neighbourhood of the closed domain -/
  U : Set (Fin d → ℝ)
  U_open : IsOpen U
  W_closed : IsClosed A.W
  W_sub : A.W ⊆ U
  /-- the prior and the observable, smooth on `U` only -/
  prior : (Fin d → ℝ) → ℝ
  obs : (Fin d → ℝ) → ℝ
  prior_nonneg : ∀ w ∈ U, 0 ≤ prior w
  prior_smooth : ContDiffOn ℝ ∞ prior U
  obs_smooth : ContDiffOn ℝ ∞ obs U
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  /-- smooth chart data -/
  φ_smooth : ∀ i, ContDiff ℝ ∞ (A.φ i)
  ω_smooth : ∀ i, ContDiff ℝ ∞ (A.ω i)
  jacAbs_smooth : ∀ i, ContDiff ℝ ∞ fun y => |A.jacUnit i y|
  /-- the phase unit is tangential -/
  hu_tan : ∀ i (w w' : Fin d → ℝ), (∀ j, ¬ 0 < A.k i j → w j = w' j) →
    A.phaseUnit i w = A.phaseUnit i w'

namespace SmoothSheetNhdsInputs

variable {d : ℕ} (X : SmoothSheetNhdsInputs d)

/-- The chosen smooth extension of the prior. -/
noncomputable def priorExt : (Fin d → ℝ) → ℝ :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub X.prior_smooth).choose

theorem priorExt_smooth : ContDiff ℝ ∞ X.priorExt :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub X.prior_smooth).choose_spec.1

theorem priorExt_eqOn : EqOn X.priorExt X.prior X.A.W :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub
    X.prior_smooth).choose_spec.2.1

theorem priorExt_nonneg (w : Fin d → ℝ) : 0 ≤ X.priorExt w :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub
    X.prior_smooth).choose_spec.2.2 X.prior_nonneg w

/-- The chosen smooth extension of the observable. -/
noncomputable def obsExt : (Fin d → ℝ) → ℝ :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub X.obs_smooth).choose

theorem obsExt_smooth : ContDiff ℝ ∞ X.obsExt :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub X.obs_smooth).choose_spec.1

theorem obsExt_eqOn : EqOn X.obsExt X.obs X.A.W :=
  (exists_contDiff_eqOn_of_contDiffOn X.U_open X.W_closed X.W_sub X.obs_smooth).choose_spec.2.1

/-- The prior measures of the original and the extended prior agree (both live on `W`). -/
theorem withDensity_priorExt_eq :
    (volume.restrict X.A.W).withDensity (fun w => ENNReal.ofReal (X.priorExt w)) =
      (volume.restrict X.A.W).withDensity fun w => ENNReal.ofReal (X.prior w) := by
  apply withDensity_congr_ae
  exact (ae_restrict_mem X.A.measurableSet_W).mono fun w hw => by
    beta_reduce
    rw [X.priorExt_eqOn hw]

theorem obsExt_int : Integrable X.obsExt
    ((volume.restrict X.A.W).withDensity fun w => ENNReal.ofReal (X.priorExt w)) := by
  rw [X.withDensity_priorExt_eq]
  refine X.obs_int.congr ?_
  have h : ∀ᵐ w ∂(volume.restrict X.A.W), X.obs w = X.obsExt w :=
    (ae_restrict_mem X.A.measurableSet_W).mono fun w hw => (X.obsExt_eqOn hw).symm
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- The globally smooth inputs obtained by extending the prior and the observable. -/
noncomputable def toInputs : SmoothSheetInputs d where
  K := X.K
  K_m := X.K_m
  Ω := X.Ω
  A := X.A
  a := X.a
  ha := X.ha
  lo_eq := X.lo_eq
  hi_eq := X.hi_eq
  K_nonneg := X.K_nonneg
  prior := X.priorExt
  obs := X.obsExt
  prior_nonneg := X.priorExt_nonneg
  prior_smooth := X.priorExt_smooth
  obs_smooth := X.obsExt_smooth
  obs_int := X.obsExt_int
  φ_smooth := X.φ_smooth
  ω_smooth := X.ω_smooth
  jacAbs_smooth := X.jacAbs_smooth
  hu_tan := X.hu_tan

/-- The partition function only sees the values on `W`. -/
theorem globalLaplace_eq (N : ℝ) :
    globalLaplace X.A.W X.K (fun w => X.prior w * X.obs w) N =
      globalLaplace X.A.W X.K (fun w => X.toInputs.prior w * X.toInputs.obs w) N := by
  unfold globalLaplace
  refine setIntegral_congr_fun X.A.measurableSet_W fun w hw => ?_
  simp only [toInputs, X.priorExt_eqOn hw, X.obsExt_eqOn hw]

/-- ★★ The smooth coordinate-free expansion of `∫_W prior·obs·e^{−NK}` with the prior and the
observable smooth only on an open neighbourhood of the closed domain `W`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w)
      X.toInputs.decomp.coeff X.toInputs.decomp.commonQ X.toInputs.decomp.commonD := by
  have h := X.toInputs.hasSmoothCoordFreeExpansion
  have hZ : (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) =
      globalLaplace X.toInputs.A.W X.toInputs.K fun w => X.toInputs.prior w * X.toInputs.obs w :=
    funext X.globalLaplace_eq
  rwa [hZ]

/-- The certificate for the original partition function. -/
noncomputable def certificate :
    SmoothExpansionCertificate (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) where
  Q := X.toInputs.decomp.commonQ
  Q_pos := X.toInputs.decomp.commonQ_pos
  D := X.toInputs.decomp.commonD
  coeff := X.toInputs.decomp.coeff
  coeff_support := X.toInputs.certificate.coeff_support
  expansion := by
    have h := X.toInputs.certificate.expansion
    have hZ : (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) =
        globalLaplace X.toInputs.A.W X.toInputs.K fun w =>
          X.toInputs.prior w * X.toInputs.obs w :=
      funext X.globalLaplace_eq
    rwa [hZ]

/-- The coefficients are those of ANY globally smooth inputs with the same domain, phase, and
the same prior and observable on `W` (presentation independence). -/
theorem coeff_eq_of_inputs {Y : SmoothSheetInputs d} (hW : X.A.W = Y.A.W) (hK : X.K = Y.K)
    (hprior : EqOn X.prior Y.prior X.A.W) (hobs : EqOn X.obs Y.obs X.A.W) (μ : ℝ) (q : ℕ) :
    X.toInputs.decomp.coeff μ q = Y.decomp.coeff μ q := by
  have hZ : (globalLaplace Y.A.W Y.K fun w => Y.prior w * Y.obs w) =
      globalLaplace X.A.W X.K fun w => X.prior w * X.obs w := by
    funext N
    unfold globalLaplace
    rw [← hW, ← hK]
    exact setIntegral_congr_fun X.A.measurableSet_W fun w hw => by
      beta_reduce
      rw [hprior hw, hobs hw]
  let C₂ : SmoothExpansionCertificate (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) :=
    { Q := Y.decomp.commonQ, Q_pos := Y.decomp.commonQ_pos, D := Y.decomp.commonD
      coeff := Y.decomp.coeff, coeff_support := Y.certificate.coeff_support
      expansion := by
        have h : CutoffExpansion Y.decomp.commonQ Y.decomp.commonD
            (globalLaplace Y.A.W Y.K fun w => Y.prior w * Y.obs w) Y.decomp.coeff :=
          Y.certificate.expansion
        rwa [hZ] at h }
  exact SmoothExpansionCertificate.coeff_eq X.certificate C₂ μ q

end SmoothSheetNhdsInputs

end SmoothEngine

end Grammar
