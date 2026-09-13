/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartCollarDecomposition
import Grammar.CoordFreeExpansionCompletion

/-!
# The certificate of a chart box with a tangential unit and Jacobian weight (unit E, part 2)

The collar decomposition of `ChartCollarDecomposition` is assembled into a `ResolvedCertificate`
on the chart model (CCCXLIII): the bases `baseStratum I ⊆ S_I`, the frames
`u ↦ Σ_{i∈I} λ_{I,i}(s) u_{σ⁻¹ i} e_i` into the coordinate normal spaces `N_I = span{e_i : i ∈ I}`
(`frameI`), the tubular identity `Φ_eq_frame`, the normal-moment presentations of the weighted
cores (E2), and the coefficient certificate with density family `J H L · fϕ` and observable jets
`fφ`. Hence ★★★ `hasCoordFreeExpansion_chart`: for a chart with active set `A`, orders `(k, h)`,
positive tangential unit `u ≥ c` on `[0,a]^d` and local normal series of the prior and the
observable at every stratum, the weighted integral
`∫_{[0,a]^d} φ · ∏|y_i|^{h_i} ϕ · e^{−n u ∏ y^{2k}}` has the coordinate-free expansion on the
chart strata. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace ChartCollar

open NormalisedBox WaterFilling CoordModel CoeffFamily

variable {d : ℕ} (A : Finset (Fin d)) (k h : Fin d → ℕ) (hkA : ∀ i ∈ A, 0 < k i)
  (hk0 : ∀ i, i ∉ A → k i = 0) (u : (Fin d → ℝ) → ℝ) (a δ : ℝ) (hδ : 0 < δ) (hu_cont : Continuous u)
  (ϕ φ : (Fin d → ℝ) → ℝ)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 < a)
  (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
  (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
  (hφint : Integrable φ ((volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt h w * ϕ w)))
  (F : ∀ I : Idx A, FaceSeries A k h hkA u a δ ϕ φ I)

/-! ### The frames -/

section Frame

include hk0 hδ hc hu_lb ha in
/-- The frame as a linear equivalence: `u ↦ Σ_i λ_{I,i}(s) u_{σ⁻¹ i} e_i`. -/
noncomputable def frameLin (I : Idx A) (s : KI A k h hkA u a δ I) :
    (Fin (nI A I + 1) → ℝ) ≃ₗ[ℝ] normalSpace d (amb A I) :=
  ((LinearEquiv.funCongrLeft ℝ ℝ (σI A I)).symm.trans
    (LinearEquiv.piCongrRight fun j : Nrm (amb A I) =>
      LinearEquiv.smulOfNeZero ℝ ℝ (lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j)
        (lamT_pos_of_mem_baseSet A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) hδ hc hu_lb ha.le
          s.2 j).ne')).trans
    (Module.Basis.span (linearIndependent_basisVec_restrict d (amb A I))).equivFun.symm

include hk0 hδ hc hu_lb ha in
theorem frameLin_apply (I : Idx A) (s : KI A k h hkA u a δ I) (v : Fin (nI A I + 1) → ℝ) :
    frameLin A k h hkA hk0 u a δ hδ hc hu_lb ha I s v =
      ∑ j : Nrm (amb A I), (lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j * v ((σI A I).symm j)) •
        Module.Basis.span (linearIndependent_basisVec_restrict d (amb A I)) j := by
  change (Module.Basis.span (linearIndependent_basisVec_restrict d (amb A I))).equivFun.symm
    (fun j => lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j * v ((σI A I).symm j)) = _
  rw [Module.Basis.equivFun_symm_apply]

include hk0 hδ hc hu_lb ha in
theorem coe_frameLin_apply (I : Idx A) (s : KI A k h hkA u a δ I) (v : Fin (nI A I + 1) → ℝ)
    (i : Fin d) :
    ((frameLin A k h hkA hk0 u a δ hδ hc hu_lb ha I s v : normalSpace d (amb A I)) : Amb d).ofLp i =
      if hi : i ∈ amb A I then
        lamT k u (amb A I) δ (eI A k h hkA u a δ I s) ⟨i, hi⟩ * v ((σI A I).symm ⟨i, hi⟩)
      else 0 := by
  rw [frameLin_apply, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]
  have hterm : ∀ j : Nrm (amb A I),
      ((((lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j * v ((σI A I).symm j)) •
        Module.Basis.span (linearIndependent_basisVec_restrict d (amb A I)) j :
          normalSpace d (amb A I)) : Amb d)).ofLp i =
        (lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j * v ((σI A I).symm j)) *
          if i = j.1 then 1 else 0 := by
    intro j
    rw [Submodule.coe_smul, Module.Basis.span_apply]
    change ((lamT k u (amb A I) δ (eI A k h hkA u a δ I s) j * v ((σI A I).symm j)) •
      basisVec d j.1).ofLp i = _
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  by_cases hi : i ∈ amb A I
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      exact fun h => hj (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    exact fun h => hi (h ▸ j.2)

include hk0 hδ hc hu_lb ha in
/-- The frame `ℝ^{|I|} ≃L N_I` at the base point `s`. -/
noncomputable def frameI (I : Idx A) (s : KI A k h hkA u a δ I) :
    (Fin (nI A I + 1) → ℝ) ≃L[ℝ] normalSpace d (amb A I) :=
  (frameLin A k h hkA hk0 u a δ hδ hc hu_lb ha I s).toContinuousLinearEquiv

include hk0 hδ hc hu_lb ha in
theorem coe_frameI_apply (I : Idx A) (s : KI A k h hkA u a δ I) (v : Fin (nI A I + 1) → ℝ)
    (i : Fin d) :
    ((frameI A k h hkA hk0 u a δ hδ hc hu_lb ha I s v : normalSpace d (amb A I)) : Amb d).ofLp i =
      if hi : i ∈ amb A I then
        lamT k u (amb A I) δ (eI A k h hkA u a δ I s) ⟨i, hi⟩ * v ((σI A I).symm ⟨i, hi⟩)
      else 0 :=
  coe_frameLin_apply A k h hkA hk0 u a δ hδ hc hu_lb ha I s v i

include hk0 hδ hc hu_lb ha in
/-- ★ **The tubular identity along the frame**: the core parametrisation `s + Σ λ_i v_i e_i` is the
chart model's tubular germ `s + ξ` at `ξ = frame v`. -/
theorem Φ_eq_frame (I : Idx A) (s : KI A k h hkA u a δ I) (v : Fin (nI A I + 1) → ℝ) :
    Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v) =
      (ChartModel.normalData d A k h hkA).Φ I.1 s.1
        (frameI A k h hkA hk0 u a δ hδ hc hu_lb ha I s v) := by
  change _ = fun i => s.1.1 i +
    ((frameI A k h hkA hk0 u a δ hδ hc hu_lb ha I s v : normalSpace d (amb A I)) : Amb d).ofLp i
  funext j
  rw [Φ_apply, coe_frameI_apply]
  by_cases hj : j ∈ amb A I
  · rw [dif_pos hj, dif_pos hj, stratum_coord_zero A k h hkA s.1 hj, zero_add]
  · rw [dif_neg hj, dif_neg hj, add_zero]
    rfl

end Frame

/-! ### The certificate -/

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
/-- ★★ **The resolved certificate of the chart box**: the collar decomposition against the
chart-model normal data, with the frames along the unit-corrected widths; prior `∏|y_i|^{h_i} ϕ`,
phase `u · ∏_{i∈A} y_i^{2k_i}`. -/
noncomputable def certificate (hA : A.Nonempty) :
    ResolvedCertificate (ChartModel.geometry d A k h hkA) (ChartModel.normalData d A k h hkA)
      (piBox d (Icc 0 a)) (ChartModel.phase d A k u) (fun w => wgt h w * ϕ w) φ := by
  have := fun I => compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact {
    L := locData A k h u a hu_cont ϕ φ hc hu_lb hφint
    obs_eq := rfl
    phase_eq := rfl
    transport := by
      change Measure.map id _ = _
      rw [Measure.map_id]
      rfl
    M := numCores A
    n := fun i => nI A (coreIdx A i)
    strat := fun i => (coreIdx A i).1
    base := fun i => baseStratum A k h hkA u a δ (coreIdx A i)
    isCompact_base := fun i => isCompact_baseStratum A k h hkA u a δ hδ hu_cont (coreIdx A i)
    β := 1
    β_pos := one_pos
    cores := collar A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F hA
    T := fun i => NormalisedBox.wpresentation (hkI A k hkA (coreIdx A i)) (measurableSet_W a) hϕm
      (fun w _ => hϕ0 w) (locData A k h u a hu_cont ϕ φ hc hu_lb hφint)
      (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa (F (coreIdx A i))) (h := h) rfl
      (locData_phase A k h hk0 u a hu_cont ϕ φ hu_tan hc hu_lb hφint (coreIdx A i)) rfl
    frame := fun i s => frameI A k h hkA hk0 u a δ hδ hc hu_lb ha (coreIdx A i) s
    Φ_eq := fun i s v => Φ_eq_frame A k h hkA hk0 u a δ hδ hc hu_lb ha (coreIdx A i) s v }

/-! ### The coefficient certificate -/

include hk0 hδ hu_cont hc hu_lb ha hδa in
theorem cc_abs_aux (I : Idx A) (s : KI A k h hkA u a δ I) :
    AbsSummableAt (fun γ => JW h (amb A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) s *
      (F I).Fϕ.f s γ) (side k (amb A I) δ) := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact ((F I).Fϕ.smul (JW h (amb A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ))
    (continuous_JW h (amb A I) _ (continuous_eI A k h hkA u a δ I) _
      (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa (F I)).hlam_cont) _
    (abs_JW_le h (amb A I) _ (continuous_eI A k h hkA u a δ I) _
      (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa
        (F I)).hlam_cont)).absSummableAt_of_le
    (side_pos k _ δ hδ).le (by linarith [side_pos k (amb A I) δ hδ]) s

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
theorem jetFamily_stratumCore (I : Idx A) (s : KI A k h hkA u a δ I) :
    jetFamily (nI A I) ((stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm
      hϕ0 hφint F I).obsFibre s) = (F I).Fφ.f s := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact NormalisedBox.jetFamily_obsFibre_w (hkI A k hkA I) (measurableSet_W a) hϕm
    (fun w _ => hϕ0 w) (locData A k h u a hu_cont ϕ φ hc hu_lb hφint)
    (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa (F I)) (h := h) rfl
    (locData_phase A k h hk0 u a hu_cont ϕ φ hu_tan hc hu_lb hφint I) rfl s

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
theorem toEta_stratumCore (I : Idx A) (s : KI A k h hkA u a δ I) :
    toEta (side k (amb A I) δ) ((stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha
      hδa hϕm hϕ0 hφint F I).x s) =
      CoeffFamily.conv (fun γ => JW h (amb A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) s *
        (F I).Fϕ.f s γ) ((F I).Fφ.f s) := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  exact NormalisedBox.toEta_wcore_x (hkI A k hkA I) (measurableSet_W a) hϕm
    (fun w _ => hϕ0 w) (locData A k h u a hu_cont ϕ φ hc hu_lb hφint)
    (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa (F I)) (h := h) rfl
    (locData_phase A k h hk0 u a hu_cont ϕ φ hu_tan hc hu_lb hφint I) rfl s

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint in
/-- ★★ **The coefficient certificate**: density family `J H L · fϕ`, observable jets `fφ`. -/
noncomputable def coeffCertificate (hA : A.Nonempty) :
    (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F
      hA).CoefficientCertificate where
  cc := fun i s γ => JW h (amb A (coreIdx A i)) (eI A k h hkA u a δ (coreIdx A i))
    (lamT k u (amb A (coreIdx A i)) δ) s * (F (coreIdx A i)).Fϕ.f s γ
  cc_abs := fun i s =>
    cc_abs_aux A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb ha hδa F (coreIdx A i) s
  jet_abs := fun i s => by
    have hj := jetFamily_stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm
      hϕ0 hφint F (coreIdx A i) s
    exact (congrArg (fun f => AbsSummableAt f (side k (amb A (coreIdx A i)) δ)) hj).mpr
      ((F (coreIdx A i)).Fφ.absSummableAt_of_le (side_pos k _ δ hδ).le
        (by linarith [side_pos k (amb A (coreIdx A i)) δ hδ]) s)
  datum_eq := fun i s => by
    have hj := jetFamily_stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm
      hϕ0 hφint F (coreIdx A i) s
    have h1 := toEta_stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0
      hφint F (coreIdx A i) s
    exact h1.trans (congrArg (CoeffFamily.conv _) hj.symm)

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint in
/-- ★★★ **The coordinate-free expansion of a chart box with a tangential unit and Jacobian
weight**: for a chart with active set `A`, orders `(k, h)` (`k > 0` on `A`, `k = 0` off `A`), a
positive tangential unit `u ≥ c` on `[0,a]^d` and local normal series of the prior `ϕ` and the
observable `φ` at every nonempty active stratum, the weighted integral
`∫_{[0,a]^d} φ · ∏_i |y_i|^{h_i} ϕ · e^{−n u(y) ∏_{i∈A} y_i^{2k_i}}` has the coordinate-free
expansion on the chart strata `S_I`, `∅ ≠ I ⊆ A`, with produced certificates. -/
theorem hasCoordFreeExpansion_chart (hA : A.Nonempty) :
    (ChartModel.normalData d A k h hkA).HasCoordFreeExpansion
      (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F
        hA).stratumMeasure
      (coeffCertificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F
        hA).field
      (spectrumLe (commonQ (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa
        hϕm hϕ0 hφint F hA).cores.k)
        (commonD (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0
          hφint F hA).n))
      (piBox d (Icc 0 a)) (ChartModel.phase d A k u) (fun w => wgt h w * ϕ w) φ :=
  (coeffCertificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint F
    hA).hasCoordFreeExpansion_le (hu_cont.measurable.mul (ChartModel.measurable_monoPhase d A k))
    ((measurable_wgt _).mul hϕm) (fun w => mul_nonneg (wgt_nonneg _ _) (hϕ0 w)) hφm

end ChartCollar

end Grammar
