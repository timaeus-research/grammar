/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PositiveUnitRangePartition
import Grammar.ScalarCellNonneg

/-!
# The variable-unit box kernel

Unit 2a of consult #81 (`tide-log/gpt6_bigpicture_v81.md`): the box kernel with a phase unit
`u(z, v)` depending on the normal coordinates,
`varBoxKernel z N = ∫_{(0,b]^{n+1}} A(z,v) ∏ v^h e^{−N u(z,v) ∏ v^{2k}} dv`, and its face
coefficient `varBoxFaceCoeff = boxFaceCoeff` of the amplitude `A · u^{−λ}` (the unit frozen on the
minimal face by `faceProj`). Infrastructure for the comparison argument of unit 2b:

* a constant unit recovers the scalar-unit kernel and face coefficient (`scalarBoxKernel_const_eq`,
  `scalarBoxFaceCoeff_const`);
* **monotonicity in the unit** for a nonnegative amplitude (`varBoxKernel_anti_unit`: a larger unit
  on the support of the amplitude gives a smaller kernel);
* **linearity in the amplitude** for kernel and face coefficient (`varBoxKernel_sum`,
  `boxFaceCoeff_sum`, `boxFaceCoeff_const_mul`);
* boundedness, strong measurability and integrability against an integrable base weight
  (`abs_varBoxKernel_le_const`, `stronglyMeasurable_varBoxKernel`, `integrableOn_mul_varBoxKernel`,
  `integrableOn_mul_scalarBoxKernel`);
* **monotonicity and nonnegativity of the face coefficient** in the amplitude on the positive
  closed box (`boxFaceCoeff_mono`, `boxFaceCoeff_nonneg'`), with the face integrand integrable
  (`integrableOn_faceIntegrand`); these take `ContinuousOn` hypotheses on the positive closed box
  only, since the frozen-unit amplitude `A · u^{−λ}` is continuous only where `u > 0`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section VarKernel

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (b : ℝ) {t : ℕ}
  (u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **The variable-unit box kernel** `∫_{(0,b]^{n+1}} A(z,v) ∏ v^h e^{−N u(z,v) ∏ v^{2k}} dv`. -/
noncomputable def varBoxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ v in piBox (n + 1) (Ioc 0 b),
    A z v * (∏ i, v i ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))

/-- **The variable-unit face coefficient**: the box face coefficient of `A · u^{−λ}`, the unit
frozen on the minimal face. -/
noncomputable def varBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  boxFaceCoeff n h k 1 b (fun z v => A z v * u z v ^ (-l)) l z

variable {n h k b}

theorem scalarBoxKernel_const_eq (c : ℝ) (z : Fin t → ℝ) (N : ℝ) :
    scalarBoxKernel n h k b (fun _ => c) A z N = varBoxKernel n h k b (fun _ _ => c) A z N := by
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  unfold origPhaseIntegral varBoxKernel
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [mul_zero, add_zero]

theorem scalarBoxFaceCoeff_const (c l : ℝ) (z : Fin t → ℝ) :
    scalarBoxFaceCoeff n h k b (fun _ => c) A l z = c ^ (-l) * boxFaceCoeff n h k 1 b A l z := rfl

/-- The positive box `(0,b]^{n+1}` lies in the closed ball of radius `b`. -/
theorem piBox_Ioc_subset_closedBall (hb : 0 < b) :
    piBox (n + 1) (Ioc 0 b) ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) b := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hb.le).2 fun i => ?_
  have := hv i (mem_univ i)
  rw [Real.norm_eq_abs, abs_of_pos this.1]
  exact this.2

/-- **Monotonicity in the unit**: for a nonnegative amplitude, a unit larger on the support gives a
smaller kernel. -/
theorem varBoxKernel_anti_unit {u₁ u₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hA : Continuous (Function.uncurry A)) (hu₁ : Continuous (Function.uncurry u₁))
    (hu₂ : Continuous (Function.uncurry u₂)) {z : Fin t → ℝ}
    (hA0 : ∀ v ∈ piBox (n + 1) (Ioc 0 b), 0 ≤ A z v)
    (hle : ∀ v ∈ piBox (n + 1) (Ioc 0 b), A z v ≠ 0 → u₁ z v ≤ u₂ z v) {N : ℝ} (hN : 0 ≤ N) :
    varBoxKernel n h k b u₂ A z N ≤ varBoxKernel n h k b u₁ A z N := by
  unfold varBoxKernel
  have hAz : Continuous (A z) := continuous_amp_of_uncurry A hA z
  have hu₁z : Continuous (u₁ z) := continuous_amp_of_uncurry u₁ hu₁ z
  have hu₂z : Continuous (u₂ z) := continuous_amp_of_uncurry u₂ hu₂ z
  refine setIntegral_mono_on (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop))
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop)) measurableSet_piBox_Ioc_pos
    fun v hv => ?_
  by_cases hAv : A z v = 0
  · simp [hAv]
  have hu0 : ∀ i, 0 < v i := fun i => (hv i (mem_univ i)).1
  have hP : 0 ≤ ∏ i, v i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
  have hQ : 0 ≤ ∏ i, v i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hA0 v hv) hP)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle v hv hAv) hN) hQ

/-- **Linearity in the amplitude** of the kernel. -/
theorem varBoxKernel_sum {α : Type*} (s : Finset α)
    (As : α → (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (hAs : ∀ j ∈ s, Continuous (Function.uncurry (As j))) (hu : Continuous (Function.uncurry u))
    (z : Fin t → ℝ) (N : ℝ) :
    varBoxKernel n h k b u (fun z v => ∑ j ∈ s, As j z v) z N =
      ∑ j ∈ s, varBoxKernel n h k b u (As j) z N := by
  unfold varBoxKernel
  have huz : Continuous (u z) := continuous_amp_of_uncurry u hu z
  rw [← integral_finsetSum s fun j hj => integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by
    have := continuous_amp_of_uncurry (As j) (hAs j hj) z
    fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Finset.sum_mul]

/-- **Boundedness of the kernel** for a nonnegative unit and a bounded amplitude. -/
theorem abs_varBoxKernel_le_const (hb : 0 < b) {z : Fin t → ℝ} {M : ℝ}
    (hM : ∀ v ∈ piBox (n + 1) (Ioc 0 b), |A z v| ≤ M)
    (hu0 : ∀ v ∈ piBox (n + 1) (Ioc 0 b), 0 ≤ u z v) {N : ℝ} (hN : 0 ≤ N) :
    |varBoxKernel n h k b u A z N| ≤ M * b ^ (∑ i, h i) * b ^ (n + 1) := by
  unfold varBoxKernel
  have hvol : (volume : Measure (Fin (n + 1) → ℝ)) (piBox (n + 1) (Ioc 0 b)) < ⊤ :=
    lt_of_le_of_lt (measure_mono (pi_mono fun _ _ => Ioc_subset_Icc_self))
      ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top)
  have hreal : (volume : Measure (Fin (n + 1) → ℝ)).real (piBox (n + 1) (Ioc 0 b)) =
      b ^ (n + 1) := by
    rw [measureReal_def]
    unfold piBox
    rw [Real.volume_pi_Ioc, ENNReal.toReal_prod]
    simp only [sub_zero, ENNReal.toReal_ofReal hb.le, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hbound : ∀ v ∈ piBox (n + 1) (Ioc 0 b),
      ‖A z v * (∏ i, v i ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))‖ ≤
        M * b ^ (∑ i, h i) := by
    intro v hv
    have hv0 : ∀ i, 0 < v i := fun i => (hv i (mem_univ i)).1
    have hvb : ∀ i, v i ≤ b := fun i => (hv i (mem_univ i)).2
    have hP : 0 ≤ ∏ i, v i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hv0 i).le _
    have hPb : ∏ i, v i ^ h i ≤ b ^ (∑ i, h i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun i _ => pow_nonneg (hv0 i).le _) fun i _ =>
        pow_le_pow_left₀ (hv0 i).le (hvb i) _
    have hQ : 0 ≤ ∏ i, v i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hv0 i).le _
    have hexp : Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.2 (mul_nonneg (mul_nonneg (hu0 v hv) hN) hQ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hP, abs_of_pos (Real.exp_pos _)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM v hv)
    calc |A z v| * (∏ i, v i ^ h i) * Real.exp _ ≤ M * b ^ (∑ i, h i) * 1 :=
          mul_le_mul (mul_le_mul (hM v hv) hPb hP hM0) hexp (Real.exp_pos _).le
            (mul_nonneg hM0 (pow_nonneg hb.le _))
      _ = M * b ^ (∑ i, h i) := mul_one _
  have h := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [Real.norm_eq_abs, hreal] at h
  exact h

/-- The kernel is strongly measurable in the base point. -/
theorem stronglyMeasurable_varBoxKernel (hA : Continuous (Function.uncurry A))
    (hu : Continuous (Function.uncurry u)) (N : ℝ) :
    StronglyMeasurable fun z => varBoxKernel n h k b u A z N := by
  unfold varBoxKernel
  refine StronglyMeasurable.integral_prod_right' (f := fun p : (Fin t → ℝ) × (Fin (n + 1) → ℝ) =>
    A p.1 p.2 * (∏ i, p.2 i ^ h i) * Real.exp (-(u p.1 p.2 * N * ∏ i, p.2 i ^ (2 * k i)))) ?_
  refine Continuous.stronglyMeasurable ?_
  fun_prop

/-- **Integrability of the weighted kernel over a compact base** with a nonnegative unit. -/
theorem integrableOn_mul_varBoxKernel (hb : 0 < b) (hA : Continuous (Function.uncurry A))
    (hu : Continuous (Function.uncurry u)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hu0 : ∀ z ∈ T, ∀ v ∈ piBox (n + 1) (Ioc 0 b), 0 ≤ u z v) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun z => βw z * varBoxKernel n h k b u A z N) T := by
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  have hK : IsCompact (T ×ˢ piBox (n + 1) (Icc 0 b)) :=
    hT.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  have hbound : ∀ z ∈ T, |varBoxKernel n h k b u A z N| ≤ M * b ^ (∑ i, h i) * b ^ (n + 1) :=
    fun z hz => abs_varBoxKernel_le_const u A hb
      (fun v hv => hM (z, v) ⟨hz, pi_mono (fun _ _ => Ioc_subset_Icc_self) hv⟩) (hu0 z hz) hN
  refine Integrable.mono' (hβw.norm.const_mul (M * b ^ (∑ i, h i) * b ^ (n + 1)))
    (hβw.aestronglyMeasurable.mul
      (stronglyMeasurable_varBoxKernel u A hA hu N).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  calc |βw z| * |varBoxKernel n h k b u A z N|
      ≤ |βw z| * (M * b ^ (∑ i, h i) * b ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (hbound z hz) (abs_nonneg _)
    _ = M * b ^ (∑ i, h i) * b ^ (n + 1) * |βw z| := by ring

/-- Integrability of the weighted constant-unit kernel over a compact base. -/
theorem integrableOn_mul_scalarBoxKernel (hb : 0 < b) (hA : Continuous (Function.uncurry A))
    {T : Set (Fin t → ℝ)} (hT : IsCompact T) {c : ℝ} (hc : 0 ≤ c) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun z => βw z * scalarBoxKernel n h k b (fun _ => c) A z N) T := by
  have := integrableOn_mul_varBoxKernel (n := n) (h := h) (k := k) (fun _ _ => c) A hb hA
    continuous_const hT (fun _ _ _ _ => hc) hβw hN
  refine this.congr (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [scalarBoxKernel_const_eq]

end VarKernel

/-! ### The face coefficient: integrability, linearity, monotonicity -/

section Face

variable {n : ℕ} {h k : Fin (n + 1) → ℕ} (hk : ∀ i, 0 < k i) {l : ℝ}
  (hmin : ∀ i, l ≤ ratioExp h k i)

include hk hmin in
/-- The face integrand `η(faceProj w) residualWeight w` is integrable on the unit box for `η`
continuous on the closed cube. -/
theorem integrableOn_faceIntegrand {η : (Fin (n + 1) → ℝ) → ℝ}
    (hη : ContinuousOn η (closedCube (n + 1))) :
    IntegrableOn (fun w => η (faceProj h k l w) * residualWeight h k l w) (unitBox (n + 1)) := by
  have hcont : ContinuousOn (fun w => η (faceProj h k l w)) (unitBox (n + 1)) :=
    hη.comp (continuous_faceProj h k l).continuousOn (faceProj_mapsTo h k l)
  obtain ⟨M, hM⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hη
  have hrw := residualWeight_integrableOn h k hk l hmin
  refine Integrable.mono' (hrw.const_mul M)
    ((hcont.aestronglyMeasurable (measurableSet_unitBox _)).mul hrw.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (residualWeight_nonneg h k l w hw)]
  exact mul_le_mul_of_nonneg_right (hM _ (faceProj_mapsTo h k l hw))
    (residualWeight_nonneg h k l w hw)

include hk hmin in
/-- **Linearity of the face functional in the amplitude.** -/
theorem amplitudeCoeff_sum {α : Type*} (s : Finset α) (ηs : α → (Fin (n + 1) → ℝ) → ℝ)
    (hη : ∀ j ∈ s, ContinuousOn (ηs j) (closedCube (n + 1))) (β : ℝ) :
    amplitudeCoeff h k l β (fun v => ∑ j ∈ s, ηs j v) = ∑ j ∈ s, amplitudeCoeff h k l β (ηs j) := by
  unfold amplitudeCoeff
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum s fun j hj => integrableOn_faceIntegrand hk hmin (hη j hj)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [Finset.sum_mul]

variable {t : ℕ} {b : ℝ}

/-- The dilated amplitude `v ↦ A z (b • v)` is continuous on the closed cube when `A z` is
continuous on the positive closed box. -/
theorem continuousOn_dilate {A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    (hb : 0 ≤ b) (hA : ContinuousOn (A z) (piBox (n + 1) (Icc 0 b))) :
    ContinuousOn (fun v => A z (b • v)) (closedCube (n + 1)) := by
  refine hA.comp (continuous_const_smul b).continuousOn fun v hv i _ => ?_
  have := hv i (mem_univ i)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ⟨mul_nonneg hb this.1, by nlinarith [this.2]⟩

include hk hmin in
/-- **Linearity of the box face coefficient in the amplitude.** -/
theorem boxFaceCoeff_sum {α : Type*} (s : Finset α)
    (As : α → (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (hb : 0 ≤ b) {z : Fin t → ℝ}
    (hAs : ∀ j ∈ s, ContinuousOn (As j z) (piBox (n + 1) (Icc 0 b))) (β : ℝ) :
    boxFaceCoeff n h k β b (fun z v => ∑ j ∈ s, As j z v) l z =
      ∑ j ∈ s, boxFaceCoeff n h k β b (As j) l z := by
  unfold boxFaceCoeff
  change b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
    amplitudeCoeff h k l β (fun v => ∑ j ∈ s, As j z (b • v)) = _
  rw [amplitudeCoeff_sum hk hmin s (fun j v => As j z (b • v))
    (fun j hj => continuousOn_dilate hb (hAs j hj)) β, Finset.mul_sum]

/-- Homogeneity of the box face coefficient in the amplitude. -/
theorem boxFaceCoeff_const_mul (c : ℝ) (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (β : ℝ)
    (z : Fin t → ℝ) :
    boxFaceCoeff n h k β b (fun z v => c * A z v) l z = c * boxFaceCoeff n h k β b A l z := by
  unfold boxFaceCoeff
  rw [amplitudeCoeff_smul (η := fun v => A z (b • v))]
  ring

include hk hmin in
/-- **Monotonicity of the box face coefficient in the amplitude** (on the positive closed box). -/
theorem boxFaceCoeff_mono (hl : 0 < l) {β : ℝ} (hβ : 0 < β) (hb : 0 < b)
    {A₁ A₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    (hA₁ : ContinuousOn (A₁ z) (piBox (n + 1) (Icc 0 b)))
    (hA₂ : ContinuousOn (A₂ z) (piBox (n + 1) (Icc 0 b)))
    (hle : ∀ v ∈ piBox (n + 1) (Icc 0 b), A₁ z v ≤ A₂ z v) :
    boxFaceCoeff n h k β b A₁ l z ≤ boxFaceCoeff n h k β b A₂ l z := by
  unfold boxFaceCoeff amplitudeCoeff
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
    (faceLeadConst_pos h k hk l β hl hβ).le)
    (mul_nonneg (pow_nonneg hb.le _) (Real.rpow_nonneg (pow_nonneg hb.le _) _))
  refine setIntegral_mono_on
    (integrableOn_faceIntegrand hk hmin (continuousOn_dilate hb.le hA₁))
    (integrableOn_faceIntegrand hk hmin (continuousOn_dilate hb.le hA₂))
    (measurableSet_unitBox _) fun w hw => ?_
  refine mul_le_mul_of_nonneg_right ?_ (residualWeight_nonneg h k l w hw)
  refine hle _ fun i _ => ?_
  have hf := faceProj_mapsTo h k l hw i (mem_univ i)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ⟨mul_nonneg hb.le hf.1, by nlinarith [hf.2]⟩

include hk hmin in
/-- **Nonnegativity of the box face coefficient** for an amplitude nonnegative on the positive
closed box. -/
theorem boxFaceCoeff_nonneg' (hl : 0 < l) {β : ℝ} (hβ : 0 < β) (hb : 0 < b)
    {A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    (hA : ContinuousOn (A z) (piBox (n + 1) (Icc 0 b)))
    (h0 : ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 ≤ A z v) :
    0 ≤ boxFaceCoeff n h k β b A l z := by
  have hzero : boxFaceCoeff n h k β b (fun _ _ => (0 : ℝ)) l z = 0 := by
    have := boxFaceCoeff_const_mul (h := h) (k := k) (l := l) (b := b) 0 A β z
    simp only [zero_mul] at this
    exact this
  rw [← hzero]
  exact boxFaceCoeff_mono hk hmin hl hβ hb continuousOn_const hA h0

end Face

end Grammar
