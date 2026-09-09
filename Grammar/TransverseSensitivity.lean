/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialSecondCoeffExplicit

/-!
# Face versus transverse phase sensitivity at order `1/L` (unit 369; Astra #45 unit 4)

Let `ξ̄ = ξ ∘ P_J` be the face restriction of the phase.  At leading order only `ξ̄` matters
(`spatialFace_congr_face`, Headline LXXII).  At the next order the two log-weighted and
`J̇`-terms of `B` cancel between `ξ` and `ξ̄`, leaving the **transverse increment**
```
B(ξ,η) − B(ξ̄,η) = (1/((m−2)! ∏_{i∈J} 2kᵢ)) ∑_{i₀∈J} 2k_{i₀}
    ∫ w(u) ∫₀¹ η(P_J u + t e_{i₀}) [J_λ(ξ(P_J u + t e_{i₀})) − J_λ(ξ(P_J u))] dt/t du
```
(`spatialSecondFace_sub_face`).  The identity is proved at the coefficient level: the face
restriction of the phase is represented by the face-restricted family (`faceRestrict`,
`evalF_faceRestrict`), the coefficient functionals are linear (`coeffFunctional_sub`), and the
difference of the dressed families vanishes on the face, so only the transverse part of
`coeffFunctional_second_eq` survives.  Consequences: equality of the phases on every
one-coordinate stratum `P_{J∖{i₀}}` gives equal second coefficients
(`spatialSecondFace_congr_strata`);
with nonnegative amplitude a transverse phase increase gives a nonnegative correction
(`spatialSecondFace_face_le`, via the monotonicity of `J_λ` in the phase,
`fluctMoment_mono_phase`); and the evidence with phase `ξ` differs from that with phase `ξ̄`
exactly at order `1/L`: `L(𝒵_N[η;ξ] − 𝒵_N[η;ξ̄])/(N^{-λ}L^{m-1}) → B(ξ,η) − B(ξ̄,η)`
(`spatialPhase_transverse_correction`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

variable {d : ℕ}

/-! ### The face projection is idempotent and absorbs transverse displacements -/

theorem faceProj_faceProj (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) :
    faceProj h k l (faceProj h k l u) = faceProj h k l u := by
  funext i
  simp only [faceProj]
  split_ifs <;> rfl

theorem faceProj_update (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) {i₀ : Fin d}
    (hi₀ : ratioExp h k i₀ = l) (t : ℝ) :
    faceProj h k l (Function.update (faceProj h k l u) i₀ t) = faceProj h k l u := by
  funext i
  simp only [faceProj]
  by_cases hi : ratioExp h k i = l
  · simp [hi]
  · have hne : i ≠ i₀ := fun h' => hi (h' ▸ hi₀)
    simp [hi, Function.update_of_ne hne, faceProj]

/-! ### The face-restricted family -/

open Classical in
/-- The face restriction of a coefficient family: the coefficients with `γ_J ≠ 0` removed. -/
noncomputable def faceRestrict (h k : Fin d → ℕ) (l : ℝ) (c : CoeffFamily d) : CoeffFamily d :=
  fun γ => if faceZero h k l γ then c γ else 0

theorem absSummable_faceRestrict (h k : Fin d → ℕ) (l : ℝ) {c : CoeffFamily d}
    (hc : AbsSummable c) : AbsSummable (faceRestrict h k l c) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun γ => by
    unfold faceRestrict
    split_ifs <;> simp) hc

theorem faceRestrict_zero (h k : Fin d → ℕ) (l : ℝ) (c : CoeffFamily d) :
    faceRestrict h k l c 0 = c 0 := by
  unfold faceRestrict
  rw [if_pos (show faceZero h k l 0 from fun i _ => rfl)]

open Classical in
theorem mono_faceProj_eq (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) (u : Fin d → ℝ) :
    mono γ (faceProj h k l u) = if faceZero h k l γ then mono γ u else 0 := by
  unfold mono faceProj
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · simp [hi, hf i hi]
    · simp [hi]
  · rw [if_neg hf]
    unfold faceZero at hf
    push Not at hf
    obtain ⟨i, hi, hγ⟩ := hf
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hγ])

/-- The face-restricted family represents the face restriction of the function. -/
theorem evalF_faceRestrict (h k : Fin d → ℕ) (l : ℝ) (c : CoeffFamily d) (u : Fin d → ℝ) :
    evalF (faceRestrict h k l c) u = evalF c (faceProj h k l u) := by
  unfold evalF faceRestrict
  refine tsum_congr fun γ => ?_
  rw [mono_faceProj_eq]
  split_ifs <;> simp

/-! ### Linearity of the coefficient functionals -/

theorem coeffFunctional_sub (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (j : ℕ)
    {f g : CoeffFamily (n + 1)} (hf : AbsSummable f) (hg : AbsSummable g) :
    coeffFunctional n h k l j (f - g) =
      coeffFunctional n h k l j f - coeffFunctional n h k l j g := by
  unfold coeffFunctional
  rw [← mul_sub, ← (summable_mul_coeffAt n h k hk hf l j).tsum_sub
    (summable_mul_coeffAt n h k hk hg l j)]
  congr 1
  refine tsum_congr fun γ => ?_
  simp only [Pi.sub_apply]
  ring

/-! ### Monotonicity of `J_λ` in the phase -/

theorem phaseKernel_mono_phase (β : ℝ) (hβ : 0 < β) {a b : ℝ} (hab : a ≤ b) (p : ℕ) (t : ℝ) :
    phaseKernel β a p t ≤ phaseKernel β b p t := by
  unfold phaseKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (pow_nonneg (Real.sqrt_nonneg _) _)
  have : 0 ≤ β * Real.sqrt t := mul_nonneg hβ.le (Real.sqrt_nonneg _)
  nlinarith

/-- `J_λ` is nondecreasing in the phase. -/
theorem fluctMoment_mono_phase (β : ℝ) (hβ : 0 < β) {a b : ℝ} (hab : a ≤ b) {ν : ℝ} (hν : 0 < ν) :
    fluctMoment β a 0 ν 0 ≤ fluctMoment β b 0 ν 0 := by
  unfold fluctMoment
  refine setIntegral_mono_on (integrableOn_fluct β a hβ 0 hν 0) (integrableOn_fluct β b hβ 0 hν 0)
    measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := mem_Ioi.1 ht
  simp only [pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (phaseKernel_mono_phase β hβ hab 0 t)
    (Real.rpow_nonneg ht0.le _)

/-! ### The transverse increment of the second coefficient -/

/-- The transverse increment functional
`∑_{i₀∈J} 2k_{i₀} ∫ w ∫₀¹ η(P_J u + t e_{i₀}) [J_λ(ξ(P_J u + t e_{i₀})) − J_λ(ξ(P_J u))] dt/t`. -/
noncomputable def transverseIncrement (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
    ∑ i₀, if ratioExp h k i₀ = l then
      2 * (k i₀ : ℝ) * ∫ u in unitBox (d + 1), residualWeight h k l u *
        ∫ t in Ioc (0 : ℝ) 1, η (Function.update (faceProj h k l u) i₀ t) *
          (fluctMoment β (ξ (Function.update (faceProj h k l u) i₀ t)) 0 l 0 -
            fluctMoment β (ξ (faceProj h k l u)) 0 l 0) / t
    else 0

/-- **Face versus transverse phase, at the coefficient level**:
`A_{λ,m−2}(cξ,cη) − A_{λ,m−2}(faceRestrict cξ, cη)` is the transverse increment. -/
theorem spatialSecondCoeff_sub_faceRestrict (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    spatialSecondCoeff n h k β cξ cη l - spatialSecondCoeff n h k β (faceRestrict h k l cξ) cη l =
      transverseIncrement h k l β ξ η := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hξ' := absSummable_faceRestrict h k l hξ
  -- the face-restricted family represents `ξ ∘ P_J`
  have hξc' : Continuous (ξ ∘ faceProj h k l) := hξc.comp (continuous_faceProj h k l)
  have hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (faceRestrict h k l cξ) u =
      (ξ ∘ faceProj h k l) u := fun u _ => by
    rw [evalF_faceRestrict]
    exact evalF_eq_on_closedCube hξ hξc hevξ
      (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ ‹_›))
  set g0 := dressedFamily β cξ cη l 0 with hg0
  set g1 := dressedFamily β cξ cη l 1 with hg1
  set g0' := dressedFamily β (faceRestrict h k l cξ) cη l 0 with hg0'
  set g1' := dressedFamily β (faceRestrict h k l cξ) cη l 1 with hg1'
  have hs0 := absSummable_dressedFamily hβ hξ hη hl 0
  have hs1 := absSummable_dressedFamily hβ hξ hη hl 1
  have hs0' := absSummable_dressedFamily hβ hξ' hη hl 0
  have hs1' := absSummable_dressedFamily hβ hξ' hη hl 1
  -- evaluations of the differences on the closed cube
  have hev0 : ∀ v ∈ closedCube (n + 1), evalF (g0 - g0') v =
      η v * (fluctMoment β (ξ v) 0 l 0 - fluctMoment β (ξ (faceProj h k l v)) 0 l 0) := by
    intro v hv
    rw [evalF_sub hs0 hs0' hv, evalF_dressedFamily_eq n hβ hξ hη hξc hηc hevξ hevη hl 0 hv,
      evalF_dressedFamily_eq n hβ hξ' hη hξc' hηc hevξ' hevη hl 0 hv]
    unfold dressedAmplitude
    simp only [Function.comp_apply]
    ring
  have hev1 : ∀ v ∈ closedCube (n + 1), evalF (g1 - g1') v =
      η v * (fluctMoment β (ξ v) 0 l 1 - fluctMoment β (ξ (faceProj h k l v)) 0 l 1) := by
    intro v hv
    rw [evalF_sub hs1 hs1' hv, evalF_dressedFamily_eq n hβ hξ hη hξc hηc hevξ hevη hl 1 hv,
      evalF_dressedFamily_eq n hβ hξ' hη hξc' hηc hevξ' hevη hl 1 hv]
    unfold dressedAmplitude
    simp only [Function.comp_apply]
    ring
  unfold spatialSecondCoeff
  rw [if_pos hm, if_pos hm, familySpectralCoeff_second_eq_dressed n h k hk hβ hξ hη hmin hatt hm,
    familySpectralCoeff_second_eq_dressed n h k hk hβ hξ' hη hmin hatt hm]
  have hlin : coeffFunctional n h k l (multCount (ratioExp h k) l - 2) g0 +
      ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
        coeffFunctional n h k l (multCount (ratioExp h k) l - 1) g1 -
      (coeffFunctional n h k l (multCount (ratioExp h k) l - 2) g0' +
      ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
        coeffFunctional n h k l (multCount (ratioExp h k) l - 1) g1') =
      coeffFunctional n h k l (multCount (ratioExp h k) l - 2) (g0 - g0') +
      ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
        coeffFunctional n h k l (multCount (ratioExp h k) l - 1) (g1 - g1') := by
    rw [coeffFunctional_sub n h k hk l _ hs0 hs0', coeffFunctional_sub n h k hk l _ hs1 hs1']
    ring
  rw [hlin, coeffFunctional_second_eq n h k hk hmin hm (hs0.sub hs0'),
    coeffFunctional_top_eq n h k hk hmin hatt (hs1.sub hs1')]
  -- the two face integrals vanish
  have hI₁ : (∫ u in unitBox (n + 1), evalF (g0 - g0') (faceProj h k l u) *
      residualWeight h k l u * logWeight h k l u) = 0 := by
    rw [← integral_zero]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
    rw [hev0 _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)), faceProj_faceProj]
    simp
  have hI₂ : (∫ u in unitBox (n + 1), evalF (g1 - g1') (faceProj h k l u) *
      residualWeight h k l u) = 0 := by
    rw [← integral_zero]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
    rw [hev1 _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)), faceProj_faceProj]
    simp
  rw [← hg0, ← hg0', ← hg1, ← hg1', hI₁, hI₂]
  simp only [mul_zero, add_zero, zero_add]
  unfold transverseIncrement
  congr 1
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  by_cases hi₀ : ratioExp h k i₀ = l
  · rw [if_pos hi₀, if_pos hi₀]
    congr 1
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
    have hmem := unitBox_subset_closedCube _ hu
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hev0 _ (update_faceProj_mem_closedCube h k l hmem i₀ ht),
      hev0 _ (faceProj_mem_closedCube h k l hmem), faceProj_update h k l u hi₀, faceProj_faceProj]
    ring
  · rw [if_neg hi₀, if_neg hi₀]

/-- **Face versus transverse phase sensitivity**: `B(ξ,η) − B(ξ∘P_J,η)` is the transverse
increment. -/
theorem spatialSecondFace_sub_face (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    spatialSecondFace h k l β ξ η - spatialSecondFace h k l β (ξ ∘ faceProj h k l) η =
      transverseIncrement h k l β ξ η := by
  have hξc' : Continuous (ξ ∘ faceProj h k l) := hξc.comp (continuous_faceProj h k l)
  have hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (faceRestrict h k l cξ) u =
      (ξ ∘ faceProj h k l) u := fun u _ => by
    rw [evalF_faceRestrict]
    exact evalF_eq_on_closedCube hξ hξc hevξ
      (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ ‹_›))
  rw [← spatialSecondCoeff_eq n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm,
    ← spatialSecondCoeff_eq n h k hk hβ (absSummable_faceRestrict h k l hξ) hη hξc' hηc hevξ' hevη
      hmin hatt hm]
  exact spatialSecondCoeff_sub_faceRestrict n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm

/-! ### Consequences -/

/-- **Equality on every one-coordinate stratum gives equal second coefficients**: if `ξ, ξ'`
agree at the face points and at every transverse displacement `P_J u + t e_{i₀}`, `i₀ ∈ J`,
`t ∈ (0,1]`, then `B(ξ,η) = B(ξ',η)`. -/
theorem spatialSecondFace_congr_strata (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    {ξ ξ' η : (Fin (d + 1) → ℝ) → ℝ}
    (hface : ∀ u ∈ unitBox (d + 1), ξ (faceProj h k l u) = ξ' (faceProj h k l u))
    (hstrata : ∀ u ∈ unitBox (d + 1), ∀ i₀, ratioExp h k i₀ = l → ∀ t ∈ Ioc (0 : ℝ) 1,
      ξ (Function.update (faceProj h k l u) i₀ t) = ξ' (Function.update (faceProj h k l u) i₀ t)) :
    spatialSecondFace h k l β ξ η = spatialSecondFace h k l β ξ' η := by
  unfold spatialSecondFace dressedAmplitude
  congr 1
  congr 1
  · congr 1
    · exact setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by rw [hface u hu]
    · exact setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by rw [hface u hu]
  · refine Finset.sum_congr rfl fun i₀ _ => ?_
    by_cases hi₀ : ratioExp h k i₀ = l
    · rw [if_pos hi₀, if_pos hi₀]
      congr 1
      refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [hface u hu, hstrata u hu i₀ hi₀ t ht]
    · rw [if_neg hi₀, if_neg hi₀]

/-- **A transverse phase increase gives a nonnegative correction**: with `η ≥ 0` on the closed
cube and `ξ ≥ ξ∘P_J` on the one-coordinate strata, `B(ξ∘P_J,η) ≤ B(ξ,η)`. -/
theorem spatialSecondFace_face_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
    (hξge : ∀ u ∈ unitBox (n + 1), ∀ i₀, ratioExp h k i₀ = l → ∀ t ∈ Ioc (0 : ℝ) 1,
      ξ (faceProj h k l u) ≤ ξ (Function.update (faceProj h k l u) i₀ t)) :
    spatialSecondFace h k l β (ξ ∘ faceProj h k l) η ≤ spatialSecondFace h k l β ξ η := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [← sub_nonneg, spatialSecondFace_sub_face n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm]
  unfold transverseIncrement
  refine mul_nonneg (by have := faceTwoK_pos h k hk l; positivity)
    (Finset.sum_nonneg fun i₀ _ => ?_)
  split_ifs with hi₀
  · refine mul_nonneg (by positivity) (setIntegral_nonneg (measurableSet_unitBox _) fun u hu => ?_)
    refine mul_nonneg (residualWeight_nonneg h k l u hu)
      (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
    have hmem := unitBox_subset_closedCube _ hu
    refine div_nonneg (mul_nonneg (hηnn _ (update_faceProj_mem_closedCube h k l hmem i₀ ht)) ?_)
      ht.1.le
    exact sub_nonneg.2 (fluctMoment_mono_phase β hβ (hξge u hu i₀ hi₀ t ht) hl)
  · exact le_rfl

/-- **Transverse phase variation appears exactly at order `1/L`**: the evidences with phases `ξ`
and `ξ∘P_J` have the same leading term, and
`L (𝒵_N[η;ξ] − 𝒵_N[η;ξ∘P_J])/(N^{-λ}L^{m-1}) → B(ξ,η) − B(ξ∘P_J,η)`, the transverse
increment. -/
theorem spatialPhase_transverse_correction (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    Tendsto (fun N => Real.log N * ((origPhaseIntegral n h k β N 1 ξ η -
        origPhaseIntegral n h k β N 1 (ξ ∘ faceProj h k l) η) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))))
      atTop (𝓝 (transverseIncrement h k l β ξ η)) := by
  have hξc' : Continuous (ξ ∘ faceProj h k l) := hξc.comp (continuous_faceProj h k l)
  have hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (faceRestrict h k l cξ) u =
      (ξ ∘ faceProj h k l) u := fun u _ => by
    rw [evalF_faceRestrict]
    exact evalF_eq_on_closedCube hξ hξc hevξ
      (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ ‹_›))
  have h1 := spatialPhase_twoTerm_explicit n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm
  have h2 := spatialPhase_twoTerm_explicit n h k hk hβ (absSummable_faceRestrict h k l hξ) hη hξc'
    hηc hevξ' hevη hmin hatt hm
  have hF : spatialFace h k l β (ξ ∘ faceProj h k l) η = spatialFace h k l β ξ η :=
    spatialFace_congr_face h k l β fun u _ => by
      simp only [Function.comp_apply, faceProj_faceProj]
  rw [← spatialSecondFace_sub_face n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm]
  refine (h1.sub h2).congr' (Eventually.of_forall fun N => ?_)
  rw [hF]
  ring

end Grammar
