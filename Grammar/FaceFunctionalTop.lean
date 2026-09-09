/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.KernelSecondCoeff
import Grammar.SpatialTwoTerm

/-!
# The top coefficient functional as a face integral (unit 363; Astra #45 unit 2, step 3)

For an absolutely summable amplitude family `f` define the coefficient functional
`Φ_j[f] = K_k ∑_γ f_γ c_{λ,j}(h+γ)` (`coeffFunctional`), so that the monomial kernel functional
at `(λ, m−1)` is `fluctMoment β a p λ 0 · Φ_{m−1}[f]` and at `(λ, m−2)` it is
`fluctMoment β a p λ 0 · Φ_{m−2}[f] + (m−1) fluctMoment β a p λ 1 · Φ_{m−1}[f]`
(`kernelFunctional_top_eq`, `kernelFunctional_second_eq`).

**Series → integral for the top functional**: termwise, `K_k c_{λ,m−1}(h+γ)` is
`(1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫_{(0,1]^d} u^γ(P_J u) w(u) du` (`coeff_top_eq_integral`,
via `integral_mono_faceProj_residualWeight`), and summing over `γ` with the absolutely summable
`f` (dominated by `|f_γ| ∫ w`),
`Φ_{m−1}[f] = (1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫_{(0,1]^d} f(P_J u) w(u) du` (`coeffFunctional_top_eq`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

/-- The coefficient functional `Φ_j[f] = K_k ∑_γ f_γ c_{λ,j}(h+γ)`. -/
noncomputable def coeffFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (l : ℝ) (j : ℕ)
    (f : CoeffFamily (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) *
    ∑' γ, f γ * PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l j

/-- The face normalisation `∏_{i∈J} 2kᵢ`. -/
noncomputable def faceTwoK {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : ℝ :=
  ∏ i, if ratioExp h k i = l then 2 * (k i : ℝ) else 1

theorem faceTwoK_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    0 < faceTwoK h k l := by
  unfold faceTwoK
  refine Finset.prod_pos fun i _ => ?_
  split_ifs
  · have := hk i
    positivity
  · exact one_pos

theorem summable_mul_coeffAt (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {f : CoeffFamily (n + 1)} (hf : AbsSummable f) (l : ℝ) (j : ℕ) :
    Summable fun γ => f γ * PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l j :=
  Summable.of_norm_bounded (hf.mul_right (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n))
    fun γ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_coeffAt_stateDensityRep_le n (h + γ) k hk l j)
        (abs_nonneg _)

/-- The kernel functional at `(λ, m−1)`. -/
theorem kernelFunctional_top_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (p : ℕ) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (f : CoeffFamily (n + 1)) :
    kernelFunctional n h k β a p l (multCount (ratioExp h k) l - 1) f =
      fluctMoment β a p l 0 * coeffFunctional n h k l (multCount (ratioExp h k) l - 1) f := by
  unfold kernelFunctional coeffFunctional
  simp_rw [kernelS_top n h k hk β a p hmin hatt]
  have : ∀ γ, f γ * (PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
      (multCount (ratioExp h k) l - 1) * fluctMoment β a p l 0) =
      f γ * PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1) * fluctMoment β a p l 0 := fun γ => by ring
  simp_rw [this]
  rw [tsum_mul_right]
  ring

/-- The kernel functional at `(λ, m−2)` (`m ≥ 2`). -/
theorem kernelFunctional_second_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (p : ℕ) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hm : 2 ≤ multCount (ratioExp h k) l)
    {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    kernelFunctional n h k β a p l (multCount (ratioExp h k) l - 2) f =
      fluctMoment β a p l 0 * coeffFunctional n h k l (multCount (ratioExp h k) l - 2) f +
        ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * fluctMoment β a p l 1 *
          coeffFunctional n h k l (multCount (ratioExp h k) l - 1) f := by
  unfold kernelFunctional coeffFunctional
  simp_rw [kernelS_second n h k hk β a p hmin hm]
  have hs1 := (summable_mul_coeffAt n h k hk hf l (multCount (ratioExp h k) l - 2)).mul_right
    (fluctMoment β a p l 0)
  have hs2 := (summable_mul_coeffAt n h k hk hf l (multCount (ratioExp h k) l - 1)).mul_right
    (((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * fluctMoment β a p l 1)
  have : ∀ γ, f γ * (PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
      (multCount (ratioExp h k) l - 2) * fluctMoment β a p l 0 +
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1) * ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
        fluctMoment β a p l 1) =
      f γ * PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 2) * fluctMoment β a p l 0 +
      f γ * PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1) *
        (((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * fluctMoment β a p l 1) := fun γ => by ring
  simp_rw [this]
  rw [hs1.tsum_add hs2, tsum_mul_right, tsum_mul_right]
  ring

/-! ### Termwise face integrals -/

open Classical in
/-- `∫_{(0,1]^d} u^γ(P_J u) w(u) du = [γ_J = 0] ∏_{i∉J} 1/(hᵢ + γᵢ + 1 − 2kᵢλ)`. -/
theorem integral_mono_faceProj_residualWeight (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) :
    ∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u =
      if faceZero h k l γ then
        ∏ i, (if ratioExp h k i = l then (1 : ℝ)
          else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l))
      else 0 := by
  have hprod : ∀ u : Fin (n + 1) → ℝ, mono γ (faceProj h k l u) * residualWeight h k l u =
      ∏ i, ((if ratioExp h k i = l then (0 : ℝ) else u i) ^ γ i *
        (if ratioExp h k i = l then (1 : ℝ) else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l))) := by
    intro u
    unfold mono residualWeight faceProj
    rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [restrict_unitBox, integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => (if ratioExp h k i = l then (0 : ℝ) else t) ^ γ i *
      (if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)))]
  have hfac : ∀ i, (∫ t in Ioc (0 : ℝ) 1, (if ratioExp h k i = l then (0 : ℝ) else t) ^ γ i *
      (if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) - 2 * (k i : ℝ) * l))) =
      if ratioExp h k i = l then (if γ i = 0 then (1 : ℝ) else 0)
      else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) := by
    intro i
    by_cases hi : ratioExp h k i = l
    · simp only [if_pos hi, mul_one]
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal
        zero_le_one, one_smul]
      by_cases hγ : γ i = 0
      · rw [if_pos hγ, hγ, pow_zero]
      · rw [if_neg hγ, zero_pow hγ]
    · simp only [if_neg hi]
      have ha := residual_exponent_gt h k hk l hmin i hi
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ =>
        t ^ ((γ i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * l))) fun t ht => by
          beta_reduce
          rw [Real.rpow_add ht.1, Real.rpow_natCast]]
      rw [integral_Ioc_rpow_factor _ (by linarith)]
      congr 1
      ring
  simp_rw [hfac]
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · rw [if_pos hi, if_pos hi, if_pos (hf i hi)]
    · rw [if_neg hi, if_neg hi]
  · rw [if_neg hf]
    unfold faceZero at hf
    push Not at hf
    obtain ⟨i, hi, hγ⟩ := hf
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hi, if_neg hγ])

/-- `2kᵢ (w_{γ,i} + 1 − λ) = hᵢ + γᵢ + 1 − 2kᵢλ`. -/
theorem two_k_mul_monoWeights_sub {d : ℕ} (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (i : Fin d) :
    2 * (k i : ℝ) * (monoWeights (h + γ) k i + 1 - l) =
      (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l := by
  rw [monoWeights_add_one_eq h k γ hk i]
  unfold ratioExp
  have hk0 : (k i : ℝ) ≠ 0 := by
    have := hk i
    positivity
  field_simp
  ring

open Classical in
/-- **Termwise identity for the top coefficient**:
`K_k c_{λ,m−1}(h+γ) = (1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫ u^γ(P_J u) w(u) du`. -/
theorem coeff_top_eq_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (γ : Fin (n + 1) → ℕ) :
    (∏ i, 1 / (2 * (k i : ℝ))) *
        PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
          (multCount (ratioExp h k) l - 1) =
      (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) * faceTwoK h k l)) *
        ∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u := by
  rw [coeffAt_monoWeights_top n h k γ hk hmin hatt, integral_mono_faceProj_residualWeight n h k hk
    hmin γ]
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf, if_pos hf]
    unfold residualProd faceTwoK
    have hK : (∏ i, 1 / (2 * (k i : ℝ))) =
        (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1) *
          ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (2 * (k i : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs <;> ring
    have hinv : (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1) =
        1 / ∏ i, if ratioExp h k i = l then 2 * (k i : ℝ) else 1 := by
      rw [one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hres : (∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (2 * (k i : ℝ))) *
        ∏ i, (if ratioExp h k i = l then (1 : ℝ) else 1 / (monoWeights (h + γ) k i + 1 - l)) =
        ∏ i, (if ratioExp h k i = l then (1 : ℝ)
          else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : ratioExp h k i = l
      · simp [hi]
      · rw [if_neg hi, if_neg hi, if_neg hi, ← two_k_mul_monoWeights_sub h k γ hk l i,
          one_div_mul_one_div]
    rw [hK, hinv, ← hres]
    ring
  · rw [if_neg hf, if_neg hf, mul_zero, mul_zero]

/-! ### The top functional as a face integral -/

theorem integrable_mono_faceProj_residualWeight (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) :
    IntegrableOn (fun u => mono γ (faceProj h k l u) * residualWeight h k l u)
      (unitBox (n + 1)) := by
  have hcm : Continuous (mono γ) := by
    unfold mono
    exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
  refine Integrable.bdd_mul (c := 1) (residualWeight_integrableOn h k hk l hmin)
    (hcm.comp (continuous_faceProj h k l)).measurable.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_unitBox _)]
  refine Eventually.of_forall fun u hu => ?_
  have hmem := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
  rw [Real.norm_eq_abs, abs_of_nonneg (mono_nonneg hmem)]
  exact mono_le_one hmem

/-- **The top coefficient functional is the face integral**:
`Φ_{m−1}[f] = (1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫_{(0,1]^d} f(P_J u) w(u) du`. -/
theorem coeffFunctional_top_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    coeffFunctional n h k l (multCount (ratioExp h k) l - 1) f =
      (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) * faceTwoK h k l)) *
        ∫ u in unitBox (n + 1), evalF f (faceProj h k l u) * residualWeight h k l u := by
  unfold coeffFunctional
  rw [← tsum_mul_left]
  set C := 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) * faceTwoK h k l) with hC
  have hterm : ∀ γ, (∏ i, 1 / (2 * (k i : ℝ))) * (f γ *
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1)) =
      C * ∫ u in unitBox (n + 1), f γ * mono γ (faceProj h k l u) * residualWeight h k l u := by
    intro γ
    rw [mul_left_comm, coeff_top_eq_integral n h k hk hmin hatt γ, ← hC]
    simp_rw [mul_assoc (f γ)]
    rw [integral_const_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1
  set F : (Fin (n + 1) → ℕ) → (Fin (n + 1) → ℝ) → ℝ :=
    fun γ u => f γ * mono γ (faceProj h k l u) * residualWeight h k l u with hF
  have hint : ∀ γ, Integrable (F γ) (volume.restrict (unitBox (n + 1))) := fun γ => by
    simp only [hF]
    have := (integrable_mono_faceProj_residualWeight n h k hk hmin γ).const_mul (f γ)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    ring
  have hw := residualWeight_integrableOn h k hk l hmin
  have hnorm : Summable fun γ => ∫ u, ‖F γ u‖ ∂(volume.restrict (unitBox (n + 1))) := by
    refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun u => norm_nonneg _)
      (fun γ => ?_) (hf.mul_right (∫ u in unitBox (n + 1), residualWeight h k l u))
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
      (hw.const_mul _) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    refine Eventually.of_forall fun u hu => ?_
    have hmem := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
    simp only [hF, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (residualWeight_nonneg h k l u hu)]
    exact mul_le_mul_of_nonneg_right (abs_term_le hmem γ) (residualWeight_nonneg h k l u hu)
  rw [integral_tsum_of_summable_integral_norm hint hnorm]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  simp only [hF]
  rw [tsum_mul_right]
  rfl

end Grammar
