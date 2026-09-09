/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FaceFunctionalTop

/-!
# The face-zero part of the second coefficient functional (unit 364; Astra #45 unit 2, step 4)

The second-top shifted coefficient `c_{λ,m−2}(h+γ)` has a face-zero part
`−(1/(m−2)!) (∏_{i∉J} 1/(w_{γ,i}+1−λ)) ∑_{i∉J} 1/(w_{γ,i}+1−λ)` (unit 362).  Since
`1/(w_{γ,i}+1−λ)² = (2kᵢ)² ∫₀¹ v^{hᵢ+γᵢ−2kᵢλ} (−log v) dv`, this part is the face integral of
`u^γ(P_J u) w(u)` against the **logarithmic face weight** `L(u) = ∑_{ℓ∉J} 2k_ℓ log u_ℓ`
(`logWeight`, `coeff_second_faceZero_eq_integral`), and summing over an absolutely summable
amplitude family (dominated by `|f_γ| w (−L)`)
`K_k ∑_γ f_γ [γ_J = 0] c^{(2)}_{λ}(h+γ) = (1/((m−2)! ∏_{i∈J} 2kᵢ)) ∫ f(P_J u) w(u) L(u) du`
(`coeffFunctional_second_faceZero_eq`).  The one-dimensional input is
`∫₀¹ t^{a−1} log t dt = −1/a²` (`integral_Ioc_rpow_mul_log`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

/-- The logarithmic face weight `L(u) = ∑_{ℓ∉J} 2k_ℓ log u_ℓ`. -/
noncomputable def logWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : ℝ :=
  ∑ ℓ, if ratioExp h k ℓ = l then (0 : ℝ) else 2 * (k ℓ : ℝ) * Real.log (u ℓ)

theorem logWeight_nonpos {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) {u : Fin d → ℝ} (hu : u ∈ unitBox d) :
    logWeight h k l u ≤ 0 := by
  unfold logWeight
  refine Finset.sum_nonpos fun ℓ _ => ?_
  split_ifs
  · exact le_rfl
  · have := hu ℓ (Set.mem_univ ℓ)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos this.1.le this.2)

theorem measurable_logWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : Measurable (logWeight h k l) := by
  unfold logWeight
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  split_ifs
  · exact measurable_const
  · exact measurable_const.mul (Real.measurable_log.comp (measurable_pi_apply ℓ))

/-- `∫₀¹ t^{a−1} log t dt = −1/a²`. -/
theorem integral_Ioc_rpow_mul_log (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (a - 1) * Real.log t = -(1 / a ^ 2) := by
  have h := integral_Ioc_rpow_mul_neg_log_pow a ha 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  have hfun : (fun t : ℝ => t ^ (a - 1) * Real.log t) =
      fun t => -(t ^ (a - 1) * -Real.log t) := by
    funext t
    ring
  rw [hfun, integral_neg, h]

theorem integrableOn_Ioc_rpow_mul_log (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.log t) (Ioc 0 1) := by
  have h := (integrableOn_powLogBasis a ha 1).neg
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
  simp only [Pi.neg_apply, powLogBasis, pow_one]
  ring

/-! ### Termwise log-weighted face integrals -/

/-- One coordinate factor of the log-weighted face integrand. -/
noncomputable def logFactor {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) (ℓ i : Fin d)
    (t : ℝ) : ℝ :=
  (if ratioExp h k i = l then (0 : ℝ) else t) ^ γ i *
    (if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)) *
    (if i = ℓ then 2 * (k ℓ : ℝ) * Real.log t else 1)

theorem prod_logFactor {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) (ℓ : Fin d)
    (u : Fin d → ℝ) :
    mono γ (faceProj h k l u) * residualWeight h k l u * (2 * (k ℓ : ℝ) * Real.log (u ℓ)) =
      ∏ i, logFactor h k l γ ℓ i (u i) := by
  unfold logFactor mono residualWeight faceProj
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ ℓ (fun i => 2 * (k ℓ : ℝ) * Real.log (u i)),
    if_pos (Finset.mem_univ ℓ)]

theorem residual_exponent_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) {i : Fin d} (hi : ratioExp h k i ≠ l) :
    0 < (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l := by
  have := residual_exponent_gt h k hk l hmin i hi
  have : (0 : ℝ) ≤ γ i := Nat.cast_nonneg _
  linarith

theorem integral_logFactor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) {ℓ : Fin (n + 1)}
    (hℓ : ratioExp h k ℓ ≠ l) (i : Fin (n + 1)) :
    ∫ t in Ioc (0 : ℝ) 1, logFactor h k l γ ℓ i t =
      if ratioExp h k i = l then (if γ i = 0 then (1 : ℝ) else 0)
      else if i = ℓ then
        -(2 * (k ℓ : ℝ) * (1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) *
          (1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l))))
      else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) := by
  by_cases hi : ratioExp h k i = l
  · have hiℓ : i ≠ ℓ := fun h' => hℓ (h' ▸ hi)
    simp only [logFactor, if_pos hi, if_neg hiℓ, mul_one]
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal
      zero_le_one, one_smul]
    by_cases hγ : γ i = 0
    · rw [if_pos hγ, hγ, pow_zero]
    · rw [if_neg hγ, zero_pow hγ]
  · have ha := residual_exponent_pos h k hk hmin γ hi
    have hc : (γ i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * l) =
        (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l - 1 := by ring
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      simp only [logFactor, if_neg hi, if_true]
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ =>
        2 * (k i : ℝ) * (t ^ ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l - 1) * Real.log t))
        fun t ht => by
          beta_reduce
          rw [← hc, Real.rpow_add ht.1, Real.rpow_natCast]
          ring]
      rw [integral_const_mul, integral_Ioc_rpow_mul_log _ ha, sq, ← one_div_mul_one_div]
      ring
    · simp only [logFactor, if_neg hi, if_neg hiℓ, mul_one]
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ =>
        t ^ ((γ i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * l))) fun t ht => by
          beta_reduce
          rw [Real.rpow_add ht.1, Real.rpow_natCast]]
      rw [integral_Ioc_rpow_factor _ (by linarith)]
      congr 1
      ring

theorem integrableOn_logFactor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) {ℓ : Fin (n + 1)}
    (hℓ : ratioExp h k ℓ ≠ l) (i : Fin (n + 1)) :
    IntegrableOn (logFactor h k l γ ℓ i) (Ioc 0 1) := by
  by_cases hi : ratioExp h k i = l
  · have hiℓ : i ≠ ℓ := fun h' => hℓ (h' ▸ hi)
    refine IntegrableOn.congr_fun (integrable_const ((0 : ℝ) ^ γ i)) (fun t _ => ?_)
      measurableSet_Ioc
    simp only [logFactor, if_pos hi, if_neg hiℓ, mul_one]
  · have ha := residual_exponent_pos h k hk hmin γ hi
    have hc : (γ i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * l) =
        (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l - 1 := by ring
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      refine IntegrableOn.congr_fun ((integrableOn_Ioc_rpow_mul_log _ ha).const_mul
        (2 * (k i : ℝ))) (fun t ht => ?_) measurableSet_Ioc
      simp only [logFactor, if_neg hi, if_true]
      rw [← hc, Real.rpow_add ht.1, Real.rpow_natCast]
      ring
    · refine IntegrableOn.congr_fun (integrableOn_Ioc_rpow_factor
        ((γ i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * l)) (by linarith)) (fun t ht => ?_)
        measurableSet_Ioc
      simp only [logFactor, if_neg hi, if_neg hiℓ, mul_one]
      rw [Real.rpow_add ht.1, Real.rpow_natCast]

theorem integrableOn_mono_faceProj_residualWeight_log (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ)
    {ℓ : Fin (n + 1)} (hℓ : ratioExp h k ℓ ≠ l) :
    IntegrableOn (fun u => mono γ (faceProj h k l u) * residualWeight h k l u *
      (2 * (k ℓ : ℝ) * Real.log (u ℓ))) (unitBox (n + 1)) := by
  simp_rw [prod_logFactor]
  unfold IntegrableOn
  rw [restrict_unitBox]
  exact Integrable.fintype_prod_dep (f := fun i t => logFactor h k l γ ℓ i t)
    fun i => integrableOn_logFactor n h k hk hmin γ hℓ i

open Classical in
/-- `∫ u^γ(P_J u) w(u) 2k_ℓ log u_ℓ du = −[γ_J = 0] 2k_ℓ (∏_{i∉J} 1/aᵢ)(1/a_ℓ)`,
`aᵢ = hᵢ + γᵢ + 1 − 2kᵢλ`, for `ℓ ∉ J`. -/
theorem integral_mono_faceProj_residualWeight_log (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ)
    {ℓ : Fin (n + 1)} (hℓ : ratioExp h k ℓ ≠ l) :
    ∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u *
        (2 * (k ℓ : ℝ) * Real.log (u ℓ)) =
      if faceZero h k l γ then
        -(2 * (k ℓ : ℝ) * ((∏ i, if ratioExp h k i = l then (1 : ℝ)
          else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) *
          (1 / ((h ℓ : ℝ) + γ ℓ + 1 - 2 * (k ℓ : ℝ) * l))))
      else 0 := by
  simp_rw [prod_logFactor]
  rw [restrict_unitBox, integral_fintype_prod_eq_prod (f := fun i t => logFactor h k l γ ℓ i t)]
  simp_rw [integral_logFactor n h k hk hmin γ hℓ]
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ),
      ← Finset.mul_prod_erase Finset.univ (fun i => if ratioExp h k i = l then (1 : ℝ)
        else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) (Finset.mem_univ ℓ)]
    have hrest : (∏ i ∈ Finset.univ.erase ℓ, (if ratioExp h k i = l then
        (if γ i = 0 then (1 : ℝ) else 0)
        else if i = ℓ then -(2 * (k ℓ : ℝ) * (1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) *
          (1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l))))
        else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l))) =
        ∏ i ∈ Finset.univ.erase ℓ, (if ratioExp h k i = l then (1 : ℝ)
          else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i ≠ ℓ := Finset.ne_of_mem_erase hi
      by_cases hJ : ratioExp h k i = l
      · rw [if_pos hJ, if_pos hJ, if_pos (hf i hJ)]
      · rw [if_neg hJ, if_neg hJ, if_neg hi']
    rw [hrest, if_neg hℓ, if_pos (rfl : ℓ = ℓ), if_neg hℓ]
    ring
  · rw [if_neg hf]
    unfold faceZero at hf
    push Not at hf
    obtain ⟨i, hi, hγ⟩ := hf
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hi, if_neg hγ])

open Classical in
/-- `∫ u^γ(P_J u) w(u) L(u) du = −[γ_J = 0] (∏_{i∉J} 1/aᵢ) ∑_{ℓ∉J} 2k_ℓ/a_ℓ`. -/
theorem integral_mono_faceProj_residualWeight_logWeight (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) :
    ∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u *
        logWeight h k l u =
      if faceZero h k l γ then
        -((∏ i, if ratioExp h k i = l then (1 : ℝ)
          else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) *
          ∑ ℓ, if ratioExp h k ℓ = l then (0 : ℝ)
            else 2 * (k ℓ : ℝ) / ((h ℓ : ℝ) + γ ℓ + 1 - 2 * (k ℓ : ℝ) * l))
      else 0 := by
  unfold logWeight
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun ℓ _ => ?_]
  · have hterm : ∀ ℓ, (∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u *
        (if ratioExp h k ℓ = l then (0 : ℝ) else 2 * (k ℓ : ℝ) * Real.log (u ℓ))) =
        if ratioExp h k ℓ = l then (0 : ℝ) else
          if faceZero h k l γ then
            -(2 * (k ℓ : ℝ) * ((∏ i, if ratioExp h k i = l then (1 : ℝ)
              else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) *
              (1 / ((h ℓ : ℝ) + γ ℓ + 1 - 2 * (k ℓ : ℝ) * l))))
          else 0 := by
      intro ℓ
      by_cases hℓ : ratioExp h k ℓ = l
      · simp [hℓ]
      · simp only [if_neg hℓ]
        exact integral_mono_faceProj_residualWeight_log n h k hk hmin γ hℓ
    simp_rw [hterm]
    by_cases hf : faceZero h k l γ
    · simp only [if_pos hf]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      split_ifs
      · simp
      · ring
    · simp only [if_neg hf]
      simp
  · by_cases hℓ : ratioExp h k ℓ = l
    · simp only [if_pos hℓ, mul_zero]
      exact integrable_zero _ _ _
    · simp only [if_neg hℓ]
      exact integrableOn_mono_faceProj_residualWeight_log n h k hk hmin γ hℓ

/-! ### The face-zero coefficient as a log-weighted face integral -/

theorem prod_inv_two_k_mul_residualProd {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (γ : Fin d → ℕ) :
    (∏ i, 1 / (2 * (k i : ℝ))) * residualProd h k γ l =
      (1 / faceTwoK h k l) * ∏ i, (if ratioExp h k i = l then (1 : ℝ)
        else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)) := by
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

theorem residualSum_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (γ : Fin d → ℕ) :
    residualSum h k γ l = ∑ ℓ, if ratioExp h k ℓ = l then (0 : ℝ)
      else 2 * (k ℓ : ℝ) / ((h ℓ : ℝ) + γ ℓ + 1 - 2 * (k ℓ : ℝ) * l) := by
  unfold residualSum
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs with hℓ
  · rfl
  · rw [← two_k_mul_monoWeights_sub h k γ hk l ℓ]
    have hk0 : (2 * (k ℓ : ℝ)) ≠ 0 := by
      have := hk ℓ
      positivity
    rw [div_mul_eq_div_div, div_self hk0]

open Classical in
/-- **Termwise identity for the face-zero part of the second coefficient**:
`K_k [γ_J = 0] c^{(2)}(h+γ) = (1/((m−2)! ∏_{i∈J} 2kᵢ)) ∫ u^γ(P_J u) w(u) L(u) du`. -/
theorem coeff_second_faceZero_eq_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) :
    (∏ i, 1 / (2 * (k i : ℝ))) * (if faceZero h k l γ then
        -(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
          (residualProd h k γ l * residualSum h k γ l)
      else 0) =
      (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
        ∫ u in unitBox (n + 1), mono γ (faceProj h k l u) * residualWeight h k l u *
          logWeight h k l u := by
  rw [integral_mono_faceProj_residualWeight_logWeight n h k hk hmin γ]
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf, if_pos hf, residualSum_eq h k hk l γ]
    have h1 := prod_inv_two_k_mul_residualProd h k hk l γ
    calc _ = -(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
          (((∏ i, 1 / (2 * (k i : ℝ))) * residualProd h k γ l) *
            ∑ ℓ, if ratioExp h k ℓ = l then (0 : ℝ)
              else 2 * (k ℓ : ℝ) / ((h ℓ : ℝ) + γ ℓ + 1 - 2 * (k ℓ : ℝ) * l)) := by ring
      _ = _ := by rw [h1]; ring
  · simp [hf]

theorem integrableOn_residualWeight_mul_logWeight (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) :
    IntegrableOn (fun u => residualWeight h k l u * logWeight h k l u) (unitBox (n + 1)) := by
  unfold logWeight
  simp_rw [Finset.mul_sum]
  refine integrable_finsetSum _ fun ℓ _ => ?_
  by_cases hℓ : ratioExp h k ℓ = l
  · simp only [if_pos hℓ, mul_zero]
    exact integrable_zero _ _ _
  · simp only [if_neg hℓ]
    refine (integrableOn_mono_faceProj_residualWeight_log n h k hk hmin 0 hℓ).congr_fun
      (fun u _ => ?_) (measurableSet_unitBox _)
    simp [mono]

open Classical in
/-- **The face-zero part of the second coefficient functional is the log-weighted face
integral**: for absolutely summable `f`,
`K_k ∑_γ f_γ [γ_J = 0] c^{(2)}(h+γ) = (1/((m−2)! ∏_{i∈J} 2kᵢ)) ∫ f(P_J u) w(u) L(u) du`. -/
theorem coeffFunctional_second_faceZero_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ * (if faceZero h k l γ then
        -(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
          (residualProd h k γ l * residualSum h k γ l)
      else 0) =
      (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
        ∫ u in unitBox (n + 1), evalF f (faceProj h k l u) * residualWeight h k l u *
          logWeight h k l u := by
  classical
  rw [← tsum_mul_left]
  set C := 1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l) with hC
  set F : (Fin (n + 1) → ℕ) → (Fin (n + 1) → ℝ) → ℝ :=
    fun γ u => f γ * mono γ (faceProj h k l u) * (residualWeight h k l u * logWeight h k l u)
    with hF
  have hterm : ∀ γ, (∏ i, 1 / (2 * (k i : ℝ))) * (f γ * (if faceZero h k l γ then
      -(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
        (residualProd h k γ l * residualSum h k γ l) else 0)) =
      C * ∫ u in unitBox (n + 1), F γ u := by
    intro γ
    rw [mul_left_comm, coeff_second_faceZero_eq_integral n h k hk hmin γ, ← hC, mul_left_comm,
      ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    simp only [hF]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1
  have hwL := integrableOn_residualWeight_mul_logWeight n h k hk hmin
  have hint : ∀ γ, Integrable (F γ) (volume.restrict (unitBox (n + 1))) := fun γ => by
    have hcm : Continuous (mono γ) := by
      unfold mono
      exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
    have := (Integrable.bdd_mul (c := 1) hwL
      (hcm.comp (continuous_faceProj h k l)).measurable.aestronglyMeasurable (by
        rw [ae_restrict_iff' (measurableSet_unitBox _)]
        refine Eventually.of_forall fun u hu => ?_
        have hmem := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
        rw [Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (mono_nonneg hmem)]
        exact mono_le_one hmem)).const_mul (f γ)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [hF, Function.comp_apply]
    ring
  have hnorm : Summable fun γ => ∫ u, ‖F γ u‖ ∂(volume.restrict (unitBox (n + 1))) := by
    refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun u => norm_nonneg _)
      (fun γ => ?_) (hf.mul_right (∫ u in unitBox (n + 1),
        residualWeight h k l u * -logWeight h k l u))
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
      ((hwL.neg.congr (Eventually.of_forall fun u => by
        simp only [Pi.neg_apply]; ring)).const_mul _)
      ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    refine Eventually.of_forall fun u hu => ?_
    have hmem := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
    have hw0 := residualWeight_nonneg h k l u hu
    have hL0 := logWeight_nonpos h k l hu
    simp only [hF, Real.norm_eq_abs]
    rw [abs_mul, abs_mul (residualWeight h k l u), abs_of_nonneg hw0, abs_of_nonpos hL0]
    exact mul_le_mul_of_nonneg_right (abs_term_le hmem γ)
      (mul_nonneg hw0 (neg_nonneg.2 hL0))
  rw [integral_tsum_of_summable_integral_norm hint hnorm]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  simp only [hF]
  rw [tsum_mul_right, mul_assoc]
  rfl

end Grammar
