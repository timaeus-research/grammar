/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FaceFunctionalLog

/-!
# The transverse part of the second coefficient functional (unit 365; Astra #45 unit 2, step 5)

The shifts `γ` moving exactly one face coordinate `i₀ ∈ J` contribute
`(1/(m−2)!) (∏_{i∉J} 1/(w_{γ,i}+1−λ)) · 2k_{i₀}/γ_{i₀}` to `c_{λ,m−2}(h+γ)` (unit 362).  Since
`1/γ_{i₀} = ∫₀¹ t^{γ_{i₀}−1} dt` and
`u^γ(P_J u + t e_{i₀}) − u^γ(P_J u) = (t^{γ_{i₀}} − 0^{γ_{i₀}}) u^{γ'}(P_J u)` with `γ' = γ` off
`i₀` and `γ'_{i₀} = 0` (`mono_update_faceProj`), this contribution is the **finite-part
transverse integral** `2k_{i₀} ∫ w(u) ∫₀¹ (u^γ(P_J u + t e_{i₀}) − u^γ(P_J u))/t dt du`
(`coeff_second_transverse_eq_integral`), and summing over an absolutely summable amplitude
family `f` (dominated by `|f_γ| w`):
`K_k ∑_γ f_γ B_{γ,i₀} =
(1/((m−2)! ∏_{i∈J} 2kᵢ)) · 2k_{i₀} ∫ w(u) ∫₀¹ (f(P_J u + t e_{i₀}) − f(P_J u))/t dt du`
(`coeffFunctional_second_transverse_eq`).  The difference quotient is bounded by `1` on the box
for every `γ`, which is what makes the finite-part integrals absolutely convergent.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

variable {d : ℕ}

/-! ### Monomials at a transversally displaced face point -/

theorem faceProj_apply_of_eq (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) {i₀ : Fin d}
    (hi₀ : ratioExp h k i₀ = l) : faceProj h k l u i₀ = 0 := by
  simp [faceProj, hi₀]

/-- `u^γ(v + t e_{i₀}) = t^{γ_{i₀}} u^{γ'}(v)` when `v_{i₀} = 0`... stated for any `v`:
`u^γ(update v i₀ t) = t^{γ_{i₀}} · u^{update γ i₀ 0}(v)`. -/
theorem mono_update (γ : Fin d → ℕ) (v : Fin d → ℝ) (i₀ : Fin d) (t : ℝ) :
    mono γ (Function.update v i₀ t) = t ^ γ i₀ * mono (Function.update γ i₀ 0) v := by
  classical
  unfold mono
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
    ← Finset.mul_prod_erase Finset.univ (fun i => v i ^ Function.update γ i₀ 0 i)
      (Finset.mem_univ i₀)]
  simp only [Function.update_self, pow_zero, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≠ i₀ := Finset.ne_of_mem_erase hi
  rw [Function.update_of_ne hi', Function.update_of_ne hi']

theorem mono_eq_pow_zero_mul (γ : Fin d → ℕ) (v : Fin d → ℝ) {i₀ : Fin d} (hv : v i₀ = 0) :
    mono γ v = (0 : ℝ) ^ γ i₀ * mono (Function.update γ i₀ 0) v := by
  have := mono_update γ v i₀ 0
  rw [Function.update_eq_self_iff.2 hv.symm] at this
  exact this

/-- The transverse difference quotient of a monomial at a face point. -/
theorem mono_transverse_quot (γ : Fin d → ℕ) (v : Fin d → ℝ) {i₀ : Fin d} (hv : v i₀ = 0) {t : ℝ}
    (ht : t ≠ 0) :
    (mono γ (Function.update v i₀ t) - mono γ v) / t =
      (if γ i₀ = 0 then (0 : ℝ) else t ^ (γ i₀ - 1)) * mono (Function.update γ i₀ 0) v := by
  rw [mono_update, mono_eq_pow_zero_mul γ v hv]
  by_cases hγ : γ i₀ = 0
  · rw [if_pos hγ, hγ]
    simp
  · rw [if_neg hγ, zero_pow hγ, zero_mul, sub_zero]
    obtain ⟨q, hq⟩ : ∃ q, γ i₀ = q + 1 := ⟨γ i₀ - 1, by omega⟩
    rw [hq, Nat.add_sub_cancel, pow_succ]
    field_simp

/-- `∫₀¹ [γ ≠ 0] t^{γ−1} dt = [γ ≠ 0]/γ`. -/
theorem integral_Ioc_transverse_pow (q : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, (if q = 0 then (0 : ℝ) else t ^ (q - 1)) =
      if q = 0 then (0 : ℝ) else 1 / (q : ℝ) := by
  by_cases hq : q = 0
  · simp [hq]
  · simp only [if_neg hq]
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    subst hr
    rw [Nat.add_sub_cancel, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    push_cast
    simp

theorem abs_transverse_pow_le {q : ℕ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    |if q = 0 then (0 : ℝ) else t ^ (q - 1)| ≤ 1 := by
  split_ifs
  · simp
  · rw [abs_of_nonneg (pow_nonneg ht.1.le _)]
    exact pow_le_one₀ ht.1.le ht.2

theorem faceZero_update_iff (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) {i₀ : Fin d}
    (hi₀ : ratioExp h k i₀ = l) :
    faceZero h k l (Function.update γ i₀ 0) ↔ ∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0 := by
  unfold faceZero
  constructor
  · intro hf i hi hne
    have := hf i hi
    rwa [Function.update_of_ne hne] at this
  · intro hf i hi
    by_cases hne : i = i₀
    · subst hne
      simp
    · rw [Function.update_of_ne hne]
      exact hf i hi hne

theorem prod_residual_update (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) {i₀ : Fin d}
    (hi₀ : ratioExp h k i₀ = l) :
    (∏ i, if ratioExp h k i = l then (1 : ℝ)
        else 1 / ((h i : ℝ) + Function.update γ i₀ 0 i + 1 - 2 * (k i : ℝ) * l)) =
      ∏ i, if ratioExp h k i = l then (1 : ℝ)
        else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : ratioExp h k i = l
  · rw [if_pos hi, if_pos hi]
  · have hne : i ≠ i₀ := fun h' => hi (h' ▸ hi₀)
    rw [if_neg hi, if_neg hi, Function.update_of_ne hne]

/-! ### Termwise transverse integrals -/

/-- The transverse difference quotient of a monomial at a displaced face point, as a function of
`t`, is integrable on `(0,1]` (it is `[γ_{i₀}≠0] t^{γ_{i₀}−1} u^{γ'}(P_J u)`). -/
theorem integrableOn_mono_transverse_quot (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ)
    (u : Fin d → ℝ) {i₀ : Fin d} (hi₀ : ratioExp h k i₀ = l) :
    IntegrableOn (fun t : ℝ => (mono γ (Function.update (faceProj h k l u) i₀ t) -
      mono γ (faceProj h k l u)) / t) (Ioc 0 1) := by
  have hc : Continuous fun t : ℝ =>
      (if γ i₀ = 0 then (0 : ℝ) else t ^ (γ i₀ - 1)) * mono (Function.update γ i₀ 0)
        (faceProj h k l u) := by
    split_ifs
    · exact continuous_const
    · exact (continuous_pow _).mul continuous_const
  refine IntegrableOn.congr_fun (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun t ht => ?_) measurableSet_Ioc
  exact (mono_transverse_quot γ _ (faceProj_apply_of_eq h k l u hi₀) ht.1.ne').symm

theorem integral_mono_transverse_quot (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) (u : Fin d → ℝ)
    {i₀ : Fin d} (hi₀ : ratioExp h k i₀ = l) :
    ∫ t in Ioc (0 : ℝ) 1, (mono γ (Function.update (faceProj h k l u) i₀ t) -
        mono γ (faceProj h k l u)) / t =
      (if γ i₀ = 0 then (0 : ℝ) else 1 / (γ i₀ : ℝ)) *
        mono (Function.update γ i₀ 0) (faceProj h k l u) := by
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ =>
    (if γ i₀ = 0 then (0 : ℝ) else t ^ (γ i₀ - 1)) * mono (Function.update γ i₀ 0)
      (faceProj h k l u)) fun t ht =>
      mono_transverse_quot γ _ (faceProj_apply_of_eq h k l u hi₀) ht.1.ne',
    integral_mul_const, integral_Ioc_transverse_pow]

theorem abs_mono_transverse_quot_le (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) {i₀ : Fin d} (hi₀ : ratioExp h k i₀ = l) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    |(mono γ (Function.update (faceProj h k l u) i₀ t) - mono γ (faceProj h k l u)) / t| ≤ 1 := by
  rw [mono_transverse_quot γ _ (faceProj_apply_of_eq h k l u hi₀) ht.1.ne', abs_mul]
  have hmem := faceProj_mem_closedCube h k l hu
  exact mul_le_one₀ (abs_transverse_pow_le ht) (abs_nonneg _)
    (by rw [abs_of_nonneg (mono_nonneg hmem)]; exact mono_le_one hmem)

open Classical in
/-- `∫ w(u) ∫₀¹ (u^γ(P_J u + t e_{i₀}) − u^γ(P_J u))/t dt du =
[γ_{i₀} ≠ 0]/γ_{i₀} · [γ_{J∖i₀} = 0] ∏_{i∉J} 1/aᵢ`. -/
theorem integral_transverse_mono (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) {i₀ : Fin (n + 1)}
    (hi₀ : ratioExp h k i₀ = l) :
    ∫ u in unitBox (n + 1), residualWeight h k l u *
        ∫ t in Ioc (0 : ℝ) 1, (mono γ (Function.update (faceProj h k l u) i₀ t) -
          mono γ (faceProj h k l u)) / t =
      (if γ i₀ = 0 then (0 : ℝ) else 1 / (γ i₀ : ℝ)) *
        (if (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
          ∏ i, (if ratioExp h k i = l then (1 : ℝ)
            else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l))
        else 0) := by
  simp_rw [integral_mono_transverse_quot h k l γ _ hi₀]
  rw [setIntegral_congr_fun (measurableSet_unitBox _) (g := fun u =>
    (if γ i₀ = 0 then (0 : ℝ) else 1 / (γ i₀ : ℝ)) *
      (mono (Function.update γ i₀ 0) (faceProj h k l u) * residualWeight h k l u))
    fun u _ => by ring, integral_const_mul,
    integral_mono_faceProj_residualWeight n h k hk hmin (Function.update γ i₀ 0)]
  congr 1
  by_cases hf : ∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0
  · rw [if_pos ((faceZero_update_iff h k l γ hi₀).2 hf), if_pos hf,
      prod_residual_update h k l γ hi₀]
  · rw [if_neg (fun h' => hf ((faceZero_update_iff h k l γ hi₀).1 h')), if_neg hf]

open Classical in
/-- **Termwise identity for the transverse part of the second coefficient**, `i₀ ∈ J`. -/
theorem coeff_second_transverse_eq_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin (n + 1) → ℕ) {i₀ : Fin (n + 1)}
    (hi₀ : ratioExp h k i₀ = l) :
    (∏ i, 1 / (2 * (k i : ℝ))) *
        (if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
          (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) * residualProd h k γ l *
            (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
        else 0) =
      (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
        (2 * (k i₀ : ℝ) * ∫ u in unitBox (n + 1), residualWeight h k l u *
          ∫ t in Ioc (0 : ℝ) 1, (mono γ (Function.update (faceProj h k l u) i₀ t) -
            mono γ (faceProj h k l u)) / t) := by
  rw [integral_transverse_mono n h k hk hmin γ hi₀]
  have h1 := prod_inv_two_k_mul_residualProd h k hk l γ
  by_cases hγ : γ i₀ = 0
  · simp [hγ]
  · by_cases hf : ∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0
    · rw [if_pos ⟨hi₀, hγ, hf⟩, if_neg hγ, if_pos hf]
      calc _ = (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
            ((∏ i, 1 / (2 * (k i : ℝ))) * residualProd h k γ l) *
            (2 * (k i₀ : ℝ) / (γ i₀ : ℝ)) := by ring
        _ = _ := by rw [h1]; ring
    · rw [if_neg (fun h' => hf h'.2.2), if_neg hf]
      simp

/-! ### The transverse functional as a finite-part integral -/

/-- The summed transverse difference quotient. -/
theorem tsum_transverse_quot (h k : Fin d → ℕ) (l : ℝ) {f : CoeffFamily d} (hf : AbsSummable f)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) {i₀ : Fin d} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ∑' γ, f γ * ((mono γ (Function.update (faceProj h k l u) i₀ t) -
        mono γ (faceProj h k l u)) / t) =
      (evalF f (Function.update (faceProj h k l u) i₀ t) - evalF f (faceProj h k l u)) / t := by
  have hmem := faceProj_mem_closedCube h k l hu
  have hmem' : Function.update (faceProj h k l u) i₀ t ∈ closedCube d := by
    intro i _
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      exact ⟨ht.1.le, ht.2⟩
    · rw [Function.update_of_ne hi]
      exact hmem i (Set.mem_univ i)
  unfold evalF
  rw [← (summable_term hf hmem').tsum_sub (summable_term hf hmem), div_eq_mul_inv,
    ← tsum_mul_right]
  refine tsum_congr fun γ => ?_
  ring

open Classical in
/-- **The transverse part of the second coefficient functional is the finite-part transverse
integral** (`i₀ ∈ J`): for absolutely summable `f`,
`K_k ∑_γ f_γ B_{γ,i₀} =
(1/((m−2)! ∏_{i∈J} 2kᵢ)) 2k_{i₀} ∫ w ∫₀¹ (f(P_J u + t e_{i₀}) − f(P_J u))/t`. -/
theorem coeffFunctional_second_transverse_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) {f : CoeffFamily (n + 1)} (hf : AbsSummable f)
    {i₀ : Fin (n + 1)} (hi₀ : ratioExp h k i₀ = l) :
    (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ *
        (if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
          (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) * residualProd h k γ l *
            (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
        else 0) =
      (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
        (2 * (k i₀ : ℝ) * ∫ u in unitBox (n + 1), residualWeight h k l u *
          ∫ t in Ioc (0 : ℝ) 1,
            (evalF f (Function.update (faceProj h k l u) i₀ t) -
              evalF f (faceProj h k l u)) / t) := by
  rw [← tsum_mul_left]
  set C := 1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l) with hC
  -- the closed form of the termwise transverse integral, as a function of `u`
  set G : (Fin (n + 1) → ℕ) → (Fin (n + 1) → ℝ) → ℝ := fun γ u =>
    (if γ i₀ = 0 then (0 : ℝ) else 1 / (γ i₀ : ℝ)) *
      mono (Function.update γ i₀ 0) (faceProj h k l u) with hG
  have hGeq : ∀ γ u, (∫ t in Ioc (0 : ℝ) 1, (mono γ (Function.update (faceProj h k l u) i₀ t) -
      mono γ (faceProj h k l u)) / t) = G γ u := fun γ u =>
    integral_mono_transverse_quot h k l γ u hi₀
  have hGabs : ∀ γ, ∀ u ∈ unitBox (n + 1), |G γ u| ≤ 1 := by
    intro γ u hu
    have hmem := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
    simp only [hG]
    rw [abs_mul]
    refine mul_le_one₀ ?_ (abs_nonneg _)
      (by rw [abs_of_nonneg (mono_nonneg hmem)]; exact mono_le_one hmem)
    split_ifs with hγ
    · simp
    · rw [abs_of_nonneg (by positivity)]
      have : (1 : ℝ) ≤ (γ i₀ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hγ
      exact div_le_one_of_le₀ this (by positivity)
  have hGc : ∀ γ, Continuous (G γ) := fun γ => by
    have hcm : Continuous (mono (Function.update γ i₀ 0)) := by
      unfold mono
      exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
    exact continuous_const.mul (hcm.comp (continuous_faceProj h k l))
  set F : (Fin (n + 1) → ℕ) → (Fin (n + 1) → ℝ) → ℝ :=
    fun γ u => f γ * (residualWeight h k l u * G γ u) with hF
  have hterm : ∀ γ, (∏ i, 1 / (2 * (k i : ℝ))) * (f γ *
      (if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
        (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) * residualProd h k γ l *
          (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
      else 0)) =
      C * (2 * (k i₀ : ℝ) * ∫ u in unitBox (n + 1), F γ u) := by
    intro γ
    rw [mul_left_comm, coeff_second_transverse_eq_integral n h k hk hmin γ hi₀, ← hC]
    simp_rw [hGeq]
    simp only [hF]
    rw [integral_const_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_mul_left]
  congr 2
  have hw := residualWeight_integrableOn h k hk l hmin
  have hint : ∀ γ, Integrable (F γ) (volume.restrict (unitBox (n + 1))) := fun γ => by
    have := (Integrable.bdd_mul (c := 1) hw (hGc γ).measurable.aestronglyMeasurable (by
      rw [ae_restrict_iff' (measurableSet_unitBox _)]
      exact Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact hGabs γ u hu)).const_mul (f γ)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [hF]
    ring
  have hnorm : Summable fun γ => ∫ u, ‖F γ u‖ ∂(volume.restrict (unitBox (n + 1))) := by
    refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun u => norm_nonneg _)
      (fun γ => ?_) (hf.mul_right (∫ u in unitBox (n + 1), residualWeight h k l u))
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
      (hw.const_mul _) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    refine Eventually.of_forall fun u hu => ?_
    have hw0 := residualWeight_nonneg h k l u hu
    simp only [hF, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, ← mul_assoc]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hw0) (hGabs γ u hu)
  rw [integral_tsum_of_summable_integral_norm hint hnorm]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  have hmem := unitBox_subset_closedCube _ hu
  -- the inner exchange at the point `u`
  have hinner : (∫ t in Ioc (0 : ℝ) 1,
      (evalF f (Function.update (faceProj h k l u) i₀ t) - evalF f (faceProj h k l u)) / t) =
      ∑' γ, f γ * G γ u := by
    have hint' : ∀ γ, Integrable (fun t : ℝ => f γ * ((mono γ (Function.update (faceProj h k l u)
        i₀ t) - mono γ (faceProj h k l u)) / t)) (volume.restrict (Ioc 0 1)) := fun γ =>
      (integrableOn_mono_transverse_quot h k l γ u hi₀).const_mul _
    have hnorm' : Summable fun γ => ∫ t, ‖f γ * ((mono γ (Function.update (faceProj h k l u)
        i₀ t) - mono γ (faceProj h k l u)) / t)‖ ∂(volume.restrict (Ioc 0 1)) := by
      refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun t => norm_nonneg _)
        (fun γ => ?_) hf
      have hb := norm_setIntegral_le_of_norm_le_const (f := fun t : ℝ => ‖f γ *
        ((mono γ (Function.update (faceProj h k l u) i₀ t) - mono γ (faceProj h k l u)) / t)‖)
        (μ := volume) (s := Ioc (0 : ℝ) 1) (C := |f γ|)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) fun t ht => by
          rw [norm_norm, Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _)
            (abs_mono_transverse_quot_le h k l γ hmem hi₀ ht)
      rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one,
        mul_one] at hb
      exact (Real.le_norm_self _).trans hb
    rw [← setIntegral_congr_fun measurableSet_Ioc (f := fun t : ℝ => ∑' γ, f γ *
      ((mono γ (Function.update (faceProj h k l u) i₀ t) - mono γ (faceProj h k l u)) / t))
      fun t ht => tsum_transverse_quot h k l hf hmem ht,
      ← integral_tsum_of_summable_integral_norm hint' hnorm']
    refine tsum_congr fun γ => ?_
    rw [integral_const_mul, hGeq]
  rw [hinner, ← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [hF]
  ring

end Grammar
