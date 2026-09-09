/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FaceFunctionalTransverse

/-!
# The second coefficient functional as a finite-part face integral (unit 366; Astra #45 unit 2,
step 6)

Assembling units 362–365: for an absolutely summable amplitude family `f` and `m ≥ 2`,
```
Φ_{m−2}[f] = (1/((m−2)! ∏_{i∈J} 2kᵢ)) [ ∫ f(P_J u) w(u) L(u) du
             + ∑_{i₀∈J} 2k_{i₀} ∫ w(u) ∫₀¹ (f(P_J u + t e_{i₀}) − f(P_J u))/t dt du ]
```
(`coeffFunctional_second_eq`), where `L(u) = ∑_{ℓ∉J} 2k_ℓ log u_ℓ`.  The two summability facts
needed to split the series come from the uniform bounds `residualProd ≤ ∏_{i∉J} 1/(ratioᵢ−λ)`,
`residualSum ≤ ∑_{i∉J} 1/(ratioᵢ−λ)` (`residualProd_le_bound`, `residualSum_le_bound`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

variable {d : ℕ}

/-! ### Uniform bounds on the residual product and sum -/

theorem residualProd_nonneg (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) : 0 ≤ residualProd h k γ l := by
  unfold residualProd
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs with hi
  · exact zero_le_one
  · have := lt_of_le_of_ne (le_monoWeights_add_one h k hk hmin γ i)
      (fun h' => hi ((monoWeights_add_one_eq_iff h k hk hmin γ i).1 h'.symm).1)
    have : 0 < monoWeights (h + γ) k i + 1 - l := by linarith
    positivity

theorem one_div_monoWeights_le (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {i : Fin d} (hi : ratioExp h k i ≠ l) :
    1 / (monoWeights (h + γ) k i + 1 - l) ≤ 1 / (ratioExp h k i - l) := by
  have hpos : 0 < ratioExp h k i - l := by
    have := lt_of_le_of_ne (hmin i) (Ne.symm hi)
    linarith
  refine one_div_le_one_div_of_le hpos ?_
  rw [monoWeights_add_one_eq h k γ hk i]
  have : (0 : ℝ) ≤ (γ i : ℝ) / (2 * (k i : ℝ)) := by positivity
  linarith

/-- The uniform bound `∏_{i∉J} 1/(ratioᵢ − λ)` for the residual product. -/
theorem residualProd_le_bound (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    residualProd h k γ l ≤
      ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (ratioExp h k i - l) := by
  unfold residualProd
  refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
  · split_ifs with hi
    · exact zero_le_one
    · have := lt_of_le_of_ne (le_monoWeights_add_one h k hk hmin γ i)
        (fun h' => hi ((monoWeights_add_one_eq_iff h k hk hmin γ i).1 h'.symm).1)
      have : 0 < monoWeights (h + γ) k i + 1 - l := by linarith
      positivity
  · split_ifs with hi
    · exact le_rfl
    · exact one_div_monoWeights_le h k γ hk hmin hi

theorem residualSum_nonneg (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) : 0 ≤ residualSum h k γ l := by
  unfold residualSum
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with hi
  · exact le_rfl
  · have := lt_of_le_of_ne (le_monoWeights_add_one h k hk hmin γ i)
      (fun h' => hi ((monoWeights_add_one_eq_iff h k hk hmin γ i).1 h'.symm).1)
    have : 0 < monoWeights (h + γ) k i + 1 - l := by linarith
    positivity

/-- The uniform bound `∑_{i∉J} 1/(ratioᵢ − λ)` for the residual sum. -/
theorem residualSum_le_bound (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    residualSum h k γ l ≤
      ∑ i, if ratioExp h k i = l then (0 : ℝ) else 1 / (ratioExp h k i - l) := by
  unfold residualSum
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with hi
  · exact le_rfl
  · exact one_div_monoWeights_le h k γ hk hmin hi

/-! ### Summability of the two parts -/

open Classical in
theorem summable_faceZero_part (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) (c : ℝ) :
    Summable fun γ => f γ * (if faceZero h k l γ then
      c * (residualProd h k γ l * residualSum h k γ l) else 0) := by
  set P := ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (ratioExp h k i - l) with hP
  set S := ∑ i, if ratioExp h k i = l then (0 : ℝ) else 1 / (ratioExp h k i - l) with hS
  refine Summable.of_norm_bounded (hf.mul_right (|c| * (P * S))) fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  split_ifs
  · rw [abs_mul, abs_of_nonneg (mul_nonneg (residualProd_nonneg h k γ hk hmin)
      (residualSum_nonneg h k γ hk hmin))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (residualProd_le_bound h k γ hk hmin) (residualSum_le_bound h k γ hk hmin)
      (residualSum_nonneg h k γ hk hmin)
      ((residualProd_nonneg h k γ hk hmin).trans (residualProd_le_bound h k γ hk hmin))
  · simp only [abs_zero]
    have hP0 : 0 ≤ P := (residualProd_nonneg h k 0 hk hmin).trans
      (residualProd_le_bound h k 0 hk hmin)
    have hS0 : 0 ≤ S := (residualSum_nonneg h k 0 hk hmin).trans
      (residualSum_le_bound h k 0 hk hmin)
    positivity

open Classical in
theorem summable_transverse_part (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) (c : ℝ)
    (i₀ : Fin (n + 1)) :
    Summable fun γ => f γ *
      (if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
        c * residualProd h k γ l * (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
      else 0) := by
  set P := ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (ratioExp h k i - l) with hP
  have hP0 : 0 ≤ P := (residualProd_nonneg h k 0 hk hmin).trans
    (residualProd_le_bound h k 0 hk hmin)
  refine Summable.of_norm_bounded (hf.mul_right (|c| * P * (2 * (k i₀ : ℝ)))) fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  split_ifs with hcond
  · obtain ⟨-, hγ, -⟩ := hcond
    have h1 : (1 : ℝ) ≤ (γ i₀ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hγ
    rw [abs_mul, abs_mul, abs_of_nonneg (residualProd_nonneg h k γ hk hmin),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k i₀ : ℝ) / (γ i₀ : ℝ))]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (residualProd_le_bound h k γ hk hmin)
      (abs_nonneg _)) (div_le_self (by positivity) h1) (by positivity) (by positivity)
  · simp only [abs_zero]
    positivity

/-! ### The assembled second coefficient functional -/

/-- **The second coefficient functional is a finite-part face integral** (`m ≥ 2`): for an
absolutely summable amplitude family `f`,
`Φ_{m−2}[f] = (1/((m−2)! ∏_{i∈J} 2kᵢ)) [∫ f(P_J u) w(u) L(u) du +
∑_{i₀∈J} 2k_{i₀} ∫ w(u) ∫₀¹ (f(P_J u + t e_{i₀}) − f(P_J u))/t dt du]`. -/
theorem coeffFunctional_second_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hm : 2 ≤ multCount (ratioExp h k) l)
    {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    coeffFunctional n h k l (multCount (ratioExp h k) l - 2) f =
      (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
        ((∫ u in unitBox (n + 1), evalF f (faceProj h k l u) * residualWeight h k l u *
            logWeight h k l u) +
          ∑ i₀, if ratioExp h k i₀ = l then
            2 * (k i₀ : ℝ) * ∫ u in unitBox (n + 1), residualWeight h k l u *
              ∫ t in Ioc (0 : ℝ) 1,
                (evalF f (Function.update (faceProj h k l u) i₀ t) -
                  evalF f (faceProj h k l u)) / t
          else 0) := by
  classical
  unfold coeffFunctional
  have hco : ∀ γ, PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
      (multCount (ratioExp h k) l - 2) = _ := fun γ =>
    coeffAt_monoWeights_second n h k γ hk hmin hm
  simp_rw [hco, mul_add, Finset.mul_sum]
  have hA := summable_faceZero_part n h k hk hmin hf
    (-(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)))
  have hB : ∀ i₀ ∈ (Finset.univ : Finset (Fin (n + 1))), Summable fun γ => f γ *
      (if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
        (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) * residualProd h k γ l *
          (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
      else 0) := fun i₀ _ => summable_transverse_part n h k hk hmin hf _ i₀
  rw [hA.tsum_add (summable_sum hB), Summable.tsum_finsetSum hB, mul_add, Finset.mul_sum,
    coeffFunctional_second_faceZero_eq n h k hk hmin hf]
  congr 1
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  by_cases hi₀ : ratioExp h k i₀ = l
  · rw [if_pos hi₀]
    exact coeffFunctional_second_transverse_eq n h k hk hmin hf hi₀
  · rw [if_neg hi₀]
    simp only [hi₀, false_and, if_false, mul_zero, tsum_zero]

end Grammar
