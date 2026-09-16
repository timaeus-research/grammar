/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldFamilyJets
import Grammar.CoordinateFrechetBridge
import Grammar.JetCloseness
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The field-family jet bound, uniform on bounded jets of the field

`exists_fieldJetBound` gives, for each smooth field `ζ`, SOME constant `C_ζ` with
`|∂^m (η e^{τ ζ})(v)| ≤ C_ζ (1+τ)^{|p|} e^{M' τ}` on the closed box. For the stochastic remainder
one needs the quantifiers the other way round: one constant for all fields whose jets of order
`≤ |p|` are bounded by `B` on the box. This follows from Mathlib's Faà di Bruno bound
(`norm_iteratedFDeriv_comp_le`, for `exp ∘ (τ ζ)`) and Leibniz bound (`norm_iteratedFDeriv_mul_le`)
with the explicit constant `C = 2^{|p|} |p|! B_η (1+B)^{|p|}` (consult #152, deliverable 1).
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ}

/-- Faà di Bruno for `exp ∘ (τ ζ)` on a set where the jets of `ζ` are bounded by `B`. -/
theorem norm_iteratedFDeriv_exp_mul_le (hζ : ContDiff ℝ ∞ ζ) {B : ℝ} (hB : 0 ≤ B) {τ : ℝ}
    (hτ : 0 ≤ τ) (n : ℕ) {v : Fin d → ℝ} (hbound : ∀ r ≤ n, ‖iteratedFDeriv ℝ r ζ v‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun v => exp (τ * ζ v)) v‖ ≤
      n.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ n := by
  have hζv : ζ v ≤ B := by
    have := hbound 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hf : ContDiff ℝ ∞ fun v => τ * ζ v := contDiff_const.mul hζ
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i exp ((fun v => τ * ζ v) v)‖ ≤ exp (τ * B) := by
    intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hζv hτ)
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (fun v => τ * ζ v) v‖ ≤
      ((1 + τ) * (1 + B)) ^ i := by
    intro i hi hin
    have heq : (fun v => τ * ζ v) = τ • ζ := rfl
    rw [heq, iteratedFDeriv_const_smul_apply ((hζ.of_le (natCast_le_infty i)).contDiffAt),
      norm_smul, Real.norm_of_nonneg hτ]
    calc τ * ‖iteratedFDeriv ℝ i ζ v‖ ≤ τ * B :=
          mul_le_mul_of_nonneg_left (hbound i hin) hτ
      _ ≤ (1 + τ) * (1 + B) := by nlinarith
      _ ≤ ((1 + τ) * (1 + B)) ^ i := le_self_pow₀ hD1 (by omega)
  have h := norm_iteratedFDeriv_comp_le (g := exp) (f := fun v => τ * ζ v) contDiff_exp hf
    (natCast_le_infty n) v hC hD
  exact h

/-- **The field-family jet bound is uniform on bounded jets**: one constant `C` for all smooth
fields `ζ` with `JetBoundOn |p| (closedBox d b) ζ B`. -/
theorem fieldJetBound_of_jetBoundOn (hη : ContDiff ℝ ∞ η) (p : Fin d → ℕ) {b B : ℝ}
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (∑ i, p i) (closedBox d b) ζ B → FieldJetBound η ζ p b C B := by
  set P : ℕ := ∑ i, p i with hP
  obtain ⟨Bη, hBη0, hBη⟩ := exists_jetBoundOn hη P (isCompact_closedBox b)
  refine ⟨2 ^ P * P.factorial * Bη * (1 + B) ^ P, by positivity, fun ζ hζ hζB m hm τ hτ v hv => ?_⟩
  have hr : ∑ i, m i ≤ P := Finset.sum_le_sum fun i _ => hm i
  set r : ℕ := ∑ i, m i with hr'
  have hfam : ContDiff ℝ ∞ (fieldFam η ζ τ) := contDiff_fieldFam hη hζ τ
  have hexp : ContDiff ℝ ∞ fun v => exp (τ * ζ v) := contDiff_exp.comp (contDiff_const.mul hζ)
  -- the coordinate derivative is bounded by the Fréchet derivative of order `r`
  have h1 : |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤
      ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖ := by
    have := abs_pdMulti_le_norm_iteratedFDeriv hfam m (List.finRange d) v
    rwa [wordLen_finRange] at this
  -- Leibniz
  have h2 : ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖ ≤ ∑ i ∈ range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
        ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ :=
    norm_iteratedFDeriv_mul_le hη hexp v (natCast_le_infty r)
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  -- each term
  have h3 : ∀ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
      ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ ≤
      (r.choose i : ℝ) * (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hηi : ‖iteratedFDeriv ℝ i η v‖ ≤ Bη := hBη i (hi'.trans hr) v hv
    have hexpi := norm_iteratedFDeriv_exp_mul_le hζ hB hτ (r - i) (v := v)
      fun s hs => hζB s (hs.trans ((Nat.sub_le r i).trans hr)) v hv
    have hfac : ((r - i).factorial : ℝ) ≤ P.factorial := by
      exact_mod_cast Nat.factorial_le ((Nat.sub_le r i).trans hr)
    have hpow : ((1 + τ) * (1 + B)) ^ (r - i) ≤ ((1 + τ) * (1 + B)) ^ P :=
      pow_le_pow_right₀ hD1 ((Nat.sub_le r i).trans hr)
    have hexpi' : ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ ≤
        P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P :=
      hexpi.trans (by gcongr)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hηi hexpi' (norm_nonneg _) hBη0
  have h4 : ∑ i ∈ range (r + 1), (r.choose i : ℝ) *
      (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) =
      2 ^ r * (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose r
  have h5 : (2 : ℝ) ^ r ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) hr
  calc |pdMulti m (List.finRange d) (fieldFam η ζ τ) v|
      ≤ ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖ := h1
    _ ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
          ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ := h2
    _ ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) *
          (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) := Finset.sum_le_sum h3
    _ = 2 ^ r * (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) := h4
    _ ≤ 2 ^ P * (Bη * (P.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ P)) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = 2 ^ P * P.factorial * Bη * (1 + B) ^ P * (1 + τ) ^ P * exp (B * τ) := by
        rw [mul_pow, mul_comm τ B]
        ring

end Grammar
