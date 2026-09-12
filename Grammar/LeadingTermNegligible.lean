/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LeadingTermConsequences

/-!
# Negligible remainders and leading terms (CCLXXIII)

Generic remainder calculus for leading-term certificates (consult #85 unit 1):

* `HasLeadingTerm.add_isLittleO`: a remainder that is `o` of the scale does not change a
  certificate (coefficient included);
* `HasExponentialBound r`: `|r N| ≤ C e^{−κN}` for `N ≥ 0`, `κ > 0`; such a remainder is `o` of
  every power–log scale (`HasExponentialBound.isLittleO_powLogScale`), so
  `HasLeadingTerm.add_exponential`;
* the elementary integral estimate `|∫_S g e^{−NK}| ≤ e^{−κN} ∫_S |g|` when `K ≥ κ` a.e. on `S`
  (`abs_setIntegral_mul_exp_le`), hence `hasExponentialBound_setIntegral`;
* the compact phase gap: a continuous function positive on a compact set is bounded below by a
  positive constant (`exists_pos_le_of_isCompact`), so the Boltzmann integral over a compact set on
  which the phase is positive is exponentially small
  (`hasExponentialBound_setIntegral_of_isCompact`).

Compactness is one producer of the gap `κ`; the integral estimate itself does not use it.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

section Generic

variable {Z R : ℝ → ℝ} {c lam : ℝ} {k : ℕ}

/-- A remainder that is `o` of the scale does not change a leading-term certificate. -/
theorem HasLeadingTerm.add_isLittleO (h : HasLeadingTerm Z c lam k)
    (hR : R =o[atTop] powLogScale lam k) : HasLeadingTerm (fun N => Z N + R N) c lam k := by
  have h0 : HasLeadingTerm R 0 lam k := hR.tendsto_div_nhds_zero
  have := h.add h0
  rwa [add_zero] at this

/-- An exponential bound `|r N| ≤ C e^{−κN}` for all `N ≥ 0`, with `κ > 0`. -/
def HasExponentialBound (r : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℝ, 0 ≤ N → |r N| ≤ C * Real.exp (-κ * N)

theorem hasExponentialBound_zero : HasExponentialBound fun _ => 0 :=
  ⟨0, le_rfl, 1, one_pos, fun _ _ => by simp⟩

theorem HasExponentialBound.neg {r : ℝ → ℝ} (h : HasExponentialBound r) :
    HasExponentialBound fun N => -r N := by
  obtain ⟨C, hC, κ, hκ, hb⟩ := h
  exact ⟨C, hC, κ, hκ, fun N hN => by rw [abs_neg]; exact hb N hN⟩

theorem HasExponentialBound.add {r s : ℝ → ℝ} (hr : HasExponentialBound r)
    (hs : HasExponentialBound s) : HasExponentialBound fun N => r N + s N := by
  obtain ⟨C, hC, κ, hκ, hb⟩ := hr
  obtain ⟨C', hC', κ', hκ', hb'⟩ := hs
  refine ⟨C + C', add_nonneg hC hC', min κ κ', lt_min hκ hκ', fun N hN => ?_⟩
  have h1 : Real.exp (-κ * N) ≤ Real.exp (-min κ κ' * N) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left κ κ'])
  have h2 : Real.exp (-κ' * N) ≤ Real.exp (-min κ κ' * N) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right κ κ'])
  calc |r N + s N| ≤ |r N| + |s N| := abs_add_le _ _
    _ ≤ C * Real.exp (-κ * N) + C' * Real.exp (-κ' * N) := add_le_add (hb N hN) (hb' N hN)
    _ ≤ C * Real.exp (-min κ κ' * N) + C' * Real.exp (-min κ κ' * N) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hC) (mul_le_mul_of_nonneg_left h2 hC')
    _ = (C + C') * Real.exp (-min κ κ' * N) := by ring

theorem HasExponentialBound.sum {α : Type*} (s : Finset α) {r : α → ℝ → ℝ}
    (h : ∀ j ∈ s, HasExponentialBound (r j)) :
    HasExponentialBound fun N => ∑ j ∈ s, r j N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasExponentialBound_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HasExponentialBound.const_mul {r : ℝ → ℝ} (h : HasExponentialBound r) (a : ℝ) :
    HasExponentialBound fun N => a * r N := by
  obtain ⟨C, hC, κ, hκ, hb⟩ := h
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, κ, hκ, fun N hN => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb N hN) (abs_nonneg a)

/-- An exponentially small remainder is `o` of every power–log scale. -/
theorem HasExponentialBound.isLittleO_powLogScale {r : ℝ → ℝ} (hr : HasExponentialBound r)
    (lam : ℝ) (k : ℕ) : r =o[atTop] powLogScale lam k := by
  obtain ⟨C, _, κ, hκ, hb⟩ := hr
  have h1 : r =O[atTop] fun N => Real.exp (-κ * N) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hb N hN
  have h2 : (fun N : ℝ => Real.exp (-κ * N)) =o[atTop] fun N : ℝ => N ^ (-lam) :=
    isLittleO_exp_neg_mul_rpow_atTop hκ (-lam)
  exact (h1.trans_isLittleO h2).trans_isBigO (rpow_neg_isBigO_powLogScale lam k)

/-- An exponentially small remainder does not change a leading-term certificate. -/
theorem HasLeadingTerm.add_exponential (h : HasLeadingTerm Z c lam k)
    (hR : HasExponentialBound R) : HasLeadingTerm (fun N => Z N + R N) c lam k :=
  h.add_isLittleO (hR.isLittleO_powLogScale lam k)

/-- The exponential-remainder form: `Z = Z₀ + R` with `Z₀` certified and `R` exponentially small. -/
theorem hasLeadingTerm_of_eq_add_exponential {Z₀ : ℝ → ℝ} (h : HasLeadingTerm Z₀ c lam k)
    (hR : HasExponentialBound R) (hZ : ∀ N, 0 ≤ N → Z N = Z₀ N + R N) :
    HasLeadingTerm Z c lam k :=
  (h.add_exponential hR).congr' ((eventually_ge_atTop 0).mono fun N hN => (hZ N hN).symm)

end Generic

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- `|∫_S g e^{−NK}| ≤ e^{−κN} ∫_S |g|` when `K ≥ κ` a.e. on `S` and `N ≥ 0`. -/
theorem abs_setIntegral_mul_exp_le {S : Set X} {g K : X → ℝ} {κ N : ℝ}
    (hg : IntegrableOn g S μ) (hK : ∀ᵐ x ∂(μ.restrict S), κ ≤ K x) (hN : 0 ≤ N) :
    |∫ x in S, g x * Real.exp (-N * K x) ∂μ| ≤ Real.exp (-κ * N) * ∫ x in S, |g x| ∂μ := by
  calc |∫ x in S, g x * Real.exp (-N * K x) ∂μ|
      = ‖∫ x in S, g x * Real.exp (-N * K x) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in S, Real.exp (-κ * N) * |g x| ∂μ := by
      refine norm_integral_le_of_norm_le (hg.abs.const_mul _) ?_
      filter_upwards [hK] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      have := mul_le_mul_of_nonneg_left hx hN
      linarith
    _ = Real.exp (-κ * N) * ∫ x in S, |g x| ∂μ := integral_const_mul _ _

/-- The Boltzmann integral over a set on which the phase is bounded below by `κ > 0` a.e. is
exponentially small. -/
theorem hasExponentialBound_setIntegral {S : Set X} {g K : X → ℝ} {κ : ℝ}
    (hg : IntegrableOn g S μ) (hκ : 0 < κ) (hK : ∀ᵐ x ∂(μ.restrict S), κ ≤ K x) :
    HasExponentialBound fun N => ∫ x in S, g x * Real.exp (-N * K x) ∂μ :=
  ⟨∫ x in S, |g x| ∂μ, integral_nonneg fun _ => abs_nonneg _, κ, hκ, fun N hN =>
    (abs_setIntegral_mul_exp_le hg hK hN).trans_eq (mul_comm _ _)⟩

/-- Pointwise form on a measurable set. -/
theorem hasExponentialBound_setIntegral_of_forall {S : Set X} {g K : X → ℝ} {κ : ℝ}
    (hS : MeasurableSet S) (hg : IntegrableOn g S μ) (hκ : 0 < κ) (hK : ∀ x ∈ S, κ ≤ K x) :
    HasExponentialBound fun N => ∫ x in S, g x * Real.exp (-N * K x) ∂μ :=
  hasExponentialBound_setIntegral hg hκ (ae_restrict_of_forall_mem hS hK)

end Integral

section Compact

variable {X : Type*} [TopologicalSpace X]

/-- **The compact phase gap**: a function continuous and positive on a compact set is bounded below
on it by a positive constant. -/
theorem exists_pos_le_of_isCompact {S : Set X} {f : X → ℝ} (hS : IsCompact S)
    (hf : ContinuousOn f S) (hpos : ∀ x ∈ S, 0 < f x) : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ S, κ ≤ f x := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x hx => by simp [h] at hx⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn h hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}

/-- The Boltzmann integral over a compact set on which the phase is continuous and positive is
exponentially small. -/
theorem hasExponentialBound_setIntegral_of_isCompact {S : Set X} {g K : X → ℝ}
    (hS : IsCompact S) (hg : IntegrableOn g S μ) (hK : ContinuousOn K S)
    (hpos : ∀ x ∈ S, 0 < K x) :
    HasExponentialBound fun N => ∫ x in S, g x * Real.exp (-N * K x) ∂μ := by
  obtain ⟨κ, hκ, hle⟩ := exists_pos_le_of_isCompact hS hK hpos
  exact hasExponentialBound_setIntegral_of_forall hS.measurableSet hg hκ hle

end Compact

end Grammar
