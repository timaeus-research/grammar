/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalTailJets
import Grammar.FieldJetUniform

/-!
# Uniform geometric jet bounds for the exponential tails on jet balls (§20, Stage E)

`exists_famJetBound_tailFam` gives, for each smooth field, geometric jet bounds `K₀ (1/2)^R` for
the tail families `tailFam η ζ R = η · expTail R (τζ)`.  Here the constant is made UNIFORM over
the jet ball `JetBoundOn |p| (closedBox d 1) ζ B`, with the fixed exponential envelope
`e^{3Bτ}`:

★ `famJetBound_tailFam_of_jetBoundOn : ∃ C, ∀ ζ ∈ jet ball, ∀ R,
     FamJetBound (tailFam η ζ R) p 1 (C (1/2)^R) (3B)`.

Route: Faà di Bruno (`norm_iteratedFDeriv_comp_le`) for `expTail R ∘ (τζ)` with the derivative
identity `iteratedDeriv i (expTail R) = expTail (R − i)` and the geometric tail bound, Leibniz
with the weight, and the coordinate/Fréchet comparison `abs_pdMulti_le_norm_iteratedFDeriv`.

Zero `sorry`/`axiom`.
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ}

theorem iteratedDeriv_expTail (R i : ℕ) : iteratedDeriv i (expTail R) = expTail (R - i) := by
  induction i generalizing R with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ',
      show deriv (expTail R) = expTail (R - 1) from
        funext fun x => (hasDerivAt_expTail R x).deriv,
      ih, Nat.sub_sub, Nat.add_comm 1 i]

/-- Faà di Bruno for `expTail R ∘ (τ ζ)` at a point where the jets of `ζ` are bounded by `B`. -/
theorem norm_iteratedFDeriv_expTail_comp_le (hζ : ContDiff ℝ ∞ ζ) {B : ℝ} (hB : 0 ≤ B) {τ : ℝ}
    (hτ : 0 ≤ τ) (R n : ℕ) {v : Fin d → ℝ} (hbound : ∀ r ≤ n, ‖iteratedFDeriv ℝ r ζ v‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun v => expTail R (τ * ζ v)) v‖ ≤
      n.factorial * (2 ^ n * (1 / 2) ^ R * exp (3 * B * τ)) * ((1 + τ) * (1 + B)) ^ n := by
  have hζv : |ζ v| ≤ B := by
    have := hbound 0 (Nat.zero_le _)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hf : ContDiff ℝ ∞ fun v => τ * ζ v := contDiff_const.mul hζ
  have hg : ContDiff ℝ ∞ (expTail R) := (contDiff_expTail R).of_le le_top
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i (expTail R) ((fun v => τ * ζ v) v)‖ ≤
      2 ^ n * (1 / 2) ^ R * exp (3 * B * τ) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expTail, Real.norm_eq_abs]
    calc |expTail (R - i) (τ * ζ v)| ≤ (1 / 2) ^ (R - i) * exp (3 * |τ * ζ v|) :=
          abs_expTail_le_half _ _
      _ ≤ (2 ^ n * (1 / 2) ^ R) * exp (3 * B * τ) := by
          refine mul_le_mul (half_pow_sub_le hi R) ?_ (exp_nonneg _) (by positivity)
          refine exp_le_exp.2 ?_
          rw [abs_mul, abs_of_nonneg hτ]
          have := mul_le_mul_of_nonneg_left hζv hτ
          linarith
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
  exact norm_iteratedFDeriv_comp_le (g := expTail R) (f := fun v => τ * ζ v) hg hf
    (natCast_le_infty n) v hC hD

/-- The Fréchet jets of the tail family `η · expTail R (τζ)` at a point where the jets of `η` are
bounded by `Bη` and those of `ζ` by `B`. -/
theorem norm_iteratedFDeriv_tailFam_le (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {B Bη : ℝ}
    (hB : 0 ≤ B) (hBη0 : 0 ≤ Bη) {τ : ℝ} (hτ : 0 ≤ τ) (R r : ℕ) {v : Fin d → ℝ}
    (hηB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i η v‖ ≤ Bη) (hζB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i ζ v‖ ≤ B) :
    ‖iteratedFDeriv ℝ r (tailFam η ζ R τ) v‖ ≤
      2 ^ r * (Bη * (r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) *
        ((1 + τ) * (1 + B)) ^ r)) := by
  have hT : ContDiff ℝ ∞ fun v => expTail R (τ * ζ v) :=
    ((contDiff_expTail R).of_le le_top).comp (contDiff_const.mul hζ)
  have h2 : ‖iteratedFDeriv ℝ r (tailFam η ζ R τ) v‖ ≤ ∑ i ∈ range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
        ‖iteratedFDeriv ℝ (r - i) (fun v => expTail R (τ * ζ v)) v‖ :=
    norm_iteratedFDeriv_mul_le hη hT v (natCast_le_infty r)
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have h3 : ∀ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
      ‖iteratedFDeriv ℝ (r - i) (fun v => expTail R (τ * ζ v)) v‖ ≤
      (r.choose i : ℝ) * (Bη * (r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) *
        ((1 + τ) * (1 + B)) ^ r)) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hηi : ‖iteratedFDeriv ℝ i η v‖ ≤ Bη := hηB i hi'
    have hTi := norm_iteratedFDeriv_expTail_comp_le hζ hB hτ R (r - i) (v := v)
      fun s hs => hζB s (hs.trans (Nat.sub_le r i))
    have hfac : ((r - i).factorial : ℝ) ≤ r.factorial := by
      exact_mod_cast Nat.factorial_le (Nat.sub_le r i)
    have hp2 : (2 : ℝ) ^ (r - i) ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (Nat.sub_le r i)
    have hpow : ((1 + τ) * (1 + B)) ^ (r - i) ≤ ((1 + τ) * (1 + B)) ^ r :=
      pow_le_pow_right₀ hD1 (Nat.sub_le r i)
    have hTi' : ‖iteratedFDeriv ℝ (r - i) (fun v => expTail R (τ * ζ v)) v‖ ≤
        r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) * ((1 + τ) * (1 + B)) ^ r :=
      hTi.trans (by gcongr)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hηi hTi' (norm_nonneg _) hBη0
  have h4 : ∑ i ∈ range (r + 1), (r.choose i : ℝ) *
      (Bη * (r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) * ((1 + τ) * (1 + B)) ^ r)) =
      2 ^ r * (Bη * (r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) *
        ((1 + τ) * (1 + B)) ^ r)) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose r
  exact h2.trans ((Finset.sum_le_sum h3).trans h4.le)

/-- ★ **Uniform geometric jet bounds for the tails on jet balls**: one constant `C` for all smooth
fields with `JetBoundOn |p| (closedBox d 1) ζ B`, with the fixed envelope `e^{3Bτ}`. -/
theorem famJetBound_tailFam_of_jetBoundOn (hη : ContDiff ℝ ∞ η) (p : Fin d → ℕ) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (∑ i, p i) (closedBox d 1) ζ B →
      ∀ R : ℕ, FamJetBound (tailFam η ζ R) p 1 (C * (1 / 2) ^ R) (3 * B) := by
  set P : ℕ := ∑ i, p i with hP
  obtain ⟨Bη, hBη0, hBη⟩ := exists_jetBoundOn hη P (isCompact_closedBox 1)
  refine ⟨2 ^ P * (Bη * (P.factorial * 2 ^ P * (1 + B) ^ P)), by positivity,
    fun ζ hζ hζB R m hm τ hτ v hv => ?_⟩
  have hr : ∑ i, m i ≤ P := Finset.sum_le_sum fun i _ => hm i
  set r : ℕ := ∑ i, m i with hr'
  have htail : ContDiff ℝ ∞ (tailFam η ζ R τ) :=
    contDiff_famSlice (contDiff_tailFam_joint hη hζ R) τ
  have h1 : |pdMulti m (List.finRange d) (tailFam η ζ R τ) v| ≤
      ‖iteratedFDeriv ℝ r (tailFam η ζ R τ) v‖ := by
    have := abs_pdMulti_le_norm_iteratedFDeriv htail m (List.finRange d) v
    rwa [wordLen_finRange] at this
  have h2 := norm_iteratedFDeriv_tailFam_le hη hζ hB hBη0 hτ R r (v := v)
    (fun i hi => hBη i (hi.trans hr) v hv) (fun i hi => hζB i (hi.trans hr) v hv)
  refine h1.trans (h2.trans ?_)
  have hτ1 : (1 : ℝ) ≤ 1 + τ := by linarith
  have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have hfac : (r.factorial : ℝ) ≤ P.factorial := by exact_mod_cast Nat.factorial_le hr
  have hp2 : (2 : ℝ) ^ r ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) hr
  have hpow : ((1 + τ) * (1 + B)) ^ r ≤ (1 + τ) ^ P * (1 + B) ^ P := by
    rw [← mul_pow]
    exact pow_le_pow_right₀ hD1 hr
  calc 2 ^ r * (Bη * (r.factorial * (2 ^ r * (1 / 2) ^ R * exp (3 * B * τ)) *
        ((1 + τ) * (1 + B)) ^ r))
      ≤ 2 ^ P * (Bη * (P.factorial * (2 ^ P * (1 / 2) ^ R * exp (3 * B * τ)) *
        ((1 + τ) ^ P * (1 + B) ^ P))) := by gcongr
    _ = 2 ^ P * (Bη * (P.factorial * 2 ^ P * (1 + B) ^ P)) * (1 / 2) ^ R * (1 + τ) ^ P *
        exp (3 * B * τ) := by ring

end Grammar
