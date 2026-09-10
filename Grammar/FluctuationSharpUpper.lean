import Grammar.FluctuationSharpBounds

/-!
# The polynomially sharp upper bound on the fluctuation function

`FluctuationSharpBounds.lean` gives `S_λ(a) ≥ e^{−β}4^{−max(λ−1,0)} a^{2λ−1} e^{βa²/4}` for `a ≥ 2`.
This file proves the matching **upper** bound

`S_λ(a) ≤ C a^{2λ−1} e^{βa²/4}` for `a ≥ 2` (`fluctuation_le_polynomial_mul_gaussian`),

so that `S_λ(a) ≍ a^{2λ−1}e^{βa²/4}` as `a → ∞`, the input for the critical-line classification of
the `p`-th moments (`pβv = 2`). Completing the square, `S_λ(a) = e^{βa²/4} ∫₀^∞ t^{λ−1}
e^{−β(√t − a/2)²} dt` (`fluctuation_eq_exp_mul_integral`); the remaining integral is split at the
window `A = [a²/16, 9a²/16]` (where `√t ∈ [a/4, 3a/4]`): on `A`, `t^{λ−1} ≤ c_A a^{2λ−2}` and
`β(√t − a/2)² ≥ (16β/(25a²))(t − a²/4)²`, so the window contributes at most `c_A a^{2λ−2} ·
(5a/4)√(π/β)`; off `A`, `(√t − a/2)² ≥ a²/16` and the `η = 1/10` bound of `fluctuation_le_eta` at
temperature `β/2` gives a contribution `≤ Γ(λ)(β/20)^{−λ} e^{−5βa²/288}`, which is `≤ C' a^{2λ−1}`
for `a ≥ 2` since `e^{x} ≥ x^k/k!`. No change of variables is used.
-/

open Real MeasureTheory Set

namespace Grammar

/-- Completing the square: `S_λ(a) = e^{βa²/4} ∫₀^∞ t^{λ−1} e^{−β(√t − a/2)²} dt`. -/
theorem fluctuation_eq_exp_mul_integral (β lam a : ℝ) :
    fluctuation β lam a = Real.exp (β * a ^ 2 / 4) *
      ∫ t in Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * (Real.sqrt t - a / 2) ^ 2) := by
  rw [fluctuation, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hsq := Real.sq_sqrt (le_of_lt ht)
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  linear_combination β * hsq

/-- `(x²/y)^z = y^{−z} x^{2z}` for `x, y > 0`. -/
theorem sq_div_rpow (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x ^ 2 / y) ^ z = y ^ (-z) * x ^ (2 * z) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hx,
    ← Real.exp_add, Real.log_div (by positivity) hy.ne', Real.log_pow]
  congr 1
  push_cast
  ring

/-- **The polynomially sharp upper bound**: there is `C > 0` with
`S_λ(a) ≤ C a^{2λ−1} e^{βa²/4}` for all `a ≥ 2`. -/
theorem fluctuation_le_polynomial_mul_gaussian (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 2 ≤ a →
      fluctuation β lam a ≤ C * a ^ (2 * lam - 1) * Real.exp (β * a ^ 2 / 4) := by
  set cA : ℝ := max ((16 : ℝ) ^ (-(lam - 1))) ((9 / 16 : ℝ) ^ (lam - 1)) with hcA
  have hcA0 : 0 < cA := lt_max_of_lt_left (Real.rpow_pos_of_pos (by norm_num) _)
  set k : ℕ := ⌈|2 * lam - 1| / 2⌉₊ with hk
  set cB : ℝ := Real.Gamma lam * (β / 20) ^ (-lam) *
    ((k.factorial : ℝ) * (288 / (5 * β)) ^ k) with hcB
  have hcB0 : 0 < cB := by
    have := Real.Gamma_pos_of_pos hlam
    positivity
  refine ⟨cA * (5 / 4) * Real.sqrt (Real.pi / β) + cB, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  rw [fluctuation_eq_exp_mul_integral]
  set f : ℝ → ℝ := fun t => t ^ (lam - 1) * Real.exp (-β * (Real.sqrt t - a / 2) ^ 2) with hf
  suffices hJ : ∫ t in Ioi (0 : ℝ), f t ≤
      (cA * (5 / 4) * Real.sqrt (Real.pi / β) + cB) * a ^ (2 * lam - 1) by
    calc Real.exp (β * a ^ 2 / 4) * ∫ t in Ioi (0 : ℝ), f t
        ≤ Real.exp (β * a ^ 2 / 4) *
          ((cA * (5 / 4) * Real.sqrt (Real.pi / β) + cB) * a ^ (2 * lam - 1)) :=
          mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le
      _ = _ := by ring
  have hf0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  have hfint : IntegrableOn f (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => Real.exp (-(β * a ^ 2 / 4)) *
        (t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t))) (Ioi 0) :=
      (fluctuation_integrableOn β lam hβ hlam a).const_mul _
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have hsq := Real.sq_sqrt (le_of_lt ht)
    simp only [hf]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    linear_combination β * hsq
  set A : Set ℝ := Icc (a ^ 2 / 16) (9 * a ^ 2 / 16) with hA
  have hAm : MeasurableSet A := measurableSet_Icc
  rw [← integral_inter_add_sdiff hAm hfint, add_mul]
  refine add_le_add ?_ ?_
  · -- the window
    set κ : ℝ := 16 * β / (25 * a ^ 2) with hκ
    have hκ0 : 0 < κ := by positivity
    set g : ℝ → ℝ := fun t => cA * a ^ (2 * lam - 2) * Real.exp (-κ * (t - a ^ 2 / 4) ^ 2) with hg
    have hgint : Integrable g :=
      ((integrable_exp_neg_mul_sq hκ0).comp_sub_right (a ^ 2 / 4)).const_mul _
    have hpt : ∀ t ∈ Ioi (0 : ℝ) ∩ A, f t ≤ g t := by
      rintro t ⟨ht0, ht1, ht2⟩
      have ht0' : (0 : ℝ) < t := ht0
      have hs := Real.sq_sqrt ht0'.le
      have hs0 := Real.sqrt_nonneg t
      have hs2 : Real.sqrt t ≤ 3 * a / 4 := by
        rw [show 3 * a / 4 = Real.sqrt ((3 * a / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hpow : t ^ (lam - 1) ≤ cA * a ^ (2 * lam - 2) := by
        rcases le_or_gt lam 1 with hl | hl
        · calc t ^ (lam - 1) ≤ (a ^ 2 / 16) ^ (lam - 1) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) ht1 (by linarith)
            _ = (16 : ℝ) ^ (-(lam - 1)) * a ^ (2 * lam - 2) := by
                rw [sq_div_rpow a 16 (lam - 1) ha0 (by norm_num)]
                ring_nf
            _ ≤ cA * a ^ (2 * lam - 2) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ha0.le _)
        · calc t ^ (lam - 1) ≤ (9 * a ^ 2 / 16) ^ (lam - 1) :=
                Real.rpow_le_rpow ht0'.le ht2 (by linarith)
            _ = (9 / 16 : ℝ) ^ (lam - 1) * a ^ (2 * lam - 2) := by
                rw [show 9 * a ^ 2 / 16 = a ^ 2 / (16 / 9) by ring,
                  sq_div_rpow a (16 / 9) (lam - 1) ha0 (by norm_num),
                  Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), inv_div]
                ring_nf
            _ ≤ cA * a ^ (2 * lam - 2) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ha0.le _)
      have hexp : Real.exp (-β * (Real.sqrt t - a / 2) ^ 2) ≤
          Real.exp (-κ * (t - a ^ 2 / 4) ^ 2) := by
        rw [Real.exp_le_exp]
        have h1 : t - a ^ 2 / 4 = (Real.sqrt t - a / 2) * (Real.sqrt t + a / 2) := by
          linear_combination -hs
        have h2 : (Real.sqrt t + a / 2) ^ 2 ≤ (5 * a / 4) ^ 2 := by nlinarith
        rw [h1, mul_pow, hκ, neg_mul, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div,
          div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h2
          (mul_nonneg hβ.le (sq_nonneg (Real.sqrt t - a / 2)))]
      exact mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    calc ∫ t in Ioi (0 : ℝ) ∩ A, f t ≤ ∫ t in Ioi (0 : ℝ) ∩ A, g t :=
          setIntegral_mono_on (hfint.mono_set inter_subset_left) hgint.integrableOn
            (measurableSet_Ioi.inter hAm) hpt
      _ ≤ ∫ t, g t :=
          setIntegral_le_integral hgint (Filter.Eventually.of_forall fun t => by positivity)
      _ = cA * a ^ (2 * lam - 2) * ∫ t, Real.exp (-κ * (t - a ^ 2 / 4) ^ 2) :=
          integral_const_mul _ _
      _ = cA * a ^ (2 * lam - 2) * Real.sqrt (Real.pi / κ) := by
          rw [integral_sub_right_eq_self (fun t => Real.exp (-κ * t ^ 2)) (a ^ 2 / 4),
            integral_gaussian]
      _ = cA * (5 / 4) * Real.sqrt (Real.pi / β) * a ^ (2 * lam - 1) := by
          rw [hκ, show Real.pi / (16 * β / (25 * a ^ 2)) = (5 * a / 4) ^ 2 * (Real.pi / β) by
            field_simp; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            show a ^ (2 * lam - 1) = a ^ (2 * lam - 2) * a by
              rw [← Real.rpow_add_one ha0.ne']; ring_nf]
          ring
  · -- off the window
    set h : ℝ → ℝ := fun t => Real.exp (-(β * a ^ 2 / 32)) *
      (t ^ (lam - 1) * Real.exp (-(β / 2) * (Real.sqrt t - a / 2) ^ 2)) with hh
    have hβ2 : 0 < β / 2 := by positivity
    have hhint : IntegrableOn h (Ioi 0) := by
      have this : IntegrableOn (fun t : ℝ => Real.exp (-(β * a ^ 2 / 32)) *
          (Real.exp (-(β / 2 * a ^ 2 / 4)) *
            (t ^ (lam - 1) * Real.exp (-(β / 2) * t + β / 2 * a * Real.sqrt t)))) (Ioi 0) :=
        ((fluctuation_integrableOn (β / 2) lam hβ2 hlam a).const_mul _).const_mul _
      refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have hsq := Real.sq_sqrt (le_of_lt ht)
      simp only [hh]
      congr 1
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      linear_combination (β / 2) * hsq
    have hpt : ∀ t ∈ Ioi (0 : ℝ) \ A, f t ≤ h t := by
      rintro t ⟨ht0, htA⟩
      have ht0' : (0 : ℝ) < t := ht0
      have hs := Real.sq_sqrt ht0'.le
      have hs0 := Real.sqrt_nonneg t
      have hfar : a ^ 2 / 16 ≤ (Real.sqrt t - a / 2) ^ 2 := by
        simp only [hA, mem_Icc, not_and_or, not_le] at htA
        rcases htA with h1 | h1
        · have : Real.sqrt t < a / 4 := by
            rw [Real.sqrt_lt' (by positivity)]
            nlinarith
          nlinarith
        · have : 3 * a / 4 < Real.sqrt t := by
            rw [Real.lt_sqrt (by positivity)]
            nlinarith
          nlinarith
      simp only [hf, hh]
      rw [mul_left_comm, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht0'.le _)
      nlinarith
    have hval : ∫ t in Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-(β / 2) * (Real.sqrt t - a / 2) ^ 2)
        = Real.exp (-(β / 2 * a ^ 2 / 4)) * fluctuation (β / 2) lam a := by
      rw [fluctuation_eq_exp_mul_integral (β / 2) lam a, ← mul_assoc, ← Real.exp_add,
        show -(β / 2 * a ^ 2 / 4) + β / 2 * a ^ 2 / 4 = 0 by ring, Real.exp_zero, one_mul]
    have hS := fluctuation_le_eta (β / 2) a lam (1 / 10) hβ2 hlam (by norm_num) (by norm_num)
    rw [max_eq_left ha0.le] at hS
    -- the tail bound `e^{−x} ≤ k!/x^k`
    set x : ℝ := 5 * β / 288 * a ^ 2 with hx
    have hx0 : 0 < x := by positivity
    have htail : Real.exp (-x) ≤ (k.factorial : ℝ) / x ^ k := by
      rw [Real.exp_neg, ← inv_div]
      exact inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp x hx0.le k)
    have hkpow : (k.factorial : ℝ) / x ^ k =
        (k.factorial : ℝ) * (288 / (5 * β)) ^ k * a ^ (-(2 * k : ℝ)) := by
      have e1 : a ^ (-(2 * k : ℝ)) = (a ^ (2 * k))⁻¹ := by
        rw [Real.rpow_neg ha0.le, show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      rw [e1, hx, mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv, ← inv_pow, inv_div]
      ring
    have hkle : a ^ (-(2 * k : ℝ)) ≤ a ^ (2 * lam - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le ha1 ?_
      have h1 : |2 * lam - 1| / 2 ≤ k := Nat.le_ceil _
      have h2 : -(2 * lam - 1) ≤ |2 * lam - 1| := neg_le_abs _
      linarith
    calc ∫ t in Ioi (0 : ℝ) \ A, f t ≤ ∫ t in Ioi (0 : ℝ) \ A, h t :=
          setIntegral_mono_on (hfint.mono_set sdiff_subset) (hhint.mono_set sdiff_subset)
            (measurableSet_Ioi.diff hAm) hpt
      _ ≤ ∫ t in Ioi (0 : ℝ), h t :=
          setIntegral_mono_set hhint (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le))
            (Filter.Eventually.of_forall sdiff_subset)
      _ = Real.exp (-(β * a ^ 2 / 32)) *
          (Real.exp (-(β / 2 * a ^ 2 / 4)) * fluctuation (β / 2) lam a) := by
          rw [integral_const_mul, hval]
      _ ≤ Real.exp (-(β * a ^ 2 / 32)) * (Real.exp (-(β / 2 * a ^ 2 / 4)) *
          (Real.Gamma lam * (β / 2 * (1 / 10)) ^ (-lam) *
            Real.exp (β / 2 * a ^ 2 / (4 * (1 - 1 / 10))))) := by gcongr
      _ = Real.Gamma lam * (β / 20) ^ (-lam) * Real.exp (-x) := by
          rw [hx, show β / 2 * (1 / 10) = β / 20 by ring]
          rw [show Real.exp (-(β * a ^ 2 / 32)) * (Real.exp (-(β / 2 * a ^ 2 / 4)) *
              (Real.Gamma lam * (β / 20) ^ (-lam) *
                Real.exp (β / 2 * a ^ 2 / (4 * (1 - 1 / 10))))) =
              Real.Gamma lam * (β / 20) ^ (-lam) * (Real.exp (-(β * a ^ 2 / 32)) *
                Real.exp (-(β / 2 * a ^ 2 / 4)) * Real.exp (β / 2 * a ^ 2 / (4 * (1 - 1 / 10)))) by
              ring, ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
      _ ≤ Real.Gamma lam * (β / 20) ^ (-lam) * ((k.factorial : ℝ) / x ^ k) := by gcongr
      _ = cB * a ^ (-(2 * k : ℝ)) := by rw [hkpow, hcB]; ring
      _ ≤ cB * a ^ (2 * lam - 1) := mul_le_mul_of_nonneg_left hkle hcB0.le

end Grammar
