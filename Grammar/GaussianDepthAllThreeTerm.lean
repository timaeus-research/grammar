/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthAllTwoTerm
import Grammar.GaussianDepthThreeRate

/-!
# The Gaussian DLN at every depth: the three-term propagation step

The two-term engine of `GaussianDepthAllTwoTerm` propagates the leading two logarithmic
coefficients through the Gaussian step `F(N) = ∫ g(x) f(N x²) dx`.  Here a third coefficient is
carried: for three-term data `|f(t) − (A ℓ^{m+3} + B ℓ^{m+2} + C ℓ^{m+1})/√t| ≤ D(1 + ℓ)^m/√t`
(`ThreeTermData`, `ℓ = log t`), the step has three-term data with

  `A' = A/((m+4)s)`, `B' = (B/(m+3) + 2A R₀)/s`, `C' = (C/(m+2) + 2B R₀ + 4(m+3) A J)/s`,

`s = √(2π)`, `R₀ = (log 2 − γ)/2`, `J = ∫₀^∞ h log x/x` (`gaussJlog`), and error `D'(1+ℓ)^{m+1}/√N`
(★★ `threeTermStep_bound`).  The new ingredient is the second-order binomial expansion of the top
term against `h/x` (★ `integral_gaussH_pow_expand₂`): the moments `∫_a^∞ h/x → R₀` and
`∫_a^∞ h log x/x → J` are retained exactly, all higher log-moments are bounded
(`gaussH_log_pow_moment_le`).  The base at depth four and the induction are in
`GaussianDepthAllThirdCoeff`.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The second-order binomial expansion -/

/-- `K₂_n = Σ_{i ≤ n} C(n+2, i) 2^{n+2−i} M_{n+2−i}`. -/
noncomputable def threeTermK (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i) * gaussHMoment (n + 2 - i)

theorem threeTermK_nonneg (n : ℕ) : 0 ≤ threeTermK n :=
  Finset.sum_nonneg fun i _ => by
    have := gaussHMoment_nonneg (n + 2 - i)
    positivity

/-- ★ **The second-order expansion**:
`|∫_a^∞ h (ℓ + 2 log x)^{n+2}/x − ℓ^{n+2} ∫_a^∞ h/x − 2(n+2) ℓ^{n+1} ∫_a^∞ h log x/x|
  ≤ (1+ℓ)^n K₂_n`
for `ℓ ≥ 0`, `0 < a ≤ 1`. -/
theorem integral_gaussH_pow_expand₂ (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    |(∫ x in Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 2) / x) -
      ℓ ^ (n + 2) * (∫ x in Ioi a, gaussH x / x) -
      2 * (n + 2) * ℓ ^ (n + 1) * ∫ x in Ioi a, gaussH x * Real.log x / x| ≤
      (1 + ℓ) ^ n * threeTermK n := by
  have e : ∀ x ∈ Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 2) / x =
      ∑ i ∈ Finset.range (n + 3), (ℓ ^ i * ((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i)) *
        (gaussH x * (Real.log x) ^ (n + 2 - i) / x) := by
    intro x _
    rw [add_pow, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  have hint : ∀ i ∈ Finset.range (n + 3), IntegrableOn
      (fun x : ℝ => (ℓ ^ i * ((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i)) *
        (gaussH x * (Real.log x) ^ (n + 2 - i) / x)) (Ioi a) :=
    fun i _ => (integrableOn_gaussH_log_pow (n + 2 - i) ha0.le ha1).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_finsetSum _ hint]
  simp_rw [integral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero,
    show n + 2 - (n + 1) = 1 by omega, Nat.choose_succ_self_right]
  simp only [Nat.cast_one, mul_one, pow_one]
  have hlast : ∫ x in Ioi a, gaussH x * (Real.log x) ^ 0 / x = ∫ x in Ioi a, gaussH x / x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp
  rw [hlast]
  have hcast : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hY : 2 * ((n : ℝ) + 2) * ℓ ^ (n + 1) * (∫ x in Ioi a, gaussH x * Real.log x / x) =
      ℓ ^ (n + 1) * ((n : ℝ) + 2) * 2 * ∫ x in Ioi a, gaussH x * Real.log x / x := by ring
  rw [hcast, hY, show ∀ S Y Z : ℝ, S + Y + Z - Z - Y = S from fun S Y Z => by ring]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold threeTermK
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hM := gaussH_log_pow_moment_le (n + 2 - i) ha0.le ha1
  have hℓi : ℓ ^ i ≤ (1 + ℓ) ^ n :=
    calc ℓ ^ i ≤ (1 + ℓ) ^ i := pow_le_pow_left₀ hℓ (by linarith) i
      _ ≤ (1 + ℓ) ^ n := pow_le_pow_right₀ (by linarith) hi'
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc ℓ ^ i * ((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i) *
        |∫ x in Ioi a, gaussH x * (Real.log x) ^ (n + 2 - i) / x|
      ≤ (1 + ℓ) ^ n * ((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i) * gaussHMoment (n + 2 - i) := by
        gcongr
    _ = (1 + ℓ) ^ n * (((n + 2).choose i : ℝ) * 2 ^ (n + 2 - i) * gaussHMoment (n + 2 - i)) := by
        ring

/-! ### The three-term data -/

/-- Three-term hypotheses: `0 ≤ f ≤ 1` on `t ≥ 0` and
`|f(t) − (A ℓ^{m+3} + B ℓ^{m+2} + C ℓ^{m+1})/√t| ≤ D (1 + ℓ)^m/√t` for `t ≥ 1`, `ℓ = log t`. -/
structure ThreeTermData (f : ℝ → ℝ) (A B C D : ℝ) (m : ℕ) : Prop where
  A_nonneg : 0 ≤ A
  D_nonneg : 0 ≤ D
  f_nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  f_le_one : ∀ t, 0 ≤ t → f t ≤ 1
  bound : ∀ t, 1 ≤ t →
    |f t - (A * (Real.log t) ^ (m + 3) + B * (Real.log t) ^ (m + 2) +
      C * (Real.log t) ^ (m + 1)) / Real.sqrt t| ≤ D * (1 + Real.log t) ^ m / Real.sqrt t

variable {f : ℝ → ℝ} {A B C D : ℝ} {m : ℕ}

/-- The inner piece: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem threeTerm_inner_le (h : ThreeTermData f A B C D m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussDensity x * f (N * x ^ 2)) (C := 1 / Real.sqrt (2 * Real.pi))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      have h0 := h.f_nonneg (N * x ^ 2) (by positivity)
      have h1 := h.f_le_one (N * x ^ 2) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _) h0)]
      calc gaussDensity x * f (N * x ^ 2) ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
            mul_le_mul (gaussDensity_le x) h1 h0 (by positivity)
        _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _)
  have hv : volume.real (Ioc (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rwa [Real.norm_eq_abs, hv] at hb

/-- `|J_a − J| ≤ 1/(2√N)` for `N ≥ 1`, `a = N^{−1/2}`. -/
theorem abs_logMoment_cutoff_le {N : ℝ} (hN : 1 ≤ N) :
    |(∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) - gaussJlog| ≤
      1 / Real.sqrt N / 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hsplit : gaussJlog = (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
      ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x := by
    unfold gaussJlog
    rw [← Ioc_union_Ioi_eq_Ioi ha0,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_gaussH_log_Ioc le_rfl |>.mono_set (Ioc_subset_Ioc_right ha1))
        (integrableOn_gaussH_log ha0 ha1)]
  rw [hsplit, show ∀ A B : ℝ, B - (A + B) = -A from fun A B => by ring, abs_neg]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (0 : ℝ) (1 / Real.sqrt N)) (f := fun x => gaussH x * Real.log x / x) (C := 1 / 2)
    measure_Ioc_lt_top (fun x hx => norm_gaussH_log_inner ⟨hx.1, hx.2.trans ha1⟩)
  rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0]
    at hb
  linarith

/-- The flat main term on `(a, 1]`:
`∫_a^1 Q/(√(2π)√N x) = (A ℓ^{m+4}/(2(m+4)) + B ℓ^{m+3}/(2(m+3)) + C ℓ^{m+2}/(2(m+2)))/(√(2π)√N)`. -/
theorem threeTerm_flat_main (A B C : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ (m + 4) / (2 * (m + 4)) + B * (Real.log N) ^ (m + 3) / (2 * (m + 3)) +
          C * (Real.log N) ^ (m + 2) / (2 * (m + 2))) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((Real.log N + 2 * Real.log x) ^ (m + 1) / x) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx.1
    field_simp
  have h3 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) (m + 3) ha0 ha1)
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) (m + 2) ha0 ha1)
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) (m + 1) ha0 ha1)
  have h32 : IntegrableOn (fun x : ℝ =>
      A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
      B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 2) / x))
      (Ioc (1 / Real.sqrt N) 1) := (h3.const_mul _).add (h2.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_add h32 (h1.const_mul _),
    integral_add (h3.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_pow_log_div _ _ ha0 ha1,
    integral_pow_log_div _ _ ha0 ha1, integral_pow_log_div _ _ ha0 ha1]
  have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
  rw [hloga, show Real.log N + 2 * -(Real.log N / 2) = 0 by ring, zero_pow (by omega),
    zero_pow (by omega), zero_pow (by omega), sub_zero, sub_zero, sub_zero]
  push_cast
  field_simp
  ring

/-- The `h`-part of the main term on `(a, ∞)`: with `R₀ = ∫₀^∞ h/x`, `J = ∫₀^∞ h log x/x`,
`∫_a^∞ h Q/(√(2π)√N x) = (A ℓ^{m+3} R₀ + 2(m+3) A ℓ^{m+2} J + B ℓ^{m+2} R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ (1+ℓ)^{m+1} (A (K₂_{m+1} + 2 + 2(m+3)) + |B| (K_{m+1} + 1) + |C| (K_m + R₀ + 1))`. -/
theorem threeTerm_h_main (A B C : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ (m + 3) * gaussR₀ +
        2 * (m + 3) * A * (Real.log N) ^ (m + 2) * gaussJlog +
        B * (Real.log N) ^ (m + 2) * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((1 + Real.log N) ^ (m + 1) *
        (A * (threeTermK (m + 1) + 2 + 2 * (m + 3)) + |B| * (twoTermK (m + 1) + 1) +
          |C| * (twoTermK m + gaussR₀ + 1))) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓN : Real.log N ≤ 2 * N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hℓs : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
  have hℓ2 : (Real.log N) ^ 2 ≤ 4 * N := by
    have := Real.sq_sqrt hN0.le
    nlinarith
  have hR0 : 0 ≤ gaussR₀ := by
    unfold gaussR₀
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
          B * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
          C * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx
    field_simp
  have h3 := integrableOn_gaussH_pow (m + 3) (Real.log N) ha0 ha1
  have h2 := integrableOn_gaussH_pow (m + 2) (Real.log N) ha0 ha1
  have h1 := integrableOn_gaussH_pow (m + 1) (Real.log N) ha0 ha1
  have h32 : IntegrableOn (fun x : ℝ =>
      A * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
      B * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x)) (Ioi (1 / Real.sqrt N)) :=
    (h3.const_mul _).add (h2.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_add h32 (h1.const_mul _), integral_add (h3.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the three expansions and the cutoffs
  have hE3 := integral_gaussH_pow_expand₂ (m + 1) hℓ ha0 ha1
  have hE2 := integral_gaussH_pow_expand (m + 1) hℓ ha0 ha1
  have hE1 := integral_gaussH_pow_expand m hℓ ha0 ha1
  have hI := abs_integral_gaussH_div_Ioc_le ha0.le ha1
  have hIa2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  rw [hIa2] at hI
  have hJ := abs_logMoment_cutoff_le hN
  rw [integral_gaussH_div_Ioi ha0.le] at hE3 hE2 hE1
  rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at hE3
  rw [show m + 1 + 1 = m + 2 by ring] at hE2
  push_cast at hE3
  rw [show (m : ℝ) + 1 + 2 = m + 3 by ring] at hE3
  set J3 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 3) / x
    with hJ3
  set J2 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x
    with hJ2
  set J1 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x
    with hJ1
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa
  set Ja := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x with hJa
  clear_value J3 J2 J1 Ia Ja
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set K2 := threeTermK (m + 1) with hK2
  set K1 := twoTermK (m + 1) with hK1
  set K0 := twoTermK m with hK0
  have hK2' : 0 ≤ K2 := threeTermK_nonneg (m + 1)
  have hK1' : 0 ≤ K1 := twoTermK_nonneg (m + 1)
  have hK0' : 0 ≤ K0 := twoTermK_nonneg m
  clear_value K2 K1 K0
  set R := gaussR₀ with hR
  set J := gaussJlog with hJdef
  clear_value R J
  have hIabs : |Ia| ≤ 1 / N / 2 := hI
  have hJabs : |Ja - J| ≤ 1 / Real.sqrt N / 2 := hJ
  clear hJ3 hJ2 hJ1 hIa hJa hℓdef hK2 hK1 hK0 hR hJdef e h3 h2 h1 h32 hI hJ hIa2
  have hp1 : 1 ≤ (1 + ℓ) ^ (m + 1) := one_le_pow₀ (by linarith)
  have hpm : ℓ ^ (m + 1) ≤ (1 + ℓ) ^ (m + 1) := pow_le_pow_left₀ hℓ (by linarith) _
  have hpm0 : ℓ ^ m ≤ (1 + ℓ) ^ m := pow_le_pow_left₀ hℓ (by linarith) _
  have hpm0' : (1 + ℓ) ^ m ≤ (1 + ℓ) ^ (m + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
  -- cutoffs
  have hcut3 : |ℓ ^ (m + 3) * Ia| ≤ 2 * (1 + ℓ) ^ (m + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity), show m + 3 = (m + 1) + 2 by ring, pow_add]
    calc ℓ ^ (m + 1) * ℓ ^ 2 * |Ia| ≤ (1 + ℓ) ^ (m + 1) * ℓ ^ 2 * (1 / N / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hpm (by positivity)) hIabs (abs_nonneg _)
            (by positivity)
      _ = (1 + ℓ) ^ (m + 1) * (ℓ ^ 2 / (2 * N)) := by ring
      _ ≤ (1 + ℓ) ^ (m + 1) * 2 := by
          gcongr
          rw [div_le_iff₀ (by positivity)]; linarith
      _ = 2 * (1 + ℓ) ^ (m + 1) := by ring
  have hcut2 : |ℓ ^ (m + 2) * Ia| ≤ (1 + ℓ) ^ (m + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity), pow_succ]
    calc ℓ ^ (m + 1) * ℓ * |Ia| ≤ ℓ ^ (m + 1) * ℓ * (1 / N / 2) :=
          mul_le_mul_of_nonneg_left hIabs (by positivity)
      _ = ℓ ^ (m + 1) * (ℓ / (2 * N)) := by ring
      _ ≤ (1 + ℓ) ^ (m + 1) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = (1 + ℓ) ^ (m + 1) := mul_one _
  have hcutJ : |2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * (Ja - J)| ≤
      2 * ((m : ℝ) + 3) * (1 + ℓ) ^ (m + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity), pow_succ]
    have hm3 : (0 : ℝ) ≤ 2 * ((m : ℝ) + 3) := by positivity
    calc 2 * ((m : ℝ) + 3) * (ℓ ^ (m + 1) * ℓ) * |Ja - J|
        ≤ 2 * ((m : ℝ) + 3) * (ℓ ^ (m + 1) * ℓ) * (1 / Real.sqrt N / 2) :=
          mul_le_mul_of_nonneg_left hJabs (by positivity)
      _ = 2 * ((m : ℝ) + 3) * (ℓ ^ (m + 1) * (ℓ / (2 * Real.sqrt N))) := by ring
      _ ≤ 2 * ((m : ℝ) + 3) * ((1 + ℓ) ^ (m + 1) * 1) := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = 2 * ((m : ℝ) + 3) * (1 + ℓ) ^ (m + 1) := by ring
  -- the `A`-part
  have hA3 : |A * J3 - A * ℓ ^ (m + 3) * R - 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J| ≤
      A * ((1 + ℓ) ^ (m + 1) * (K2 + 2 + 2 * ((m : ℝ) + 3))) := by
    rw [show A * J3 - A * ℓ ^ (m + 3) * R - 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J =
      A * ((J3 - ℓ ^ (m + 3) * (R - Ia) - 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * Ja) -
        ℓ ^ (m + 3) * Ia + 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * (Ja - J)) by ring, abs_mul,
      abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc |(J3 - ℓ ^ (m + 3) * (R - Ia) - 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * Ja) -
          ℓ ^ (m + 3) * Ia + 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * (Ja - J)|
        ≤ |J3 - ℓ ^ (m + 3) * (R - Ia) - 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * Ja| +
          |ℓ ^ (m + 3) * Ia| + |2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * (Ja - J)| := by
          have t1 := abs_sub (J3 - ℓ ^ (m + 3) * (R - Ia) - 2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * Ja)
            (ℓ ^ (m + 3) * Ia)
          have t2 := abs_add_le (J3 - ℓ ^ (m + 3) * (R - Ia) -
            2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * Ja - ℓ ^ (m + 3) * Ia)
            (2 * ((m : ℝ) + 3) * ℓ ^ (m + 2) * (Ja - J))
          linarith
      _ ≤ (1 + ℓ) ^ (m + 1) * K2 + 2 * (1 + ℓ) ^ (m + 1) + 2 * ((m : ℝ) + 3) * (1 + ℓ) ^ (m + 1) :=
          add_le_add (add_le_add hE3 hcut3) hcutJ
      _ = (1 + ℓ) ^ (m + 1) * (K2 + 2 + 2 * ((m : ℝ) + 3)) := by ring
  -- the `B`-part
  have hB2 : |B * J2 - B * ℓ ^ (m + 2) * R| ≤ |B| * ((1 + ℓ) ^ (m + 1) * (K1 + 1)) := by
    rw [show B * J2 - B * ℓ ^ (m + 2) * R = B * ((J2 - ℓ ^ (m + 2) * (R - Ia)) - ℓ ^ (m + 2) * Ia)
        by ring, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |(J2 - ℓ ^ (m + 2) * (R - Ia)) - ℓ ^ (m + 2) * Ia|
        ≤ |J2 - ℓ ^ (m + 2) * (R - Ia)| + |ℓ ^ (m + 2) * Ia| := abs_sub _ _
      _ ≤ (1 + ℓ) ^ (m + 1) * K1 + (1 + ℓ) ^ (m + 1) := add_le_add hE2 hcut2
      _ = (1 + ℓ) ^ (m + 1) * (K1 + 1) := by ring
  -- the `C`-part
  have hC1 : |C * J1| ≤ |C| * ((1 + ℓ) ^ (m + 1) * (K0 + R + 1)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have t1 : |J1| ≤ |J1 - ℓ ^ (m + 1) * (R - Ia)| + |ℓ ^ (m + 1) * (R - Ia)| := by
      have := abs_sub_abs_le_abs_sub J1 (ℓ ^ (m + 1) * (R - Ia))
      linarith
    have t2 : |ℓ ^ (m + 1) * (R - Ia)| ≤ (1 + ℓ) ^ (m + 1) * R + (1 + ℓ) ^ (m + 1) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have h3 : |R - Ia| ≤ R + |Ia| := by
        have := abs_sub R Ia
        rw [abs_of_nonneg hR0] at this
        exact this
      have h4 : ℓ ^ (m + 1) * |Ia| ≤ (1 + ℓ) ^ (m + 1) := by
        calc ℓ ^ (m + 1) * |Ia| ≤ (1 + ℓ) ^ (m + 1) * (1 / N / 2) :=
              mul_le_mul hpm hIabs (abs_nonneg _) (by positivity)
          _ ≤ (1 + ℓ) ^ (m + 1) * 1 := by
              gcongr
              rw [div_le_one (by norm_num), div_le_iff₀ hN0]; linarith
          _ = (1 + ℓ) ^ (m + 1) := mul_one _
      have h5 : ℓ ^ (m + 1) * R ≤ (1 + ℓ) ^ (m + 1) * R := mul_le_mul_of_nonneg_right hpm hR0
      calc ℓ ^ (m + 1) * |R - Ia| ≤ ℓ ^ (m + 1) * (R + |Ia|) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ℓ ^ (m + 1) * R + ℓ ^ (m + 1) * |Ia| := by ring
        _ ≤ (1 + ℓ) ^ (m + 1) * R + (1 + ℓ) ^ (m + 1) := add_le_add h5 h4
    have hK0m : (1 + ℓ) ^ m * K0 ≤ (1 + ℓ) ^ (m + 1) * K0 := mul_le_mul_of_nonneg_right hpm0' hK0'
    calc |J1| ≤ |J1 - ℓ ^ (m + 1) * (R - Ia)| + |ℓ ^ (m + 1) * (R - Ia)| := t1
      _ ≤ (1 + ℓ) ^ m * K0 + ((1 + ℓ) ^ (m + 1) * R + (1 + ℓ) ^ (m + 1)) := add_le_add hE1 t2
      _ ≤ (1 + ℓ) ^ (m + 1) * (K0 + R + 1) := by linarith
  calc |A * J3 + B * J2 + C * J1 - (A * ℓ ^ (m + 3) * R + 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J +
        B * ℓ ^ (m + 2) * R)|
      = |(A * J3 - A * ℓ ^ (m + 3) * R - 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J) +
          (B * J2 - B * ℓ ^ (m + 2) * R) + C * J1| := by ring_nf
    _ ≤ |A * J3 - A * ℓ ^ (m + 3) * R - 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J| +
          |B * J2 - B * ℓ ^ (m + 2) * R| + |C * J1| := by
        have t1 := abs_add_le (A * J3 - A * ℓ ^ (m + 3) * R -
          2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J) (B * J2 - B * ℓ ^ (m + 2) * R)
        have t2 := abs_add_le ((A * J3 - A * ℓ ^ (m + 3) * R -
          2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J) + (B * J2 - B * ℓ ^ (m + 2) * R)) (C * J1)
        linarith
    _ ≤ A * ((1 + ℓ) ^ (m + 1) * (K2 + 2 + 2 * ((m : ℝ) + 3))) +
          |B| * ((1 + ℓ) ^ (m + 1) * (K1 + 1)) + |C| * ((1 + ℓ) ^ (m + 1) * (K0 + R + 1)) :=
        add_le_add (add_le_add hA3 hB2) hC1
    _ = (1 + ℓ) ^ (m + 1) * (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) +
          |C| * (K0 + R + 1)) := by ring

/-- The error piece on `(a, ∞)`: with `Q(x) = A q^{m+3} + B q^{m+2} + C q^{m+1}`, `q = ℓ + 2 log x`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ D (1/2 + 8·3^m m!) (1+ℓ)^{m+1}/√N`. -/
theorem threeTerm_err_le (h : ThreeTermData f A B C D m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)))| ≤
      D * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hD := h.D_nonneg
  have he : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  set Dm : ℝ → ℝ := fun x => (Ioc (1 / Real.sqrt N) 1).indicator
    (fun x => D / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + Real.log N + 2 * Real.log x) ^ m / x)) x +
    (Ioi 1).indicator (fun x => D * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2)) x with hDm
  have hD1 : IntegrableOn (fun x : ℝ => D / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + Real.log N + 2 * Real.log x) ^ m / x)) (Ioc (1 / Real.sqrt N) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1)).const_mul _
  have hD2 : IntegrableOn (fun x : ℝ => D * (1 + Real.log N) ^ m * 3 ^ m * m.factorial *
      Real.exp 2 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2)) (Ioi 1) :=
    integrableOn_exp_neg_half_Ioi_one.const_mul _
  have hD1' := (hD1.integrable_indicator measurableSet_Ioc).integrableOn
    (s := Ioi (1 / Real.sqrt N))
  have hD2' := (hD2.integrable_indicator measurableSet_Ioi).integrableOn
    (s := Ioi (1 / Real.sqrt N))
  have hDint : IntegrableOn Dm (Ioi (1 / Real.sqrt N)) := by
    rw [hDm]
    exact hD1'.add hD2'
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 / Real.sqrt N)))
    (f := fun x => gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) hDint ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [hDm, integral_add hD1' hD2',
      setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
        inter_eq_right.2 fun x hx => hx.1,
      show Ioi (1 / Real.sqrt N) ∩ Ioi (1 : ℝ) = Ioi 1 from
        inter_eq_right.2 fun x hx => lt_of_le_of_lt ha1 hx,
      integral_const_mul, integral_const_mul, integral_pow_log_div _ _ ha0 ha1,
      integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)]
    have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
      rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
    rw [hloga, show 1 + Real.log N + 2 * -(Real.log N / 2) = 1 by ring, one_pow]
    have hp1 : 1 ≤ (1 + Real.log N) ^ (m + 1) := one_le_pow₀ (by linarith)
    have hpm : (1 + Real.log N) ^ m ≤ (1 + Real.log N) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have hm1 : (1 : ℝ) ≤ 2 * (m + 1) := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have t1 : D / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) ≤
        D * (1 / 2) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
      rw [show D / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) =
        D * (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) / Real.sqrt (2 * Real.pi)) /
          Real.sqrt N by ring]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      rw [mul_assoc D (1 / 2) ((1 + Real.log N) ^ (m + 1))]
      refine mul_le_mul_of_nonneg_left ?_ hD
      rw [div_le_iff₀ hs]
      have : ((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) ≤ (1 + Real.log N) ^ (m + 1) / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    have t2 : D * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
        (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (2 * Real.exp (-1 / 2)) ≤
        D * (8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
      rw [show D * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
        (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (2 * Real.exp (-1 / 2)) =
        D * ((1 + Real.log N) ^ m * (3 ^ m * m.factorial) *
          (2 * Real.exp 2 * Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi))) / Real.sqrt N by
        field_simp]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      rw [mul_assoc D (8 * 3 ^ m * m.factorial) ((1 + Real.log N) ^ (m + 1))]
      refine mul_le_mul_of_nonneg_left ?_ hD
      have hq : 2 * Real.exp 2 * Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi) ≤ 8 := by
        rw [div_le_iff₀ hs]
        nlinarith [Real.exp_pos 2, Real.exp_pos (-1 / 2), mul_le_mul_of_nonneg_left he2
            (Real.exp_pos 2).le]
      have h0 : 0 ≤ (1 + Real.log N) ^ m * (3 ^ m * m.factorial : ℝ) := by positivity
      calc (1 + Real.log N) ^ m * (3 ^ m * m.factorial) *
            (2 * Real.exp 2 * Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi))
          ≤ (1 + Real.log N) ^ m * (3 ^ m * m.factorial) * 8 := mul_le_mul_of_nonneg_left hq h0
        _ ≤ (1 + Real.log N) ^ (m + 1) * (3 ^ m * m.factorial) * 8 := by gcongr
        _ = 8 * 3 ^ m * m.factorial * (1 + Real.log N) ^ (m + 1) := by ring
    calc _ ≤ D * (1 / 2) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N +
          D * (8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := add_le_add t1
              t2
      _ = D * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
          ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := lt_trans ha0 hx
    have ht := one_le_mul_sq_of_le (x := x) hN hx.le
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := h.bound (N * x ^ 2) ht
    rw [hlog, hsqrt] at hbd
    have hg0 := gaussDensity_nonneg x
    have hg1 : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := gaussDensity_le x
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hg0, hDm]
    simp only
    by_cases hx1 : x ≤ 1
    · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, hx1⟩
      have hm' : x ∉ Ioi (1 : ℝ) := fun h => absurd h (not_lt.2 hx1)
      rw [indicator_of_mem hm, indicator_of_notMem hm', add_zero]
      calc gaussDensity x * |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
            B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
            C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)|
          ≤ 1 / Real.sqrt (2 * Real.pi) *
            (D * (1 + (Real.log N + 2 * Real.log x)) ^ m / (Real.sqrt N * x)) :=
            mul_le_mul hg1 hbd (abs_nonneg _) (by positivity)
        _ = D / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            ((1 + Real.log N + 2 * Real.log x) ^ m / x) := by
            rw [show 1 + (Real.log N + 2 * Real.log x) = 1 + Real.log N + 2 * Real.log x by ring]
            field_simp
    · have hx1' := not_le.1 hx1
      have hm : x ∉ Ioc (1 / Real.sqrt N) 1 := fun h => absurd h.2 (not_le.2 hx1')
      have hm' : x ∈ Ioi (1 : ℝ) := hx1'
      rw [indicator_of_notMem hm, indicator_of_mem hm', zero_add]
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1'.le
      have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
      have h3 : 1 + (Real.log N + 2 * Real.log x) ≤ (1 + Real.log N) * (3 * x) := by nlinarith
      have h4 : (1 + (Real.log N + 2 * Real.log x)) ^ m ≤ (1 + Real.log N) ^ m * 3 ^ m * x ^ m := by
        calc (1 + (Real.log N + 2 * Real.log x)) ^ m ≤ ((1 + Real.log N) * (3 * x)) ^ m :=
              pow_le_pow_left₀ (by linarith) h3 _
          _ = (1 + Real.log N) ^ m * 3 ^ m * x ^ m := by rw [mul_pow, mul_pow]; ring
      have hxm := pow_mul_exp_neg_half_sq_le m hx0.le
      have hx1le : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx1'.le
      unfold gaussDensity
      calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
            |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
              B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
              C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)|
          ≤ Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
            (D * ((1 + Real.log N) ^ m * 3 ^ m * x ^ m) / (Real.sqrt N * x)) := by
            refine mul_le_mul_of_nonneg_left (hbd.trans ?_) (by positivity)
            gcongr
        _ = D * (1 + Real.log N) ^ m * 3 ^ m / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            (x ^ m * Real.exp (-x ^ 2 / 2)) * (1 / x) := by
            field_simp
        _ ≤ D * (1 + Real.log N) ^ m * 3 ^ m / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            ((m.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)) * 1 := by
            gcongr
        _ = D * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
            (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2) := by ring

set_option maxHeartbeats 1600000 in
-- The three-term assembly (six integrals, three coefficients) exceeds the default heartbeat
-- budget in the final `field_simp`/`nlinarith`; the same shape as `twoTermStep_bound`.
/-- ★★ **The three-term propagation step**: for three-term data `(A, B, C, D, m)` of `f`, the
Gaussian step `F(N) = ∫ g(x) f(N x²) dx` has the three-term data
`A' = A/((m+4)√(2π))`, `B' = (B/(m+3) + 2 A R₀)/√(2π)`, `C' = (C/(m+2) + 2 B R₀ + 4(m+3) A J)/√(2π)`
with an error constant depending on `A, B, C, D, m` only. -/
theorem threeTermStep_bound (h : ThreeTermData f A B C D m) : ∃ D' : ℝ, 0 ≤ D' ∧ ∀ N : ℝ, 1 ≤ N →
    Integrable (fun x => gaussDensity x * f (N * x ^ 2)) →
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      (A / ((m + 4) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 4) +
        (B / (m + 3) + 2 * A * gaussR₀) / Real.sqrt (2 * Real.pi) * (Real.log N) ^ (m + 3) +
        (C / (m + 2) + 2 * B * gaussR₀ + 4 * (m + 3) * A * gaussJlog) / Real.sqrt (2 * Real.pi) *
          (Real.log N) ^ (m + 2)) / Real.sqrt N| ≤
      D' * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hA := h.A_nonneg
  have hD := h.D_nonneg
  have hR0 : 0 ≤ gaussR₀ := by
    unfold gaussR₀
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have hK2 := threeTermK_nonneg (m + 1)
  have hK1 := twoTermK_nonneg (m + 1)
  have hK0 := twoTermK_nonneg m
  refine ⟨1 + (A * (threeTermK (m + 1) + 2 + 2 * (m + 3)) + |B| * (twoTermK (m + 1) + 1) +
    |C| * (twoTermK m + gaussR₀ + 1)) + 2 * (D * (1 / 2 + 8 * 3 ^ m * m.factorial)),
    by positivity, fun N hN hint => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have heven : ∫ x, gaussDensity x * f (N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => gaussDensity x * f (N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [gaussDensity, sq_abs]
  have hsplit : ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2)) +
        ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
        hint.integrableOn]
  set Q : ℝ → ℝ := fun x => A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
    B * (Real.log N + 2 * Real.log x) ^ (m + 2) + C * (Real.log N + 2 * Real.log x) ^ (m + 1)
    with hQ
  have hQint1 : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)))
      (Ioc (1 / Real.sqrt N) 1) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 3) / x)
            +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 2) / x)
            +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 1) / x)
            := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    have h3 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) (m + 3) ha0 ha1)).const_mul
      (A / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h2 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) (m + 2) ha0 ha1)).const_mul
      (B / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h1 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) (m + 1) ha0 ha1)).const_mul
      (C / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h32 : IntegrableOn (fun x : ℝ =>
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 3) / x)
          +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 2) / x))
        (Ioc (1 / Real.sqrt N) 1) := h3.add h2
    exact h32.add h1
  have hQind : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator
      (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))))
      (Ioi (1 / Real.sqrt N)) :=
    (hQint1.integrable_indicator measurableSet_Ioc).integrableOn
  have hQh : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * Q x / (Real.sqrt N * x))) (Ioi (1 / Real.sqrt N)) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (gaussH x * Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x) := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    have h3 := (integrableOn_gaussH_pow (m + 3) (Real.log N) ha0 ha1).const_mul
      (A / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h2 := (integrableOn_gaussH_pow (m + 2) (Real.log N) ha0 ha1).const_mul
      (B / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h1 := (integrableOn_gaussH_pow (m + 1) (Real.log N) ha0 ha1).const_mul
      (C / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h32 : IntegrableOn (fun x : ℝ =>
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 3) / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x)) (Ioi (1 / Real.sqrt N)) :=
      h3.add h2
    exact h32.add h1
  have hgQ : ∀ x ∈ Ioi (1 / Real.sqrt N), gaussDensity x * (Q x / (Real.sqrt N * x)) =
      (Ioc (1 / Real.sqrt N) 1).indicator
        (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))) x +
      1 / Real.sqrt (2 * Real.pi) * (gaussH x * Q x / (Real.sqrt N * x)) := by
    intro x hx
    rw [gaussDensity_eq_indicator_add]
    by_cases h1 : x ≤ 1
    · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, h1⟩
      have hm' : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_trans ha0 hx, h1⟩
      rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply]
      ring
    · have h1' := not_le.1 h1
      rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1')),
        indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1'))]
      ring
  have hgQint : IntegrableOn (fun x : ℝ => gaussDensity x * (Q x / (Real.sqrt N * x)))
      (Ioi (1 / Real.sqrt N)) :=
    (hQind.add hQh).congr_fun (fun x hx => (hgQ x hx).symm) measurableSet_Ioi
  have hmid : ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2) =
      (∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))) +
      (∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
        (gaussH x * Q x / (Real.sqrt N * x))) +
      ∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) -
        gaussDensity x * (Q x / (Real.sqrt N * x))) := by
    rw [integral_sub hint.integrableOn hgQint, setIntegral_congr_fun measurableSet_Ioi hgQ,
      integral_add hQind hQh, setIntegral_indicator measurableSet_Ioc,
      show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
        inter_eq_right.2 fun x hx => hx.1]
    ring
  have hP1 := threeTerm_flat_main A B C m hN
  have hP2 := threeTerm_h_main A B C m hN hA
  have hE := threeTerm_err_le h hN
  have h0 := threeTerm_inner_le h hN0.le ha0.le
  simp only [hQ] at hmid hP1 hP2 hE
  rw [heven, hsplit, hmid, hP1]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2) with hI₀
  set P2 := ∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
    (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
      B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
      C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) with hP2def
  set E := ∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
    ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
      B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
      C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) with hEdef
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set X := (1 + ℓ) ^ (m + 1) / Real.sqrt N with hX
  have hX1 : 1 / Real.sqrt N ≤ X := by
    rw [hX]; exact div_le_div_of_nonneg_right (one_le_pow₀ (by linarith)) hsN.le
  have hX0 : 0 ≤ X := by positivity
  set K2 := threeTermK (m + 1) with hK2def
  set K1 := twoTermK (m + 1) with hK1def
  set K0 := twoTermK m with hK0def
  set R := gaussR₀ with hRdef
  set J := gaussJlog with hJdef
  clear_value K2 K1 K0 R J
  clear hK2def hK1def hK0def hRdef hJdef hℓdef
  have h0' : |I₀| ≤ 1 / 2 * X := by
    calc |I₀| ≤ 1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N) := h0
      _ ≤ 1 / 2 * (1 / Real.sqrt N) := by gcongr
      _ ≤ 1 / 2 * X := by linarith
  have h2' : |P2 - 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      (A * ℓ ^ (m + 3) * R + 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J + B * ℓ ^ (m + 2) * R)| ≤
      1 / 2 * (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) + |C| * (K0 + R + 1)) * X := by
    refine hP2.trans ?_
    rw [hX, show 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + ℓ) ^ (m + 1) * (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) +
        |C| * (K0 + R + 1))) =
      1 / Real.sqrt (2 * Real.pi) * (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) +
        |C| * (K0 + R + 1)) * ((1 + ℓ) ^ (m + 1) / Real.sqrt N) by field_simp]
    have hb0 : 0 ≤ A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) + |C| * (K0 + R + 1) := by
      positivity
    gcongr
  have hE' : |E| ≤ D * (1 / 2 + 8 * 3 ^ m * m.factorial) * X := by
    refine hE.trans (le_of_eq ?_)
    rw [hX]; ring
  clear h0 hP2 hE hP1 hint h hQ
  have hkey : 2 * (I₀ + (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      (A * ℓ ^ (m + 4) / (2 * (m + 4)) + B * ℓ ^ (m + 3) / (2 * (m + 3)) +
        C * ℓ ^ (m + 2) / (2 * (m + 2))) + P2 + E)) -
      (A / ((m + 4) * Real.sqrt (2 * Real.pi)) * ℓ ^ (m + 4) +
        (B / (m + 3) + 2 * A * R) / Real.sqrt (2 * Real.pi) * ℓ ^ (m + 3) +
        (C / (m + 2) + 2 * B * R + 4 * (m + 3) * A * J) / Real.sqrt (2 * Real.pi) * ℓ ^ (m + 2)) /
          Real.sqrt N =
      2 * I₀ + 2 * (P2 - 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * ℓ ^ (m + 3) * R + 2 * ((m : ℝ) + 3) * A * ℓ ^ (m + 2) * J + B * ℓ ^ (m + 2) * R)) +
        2 * E := by
    have hm4 : (0 : ℝ) < m + 4 := by positivity
    have hm3 : (0 : ℝ) < m + 3 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    field_simp
    ring
  rw [hkey, show (1 + (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) + |C| * (K0 + R + 1)) +
    2 * (D * (1 / 2 + 8 * 3 ^ m * m.factorial))) * (1 + ℓ) ^ (m + 1) / Real.sqrt N =
    (1 + (A * (K2 + 2 + 2 * ((m : ℝ) + 3)) + |B| * (K1 + 1) + |C| * (K0 + R + 1)) +
      2 * (D * (1 / 2 + 8 * 3 ^ m * m.factorial))) * X by
    rw [hX]; ring]
  rw [abs_le] at h0' h2' hE' ⊢
  constructor <;> nlinarith [h0'.1, h0'.2, h2'.1, h2'.2, hE'.1, hE'.2]

end Grammar
