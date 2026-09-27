/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthAllLeading
import Grammar.GaussianDepthThreeTwoTerm

/-!
# The Gaussian-prior deep linear network at every depth: the second coefficient

The two-term propagation step: if
`f(t) = (A (log t)^{m+2} + B (log t)^{m+1})/√t + O((1+log t)^m/√t)` for `t ≥ 1` with `0 ≤ f ≤ 1`
(`TwoTermData f A B C m`), then `F(N) = ∫ g(x) f(Nx²) dx` has

  `A' = A/((m+3)√(2π))`,  `B' = (B/(m+2) + 2A R₀)/√(2π)`,  `R₀ = (log 2 − γ)/2`,

with error `O((1+log N)^{m+1}/√N)` (★★ `twoTermStep_bound`): the Gaussian is kept on the whole
outer region through `h = e^{−x²/2} − 1_{(0,1]}` (`Grammar.GaussianDepthThreeTwoTerm`), and the
moments `∫₀^∞ |h(x)| |log x|^j/x dx` are finite (`gaussH_log_pow_moment_le`), so the binomial
expansion of `(log N + 2 log x)^n` against `h/x` keeps only `(log N)^n R₀` at the top order
(`integral_gaussH_pow_expand`).  By induction from the depth-three case
(`Grammar.GaussianDepthThreeTwoTerm`)

  `Z_L(N) = [A_L (log N)^{L−1} + B_L (log N)^{L−2}]/√N + O((1+log N)^{L−3}/√N)`,
  `A_L = 1/((L−1)! √(2π)^{L−1})`,  `B_L = ((L+1) log 2 − (L−1)γ)/((L−2)! √(2π)^{L−1})`

for every `L ≥ 3` (★★★ `gaussLaplaceL_two_term_bound`): the subleading coefficient of the note's
polynomials `P_{L−1}` at every depth (Astra round-9 target 2).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Moments of `h` against powers of the logarithm -/

/-- `x |log x|^j ≤ (j+1)^j` on `(0, 1]`. -/
theorem mul_abs_log_pow_le {x : ℝ} (j : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    x * |Real.log x| ^ j ≤ (j + 1) ^ j := by
  have hx0 : 0 < x := hx.1
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [pow_zero, mul_one, Nat.cast_zero, zero_add]
    exact hx.2
  · have hδ : (0 : ℝ) < 1 / j := by positivity
    have hlog := abs_log_le_rpow_div hδ hx
    rw [div_div_eq_mul_div, div_one] at hlog
    have h1 : |Real.log x| ^ j ≤ ((j : ℝ) * x ^ (-(1 / (j : ℝ)))) ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
    have h3 : (x ^ (-(1 / (j : ℝ)))) ^ j = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
        show (-(1 / (j : ℝ)) * (j : ℝ)) = -1 by field_simp, Real.rpow_neg_one]
    rw [mul_pow, h3] at h1
    calc x * |Real.log x| ^ j ≤ x * ((j : ℝ) ^ j * x⁻¹) := mul_le_mul_of_nonneg_left h1 hx0.le
      _ = (j : ℝ) ^ j := by field_simp
      _ ≤ (j + 1) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j

/-- On `(0, 1]`: `|h(x)| |log x|^j / x ≤ (j+1)^j / 2`. -/
theorem gaussH_log_pow_inner {x : ℝ} (j : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    |gaussH x| * |Real.log x| ^ j / x ≤ (j + 1) ^ j / 2 := by
  have hx0 : 0 < x := hx.1
  obtain ⟨h1, h2⟩ := gaussH_inner hx
  have hh : |gaussH x| ≤ x ^ 2 / 2 := by rw [abs_of_nonpos h2]; linarith
  rw [div_le_iff₀ hx0]
  calc |gaussH x| * |Real.log x| ^ j ≤ x ^ 2 / 2 * |Real.log x| ^ j :=
        mul_le_mul_of_nonneg_right hh (by positivity)
    _ = x / 2 * (x * |Real.log x| ^ j) := by ring
    _ ≤ x / 2 * (j + 1) ^ j := mul_le_mul_of_nonneg_left (mul_abs_log_pow_le j hx) (by positivity)
    _ = (j + 1) ^ j / 2 * x := by ring

/-- On `(1, ∞)`: `|h(x)| |log x|^j / x ≤ j! e² e^{−x/2}`. -/
theorem gaussH_log_pow_outer {x : ℝ} (j : ℕ) (hx : 1 < x) :
    |gaussH x| * |Real.log x| ^ j / x ≤ (j.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h1, h2⟩ := gaussH_outer hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hpow : |Real.log x| ^ j ≤ x ^ j := by
    rw [abs_of_nonneg hlog0]; exact pow_le_pow_left₀ hlog0 hlx j
  have hh : |gaussH x| = Real.exp (-x ^ 2 / 2) := by
    rw [abs_of_nonneg h1]; unfold gaussH
    rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hx)), sub_zero]
  rw [hh]
  calc Real.exp (-x ^ 2 / 2) * |Real.log x| ^ j / x ≤ Real.exp (-x ^ 2 / 2) * x ^ j / 1 := by
        gcongr
    _ = x ^ j * Real.exp (-x ^ 2 / 2) := by ring
    _ ≤ (j.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2) := pow_mul_exp_neg_half_sq_le j hx0.le

theorem measurable_gaussH_log_pow (j : ℕ) :
    Measurable fun x : ℝ => gaussH x * (Real.log x) ^ j / x :=
  (measurable_gaussH.mul (Real.measurable_log.pow_const j)).div measurable_id

theorem integrableOn_gaussH_log_pow_Ioc (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioc a 1) := by
  refine Measure.integrableOn_of_bounded (M := (j + 1) ^ j / 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_gaussH_log_pow j).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun x hx => ?_
  have hx0 : 0 < x := lt_of_le_of_lt ha0 hx.1
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hx0]
  exact gaussH_log_pow_inner j ⟨hx0, hx.2⟩

theorem integrableOn_gaussH_log_pow_Ioi_one (j : ℕ) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioi 1) := by
  refine ((integrableOn_exp_neg_half_Ioi_one.const_mul ((j.factorial : ℝ) * Real.exp 2)).mono'
    (measurable_gaussH_log_pow j).aestronglyMeasurable.restrict ?_)
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun x hx => ?_
  have hx : (1 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos (by linarith : (0 : ℝ) < x)]
  exact gaussH_log_pow_outer j hx

theorem integrableOn_gaussH_log_pow (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * (Real.log x) ^ j / x) (Ioi a) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha1]
  exact (integrableOn_gaussH_log_pow_Ioc j ha0).union (integrableOn_gaussH_log_pow_Ioi_one j)

/-- The moment constant `M_j = (j+1)^j/2 + 16 j!`. -/
noncomputable def gaussHMoment (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ j / 2 + 16 * j.factorial

theorem gaussHMoment_nonneg (j : ℕ) : 0 ≤ gaussHMoment j := by unfold gaussHMoment; positivity

/-- `|∫_a^∞ h(x) (log x)^j/x dx| ≤ M_j` for `0 ≤ a ≤ 1`. -/
theorem gaussH_log_pow_moment_le (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioi a, gaussH x * (Real.log x) ^ j / x| ≤ gaussHMoment j := by
  have hin : |∫ x in Ioc a 1, gaussH x * (Real.log x) ^ j / x| ≤ (j + 1) ^ j / 2 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a 1)
      (f := fun x => gaussH x * (Real.log x) ^ j / x) (C := (j + 1) ^ j / 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x hx => by
        have hx0 : 0 < x := lt_of_le_of_lt ha0 hx.1
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hx0]
        exact gaussH_log_pow_inner j ⟨hx0, hx.2⟩)
    have hv : volume.real (Ioc a 1) = 1 - a := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [Real.norm_eq_abs, hv] at h
    have hc : 0 ≤ ((j : ℝ) + 1) ^ j / 2 := by positivity
    nlinarith
  have hout : |∫ x in Ioi 1, gaussH x * (Real.log x) ^ j / x| ≤ 16 * j.factorial := by
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun x => gaussH x * (Real.log x) ^ j / x)
      (integrableOn_exp_neg_half_Ioi_one.const_mul ((j.factorial : ℝ) * Real.exp 2)) (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun x hx => ?_
        have hx : (1 : ℝ) < x := hx
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos (by linarith : (0 : ℝ) < x)]
        exact gaussH_log_pow_outer j hx)
    rw [Real.norm_eq_abs, integral_const_mul, integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) <
        2)]
      at h
    have he : Real.exp 2 ≤ 8 := by
      have h1 := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1]
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have hf : (0 : ℝ) ≤ j.factorial := by positivity
    refine h.trans ?_
    nlinarith [Real.exp_pos 2, Real.exp_pos (-1 / 2), mul_nonneg hf (Real.exp_pos 2).le]
  rw [← Ioc_union_Ioi_eq_Ioi ha1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (integrableOn_gaussH_log_pow_Ioc j ha0) (integrableOn_gaussH_log_pow_Ioi_one j)]
  unfold gaussHMoment
  calc |(∫ x in Ioc a 1, gaussH x * (Real.log x) ^ j / x) +
        ∫ x in Ioi 1, gaussH x * (Real.log x) ^ j / x|
      ≤ |∫ x in Ioc a 1, gaussH x * (Real.log x) ^ j / x| +
        |∫ x in Ioi 1, gaussH x * (Real.log x) ^ j / x| := abs_add_le _ _
    _ ≤ (j + 1) ^ j / 2 + 16 * j.factorial := add_le_add hin hout

/-! ### The binomial expansion against `h/x` -/

/-- `K_n = Σ_{i ≤ n} C(n+1, i) 2^{n+1−i} M_{n+1−i}`. -/
noncomputable def twoTermK (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i) * gaussHMoment (n + 1 - i)

theorem twoTermK_nonneg (n : ℕ) : 0 ≤ twoTermK n :=
  Finset.sum_nonneg fun i _ => by
    have := gaussHMoment_nonneg (n + 1 - i)
    positivity

/-- ★ **The expansion**: `|∫_a^∞ h (ℓ + 2 log x)^{n+1}/x − ℓ^{n+1} ∫_a^∞ h/x| ≤ (1+ℓ)^n K_n`
for `ℓ ≥ 0`, `0 < a ≤ 1`. -/
theorem integral_gaussH_pow_expand (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    |(∫ x in Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 1) / x) -
      ℓ ^ (n + 1) * ∫ x in Ioi a, gaussH x / x| ≤ (1 + ℓ) ^ n * twoTermK n := by
  have e : ∀ x ∈ Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 1) / x =
      ∑ i ∈ Finset.range (n + 2), (ℓ ^ i * ((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i)) *
        (gaussH x * (Real.log x) ^ (n + 1 - i) / x) := by
    intro x _
    rw [add_pow, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  have hint : ∀ i ∈ Finset.range (n + 2), IntegrableOn
      (fun x : ℝ => (ℓ ^ i * ((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i)) *
        (gaussH x * (Real.log x) ^ (n + 1 - i) / x)) (Ioi a) :=
    fun i _ => (integrableOn_gaussH_log_pow (n + 1 - i) ha0.le ha1).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_finsetSum _ hint]
  simp_rw [integral_const_mul]
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero]
  simp only [Nat.cast_one, mul_one]
  have hlast : ∫ x in Ioi a, gaussH x * (Real.log x) ^ 0 / x = ∫ x in Ioi a, gaussH x / x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp
  rw [hlast, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold twoTermK
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hM := gaussH_log_pow_moment_le (n + 1 - i) ha0.le ha1
  have hℓi : ℓ ^ i ≤ (1 + ℓ) ^ n :=
    calc ℓ ^ i ≤ (1 + ℓ) ^ i := pow_le_pow_left₀ hℓ (by linarith) i
      _ ≤ (1 + ℓ) ^ n := pow_le_pow_right₀ (by linarith) hi'
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc ℓ ^ i * ((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i) *
        |∫ x in Ioi a, gaussH x * (Real.log x) ^ (n + 1 - i) / x|
      ≤ (1 + ℓ) ^ n * ((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i) * gaussHMoment (n + 1 - i) := by
        gcongr
    _ = (1 + ℓ) ^ n * (((n + 1).choose i : ℝ) * 2 ^ (n + 1 - i) * gaussHMoment (n + 1 - i)) := by
        ring

/-! ### The two-term data and the pieces of the step -/

/-- The two-term hypotheses: `0 ≤ f ≤ 1` on `t ≥ 0` and
`|f(t) − (A (log t)^{m+2} + B (log t)^{m+1})/√t| ≤ C (1 + log t)^m/√t` for `t ≥ 1`. -/
structure TwoTermData (f : ℝ → ℝ) (A B C : ℝ) (m : ℕ) : Prop where
  A_nonneg : 0 ≤ A
  C_nonneg : 0 ≤ C
  f_nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  f_le_one : ∀ t, 0 ≤ t → f t ≤ 1
  bound : ∀ t, 1 ≤ t →
    |f t - (A * (Real.log t) ^ (m + 2) + B * (Real.log t) ^ (m + 1)) / Real.sqrt t| ≤
      C * (1 + Real.log t) ^ m / Real.sqrt t

variable {f : ℝ → ℝ} {A B C : ℝ} {m : ℕ}

/-- `R₀ = (log 2 − γ)/2`. -/
noncomputable def gaussR₀ : ℝ := (Real.log 2 - Real.eulerMascheroniConstant) / 2

/-- The inner piece for two-term data: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem twoTerm_inner_le (h : TwoTermData f A B C m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussDensity x * f (N * x ^ 2)) (C := 1 / Real.sqrt (2 * Real.pi))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      have h0 := h.f_nonneg (N * x ^ 2) (by positivity)
      have h1 := h.f_le_one (N * x ^ 2) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _) h0)]
      unfold gaussDensity
      calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * f (N * x ^ 2)
          ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right
              (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le) h1 h0 (by positivity)
        _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _)
  have hv : volume.real (Ioc (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rwa [Real.norm_eq_abs, hv] at hb

/-- `∫_a^∞ h/x = R₀ − ∫₀^a h/x` for `0 ≤ a`. -/
theorem integral_gaussH_div_Ioi {a : ℝ} (ha0 : 0 ≤ a) :
    ∫ x in Ioi a, gaussH x / x = gaussR₀ - ∫ x in Ioc (0 : ℝ) a, gaussH x / x := by
  unfold gaussR₀
  rw [← integral_gaussH_div, ← Ioc_union_Ioi_eq_Ioi ha0,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_gaussH_div.mono_set Ioc_subset_Ioi_self)
      (integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0))]
  ring

/-- `h(x)(ℓ + 2 log x)^n / x` is integrable on `(a, ∞)` for `0 < a ≤ 1`. -/
theorem integrableOn_gaussH_pow (n : ℕ) (ℓ : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * (ℓ + 2 * Real.log x) ^ n / x) (Ioi a) := by
  have e : ∀ x ∈ Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ n / x =
      ∑ i ∈ Finset.range (n + 1), (ℓ ^ i * (n.choose i : ℝ) * 2 ^ (n - i)) *
        (gaussH x * (Real.log x) ^ (n - i) / x) := by
    intro x _
    rw [add_pow, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  have hsum : IntegrableOn (fun x : ℝ => ∑ i ∈ Finset.range (n + 1),
      (ℓ ^ i * (n.choose i : ℝ) * 2 ^ (n - i)) * (gaussH x * (Real.log x) ^ (n - i) / x))
      (Ioi a) :=
    integrable_finsetSum _ fun i _ =>
      (integrableOn_gaussH_log_pow (n - i) ha0.le ha1).const_mul
        (ℓ ^ i * (n.choose i : ℝ) * 2 ^ (n - i))
  exact hsum.congr_fun (fun x hx => (e x hx).symm) measurableSet_Ioi

/-- The flat main term on `(a, 1]`:
`∫_a^1 Q(x)/(√(2π)√N x) = (A ℓ^{m+3}/(2(m+3)) + B ℓ^{m+2}/(2(m+2)))/(√(2π)√N)`. -/
theorem twoTerm_flat_main (A B : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ (m + 3) / (2 * (m + 3)) + B * (Real.log N) ^ (m + 2) / (2 * (m + 2)))
            := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((Real.log N + 2 * Real.log x) ^ (m + 1) / x) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx.1
    field_simp
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) (m + 2) ha0 ha1)
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) (m + 1) ha0 ha1)
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_add (h2.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_pow_log_div _ _ ha0 ha1,
    integral_pow_log_div _ _ ha0 ha1]
  have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
  rw [hloga, show Real.log N + 2 * -(Real.log N / 2) = 0 by ring, zero_pow (by omega),
    zero_pow (by omega), sub_zero, sub_zero]
  push_cast
  field_simp
  ring

/-- The `h`-part of the main term on `(a, ∞)`: with `I_a = ∫₀^a h/x`,
`∫_a^∞ h Q/(√(2π)√N x) = (A ℓ^{m+2} R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ (1+ℓ)^{m+1} (A (K_{m+1} + 1) + |B| (K_m + R₀ + 1))`. -/
theorem twoTerm_h_main (A B : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ (m + 2) * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((1 + Real.log N) ^ (m + 1) *
        (A * (twoTermK (m + 1) + 1) + |B| * (twoTermK m + gaussR₀ + 1))) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓN : Real.log N ≤ 2 * N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hR0 : 0 ≤ gaussR₀ := by
    unfold gaussR₀
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
          B * (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx
    field_simp
  have h2 := integrableOn_gaussH_pow (m + 2) (Real.log N) ha0 ha1
  have h1 := integrableOn_gaussH_pow (m + 1) (Real.log N) ha0 ha1
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_add (h2.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul,
    ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the two expansions and the cutoff
  have hE2 := integral_gaussH_pow_expand (m + 1) hℓ ha0 ha1
  have hE1 := integral_gaussH_pow_expand m hℓ ha0 ha1
  have hI := abs_integral_gaussH_div_Ioc_le ha0.le ha1
  have hIa2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  rw [hIa2] at hI
  rw [integral_gaussH_div_Ioi ha0.le] at hE2 hE1
  set J2 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x
    with hJ2
  set J1 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x
    with hJ1
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa
  clear_value J2 J1 Ia
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set K1 := twoTermK (m + 1) with hK1
  set K0 := twoTermK m with hK0
  have hK1' := twoTermK_nonneg (m + 1)
  have hK0' := twoTermK_nonneg m
  clear_value K1 K0
  set R := gaussR₀ with hR
  clear_value R
  have hp1 : 1 ≤ (1 + ℓ) ^ (m + 1) := one_le_pow₀ (by linarith)
  have hpm : ℓ ^ (m + 1) ≤ (1 + ℓ) ^ (m + 1) := pow_le_pow_left₀ hℓ (by linarith) _
  have hpm0 : ℓ ^ m ≤ (1 + ℓ) ^ m := pow_le_pow_left₀ hℓ (by linarith) _
  have hpm0' : (1 + ℓ) ^ m ≤ (1 + ℓ) ^ (m + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
  -- `|ℓ^{m+2} I_a| ≤ (1+ℓ)^{m+1}`: `ℓ^{m+2}/(2N) = ℓ^{m+1} · ℓ/(2N) ≤ (1+ℓ)^{m+1}`
  have hIabs : |Ia| ≤ 1 / N / 2 := hI
  have hcut2 : |ℓ ^ (m + 2) * Ia| ≤ (1 + ℓ) ^ (m + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity), pow_succ]
    calc ℓ ^ (m + 1) * ℓ * |Ia| ≤ ℓ ^ (m + 1) * ℓ * (1 / N / 2) :=
          mul_le_mul_of_nonneg_left hIabs (by positivity)
      _ = ℓ ^ (m + 1) * (ℓ / (2 * N)) := by ring
      _ ≤ (1 + ℓ) ^ (m + 1) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = (1 + ℓ) ^ (m + 1) := mul_one _
  have hcut1 : |ℓ ^ (m + 1) * Ia| ≤ (1 + ℓ) ^ (m + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc ℓ ^ (m + 1) * |Ia| ≤ (1 + ℓ) ^ (m + 1) * (1 / N / 2) :=
          mul_le_mul hpm hIabs (abs_nonneg _) (by positivity)
      _ ≤ (1 + ℓ) ^ (m + 1) * 1 := by
          gcongr
          rw [div_le_one (by norm_num)]
          rw [div_le_iff₀ hN0]; linarith
      _ = (1 + ℓ) ^ (m + 1) := mul_one _
  -- assemble
  have hA2 : |A * J2 - A * ℓ ^ (m + 2) * R| ≤ A * ((1 + ℓ) ^ (m + 1) * (K1 + 1)) := by
    rw [show A * J2 - A * ℓ ^ (m + 2) * R = A * ((J2 - ℓ ^ (m + 2) * (R - Ia)) - ℓ ^ (m + 2) * Ia)
        by
      ring, abs_mul, abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc |(J2 - ℓ ^ (m + 2) * (R - Ia)) - ℓ ^ (m + 2) * Ia|
        ≤ |J2 - ℓ ^ (m + 2) * (R - Ia)| + |ℓ ^ (m + 2) * Ia| := abs_sub _ _
      _ ≤ (1 + ℓ) ^ (m + 1) * K1 + (1 + ℓ) ^ (m + 1) := add_le_add hE2 hcut2
      _ = (1 + ℓ) ^ (m + 1) * (K1 + 1) := by ring
  have hB1 : |B * J1| ≤ |B| * ((1 + ℓ) ^ (m + 1) * (K0 + R + 1)) := by
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
        have := hcut1
        rwa [abs_mul, abs_of_nonneg (by positivity)] at this
      have h5 : ℓ ^ (m + 1) * R ≤ (1 + ℓ) ^ (m + 1) * R := mul_le_mul_of_nonneg_right hpm hR0
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ℓ ^ (m + 1))]
    calc |J1| ≤ |J1 - ℓ ^ (m + 1) * (R - Ia)| + |ℓ ^ (m + 1) * (R - Ia)| := t1
      _ ≤ (1 + ℓ) ^ m * K0 + ((1 + ℓ) ^ (m + 1) * R + (1 + ℓ) ^ (m + 1)) := add_le_add hE1 t2
      _ ≤ (1 + ℓ) ^ (m + 1) * (K0 + R + 1) := by nlinarith
  calc |A * J2 + B * J1 - A * ℓ ^ (m + 2) * R|
      = |(A * J2 - A * ℓ ^ (m + 2) * R) + B * J1| := by ring_nf
    _ ≤ |A * J2 - A * ℓ ^ (m + 2) * R| + |B * J1| := abs_add_le _ _
    _ ≤ A * ((1 + ℓ) ^ (m + 1) * (K1 + 1)) + |B| * ((1 + ℓ) ^ (m + 1) * (K0 + R + 1)) :=
        add_le_add hA2 hB1
    _ = (1 + ℓ) ^ (m + 1) * (A * (K1 + 1) + |B| * (K0 + R + 1)) := by ring

/-- The error piece on `(a, ∞)`: with `Q(x) = A(ℓ+2log x)^{m+2} + B(ℓ+2log x)^{m+1}`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ C (1/2 + 8·3^m m!) (1+ℓ)^{m+1}/√N`. -/
theorem twoTerm_err_le (h : TwoTermData f A B C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)))| ≤
      C * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hC := h.C_nonneg
  have he : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  -- the pointwise bound `|g e| ≤ D`
  set D : ℝ → ℝ := fun x => (Ioc (1 / Real.sqrt N) 1).indicator
    (fun x => C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + Real.log N + 2 * Real.log x) ^ m / x)) x +
    (Ioi 1).indicator (fun x => C * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2)) x with hD
  have hD1 : IntegrableOn (fun x : ℝ => C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + Real.log N + 2 * Real.log x) ^ m / x)) (Ioc (1 / Real.sqrt N) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1)).const_mul _
  have hD2 : IntegrableOn (fun x : ℝ => C * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2
      /
      (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2)) (Ioi 1) :=
    integrableOn_exp_neg_half_Ioi_one.const_mul _
  have hD1' := (hD1.integrable_indicator measurableSet_Ioc).integrableOn (s := Ioi (1 / Real.sqrt
      N))
  have hD2' := (hD2.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi (1 / Real.sqrt
      N))
  have hDint : IntegrableOn D (Ioi (1 / Real.sqrt N)) := by
    rw [hD]
    exact hD1'.add hD2'
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 / Real.sqrt N)))
    (f := fun x => gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) hDint ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [hD, integral_add hD1' hD2',
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
    -- first piece `≤ C (1+ℓ)^{m+1}/(2√N)`, second piece `≤ 8 C 3^m m! (1+ℓ)^{m+1}/√N`
    have t1 : C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) ≤
        C * (1 / 2) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
      rw [show C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) =
        C * (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) / Real.sqrt (2 * Real.pi)) /
          Real.sqrt N by ring]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      rw [mul_assoc C (1 / 2) ((1 + Real.log N) ^ (m + 1))]
      refine mul_le_mul_of_nonneg_left ?_ hC
      rw [div_le_iff₀ hs]
      have : ((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) ≤ (1 + Real.log N) ^ (m + 1) / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    have t2 : C * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
        (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (2 * Real.exp (-1 / 2)) ≤
        C * (8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
      rw [show C * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
        (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (2 * Real.exp (-1 / 2)) =
        C * ((1 + Real.log N) ^ m * (3 ^ m * m.factorial) *
          (2 * Real.exp 2 * Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi))) / Real.sqrt N by
        field_simp]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      rw [mul_assoc C (8 * 3 ^ m * m.factorial) ((1 + Real.log N) ^ (m + 1))]
      refine mul_le_mul_of_nonneg_left ?_ hC
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
    calc _ ≤ C * (1 / 2) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N +
          C * (8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := add_le_add t1
              t2
      _ = C * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
          ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := lt_trans ha0 hx
    have ht := one_le_mul_sq_of_le (x := x) hN hx.le
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := h.bound (N * x ^ 2) ht
    rw [hlog, hsqrt] at hbd
    have hg0 := gaussDensity_nonneg x
    have hg1 : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
      unfold gaussDensity
      exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hg0, hD]
    simp only
    by_cases hx1 : x ≤ 1
    · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, hx1⟩
      have hm' : x ∉ Ioi (1 : ℝ) := fun h => absurd h (not_lt.2 hx1)
      rw [indicator_of_mem hm, indicator_of_notMem hm', add_zero]
      calc gaussDensity x * |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
            B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)|
          ≤ 1 / Real.sqrt (2 * Real.pi) *
            (C * (1 + (Real.log N + 2 * Real.log x)) ^ m / (Real.sqrt N * x)) :=
            mul_le_mul hg1 hbd (abs_nonneg _) (by positivity)
        _ = C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
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
            |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
              B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)|
          ≤ Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
            (C * ((1 + Real.log N) ^ m * 3 ^ m * x ^ m) / (Real.sqrt N * x)) := by
            refine mul_le_mul_of_nonneg_left (hbd.trans ?_) (by positivity)
            gcongr
        _ = C * (1 + Real.log N) ^ m * 3 ^ m / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            (x ^ m * Real.exp (-x ^ 2 / 2)) * (1 / x) := by
            field_simp
        _ ≤ C * (1 + Real.log N) ^ m * 3 ^ m / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            ((m.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)) * 1 := by
            gcongr
        _ = C * (1 + Real.log N) ^ m * 3 ^ m * m.factorial * Real.exp 2 /
            (Real.sqrt (2 * Real.pi) * Real.sqrt N) * Real.exp (-x / 2) := by ring

/-- `g(x) = (1_{(0,1]}(x) + h(x))/√(2π)`. -/
theorem gaussDensity_eq_indicator_add (x : ℝ) :
    gaussDensity x = ((Ioc 0 1).indicator 1 x + gaussH x) / Real.sqrt (2 * Real.pi) := by
  unfold gaussDensity gaussH; ring

/-- ★★ **The two-term propagation step**: for two-term data `(A, B, C, m)` of `f`, the Gaussian step
`F(N) = ∫ g(x) f(N x²) dx` has the two-term data
`A' = A/((m+3)√(2π))`, `B' = (B/(m+2) + 2 A R₀)/√(2π)` with an error constant depending on
`A, B, C, m` only. -/
theorem twoTermStep_bound (h : TwoTermData f A B C m) : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℝ, 1 ≤ N →
    Integrable (fun x => gaussDensity x * f (N * x ^ 2)) →
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      (A / ((m + 3) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 3) +
        (B / (m + 2) + 2 * A * gaussR₀) / Real.sqrt (2 * Real.pi) * (Real.log N) ^ (m + 2)) /
          Real.sqrt N| ≤ C' * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  have hR0 : 0 ≤ gaussR₀ := by
    unfold gaussR₀
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have hK1 := twoTermK_nonneg (m + 1)
  have hK0 := twoTermK_nonneg m
  refine ⟨1 + (A * (twoTermK (m + 1) + 1) + |B| * (twoTermK m + gaussR₀ + 1)) +
    2 * (C * (1 / 2 + 8 * 3 ^ m * m.factorial)), by positivity, fun N hN hint => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  -- evenness and the split
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
  -- the main-term integrand `g Q/(√N x)` and its two pieces on `(a, ∞)`
  set Q : ℝ → ℝ := fun x => A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
    B * (Real.log N + 2 * Real.log x) ^ (m + 1) with hQ
  have hQint1 : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)))
      (Ioc (1 / Real.sqrt N) 1) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 2) / x)
            +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 1) / x)
            := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) (m + 2) ha0 ha1)).const_mul _).add
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
        (intervalIntegrable_pow_log_div (Real.log N) (m + 1) ha0 ha1)).const_mul _)
  have hQind : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator
      (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))))
      (Ioi (1 / Real.sqrt N)) :=
    (hQint1.integrable_indicator measurableSet_Ioc).integrableOn
  have hQh : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * Q x / (Real.sqrt N * x))) (Ioi (1 / Real.sqrt N)) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (gaussH x * Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 2) / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ (m + 1) / x) := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    exact ((integrableOn_gaussH_pow (m + 2) (Real.log N) ha0 ha1).const_mul _).add
      ((integrableOn_gaussH_pow (m + 1) (Real.log N) ha0 ha1).const_mul _)
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
  have hP1 := twoTerm_flat_main A B m hN
  have hP2 := twoTerm_h_main A B m hN hA
  have hE := twoTerm_err_le h hN
  have h0 := twoTerm_inner_le h hN0.le ha0.le
  simp only [hQ] at hmid hP1 hP2 hE
  rw [heven, hsplit, hmid, hP1]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2) with hI₀
  set P2 := ∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
    (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
      B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) with hP2def
  set E := ∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
    ((A * (Real.log N + 2 * Real.log x) ^ (m + 2) +
      B * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) with hEdef
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set X := (1 + ℓ) ^ (m + 1) / Real.sqrt N with hX
  have hX1 : 1 / Real.sqrt N ≤ X := by
    rw [hX]; exact div_le_div_of_nonneg_right (one_le_pow₀ (by linarith)) hsN.le
  have hX0 : 0 ≤ X := by positivity
  set K1 := twoTermK (m + 1) with hK1def
  set K0 := twoTermK m with hK0def
  set R := gaussR₀ with hRdef
  clear_value K1 K0 R
  -- the pieces against `X`
  have h0' : |I₀| ≤ 1 / 2 * X := by
    calc |I₀| ≤ 1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N) := h0
      _ ≤ 1 / 2 * (1 / Real.sqrt N) := by gcongr
      _ ≤ 1 / 2 * X := by linarith
  have h2' : |P2 - 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * ℓ ^ (m + 2) * R)| ≤
      1 / 2 * (A * (K1 + 1) + |B| * (K0 + R + 1)) * X := by
    refine hP2.trans ?_
    rw [hX, show 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      ((1 + ℓ) ^ (m + 1) * (A * (K1 + 1) + |B| * (K0 + R + 1))) =
      1 / Real.sqrt (2 * Real.pi) * (A * (K1 + 1) + |B| * (K0 + R + 1)) *
        ((1 + ℓ) ^ (m + 1) / Real.sqrt N) by field_simp]
    have hb0 : 0 ≤ A * (K1 + 1) + |B| * (K0 + R + 1) := by positivity
    gcongr
  have hE' : |E| ≤ C * (1 / 2 + 8 * 3 ^ m * m.factorial) * X := by
    refine hE.trans (le_of_eq ?_)
    rw [hX]; ring
  have hkey : 2 * (I₀ + (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
      (A * ℓ ^ (m + 3) / (2 * (m + 3)) + B * ℓ ^ (m + 2) / (2 * (m + 2))) + P2 + E)) -
      (A / ((m + 3) * Real.sqrt (2 * Real.pi)) * ℓ ^ (m + 3) +
        (B / (m + 2) + 2 * A * R) / Real.sqrt (2 * Real.pi) * ℓ ^ (m + 2)) / Real.sqrt N =
      2 * I₀ + 2 * (P2 - 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * ℓ ^ (m + 2) * R)) +
        2 * E := by
    have hm3 : (0 : ℝ) < m + 3 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    field_simp
    ring
  rw [hkey, show (1 + (A * (K1 + 1) + |B| * (K0 + R + 1)) +
    2 * (C * (1 / 2 + 8 * 3 ^ m * m.factorial))) * (1 + ℓ) ^ (m + 1) / Real.sqrt N =
    (1 + (A * (K1 + 1) + |B| * (K0 + R + 1)) + 2 * (C * (1 / 2 + 8 * 3 ^ m * m.factorial))) * X by
    rw [hX]; ring]
  rw [abs_le] at h0' h2' hE' ⊢
  constructor <;> nlinarith [h0'.1, h0'.2, h2'.1, h2'.2, hE'.1, hE'.2]

/-! ### The induction from depth three -/

/-- The depth-three base: two-term data of `Z_3` with `A = 1/(4π)`, `B = (2 log 2 − γ)/π`,
`C = 12`, `m = 0` (from `Grammar.GaussianDepthThreeTwoTerm`). -/
theorem twoTermData_three :
    TwoTermData (gaussLaplaceL 3) (1 / (4 * Real.pi)) ((2 * Real.log 2 -
        Real.eulerMascheroniConstant) / Real.pi)
      12 0 where
  A_nonneg := by positivity
  C_nonneg := by norm_num
  f_nonneg t _ := gaussLaplaceL_nonneg 3 t
  f_le_one t ht := gaussLaplaceL_le_one 3 ht
  bound t ht := by
    have h := gaussLaplaceL_three_two_term_bound ht
    have e : (1 / (4 * Real.pi) * (Real.log t) ^ (0 + 2) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (Real.log t) ^ (0 + 1)) /
          Real.sqrt t =
        ((Real.log t) ^ 2 + 4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log t) /
          (4 * Real.pi * Real.sqrt t) := by
      have := Real.pi_pos
      field_simp
      ring
    rw [e, pow_zero, mul_one]
    exact h

/-- ★★★ **The two-term expansion at every depth**: for every `m`, there is `C_m` with
`|Z_{m+3}(N) − (A (log N)^{m+2} + B (log N)^{m+1})/√N| ≤ C_m (1 + log N)^m/√N` for `N ≥ 1`,
`A = 1/((m+2)! √(2π)^{m+2})`, `B = ((m+4) log 2 − (m+2) γ)/((m+1)! √(2π)^{m+2})`. -/
theorem gaussLaplaceL_two_term_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    TwoTermData (gaussLaplaceL (m + 3))
      (1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)))
      (((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
        ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2))) C m := by
  induction m with
  | zero =>
    refine ⟨12, by norm_num, ?_⟩
    have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hA : (1 : ℝ) / ((0 + 2).factorial * Real.sqrt (2 * Real.pi) ^ (0 + 2)) = 1 / (4 * Real.pi)
        := by
      rw [zero_add, hsq]; norm_num [Nat.factorial]; ring
    have hB : (((0 : ℕ) + 4) * Real.log 2 - ((0 : ℕ) + 2) * Real.eulerMascheroniConstant) /
        (((0 : ℕ) + 1).factorial * Real.sqrt (2 * Real.pi) ^ (0 + 2)) =
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi := by
      rw [zero_add, hsq]; norm_num [Nat.factorial]
      have := Real.pi_pos
      field_simp
      ring
    rw [hA, hB]
    exact twoTermData_three
  | succ m ih =>
    obtain ⟨C, hC, hd⟩ := ih
    obtain ⟨C', hC', hstep⟩ := twoTermStep_bound hd
    refine ⟨C', hC', ?_⟩
    set A := 1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) with hA
    set B := ((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
      ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) with hB
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hA' : 1 / ((m + 1 + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1 + 2)) =
        A / ((m + 3) * Real.sqrt (2 * Real.pi)) := by
      rw [hA, show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hB' : ((m + 1 + 4) * Real.log 2 - (m + 1 + 2) * Real.eulerMascheroniConstant) /
        ((m + 1 + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1 + 2)) =
        (B / (m + 2) + 2 * A * gaussR₀) / Real.sqrt (2 * Real.pi) := by
      rw [hA, hB, show m + 1 + 1 = (m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      unfold gaussR₀
      push_cast
      field_simp
      ring
    refine ⟨by rw [hA']; exact div_nonneg hd.A_nonneg (by positivity), hC',
      fun t _ => gaussLaplaceL_nonneg _ t, fun t ht => gaussLaplaceL_le_one _ ht, fun t ht => ?_⟩
    have hint := integrable_density_mul_gaussLaplaceL (m + 3) (by linarith : (0 : ℝ) ≤ t)
    have h := hstep t ht hint
    rw [← gaussLaplaceL_succ_scalar (m + 3) (by linarith)] at h
    push_cast at hA' hB' ⊢
    rw [hA', hB']
    exact h

/-- ★★★ **The second coefficient at every depth**:
`(√N Z_{m+3}(N) − A (log N)^{m+2})/(log N)^{m+1} → B = ((m+4) log 2 − (m+2)γ)/((m+1)!
√(2π)^{m+2})`. -/
theorem gaussLaplaceL_second_coeff (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 3) N -
      1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop
      (𝓝 (((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
        ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)))) := by
  obtain ⟨C, hC, hd⟩ := gaussLaplaceL_two_term_bound m
  set A := 1 / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) with hA
  set B := ((m + 4) * Real.log 2 - (m + 2) * Real.eulerMascheroniConstant) /
    ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 2)) with hB
  clear_value A B
  have hbound : ∀ᶠ N : ℝ in atTop,
      |(Real.sqrt N * gaussLaplaceL (m + 3) N - A * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1) - B| ≤ C * 2 ^ m / Real.log N := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log N := by linarith
    have h := hd.bound N hN
    have e : (Real.sqrt N * gaussLaplaceL (m + 3) N - A * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1) - B = (Real.sqrt N / (Real.log N) ^ (m + 1)) *
          (gaussLaplaceL (m + 3) N -
            (A * (Real.log N) ^ (m + 2) + B * (Real.log N) ^ (m + 1)) / Real.sqrt N) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hpow : (1 + Real.log N) ^ m ≤ (2 * Real.log N) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    calc Real.sqrt N / (Real.log N) ^ (m + 1) *
          |gaussLaplaceL (m + 3) N -
            (A * (Real.log N) ^ (m + 2) + B * (Real.log N) ^ (m + 1)) / Real.sqrt N|
        ≤ Real.sqrt N / (Real.log N) ^ (m + 1) * (C * (1 + Real.log N) ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * (1 + Real.log N) ^ m / (Real.log N) ^ (m + 1) := by field_simp
      _ ≤ C * (2 * Real.log N) ^ m / (Real.log N) ^ (m + 1) := by gcongr
      _ = C * 2 ^ m / Real.log N := by
          rw [mul_pow, pow_succ]
          field_simp
  have hlim : Tendsto (fun N : ℝ => C * 2 ^ m / Real.log N) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (C * 2 ^ m)
    simpa [div_eq_mul_inv] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs]
  exact hN

end Grammar
