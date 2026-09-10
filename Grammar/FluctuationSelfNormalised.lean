/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Fluctuation
import Grammar.GaussianBound
import Grammar.GaussianDichotomy

/-!
# Self-normalisation of the fluctuation function

The Gaussian-averaging note works with ratios of fluctuation functions
`R₁(a) = S_{λ+1/2}(a)/S_λ(a)` and `R₂(a) = S_{λ+1}(a)/S_λ(a)` (posterior moments of the radial
variable).  This file proves the elementary facts that make every such ratio polynomially bounded,
hence integrable against any Gaussian law for every `β > 0`:

* `fluctuation_eq_two_mul_gaussMomentJ`: `S_μ = 2 J_{2μ}` (the two normalisations of the paper);
* `fluctuation_half_sq_le`: the posterior Cauchy–Schwarz inequality `S_{λ+1/2}² ≤ S_λ S_{λ+1}`,
  from `∫ t^{λ−1} e^{…} (√t − r)² dt ≥ 0`;
* `fluctuation_succ_le`, `fluctuation_half_le`: with the Weber recurrence `R₂ = λ/β + (a/2) R₁`,
  `R₂(a) ≤ 2λ/β + a₊²/4` and `R₁(a) ≤ √(2λ/β + a₊²/4)`;
* `fluctuation_ge_lower`: the polynomial lower bound `S_λ(a) ≥ e^{−2β} λ⁻¹ (1 + |a|)^{−2λ}`, from
  the initial segment `0 < t < (1+|a|)^{−2}` of the integral; with the Gaussian upper bound
  `fluctuation_le_gaussian` this bounds `|log S_λ(a)|` by a quadratic in `a`.
-/

open Real MeasureTheory Set

namespace Grammar

section Basic

variable {β lam : ℝ}

/-- The fluctuation integrand. -/
noncomputable def fluctIntegrandFn (β lam a t : ℝ) : ℝ :=
  t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

theorem fluctuation_eq_integral (β lam a : ℝ) :
    fluctuation β lam a = ∫ t in Ioi (0 : ℝ), fluctIntegrandFn β lam a t := rfl

theorem fluctIntegrandFn_pos {a t : ℝ} (ht : 0 < t) : 0 < fluctIntegrandFn β lam a t :=
  mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

theorem fluctIntegrandFn_nonneg_ae (β lam a : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fluctIntegrandFn β lam a := by
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall fun t ht => (fluctIntegrandFn_pos ht).le

theorem integrableOn_fluctIntegrandFn (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    IntegrableOn (fluctIntegrandFn β lam a) (Ioi 0) :=
  fluctuation_integrableOn β lam hβ hlam a

/-- **The two normalisations**: `S_μ(a) = 2 J_{2μ}(a)` with
`J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds`. -/
theorem fluctuation_eq_two_mul_gaussMomentJ (a : ℝ) :
    fluctuation β lam a = 2 * gaussMomentJ β (2 * lam) a := by
  have h := integral_comp_rpow_Ioi_of_pos (g := fluctIntegrandFn β lam a) (p := 2) two_pos
  rw [fluctuation_eq_integral, ← h]
  unfold gaussMomentJ logMoment
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  simp only [fluctIntegrandFn, smul_eq_mul, pow_zero, mul_one]
  have hsq : Real.sqrt (s ^ (2 : ℝ)) = s := by
    rw [show s ^ (2 : ℝ) = s ^ (2 : ℕ) by exact_mod_cast Real.rpow_natCast s 2]
    exact Real.sqrt_sq hs'.le
  have hpow : (s ^ (2 : ℝ)) ^ (lam - 1) = s ^ (2 * lam - 2) := by
    rw [← Real.rpow_mul hs'.le]; ring_nf
  have hcomb : s ^ ((2 : ℝ) - 1) * s ^ (2 * lam - 2) = s ^ (2 * lam - 1) := by
    rw [← Real.rpow_add hs']; ring_nf
  have h2 : s ^ (2 : ℝ) = s ^ (2 : ℕ) := by exact_mod_cast Real.rpow_natCast s 2
  rw [hsq, hpow, h2, ← Real.exp_add]
  calc 2 * s ^ ((2 : ℝ) - 1) * (s ^ (2 * lam - 2) * Real.exp (-β * s ^ 2 + β * a * s))
      = 2 * (s ^ ((2 : ℝ) - 1) * s ^ (2 * lam - 2)) * Real.exp (-β * s ^ 2 + β * a * s) := by ring
    _ = 2 * (s ^ (2 * lam - 1) * Real.exp (-β * s ^ 2 + β * s * a)) := by rw [hcomb]; ring_nf

end Basic

/-! ### The posterior Cauchy–Schwarz inequality -/

section CauchySchwarz

variable {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ)
include hβ hlam

omit hβ hlam in
theorem fluctIntegrandFn_mul_sqrt (t : ℝ) (ht : 0 < t) :
    fluctIntegrandFn β lam a t * Real.sqrt t = fluctIntegrandFn β (lam + 1 / 2) a t := by
  unfold fluctIntegrandFn
  rw [Real.sqrt_eq_rpow, mul_right_comm, ← Real.rpow_add ht]
  ring_nf

omit hβ hlam in
theorem fluctIntegrandFn_mul_self (t : ℝ) (ht : 0 < t) :
    fluctIntegrandFn β lam a t * t = fluctIntegrandFn β (lam + 1) a t := by
  unfold fluctIntegrandFn
  rw [mul_right_comm]
  nth_rewrite 2 [show t = t ^ (1 : ℝ) from (Real.rpow_one t).symm]
  rw [← Real.rpow_add ht]
  ring_nf

/-- `0 ≤ ∫ t^{λ−1} e^{…} (√t − r)² dt = S_{λ+1} − 2r S_{λ+1/2} + r² S_λ`. -/
theorem fluctuation_quadratic_nonneg (r : ℝ) :
    0 ≤ fluctuation β (lam + 1) a - 2 * r * fluctuation β (lam + 1 / 2) a +
      r ^ 2 * fluctuation β lam a := by
  have h2 := integrableOn_fluctIntegrandFn (lam := lam + 1) hβ (by linarith) a
  have h1 := integrableOn_fluctIntegrandFn (lam := lam + 1 / 2) hβ (by linarith) a
  have h0 := integrableOn_fluctIntegrandFn (lam := lam) hβ hlam a
  have hA : Integrable (fun t => fluctIntegrandFn β (lam + 1) a t -
      2 * r * fluctIntegrandFn β (lam + 1 / 2) a t) (volume.restrict (Ioi 0)) :=
    h2.sub (h1.const_mul _)
  have hint : ∫ t in Ioi (0 : ℝ), (fluctIntegrandFn β (lam + 1) a t -
      2 * r * fluctIntegrandFn β (lam + 1 / 2) a t + r ^ 2 * fluctIntegrandFn β lam a t) =
      fluctuation β (lam + 1) a - 2 * r * fluctuation β (lam + 1 / 2) a +
        r ^ 2 * fluctuation β lam a := by
    rw [integral_add hA (h0.const_mul _), integral_sub h2 (h1.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  rw [← hint]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  rw [← fluctIntegrandFn_mul_self a t ht', ← fluctIntegrandFn_mul_sqrt a t ht']
  have hf := (fluctIntegrandFn_pos (β := β) (lam := lam) (a := a) ht').le
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht'.le
  calc (0 : ℝ) ≤ fluctIntegrandFn β lam a t * (Real.sqrt t - r) ^ 2 := by positivity
    _ = _ := by linear_combination fluctIntegrandFn β lam a t * hsq

/-- **Posterior Cauchy–Schwarz**: `S_{λ+1/2}(a)² ≤ S_λ(a) S_{λ+1}(a)`. -/
theorem fluctuation_half_sq_le :
    fluctuation β (lam + 1 / 2) a ^ 2 ≤ fluctuation β lam a * fluctuation β (lam + 1) a := by
  have h0 := fluctuation_pos β lam a hβ hlam
  have hq := fluctuation_quadratic_nonneg hβ hlam a
    (fluctuation β (lam + 1 / 2) a / fluctuation β lam a)
  have h0' : fluctuation β lam a ≠ 0 := h0.ne'
  have heq : fluctuation β (lam + 1) a -
      2 * (fluctuation β (lam + 1 / 2) a / fluctuation β lam a) * fluctuation β (lam + 1 / 2) a +
      (fluctuation β (lam + 1 / 2) a / fluctuation β lam a) ^ 2 * fluctuation β lam a =
      fluctuation β (lam + 1) a - fluctuation β (lam + 1 / 2) a ^ 2 / fluctuation β lam a := by
    field_simp
    ring
  rw [heq, sub_nonneg, div_le_iff₀ h0] at hq
  linarith

/-- **The second-moment ratio is quadratically bounded**:
`S_{λ+1}(a) ≤ (2λ/β + a₊²/4) S_λ(a)`. -/
theorem fluctuation_succ_le :
    fluctuation β (lam + 1) a ≤ (2 * lam / β + max a 0 ^ 2 / 4) * fluctuation β lam a := by
  have h0 := fluctuation_pos β lam a hβ hlam
  have h1 := fluctuation_pos β (lam + 1 / 2) a hβ (by linarith)
  have hcs := fluctuation_half_sq_le hβ hlam a
  have hrec := fluctuation_recurrence β lam hβ hlam a
  set S0 := fluctuation β lam a
  set S1 := fluctuation β (lam + 1 / 2) a
  set S2 := fluctuation β (lam + 1) a
  have hmax : a ≤ max a 0 := le_max_left _ _
  have hmax0 : 0 ≤ max a 0 := le_max_right _ _
  -- `S2 = (a/2) S1 + (λ/β) S0 ≤ (a₊/2) S1 + (λ/β) S0` and `(a₊/2) S1 ≤ a₊² S0/8 + S1²/(2 S0)`
  have hAM : max a 0 / 2 * S1 ≤ max a 0 ^ 2 / 8 * S0 + S1 ^ 2 / (2 * S0) := by
    have hS0 : 0 < 2 * S0 := by linarith
    have hS0' : S0 ≠ 0 := h0.ne'
    rw [← sub_nonneg]
    have : max a 0 ^ 2 / 8 * S0 + S1 ^ 2 / (2 * S0) - max a 0 / 2 * S1 =
        (max a 0 / 2 * S0 - S1) ^ 2 / (2 * S0) := by
      field_simp
      ring
    rw [this]
    positivity
  have hS1sq : S1 ^ 2 / (2 * S0) ≤ S2 / 2 := by
    rw [div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  have hstep : S2 ≤ max a 0 / 2 * S1 + lam / β * S0 := by
    rw [hrec]
    have : a / 2 * S1 ≤ max a 0 / 2 * S1 := by
      apply mul_le_mul_of_nonneg_right _ h1.le
      linarith
    linarith
  have hlb : 0 < lam / β := div_pos hlam hβ
  have : S2 ≤ max a 0 ^ 2 / 8 * S0 + S2 / 2 + lam / β * S0 := by linarith
  have h2 : S2 / 2 ≤ max a 0 ^ 2 / 8 * S0 + lam / β * S0 := by linarith
  calc S2 = 2 * (S2 / 2) := by ring
    _ ≤ 2 * (max a 0 ^ 2 / 8 * S0 + lam / β * S0) := by linarith
    _ = (2 * lam / β + max a 0 ^ 2 / 4) * S0 := by ring

/-- **The first-moment ratio is linearly bounded**:
`S_{λ+1/2}(a) ≤ √(2λ/β + a₊²/4) S_λ(a)`. -/
theorem fluctuation_half_le :
    fluctuation β (lam + 1 / 2) a ≤
      Real.sqrt (2 * lam / β + max a 0 ^ 2 / 4) * fluctuation β lam a := by
  have h0 := fluctuation_pos β lam a hβ hlam
  have h1 := fluctuation_pos β (lam + 1 / 2) a hβ (by linarith)
  have hcs := fluctuation_half_sq_le hβ hlam a
  have hsucc := fluctuation_succ_le hβ hlam a
  have hB : 0 ≤ 2 * lam / β + max a 0 ^ 2 / 4 := by positivity
  have hsq : fluctuation β (lam + 1 / 2) a ^ 2 ≤
      (2 * lam / β + max a 0 ^ 2 / 4) * fluctuation β lam a ^ 2 := by
    calc fluctuation β (lam + 1 / 2) a ^ 2 ≤ fluctuation β lam a * fluctuation β (lam + 1) a := hcs
      _ ≤ fluctuation β lam a * ((2 * lam / β + max a 0 ^ 2 / 4) * fluctuation β lam a) :=
          mul_le_mul_of_nonneg_left hsucc h0.le
      _ = _ := by ring
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq h1.le, Real.sqrt_mul hB, Real.sqrt_sq h0.le] at this
  exact this

end CauchySchwarz

/-! ### The polynomial lower bound -/

section Lower

variable {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ)
include hβ hlam

/-- **The polynomial lower bound**: `S_λ(a) ≥ e^{−2β} λ⁻¹ (1 + |a|)^{−2λ}`. -/
theorem fluctuation_ge_lower :
    Real.exp (-2 * β) / lam * (1 + |a|) ^ (-(2 * lam)) ≤ fluctuation β lam a := by
  set c : ℝ := (1 + |a|) ^ (-(2 : ℝ)) with hc
  have h1a : 0 < 1 + |a| := by positivity
  have hcpos : 0 < c := Real.rpow_pos_of_pos h1a _
  have hc1 : c ≤ 1 := by
    rw [hc]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg a]) (by norm_num)
  have hsqrtc : Real.sqrt c = (1 + |a|)⁻¹ := by
    rw [hc, Real.sqrt_eq_rpow, ← Real.rpow_mul h1a.le]
    norm_num
    exact Real.rpow_neg_one _
  -- on `(0, c]` the integrand is at least `e^{−2β} t^{λ−1}`
  have hlow : ∀ t ∈ Ioc (0 : ℝ) c,
      Real.exp (-2 * β) * t ^ (lam - 1) ≤ fluctIntegrandFn β lam a t := by
    intro t ht
    unfold fluctIntegrandFn
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht.1.le _)
    have hsqrt : Real.sqrt t ≤ (1 + |a|)⁻¹ := by
      rw [← hsqrtc]; exact Real.sqrt_le_sqrt ht.2
    have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have htle : t ≤ 1 := ht.2.trans hc1
    have h1 : -β * t ≥ -β := by nlinarith
    have h2 : β * a * Real.sqrt t ≥ -β := by
      have : |a| * Real.sqrt t ≤ 1 := by
        calc |a| * Real.sqrt t ≤ |a| * (1 + |a|)⁻¹ := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg a)
          _ ≤ 1 := by rw [mul_inv_le_iff₀ h1a]; linarith
      have : a * Real.sqrt t ≥ -1 := by
        have := neg_abs_le a
        nlinarith [abs_nonneg a, mul_le_mul_of_nonneg_right this hsqrt0]
      nlinarith
    linarith
  have hIoc : IntegrableOn (fluctIntegrandFn β lam a) (Ioc 0 c) :=
    (integrableOn_fluctIntegrandFn hβ hlam a).mono_set Ioc_subset_Ioi_self
  have hrpow : IntegrableOn (fun t : ℝ => Real.exp (-2 * β) * t ^ (lam - 1)) (Ioc 0 c) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (r := lam - 1)
      (by linarith)).const_mul (Real.exp (-2 * β))
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hcpos.le] at this
  calc Real.exp (-2 * β) / lam * (1 + |a|) ^ (-(2 * lam))
      = ∫ t in Ioc (0 : ℝ) c, Real.exp (-2 * β) * t ^ (lam - 1) := by
        rw [← intervalIntegral.integral_of_le hcpos.le, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero,
          show lam - 1 + 1 = lam by ring, hc, ← Real.rpow_mul h1a.le]
        ring_nf
    _ ≤ ∫ t in Ioc (0 : ℝ) c, fluctIntegrandFn β lam a t :=
        setIntegral_mono_on hrpow hIoc measurableSet_Ioc hlow
    _ ≤ ∫ t in Ioi (0 : ℝ), fluctIntegrandFn β lam a t :=
        setIntegral_mono_set (integrableOn_fluctIntegrandFn hβ hlam a)
          (fluctIntegrandFn_nonneg_ae β lam a) (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    _ = fluctuation β lam a := rfl

/-- **`log S_λ` is quadratically bounded**: `|log S_λ(a)| ≤ C₁ + C₂ a²` with explicit constants. -/
theorem abs_log_fluctuation_le :
    |Real.log (fluctuation β lam a)| ≤
      |Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)| + β * a ^ 2 / 2 +
        (2 * β + |Real.log lam| + 2 * lam * Real.log (1 + |a|)) := by
  have hpos := fluctuation_pos β lam a hβ hlam
  have hup := fluctuation_le_gaussian β a lam hβ hlam
  have hlo := fluctuation_ge_lower hβ hlam a
  have h1a : 0 < 1 + |a| := by positivity
  have hG : 0 < (β / 2) ^ (-lam) * Real.Gamma lam :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hlam)
  have hL : 0 < Real.exp (-2 * β) / lam * (1 + |a|) ^ (-(2 * lam)) := by positivity
  have hlogup : Real.log (fluctuation β lam a) ≤
      β * a ^ 2 / 2 + Real.log ((β / 2) ^ (-lam) * Real.Gamma lam) := by
    calc Real.log (fluctuation β lam a) ≤
        Real.log (Real.exp (β * a ^ 2 / 2) * ((β / 2) ^ (-lam) * Real.Gamma lam)) :=
          Real.log_le_log hpos (by rw [← mul_assoc]; exact hup)
      _ = _ := by rw [Real.log_mul (Real.exp_pos _).ne' hG.ne', Real.log_exp]
  have hloglo : -(2 * β) - Real.log lam - 2 * lam * Real.log (1 + |a|) ≤
      Real.log (fluctuation β lam a) := by
    calc -(2 * β) - Real.log lam - 2 * lam * Real.log (1 + |a|)
        = Real.log (Real.exp (-2 * β) / lam * (1 + |a|) ^ (-(2 * lam))) := by
          rw [Real.log_mul (div_pos (Real.exp_pos _) hlam).ne'
            (Real.rpow_pos_of_pos h1a _).ne', Real.log_div (Real.exp_pos _).ne' hlam.ne',
            Real.log_exp, Real.log_rpow h1a]
          ring
      _ ≤ _ := Real.log_le_log hL hlo
  have hlog1a : 0 ≤ Real.log (1 + |a|) := Real.log_nonneg (by linarith [abs_nonneg a])
  have hsq : 0 ≤ β * a ^ 2 / 2 := by positivity
  have hll : 0 ≤ 2 * lam * Real.log (1 + |a|) := by positivity
  rw [abs_le]
  constructor
  · linarith [abs_nonneg (Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)),
      le_abs_self (Real.log lam)]
  · linarith [le_abs_self (Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)),
      abs_nonneg (Real.log lam)]

end Lower

end Grammar
