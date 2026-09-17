/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialShift
import Grammar.JetPowerBound
import Grammar.EmpiricalGeneratingIdentity
import Grammar.AmplitudeFunctional
import Grammar.GaussianJetLaw

/-!
# The absolute-moment envelope of the Wick series

The `r`-th term of the generating series of the empirical coefficient is the population
coefficient of `η (u^k ζ)^r` at exponent `μ + r/2`.  Writing `(u^k)^r = u^{2jk}` (`r = 2j` or
`2j+1`) and applying the iterated monomial shift (`abs_empCoeff_mono_pow_le`) at the FIXED depth
data of `μ` and `μ + 1/2`, then the jet bound of the population coefficient and the Leibniz bound
for jets of powers, gives the deterministic Gamma-growth estimate

`|C_{μ+r/2,q}[η (u^k ζ)^r]| ≤ K · Π_{i<⌊r/2⌋} (μ + 1/2 + i + d − 1) · C_η · (r+1)^R · ‖J_R ζ‖^r`

(`abs_empCoeff_wick_term_le`).  Against an exponential moment `E e^{δ‖J_R ζ‖²} < ∞` with
`δ > 1/4`, the weighted absolute moments `Σ_r (1/r!) E|C_{μ+r/2,q}[η (u^k ζ)^r]|` are summable
(`summable_wick_envelope`, ratio test with limit `1/(4δ)`): the envelope hypothesis of the Wick
series is discharged by a Gaussian-type moment of the field's jet, with the sharp threshold
`δ > 1/4` (for a scalar Gaussian of variance `W`, `E e^{δ Y²} < ∞ ⟺ δ < 1/(2W)`, so `δ > 1/4`
is `W < 2`, the threshold of the fluctuation function).  Combined with the Gaussian jet law
(`GaussianJetLaw`), the Wick series holds for every smooth field with a Gaussian value process and
an exponential moment of its jet with `δ > 1/4` (`integral_empCoeff_gaussian_wick_of_exp_moment`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

variable {d : ℕ} {h k : Fin d → ℕ}

/-- The even Wick amplitude `η (u^k ζ)^{2j} = u^{2jk} (η ζ^{2j})`. -/
theorem wick_amp_even (η ζ : (Fin d → ℝ) → ℝ) (k : Fin d → ℕ) (j : ℕ) :
    (fun v => η v * (mono k v * ζ v) ^ (2 * j)) =
      fun v => mono (fun i => 2 * j * k i) v * (η v * ζ v ^ (2 * j)) := by
  funext v
  rw [mul_pow, mono_pow, show (fun i => k i * (2 * j)) = fun i => 2 * j * k i from
    funext fun i => by ring]
  ring

/-- The odd Wick amplitude `η (u^k ζ)^{2j+1} = u^{2jk} ((η u^k) ζ^{2j+1})`. -/
theorem wick_amp_odd (η ζ : (Fin d → ℝ) → ℝ) (k : Fin d → ℕ) (j : ℕ) :
    (fun v => η v * (mono k v * ζ v) ^ (2 * j + 1)) =
      fun v => mono (fun i => 2 * j * k i) v * ((η v * mono k v) * ζ v ^ (2 * j + 1)) := by
  funext v
  rw [mul_pow, pow_succ, mono_pow, show (fun i => k i * (2 * j)) = fun i => 2 * j * k i from
    funext fun i => by ring]
  ring

/-- The shift products are monotone in the base exponent. -/
theorem prod_shift_le {a b : ℝ} (hab : a ≤ b) (c : ℝ) (hc : 0 ≤ a + c) (j : ℕ) :
    ∏ i ∈ range j, (a + i + c) ≤ ∏ i ∈ range j, (b + i + c) :=
  Finset.prod_le_prod (fun i _ => by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
    fun i _ => by linarith

/-- ★★ **The Gamma-growth bound for the Wick terms at fixed depth**: with `K` the jet bound of
the population coefficients at the depth data of `μ + 1/2`,
`|C_{μ+r/2,q}[η (u^k ζ)^r]| ≤ K Π_{i<⌊r/2⌋}(μ + 1/2 + i + d − 1) · C_η · (r+1)^R ‖J_R ζ‖^r`. -/
theorem abs_empCoeff_wick_term_le (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) {q : ℕ} (hq : q ≤ d - 1)
    {η ζ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ (A : (Fin d → ℝ) → ℝ) (hA : ContDiff ℝ ∞ A),
      ∀ μ' ∈ latticeBelow (Qamb k) (cutoffOf h (μ + 1 / 2)), ∀ q ≤ d - 1,
        |empCoeff A (fun _ => 0) h k μ' q| ≤ K * ‖cubeJet R 1 A hA‖) (r : ℕ) :
    |empCoeff (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ≤
      K * (∏ i ∈ range (r / 2), (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ))) *
        max ‖cubeJet R 1 η hη‖ ‖cubeJet R 1 (fun v => η v * mono k v) (hη.mul (contDiff_mono k))‖ *
        ((r + 1 : ℝ) ^ R * ‖cubeJet R 1 ζ hζ‖ ^ r) := by
  have hQ : 0 < Qamb k := Qamb_pos k hk
  have hμL : μ ∈ latticeBelow (Qamb k) (cutoffOf h (μ + 1 / 2)) := by
    obtain ⟨m, hm⟩ := hμ
    rw [hm]
    refine mem_latticeBelow hQ ?_
    rw [← hm]
    linarith [lt_cutoffOf h (μ + 1 / 2)]
  have hμ' : ∃ m : ℕ, μ + 1 / 2 = (m : ℝ) / Qamb k := by
    obtain ⟨m, hm⟩ := hμ
    obtain ⟨m₀, hm₀⟩ := half_mem_lattice k hk 1
    refine ⟨m + m₀, ?_⟩
    rw [hm, Nat.cast_add, add_div, ← hm₀]
    norm_num
  have hμ'L : μ + 1 / 2 ∈ latticeBelow (Qamb k) (cutoffOf h (μ + 1 / 2)) := by
    obtain ⟨m, hm⟩ := hμ'
    rw [hm]
    refine mem_latticeBelow hQ ?_
    rw [← hm]
    exact lt_cutoffOf h _
  set Cη := max ‖cubeJet R 1 η hη‖
    ‖cubeJet R 1 (fun v => η v * mono k v) (hη.mul (contDiff_mono k))‖ with hCη
  have hCη1 : ‖cubeJet R 1 η hη‖ ≤ Cη := le_max_left _ _
  have hCη2 : ‖cubeJet R 1 (fun v => η v * mono k v) (hη.mul (contDiff_mono k))‖ ≤ Cη :=
    le_max_right _ _
  have hd0 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJζ : 0 ≤ ‖cubeJet R 1 ζ hζ‖ := norm_nonneg _
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' r
  · -- even `r = 2j`: base amplitude `η ζ^{2j}` at `μ`
    subst hj
    have hdiv : 2 * j / 2 = j := by omega
    rw [hdiv, wick_amp_even, show μ + ((2 * j : ℕ) : ℝ) / 2 = μ + j by push_cast; ring]
    have hA : ContDiff ℝ ∞ fun v => η v * ζ v ^ (2 * j) := hη.mul (hζ.pow _)
    have hB : ∀ q ≤ d - 1, |empCoeff (fun v => η v * ζ v ^ (2 * j)) (fun _ => 0) h k μ q| ≤
        K * ‖cubeJet R 1 (fun v => η v * ζ v ^ (2 * j)) hA‖ :=
      fun q hq => hK _ hA μ hμL q hq
    have h1 : |empCoeff (fun v => mono (fun i => 2 * j * k i) v * (η v * ζ v ^ (2 * j)))
        (fun _ => 0) h k (μ + j) q| ≤
        (∏ i ∈ range j, (μ + i + ((d - 1 : ℕ) : ℝ))) *
          (K * ‖cubeJet R 1 (fun v => η v * ζ v ^ (2 * j)) hA‖) :=
      abs_empCoeff_mono_pow_le hA hk hμ hμ0 hB j q hq
    have hJ := norm_cubeJet_mul_pow_le hη hζ R 1 (2 * j)
    have hP : ∏ i ∈ range j, (μ + i + ((d - 1 : ℕ) : ℝ)) ≤
        ∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ)) :=
      prod_shift_le (by linarith) _ (by linarith) j
    have hP0 : 0 ≤ ∏ i ∈ range j, (μ + i + ((d - 1 : ℕ) : ℝ)) :=
      prod_nonneg fun i _ => by positivity
    have hpow0 : 0 ≤ ((2 * j : ℕ) + 1 : ℝ) ^ R * ‖cubeJet R 1 ζ hζ‖ ^ (2 * j) := by positivity
    calc _ ≤ (∏ i ∈ range j, (μ + i + ((d - 1 : ℕ) : ℝ))) *
          (K * ‖cubeJet R 1 (fun v => η v * ζ v ^ (2 * j)) hA‖) := h1
      _ ≤ (∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ))) *
          (K * (Cη * (((2 * j : ℕ) + 1 : ℝ) ^ R * ‖cubeJet R 1 ζ hζ‖ ^ (2 * j)))) := by
          refine mul_le_mul hP (mul_le_mul_of_nonneg_left (hJ.trans ?_) hK0)
            (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hCη1 hpow0
      _ = _ := by
          push_cast
          ring
  · -- odd `r = 2j+1`: base amplitude `(η u^k) ζ^{2j+1}` at `μ + 1/2`
    subst hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv, wick_amp_odd,
      show μ + ((2 * j + 1 : ℕ) : ℝ) / 2 = (μ + 1 / 2) + j by push_cast; ring]
    have hA : ContDiff ℝ ∞ fun v => (η v * mono k v) * ζ v ^ (2 * j + 1) :=
      (hη.mul (contDiff_mono k)).mul (hζ.pow _)
    have hB : ∀ q ≤ d - 1, |empCoeff (fun v => (η v * mono k v) * ζ v ^ (2 * j + 1))
        (fun _ => 0) h k (μ + 1 / 2) q| ≤
        K * ‖cubeJet R 1 (fun v => (η v * mono k v) * ζ v ^ (2 * j + 1)) hA‖ :=
      fun q hq => hK _ hA _ hμ'L q hq
    have h1 : |empCoeff (fun v => mono (fun i => 2 * j * k i) v *
        ((η v * mono k v) * ζ v ^ (2 * j + 1))) (fun _ => 0) h k (μ + 1 / 2 + j) q| ≤
        (∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ))) *
          (K * ‖cubeJet R 1 (fun v => (η v * mono k v) * ζ v ^ (2 * j + 1)) hA‖) :=
      abs_empCoeff_mono_pow_le hA hk hμ' (by linarith) hB j q hq
    have hJ := norm_cubeJet_mul_pow_le (hη.mul (contDiff_mono k)) hζ R 1 (2 * j + 1)
    have hP0 : 0 ≤ ∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ)) :=
      prod_nonneg fun i _ => by positivity
    have hpow0 : 0 ≤ ((2 * j + 1 : ℕ) + 1 : ℝ) ^ R * ‖cubeJet R 1 ζ hζ‖ ^ (2 * j + 1) := by
      positivity
    calc _ ≤ (∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ))) *
          (K * ‖cubeJet R 1 (fun v => (η v * mono k v) * ζ v ^ (2 * j + 1)) hA‖) := h1
      _ ≤ (∏ i ∈ range j, (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ))) *
          (K * (Cη * (((2 * j + 1 : ℕ) + 1 : ℝ) ^ R * ‖cubeJet R 1 ζ hζ‖ ^ (2 * j + 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hJ.trans ?_) hK0) hP0
          exact mul_le_mul_of_nonneg_right hCη2 hpow0
      _ = _ := by
          push_cast
          ring

/-! ### From an exponential moment of the jet norm to the envelope -/

/-- `x^{2n} ≤ (n!/δ^n) e^{δ x²}`. -/
theorem pow_two_mul_le_factorial_mul_exp {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (n : ℕ) :
    x ^ (2 * n) ≤ ((n.factorial : ℝ) / δ ^ n) * Real.exp (δ * x ^ 2) := by
  have h := Real.pow_div_factorial_le_exp (δ * x ^ 2) (mul_nonneg hδ.le (sq_nonneg x)) n
  have hδn : 0 < δ ^ n := pow_pos hδ n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hmp : (δ * x ^ 2) ^ n = δ ^ n * x ^ (2 * n) := by
    rw [mul_pow, ← pow_mul]
  rw [hmp, div_le_iff₀ hfac] at h
  calc x ^ (2 * n) = (δ ^ n * x ^ (2 * n)) / δ ^ n := by field_simp
    _ ≤ (Real.exp (δ * x ^ 2) * n.factorial) / δ ^ n := div_le_div_of_nonneg_right h hδn.le
    _ = ((n.factorial : ℝ) / δ ^ n) * Real.exp (δ * x ^ 2) := by ring

/-- `n!/δ^n ≤ δ · (n+1)!/δ^{n+1}`. -/
theorem factorial_div_pow_le_succ {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (n.factorial : ℝ) / δ ^ n ≤ δ * ((n + 1).factorial / δ ^ (n + 1)) := by
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hδn : 0 < δ ^ n := pow_pos hδ n
  rw [show δ * ((↑n + 1) * ↑n.factorial / (δ ^ n * δ)) = (↑n + 1) * (↑n.factorial / δ ^ n) by
    field_simp]
  have : (0 : ℝ) ≤ n.factorial / δ ^ n := by positivity
  nlinarith

/-- ★ **The moment bound**: `x^r ≤ (1+δ) ((⌊r/2⌋+1)!/δ^{⌊r/2⌋+1}) e^{δ x²}` for `x ≥ 0`. -/
theorem pow_le_factorial_mul_exp_sq {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    x ^ r ≤ (1 + δ) * (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1)) * Real.exp (δ * x ^ 2) := by
  have hexp0 : 0 < Real.exp (δ * x ^ 2) := Real.exp_pos _
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' r
  · subst hj
    have hdiv : 2 * j / 2 = j := by omega
    rw [hdiv]
    have h1 := pow_two_mul_le_factorial_mul_exp hδ x j
    have h2 := factorial_div_pow_le_succ hδ j
    have h3 : (0 : ℝ) ≤ ((j + 1).factorial : ℝ) / δ ^ (j + 1) := by positivity
    calc x ^ (2 * j) ≤ ((j.factorial : ℝ) / δ ^ j) * Real.exp (δ * x ^ 2) := h1
      _ ≤ (δ * (((j + 1).factorial : ℝ) / δ ^ (j + 1))) * Real.exp (δ * x ^ 2) :=
          mul_le_mul_of_nonneg_right h2 hexp0.le
      _ ≤ (1 + δ) * (((j + 1).factorial : ℝ) / δ ^ (j + 1)) * Real.exp (δ * x ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hexp0.le
          nlinarith
  · subst hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv]
    have h1 := pow_two_mul_le_factorial_mul_exp hδ x j
    have h1' := pow_two_mul_le_factorial_mul_exp hδ x (j + 1)
    have h2 := factorial_div_pow_le_succ hδ j
    have h3 : (0 : ℝ) ≤ ((j + 1).factorial : ℝ) / δ ^ (j + 1) := by positivity
    have hodd : x ^ (2 * j + 1) ≤ x ^ (2 * j) + x ^ (2 * (j + 1)) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · have : x ^ (2 * j + 1) ≤ x ^ (2 * j) := by
          rw [pow_succ]
          exact mul_le_of_le_one_right (pow_nonneg hx _) hx1
        have : 0 ≤ x ^ (2 * (j + 1)) := pow_nonneg hx _
        linarith
      · have : x ^ (2 * j + 1) ≤ x ^ (2 * (j + 1)) :=
          pow_le_pow_right₀ hx1.le (by omega)
        have : 0 ≤ x ^ (2 * j) := pow_nonneg hx _
        linarith
    calc x ^ (2 * j + 1) ≤ x ^ (2 * j) + x ^ (2 * (j + 1)) := hodd
      _ ≤ ((j.factorial : ℝ) / δ ^ j) * Real.exp (δ * x ^ 2) +
          (((j + 1).factorial : ℝ) / δ ^ (j + 1)) * Real.exp (δ * x ^ 2) := add_le_add h1 h1'
      _ ≤ (δ * (((j + 1).factorial : ℝ) / δ ^ (j + 1))) * Real.exp (δ * x ^ 2) +
          (((j + 1).factorial : ℝ) / δ ^ (j + 1)) * Real.exp (δ * x ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_right h2 hexp0.le) le_rfl
      _ = (1 + δ) * (((j + 1).factorial : ℝ) / δ ^ (j + 1)) * Real.exp (δ * x ^ 2) := by ring

/-- The rational factors of the ratio test: `(a + c j)/(b + e j) → c/e`. -/
theorem tendsto_linear_div_linear (a : ℝ) {b c e : ℝ} (hb : 0 ≤ b) (he : 0 < e) :
    Tendsto (fun j : ℕ => (a + c * j) / (b + e * j)) atTop (𝓝 (c / e)) := by
  have h1 : Tendsto (fun j : ℕ => a / j) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat a
  have h2 : Tendsto (fun j : ℕ => b / j) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat b
  have h3 : Tendsto (fun j : ℕ => (a / j + c) / (b / j + e)) atTop (𝓝 ((0 + c) / (0 + e))) :=
    (h1.add tendsto_const_nhds).div (h2.add tendsto_const_nhds) (by linarith)
  rw [zero_add, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with j hj
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hden : b + e * j ≠ 0 := by positivity
  have hden' : b / j + e ≠ 0 := by positivity
  rw [div_eq_div_iff hden' hden]
  field_simp

/-! ### The envelope sequence and the ratio test -/

/-- The envelope sequence `K C M (1+δ) · Π_{i<j}(a+i) · (2j+2)^R · (j+1)!/((2j)! δ^{j+1})`. -/
noncomputable def wickEnvelopeSeq (K C M δ a : ℝ) (R : ℕ) (j : ℕ) : ℝ :=
  K * C * M * (1 + δ) * ((∏ i ∈ range j, (a + i)) * ((2 * j + 2 : ℝ) ^ R *
    (((j + 1).factorial : ℝ) / (((2 * j).factorial : ℝ) * δ ^ (j + 1)))))

theorem wickEnvelopeSeq_pos {K C M δ a : ℝ} (hK : 0 < K) (hC : 0 < C) (hM : 0 < M) (hδ : 0 < δ)
    (ha : 0 < a) (R j : ℕ) : 0 < wickEnvelopeSeq K C M δ a R j := by
  unfold wickEnvelopeSeq
  have h1 : 0 < ∏ i ∈ range j, (a + i) := prod_pos fun i _ => by positivity
  have h2 : (0 : ℝ) < (2 * j).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  positivity

theorem wickEnvelopeSeq_ratio {K C M δ a : ℝ} (hK : 0 < K) (hC : 0 < C) (hM : 0 < M)
    (hδ : 0 < δ) (ha : 0 < a) (R j : ℕ) :
    wickEnvelopeSeq K C M δ a R (j + 1) / wickEnvelopeSeq K C M δ a R j =
      ((a + j) / (2 * j + 1)) * ((j + 2) / (2 * j + 2)) * ((2 * j + 4) / (2 * j + 2)) ^ R *
        (1 / δ) := by
  unfold wickEnvelopeSeq
  rw [prod_range_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ (2 * j + 1),
    Nat.factorial_succ (2 * j), Nat.factorial_succ (j + 1)]
  push_cast
  have h1 : (0 : ℝ) < ∏ i ∈ range j, (a + i) := prod_pos fun i _ => by positivity
  have h2 : (0 : ℝ) < (2 * j).factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_pow]
  field_simp
  ring

theorem tendsto_wickEnvelopeSeq_ratio {K C M δ a : ℝ} (hK : 0 < K) (hC : 0 < C) (hM : 0 < M)
    (hδ : 0 < δ) (ha : 0 < a) (R : ℕ) :
    Tendsto (fun j => wickEnvelopeSeq K C M δ a R (j + 1) / wickEnvelopeSeq K C M δ a R j) atTop
      (𝓝 (1 / (4 * δ))) := by
  rw [show (fun j => wickEnvelopeSeq K C M δ a R (j + 1) / wickEnvelopeSeq K C M δ a R j) =
    fun j : ℕ => ((a + j) / (2 * j + 1)) * ((j + 2) / (2 * j + 2)) *
      ((2 * j + 4) / (2 * j + 2)) ^ R * (1 / δ) from
    funext fun j => wickEnvelopeSeq_ratio hK hC hM hδ ha R j]
  have t1 := tendsto_linear_div_linear a (b := 1) (c := 1) (e := 2) zero_le_one two_pos
  have t2 := tendsto_linear_div_linear 2 (b := 2) (c := 1) (e := 2) (by norm_num) two_pos
  have t3 := tendsto_linear_div_linear 4 (b := 2) (c := 2) (e := 2) (by norm_num) two_pos
  have := ((t1.mul t2).mul (t3.pow R)).mul_const (1 / δ)
  have hlim : (1 / 2 : ℝ) * (1 / 2) * (2 / 2) ^ R * (1 / δ) = 1 / (4 * δ) := by
    norm_num
    ring
  rw [← hlim]
  refine this.congr fun j => ?_
  ring

theorem summable_wickEnvelopeSeq {K C M δ a : ℝ} (hK : 0 < K) (hC : 0 < C) (hM : 0 < M)
    (hδ : 1 / 4 < δ) (ha : 0 < a) (R : ℕ) : Summable (wickEnvelopeSeq K C M δ a R) := by
  have hδ0 : 0 < δ := by linarith
  refine summable_of_ratio_test_tendsto_lt_one (l := 1 / (4 * δ)) ?_
    (Eventually.of_forall fun j => (wickEnvelopeSeq_pos hK hC hM hδ0 ha R j).ne') ?_
  · rw [div_lt_one (by positivity)]
    linarith
  · refine (tendsto_wickEnvelopeSeq_ratio hK hC hM hδ0 ha R).congr fun j => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (wickEnvelopeSeq_pos hK hC hM hδ0 ha R _),
      abs_of_pos (wickEnvelopeSeq_pos hK hC hM hδ0 ha R _)]

/-- The envelope sequence read at `⌊r/2⌋` is summable in `r`. -/
theorem summable_wickEnvelopeSeq_half {K C M δ a : ℝ} (hK : 0 < K) (hC : 0 < C) (hM : 0 < M)
    (hδ : 1 / 4 < δ) (ha : 0 < a) (R : ℕ) :
    Summable fun r : ℕ => wickEnvelopeSeq K C M δ a R (r / 2) := by
  have hs := summable_wickEnvelopeSeq hK hC hM hδ ha R
  refine Summable.even_add_odd ?_ ?_
  · refine hs.congr fun j => ?_
    rw [show 2 * j / 2 = j by omega]
  · refine hs.congr fun j => ?_
    rw [show (2 * j + 1) / 2 = j by omega]

/-! ### The envelope -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- ★★★ **The absolute-moment envelope of the Wick series from an exponential moment of the jet
norm**: if `E e^{δ ‖J_R ζ‖²} < ∞` for some `δ > 1/4` (jet order `R` at least the depth of
`μ + 1/2`), then `Σ_r (1/r!) E|C_{μ+r/2,q}[η (u^k ζ)^r]| < ∞`. -/
theorem summable_wick_envelope (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k)
    (hμ0 : 0 < μ) {q : ℕ} (hq : q ≤ d - 1) {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {R : ℕ}
    (hR : ∑ i, depthOf h k (cutoffOf h (μ + 1 / 2)) i ≤ R) {δ : ℝ} (hδ : 1 / 4 < δ)
    (hexp : Integrable (fun o => Real.exp (δ * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ 2)) P) :
    Summable fun r : ℕ => ∫ o, |(1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P := by
  have hδ0 : 0 < δ := by linarith
  have hL0 : L₀ h ≤ cutoffOf h (μ + 1 / 2) := L₀_le_cutoffOf h _
  have hLpos : 0 < cutoffOf h (μ + 1 / 2) := lt_of_lt_of_le (by unfold L₀; omega) hL0
  obtain ⟨K, hK0, hK⟩ := exists_abs_empCoeff_zero_le_norm_cubeJet hk hLpos (depthOf_add hk hL0)
    (depthOf_pos hk hL0) hR
  set Cη := max ‖cubeJet R 1 η hη‖
    ‖cubeJet R 1 (fun v => η v * mono k v) (hη.mul (contDiff_mono k))‖ with hCη
  have hCη0 : 0 ≤ Cη := le_trans (norm_nonneg _) (le_max_left _ _)
  set M := ∫ o, Real.exp (δ * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ 2) ∂P with hM
  have hM0 : 0 ≤ M := integral_nonneg fun o => (Real.exp_pos _).le
  set a := μ + 1 / 2 + ((d - 1 : ℕ) : ℝ) with ha
  have hd0 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 < a := by linarith
  -- the termwise bound
  have hterm : ∀ r : ℕ, ∫ o, |(1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P ≤
      wickEnvelopeSeq (K + 1) (Cη + 1) (M + 1) δ a R (r / 2) := by
    intro r
    have hjr : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
    have hr1 : (r : ℝ) + 1 ≤ 2 * (r / 2 : ℕ) + 2 := by
      have : r ≤ 2 * (r / 2) + 1 := by omega
      exact_mod_cast Nat.succ_le_succ this
    have hfac : ((2 * (r / 2)).factorial : ℝ) ≤ r.factorial := by
      exact_mod_cast Nat.factorial_le hjr
    have hfacpos : (0 : ℝ) < (2 * (r / 2)).factorial := by exact_mod_cast Nat.factorial_pos _
    have hrfacpos : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos _
    have hP0 : 0 ≤ ∏ i ∈ range (r / 2), (a + i) := prod_nonneg fun i _ => by positivity
    have hfac1 : (0 : ℝ) ≤ ((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1) := by positivity
    set A : ℝ := (1 / (r.factorial : ℝ)) * K * Cη * (r + 1 : ℝ) ^ R with hA
    have hA0 : 0 ≤ A := by positivity
    -- pointwise in `o`
    have hpt : ∀ o, |(1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ≤
        (A * ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1)))) *
          Real.exp (δ * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ 2) := fun o => by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / r.factorial)]
      have h1 := abs_empCoeff_wick_term_le (h := h) hk hμ hμ0 hq hη (hζ o) hK0 hK r
      have h2 := pow_le_factorial_mul_exp_sq hδ0 (norm_nonneg (cubeJet R 1 (ζ o) (hζ o))) r
      have hprod : ∏ i ∈ range (r / 2), (μ + 1 / 2 + i + ((d - 1 : ℕ) : ℝ)) =
          ∏ i ∈ range (r / 2), (a + i) := prod_congr rfl fun i _ => by rw [ha]; ring
      rw [hprod] at h1
      have hx : 0 ≤ ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ r := by positivity
      calc (1 / (r.factorial : ℝ)) *
            |empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q|
          ≤ (1 / (r.factorial : ℝ)) * (K * (∏ i ∈ range (r / 2), (a + i)) * Cη *
              ((r + 1 : ℝ) ^ R * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ r)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (A * ∏ i ∈ range (r / 2), (a + i)) * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ r := by
            rw [hA]
            ring
        _ ≤ (A * ∏ i ∈ range (r / 2), (a + i)) * ((1 + δ) *
              (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1)) *
              Real.exp (δ * ‖cubeJet R 1 (ζ o) (hζ o)‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    -- integrate
    have hint : ∫ o, |(1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P ≤
        (A * ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1)))) * M := by
      rw [hM, ← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun o => abs_nonneg _)
        (hexp.const_mul _) (Eventually.of_forall hpt)
    refine hint.trans ?_
    have hcore : 0 ≤ ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1))) := by
      positivity
    have e1 : 1 / (r.factorial : ℝ) ≤ 1 / ((2 * (r / 2)).factorial : ℝ) :=
      one_div_le_one_div_of_le hfacpos hfac
    have e4 : (r + 1 : ℝ) ^ R ≤ (2 * (r / 2 : ℕ) + 2 : ℝ) ^ R :=
      pow_le_pow_left₀ (by positivity) hr1 R
    have p1 : (0 : ℝ) ≤ 1 / (r.factorial : ℝ) := by positivity
    have p4 : (0 : ℝ) ≤ (r + 1 : ℝ) ^ R := by positivity
    have hfive : (1 / (r.factorial : ℝ)) * K * Cη * (r + 1 : ℝ) ^ R * M ≤
        (1 / ((2 * (r / 2)).factorial : ℝ)) * (K + 1) * (Cη + 1) *
          (2 * (r / 2 : ℕ) + 2 : ℝ) ^ R * (M + 1) := by
      gcongr <;> linarith
    have hfinal : A * ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1))) * M =
        ((1 / (r.factorial : ℝ)) * K * Cη * (r + 1 : ℝ) ^ R * M) *
          ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1))) := by
      rw [hA]
      ring
    have hunf : wickEnvelopeSeq (K + 1) (Cη + 1) (M + 1) δ a R (r / 2) =
        ((1 / ((2 * (r / 2)).factorial : ℝ)) * (K + 1) * (Cη + 1) *
          (2 * (r / 2 : ℕ) + 2 : ℝ) ^ R * (M + 1)) *
          ((∏ i ∈ range (r / 2), (a + i)) * (1 + δ) *
          (((r / 2 + 1).factorial : ℝ) / δ ^ (r / 2 + 1))) := by
      unfold wickEnvelopeSeq
      field_simp
    rw [hfinal, hunf]
    exact mul_le_mul_of_nonneg_right hfive hcore
  exact Summable.of_nonneg_of_le (fun r => integral_nonneg fun o => abs_nonneg _) hterm
    (summable_wickEnvelopeSeq_half (by linarith) (by linarith) (by linarith) hδ ha0 R)

/-- ★★★ **The Wick series with every integrability hypothesis discharged**: for a smooth field
whose value process on an open `U ⊇ closedBox d 1` is Gaussian, with pointwise variance profile
`W` of the scaled field `u^k ζ`, measurable jets, and an exponential moment
`E e^{δ ‖J_{R₀} ζ‖²} < ∞` of the field's jet with `δ > 1/4` at the depth data of `μ + 1/2`,

`E[C_{μ,q}[ζ, η]] = Σ_j (1/(2^j j!)) · C^pop_{μ+j,q}[η W^j]`. -/
theorem integral_empCoeff_gaussian_wick_of_exp_moment [IsProbabilityMeasure P]
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {ζ : Ω → (Fin d → ℝ) → ℝ}
    (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hb : closedBox d 1 ⊆ U) (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P)
    {W : (Fin d → ℝ) → ℝ} (hW : ContDiff ℝ ∞ W) (hW0 : ∀ x, 0 ≤ W x)
    (hlaw : ∀ x ∈ closedBox d 1,
      HasLaw (fun o => mono k x * ζ o x) (gaussianReal 0 ⟨W x, hW0 x⟩) P)
    (hJ : ∀ R : ℕ, AEMeasurable
      (fun o => cubeJet R 1 (fun v => mono k v * ζ o v) ((contDiff_mono k).mul (hζ o))) P)
    (hmeas : ∀ r R : ℕ, AEStronglyMeasurable
      (fun o => cubeJet R 1 (fun v => η v * (mono k v * ζ o v) ^ r)
        (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) P)
    {R₀ : ℕ} (hR₀ : ∑ i, depthOf h k (cutoffOf h (μ + 1 / 2)) i ≤ R₀) {δ : ℝ} (hδ : 1 / 4 < δ)
    (hexp : Integrable (fun o => Real.exp (δ * ‖cubeJet R₀ 1 (ζ o) (hζ o)‖ ^ 2)) P) :
    Integrable (fun o => empCoeff η (ζ o) h k μ q) P ∧
    ∫ o, empCoeff η (ζ o) h k μ q ∂P = ∑' j : ℕ, (1 / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q :=
  integral_empCoeff_gaussian_wick_of_isGaussianProcess hk hμ hq hη hζ hU hb hG hW hW0 hlaw hJ
    hmeas (summable_wick_envelope hk hμ hμ0 hq hη hζ hR₀ hδ hexp)

end Grammar
