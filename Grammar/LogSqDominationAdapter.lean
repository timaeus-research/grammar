/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AveragedFibrePolar

/-!
# A derivative-domination adapter for the averaged fibre theorem

`Grammar.AveragedFibrePolar` averages the fibre polar distributions of the naive Bayes model
(`Grammar.LogSquareDensityPolar`) under an abstract hypothesis: the holomorphic remainders `H_λ`
have derivatives dominated by an integrable function of `λ`.  This file derives that hypothesis
from the fibre data, on a ball `|s − ½| < r`, `0 < r < ½` (Astra round-5 target 3):

* `norm_deriv_mellinIoc_le`: for `‖g(t)‖ ≤ C t^b` on `(0,1]` and `Re s ≤ σ` with `b − 2σ > −1`,
  `‖(M g)'(s)‖ ≤ 2C/(b − 2σ + 1)²` (the exact log-moment `∫₀¹ t^a |log t| dt = 1/(a+1)²`);
* `norm_deriv_mellinIoc_cutoff_le`: for a cutoff integrand `1_{(M,1]} g` with `‖g‖ ≤ K` there and
  `Re s ≤ ½ + r`, `‖(M[1_{(M,1]} g])'(s)‖ ≤ K |log M| M^{−2r}/r` — the negative moment `M^{−2r}`
  of the cutoff, as the consult predicted;
* ★★ `norm_deriv_logSqHolo_le`: the derivative of the fibre remainder `logSqHolo ℓ c b M φ` on the
  ball is bounded by the explicit `logSqDomBound ℓ c b M L φ(0) r`, a polynomial in
  `ℓ, |c|, |b|, L, |φ(0)|, |log M|` times `(1 + M^{−2r})`;
* `averaged_logSq_polar_ball`: the averaged theorem on a ball around `½` (only a neighbourhood is
  needed for the polar conclusion);
* ★★★ `averaged_naiveBayes_polar`: for a measurable family of fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)`
  with `0 < M_λ ≤ 1` and `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, if the polar coefficients and the explicit
  bound are `ν`-integrable (and the remainders are measurable and integrable in `λ` at each `s`),
  the averaged continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`:
  `C̄_{½,3} = −∫φ_λ(0)`, `C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`;
  `integral_logSqMellinFull_eq` identifies it with the averaged fibre Mellin transform on the
  strip `Re s < ½`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The real log-moment and the two derivative bounds -/

/-- `∫₀¹ t^a |log t| dt = 1/(a + 1)²` for `a > −1`. -/
theorem integral_rpow_mul_abs_log_Ioc {a : ℝ} (ha : -1 < a) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ a * |Real.log t| = 1 / (a + 1) ^ 2 := by
  have hs : ((-a / 2 : ℝ) : ℂ).re < 1 / 2 := by simp; linarith
  have h := integral_cpow_log_Ioc hs
  have e : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * ((-a / 2 : ℝ) : ℂ)) * (-2 * (Real.log t : ℂ)) =
      ((2 * (t ^ a * |Real.log t|) : ℝ) : ℂ) := by
    intro t ht
    rw [show (-2 * ((-a / 2 : ℝ) : ℂ)) = ((a : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht.1.le, abs_of_nonpos (Real.log_nonpos ht.1.le ht.2)]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_complex_ofReal, integral_const_mul,
    show (1 - 2 * ((-a / 2 : ℝ) : ℂ)) = ((a + 1 : ℝ) : ℂ) by push_cast; ring,
    show (2 : ℂ) / ((a + 1 : ℝ) : ℂ) ^ 2 = ((2 / (a + 1) ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
  have h' := Complex.ofReal_inj.1 h
  have : (1 : ℝ) / (a + 1) ^ 2 = 2 / (a + 1) ^ 2 / 2 := by ring
  rw [this, ← h']
  ring

/-- Derivative domination for a power-bounded Mellin integrand: `‖g(t)‖ ≤ C t^b` on `(0,1]` and
`Re s ≤ σ` with `b − 2σ > −1` give `‖(M g)'(s)‖ ≤ 2C/(b − 2σ + 1)²`. -/
theorem norm_deriv_mellinIoc_le {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {σ : ℝ} (hσ : -1 < b - 2 * σ) {s : ℂ}
    (hs : s.re ≤ σ) :
    ‖deriv (mellinIoc g) s‖ ≤ 2 * C / (b - 2 * σ + 1) ^ 2 := by
  have hs' : s.re < (b + 1) / 2 := by linarith
  rw [(hasDerivAt_mellinIoc hg hC hb hs').deriv]
  have hmaj : IntegrableOn (fun t : ℝ => 2 * C * (t ^ (b - 2 * σ) * |Real.log t|)) (Ioc 0 1) :=
    (integrableOn_rpow_mul_log_Ioc hσ).const_mul _
  refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have h2 : ‖(-2 * (Real.log t : ℂ))‖ = 2 * |Real.log t| := by
      rw [norm_mul, norm_neg, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
    have hpow : t ^ (-2 * s.re) ≤ t ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
    rw [norm_mul, norm_mul, norm_cpow_neg_two s ht0, h2]
    calc ‖g t‖ * t ^ (-2 * s.re) * (2 * |Real.log t|)
        ≤ C * t ^ b * t ^ (-2 * σ) * (2 * |Real.log t|) := by
          gcongr
          exact hb t ht
      _ = 2 * C * (t ^ (b - 2 * σ) * |Real.log t|) := by
          rw [show b - 2 * σ = b + -2 * σ by ring, Real.rpow_add ht0]
          ring
  · rw [integral_const_mul, integral_rpow_mul_abs_log_Ioc hσ]
    exact le_of_eq (by ring)

/-- Derivative domination for a cutoff integrand: `g` bounded by `K` on `(M, 1]`, `0 < M ≤ 1`,
`Re s ≤ ½ + r`, `0 < r < ½`: `‖(M[1_{(M,1]} g])'(s)‖ ≤ K |log M| M^{−2r}/r`. -/
theorem norm_deriv_mellinIoc_cutoff_le {g : ℝ → ℂ} (hg : Measurable g) {K : ℝ} (hK : 0 ≤ K)
    {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) (hb : ∀ t ∈ Ioc M 1, ‖g t‖ ≤ K) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) {s : ℂ} (hs : s.re ≤ 1 / 2 + r) :
    ‖deriv (mellinIoc ((Ioc M 1).indicator g)) s‖ ≤ K * |Real.log M| * M ^ (-2 * r) / r := by
  have hmeas : AEStronglyMeasurable ((Ioc M 1).indicator g) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hg.indicator measurableSet_Ioc).aestronglyMeasurable
  have hM3 : 0 < M ^ (3 : ℝ) := Real.rpow_pos_of_pos hM0 _
  have hb' : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(Ioc M 1).indicator g t‖ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by
    intro t ht
    by_cases hmem : t ∈ Ioc M 1
    · rw [indicator_of_mem hmem]
      have h1 : M ^ (3 : ℝ) ≤ t ^ (3 : ℝ) := Real.rpow_le_rpow hM0.le hmem.1.le (by norm_num)
      calc ‖g t‖ ≤ K := hb t hmem
        _ = K / M ^ (3 : ℝ) * M ^ (3 : ℝ) := by field_simp
        _ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by gcongr
    · rw [indicator_of_notMem hmem, norm_zero]
      have : 0 ≤ t ^ (3 : ℝ) := Real.rpow_nonneg ht.1.le _
      positivity
  have hs3 : s.re < ((3 : ℝ) + 1) / 2 := by norm_num; linarith
  rw [(hasDerivAt_mellinIoc hmeas (by positivity) hb' hs3).deriv]
  have hlogM : 0 ≤ |Real.log M| := abs_nonneg _
  -- the majorant `2K|log M| t^{−1−2r}` on `(M, 1]`
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-1 - 2 * r)) volume M 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr fun h => by
      rw [uIcc_of_le hM1] at h; exact absurd h.1 (not_le.2 hM0))
  have hmajM : IntegrableOn (fun t : ℝ => 2 * K * |Real.log M| * t ^ (-1 - 2 * r)) (Ioc M 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM1).1 hint).const_mul _
  have hmaj : IntegrableOn ((Ioc M 1).indicator
      fun t : ℝ => 2 * K * |Real.log M| * t ^ (-1 - 2 * r)) (Ioc 0 1) :=
    (hmajM.integrable_indicator measurableSet_Ioc).integrableOn
  refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    by_cases hmem : t ∈ Ioc M 1
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      have h2 : ‖(-2 * (Real.log t : ℂ))‖ = 2 * |Real.log t| := by
        rw [norm_mul, norm_neg, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
      have hpow : t ^ (-2 * s.re) ≤ t ^ (-1 - 2 * r) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
      have hlt : |Real.log t| ≤ |Real.log M| := by
        rw [abs_of_nonpos (Real.log_nonpos ht0.le ht.2), abs_of_nonpos (Real.log_nonpos hM0.le hM1)]
        linarith [Real.log_le_log hM0 hmem.1.le]
      rw [norm_mul, norm_mul, norm_cpow_neg_two s ht0, h2]
      calc ‖g t‖ * t ^ (-2 * s.re) * (2 * |Real.log t|)
          ≤ K * t ^ (-1 - 2 * r) * (2 * |Real.log M|) := by
            gcongr
            exact hb t hmem
        _ = 2 * K * |Real.log M| * t ^ (-1 - 2 * r) := by ring
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
      simp
  · rw [setIntegral_indicator measurableSet_Ioc,
      show Ioc (0 : ℝ) 1 ∩ Ioc M 1 = Ioc M 1 from
        inter_eq_right.2 fun t ht => ⟨hM0.trans ht.1, ht.2⟩,
      ← intervalIntegral.integral_of_le hM1, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, fun h => by
        rw [uIcc_of_le hM1] at h; exact absurd h.1 (not_le.2 hM0)⟩)]
    rw [show (-1 - 2 * r + 1) = -2 * r by ring, Real.one_rpow]
    have hM2 : 0 < M ^ (-2 * r) := Real.rpow_pos_of_pos hM0 _
    have : 2 * K * |Real.log M| * ((1 - M ^ (-2 * r)) / (-2 * r)) =
        K * |Real.log M| * (M ^ (-2 * r) - 1) / r := by
      field_simp
      ring
    rw [this]
    have hKL : 0 ≤ K * |Real.log M| := by positivity
    refine div_le_div_of_nonneg_right ?_ hr.le
    nlinarith

/-! ### The explicit bound for the fibre remainder -/

/-- The explicit dominating constant for `(logSqHolo ℓ c b M φ)'` on `|s − ½| < r`: the four
pieces (even remainder, even cutoff, odd part, odd cutoff). -/
noncomputable def logSqDomBound (ℓ c b M L φ₀ r : ℝ) : ℝ :=
  2 * ((4 * ℓ ^ 2 + |c| + 4 / ((1 / 2 - r) / 2) ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2 +
    (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * |Real.log M| * M ^ (-2 * r) / r +
    2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 +
    2 * |b| * L * |Real.log M| * M ^ (-2 * r) / r

/-- The odd amplitude bound `‖b(φ(t) − φ(−t))‖ ≤ 2|b|L t` on `(0, 1]`. -/
theorem norm_logSqOddAmp_le (b : ℝ) {φ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ) := by
  intro t ht
  have h1 := hL t ⟨by linarith [ht.1], ht.2⟩
  have h2 := hL (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [abs_of_pos ht.1] at h1
  rw [abs_neg, abs_of_pos ht.1] at h2
  unfold logSqOddAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.rpow_one]
  have : |φ t - φ (-t)| ≤ 2 * L * t := by
    calc |φ t - φ (-t)| = |(φ t - φ 0) - (φ (-t) - φ 0)| := by ring_nf
      _ ≤ |φ t - φ 0| + |φ (-t) - φ 0| := abs_sub _ _
      _ ≤ 2 * L * t := by linarith
  calc |b| * |φ t - φ (-t)| ≤ |b| * (2 * L * t) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 2 * |b| * L * t := by ring

theorem measurable_logSqOddAmp (b : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Measurable (logSqOddAmp b φ) := by
  unfold logSqOddAmp
  exact Complex.measurable_ofReal.comp (measurable_const.mul
    (hφ.measurable.sub (hφ.comp continuous_neg).measurable))

/-- The even amplitude is bounded on `(M, 1]` by `(2(|ℓ| + |log M|)² + |c|)(2|φ(0)| + 2L)`. -/
theorem norm_logSqAmp_symm_cutoff_le (ℓ c : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc M 1, ‖logSqAmp ℓ c (symmAmp φ) t‖ ≤
      (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ 0| + 2 * L) := by
  intro t ht
  have ht0 : 0 < t := hM0.trans ht.1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (by simpa using hL 1 ⟨by norm_num, le_rfl⟩)
  have hψL := symmAmp_bound hL t ⟨ht0, ht.2⟩
  have hψ0 := symmAmp_zero φ
  have hlt : |Real.log (1 / t)| ≤ |Real.log M| := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos ht0.le ht.2),
      abs_of_nonpos (Real.log_nonpos hM0.le hM1)]
    linarith [Real.log_le_log hM0 ht.1.le]
  have hsq : (ℓ + Real.log (1 / t)) ^ 2 ≤ (|ℓ| + |Real.log M|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (by linarith)) 2
  have hden : |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| ≤ 2 * (|ℓ| + |Real.log M|) ^ 2 + |c| := by
    calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| ≤ |2 * (ℓ + Real.log (1 / t)) ^ 2| + |c| :=
          abs_sub _ _
      _ ≤ 2 * (|ℓ| + |Real.log M|) ^ 2 + |c| := by
          rw [abs_of_nonneg (by positivity)]
          linarith
  have hamp : |symmAmp φ t| ≤ 2 * |φ 0| + 2 * L := by
    have h1 := abs_le.1 hψL
    have h2 : 2 * L * t ≤ 2 * L := by nlinarith [ht.2]
    rw [hψ0] at h1
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (φ 0), h1.1]
    · linarith [le_abs_self (φ 0), h1.2]
  unfold logSqAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hden hamp (abs_nonneg _) (by positivity)

/-- `|s − ½| < r` gives `Re s ≤ ½ + r`. -/
theorem re_le_of_mem_ball_half {r : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    s.re ≤ 1 / 2 + r := by
  have h := Complex.abs_re_le_norm (s - 1 / 2)
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [this] at h
  linarith [(abs_le.1 (h.trans hs.le)).2]

/-- ★★ **Derivative domination for the fibre remainder**: on the ball `|s − ½| < r`, `0 < r < ½`,
`‖(logSqHolo ℓ c b M φ)'(s)‖ ≤ logSqDomBound ℓ c b M L φ(0) r`. -/
theorem norm_deriv_logSqHolo_le (ℓ c b : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    ‖deriv (logSqHolo ℓ c b M φ) s‖ ≤ logSqDomBound ℓ c b M L (φ 0) r := by
  have hsre : s.re ≤ 1 / 2 + r := re_le_of_mem_ball_half hs
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (by simpa using hL 1 ⟨by norm_num, le_rfl⟩)
  have hψ := continuous_symmAmp hφ
  have hψL := symmAmp_bound hL
  set δ : ℝ := (1 / 2 - r) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the four pieces and their derivatives
  have hAm : AEStronglyMeasurable (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_logSqAmp ℓ c (hψ.sub continuous_const).measurable).aestronglyMeasurable
  have hAb := norm_logSqAmp_sub_le ℓ c hψL hδpos
  have hC0 : 0 ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L) := by positivity
  have hA : HasDerivAt (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0))
      (deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s) s :=
    (hasDerivAt_mellinIoc hAm hC0 hAb (by rw [hδ]; linarith)).differentiableAt.hasDerivAt
  have hBm : Measurable (logSqAmp ℓ c (symmAmp φ)) := measurable_logSqAmp ℓ c hψ.measurable
  have hBb := norm_logSqAmp_symm_cutoff_le ℓ c hM0 hM1 hL
  have hK0 : 0 ≤ (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ 0| + 2 * L) := by positivity
  have hB : HasDerivAt (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ))))
      (deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s) s :=
    ((differentiableOn_mellinIoc_cutoff hBm hK0 hM0 hBb).differentiableAt
      ((isOpen_re_lt 2).mem_nhds (by change s.re < 2; linarith))).hasDerivAt
  have hCm : Measurable (logSqOddAmp b φ) := measurable_logSqOddAmp b hφ
  have hCb := norm_logSqOddAmp_le b hL
  have hCC : 0 ≤ 2 * |b| * L := by positivity
  have hC : HasDerivAt (mellinIoc (logSqOddAmp b φ)) (deriv (mellinIoc (logSqOddAmp b φ)) s) s :=
    (hasDerivAt_mellinIoc hCm.aestronglyMeasurable hCC hCb
      (by norm_num; linarith)).differentiableAt.hasDerivAt
  have hDb : ∀ t ∈ Ioc M 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L := by
    intro t ht
    have ht0 : 0 < t := hM0.trans ht.1
    calc ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ) := hCb t ⟨ht0, ht.2⟩
      _ ≤ 2 * |b| * L := by rw [Real.rpow_one]; nlinarith [ht.2]
  have hD : HasDerivAt (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ)))
      (deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s) s :=
    ((differentiableOn_mellinIoc_cutoff hCm hCC hM0 hDb).differentiableAt
      ((isOpen_re_lt 2).mem_nhds (by change s.re < 2; linarith))).hasDerivAt
  have hsum := (hA.sub hB).add (hC.sub hD)
  have hderiv : deriv (logSqHolo ℓ c b M φ) s =
      deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s -
        deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s +
        (deriv (mellinIoc (logSqOddAmp b φ)) s -
          deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s) := by
    refine HasDerivAt.deriv ?_
    exact hsum
  rw [hderiv]
  -- the four bounds
  have h1 := norm_deriv_mellinIoc_le hAm hC0 hAb (σ := 1 / 2 + r) (by rw [hδ]; linarith) hsre
  have h2 := norm_deriv_mellinIoc_cutoff_le hBm hK0 hM0 hM1 hBb hr hr1 hsre
  have h3 := norm_deriv_mellinIoc_le hCm.aestronglyMeasurable hCC hCb (σ := 1 / 2 + r)
    (by linarith) hsre
  have h4 := norm_deriv_mellinIoc_cutoff_le hCm hCC hM0 hM1 hDb hr hr1 hsre
  have e1 : (1 - 2 * δ - 2 * (1 / 2 + r) + 1) = 1 / 2 - r := by rw [hδ]; ring
  have e3 : ((1 : ℝ) - 2 * (1 / 2 + r) + 1) = 1 - 2 * r := by ring
  rw [e1] at h1
  rw [e3] at h3
  unfold logSqDomBound
  rw [← hδ]
  calc ‖deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s -
        deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s +
        (deriv (mellinIoc (logSqOddAmp b φ)) s -
          deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s)‖
      ≤ ‖deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s‖ +
        ‖deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s‖ +
        (‖deriv (mellinIoc (logSqOddAmp b φ)) s‖ +
          ‖deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    _ ≤ _ := by linarith

/-! ### The averaged theorem on a ball and the naive Bayes corollary -/

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}

/-- The averaged polar theorem on a ball `|s − ½| < r` with a single dominating function `B`. -/
theorem averaged_logSq_polar_ball {φ₀ ℓ c : Λ → ℝ} {H : Λ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableOn ℂ (H l) (Metric.ball (1 / 2 : ℂ) r))
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, Integrable (fun l => H l s) ν)
    {B : Λ → ℝ} (hB : Integrable B ν)
    (hdom : ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv (H l) s‖ ≤ B l) :
    (fun s => (∫ l, (((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s) ∂ν) -
      polarPart 2 (logSqAvgA φ₀ ℓ c ν) (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hopen : IsOpen (Metric.ball (1 / 2 : ℂ) r) := Metric.isOpen_ball
  have hmem : (1 / 2 : ℂ) ∈ Metric.ball (1 / 2 : ℂ) r := Metric.mem_ball_self hr
  have hdom' : ∀ s₀ ∈ Metric.ball (1 / 2 : ℂ) r, ∃ ε > 0,
      Metric.ball s₀ ε ⊆ Metric.ball (1 / 2 : ℂ) r ∧ ∃ B : Λ → ℝ, Integrable B ν ∧
        ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball s₀ ε, ‖deriv (H l) s‖ ≤ B l := by
    intro s₀ hs₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hs₀)
    exact ⟨ε, hε, hball, B, hB, hdom.mono fun l hl s hs => hl s (hball hs)⟩
  have hHol := differentiableOn_integral_of_deriv_dominated hopen hmeas hdiff hint hdom'
  have hcont : ContinuousAt (fun s => ∫ l, H l s ∂ν) (1 / 2) :=
    (hHol.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have hO : (fun s => ∫ l, H l s ∂ν) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  have hU : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s ∈ Metric.ball (1 / 2 : ℂ) r :=
    eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hmem)
  filter_upwards [hU, self_mem_nhdsWithin] with s hs hs'
  have hs2 : s ≠ 1 / 2 := hs'
  have hpt : ∀ l, ((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s =
      polarPart 2 (logSqA (ℓ l) (c l) (2 * φ₀ l)) (1 / 2 : ℂ) s + H l s := fun l => by
    rw [← logSqRat_eq_polarPart (ℓ l) (c l) (2 * φ₀ l) hs2]
  simp_rw [hpt]
  rw [integral_add (integrable_polarPart_logSqA hcoef s) (hint s hs),
    integral_polarPart_logSqA hcoef s]
  ring

/-- On the strip `Re s < ½` the averaged fibre Mellin transform is the averaged continuation. -/
theorem integral_logSqMellinFull_eq {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ}
    (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ l, logSqMellinFull (ℓ l) (c l) (b l) (M l) (φ l) s ∂ν =
      ∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
        logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν := by
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  beta_reduce
  rw [(logSqMellinFull_eq (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l)).2 s hs]
  push_cast
  ring

/-- ★★★ **The averaged naive Bayes polar distributions from the fibre data**: for a family of
fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)` with `0 < M_λ ≤ 1` and `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, if the
fibre polar coefficients and the explicit bound `logSqDomBound` are `ν`-integrable (and the
remainders are measurable and integrable in `λ` at each `s` of the ball `|s − ½| < r`), the averaged
continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`: `C̄_{½,3} = −∫φ_λ(0)`,
`C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`. -/
theorem averaged_naiveBayes_polar {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ} {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ l 0) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      AEStronglyMeasurable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      Integrable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hB : Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r) ν) :
    (fun s => (∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
      logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν) -
      polarPart 2 (logSqAvgA (fun l => φ l 0) ℓ c ν) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  refine averaged_logSq_polar_ball (φ₀ := fun l => φ l 0) hr hcoef hmeas ?_ hint hB ?_
  · refine Eventually.of_forall fun l => ?_
    refine ((logSqMellinFull_eq (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l)).1).mono ?_
    intro s hs
    have := re_le_of_mem_ball_half hs
    change s.re < 1
    linarith
  · exact Eventually.of_forall fun l s hs =>
      norm_deriv_logSqHolo_le (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l) hr hr1 hs

end Grammar
