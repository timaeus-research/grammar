/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.LogSqDominationAdapter

/-!
# The envelope certificate and the basepoint adapter for the averaged fibre theorem

`Grammar.LogSqDominationAdapter` bounds the derivative of the fibre remainder by the explicit
`logSqDomBound`.  This file makes that bound usable facewise (Astra round-6 target 2):

* ★★ `logSqDomBound_le_envelope`: for fixed `0 < r < ½`,
  `logSqDomBound ℓ c b M L φ₀ r ≤ envelopeConst r · W · (1 + M^{−2r})(1 + |log M|⁴)` with the weight
  `W = (1 + |φ₀| + L)(1 + ℓ² + |c| + |b|)` — the consult's coarse envelope, so that near a face with
  `M ≳ d^β`, `W ≲ d^{−η}` and `dν ≲ d^{a−1} dd` the condition is `η + 2rβ < a`;
* `integrable_logSqDomBound_of_envelope`: integrability of the bound from integrability of the
  envelope (measurable fibre data);
* `norm_sub_le_of_deriv_le_ball`: the mean value inequality `‖H(s) − H(½)‖ ≤ B r` on the ball;
* ★★★ `averaged_naiveBayes_polar_basepoint`: the averaged polar theorem with the remainders
  required to be integrable at the single basepoint `s = ½` only (plus the integrable envelope):
  the analytic hypotheses of `averaged_naiveBayes_polar` are discharged from the fibre data.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### Elementary polynomial bounds -/

theorem le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ 4 := by
  rcases le_or_gt x 1 with h | h
  · nlinarith [pow_nonneg hx 4]
  · have h3 : 1 ≤ x ^ 3 := one_le_pow₀ h.le
    nlinarith [mul_le_mul_of_nonneg_left h3 hx]

theorem pow_three_le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 1 + x ^ 4 := by
  rcases le_or_gt x 1 with h | h
  · nlinarith [pow_le_one₀ hx h (n := 3), pow_nonneg hx 4]
  · have : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ h.le (by norm_num)
    linarith

/-! ### The coarse envelope -/

/-- The envelope constant `C_r` of the coarse bound. -/
noncomputable def envelopeConst (r : ℝ) : ℝ :=
  4 * (5 + 4 / ((1 / 2 - r) / 2) ^ 2) / (1 / 2 - r) ^ 2 + 18 / r + 4 / (1 - 2 * r) ^ 2 + 2 / r

/-- ★★ **The coarse envelope**: for `0 < r < ½`, `M > 0`, `L ≥ 0`,
`logSqDomBound ℓ c b M L φ₀ r ≤
  C_r (1 + |φ₀| + L)(1 + ℓ² + |c| + |b|)(1 + M^{−2r})(1 + |log M|⁴)`. -/
theorem logSqDomBound_le_envelope {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2)
    (hM0 : 0 < M) (hL : 0 ≤ L) :
    logSqDomBound ℓ c b M L φ₀ r ≤ envelopeConst r *
      ((1 + |φ₀| + L) * (1 + ℓ ^ 2 + |c| + |b|)) * (1 + M ^ (-2 * r)) *
        (1 + |Real.log M| ^ 4) := by
  unfold logSqDomBound envelopeConst
  set P := 1 + |φ₀| + L with hP
  set Q := 1 + ℓ ^ 2 + |c| + |b| with hQ
  set x := |Real.log M| with hx
  set δ := (1 / 2 - r) / 2 with hδ
  have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg φ₀]
  have hQ1 : 1 ≤ Q := by rw [hQ]; linarith [abs_nonneg c, abs_nonneg b, sq_nonneg ℓ]
  have hx0 : 0 ≤ x := abs_nonneg _
  have hMr : 0 < M ^ (-2 * r) := Real.rpow_pos_of_pos hM0 _
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hd1 : 0 < (1 / 2 - r) ^ 2 := by positivity
  have hd3 : 0 < (1 - 2 * r) ^ 2 := by nlinarith
  have hℓQ : ℓ ^ 2 ≤ Q := by rw [hQ]; linarith [abs_nonneg c, abs_nonneg b]
  have hcQ : |c| ≤ Q := by rw [hQ]; linarith [abs_nonneg b, sq_nonneg ℓ]
  have hbQ : |b| ≤ Q := by rw [hQ]; linarith [abs_nonneg c, sq_nonneg ℓ]
  have hLP : L ≤ P := by rw [hP]; linarith [abs_nonneg φ₀]
  have hφP : |φ₀| ≤ P := by rw [hP]; linarith
  clear_value P Q x δ
  set E := P * Q * (1 + M ^ (-2 * r)) * (1 + x ^ 4) with hE
  clear_value E
  have hPQ : 0 ≤ P * Q := by positivity
  have hE1 : P * Q ≤ E := by
    rw [hE]
    have h1 : 1 ≤ 1 + M ^ (-2 * r) := by linarith
    have h2 : 1 ≤ 1 + x ^ 4 := by nlinarith [pow_nonneg hx0 4]
    nlinarith [mul_le_mul_of_nonneg_left h1 hPQ, mul_le_mul_of_nonneg_left h2
      (mul_nonneg hPQ (by linarith : (0 : ℝ) ≤ 1 + M ^ (-2 * r)))]
  have hE0 : 0 ≤ E := hPQ.trans hE1
  have ha : 4 * ℓ ^ 2 + |c| + 4 / δ ^ 2 ≤ (5 + 4 / δ ^ 2) * Q := by
    have : 0 ≤ 4 / δ ^ 2 := by positivity
    nlinarith
  have hc' : (2 * (|ℓ| + x) ^ 2 + |c|) * x ≤ 9 * Q * (1 + x ^ 4) := by
    have h1 : (|ℓ| + x) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * x ^ 2 := by
      nlinarith [sq_nonneg (|ℓ| - x), sq_abs ℓ]
    have h2 : x ≤ 1 + x ^ 4 := le_one_add_pow_four hx0
    have h3 : x ^ 3 ≤ 1 + x ^ 4 := pow_three_le_one_add_pow_four hx0
    have h4 : (4 * ℓ ^ 2 + |c|) * x ≤ 5 * Q * x :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    have h5 : 5 * Q * x ≤ 5 * Q * (1 + x ^ 4) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : 4 * x ^ 3 ≤ 4 * Q * (1 + x ^ 4) := by
      have : 1 + x ^ 4 ≤ Q * (1 + x ^ 4) := le_mul_of_one_le_left (by positivity) hQ1
      linarith
    have h7 : (2 * (|ℓ| + x) ^ 2 + |c|) * x ≤ (4 * ℓ ^ 2 + 4 * x ^ 2 + |c|) * x :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    have h8 : (4 * ℓ ^ 2 + 4 * x ^ 2 + |c|) * x = (4 * ℓ ^ 2 + |c|) * x + 4 * x ^ 3 := by ring
    linarith
  -- piece 1
  have hp1 : 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2 ≤
      4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E := by
    have h1 : (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L) ≤ ((5 + 4 / δ ^ 2) * Q) * (2 * P) :=
      mul_le_mul ha (by linarith) (by positivity) (by positivity)
    calc 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2
        ≤ 2 * (((5 + 4 / δ ^ 2) * Q) * (2 * P)) / (1 / 2 - r) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) hd1.le
      _ = 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * (P * Q) := by ring
      _ ≤ 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
  -- piece 2
  have hp2 : (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) / r ≤
      18 / r * E := by
    have h1 : (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) =
        ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r) := by ring
    have h2 : 2 * |φ₀| + 2 * L ≤ 2 * P := by linarith
    have h3 : M ^ (-2 * r) ≤ 1 + M ^ (-2 * r) := by linarith
    have h4 : ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r) ≤
        (9 * Q * (1 + x ^ 4)) * (2 * P) * (1 + M ^ (-2 * r)) := by
      have hA0 : 0 ≤ (2 * (|ℓ| + x) ^ 2 + |c|) * x := by positivity
      refine mul_le_mul (mul_le_mul hc' h2 (by positivity) (by positivity)) h3 hMr.le ?_
      positivity
    rw [h1, div_le_iff₀ hr]
    calc ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r)
        ≤ (9 * Q * (1 + x ^ 4)) * (2 * P) * (1 + M ^ (-2 * r)) := h4
      _ = 18 * E := by rw [hE]; ring
      _ = 18 / r * E * r := by field_simp
  -- piece 3
  have hp3 : 2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 ≤ 4 / (1 - 2 * r) ^ 2 * E := by
    have h1 : |b| * L ≤ Q * P := mul_le_mul hbQ hLP hL (by linarith)
    calc 2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 = 4 / (1 - 2 * r) ^ 2 * (|b| * L) := by ring
      _ ≤ 4 / (1 - 2 * r) ^ 2 * (P * Q) := by
          rw [mul_comm P Q]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 / (1 - 2 * r) ^ 2 * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  -- piece 4
  have hp4 : 2 * |b| * L * x * M ^ (-2 * r) / r ≤ 2 / r * E := by
    have h1 : |b| * L ≤ Q * P := mul_le_mul hbQ hLP hL (by linarith)
    have h2 : x ≤ 1 + x ^ 4 := le_one_add_pow_four hx0
    have h3 : M ^ (-2 * r) ≤ 1 + M ^ (-2 * r) := by linarith
    have h4 : |b| * L * x * M ^ (-2 * r) ≤ Q * P * (1 + x ^ 4) * (1 + M ^ (-2 * r)) := by
      refine mul_le_mul (mul_le_mul h1 h2 hx0 (by positivity)) h3 hMr.le (by positivity)
    rw [div_le_iff₀ hr]
    calc 2 * |b| * L * x * M ^ (-2 * r) = 2 * (|b| * L * x * M ^ (-2 * r)) := by ring
      _ ≤ 2 * (Q * P * (1 + x ^ 4) * (1 + M ^ (-2 * r))) := by
          exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * E := by rw [hE]; ring
      _ = 2 / r * E * r := by field_simp
  calc 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2 +
        (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) / r +
        2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 + 2 * |b| * L * x * M ^ (-2 * r) / r
      ≤ 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E + 18 / r * E + 4 / (1 - 2 * r) ^ 2 * E +
        2 / r * E := by linarith
    _ = (4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 + 18 / r + 4 / (1 - 2 * r) ^ 2 + 2 / r) *
        (P * Q) * (1 + M ^ (-2 * r)) * (1 + x ^ 4) := by rw [hE]; ring

theorem logSqDomBound_nonneg {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hM0 : 0 < M) (hL : 0 ≤ L) :
    0 ≤ logSqDomBound ℓ c b M L φ₀ r := by
  unfold logSqDomBound
  have := Real.rpow_pos_of_pos hM0 (-2 * r)
  positivity

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}

theorem measurable_logSqDomBound {ℓ c b M L φ₀ : Λ → ℝ} (hℓ : Measurable ℓ) (hc : Measurable c)
    (hb : Measurable b) (hM : Measurable M) (hL : Measurable L) (hφ : Measurable φ₀) (r : ℝ) :
    Measurable fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r := by
  unfold logSqDomBound
  fun_prop

/-- ★★ **Integrability of the domination bound from an integrable envelope.** -/
theorem integrable_logSqDomBound_of_envelope {ℓ c b M L φ₀ : Λ → ℝ} (hℓ : Measurable ℓ)
    (hc : Measurable c) (hb : Measurable b) (hM : Measurable M) (hLm : Measurable L)
    (hφ : Measurable φ₀) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l)
    (hL : ∀ l, 0 ≤ L l)
    (hEnv : Integrable (fun l => (1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|) *
      (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4)) ν) :
    Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r) ν := by
  refine (hEnv.const_mul (envelopeConst r)).mono'
    (measurable_logSqDomBound hℓ hc hb hM hLm hφ r).aestronglyMeasurable ?_
  refine Eventually.of_forall fun l => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (logSqDomBound_nonneg hr (hM0 l) (hL l))]
  calc logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r
      ≤ envelopeConst r * ((1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|)) *
        (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4) :=
        logSqDomBound_le_envelope hr hr1 (hM0 l) (hL l)
    _ = envelopeConst r * ((1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|) *
        (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4)) := by ring

/-! ### The basepoint adapter -/

/-- The mean value inequality on the ball: `‖H(s) − H(½)‖ ≤ B r`. -/
theorem norm_sub_le_of_deriv_le_ball {H : ℂ → ℂ} {r B : ℝ}
    (hdiff : DifferentiableOn ℂ H (Metric.ball (1 / 2 : ℂ) r))
    (hbound : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv H s‖ ≤ B) (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) : ‖H s - H (1 / 2)‖ ≤ B * r := by
  have h := (convex_ball (1 / 2 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hx)) hbound
    (Metric.mem_ball_self hr) hs
  refine h.trans ?_
  have hlt : ‖s - 1 / 2‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hs
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound _ (Metric.mem_ball_self hr))
  exact mul_le_mul_of_nonneg_left hlt.le hB

/-- ★★★ **The averaged naive Bayes polar distributions with a basepoint hypothesis**: the
remainders `logSqHolo_λ` need only be measurable in `λ` on the ball and integrable at `s = ½`; with
the fibre polar coefficients and the explicit bound `logSqDomBound` integrable, the averaged
continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`. -/
theorem averaged_naiveBayes_polar_basepoint {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1)
    (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ l 0) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      AEStronglyMeasurable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hint0 : Integrable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)) ν)
    (hB : Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r) ν) :
    (fun s => (∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
      logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν) -
      polarPart 2 (logSqAvgA (fun l => φ l 0) ℓ c ν) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  refine averaged_naiveBayes_polar hr hr1 hM0 hM1 hφ hL hcoef hmeas ?_ hB
  intro s hs
  refine (hint0.norm.add (hB.const_mul r)).mono' (hmeas s hs) ?_
  refine Eventually.of_forall fun l => ?_
  have hdiff : DifferentiableOn ℂ (logSqHolo (ℓ l) (c l) (b l) (M l) (φ l))
      (Metric.ball (1 / 2 : ℂ) r) := by
    refine ((logSqMellinFull_eq (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l)).1).mono ?_
    intro z hz
    have := re_le_of_mem_ball_half hz
    change z.re < 1
    linarith
  have hbound : ∀ z ∈ Metric.ball (1 / 2 : ℂ) r,
      ‖deriv (logSqHolo (ℓ l) (c l) (b l) (M l) (φ l)) z‖ ≤
        logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r :=
    fun z hz => norm_deriv_logSqHolo_le (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l) hr hr1 hz
  have hmv := norm_sub_le_of_deriv_le_ball hdiff hbound hr hs
  calc ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s‖
      ≤ ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s -
          logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ +
        ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ := norm_le_norm_sub_add _ _
    _ ≤ logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r * r +
        ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ := by linarith
    _ = ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ +
        r * logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r := by ring

end Grammar
