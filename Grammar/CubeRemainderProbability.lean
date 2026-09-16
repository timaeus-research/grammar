/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.RectRemainderUniform
import Grammar.CubeJets
import Grammar.TightNormTail
import Grammar.GlobalExponentBound

/-!
# The remainder of the random-field cube expansion vanishes in probability

For random smooth fields `ζ n w` on a cube whose jets of the required order (as random elements
of `CubeJetSpace`) have tight laws, the remainder of the cube expansion with cutoff `U`,
normalised by `n^A / (1 + log n)^{d−1}` for any `A < U`, tends to zero in probability. The proof
localises on the jet ball `{‖jet‖ ≤ B}` of probability `≥ 1 − δ` (`TightNormTail`), where the
remainder is bounded by `K_B n^{−U} (1 + log n)^{d−1}` (`RectRemainderUniform`), and lets
`K_B n^{A−U} → 0`. At the cutoff rate itself the remainder is only `O_P(1)` (consult #152).
-/

open MeasureTheory Filter Topology Set Real
open scoped ContDiff ENNReal

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The jet order required by the cube expansion with cutoff `U`. -/
noncomputable def requiredOrder (h k : Fin d → ℕ) (U : ℝ) : ℕ :=
  ∑ i, depthOf h k (max ⌈U⌉₊ (L₀ h)) i

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- ★★ **The random-field cube remainder, normalised by any deterministic sequence `s n` with
`s n · n^{−U} (1 + log n)^{d−1} → 0`, tends to zero in probability.** -/
theorem tendstoInMeasure_cubeRemainder_of_tendsto (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {U : ℝ} {s : ℕ → ℝ}
    (hs : Tendsto (fun n : ℕ => s n * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))) atTop (𝓝 0))
    {R : ℕ} (hR : requiredOrder h k U ≤ R)
    {ζ : ℕ → Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ n w, ContDiff ℝ ∞ (ζ n w))
    {Y : ℕ → Ω → CubeJetSpace d R b} (hYm : ∀ n, Measurable (Y n))
    (htight : IsTightMeasureSet (Set.range fun n => P.map (Y n)))
    (hae : ∀ n, ∀ᵐ w ∂P, Y n w = cubeJet R b (ζ n w) (hζ n w)) :
    TendstoInMeasure P (fun (n : ℕ) w => s n *
      (empIntegralRect η (ζ n w) h k (fun _ => b) n -
        absSpectralSum (Qamb k) (d - 1) (empCoeffRect η (ζ n w) h k (fun _ => b)) U n))
      atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨B, hB0, hB⟩ := exists_norm_tail_bound_of_isTightMeasureSet hYm htight hδ
  obtain ⟨K, N₀, hK0, hK⟩ :=
    empRect_remainder_uniform_on_jetBall (h := h) (k := k) hη hk hb U hB0
  have hlogn : ∀ n : ℕ, 0 ≤ 1 + log (n : ℝ) := fun n => by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [log_nonneg this]
  have hrate : Tendsto (fun n : ℕ => K * (|s n| * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))))
      atTop (𝓝 0) := by
    have h2 := (hs.abs).const_mul K
    rw [abs_zero, mul_zero] at h2
    refine h2.congr fun n => ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (hlogn n) _))]
  have hev : ∀ᶠ n : ℕ in atTop,
      K * (|s n| * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))) < ε :=
    hrate.eventually (gt_mem_nhds hε)
  have hN₀ : ∀ᶠ n : ℕ in atTop, N₀ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop N₀
  have hN1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop 1
  filter_upwards [hev, hN₀, hN1] with n hn hnN₀ hn1
  have hsub : {w | ε ≤ ‖s n *
      (empIntegralRect η (ζ n w) h k (fun _ => b) n -
        absSpectralSum (Qamb k) (d - 1) (empCoeffRect η (ζ n w) h k (fun _ => b)) U n) -
      (0 : ℝ)‖} ⊆ {w | B < ‖Y n w‖} ∪ {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)} := by
    intro w hw
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hYB : ‖Y n w‖ ≤ B := not_lt.1 h1
    have hYeq : Y n w = cubeJet R b (ζ n w) (hζ n w) := not_not.1 h2
    rw [hYeq] at hYB
    have hjet : JetBoundOn (requiredOrder h k U) (closedBox d b) (ζ n w) B :=
      (jetBoundOn_of_norm_cubeJet_le hYB).of_le_order hR
    have hrem := hK (ζ n w) (hζ n w) hjet n hnN₀
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hw
    rw [abs_mul] at hw
    have hle : |s n| * |empIntegralRect η (ζ n w) h k (fun _ => b) n -
          absSpectralSum (Qamb k) (d - 1) (empCoeffRect η (ζ n w) h k (fun _ => b)) U n| ≤
        |s n| * (K * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))) :=
      mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
    have hcalc : |s n| * (K * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))) =
        K * (|s n| * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ (d - 1))) := by ring
    linarith
  calc P {w | ε ≤ ‖s n *
        (empIntegralRect η (ζ n w) h k (fun _ => b) n -
          absSpectralSum (Qamb k) (d - 1) (empCoeffRect η (ζ n w) h k (fun _ => b)) U n) -
        (0 : ℝ)‖}
      ≤ P ({w | B < ‖Y n w‖} ∪ {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)}) := measure_mono hsub
    _ ≤ P {w | B < ‖Y n w‖} + P {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)} :=
        measure_union_le _ _
    _ ≤ δ + 0 := add_le_add (hB n) (le_of_eq (ae_iff.1 (hae n)))
    _ = δ := add_zero δ

/-- `n^A · n^{−U} (1 + log n)^r → 0` for every `A < U`. -/
theorem tendsto_rpow_mul_remainder_scale {A U : ℝ} (hAU : A < U) (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ A * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ r)) atTop (𝓝 0) := by
  have hpos : 0 < U - A := sub_pos.2 hAU
  have h1 : Tendsto (powLogScale (U - A) r) atTop (𝓝 0) := by
    refine (powLogScale_isLittleO_of_lt (half_lt_self hpos) 0 r).trans_tendsto ?_
    refine (tendsto_rpow_neg_atTop (half_pos hpos)).congr' ?_
    filter_upwards with N
    simp [powLogScale]
  have h3 : Tendsto (fun n : ℕ => (2 : ℝ) ^ r * powLogScale (U - A) r n) atTop (𝓝 0) := by
    simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ) ^ r)
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 1 ≤ log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    have h3n : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog0 : 0 ≤ 1 + log (n : ℝ) := by linarith
  have hpow : (1 + log (n : ℝ)) ^ r ≤ 2 ^ r * log (n : ℝ) ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlog0 (by linarith) r
  have hrpow : (n : ℝ) ^ A * (n : ℝ) ^ (-U) = (n : ℝ) ^ (-(U - A)) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _)
    (mul_nonneg (Real.rpow_nonneg hn0.le _) (pow_nonneg hlog0 _)))]
  calc (n : ℝ) ^ A * ((n : ℝ) ^ (-U) * (1 + log (n : ℝ)) ^ r)
      = (n : ℝ) ^ (-(U - A)) * (1 + log (n : ℝ)) ^ r := by rw [← hrpow]; ring
    _ ≤ (n : ℝ) ^ (-(U - A)) * (2 ^ r * log (n : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hn0.le _)
    _ = 2 ^ r * powLogScale (U - A) r n := by unfold powLogScale; ring

/-- ★★ **Below the cutoff rate the cube remainder is `o_P`:** for every `A < U` the remainder of
the cube expansion with cutoff `U`, multiplied by `n^A`, tends to zero in probability. -/
theorem tendstoInMeasure_cubeRemainder_rpow (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {A U : ℝ} (hAU : A < U) {R : ℕ} (hR : requiredOrder h k U ≤ R)
    {ζ : ℕ → Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ n w, ContDiff ℝ ∞ (ζ n w))
    {Y : ℕ → Ω → CubeJetSpace d R b} (hYm : ∀ n, Measurable (Y n))
    (htight : IsTightMeasureSet (Set.range fun n => P.map (Y n)))
    (hae : ∀ n, ∀ᵐ w ∂P, Y n w = cubeJet R b (ζ n w) (hζ n w)) :
    TendstoInMeasure P (fun (n : ℕ) w => (n : ℝ) ^ A *
      (empIntegralRect η (ζ n w) h k (fun _ => b) n -
        absSpectralSum (Qamb k) (d - 1) (empCoeffRect η (ζ n w) h k (fun _ => b)) U n))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInMeasure_cubeRemainder_of_tendsto hη hk hb
    (tendsto_rpow_mul_remainder_scale hAU (d - 1)) hR hζ hYm htight hae

end SmoothEngine

end Grammar
