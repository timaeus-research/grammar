/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneratingUniform
import Grammar.CubeRemainderProbability

/-!
# Truncation of the generating series in probability (§20, Stage E)

For random smooth fields whose cube jets (measurable, `CubeJetSpace`-valued) have tight laws and
any deterministic `R_n → ∞`, the truncation error of the generating identity
`empCoeffRect η ζₙ … μ q − Σ_{r<R_n} (1/r!) empCoeffRect (η (u^k ζₙ)^r) 0 … (μ + r/2) q`
tends to zero in probability (★★ `tendstoInMeasure_generatingTruncation`): on the event
`‖jet‖ ≤ B` the error is `≤ C_B (1/2)^{R_n}` by the uniform ballwise estimate, and the event
`‖jet‖ > B` has probability `≤ δ` by tightness.  No expectation is interchanged.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Real
open scoped ContDiff ENNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} (h k : Fin d → ℕ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- ★★ **Truncation of the generating series in probability**: for tight random cube jets and any
deterministic `R_n → ∞`, the truncation error of the generating identity tends to zero in
probability. -/
theorem tendstoInMeasure_generatingTruncation (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) {ζ : ℕ → Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ n w, ContDiff ℝ ∞ (ζ n w))
    {Y : ℕ → Ω → CubeJetSpace d R b} (hYm : ∀ n, Measurable (Y n))
    (htight : IsTightMeasureSet (Set.range fun n => P.map (Y n)))
    (hae : ∀ n, ∀ᵐ w ∂P, Y n w = cubeJet R b (ζ n w) (hζ n w)) {Rn : ℕ → ℕ}
    (hRn : Tendsto Rn atTop atTop) :
    TendstoInMeasure P (fun (n : ℕ) w => empCoeffRect η (ζ n w) h k (fun _ => b) μ q -
      ∑ r ∈ Finset.range (Rn n), (1 / (r.factorial : ℝ)) *
        empCoeffRect (fun v => η v * (mono k v * ζ n w v) ^ r) (fun _ => 0) h k (fun _ => b)
          (μ + r / 2) q) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨B, hB0, hB⟩ := exists_norm_tail_bound_of_isTightMeasureSet hYm htight hδ
  obtain ⟨C, hC0, hC⟩ := exists_generatingTail_bound_jetBall_rect h k hη hk hb μ q hB0
  have hgeo : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ (Rn n)) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp hRn
    have h2 := h1.const_mul C
    simpa using h2
  have hev : ∀ᶠ n : ℕ in atTop, C * (1 / 2 : ℝ) ^ (Rn n) < ε := hgeo.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with n hn
  have hsub : {w | ε ≤ ‖(empCoeffRect η (ζ n w) h k (fun _ => b) μ q -
      ∑ r ∈ Finset.range (Rn n), (1 / (r.factorial : ℝ)) *
        empCoeffRect (fun v => η v * (mono k v * ζ n w v) ^ r) (fun _ => 0) h k (fun _ => b)
          (μ + r / 2) q) - (0 : ℝ)‖} ⊆
      {w | B < ‖Y n w‖} ∪ {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)} := by
    intro w hw
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hYB : ‖Y n w‖ ≤ B := not_lt.1 h1
    have hYeq : Y n w = cubeJet R b (ζ n w) (hζ n w) := not_not.1 h2
    rw [hYeq] at hYB
    have hjet : JetBoundOn (cubeOrder h k μ) (closedBox d b) (ζ n w) B :=
      (jetBoundOn_of_norm_cubeJet_le hYB).of_le_order hR
    have hrem := hC (ζ n w) (hζ n w) hjet hμ (Rn n)
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hw
    linarith
  calc P {w | ε ≤ ‖(empCoeffRect η (ζ n w) h k (fun _ => b) μ q -
        ∑ r ∈ Finset.range (Rn n), (1 / (r.factorial : ℝ)) *
          empCoeffRect (fun v => η v * (mono k v * ζ n w v) ^ r) (fun _ => 0) h k (fun _ => b)
            (μ + r / 2) q) - (0 : ℝ)‖}
      ≤ P ({w | B < ‖Y n w‖} ∪ {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)}) := measure_mono hsub
    _ ≤ P {w | B < ‖Y n w‖} + P {w | Y n w ≠ cubeJet R b (ζ n w) (hζ n w)} :=
        measure_union_le _ _
    _ ≤ δ + 0 := add_le_add (hB n) (le_of_eq (ae_iff.1 (hae n)))
    _ = δ := add_zero δ

end Grammar
