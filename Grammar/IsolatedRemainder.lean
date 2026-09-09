/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Flatness
import Grammar.EnergyCorrection

/-!
# Isolated remainders of a cutoff expansion at its first exponent (unit 320)

For any finite-cutoff expansion `CutoffExpansion Q D Z c` whose coefficients vanish at every
lattice exponent below `μ₁ = a/Q`, the cutoff `μ₁ + 1/Q` isolates the single exponent `μ₁`
(`absSpectralSum_isolated`), so the remainder `Z − N^{-μ₁} P(log N)` is `O(N^{-μ₁-1/Q}(1+log N)^D)`
and hence, multiplied by ANY power of `log N` and normalised by `N^{-μ₁}`, tends to zero
(`cutoffExpansion_isolated_remainder_mul`: the power gap beats every logarithm). Two derived forms
feed the energy-correction quotient lemmas: the two-term form
`Z/(N^{-μ₁}L^r) − c(μ₁,r+1) L → c(μ₁,r)` when `c(μ₁,q) = 0` above `r+1` (`twoTerm_of_isolated`),
and the log-weighted one-term form `L (Z/N^{-μ₁} − c(μ₁,0)) → 0` when `c(μ₁,q) = 0` for `q > 0`
(`oneTerm_of_isolated`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Below the cutoff `a/Q + 1/Q` only the lattice exponent `a/Q` survives when the coefficients at
`m/Q`, `m < a`, vanish. -/
theorem absSpectralSum_isolated {Q D : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {a : ℕ}
    (hpred : ∀ m : ℕ, m < a → ∀ j, c ((m : ℝ) / Q) j = 0) (N : ℝ) :
    absSpectralSum Q D c ((a : ℝ) / Q + 1 / Q) N =
      N ^ (-((a : ℝ) / Q)) * ∑ j ∈ Finset.range (D + 1), c ((a : ℝ) / Q) j * Real.log N ^ j := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  unfold absSpectralSum
  rw [Finset.sum_eq_single ((a : ℝ) / Q)]
  · intro μ hμ hne
    obtain ⟨⟨m, hm⟩, hμL⟩ := (mem_latticeBelow_iff hQ).1 hμ
    have hma : m < a := by
      rw [hm, ← add_div, div_lt_div_iff_of_pos_right hQ'] at hμL
      have h1 : m < a + 1 := by exact_mod_cast hμL
      have h2 : m ≠ a := fun h => hne (by rw [hm, h])
      omega
    rw [hm, Finset.sum_eq_zero fun j _ => by rw [hpred m hma j, zero_mul], mul_zero]
  · intro hnot
    exfalso
    apply hnot
    have : (0 : ℝ) < 1 / Q := by positivity
    exact mem_latticeBelow hQ (by linarith)

/-- **Isolated remainder with any log weight**: `(Z − N^{-μ₁} P(log N)) (log N)^r / N^{-μ₁} → 0`. -/
theorem cutoffExpansion_isolated_remainder_mul {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {a : ℕ}
    (hpred : ∀ m : ℕ, m < a → ∀ j, c ((m : ℝ) / Q) j = 0) (r : ℕ) :
    Tendsto (fun N => (Z N - N ^ (-((a : ℝ) / Q)) *
        ∑ j ∈ Finset.range (D + 1), c ((a : ℝ) / Q) j * Real.log N ^ j) * Real.log N ^ r /
        N ^ (-((a : ℝ) / Q))) atTop (𝓝 0) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / Q := by positivity
  have hL : 0 < (a : ℝ) / Q + 1 / Q := by positivity
  obtain ⟨K, hK⟩ := h ((a : ℝ) / Q + 1 / Q) hL
  have hmaj := (tendsto_cutoff_ratio (D + r) (μ := (a : ℝ) / Q) (L := (a : ℝ) / Q + 1 / Q)
    (by linarith)).const_mul |K|
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  rw [absSpectralSum_isolated hQ c hpred N] at hN
  have hpow : 0 < N ^ (-((a : ℝ) / Q)) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogr : Real.log N ^ r ≤ (1 + Real.log N) ^ r := pow_le_pow_left₀ hlog (by linarith) r
  have key : |Z N - N ^ (-((a : ℝ) / Q)) *
      ∑ j ∈ Finset.range (D + 1), c ((a : ℝ) / Q) j * Real.log N ^ j| * Real.log N ^ r ≤
      |K| * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ (D + r)) := by
    have h0 : 0 ≤ N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ D * (1 + Real.log N) ^ r := by
      positivity
    calc |Z N - N ^ (-((a : ℝ) / Q)) *
          ∑ j ∈ Finset.range (D + 1), c ((a : ℝ) / Q) j * Real.log N ^ j| * Real.log N ^ r
        ≤ K * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ D) * (1 + Real.log N) ^ r :=
          mul_le_mul hN hlogr (pow_nonneg hlog r) (le_trans (abs_nonneg _) hN)
      _ = K * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ D * (1 + Real.log N) ^ r) := by
          ring
      _ ≤ |K| * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ D * (1 + Real.log N) ^ r) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) h0
      _ = |K| * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ (D + r)) := by
          rw [pow_add]; ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, abs_mul, abs_of_nonneg (pow_nonneg hlog r),
    div_le_iff₀ hpow]
  calc _ ≤ |K| * (N ^ (-((a : ℝ) / Q + 1 / Q)) * (1 + Real.log N) ^ (D + r)) := key
    _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hpow.ne']

/-- Division by a natural power of `log N` preserves convergence to zero. -/
theorem tendsto_div_logpow_of_tendsto {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun N => f N / Real.log N ^ r) atTop (𝓝 0) := by
  have hn : Tendsto (fun N => ‖f N‖) atTop (𝓝 0) := by simpa using hf.norm
  refine squeeze_zero_norm' ?_ hn
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hN)]
    exact hN
  rw [norm_div, Real.norm_eq_abs (Real.log N ^ r), abs_of_pos (pow_pos (by linarith) r)]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ hlog)

/-- A residual with `E · log N / N^{-μ} → 0` is negligible at every scale `N^{-μ} (log N)^r`. -/
theorem tendsto_div_powLog_of_tendsto_mul_log {E : ℝ → ℝ} {μ : ℝ}
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μ)) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun N => E N / (N ^ (-μ) * Real.log N ^ r)) atTop (𝓝 0) := by
  refine (tendsto_div_logpow_of_tendsto hE (r + 1)).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hpow : N ^ (-μ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  field_simp
  ring

/-- An exponentially small residual satisfies the log-weighted hypothesis at every exponent. -/
theorem tendsto_mul_log_div_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (μ : ℝ) :
    Tendsto (fun N => E N * Real.log N / N ^ (-μ)) atTop (𝓝 0) := by
  have h1 := tendsto_target_of_exp E hε hE (μ + 1) 0
  have h2 : Tendsto (fun N : ℝ => Real.log N / N) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-(μ + 1)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hsplit : N ^ (-μ) = N ^ (-(μ + 1)) * N := by
    rw [← Real.rpow_add_one hN0.ne' (-(μ + 1))]
    congr 1
    ring
  rw [hsplit, pow_zero, mul_one]
  field_simp

/-- **Two-term form at the first exponent**: with `c(μ₁, q) = 0` for `q > r + 1`,
`Z/(N^{-μ₁} L^r) − c(μ₁, r+1) L → c(μ₁, r)`. -/
theorem twoTerm_of_isolated {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) {a : ℕ}
    (hpred : ∀ m : ℕ, m < a → ∀ j, c ((m : ℝ) / Q) j = 0) {r : ℕ} (hr : r + 1 ≤ D)
    (hz : ∀ q, r + 1 < q → c ((a : ℝ) / Q) q = 0) :
    Tendsto (fun N => Z N / (N ^ (-((a : ℝ) / Q)) * Real.log N ^ r) -
      c ((a : ℝ) / Q) (r + 1) * Real.log N) atTop (𝓝 (c ((a : ℝ) / Q) r)) := by
  have h1 := tendsto_div_logpow_of_tendsto
    (cutoffExpansion_isolated_remainder_mul hQ h hpred 0) r
  have h2 := twoTerm_split (c ((a : ℝ) / Q)) D r hr hz
  have h3 := (h1.add h2).add_const (c ((a : ℝ) / Q) r)
  rw [zero_add, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hpow : N ^ (-((a : ℝ) / Q)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hlogr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlog
  simp only [pow_zero, mul_one]
  field_simp
  ring

/-- **Log-weighted one-term form** (multiplicity one): with `c(μ₁, q) = 0` for `q > 0`,
`log N · (Z/N^{-μ₁} − c(μ₁, 0)) → 0`. -/
theorem oneTerm_of_isolated {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) {a : ℕ}
    (hpred : ∀ m : ℕ, m < a → ∀ j, c ((m : ℝ) / Q) j = 0)
    (hz : ∀ q, 0 < q → c ((a : ℝ) / Q) q = 0) :
    Tendsto (fun N => Real.log N * (Z N / N ^ (-((a : ℝ) / Q)) - c ((a : ℝ) / Q) 0)) atTop
      (𝓝 0) := by
  have h1 := cutoffExpansion_isolated_remainder_mul hQ h hpred 1
  have hP : ∀ N : ℝ, ∑ j ∈ Finset.range (D + 1), c ((a : ℝ) / Q) j * Real.log N ^ j =
      c ((a : ℝ) / Q) 0 := by
    intro N
    rw [Finset.sum_eq_single 0]
    · simp
    · intro q _ hq
      rw [hz q (Nat.pos_of_ne_zero hq), zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.2 (Nat.succ_pos D)) h0
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hpow : N ^ (-((a : ℝ) / Q)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  rw [hP N, pow_one]
  field_simp

end Grammar
