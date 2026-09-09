/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FirstNonzeroAsymptotic

/-!
# Superpolynomial flatness under all-cutoff coefficient vanishing (Programme Q, N1, unit 308)

The alternative to a first nonzero coefficient: if every admissible coefficient of a finite-cutoff
expansion vanishes, then `Z(N) = o(N^{-L})` for every real `L` (`flat_of_cutoffExpansion`), because
the expansion at the cutoff `max (L+1) 1` reduces to its remainder `O(N^{-L'}(1+log N)^D)`, `L' >
L`. Assembled: the
global integral of zero-noise (or any) joint data is a finite-cutoff expansion
(`cutoffExpansion_gInt`, from the uniform assembled cutoff bound), so `𝒵_pop = ∑_I 𝒵^I + E` with all
assembled coefficients zero and `E = o(N^{-L})` for all `L` is itself `o(N^{-L})` for all `L`
(`population_flat`, `_exp`).

**Flat does not mean zero**: `e^{-N}` is `o(N^{-L})` for every `L` and never vanishes
(`exp_neg_flat`, `exp_neg_ne_zero`); the flat branch asserts nothing beyond superpolynomial decay.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Flatness**: all admissible coefficients zero ⇒ `Z = o(N^{-L})` for every `L`. -/
theorem flat_of_cutoffExpansion {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) (hzero : ∀ p ∈ admissible D Q, c p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Z N / N ^ (-L)) atTop (𝓝 0) := by
  -- use the cutoff `max (L+1) 1 > 0` (`L` may be negative)
  set L' : ℝ := max (L + 1) 1 with hL'
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLL' : L < L' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨K, hK⟩ := h L' hL'pos
  have hsum : ∀ N, absSpectralSum Q D c L' N = 0 := by
    intro N
    rw [absSpectralSum_eq_sum_indexSet]
    refine Finset.sum_eq_zero fun p hp => ?_
    unfold absTerm
    rw [hzero p (indexSet_subset_admissible hQ hp), zero_mul]
  have hmaj := (tendsto_cutoff_ratio D hLL').const_mul |K|
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hK, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  rw [hsum N, sub_zero] at hN
  have hpow : 0 < N ^ (-L) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow, ← mul_div_assoc,
    div_mul_cancel₀ _ hpow.ne']
  exact hN.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The assembled integral of a fixed joint datum is a finite-cutoff expansion. -/
theorem cutoffExpansion_gInt (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) :
    CutoffExpansion (commonQ k) (commonD n) (gInt ν h k β b x) (gCoeff ν h k β b x) := by
  intro L hL
  refine ⟨gCutoffConst ν h k β b L ‖x‖, ?_⟩
  have hbs : ∀ᶠ N : ℝ in atTop, ∀ I, 1 ≤ boxScale (k I) (b I) N := by
    rw [eventually_all]
    intro I
    have hc : 0 < (b I) ^ (2 * ∑ i, k I i) := pow_pos (hb I) _
    filter_upwards [eventually_ge_atTop (1 / (b I) ^ (2 * ∑ i, k I i))] with N hN
    unfold boxScale
    rwa [div_le_iff₀ hc] at hN
  filter_upwards [hbs, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  exact gCutoff_bound ν h k β b hk hβ hb hL hN1 hN le_rfl

/-- **Assembled flatness**: all assembled coefficients zero and a residual `o(N^{-L})` for every
`L` give `𝒵_pop = o(N^{-L})` for every `L`. -/
theorem population_flat (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : ∀ L : ℝ, Tendsto (fun N => E N / N ^ (-L)) atTop (𝓝 0))
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ k), gCoeff ν h k β b x p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Zpop N / N ^ (-L)) atTop (𝓝 0) := by
  have h1 := flat_of_cutoffExpansion (commonQ_pos k hk) (cutoffExpansion_gInt ν h k β b hk hβ hb x)
    hzero L
  have := h1.add (hE L)
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [hdecomp N, add_div]

/-- The exponentially small residual is `o(N^{-L})` for every `L`. -/
theorem tendsto_div_rpow_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (L : ℝ) :
    Tendsto (fun N => E N / N ^ (-L)) atTop (𝓝 0) := by
  have := tendsto_target_of_exp E hε hE L 0
  simpa using this

/-- Assembled flatness with an exponentially small residual. -/
theorem population_flat_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    {ε : ℝ} (hε : 0 < ε) (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ k), gCoeff ν h k β b x p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Zpop N / N ^ (-L)) atTop (𝓝 0) :=
  population_flat ν h k β b hk hβ hb x Zpop E hdecomp (tendsto_div_rpow_of_exp E hε hE) hzero L

/-- **Regression: flat is not zero.** `e^{-N} = o(N^{-L})` for every `L`… -/
theorem exp_neg_flat (L : ℝ) :
    Tendsto (fun N : ℝ => Real.exp (-N) / N ^ (-L)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero L 1 one_pos
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [Real.rpow_neg hN.le, div_inv_eq_mul, mul_comm, neg_one_mul]

/-- …and never vanishes. -/
theorem exp_neg_ne_zero (N : ℝ) : Real.exp (-N) ≠ 0 := (Real.exp_pos _).ne'

end Grammar
