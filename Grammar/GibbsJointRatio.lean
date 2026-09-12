/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.QuotientInDistribution
import Grammar.ExpectationBridge
import Grammar.EmpiricalConcentration

/-!
# The joint ratio theorem for empirical Gibbs expectations (CCLXXXIX)

The C4 step of the statistical-transfer programme (consult #87): the empirical posterior
expectation `μ̂_n(φ) = Z_n[φ] / Z_n[1]` converges in distribution to `L_φ / L_1` whenever the
PAIR `(a_n Z_n[φ], a_n Z_n[1])` converges jointly in distribution to `(L_φ, L_1)` with
`P(L_1 = 0) = 0` (`tendstoInDistribution_expectation`) — marginal convergence of the two
normalisers is insufficient; the joint law is the hypothesis. The abstract quotient theorem is
`tendstoInDistribution_div_of_scaled` (`QuotientInDistribution.lean`); this file specialises it to
the Gibbs numerator/normaliser of `EmpiricalConcentration.lean` and adds:

* the bounded-observable corollary: `|φ| ≤ M` gives `|μ̂_n(φ)| ≤ M` (`abs_expectation_le`, no
  positivity of the normaliser needed) and hence `E[μ̂_n(φ)] → E[L_φ / L_1]` with `L_φ / L_1`
  integrable (`tendsto_integral_expectation`, through the uniform second-moment bound);
* the consistency of the two routes: if `μ̂_n(φ) ⇒ L_φ / L_1` and also `μ̂_n(φ) → φ₀` almost
  surely (as for a constant-on-minimisers observable under an a.s.-uniform law of large numbers,
  CCLXXXVIII), then `L_φ / L_1 = φ₀` a.s. — the limiting ratio law is degenerate
  (`ae_div_eq_of_ae_tendsto`, `ae_div_eq_of_eq_on_zeroSet`).

The three quantities `E[L_φ / L_1]`, `E L_φ / E L_1` and `c_φ / c_1` are distinct in general and
none is identified with another here.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace Gibbs

variable {W : Type*} [MeasurableSpace W] (π : Measure W)

/-- The Gibbs numerator `Z[φ] = ∫ φ e^{−n K̂} dπ`, so that `expectation = numerator / normaliser`.
-/
noncomputable def numerator (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ :=
  ∫ w, φ w * Real.exp (-n * Kh w) ∂π

theorem expectation_eq_div (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) :
    expectation π Kh n φ = numerator π Kh n φ / normaliser π Kh n := rfl

theorem normaliser_nonneg (Kh : W → ℝ) (n : ℝ) : 0 ≤ normaliser π Kh n :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- `|Z[φ]| ≤ M Z[1]` for `|φ| ≤ M`. -/
theorem abs_numerator_le {Kh φ : W → ℝ} {n M : ℝ} (hM : ∀ w, |φ w| ≤ M)
    (hI : Integrable (fun w => Real.exp (-n * Kh w)) π) :
    |numerator π Kh n φ| ≤ M * normaliser π Kh n := by
  unfold numerator normaliser
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hI.const_mul M) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hM w) (Real.exp_pos _).le

/-- **The bounded-observable bound**: `|μ̂(φ)| ≤ M` for `|φ| ≤ M`, `0 ≤ M` (with the convention
`x / 0 = 0` no positivity of the normaliser is needed). -/
theorem abs_expectation_le {Kh φ : W → ℝ} {n M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, |φ w| ≤ M)
    (hI : Integrable (fun w => Real.exp (-n * Kh w)) π) :
    |expectation π Kh n φ| ≤ M := by
  rw [expectation_eq_div]
  rcases (normaliser_nonneg π Kh n).lt_or_eq with hZ | hZ
  · rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact abs_numerator_le π hM hI
  · rw [← hZ, div_zero, abs_zero]; exact hM0

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- ★ **The joint ratio theorem for Gibbs expectations**: if `(a_i Z_i[φ], a_i Z_i[1]) ⇒ (L_φ, L_1)`
jointly in distribution with `a_i ≠ 0` and `P(L_1 = 0) = 0`, then `μ̂_i(φ) ⇒ L_φ / L_1`. -/
theorem tendstoInDistribution_expectation (Kh : ι → Ω → W → ℝ) (n : ι → ℝ) (φ : W → ℝ)
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hNm : ∀ i, Measurable fun ω => numerator π (Kh i ω) (n i) φ)
    (hZm : ∀ i, Measurable fun ω => normaliser π (Kh i ω) (n i))
    (Lφ L1 : Ω' → ℝ) (hLφm : Measurable Lφ) (hL1m : Measurable L1)
    (hjoint : TendstoInDistribution
      (fun i ω => (a i * numerator π (Kh i ω) (n i) φ, a i * normaliser π (Kh i ω) (n i))) l
      (fun ω => (Lφ ω, L1 ω)) (fun _ => μ) μ')
    (hL1 : μ' {ω | L1 ω = 0} = 0) :
    TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) l
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ' := by
  have heq : (fun i ω => (numerator π (Kh i ω) (n i) φ / (a i)⁻¹,
      normaliser π (Kh i ω) (n i) / (a i)⁻¹)) =
      fun i ω => (a i * numerator π (Kh i ω) (n i) φ, a i * normaliser π (Kh i ω) (n i)) := by
    funext i ω
    simp only [div_inv_eq_mul, Prod.mk.injEq]
    exact ⟨mul_comm _ _, mul_comm _ _⟩
  have h := tendstoInDistribution_div_of_scaled (fun i ω => numerator π (Kh i ω) (n i) φ)
    (fun i ω => normaliser π (Kh i ω) (n i)) (fun i => (a i)⁻¹) (fun i => inv_ne_zero (ha i))
    hNm hZm Lφ L1 hLφm hL1m (by rw [heq]; exact hjoint) hL1
  exact h

/-- **Bounded observables have convergent expectations**: with `|φ| ≤ M` and `μ̂_i(φ) ⇒ L_φ / L_1`
along `ℕ`, the limit is integrable and `E[μ̂_i(φ)] → E[L_φ / L_1]`. -/
theorem tendsto_integral_expectation {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ w, |φ w| ≤ M)
    (hI : ∀ i ω, Integrable (fun w => Real.exp (-n i * Kh i ω w)) π)
    (hEm : ∀ i, Measurable fun ω => expectation π (Kh i ω) (n i) φ) {Lφ L1 : Ω' → ℝ}
    (h : TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) atTop
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ') :
    Integrable (fun ω => Lφ ω / L1 ω) μ' ∧
      Tendsto (fun i => ∫ ω, expectation π (Kh i ω) (n i) φ ∂μ) atTop
        (𝓝 (∫ ω, Lφ ω / L1 ω ∂μ')) := by
  have hbound : ∀ i ω, |expectation π (Kh i ω) (n i) φ| ^ (2:ℝ) ≤ M ^ (2:ℝ) := fun i ω =>
    Real.rpow_le_rpow (abs_nonneg _) (abs_expectation_le π hM0 hM (hI i ω)) two_pos.le
  have hint : ∀ i, Integrable (fun ω => |expectation π (Kh i ω) (n i) φ| ^ (2:ℝ)) μ := fun i =>
    (integrable_const (M ^ (2:ℝ))).mono' ((hEm i).abs.pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hbound i ω)
  have hMb : ∀ i, ∫ ω, |expectation π (Kh i ω) (n i) φ| ^ (2:ℝ) ∂μ ≤ M ^ (2:ℝ) := fun i => by
    refine (integral_mono (hint i) (integrable_const _) fun ω => hbound i ω).trans_eq ?_
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
  exact tendsto_integral_of_tendstoInDistribution_of_moment (Ω := fun _ => Ω) (μ := fun _ => μ) h
    one_lt_two hint hMb

/-- **Consistency of the two routes**: if `μ̂_i(φ) ⇒ L_φ / L_1` in distribution and `μ̂_i(φ) → φ₀`
almost surely, then `L_φ / L_1 = φ₀` almost surely — the limiting ratio law is degenerate. -/
theorem ae_div_eq_of_ae_tendsto {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ}
    (hEm : ∀ i, Measurable fun ω => expectation π (Kh i ω) (n i) φ) {Lφ L1 : Ω' → ℝ}
    (h : TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) atTop
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ') {φ₀ : ℝ}
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun i => expectation π (Kh i ω) (n i) φ) atTop (𝓝 φ₀)) :
    ∀ᵐ ω ∂μ', Lφ ω / L1 ω = φ₀ := by
  have h2 : TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) atTop
      (fun _ => φ₀) (fun _ => μ) μ :=
    tendstoInDistribution_of_ae_tendsto (fun i => (hEm i).aemeasurable) aemeasurable_const hae
  have hmap : μ'.map (fun ω => Lφ ω / L1 ω) = Measure.dirac φ₀ := by
    rw [tendstoInDistribution_unique _ h h2, Measure.map_const, measure_univ, one_smul]
  rw [ae_iff]
  have hset : {ω | ¬ Lφ ω / L1 ω = φ₀} = (fun ω => Lφ ω / L1 ω) ⁻¹' {φ₀}ᶜ := by
    ext ω; simp
  rw [hset, ← Measure.map_apply_of_aemeasurable h.aemeasurable_limit
    (measurableSet_singleton _).compl, hmap, Measure.dirac_apply,
    Set.indicator_of_notMem (by simp)]

end Gibbs

/-! ### Constant-on-minimisers observables: the degenerate ratio law -/

namespace Gibbs

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
  (hunif : ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n ω w - K w| ≤ ε)

omit [IsProbabilityMeasure μ] in
include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 hKhm hunif in
/-- **The almost-sure wrapper of CCLXXXVIII's observable theorem**: under an a.s.-uniform law of
large numbers, `μ̂_n(φ) → φ₀` almost surely for a constant-on-minimisers observable. -/
theorem ae_tendsto_expectation_of_eq_on_zeroSet :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => expectation π (Kh n ω) n φ) atTop (𝓝 φ₀) := by
  filter_upwards [hunif] with ω hω
  exact tendsto_expectation_of_eq_on_zeroSet π hS hπS hK0 hKm hKc hφm hφc hpos hφ0
    (fun n => Kh n ω) (hKhm · ω) hω

include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 hKhm hunif in
/-- ★★ **The degenerate ratio law**: for a constant-on-minimisers observable, any joint
distributional limit `(a_n Z_n[φ], a_n Z_n[1]) ⇒ (L_φ, L_1)` with `P(L_1 = 0) = 0` has
`L_φ / L_1 = φ₀` almost surely (under an a.s.-uniform law of large numbers for the empirical
phase): the fluctuation of the empirical posterior cannot move the limiting posterior expectation
of such an observable. -/
theorem ae_div_eq_of_eq_on_zeroSet (a : ℕ → ℝ) (ha : ∀ i, a i ≠ 0)
    (hNm : ∀ i, Measurable fun ω => numerator π (Kh i ω) i φ)
    (hZm : ∀ i, Measurable fun ω => normaliser π (Kh i ω) i)
    (Lφ L1 : Ω' → ℝ) (hLφm : Measurable Lφ) (hL1m : Measurable L1)
    (hjoint : TendstoInDistribution
      (fun i ω => (a i * numerator π (Kh i ω) i φ, a i * normaliser π (Kh i ω) i)) atTop
      (fun ω => (Lφ ω, L1 ω)) (fun _ => μ) μ')
    (hL1 : μ' {ω | L1 ω = 0} = 0) :
    ∀ᵐ ω ∂μ', Lφ ω / L1 ω = φ₀ :=
  ae_div_eq_of_ae_tendsto π (fun i => (hNm i).div (hZm i))
    (tendstoInDistribution_expectation π Kh (fun i : ℕ => (i : ℝ)) φ a ha hNm hZm Lφ L1 hLφm hL1m
      hjoint hL1)
    (ae_tendsto_expectation_of_eq_on_zeroSet π hS hπS hK0 hKm hKc hφm hφc hpos hφ0 Kh hKhm hunif)

end Gibbs

end Grammar
