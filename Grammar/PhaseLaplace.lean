/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseMoving
import Grammar.GammaLaplace

/-!
# Posterior Laplace transform of `NK` at constant phase (unit 342; Astra #41 unit 1)

Two exact identities, deliberately distinguished:
* changing the temperature at fixed phase rescales the sample size and the phase,
  `𝒵_{β+t}(N; a) = 𝒵_β(rN; a√r)`, `r = (β+t)/β`;
* the posterior Laplace transform of `NK` is a temperature change with a *rescaled* phase,
  `𝒵_β(N; a)[e^{-tNK} η] = 𝒵_{β+t}(N; a/r)`.

Hence the posterior Laplace transform `T_N(a,t) = 𝒵_{β+t}(N; a/r)/𝒵_β(N; a)` has the same
normaliser `N^{-λ}L^{m-1}` in numerator and denominator and the constant-phase two-term data apply
at both temperatures: `T_N(a,t) → A_{β+t}(a/r)/A_β(a)` with next-log correction
`(A_β B_{β+t} − A_{β+t} B_β)/A_β²`.  The fixed-phase temperature ratio of `energy_laplace_chart`
is a different quantity once `a ≠ 0`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-- **Temperature rescaling at constant phase**: `𝒵_{β+t}(N; a) = 𝒵_β(rN; a√r)`. -/
theorem origPhaseIntegral_beta_rescale_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {t : ℝ} (ht : 0 ≤ t) {N : ℝ} (hN : 0 ≤ N) (b a : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k (β + t) N b (fun _ => a) η =
      origPhaseIntegral n h k β (N * ((β + t) / β)) b
        (fun _ => a * Real.sqrt ((β + t) / β)) η := by
  unfold origPhaseIntegral
  congr 1
  funext u
  have hr : 0 ≤ (β + t) / β := by positivity
  have hβr : β * ((β + t) / β) = β + t := mul_div_cancel₀ _ hβ.ne'
  have hsq : Real.sqrt ((β + t) / β) * Real.sqrt ((β + t) / β) = (β + t) / β :=
    Real.mul_self_sqrt hr
  rw [Real.sqrt_mul hN]
  congr 2
  linear_combination (N * ∏ i, u i ^ (2 * k i) - Real.sqrt N * (∏ i, u i ^ k i) * a) * hβr -
    (β * Real.sqrt N * (∏ i, u i ^ k i) * a) * hsq

/-- **Energy tilt at constant phase**: `𝒵_β(N; a)[e^{-tNK} η] = 𝒵_{β+t}(N; a β/(β+t))`. -/
theorem origPhaseIntegral_energy_tilt (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {t : ℝ} (ht : 0 ≤ t) (N b a : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N b (fun _ => a)
        (fun u => Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * η u) =
      origPhaseIntegral n h k (β + t) N b (fun _ => a * (β / (β + t))) η := by
  unfold origPhaseIntegral
  congr 1
  funext u
  have hβt : β + t ≠ 0 := by linarith
  rw [show Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * η u * (∏ i, u i ^ h i) *
      Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a) =
      η u * (∏ i, u i ^ h i) * (Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a))
      by ring, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The posterior Laplace transform of `NK` at constant phase `a`:
`T_N(a,t) = 𝒵_N[e^{-tNK} η; a]/𝒵_N[η; a]`. -/
noncomputable def constPhaseLaplace (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a t : ℝ) : ℝ :=
  origPhaseIntegral n h k β N 1 (fun _ => a)
      (fun u => Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * η u) /
    origPhaseIntegral n h k β N 1 (fun _ => a) η

theorem constPhaseLaplace_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β) {t : ℝ}
    (ht : 0 ≤ t) (N : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) :
    constPhaseLaplace n h k β N η a t =
      origPhaseIntegral n h k (β + t) N 1 (fun _ => a * (β / (β + t))) η /
        origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  unfold constPhaseLaplace
  rw [origPhaseIntegral_energy_tilt n h k hβ ht]

/-- At `t = 0` the transform is `1` (nonvanishing denominator). -/
theorem constPhaseLaplace_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) (hZ : origPhaseIntegral n h k β N 1 (fun _ => a) η ≠ 0) :
    constPhaseLaplace n h k β N η a 0 = 1 := by
  unfold constPhaseLaplace
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact div_self hZ

/-- **Constant-phase posterior Laplace limit**:
`T_N(a,t) → A_{β+t}(aβ/(β+t))/A_β(a)`, the leading coefficients at the two temperatures. -/
theorem constPhaseLaplace_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => constPhaseLaplace n h k β N η a t) atTop
      (𝓝 (familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
          (multCount (ratioExp h k) l - 1) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))) := by
  have hβt : 0 < β + t := by linarith
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hZ := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt a η hηc
  have hZ' := constPhase_tendsto n h k hk l (β + t) hl0 hβt hmin hatt (a * (β / (β + t))) η hηc
  rw [← (constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt).2] at hZ
  rw [← (constPhase_leadingCoeff n h k hk hβt (a * (β / (β + t))) hη hηc hev hmin hatt).2] at hZ'
  refine ((hZ'.div hZ hA).congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hN0 _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  simp only [Pi.div_apply]
  rw [constPhaseLaplace_eq n h k hβ ht N η a, div_div_div_cancel_right₀ hpow]

/-- **Next-log correction of the constant-phase posterior Laplace transform**:
`log N (T_N(a,t) − A'/A) → (A B' − A' B)/A²` with `(A, B)` the two-term data at `(β, a)` and
`(A', B')` those at `(β + t, aβ/(β+t))`. -/
theorem constPhaseLaplace_correction (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => Real.log N * (constPhaseLaplace n h k β N η a t -
        familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
          (multCount (ratioExp h k) l - 1) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)))
      atTop (𝓝 ((familySpectralCoeff n h k β (constFamily a) cη l
            (multCount (ratioExp h k) l - 1) *
          constPhaseSecondCoeff n h k (β + t) cη (a * (β / (β + t))) l -
        familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
          (multCount (ratioExp h k) l - 1) * constPhaseSecondCoeff n h k β cη a l) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2)) :=
    by
  have hβt : 0 < β + t := by linarith
  have hZ := constPhase_twoTerm_chart n h k hk hβ a hη hηc hev hmin hatt
  have hZ' := constPhase_twoTerm_chart n h k hk hβt (a * (β / (β + t))) hη hηc hev hmin hatt
  have hq := quotient_second_order hA hZ hZ'
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  rw [constPhaseLaplace_eq n h k hβ ht N η a, sub_self, Real.rpow_zero, one_mul, div_self hlog,
    mul_one]

end Grammar
