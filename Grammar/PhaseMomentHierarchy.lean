/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseLaplaceLaw
import Grammar.EnergyHierarchyChart

/-!
# Phase-dressed energy moment hierarchy (unit 344; Astra #41 unit 4)

The leading constant-phase coefficient of the `q`-th energy family `h + 2qk` at exponent `λ + q`
is `(H/2) J_{λ+q}(a)`, with `H` the phase-independent face factor and
`J_ν(a) = ∫₀^∞ y^{ν-1} e^{-βy+βa√y} dy`: both sides satisfy the recursion
`M_{q+1} = ((λ+q) M_q + (a/2) ∂_a M_q)/β` (coefficient transport on one side, the phase-dressed
moment recurrence and `∂_a J_ν = β J_{ν+1/2}` on the other).  Hence the posterior moments
`N^q E[K^q]` at constant phase converge to `J_{λ+q}(a)/J_λ(a) = ∫ y^q dρ_a(y)`, the moments of the
limiting law, and the posterior variance of `NK` converges to the variance of `ρ_a`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

theorem hmin_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    ∀ i, l + r ≤ ratioExp (fun i => h i + 2 * r * k i) k i := by
  intro i
  rw [ratioExp_add_two_mul_k h k hk r i]
  linarith [hmin i]

theorem hatt_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ i, ratioExp (fun i => h i + 2 * r * k i) k i = l + r := by
  obtain ⟨i, hi⟩ := hatt
  exact ⟨i, by rw [ratioExp_add_two_mul_k h k hk r i, hi]⟩

/-- **Leading coefficient of the `q`-th energy family**: `M_q(a) = (H/2) J_{λ+q}(a)`. -/
theorem constPhase_momentCoeff_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (q : ℕ) (a : ℝ) :
    familySpectralCoeff n (fun i => h i + 2 * q * k i) k β (constFamily a) cη (l + q)
        (multCount (ratioExp h k) l - 1) =
      phaseFaceFactor h k l η / 2 * fluctMoment β a 0 (l + q) 0 := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  induction q generalizing a with
  | zero =>
    have e : (fun i => h i + 2 * 0 * k i) = h := funext fun i => by simp
    rw [e]
    simp only [Nat.cast_zero, add_zero]
    rw [(constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt).2, phaseFace_eq_mul,
      fluctMoment_eq_two_mul_phaseMoment]
    ring
  | succ q ih =>
    have e : (fun i => h i + 2 * (q + 1) * k i) = fun i => h i + 2 * q * k i + 2 * k i :=
      funext fun i => by ring
    have hminq := hmin_add_two_mul_k h k hk q hmin
    have hattq := hatt_add_two_mul_k h k hk q hatt
    have hmq : multCount (ratioExp (fun i => h i + 2 * q * k i) k) (l + q) =
        multCount (ratioExp h k) l := multCount_add_two_mul_k h k hk q l
    have hlq : 0 < l + q := by positivity
    rw [e, show l + ((q + 1 : ℕ) : ℝ) = (l + q) + 1 by push_cast; ring,
      population_coeff_add_two_k_phase_deriv n (fun i => h i + 2 * q * k i) k hk hβ a hη hlq
        (multCount (ratioExp h k) l - 1)]
    have hzero := (constPhase_leadingCoeff n (fun i => h i + 2 * q * k i) k hk hβ a hη hηc hev
      hminq hattq).1
    rw [hmq] at hzero
    rw [hzero (multCount (ratioExp h k) l - 1 + 1) (by omega), mul_zero, sub_zero]
    have hfun : (fun a => familySpectralCoeff n (fun i => h i + 2 * q * k i) k β (constFamily a)
        cη (l + q) (multCount (ratioExp h k) l - 1)) =
        fun a => phaseFaceFactor h k l η / 2 * fluctMoment β a 0 (l + q) 0 := funext ih
    rw [hfun, ih a, deriv_const_mul _ (hasDerivAt_fluctMoment_phase hβ hlq 0 a).differentiableAt,
      (hasDerivAt_fluctMoment_phase hβ hlq 0 a).deriv, fluctMoment_succ_exponent_phase hβ hlq a 0]
    simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
    field_simp

/-- **Constant-phase energy moments**: `N^q 𝒵_N[K^q η; a]/𝒵_N[η; a] → J_{λ+q}(a)/J_λ(a)`. -/
theorem constPhase_energy_moment_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0)
    (q : ℕ) :
    Tendsto (fun N => N ^ q * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ q * η u) /
      origPhaseIntegral n h k β N 1 (fun _ => a) η)) atTop
      (𝓝 (fluctMoment β a 0 (l + q) 0 / fluctMoment β a 0 l 0)) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hlq : 0 < l + q := by positivity
  have hminq := hmin_add_two_mul_k h k hk q hmin
  have hattq := hatt_add_two_mul_k h k hk q hatt
  have hmq : multCount (ratioExp (fun i => h i + 2 * q * k i) k) (l + q) =
      multCount (ratioExp h k) l := multCount_add_two_mul_k h k hk q l
  have hZ := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt a η hηc
  have hZq := constPhase_tendsto n (fun i => h i + 2 * q * k i) k hk (l + q) β hlq hβ hminq hattq
    a η hηc
  rw [← (constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt).2] at hZ
  rw [← (constPhase_leadingCoeff n (fun i => h i + 2 * q * k i) k hk hβ a hη hηc hev hminq
    hattq).2, hmq, constPhase_momentCoeff_eq n h k hk hβ hη hηc hev hmin hatt q a] at hZq
  have hA0 := constPhase_momentCoeff_eq n h k hk hβ hη hηc hev hmin hatt 0 a
  simp only [mul_zero, zero_mul, add_zero, Nat.cast_zero] at hA0
  rw [hA0] at hZ hA
  have hH : phaseFaceFactor h k l η / 2 ≠ 0 := left_ne_zero_of_mul hA
  have hJ : fluctMoment β a 0 l 0 ≠ 0 := right_ne_zero_of_mul hA
  have hdiv := hZq.div hZ hA
  rw [mul_div_mul_left _ _ hH] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  have hpow : N ^ (-(l + q)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hNq : N ^ q ≠ 0 := pow_ne_zero _ hN0.ne'
  simp only [Pi.div_apply]
  rw [origPhaseIntegral_energy_pow, show N ^ (-l) = N ^ (-(l + q)) * N ^ q by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
    congr 1
    ring]
  field_simp

/-- The moments of the limiting law: `∫ y^q dρ_a = J_{λ+q}(a)/J_λ(a)`. -/
theorem phaseLaw_moment (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) (q : ℕ) :
    ∫ y, y ^ q ∂(phaseLaw β a l) = fluctMoment β a 0 (l + q) 0 / fluctMoment β a 0 l 0 := by
  rw [phaseLaw_integral β a l hβ hl, ← integral_phaseLawKernel β a (l + q)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 < y := hy
  unfold phaseLawKernel
  rw [mul_right_comm, ← Real.rpow_natCast y q, ← Real.rpow_add hy0]
  congr 2
  ring

/-- **Constant-phase energy moments converge to the moments of `ρ_a`.** -/
theorem constPhase_energy_moment_law (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0)
    (q : ℕ) :
    Tendsto (fun N => N ^ q * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ q * η u) /
      origPhaseIntegral n h k β N 1 (fun _ => a) η)) atTop
      (𝓝 (∫ y, y ^ q ∂(phaseLaw β a l))) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [phaseLaw_moment β a l hβ hl0 q]
  exact constPhase_energy_moment_chart n h k hk hβ a hη hηc hev hmin hatt hA q

/-- **Constant-phase posterior variance of `NK`** converges to the variance of `ρ_a`,
`J_{λ+2}/J_λ − (J_{λ+1}/J_λ)²`. -/
theorem constPhase_energy_variance_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => N ^ 2 * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ 2 * η u) /
      origPhaseIntegral n h k β N 1 (fun _ => a) η) -
      (N * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) * η u) /
      origPhaseIntegral n h k β N 1 (fun _ => a) η)) ^ 2) atTop
      (𝓝 (fluctMoment β a 0 (l + 2) 0 / fluctMoment β a 0 l 0 -
        (fluctMoment β a 0 (l + 1) 0 / fluctMoment β a 0 l 0) ^ 2)) := by
  have h2 := constPhase_energy_moment_chart n h k hk hβ a hη hηc hev hmin hatt hA 2
  have h1 := constPhase_energy_moment_chart n h k hk hβ a hη hηc hev hmin hatt hA 1
  simp only [pow_one, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  exact h2.sub (h1.pow 2)

end Grammar
