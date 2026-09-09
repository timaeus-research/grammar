/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EnergyHierarchy

/-!
# The population energy hierarchy at chart level (unit 330)

The chart-level counterpart of `EnergyHierarchy`: for an analytic amplitude `η` on one normal chart
with face functional `A ≠ 0`, the `r`-fold energy insertion `(u^{2k})^r η` is the weight shift
`h ↦ h + 2rk` (`origPhaseIntegral_energy_pow`), its canonical coefficients are the `r`-fold
transport of those of `η` (`population_coeff_add_two_mul_k`), and
```
N^r 𝒵_N[(K∘π)^r η]/𝒵_N[η] → (λ)_r/β^r,
log N · (N^r 𝒵_N[(K∘π)^r η]/𝒵_N[η] − (λ)_r/β^r) → −(m−1) ∂_λ(λ)_r/β^r
```
(`energy_moment_chart`), with the posterior variance of `NK` (`energy_variance_chart`):
`V_N → λ/β²`, `log N (V_N − λ/β²) → −(m−1)/β²`. The identification of the face functional with the
canonical leading coefficient of the Taylor family is `amplitudeCoeff_eq_spectral`. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **The face functional is the canonical leading coefficient of the Taylor family**, and the
canonical coefficients at `λ` vanish above log degree `m − 1`. -/
theorem amplitudeCoeff_eq_spectral (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    familySpectralCoeff n h k β 0 (taylorFamily (n + 1) Fη) l (multCount (ratioExp h k) l - 1) =
      amplitudeCoeff h k l β η ∧
    ∀ q, multCount (ratioExp h k) l - 1 < q →
      familySpectralCoeff n h k β 0 (taylorFamily (n + 1) Fη) l q = 0 := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor' n h k hk β hβ one_pos hR hFη hη
  have hηabs : AbsSummable (taylorFamily (n + 1) Fη) := by
    have hr : (0 : ℝ) < (1 + R) / 2 := by linarith
    have hrR : (1 + R) / 2 < R := by linarith
    have h1r : (1 : ℝ) < (1 + R) / 2 := by linarith
    have := absSummableAt_polyRealCoeff hr hrR zero_le_one h1r hFη
    rw [polyRealCoeff_eq_taylorFamily hr hrR hFη] at this
    exact (absSummableAt_one_iff _).1 this
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β 0 (taylorFamily (n + 1) Fη) μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  obtain ⟨hzero, hlead⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC hηc hI hmin hatt
  refine ⟨by rw [← hCeq]; exact hlead, fun q hq => ?_⟩
  by_cases hqn : q ≤ n
  · rw [← hCeq]
    exact hzero q (Finset.mem_range.2 (Nat.lt_succ_of_le hqn)) hq
  · exact population_coeff_eq_zero_of_gt_degree n h k hk hβ hηabs hl0 (not_le.1 hqn)

/-- **Iterated coefficient transport for the analytic family.** -/
theorem population_coeff_add_two_mul_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ)
    (r j : ℕ) :
    familySpectralCoeff n (fun i => h i + 2 * r * k i) k β 0 cη (μ + r) j =
      iterTransport β μ r (familySpectralCoeff n h k β 0 cη μ) j := by
  induction r generalizing j with
  | zero => simp [iterTransport]
  | succ r ih =>
    have e : (fun i => h i + 2 * (r + 1) * k i) = fun i => (h i + 2 * r * k i) + 2 * k i := by
      funext i
      ring
    have hμr : 0 < μ + r := by positivity
    have hstep := population_coeff_add_two_k n (fun i => h i + 2 * r * k i) k hk hβ hη hμr j
    rw [e, show μ + ((r + 1 : ℕ) : ℝ) = (μ + r) + 1 by push_cast; ring, hstep]
    simp only [iterTransport, transportOp]
    rw [ih j, ih (j + 1)]

/-- The `r`-fold energy insertion is the weight shift `h ↦ h + 2rk`. -/
theorem origPhaseIntegral_energy_pow (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) :
    origPhaseIntegral n h k β N b ξ (fun u => (∏ i, u i ^ (2 * k i)) ^ r * η u) =
      origPhaseIntegral n (fun i => h i + 2 * r * k i) k β N b ξ η := by
  rw [← origPhaseIntegral_monomial_shift n h k β N b ξ η (fun i => 2 * r * k i)]
  congr 1
  funext u
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul]
  congr 1
  ring

/-- **Two-term data of the `r`-fold energy insertion at chart level.** -/
theorem population_twoTerm_chart_energy (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (r : ℕ) :
    Tendsto (fun N => Real.log N *
      (origPhaseIntegral n (fun i => h i + 2 * r * k i) k β N 1 (fun _ => 0) η /
        (N ^ (-(l + r)) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        amplitudeCoeff h k l β η * poch l r / β ^ r)) atTop
      (𝓝 ((poch l r * secondCoeff n h k β Fη l -
        ((multCount (ratioExp h k) l : ℝ) - 1) * amplitudeCoeff h k l β η * pochD l r) /
        β ^ r)) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hηabs : AbsSummable (taylorFamily (n + 1) Fη) := by
    have hr : (0 : ℝ) < (1 + R) / 2 := by linarith
    have hrR : (1 + R) / 2 < R := by linarith
    have h1r : (1 : ℝ) < (1 + R) / 2 := by linarith
    have := absSummableAt_polyRealCoeff hr hrR zero_le_one h1r hFη
    rw [polyRealCoeff_eq_taylorFamily hr hrR hFη] at this
    exact (absSummableAt_one_iff _).1 this
  have hminr : ∀ i, l + r ≤ ratioExp (fun i => h i + 2 * r * k i) k i := by
    intro i
    rw [ratioExp_add_two_mul_k h k hk r i]
    linarith [hmin i]
  have hattr : ∃ i, ratioExp (fun i => h i + 2 * r * k i) k i = l + r := by
    obtain ⟨i, hi⟩ := hatt
    exact ⟨i, by rw [ratioExp_add_two_mul_k h k hk r i, hi]⟩
  have hm := multCount_add_two_mul_k h k hk r l
  have hT := population_twoTerm_chart n (fun i => h i + 2 * r * k i) k hk β hβ hR hFη hη hηc hminr
    hattr
  rw [hm] at hT
  -- the shifted face functional and second coefficient
  obtain ⟨hlead, hvan⟩ := amplitudeCoeff_eq_spectral n h k hk β hβ hR hFη hη hηc hmin hatt
  obtain ⟨hleadr, -⟩ := amplitudeCoeff_eq_spectral n _ k hk β hβ hR hFη hη hηc hminr hattr
  rw [hm] at hleadr
  have hAr : amplitudeCoeff (fun i => h i + 2 * r * k i) k (l + r) β η =
      amplitudeCoeff h k l β η * poch l r / β ^ r := by
    rw [← hleadr, population_coeff_add_two_mul_k n h k hk hβ hηabs hl0 r,
      iterTransport_top hβ.ne' hvan r, hlead]
  have hBr : secondCoeff n (fun i => h i + 2 * r * k i) k β Fη (l + r) =
      (poch l r * secondCoeff n h k β Fη l -
        ((multCount (ratioExp h k) l : ℝ) - 1) * amplitudeCoeff h k l β η * pochD l r) / β ^ r := by
    unfold secondCoeff
    rw [hm]
    split_ifs with hms
    · obtain ⟨s, hs⟩ : ∃ s, multCount (ratioExp h k) l = s + 2 :=
        ⟨multCount (ratioExp h k) l - 2, by omega⟩
      rw [hs] at hlead hvan ⊢
      have e1 : s + 2 - 1 = s + 1 := by omega
      have e2 : s + 2 - 2 = s := by omega
      rw [e1] at hlead hvan
      rw [e2, population_coeff_add_two_mul_k n h k hk hβ hηabs hl0 r, ← hlead,
        iterTransport_next hβ.ne' (fun q hq => hvan q (by omega)) r]
      push_cast
      ring
    · have hm1 : multCount (ratioExp h k) l = 1 := by
        have := multCount_pos (ratioExp h k) l hatt
        omega
      rw [hm1]
      simp
  rw [hAr, hBr] at hT
  exact hT

/-- **All moments of `NK` at chart level with their first log corrections.** -/
theorem energy_moment_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hA : amplitudeCoeff h k l β η ≠ 0) (r : ℕ) :
    Tendsto (fun N => N ^ r *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ r * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η)) atTop (𝓝 (poch l r / β ^ r)) ∧
    Tendsto (fun N => Real.log N * (N ^ r *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ r * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) - poch l r / β ^ r)) atTop
      (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) * pochD l r / β ^ r)) := by
  have hZ := population_twoTerm_chart n h k hk β hβ hR hFη hη hηc hmin hatt
  have hZr := population_twoTerm_chart_energy n h k hk β hβ hR hFη hη hηc hmin hatt r
  have hq := quotient_second_order hA hZ hZr
  have hlim : (amplitudeCoeff h k l β η * ((poch l r * secondCoeff n h k β Fη l -
      ((multCount (ratioExp h k) l : ℝ) - 1) * amplitudeCoeff h k l β η * pochD l r) / β ^ r) -
      amplitudeCoeff h k l β η * poch l r / β ^ r * secondCoeff n h k β Fη l) /
      amplitudeCoeff h k l β η ^ 2 =
      -((multCount (ratioExp h k) l : ℝ) - 1) * pochD l r / β ^ r := by
    field_simp
    ring
  have hAA : amplitudeCoeff h k l β η * poch l r / β ^ r / amplitudeCoeff h k l β η =
      poch l r / β ^ r := by
    field_simp
  rw [hlim, hAA] at hq
  have hq' : Tendsto (fun N => Real.log N * (N ^ r *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ r * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) - poch l r / β ^ r)) atTop
      (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) * pochD l r / β ^ r)) := by
    refine hq.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      pow_ne_zero _ (Real.log_pos hN).ne'
    rw [origPhaseIntegral_energy_pow, show l + r - l = (r : ℝ) by ring, Real.rpow_natCast,
      mul_div_assoc, div_self hlog, mul_one]
    ring
  refine ⟨?_, hq'⟩
  have := hq'.mul tendsto_inv_log
  rw [mul_zero] at this
  have h0 : Tendsto (fun N => N ^ r *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ r * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) - poch l r / β ^ r) atTop (𝓝 0) := by
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul]
  have := h0.add_const (poch l r / β ^ r)
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun N => ?_)
  ring

/-- **Posterior variance of `NK` at chart level**: `V_N → λ/β²` and
`log N (V_N − λ/β²) → −(m−1)/β²`. -/
theorem energy_variance_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hA : amplitudeCoeff h k l β η ≠ 0) :
    Tendsto (fun N => N ^ 2 *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ 2 * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) -
      (N ^ 1 * (origPhaseIntegral n h k β N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ 1 * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η)) ^ 2) atTop (𝓝 (l / β ^ 2)) ∧
    Tendsto (fun N => Real.log N * (N ^ 2 *
      (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) ^ 2 * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) -
      (N ^ 1 * (origPhaseIntegral n h k β N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ 1 * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η)) ^ 2 - l / β ^ 2)) atTop
      (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) / β ^ 2)) := by
  obtain ⟨h1a, h1b⟩ := energy_moment_chart n h k hk β hβ hR hFη hη hηc hmin hatt hA 1
  obtain ⟨h2a, h2b⟩ := energy_moment_chart n h k hk β hβ hR hFη hη hηc hmin hatt hA 2
  simp only [poch, pochD, Nat.cast_zero, Nat.cast_one, add_zero, one_mul, zero_mul, zero_add,
    pow_one] at h1a h1b h2a h2b
  constructor
  · convert h2a.sub (h1a.pow 2) using 2 <;> ring
  · convert h2b.sub (h1b.mul (h1a.add_const (l / β))) using 2 <;> ring

end Grammar
