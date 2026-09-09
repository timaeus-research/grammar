/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EnergyCorrectionCore
import Grammar.CoefficientTransport
import Grammar.PopulationEnergy
import Grammar.PopulationDataBridge

/-!
# The first logarithmic correction to the energy expectation (Programme Q, N2, unit 316)

The paper's `ex:phi_equals_K`: `E_n[K] = λ/n − (m−1)/(n log n) + …`. At chart level, for a
continuous amplitude `η` with a holomorphic extension on a polydisc of radius `R > 1`, minimal ratio
`λ` with multiplicity `m`, and nonzero face functional `A`,
```
N log N · (𝒵_N[K∘π]/𝒵_N[1] − λ/(βN)) → −(m−1)/β                (energy_correction_chart)
```
for every `m ≥ 1` (the `m = 1` branch has zero correction). Route B (Astra #38): the two-term
expansions `𝒵 = N^{-λ}(A L^{m−1} + B L^{m−2} + o(L^{m−2}))` and
`𝒵_K = N^{-λ-1}(A_K L^{m−1} + B_K L^{m−2} + o(L^{m−2}))` come from the population Taylor tree with
the remainder at every log scale and the polynomial split at the top two degrees
(`twoTerm_split`); `A_K = λA/β`, `B_K = (λB − (m−1)A)/β` come from the coefficient transport
(unit 315); the quotient algebra is unit 316's core. Nothing is differentiated asymptotically. With
`β = 1` this is the paper's statement with the correction `−(m−1)/(n log n)`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Splitting a log-polynomial at its top two degrees**: if `c q = 0` for `q > r + 1` then
`(∑_{q≤n} c_q L^q)/L^r − c_{r+1} L − c_r → 0`. -/
theorem twoTerm_split (c : ℕ → ℝ) (n r : ℕ) (hr : r + 1 ≤ n) (hz : ∀ q, r + 1 < q → c q = 0) :
    Tendsto (fun N : ℝ => (∑ q ∈ Finset.range (n + 1), c q * Real.log N ^ q) / Real.log N ^ r -
      c (r + 1) * Real.log N - c r) atTop (𝓝 0) := by
  have hmem1 : r + 1 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hmem0 : r ∈ (Finset.range (n + 1)).erase (r + 1) :=
    Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  set S := ((Finset.range (n + 1)).erase (r + 1)).erase r with hS
  have htail : Tendsto (fun N : ℝ => (∑ q ∈ S, c q * Real.log N ^ q) / Real.log N ^ r) atTop
      (𝓝 0) := by
    simp_rw [Finset.sum_div]
    have h0 : Tendsto (fun N : ℝ => ∑ q ∈ S, c q * Real.log N ^ q / Real.log N ^ r) atTop
        (𝓝 (∑ q ∈ S, (0 : ℝ))) := by
      refine tendsto_finsetSum S fun q hq => ?_
      obtain ⟨hqr, hq'⟩ := Finset.mem_erase.1 hq
      obtain ⟨hqr1, -⟩ := Finset.mem_erase.1 hq'
      rcases lt_or_gt_of_ne hqr with hlt | hgt
      · have := (tendsto_log_pow_div_pow q r hlt).const_mul (c q)
        rw [mul_zero] at this
        refine this.congr' (Eventually.of_forall fun N => ?_)
        ring
      · have hq1 : r + 1 < q := by omega
        simp [hz q hq1]
    simpa using h0
  refine htail.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  rw [← Finset.sum_erase_add _ _ hmem1, ← Finset.sum_erase_add _ _ hmem0]
  field_simp
  ring

/-- **The first logarithmic correction to the energy expectation at chart level**:
`N log N (𝒵_N[K∘π]/𝒵_N[1] − λ/(βN)) → −(m−1)/β` when the face functional is nonzero. -/
theorem energy_correction_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hA : amplitudeCoeff h k l β η ≠ 0) :
    Tendsto (fun N => N * Real.log N * (origPhaseIntegral n h k β N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) * η u) / origPhaseIntegral n h k β N 1 (fun _ => 0) η -
        l / (β * N))) atTop (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) / β)) := by
  set m := multCount (ratioExp h k) l with hm
  have hm1 : 1 ≤ m := multCount_pos _ _ hatt
  have hmn : m - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- the two Taylor trees
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor' n h k hk β hβ one_pos hR hFη hη
  obtain ⟨CK, hCK, hIK⟩ :=
    population_TaylorTree_taylor' n (fun i => h i + 2 * k i) k hk β hβ one_pos hR hFη hη
  set cη := taylorFamily (n + 1) Fη with hcη
  have hηabs : AbsSummable cη := by
    have hr : (0 : ℝ) < (1 + R) / 2 := by linarith
    have hrR : (1 + R) / 2 < R := by linarith
    have h1r : (1 : ℝ) < (1 + R) / 2 := by linarith
    have := absSummableAt_polyRealCoeff hr hrR zero_le_one h1r hFη
    rw [polyRealCoeff_eq_taylorFamily hr hrR hFη] at this
    exact (absSummableAt_one_iff _).1 this
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β 0 cη μ q := fun μ q => by
    rw [hC.coeff_eq, scale_one, scale_one]
  have hCKeq : ∀ μ q, CK μ q = familySpectralCoeff n (fun i => h i + 2 * k i) k β 0 cη μ q :=
    fun μ q => by rw [hCK.coeff_eq, scale_one, scale_one]
  obtain ⟨hzero, hlead⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC hηc hI hmin hatt
  have hCz : ∀ q, m - 1 < q → C l q = 0 := by
    intro q hq
    by_cases hqn : q ≤ n
    · exact hzero q (Finset.mem_range.2 (Nat.lt_succ_of_le hqn)) hq
    · rw [hCeq]
      exact population_coeff_eq_zero_of_gt_degree n h k hk hβ hηabs hl0 (not_le.1 hqn)
  have htrans : ∀ q, CK (l + 1) q = (l * C l q - ((q : ℝ) + 1) * C l (q + 1)) / β := by
    intro q
    rw [hCKeq, hCeq, hCeq]
    exact population_coeff_add_two_k n h k hk hβ hηabs hl0 q
  have hCKz : ∀ q, m - 1 < q → CK (l + 1) q = 0 := by
    intro q hq
    rw [htrans, hCz q hq, hCz (q + 1) (by omega)]
    simp
  -- the shifted ordering data
  have hminK := hmin_add_two_k h k hk hmin
  have hattK := hatt_add_two_k h k hk hatt
  have hmK : multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = m := by
    rw [multCount_add_two_k h k hk l]
  -- the two integrals as family integrals
  set Z : ℝ → ℝ := fun N => familyPhaseIntegralBox n h k β N 1 0 cη with hZdef
  set ZK : ℝ → ℝ := fun N => familyPhaseIntegralBox n (fun i => h i + 2 * k i) k β N 1 0 cη
    with hZKdef
  have hfun : (fun N => N * Real.log N * (origPhaseIntegral n h k β N 1 (fun _ => 0)
      (fun u => (∏ i, u i ^ (2 * k i)) * η u) / origPhaseIntegral n h k β N 1 (fun _ => 0) η -
      l / (β * N))) = fun N => N * Real.log N * (ZK N / Z N - l / (β * N)) := by
    funext N
    rw [origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => 0) η (fun i => 2 * k i), ← hIK N,
      ← hI N]
  rw [hfun]
  -- leading coefficients
  set A := C l (m - 1) with hAdef
  have hA0 : A ≠ 0 := by
    intro h0
    apply hA
    rw [← hlead]
    exact h0
  have hAK : CK (l + 1) (m - 1) = l * A / β := by
    rw [htrans, Nat.sub_add_cancel hm1, hCz m (by omega)]
    simp only [mul_zero, sub_zero]
    rfl
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- `m = 1`: no logarithmic term
    have hm1' : m = 1 := by omega
    have hP : ∀ N, ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q = A := by
      intro N
      rw [Finset.sum_eq_single 0]
      · simp [hAdef, hm1']
      · intro q _ hq
        rw [hCz q (by omega), zero_mul]
      · intro h0
        exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0
    have hPK : ∀ N, ∑ q ∈ Finset.range (n + 1), CK (l + 1) q * Real.log N ^ q = l * A / β := by
      intro N
      rw [Finset.sum_eq_single 0]
      · rw [← hAK, hm1']
        simp
      · intro q _ hq
        rw [hCKz q (by omega), zero_mul]
      · intro h0
        exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0
    have hZ1 : Tendsto (fun N => Real.log N * (Z N / N ^ (-l) - A)) atTop (𝓝 0) := by
      have := population_remainder_tendsto_mul_pow n h k hk β hC hmin hatt 1
      simp only [hP, pow_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp
      ring
    have hZK1 : Tendsto (fun N => Real.log N * (ZK N / N ^ (-(l + 1)) - l * A / β)) atTop
        (𝓝 0) := by
      have := population_remainder_tendsto_mul_pow n (fun i => h i + 2 * k i) k hk β hCK hminK
        hattK 1
      simp only [hPK, pow_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hpow : N ^ (-(l + 1)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp
      ring
    have := oneTerm_energy_quotient hβ hA0 rfl hZ1 hZK1
    rw [hm1']
    simpa using this
  · -- `m ≥ 2`: two-term expansions
    set r := m - 2 with hr
    have hr1 : r + 1 = m - 1 := by omega
    have hrn : r + 1 ≤ n := by omega
    set B := C l r with hBdef
    have hzC : ∀ q, r + 1 < q → C l q = 0 := fun q hq => hCz q (by omega)
    have hzCK : ∀ q, r + 1 < q → CK (l + 1) q = 0 := fun q hq => hCKz q (by omega)
    have hBK : CK (l + 1) r = (l * B - ((r : ℝ) + 1) * A) / β := by
      rw [htrans, hr1]
    -- Z two-term
    have hZ2 : Tendsto (fun N => Z N / (N ^ (-l) * Real.log N ^ r) - A * Real.log N) atTop
        (𝓝 B) := by
      have h1 := population_remainder_tendsto_pow n h k hk β hC hmin hatt r
      have h2 := twoTerm_split (fun q => C l q) n r hrn hzC
      rw [hr1] at h2
      have h3 := (h1.add h2).add_const B
      simp only [zero_add, zero_add] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp
      ring
    have hZK2 : Tendsto (fun N => ZK N / (N ^ (-(l + 1)) * Real.log N ^ r) -
        (l * A / β) * Real.log N) atTop (𝓝 ((l * B - ((r : ℝ) + 1) * A) / β)) := by
      have h1 := population_remainder_tendsto_pow n (fun i => h i + 2 * k i) k hk β hCK hminK
        hattK r
      have h2 := twoTerm_split (fun q => CK (l + 1) q) n r hrn hzCK
      rw [hr1, hAK, hBK] at h2
      have h3 := (h1.add h2).add_const ((l * B - ((r : ℝ) + 1) * A) / β)
      simp only [zero_add] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-(l + 1)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp
      ring
    have := twoTerm_energy_quotient hβ hA0 rfl rfl hZ2 hZK2
    have hcast : -((r : ℝ) + 1) / β = -((m : ℝ) - 1) / β := by
      rw [hr, Nat.cast_sub hm2]
      push_cast
      ring
    rwa [hcast] at this

end Grammar
