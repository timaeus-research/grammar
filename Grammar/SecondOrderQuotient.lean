/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.IsolatedRemainder

/-!
# The second-order expectation quotient for a general observable (unit 322)

Programme P gave the leading quotient
`𝒵_N[φ]/𝒵_N ~ (A'/A) N^{-(λ'−λ)} (log N)^{(m'−1)−(m−1)}`.
Here the next term. Abstractly (`quotient_second_order`): if `log N · (Z/(N^{-λ} L^{s}) − A) → B`
and `log N · (Z'/(N^{-λ'} L^{s'}) − A') → B'` with `A ≠ 0`, then
```
log N · ( Z'/Z · N^{λ'−λ} L^{s}/L^{s'} − A'/A ) → (A B' − A' B)/A²,
```
i.e. `Z'/Z = (A'/A) N^{-(λ'−λ)} L^{s'−s} (1 + (B'/A' − B/A)/log N + o(1/log N))` when also
`A' ≠ 0`. The two-term data of a population chart integral with analytic amplitude are supplied by
the isolated remainders of `IsolatedRemainder` (`population_twoTerm_chart`): `s = m − 1`, `A` the
face functional,
`B` the canonical coefficient of `N^{-λ}(log N)^{m−2}` (`secondCoeff`; zero when `m = 1`). The
paper-facing statement `population_second_order_chart` takes two analytic amplitude data on the
same chart (weights `h`, `h'`; for an observable `φ∘π = u^l ψ`, `h' = h + l`, `η' = ψ`) and gives
the second-order expansion of `𝒵_N[η']/𝒵_N[η]` at chart level, for all multiplicities. The `1/log N`
correction is absent when `m = m' = 1` (the limit is `0`; the next correction is then a power of
`N`). Not claimed: chart assembly for this quotient; anything when `A = 0`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Second-order quotient of two two-term asymptotics.** -/
theorem quotient_second_order {Z Z' : ℝ → ℝ} {A B A' B' l l' : ℝ} {s s' : ℕ} (hA : A ≠ 0)
    (hZ : Tendsto (fun N => Real.log N * (Z N / (N ^ (-l) * Real.log N ^ s) - A)) atTop (𝓝 B))
    (hZ' : Tendsto (fun N => Real.log N * (Z' N / (N ^ (-l') * Real.log N ^ s') - A')) atTop
      (𝓝 B')) :
    Tendsto (fun N => Real.log N * (Z' N / Z N * (N ^ (l' - l) * Real.log N ^ s /
      Real.log N ^ s') - A' / A)) atTop (𝓝 ((A * B' - A' * B) / A ^ 2)) := by
  have hε : Tendsto (fun N => Z N / (N ^ (-l) * Real.log N ^ s) - A) atTop (𝓝 0) := by
    have := hZ.mul tendsto_inv_log
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul]
  have hAε : Tendsto (fun N => A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)) atTop (𝓝 A) := by
    have := (tendsto_const_nhds (x := A)).add hε
    rwa [add_zero] at this
  have hev : ∀ᶠ N in atTop, A + (Z N / (N ^ (-l) * Real.log N ^ s) - A) ≠ 0 :=
    hAε.eventually (isOpen_ne.mem_nhds hA)
  have hlim : Tendsto (fun N => (A * (Real.log N * (Z' N / (N ^ (-l') * Real.log N ^ s') - A')) -
      A' * (Real.log N * (Z N / (N ^ (-l) * Real.log N ^ s) - A))) /
      (A * (A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)))) atTop
      (𝓝 ((A * B' - A' * B) / (A * A))) :=
    ((tendsto_const_nhds.mul hZ').sub (tendsto_const_nhds.mul hZ)).div
      (tendsto_const_nhds.mul hAε) (mul_ne_zero hA hA)
  rw [← sq] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpow' : N ^ (-l') ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlogs : Real.log N ^ s ≠ 0 := pow_ne_zero _ hlog
  have hlogs' : Real.log N ^ s' ≠ 0 := pow_ne_zero _ hlog
  have hN' : A + (Z N / (N ^ (-l) * Real.log N ^ s) - A) ≠ 0 := hN
  have hZne : Z N ≠ 0 := by
    intro h0
    apply hN'
    rw [h0, zero_div]
    ring
  have hrpow : N ^ (l' - l) = N ^ (-l) / N ^ (-l') := by
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  rw [hrpow]
  have hZeq : Z N = N ^ (-l) * Real.log N ^ s * (A + (Z N / (N ^ (-l) * Real.log N ^ s) - A)) := by
    field_simp
    ring
  have hZ'eq : Z' N = N ^ (-l') * Real.log N ^ s' *
      (A' + (Z' N / (N ^ (-l') * Real.log N ^ s') - A')) := by
    field_simp
    ring
  generalize hε1 : Z N / (N ^ (-l) * Real.log N ^ s) - A = ε at hZeq hN' ⊢
  generalize hε2 : Z' N / (N ^ (-l') * Real.log N ^ s') - A' = ε' at hZ'eq ⊢
  rw [hZeq, hZ'eq]
  field_simp
  ring

/-- The canonical coefficient of `N^{-λ}(log N)^{m−2}` in the population expansion of an analytic
amplitude (`0` when the multiplicity `m` is one). -/
noncomputable def secondCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (Fη : (Fin (n + 1) → ℂ) → ℂ) (l : ℝ) : ℝ :=
  if 2 ≤ multCount (ratioExp h k) l then
    familySpectralCoeff n h k β 0 (taylorFamily (n + 1) Fη) l (multCount (ratioExp h k) l - 2)
  else 0

/-- **Two-term data of a population chart integral**, uniformly in the multiplicity:
`log N · (𝒵_N/(N^{-λ}(log N)^{m−1}) − A) → B` with `A` the face functional and `B = secondCoeff`. -/
theorem population_twoTerm_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 (fun _ => 0) η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) - amplitudeCoeff h k l β η))
      atTop (𝓝 (secondCoeff n h k β Fη l)) := by
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
  have hCz : ∀ q, multCount (ratioExp h k) l - 1 < q → C l q = 0 := by
    intro q hq
    by_cases hqn : q ≤ n
    · exact hzero q (Finset.mem_range.2 (Nat.lt_succ_of_le hqn)) hq
    · rw [hCeq]
      exact population_coeff_eq_zero_of_gt_degree n h k hk hβ hηabs hl0 (not_le.1 hqn)
  have hcut := cutoffExpansion_of_conclusion n h k β hC
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨i₀, hi₀⟩ := hatt
  obtain ⟨a, -, ha⟩ := ratio_mem_lattice k hk i₀ (h i₀)
  have hla : l = (a : ℝ) / latticeQ k := by rw [← hi₀]; exact ha
  have hpred : ∀ m' : ℕ, m' < a → ∀ j, C ((m' : ℝ) / latticeQ k) j = 0 := by
    intro m' hm' j
    apply hC.vanish
    intro hcand
    have hle := le_of_candidateExp h k hk hmin hcand
    rw [hla, div_le_div_iff_of_pos_right hQ'] at hle
    have : a ≤ m' := by exact_mod_cast hle
    omega
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ ⟨i₀, hi₀⟩
  have hmn : multCount (ratioExp h k) l ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  rcases Nat.lt_or_ge (multCount (ratioExp h k) l) 2 with hm | hm
  · -- multiplicity one
    have hm1' : multCount (ratioExp h k) l = 1 := by omega
    have hz0 : ∀ q, 0 < q → C ((a : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hCz q (by omega)
    have h1 := oneTerm_of_isolated hQ hcut hpred hz0
    rw [← hla] at h1
    have hlead0 : C l 0 = amplitudeCoeff h k l β η := by rw [← hlead, hm1']
    unfold secondCoeff
    rw [hm1', if_neg (by omega)]
    refine h1.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [hlead0, hI N, Nat.sub_self, pow_zero, mul_one]
  · -- multiplicity at least two
    obtain ⟨r, hr⟩ : ∃ r, multCount (ratioExp h k) l = r + 2 :=
      ⟨multCount (ratioExp h k) l - 2, by omega⟩
    have hr1 : r + 1 ≤ n := by omega
    have hz : ∀ q, r + 1 < q → C ((a : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hCz q (by omega)
    have h2 := twoTerm_of_isolated hQ hcut hpred hr1 hz
    rw [← hla] at h2
    have e1 : r + 2 - 1 = r + 1 := by omega
    have e2 : r + 2 - 2 = r := by omega
    have hleadr : C l (r + 1) = amplitudeCoeff h k l β η := by
      rw [← hlead, hr, e1]
    unfold secondCoeff
    rw [hr, if_pos (by omega), e1, e2, ← hCeq]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hlogr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlog
    rw [hleadr, hI N]
    field_simp
    ring

/-- **Second-order expectation quotient at chart level** for two analytic amplitude data on the same
chart (weights `h`, `h'`; observable `φ∘π = u^{l}ψ` means `h' = h + l`, `η' = ψ`): with
`A = A(h,η) ≠ 0`, `A' = A(h',η')`, `B`, `B'` the second coefficients,
`log N · ( 𝒵_N[η']/𝒵_N[η] · N^{λ'−λ} (log N)^{m−1}/(log N)^{m'−1} − A'/A ) → (A B' − A' B)/A²`. -/
theorem population_second_order_chart (n : ℕ) (h h' k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη Fη' : (Fin (n + 1) → ℂ) → ℂ}
    {η η' : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u) (hηc : Continuous η)
    (hFη' : DifferentiableOn ℂ Fη' (openPolydisc (n + 1) R))
    (hη' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη' fun i => (u i : ℂ)).re = η' u)
    (hηc' : Continuous η') {l l' : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hmin' : ∀ i, l' ≤ ratioExp h' k i)
    (hatt' : ∃ i, ratioExp h' k i = l') (hA : amplitudeCoeff h k l β η ≠ 0) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h' k β N 1 (fun _ => 0) η' /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η *
        (N ^ (l' - l) * Real.log N ^ (multCount (ratioExp h k) l - 1) /
          Real.log N ^ (multCount (ratioExp h' k) l' - 1)) -
        amplitudeCoeff h' k l' β η' / amplitudeCoeff h k l β η)) atTop
      (𝓝 ((amplitudeCoeff h k l β η * secondCoeff n h' k β Fη' l' -
        amplitudeCoeff h' k l' β η' * secondCoeff n h k β Fη l) / amplitudeCoeff h k l β η ^ 2)) :=
  quotient_second_order hA (population_twoTerm_chart n h k hk β hβ hR hFη hη hηc hmin hatt)
    (population_twoTerm_chart n h' k hk β hβ hR hFη' hη' hηc' hmin' hatt')

end Grammar
