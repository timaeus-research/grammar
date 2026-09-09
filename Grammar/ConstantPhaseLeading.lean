/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseDerivative
import Grammar.HeadlinePhase
import Grammar.PopulationLeadingCoeff
import Grammar.PopulationShift
import Grammar.PopulationDataBridge
import Grammar.PopulationEnergy

/-!
# Constant-phase leading coefficient and the constant-phase energy ratio (unit 336)

For a constant fluctuation `ξ ≡ a` the chart integral
`𝒵_N[η; a] = ∫ η u^h e^{−βN u^{2k} + β√N u^k a}` has, by Headline XIX in the variable `√N`, the
leading term `A(a) N^{-λ}(log N)^{m−1}` with
`A(a) = 2^{-(m−1)}/((m−1)! ∏_J k_i) ∫ η(P_J u) J_{2λ}(a) ∏_{i∉J} u_i^{h_i−2k_iλ} du` (`phaseFace`),
and the polynomial-uniqueness argument of Programme P identifies it with the canonical coefficient
`C(λ, m−1; a)` of the constant-phase Taylor tree and kills the coefficients above log degree `m−1`
(`constPhase_leadingCoeff_of_conclusion`, `constPhase_leadingCoeff`). Combined with the
constant-phase transport and the phase derivative:
```
N 𝒵_N[K∘π η; a]/𝒵_N[η; a] → λ/β + (a/(2β)) ∂_a A(a)/A(a)        (A(a) ≠ 0),
```
the leading constant-phase energy ratio (`constPhase_energy_ratio_chart`): the fluctuation shifts
the leading expectation of `nK` by `(a/2β) ∂_a log A(a)`. Not claimed: the next-log correction with
phase, or anything for spatially varying `ξ`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- Evaluation of the constant family. -/
theorem evalF_constFamily {d : ℕ} (a : ℝ) (u : Fin d → ℝ) :
    evalF (constFamily a : CoeffFamily d) u = a := by
  unfold evalF constFamily
  rw [tsum_eq_single 0]
  · simp [MonoRep.mono]
  · intro γ hγ
    simp [hγ]

/-- The constant-phase face functional: the Headline XIX limit in the variable `√N`, rescaled to
the variable `N` (the factor `2^{-(m−1)}` from `log √N = (log N)/2`). -/
noncomputable def phaseFace {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β a : ℝ)
    (η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
    (∫ u in unitBox (d + 1),
      (η (faceProj h k l u) * phaseMoment β (2 * l) a) * residualWeight h k l u) /
    2 ^ (multCount (ratioExp h k) l - 1)

/-- The constant-phase chart integral as the Headline XIX integrand in the variable `√N`. -/
theorem origPhaseIntegral_constPhase_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ}
    (hN : 0 ≤ N) (a : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 (fun _ => a) η =
      ∫ u in unitBox (n + 1), η u * ((∏ i, u i ^ h i) *
        Real.exp (-(β * Real.sqrt N ^ 2 * ∏ i, u i ^ (2 * k i)) +
          β * (Real.sqrt N * ∏ i, u i ^ k i) * a)) := by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset, Real.sq_sqrt hN]
  congr 1
  funext u
  ring

/-- **Constant-phase leading term in the variable `N`**: Headline XIX composed with `N ↦ √N`. -/
theorem constPhase_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (a : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) :
    Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => a) η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (phaseFace h k l β a η)) := by
  have hT := headline_phase_leading n h k hk l β hl hβ hmin hatt (fun _ => a) η continuous_const hηc
  have hsq : Tendsto (fun N : ℝ => Real.sqrt N) atTop atTop := by
    have := tendsto_rpow_atTop (y := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr fun N => ?_
    rw [Real.sqrt_eq_rpow]
  have hc := (hT.comp hsq).div_const (2 ^ (multCount (ratioExp h k) l - 1))
  unfold phaseFace
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  have hpow : Real.sqrt N ^ (-(2 * l)) = N ^ (-l) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  show (∫ u in unitBox (n + 1), η u * ((∏ i, u i ^ h i) *
      Real.exp (-(β * Real.sqrt N ^ 2 * ∏ i, u i ^ (2 * k i)) +
        β * (Real.sqrt N * ∏ i, u i ^ k i) * a))) /
      (Real.sqrt N ^ (-(2 * l)) * Real.log (Real.sqrt N) ^ (multCount (ratioExp h k) l - 1)) /
      2 ^ (multCount (ratioExp h k) l - 1) =
    origPhaseIntegral n h k β N 1 (fun _ => a) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))
  rw [← origPhaseIntegral_constPhase_eq n h k β hN0.le a η, hlog, hpow, div_pow]
  have hpowN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlogN : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  have h2 : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero hpowN (div_ne_zero hlogN h2)) h2)
    (mul_ne_zero hpowN hlogN)]
  rw [mul_assoc (N ^ (-l)), div_mul_cancel₀ _ h2]

/-- **Constant-phase leading coefficient of a Taylor-tree conclusion**: the coefficients at `λ`
vanish above log degree `m − 1` and `C(λ, m−1) = phaseFace`. -/
theorem constPhase_leadingCoeff_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {η : (Fin (n + 1) → ℝ) → ℝ}
    (hηc : Continuous η) (a : ℝ)
    (hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη =
      origPhaseIntegral n h k β N 1 (fun _ => a) η)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = phaseFace h k l β a η := by
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hA := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt a η hηc
  have hR := population_remainder_tendsto n h k hk β hC hmin hatt
  have hP : Tendsto (fun N => (∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j) /
      Real.log N ^ (m - 1)) atTop (𝓝 (phaseFace h k l β a η)) := by
    have hsub := hA.sub hR
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    rw [← hI N, ← sub_div, sub_sub_cancel, mul_div_mul_left _ _ hpow]
  have hm_le : m - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  obtain ⟨hzero, hlead, -⟩ := coeff_eq_of_tendsto_div_pow (a := fun j => C l j)
    Real.tendsto_log_atTop hP
  exact ⟨hzero, hlead hm_le⟩

/-- Constant-phase coefficients vanish above the ambient log degree `n`. -/
theorem constPhase_coeff_eq_zero_of_gt_degree (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) {j : ℕ} (hj : n < j) :
    familySpectralCoeff n h k β (constFamily a) cη μ j = 0 := by
  rw [familySpectralCoeff_constPhase n h k hk hβ a hη hμ j]
  unfold kernelFunctional
  simp [kernelS_eq_zero_of_lt n h k β a 0 μ hj]

/-- **The canonical constant-phase leading coefficient is the phase face functional**, and the
coefficients at `λ` vanish above log degree `m − 1`, for an absolutely summable amplitude family
representing a continuous `η` on the unit box. -/
theorem constPhase_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j, multCount (ratioExp h k) l - 1 < j →
      familySpectralCoeff n h k β (constFamily a) cη l j = 0) ∧
    familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) =
      phaseFace h k l β a η := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    ((absSummableAt_one_iff _).2 (absSummable_constFamily a)) ((absSummableAt_one_iff _).2 hη)
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β (constFamily a) cη μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  have hI : ∀ N, familyPhaseIntegralBox n h k β N 1 (constFamily a) cη =
      origPhaseIntegral n h k β N 1 (fun _ => a) η := fun N =>
    familyPhaseIntegralBox_eq_orig n h k β N 1 (fun u _ => evalF_constFamily a u) hev
  obtain ⟨hzero, hlead⟩ := constPhase_leadingCoeff_of_conclusion n h k hk β hβ hC hηc a hI hmin hatt
  refine ⟨fun j hj => ?_, by rw [← hCeq]; exact hlead⟩
  by_cases hjn : j ≤ n
  · rw [← hCeq]
    exact hzero j (Finset.mem_range.2 (Nat.lt_succ_of_le hjn)) hj
  · exact constPhase_coeff_eq_zero_of_gt_degree n h k hk hβ a hη hl0 (not_le.1 hjn)

/-- **The leading constant-phase energy ratio**: with `A(a) = C(λ, m−1; a) ≠ 0`,
`N 𝒵_N[K∘π η; a]/𝒵_N[η; a] → λ/β + (a/(2β)) ∂_a A(a)/A(a)`. -/
theorem constPhase_energy_ratio_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => N * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) * η u) / origPhaseIntegral n h k β N 1 (fun _ => a) η))
      atTop (𝓝 (l / β + a / (2 * β) *
        deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
          (multCount (ratioExp h k) l - 1)) a /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ hatt
  obtain ⟨hzero, hlead⟩ := constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt
  -- the denominator and numerator leading terms
  have hZ := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt a η hηc
  have hminK := hmin_add_two_k h k hk hmin
  have hattK := hatt_add_two_k h k hk hatt
  have hmK : multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l :=
    multCount_add_two_k h k hk l
  have hZK := constPhase_tendsto n (fun i => h i + 2 * k i) k hk (l + 1) β (by linarith) hβ hminK
    hattK a η hηc
  rw [hmK] at hZK
  obtain ⟨-, hleadK⟩ := constPhase_leadingCoeff n _ k hk hβ a hη hηc hev hminK hattK
  rw [hmK] at hleadK
  -- the transported leading coefficient
  have htrans := population_coeff_add_two_k_phase_deriv n h k hk hβ a hη hl0
    (multCount (ratioExp h k) l - 1)
  have hCm : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1 + 1)
      = 0 := hzero _ (by omega)
  rw [hCm] at htrans
  -- the ratio
  have hq := hZK.div hZ (by rw [hlead] at hA; exact hA)
  rw [← hleadK, htrans, ← hlead] at hq
  refine (hq.congr' ?_).trans ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    simp only [Pi.div_apply]
    have hN0 : 0 < N := by linarith
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      pow_ne_zero _ (Real.log_pos hN).ne'
    have hsplit : N ^ (-(l + 1)) = N ^ (-l) / N := by
      rw [show -(l + 1) = -l + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one, div_eq_mul_inv]
    rw [origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => a) η (fun i => 2 * k i), hsplit]
    field_simp
  · rw [show l / β + a / (2 * β) * deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
        (multCount (ratioExp h k) l - 1)) a /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) =
        (l * familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) -
          ((multCount (ratioExp h k) l - 1 : ℕ) + 1 : ℝ) * 0 +
          a / 2 * deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
            (multCount (ratioExp h k) l - 1)) a) / β /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) by
      field_simp
      ring]

end Grammar
