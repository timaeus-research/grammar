/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialPhaseStability
import Grammar.ConstantPhaseCorrection

/-!
# Two-term asymptotics for an arbitrary analytic spatial phase (unit 360; Astra #45 unit 1)

For coefficient-family data `cξ, cη` (absolutely summable on the unit box) representing a
continuous phase `ξ` and amplitude `η`, the Taylor tree gives the full expansion of
`𝒵_N[η; ξ]`; isolating the exponent `λ` and the log degrees `m − 1`, `m − 2` yields

`𝒵_N[η; ξ]/(N^{-λ} L^{m-1}) = F(ξ, η) + B(ξ, η)/L + o(1/L)`.

The leading coefficient is identified **by uniqueness** against the continuous-phase limit
`spatialPhase_tendsto` (Headline LXXII): `A_{λ,m-1}(cξ, cη) = spatialFace h k l β ξ η`
(`spatial_leadingCoeff`), and the coefficients at `λ` vanish above log degree `m − 1`
(all `j`, using that every family coefficient vanishes above the ambient degree `n`,
`coeff_eq_zero_of_gt_degree_of_conclusion`).  The second coefficient is the family spectral
coefficient `B(ξ, η) = A_{λ,m-2}(cξ, cη)` (`spatialSecondCoeff`); the two-term statement is
`spatialPhase_twoTerm_chart`, and `spatialPhase_twoTerm_analytic` is the version for phase and
amplitude data with holomorphic extensions to a common polydisc of radius `> 1`.
For `m = 1` the theorem says `L (𝒵_N/N^{-λ} − F) → 0`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

open CoeffFamily

/-- Every Taylor-tree coefficient vanishes above the ambient log degree `n`. -/
theorem coeff_eq_zero_of_gt_degree_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ} (hC : TaylorTreeConclusion n h k β 1 cξ cη C)
    (μ : ℝ) {j : ℕ} (hj : n < j) : C μ j = 0 := by
  rw [hC.series]
  unfold familyCoeffSeries familyCoeffTerm kernelFunctional
  simp [kernelS_eq_zero_of_lt n h k β _ _ μ hj]

/-- **Leading coefficient by uniqueness**: for any coefficient system satisfying the Taylor-tree
conclusion whose family integral is `𝒵_N[η; ξ]` with `ξ, η` continuous, `C(λ, m−1) = F(ξ, η)` and
`C(λ, j) = 0` for `m − 1 < j`. -/
theorem spatial_leadingCoeff_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη = origPhaseIntegral n h k β N 1 ξ η)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j, multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = spatialFace h k l β ξ η := by
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hA := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt ξ η hξc hηc
  have hR := population_remainder_tendsto n h k hk β hC hmin hatt
  have hP : Tendsto (fun N => (∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j) /
      Real.log N ^ (m - 1)) atTop (𝓝 (spatialFace h k l β ξ η)) := by
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
  refine ⟨fun j hj => ?_, hlead hm_le⟩
  by_cases hjn : j ≤ n
  · exact hzero j (Finset.mem_range.2 (Nat.lt_succ_of_le hjn)) hj
  · exact coeff_eq_zero_of_gt_degree_of_conclusion n h k β hC l (not_le.1 hjn)

/-- **The leading family coefficient of continuous phase data is the face functional**:
`A_{λ,m−1}(cξ, cη) = F(ξ, η)`, and `A_{λ,j}(cξ, cη) = 0` for `j > m − 1`. -/
theorem spatial_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j, multCount (ratioExp h k) l - 1 < j → familySpectralCoeff n h k β cξ cη l j = 0) ∧
    familySpectralCoeff n h k β cξ cη l (multCount (ratioExp h k) l - 1) =
      spatialFace h k l β ξ η := by
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    ((absSummableAt_one_iff _).2 hξ) ((absSummableAt_one_iff _).2 hη)
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β cξ cη μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  have hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη = origPhaseIntegral n h k β N 1 ξ η :=
    fun N => familyPhaseIntegralBox_eq_orig n h k β N 1 hevξ hevη
  obtain ⟨hzero, hlead⟩ :=
    spatial_leadingCoeff_of_conclusion n h k hk β hβ hC hξc hηc hI hmin hatt
  exact ⟨fun j hj => by rw [← hCeq]; exact hzero j hj, by rw [← hCeq]; exact hlead⟩

/-- The second spatial coefficient `B(ξ, η) = A_{λ,m−2}(cξ, cη)` (zero when `m = 1`). -/
noncomputable def spatialSecondCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (l : ℝ) : ℝ :=
  if 2 ≤ multCount (ratioExp h k) l then
    familySpectralCoeff n h k β cξ cη l (multCount (ratioExp h k) l - 2)
  else 0

theorem spatialSecondCoeff_const (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (a l : ℝ) :
    spatialSecondCoeff n h k β (constFamily a) cη l = constPhaseSecondCoeff n h k β cη a l := rfl

/-- **Two-term asymptotics for an arbitrary spatial phase**:
`L (𝒵_N[η; ξ]/(N^{-λ} L^{m-1}) − F(ξ, η)) → B(ξ, η)`, uniformly in the multiplicity
(for `m = 1` the limit is `0`). -/
theorem spatialPhase_twoTerm_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        spatialFace h k l β ξ η))
      atTop (𝓝 (spatialSecondCoeff n h k β cξ cη l)) := by
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    ((absSummableAt_one_iff _).2 hξ) ((absSummableAt_one_iff _).2 hη)
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β cξ cη μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  have hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη = origPhaseIntegral n h k β N 1 ξ η :=
    fun N => familyPhaseIntegralBox_eq_orig n h k β N 1 hevξ hevη
  obtain ⟨hzero, hlead⟩ :=
    spatial_leadingCoeff_of_conclusion n h k hk β hβ hC hξc hηc hI hmin hatt
  have hcut := cutoffExpansion_of_conclusion n h k β hC
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨i₀, hi₀⟩ := hatt
  obtain ⟨a₀, -, ha₀⟩ := ratio_mem_lattice k hk i₀ (h i₀)
  have hla : l = (a₀ : ℝ) / latticeQ k := by rw [← hi₀]; exact ha₀
  have hpred : ∀ m' : ℕ, m' < a₀ → ∀ j, C ((m' : ℝ) / latticeQ k) j = 0 := by
    intro m' hm' j
    apply hC.vanish
    intro hcand
    have hle := le_of_candidateExp h k hk hmin hcand
    rw [hla, div_le_div_iff_of_pos_right hQ'] at hle
    have : a₀ ≤ m' := by exact_mod_cast hle
    omega
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ ⟨i₀, hi₀⟩
  have hmn : multCount (ratioExp h k) l ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  rcases Nat.lt_or_ge (multCount (ratioExp h k) l) 2 with hm | hm
  · have hm1' : multCount (ratioExp h k) l = 1 := by omega
    have hz0 : ∀ q, 0 < q → C ((a₀ : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hzero q (by omega)
    have h1 := oneTerm_of_isolated hQ hcut hpred hz0
    rw [← hla] at h1
    unfold spatialSecondCoeff
    rw [if_neg (by omega)]
    rw [hm1', Nat.sub_self] at hlead ⊢
    refine h1.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [hI N, hlead, pow_zero, mul_one]
  · obtain ⟨r, hr⟩ : ∃ r, multCount (ratioExp h k) l = r + 2 :=
      ⟨multCount (ratioExp h k) l - 2, by omega⟩
    have hr1 : r + 1 ≤ n := by omega
    have hz : ∀ q, r + 1 < q → C ((a₀ : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hzero q (by omega)
    have h2 := twoTerm_of_isolated hQ hcut hpred hr1 hz
    rw [← hla] at h2
    have e1 : r + 2 - 1 = r + 1 := by omega
    have e2 : r + 2 - 2 = r := by omega
    unfold spatialSecondCoeff
    rw [hr, if_pos (by omega), e1, e2, ← hCeq]
    rw [hr, e1] at hlead
    rw [← hlead]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hlogr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlog
    rw [hI N]
    field_simp
    ring

/-- **Two-term asymptotics for holomorphic phase and amplitude data**: if `ξ, η` are continuous
and agree on the unit box with the real parts of holomorphic `Fξ, Fη` on a polydisc of radius
`R > 1`, then `L (𝒵_N[η; ξ]/(N^{-λ} L^{m-1}) − F(ξ, η)) → B(ξ, η)`, with `B` the family
spectral coefficient of the Cauchy coefficient families at any radius `r ∈ (1, R)`. -/
theorem spatialPhase_twoTerm_analytic (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {r R : ℝ} (hr : 1 < r) (hrR : r < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hξc : Continuous ξ) (hηc : Continuous η) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        spatialFace h k l β ξ η))
      atTop (𝓝 (spatialSecondCoeff n h k β (polyRealCoeff (n + 1) r Fξ)
        (polyRealCoeff (n + 1) r Fη) l)) := by
  have hr0 : 0 < r := by linarith
  refine spatialPhase_twoTerm_chart n h k hk hβ
    ((absSummableAt_one_iff _).1 (absSummableAt_polyRealCoeff hr0 hrR zero_le_one hr hFξ))
    ((absSummableAt_one_iff _).1 (absSummableAt_polyRealCoeff hr0 hrR zero_le_one hr hFη))
    hξc hηc (fun u hu => ?_) (fun u hu => ?_) hmin hatt
  · rw [evalF_polyRealCoeff hr0 hrR hr hFξ hu, hξ u hu]
  · rw [evalF_polyRealCoeff hr0 hrR hr hFη hu, hη u hu]

end Grammar
