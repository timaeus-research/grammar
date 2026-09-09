/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TransverseSensitivity

/-!
# The next-log posterior energy correction with spatial phase (unit 370; Astra #45 unit 3)

The insertion of `NK = N u^{2k}` is the weight shift `h ↦ h + 2k`, `λ ↦ λ + 1`, which preserves
the face and the multiplicity (`multCount_add_two_mul_k`).  Applying the two-term theorem
(Headline LXXVII) to both the numerator and the denominator and dividing (`quotient_second_order`)
gives, for every coefficient-family phase and amplitude data with nonzero face coefficient,
```
L (E_{Q_N^ξ}[NK] − μ_ξ) → c₂(ξ) = (A₀ B₁ − A₁ B₀)/A₀²,
```
`A₀ = F(ξ,η)`, `A₁ = F_{h+2k}(ξ,η)`, `μ_ξ = A₁/A₀` (the leading posterior mean of Headline LXXV),
`B₀ = B(ξ,η)`, `B₁ = B_{h+2k}(ξ,η)` (`spatialEnergyMean_twoTerm`), with `B₀, B₁` explicit
finite-part face integrals for `m ≥ 2` (`spatialEnergyCorrection`,
`spatialEnergyMean_twoTerm_explicit`).
**Sanity check** (Astra #45): at zero phase the correction is the Programme Q value `−(m−1)/β`
and the leading mean is `λ/β`, both recovered by uniqueness of limits against
`energy_correction_chart` (`spatialEnergyCorrection_zero_phase`, `spatialEnergyMean_zero_phase`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

/-- The posterior energy mean `E_{Q_N^ξ}[NK] = N 𝒵_N[K η; ξ]/𝒵_N[η; ξ]`. -/
noncomputable def spatialEnergyMean (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  origPhaseIntegral n h k β N 1 ξ (fun u => (N * ∏ i, u i ^ (2 * k i)) * η u) /
    origPhaseIntegral n h k β N 1 ξ η

theorem shift_fun_eq (h k : Fin d → ℕ) :
    (fun i => h i + 2 * 1 * k i) = fun i => h i + 2 * k i := by
  funext i
  ring

theorem hmin_shift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) : ∀ i, l + 1 ≤ ratioExp (fun i => h i + 2 * k i) k i := by
  have := hmin_add_two_mul_k h k hk 1 hmin
  rwa [shift_fun_eq, Nat.cast_one] at this

theorem hatt_shift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) : ∃ i, ratioExp (fun i => h i + 2 * k i) k i = l + 1 := by
  have := hatt_add_two_mul_k h k hk 1 hatt
  rwa [shift_fun_eq, Nat.cast_one] at this

theorem multCount_shift {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l := by
  have := multCount_add_two_mul_k h k hk 1 l
  rwa [shift_fun_eq, Nat.cast_one] at this

theorem spatialEnergyMean_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    spatialEnergyMean n h k β N ξ η =
      N * origPhaseIntegral n (fun i => h i + 2 * k i) k β N 1 ξ η /
        origPhaseIntegral n h k β N 1 ξ η := by
  unfold spatialEnergyMean
  have := origPhaseIntegral_energy_pow_mul n h k β N ξ η 1
  simp only [pow_one, shift_fun_eq] at this
  rw [this]

/-- **Two-term asymptotics of the posterior energy mean with spatial phase**:
`L (E_{Q_N^ξ}[NK] − A₁/A₀) → (A₀ B₁ − A₁ B₀)/A₀²`. -/
theorem spatialEnergyMean_twoTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : spatialFace h k l β ξ η ≠ 0) :
    Tendsto (fun N => Real.log N * (spatialEnergyMean n h k β N ξ η -
        spatialFace (fun i => h i + 2 * k i) k (l + 1) β ξ η / spatialFace h k l β ξ η)) atTop
      (𝓝 ((spatialFace h k l β ξ η *
          spatialSecondCoeff n (fun i => h i + 2 * k i) k β cξ cη (l + 1) -
        spatialFace (fun i => h i + 2 * k i) k (l + 1) β ξ η * spatialSecondCoeff n h k β cξ cη l) /
        spatialFace h k l β ξ η ^ 2)) := by
  have hZ := spatialPhase_twoTerm_chart n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
  have hZ' := spatialPhase_twoTerm_chart n (fun i => h i + 2 * k i) k hk hβ hξ hη hξc hηc hevξ hevη
    (hmin_shift h k hk hmin) (hatt_shift h k hk hatt)
  rw [multCount_shift h k hk l] at hZ'
  have hq := quotient_second_order hA hZ hZ'
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  rw [spatialEnergyMean_eq, add_sub_cancel_left, Real.rpow_one, mul_div_assoc, div_self hlog,
    mul_one]
  ring

/-- The next-log posterior energy correction `c₂(ξ) = (A₀ B₁ − A₁ B₀)/A₀²` with the explicit
finite-part second coefficients. -/
noncomputable def spatialEnergyCorrection {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  (spatialFace h k l β ξ η * spatialSecondFace (fun i => h i + 2 * k i) k (l + 1) β ξ η -
    spatialFace (fun i => h i + 2 * k i) k (l + 1) β ξ η * spatialSecondFace h k l β ξ η) /
    spatialFace h k l β ξ η ^ 2

/-- **Explicit next-log correction of the posterior energy mean** (`m ≥ 2`):
`L (E_{Q_N^ξ}[NK] − μ_ξ) → c₂(ξ)`. -/
theorem spatialEnergyMean_twoTerm_explicit (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) (hA : spatialFace h k l β ξ η ≠ 0) :
    Tendsto (fun N => Real.log N * (spatialEnergyMean n h k β N ξ η -
        spatialFace (fun i => h i + 2 * k i) k (l + 1) β ξ η / spatialFace h k l β ξ η)) atTop
      (𝓝 (spatialEnergyCorrection h k l β ξ η)) := by
  have := spatialEnergyMean_twoTerm n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hA
  rwa [spatialSecondCoeff_eq n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm,
    spatialSecondCoeff_eq n (fun i => h i + 2 * k i) k hk hβ hξ hη hξc hηc hevξ hevη
      (hmin_shift h k hk hmin) (hatt_shift h k hk hatt)
      (by rw [multCount_shift h k hk l]; exact hm)] at this

/-! ### Zero-phase sanity check against Programme Q -/

/-- A sequence `L · c` with `L → ∞` converges only if `c = 0`. -/
theorem eq_zero_of_tendsto_log_mul_const {c x : ℝ}
    (h : Tendsto (fun N : ℝ => Real.log N * c) atTop (𝓝 x)) : c = 0 := by
  by_contra hc
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · exact not_tendsto_atBot_of_tendsto_nhds h
      (Real.tendsto_log_atTop.atTop_mul_const_of_neg hneg)
  · exact not_tendsto_atTop_of_tendsto_nhds h (Real.tendsto_log_atTop.atTop_mul_const hpos)

theorem spatialEnergyMean_zero_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) :
    spatialEnergyMean n h k β N (fun _ => 0) η =
      N * (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) := by
  unfold spatialEnergyMean origPhaseIntegral
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u _ => ?_
  ring

/-- **Zero-phase check**: at `ξ = 0` the leading posterior mean is `λ/β` and the next-log
correction is `−(m−1)/β` (the Programme Q value), for analytic amplitudes with nonzero face
coefficient. -/
theorem spatialEnergyMean_zero_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {r R : ℝ} (hr : 1 < r) (hrR : r < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hA : amplitudeCoeff h k l β η ≠ 0) :
    spatialFace (fun i => h i + 2 * k i) k (l + 1) β (fun _ => 0) η /
        spatialFace h k l β (fun _ => 0) η = l / β ∧
      (spatialFace h k l β (fun _ => 0) η *
          spatialSecondCoeff n (fun i => h i + 2 * k i) k β (constFamily 0)
            (polyRealCoeff (n + 1) r Fη) (l + 1) -
        spatialFace (fun i => h i + 2 * k i) k (l + 1) β (fun _ => 0) η *
          spatialSecondCoeff n h k β (constFamily 0) (polyRealCoeff (n + 1) r Fη) l) /
        spatialFace h k l β (fun _ => 0) η ^ 2 =
      -((multCount (ratioExp h k) l : ℝ) - 1) / β := by
  have hl : 0 < l := ratioExp_min_pos h k hk hatt
  have hr0 : 0 < r := by linarith
  have hR1 : 1 < R := by linarith
  -- the zero-phase face functional is the amplitude coefficient
  have hF0 : spatialFace h k l β (fun _ => 0) η = amplitudeCoeff h k l β η := by
    refine tendsto_nhds_unique (spatialPhase_tendsto n h k hk l β hl hβ hmin hatt _ η
      continuous_const hηc) ?_
    have := amplitude_tendsto n h k hk l β hl hβ hmin hatt η hηc
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [origPhaseIntegral_population_one]
  have hA' : spatialFace h k l β (fun _ => 0) η ≠ 0 := by rw [hF0]; exact hA
  have hη' := (absSummableAt_one_iff _).1 (absSummableAt_polyRealCoeff hr0 hrR zero_le_one hr hFη)
  have hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (polyRealCoeff (n + 1) r Fη) u = η u :=
    fun u hu => by rw [evalF_polyRealCoeff hr0 hrR hr hFη hu, hη u hu]
  have hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (constFamily 0 : CoeffFamily (n + 1)) u =
      (fun _ => (0 : ℝ)) u := fun u _ => evalF_constFamily 0 u
  have h1 := spatialEnergyMean_twoTerm n h k hk hβ (absSummable_constFamily 0) hη' continuous_const
    hηc hevξ hevη hmin hatt hA'
  have h2 := energy_correction_chart n h k hk β hβ hR1 hFη hη hηc hmin hatt hA
  -- `h2` in terms of the posterior energy mean
  have h2' : Tendsto (fun N => Real.log N * (spatialEnergyMean n h k β N (fun _ => 0) η - l / β))
      atTop (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) / β)) := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : N ≠ 0 := by positivity
    rw [spatialEnergyMean_zero_eq]
    field_simp
  -- the difference of the two centred sequences is `L · c` with `c` the difference of centres
  have hdiff := h1.sub h2'
  have hzero : l / β - spatialFace (fun i => h i + 2 * k i) k (l + 1) β (fun _ => 0) η /
      spatialFace h k l β (fun _ => 0) η = 0 :=
    eq_zero_of_tendsto_log_mul_const (hdiff.congr' (Eventually.of_forall fun N => by ring))
  have hmean : spatialFace (fun i => h i + 2 * k i) k (l + 1) β (fun _ => 0) η /
      spatialFace h k l β (fun _ => 0) η = l / β := by linarith
  refine ⟨hmean, ?_⟩
  rw [hmean] at h1
  exact tendsto_nhds_unique h1 h2'

end Grammar
