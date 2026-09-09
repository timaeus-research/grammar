/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseUniform
import Grammar.ConstantPhaseRandom
import Grammar.SecondOrderStochastic
import Grammar.SecondOrderStochasticOne

/-!
# Moving random constant phase (unit 341; Astra #40 unit 5b)

For random constant phases `X_N ⇒ X`, the normalised constant-phase energy
`Q_N(a) = N 𝒵_N[K∘π η; a]/𝒵_N[η; a]` satisfies `Q_N(X_N) ⇒ c₁(X)` and the next-log statement
`log N (Q_N(X_N) − c₁(X_N)) ⇒ c₂(X)`, centred at `c₁(X_N)` (not at `c₁(X)`).  The proof runs
the four-statistics second-order interface on `(R_N, A(X_N), R'_N, E(X_N))`: the remainders
`R_N − B(X_N)`, `R'_N − D(X_N)` tend to zero in measure by the compact-uniform two-term data
and tightness of `X_N`, while `(B, A, D, E)(X_N) ⇒ (B, A, D, E)(X)` by continuous mapping.  The
leading coefficient is assumed positive for every phase (as under a positive face witness), so
no localisation away from zeros of `A` is needed.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### Continuity of the constant-phase coefficients and the transported data -/

theorem continuous_constPhaseCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) (j : ℕ) :
    Continuous fun a => familySpectralCoeff n h k β (constFamily a) cη l j :=
  continuous_iff_continuousAt.2 fun a =>
    (hasDerivAt_constPhase_coeff n h k hk hβ hη hl j a).continuousAt

theorem continuous_constPhaseSecondCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) :
    Continuous fun a => constPhaseSecondCoeff n h k β cη a l := by
  unfold constPhaseSecondCoeff
  split_ifs
  · exact continuous_constPhaseCoeff n h k hk hβ hη hl _
  · exact continuous_const

/-- The energy numerator's leading coefficient `E(a) = (λ A(a) + (a/2) A'(a))/β`. -/
theorem constPhase_energyCoeff_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
        (multCount (ratioExp h k) l - 1) =
      (l * familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) +
        a / 2 * deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
          (multCount (ratioExp h k) l - 1)) a) / β := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  obtain ⟨hzero, -⟩ := constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt
  rw [population_coeff_add_two_k_phase_deriv n h k hk hβ a hη hl0 (multCount (ratioExp h k) l - 1),
    hzero (multCount (ratioExp h k) l - 1 + 1) (by omega), mul_zero, sub_zero]

/-- The energy numerator's second coefficient `D(a) = (λ B(a) − (m−1) A(a) + (a/2) B'(a))/β`. -/
theorem constPhaseSecondCoeff_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) :
    constPhaseSecondCoeff n (fun i => h i + 2 * k i) k β cη a (l + 1) =
      (l * constPhaseSecondCoeff n h k β cη a l -
        ((multCount (ratioExp h k) l : ℝ) - 1) *
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) +
        a / 2 * deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a) / β := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ hatt
  have hmK : multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l :=
    multCount_add_two_k h k hk l
  rcases Nat.lt_or_ge (multCount (ratioExp h k) l) 2 with hm2 | hm2
  · have hm1' : multCount (ratioExp h k) l = 1 := by omega
    simp only [constPhaseSecondCoeff, hmK, hm1', (by norm_num : ¬ (2 ≤ 1)), if_false, deriv_const]
    simp
  · obtain ⟨s, hs⟩ : ∃ s, multCount (ratioExp h k) l = s + 2 :=
      ⟨multCount (ratioExp h k) l - 2, by omega⟩
    have e1 : s + 2 - 1 = s + 1 := by omega
    have e2 : s + 2 - 2 = s := by omega
    simp only [constPhaseSecondCoeff, hmK, hs, e1, e2, (by omega : 2 ≤ s + 2), if_true]
    rw [population_coeff_add_two_k_phase_deriv n h k hk hβ a hη hl0 s]
    push_cast
    ring

/-- `c₁(a) = E(a)/A(a)`: the leading energy is the ratio of the leading coefficients. -/
theorem constPhaseC1_eq_div (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    constPhaseC1 n h k β cη l a =
      familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
          (multCount (ratioExp h k) l - 1) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) := by
  rw [constPhase_energyCoeff_eq n h k hk hβ a hη hηc hev hmin hatt]
  unfold constPhaseC1
  field_simp

/-- `c₂(a) = (A D − E B)/A²` in terms of the two-term data of denominator and numerator. -/
theorem constPhaseC2_eq_div (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    constPhaseC2 n h k β cη l a =
      (familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) *
          constPhaseSecondCoeff n (fun i => h i + 2 * k i) k β cη a (l + 1) -
        familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
          (multCount (ratioExp h k) l - 1) * constPhaseSecondCoeff n h k β cη a l) /
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2 := by
  rw [constPhase_energyCoeff_eq n h k hk hβ a hη hηc hev hmin hatt,
    constPhaseSecondCoeff_add_two_k n h k hk hβ a hη hatt]
  unfold constPhaseC2
  linear_combination (((multCount (ratioExp h k) l : ℝ) - 1) / β) *
    mul_inv_cancel₀ (pow_ne_zero 2 hA)

theorem continuous_constPhaseC1 (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) :
    Continuous (constPhaseC1 n h k β cη l) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have e : constPhaseC1 n h k β cη l = fun a =>
      familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
          (multCount (ratioExp h k) l - 1) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) :=
    funext fun a => constPhaseC1_eq_div n h k hk hβ a hη hηc hev hmin hatt (hApos a).ne'
  rw [e]
  exact (continuous_constPhaseCoeff n _ k hk hβ hη (by linarith) _).div
    (continuous_constPhaseCoeff n h k hk hβ hη hl0 _) fun a => (hApos a).ne'

theorem continuous_constPhaseC2 (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) :
    Continuous (constPhaseC2 n h k β cη l) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hl1 : 0 < l + 1 := by linarith
  have e : constPhaseC2 n h k β cη l = fun a =>
      (familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) *
          constPhaseSecondCoeff n (fun i => h i + 2 * k i) k β cη a (l + 1) -
        familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
          (multCount (ratioExp h k) l - 1) * constPhaseSecondCoeff n h k β cη a l) /
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2 :=
    funext fun a => constPhaseC2_eq_div n h k hk hβ a hη hηc hev hmin hatt (hApos a).ne'
  rw [e]
  have hA := continuous_constPhaseCoeff n h k hk hβ hη hl0 (multCount (ratioExp h k) l - 1)
  exact ((hA.mul (continuous_constPhaseSecondCoeff n _ k hk hβ hη hl1)).sub
    ((continuous_constPhaseCoeff n _ k hk hβ hη hl1 _).mul
      (continuous_constPhaseSecondCoeff n h k hk hβ hη hl0))).div (hA.pow 2)
    fun a => pow_ne_zero 2 (hApos a).ne'

/-! ### The moving random phase -/

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {F : Filter ι}
  [F.IsCountablyGenerated]

/-- **Moving random constant phase, next-log order.** If `X_N ⇒ X` and the leading
constant-phase coefficient `A(a)` is positive for every phase, then
`log N (Q_N(X_N) − c₁(X_N)) ⇒ c₂(X)`, centred at the current phase `c₁(X_N)`. -/
theorem constPhase_energy_correction_moving (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ) (hXzm : Measurable Xz)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
        (constPhaseEnergy n h k β (Nseq i) η (X i ω) - constPhaseC1 n h k β cη l (X i ω))) F
      (fun ω => constPhaseC2 n h k β cη l (Xz ω)) (fun _ => μ) μ' := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hl1 : 0 < l + 1 := by linarith
  have hminK := hmin_add_two_k h k hk hmin
  have hattK := hatt_add_two_k h k hk hatt
  have hmK : multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l :=
    multCount_add_two_k h k hk l
  -- the four coefficient functions
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ a, A a =
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, ∀ a, B a = constPhaseSecondCoeff n h k β cη a l :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, ∀ a, E a = familySpectralCoeff n (fun i => h i + 2 * k i) k β
      (constFamily a) cη (l + 1) (multCount (ratioExp h k) l - 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : ℝ → ℝ, ∀ a, Dc a =
      constPhaseSecondCoeff n (fun i => h i + 2 * k i) k β cη a (l + 1) := ⟨_, fun _ => rfl⟩
  have hAc : Continuous A := by
    rw [funext hA]
    exact continuous_constPhaseCoeff n h k hk hβ hη hl0 _
  have hBc : Continuous B := by
    rw [funext hB]
    exact continuous_constPhaseSecondCoeff n h k hk hβ hη hl0
  have hEc : Continuous E := by
    rw [funext hE]
    exact continuous_constPhaseCoeff n _ k hk hβ hη hl1 _
  have hDcc : Continuous Dc := by
    rw [funext hDc]
    exact continuous_constPhaseSecondCoeff n _ k hk hβ hη hl1
  -- sample size, logarithm, normalisers
  have hN0 : ∀ i, 0 < Nseq i := fun i => lt_trans one_pos (hN1 i)
  have hL : ∀ i, 0 < Real.log (Nseq i) := fun i => Real.log_pos (hN1 i)
  have hP : ∀ i, Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    fun i => mul_ne_zero (Real.rpow_pos_of_pos (hN0 i) _).ne' (pow_ne_zero _ (hL i).ne')
  have hP' : ∀ i, Nseq i ^ (-(l + 1)) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    fun i => mul_ne_zero (Real.rpow_pos_of_pos (hN0 i) _).ne' (pow_ne_zero _ (hL i).ne')
  obtain ⟨D, hD⟩ : ∃ D : ι → ℝ, ∀ i, D i = Nseq i ^ (-l) *
      Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) / Real.log (Nseq i) := ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ι → ℝ, ∀ i, D' i = Nseq i ^ (-(l + 1)) *
      Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) / Real.log (Nseq i) := ⟨_, fun _ => rfl⟩
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD]
    exact div_ne_zero (hP i) (hL i).ne'
  have hD'ne : ∀ i, D' i ≠ 0 := fun i => by
    rw [hD']
    exact div_ne_zero (hP' i) (hL i).ne'
  have hDD : ∀ i, D i / D' i = Nseq i := fun i => by
    have hrp : Nseq i ^ (-l) = Nseq i * Nseq i ^ (-(l + 1)) := by
      rw [show -(l + 1) = -l + -1 by ring, Real.rpow_add (hN0 i), Real.rpow_neg (hN0 i).le 1,
        Real.rpow_one, mul_comm (Nseq i), mul_assoc, inv_mul_cancel₀ (hN0 i).ne', mul_one]
    rw [div_eq_iff (hD'ne i), hD, hD', hrp]
    ring
  -- the two integrals
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : ι → Ω → ℝ, ∀ i ω,
      Z1 i ω = origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Zφ, hZφ⟩ : ∃ Zφ : ι → Ω → ℝ, ∀ i ω, Zφ i ω =
      origPhaseIntegral n (fun i => h i + 2 * k i) k β (Nseq i) 1 (fun _ => X i ω) η :=
    ⟨_, fun _ _ => rfl⟩
  -- the two remainder statistics
  obtain ⟨R, hR⟩ : ∃ R : ι → Ω → ℝ, ∀ i ω, R i ω = Real.log (Nseq i) *
      (Z1 i ω / (Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)) -
        A (X i ω)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ι → Ω → ℝ, ∀ i ω, R' i ω = Real.log (Nseq i) *
      (Zφ i ω / (Nseq i ^ (-(l + 1)) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)) -
        E (X i ω)) := ⟨_, fun _ _ => rfl⟩
  -- measurability
  have hZ1m : ∀ i, Measurable (Z1 i) := fun i => by
    rw [show Z1 i = (fun a => origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a) η) ∘ X i from
      funext (hZ1 i)]
    exact (continuous_constPhase_integral n h k hβ (hN0 i).le η hηc).measurable.comp (hXm i)
  have hZφm : ∀ i, Measurable (Zφ i) := fun i => by
    rw [show Zφ i = (fun a => origPhaseIntegral n (fun i => h i + 2 * k i) k β (Nseq i) 1
      (fun _ => a) η) ∘ X i from funext (hZφ i)]
    exact (continuous_constPhase_integral n _ k hβ (hN0 i).le η hηc).measurable.comp (hXm i)
  have hAm : ∀ i, Measurable fun ω => A (X i ω) := fun i => hAc.measurable.comp (hXm i)
  have hEm : ∀ i, Measurable fun ω => E (X i ω) := fun i => hEc.measurable.comp (hXm i)
  have hRm : ∀ i, Measurable (R i) := fun i => by
    rw [show R i = fun ω => _ from funext (hR i)]
    exact (((hZ1m i).div_const _).sub (hAm i)).const_mul _
  have hR'm : ∀ i, Measurable (R' i) := fun i => by
    rw [show R' i = fun ω => _ from funext (hR' i)]
    exact (((hZφm i).div_const _).sub (hEm i)).const_mul _
  -- the structural identities `Z = D (A log N + R)`
  have hZ1eq : ∀ i ω, Z1 i ω = D i * (A (X i ω) * Real.log (Nseq i) + R i ω) := fun i ω => by
    have h1 : Nseq i ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (hN0 i) _).ne'
    have h2 := (hL i).ne'
    have h3 : Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ h2
    rw [hR, hD]
    field_simp
    ring
  have hZφeq : ∀ i ω, Zφ i ω = D' i * (E (X i ω) * Real.log (Nseq i) + R' i ω) := fun i ω => by
    have h1 : Nseq i ^ (-(l + 1)) ≠ 0 := (Real.rpow_pos_of_pos (hN0 i) _).ne'
    have h2 := (hL i).ne'
    have h3 : Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ h2
    rw [hR', hD']
    field_simp
    ring
  -- the remainders vanish in measure: compact-uniform two-term data plus tightness of `X`
  have htight := normBounded_of_tendstoInDistribution' X Xz hX
  have hRsub : TendstoInMeasure μ (fun i ω => R i ω - B (X i ω)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_) htight
    filter_upwards [hN.eventually
      (constPhase_twoTerm_uniform n h k hk hβ hη hηc hev hmin hatt hM hε)] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [hR, hB, hA, hZ1]
    exact hi _ hω
  have hR'sub : TendstoInMeasure μ (fun i ω => R' i ω - Dc (X i ω)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_) htight
    have hu := constPhase_twoTerm_uniform n (fun i => h i + 2 * k i) k hk hβ hη hηc hev hminK
      hattK hM hε
    rw [hmK] at hu
    filter_upwards [hN.eventually hu] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [hR', hDc, hE, hZφ]
    exact hi _ hω
  -- continuous mapping of the coefficient vector
  have hC : TendstoInDistribution
      (fun i ω => (![B (X i ω), A (X i ω), Dc (X i ω), E (X i ω)] : Fin 4 → ℝ)) F
      (fun ω => (![B (Xz ω), A (Xz ω), Dc (Xz ω), E (Xz ω)] : Fin 4 → ℝ)) (fun _ => μ) μ' :=
    hX.continuous_comp (continuous_vec4 hBc hAc hDcc hEc)
  have hVm : ∀ i, Measurable fun ω => (![R i ω, A (X i ω), R' i ω, E (X i ω)] : Fin 4 → ℝ) :=
    fun i => measurable_vec4 (hRm i) (hAm i) (hR'm i) (hEm i)
  have hV : TendstoInDistribution
      (fun i ω => (![R i ω, A (X i ω), R' i ω, E (X i ω)] : Fin 4 → ℝ)) F
      (fun ω => (![B (Xz ω), A (Xz ω), Dc (Xz ω), E (Xz ω)] : Fin 4 → ℝ)) (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => (hVm i).aemeasurable
    have hzero : TendstoInMeasure μ (fun i ω => (0 : ℝ)) F (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto (fun _ => (0 : ℝ)) 0 tendsto_const_nhds
    have hpi := tendstoInMeasure_pi_zero (μ := μ) (L := F) (κ := Fin 4) (E := ℝ)
      ![fun i ω => R i ω - B (X i ω), fun _ _ => (0 : ℝ), fun i ω => R' i ω - Dc (X i ω),
        fun _ _ => (0 : ℝ)]
      (fun a => by fin_cases a <;> simp <;> first | exact hRsub | exact hR'sub | exact hzero)
    refine hpi.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    funext a
    simp only [Pi.sub_apply]
    fin_cases a <;> simp
  -- the limit denominator never vanishes
  have hBz : μ' {ω | A (Xz ω) = 0} = 0 := by
    have : {ω | A (Xz ω) = 0} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rw [hA]
      exact (hApos _).ne'
    rw [this, measure_empty]
  -- the four-statistics interface
  have hmain := tendstoInDistribution_secondOrder_of_stats Nseq hN1 hN (fun i ω => A (X i ω)) R
    (fun i ω => E (X i ω)) R' Zφ Z1 D D' hDne hD'ne hAm hRm hEm hR'm hZφm hZ1m hZ1eq hZφeq
    (fun ω => A (Xz ω)) (fun ω => B (Xz ω)) (fun ω => E (Xz ω)) (fun ω => Dc (Xz ω))
    (hAc.measurable.comp hXzm) (hBc.measurable.comp hXzm) (hEc.measurable.comp hXzm)
    (hDcc.measurable.comp hXzm) hV hBz
  -- identify the statistic and the limit
  have hfun : (fun i ω => Real.log (Nseq i) *
      (constPhaseEnergy n h k β (Nseq i) η (X i ω) - constPhaseC1 n h k β cη l (X i ω))) =
      fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω * (D i / D' i) - E (X i ω) / A (X i ω)) := by
    funext i ω
    unfold constPhaseEnergy
    rw [origPhaseIntegral_monomial_shift n h k β (Nseq i) 1 (fun _ => X i ω) η (fun i => 2 * k i),
      ← hZφ i ω, ← hZ1 i ω,
      constPhaseC1_eq_div n h k hk hβ _ hη hηc hev hmin hatt (hApos _).ne', ← hE, ← hA, hDD i]
    ring
  have hlim : (fun ω => constPhaseC2 n h k β cη l (Xz ω)) =
      fun ω => (A (Xz ω) * Dc (Xz ω) - E (Xz ω) * B (Xz ω)) / A (Xz ω) ^ 2 := by
    funext ω
    rw [constPhaseC2_eq_div n h k hk hβ _ hη hηc hev hmin hatt (hApos _).ne', ← hA, ← hB, ← hE,
      ← hDc]
  rw [hfun, hlim]
  exact hmain

/-- **Moving random constant phase, leading order**: `Q_N(X_N) ⇒ c₁(X)`. -/
theorem constPhase_energy_moving (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ) (hXzm : Measurable Xz)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => constPhaseEnergy n h k β (Nseq i) η (X i ω)) F
      (fun ω => constPhaseC1 n h k β cη l (Xz ω)) (fun _ => μ) μ' := by
  have hY := constPhase_energy_correction_moving n h k hk hβ hη hηc hev hmin hatt hApos Nseq hN1
    hN X hXm Xz hXzm hX
  have hC1 : TendstoInDistribution (fun i ω => constPhaseC1 n h k β cη l (X i ω)) F
      (fun ω => constPhaseC1 n h k β cη l (Xz ω)) (fun _ => μ) μ' :=
    hX.continuous_comp (g := constPhaseC1 n h k β cη l)
      (continuous_constPhaseC1 n h k hk hβ hη hηc hev hmin hatt hApos)
  have hN0 : ∀ i, 0 < Nseq i := fun i => lt_trans one_pos (hN1 i)
  have hL : ∀ i, 0 < Real.log (Nseq i) := fun i => Real.log_pos (hN1 i)
  have hQm : ∀ i, Measurable fun ω => constPhaseEnergy n h k β (Nseq i) η (X i ω) := fun i =>
    (measurable_constPhaseEnergy n h k hβ (hN0 i).le η hηc).comp (hXm i)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC1 ?_ fun i => (hQm i).aemeasurable
  have htight := normBounded_of_tendstoInDistribution' _ _ hY
  have hsub : TendstoInMeasure μ (fun i ω => Real.log (Nseq i) *
      (constPhaseEnergy n h k β (Nseq i) η (X i ω) - constPhaseC1 n h k β cη l (X i ω)) /
        Real.log (Nseq i)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ _ (fun M hM ε hε => ?_) htight
    have hLinf : Tendsto (fun i => Real.log (Nseq i)) F atTop := Real.tendsto_log_atTop.comp hN
    filter_upwards [hLinf.eventually (eventually_ge_atTop (M / ε))] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [abs_div, abs_of_pos (hL i), div_le_iff₀ (hL i)]
    calc _ ≤ M := hω
      _ = ε * (M / ε) := by field_simp
      _ ≤ ε * Real.log (Nseq i) := mul_le_mul_of_nonneg_left hi hε.le
  refine hsub.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun _ => rfl)
  simp only [Pi.sub_apply]
  exact mul_div_cancel_left₀ _ (hL i).ne'

/-- The moving-phase statements under a positive face witness (global positivity of `A`). -/
theorem constPhase_energy_correction_moving_of_witness (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hnn : ∀ u ∈ closedCube (n + 1), 0 ≤ η (faceProj h k l u))
    (u₁ : Fin (n + 1) → ℝ) (hu₁ : u₁ ∈ closedCube (n + 1)) (hpos : 0 < η (faceProj h k l u₁))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ) (hXzm : Measurable Xz)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => constPhaseEnergy n h k β (Nseq i) η (X i ω)) F
      (fun ω => constPhaseC1 n h k β cη l (Xz ω)) (fun _ => μ) μ' ∧
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
        (constPhaseEnergy n h k β (Nseq i) η (X i ω) - constPhaseC1 n h k β cη l (X i ω))) F
      (fun ω => constPhaseC2 n h k β cη l (Xz ω)) (fun _ => μ) μ' :=
  have hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) :=
    fun a => constPhase_coeff_pos n h k hk hβ a hη hηc hev hmin hatt hnn u₁ hu₁ hpos
  ⟨constPhase_energy_moving n h k hk hβ hη hηc hev hmin hatt hApos Nseq hN1 hN X hXm Xz hXzm hX,
    constPhase_energy_correction_moving n h k hk hβ hη hηc hev hmin hatt hApos Nseq hN1 hN X hXm
      Xz hXzm hX⟩

end Grammar
