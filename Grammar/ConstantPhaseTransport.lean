/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseMomentRecurrence
import Grammar.CoefficientTransport

/-!
# Constant-phase coefficient transport (unit 334; Astra #39 unit 10, kernel level)

For a constant fluctuation `ξ ≡ a` the Taylor data are the constant family `constFamily a` (the
coefficient `a` at `γ = 0`). Its constant-free part is zero, so the paper's coefficient series
collapses to its `p = 0` term with the phase-dressed kernel:
`C(μ, j; a) = K_k ∑_γ cη_γ S(μ, j; γ; a)` with `S` built from the moments
`J_{μ,i}(a) = ∫ t^{μ−1}(−log t)^i e^{−βt+β√t a} dt` (`familySpectralCoeff_constPhase`). The phase
moment recurrence then transports the energy insertion `h ↦ h + 2k`:
```
C_K(μ+1, j; a) = (μ C(μ,j;a) − (j+1) C(μ,j+1;a))/β + (a/2) H(μ, j; a),
```
where `H` is the half-shifted kernel functional built from `J_{μ+1/2, ·}(a)`
(`kernelSHalf`, `kernelFunctionalHalf`, `kernelS_add_two_k_phase`,
`kernelFunctional_add_two_k_phase`, `population_coeff_add_two_k_phase`). At the level of a single
kernel term the half-shifted kernel is the phase derivative: `∂_a S(μ,j;γ;a) = β H(μ,j;γ;a)`
(`hasDerivAt_kernelS_phase`), so formally `C_K(μ+1,j;a) = (μC − (j+1)C(μ,j+1) + (a/2)∂_a C)/β`.
NOT claimed: the derivative at the level of the summed functional (passing `∂_a` through the
`γ`-sum needs a locally uniform domination of the half kernels), nor any asymptotic statement for
the fluctuation-dressed integral. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- The constant coefficient family: `a` at `γ = 0`, zero elsewhere. -/
noncomputable def CoeffFamily.constFamily (a : ℝ) : CoeffFamily d :=
  fun γ => if γ = 0 then a else 0

theorem CoeffFamily.constFamily_zero_apply (a : ℝ) : (constFamily a : CoeffFamily d) 0 = a := by
  simp [constFamily]

theorem CoeffFamily.fluctFamily_constFamily (a : ℝ) :
    fluctFamily (constFamily a : CoeffFamily d) = 0 := by
  funext γ
  unfold fluctFamily constFamily
  split_ifs <;> rfl

theorem CoeffFamily.absSummable_constFamily (a : ℝ) :
    AbsSummable (constFamily a : CoeffFamily d) := by
  unfold AbsSummable constFamily
  refine (hasSum_ite_eq (0 : Fin d → ℕ) |a|).summable.congr fun γ => ?_
  split_ifs <;> simp

/-- At constant phase every coefficient term of positive fluctuation order vanishes. -/
theorem familyCoeffTerm_constPhase_ne (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) {p : ℕ} (hp : p ≠ 0) :
    familyCoeffTerm n h k β (constFamily a) cη μ j p = 0 := by
  unfold familyCoeffTerm
  rw [fluctFamily_constFamily, convPow_zero_family hp, conv_zero_right,
    kernelFunctional_zero_family, mul_zero]

/-- At constant phase the `p = 0` term is the phase-dressed kernel functional. -/
theorem familyCoeffTerm_constPhase_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffTerm n h k β (constFamily a) cη μ j 0 = kernelFunctional n h k β a 0 μ j cη := by
  unfold familyCoeffTerm
  rw [fluctFamily_constFamily, conv_convPow_zero, constFamily_zero_apply]
  simp

/-- **Constant-phase coefficients are the phase-dressed kernel functionals**
`C(μ,j;a) = K_k ∑_γ cη_γ S(μ,j;γ;a)`. -/
theorem familySpectralCoeff_constPhase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β (constFamily a) cη μ j = kernelFunctional n h k β a 0 μ j cη := by
  rw [familySpectralCoeff_eq_series n h k hk β hβ (absSummable_constFamily a) hη hμ j]
  unfold familyCoeffSeries
  rw [tsum_eq_single 0 fun p hp => familyCoeffTerm_constPhase_ne n h k β a cη μ j hp]
  exact familyCoeffTerm_constPhase_zero n h k β a cη μ j

/-- The half-shifted kernel: the state-density coefficients at `μ` against the moments at
`μ + 1/2`. -/
noncomputable def kernelSHalf (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a μ : ℝ) (j : ℕ)
    (γ : Fin (n + 1) → ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β a 0 (μ + 1 / 2) (q - j)

/-- The half-shifted kernel functional `H(μ,j) = K_k ∑_γ f_γ S^{1/2}(μ,j;γ)`. -/
noncomputable def kernelFunctionalHalf (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a μ : ℝ) (j : ℕ)
    (f : CoeffFamily (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ * kernelSHalf n h k β a μ j γ

theorem abs_kernelSHalf_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    |kernelSHalf n h k β a μ j γ| ≤ kernelBudget n k * phaseLogMoment β a (μ + 1 / 2) n 0 := by
  have hμ' : 0 < μ + 1 / 2 := by linarith
  unfold kernelSHalf kernelBudget
  set M := phaseLogMoment β a (μ + 1 / 2) n 0 with hM
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg β a (μ + 1 / 2) n 0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a 0 (μ + 1 / 2) (q - j)| ≤
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
    intro q hq
    have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
    rw [abs_mul, abs_mul, Nat.abs_cast]
    refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n (h + γ) k hk μ q) ?_
      (by positivity) (by positivity)) (abs_fluctMoment_le β a hβ 0 hμ' (by omega))
      (abs_nonneg _) (by positivity)
    calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
      _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Ico]
  have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
  calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
      ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem summable_kernelHalf_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    Summable fun γ => |f γ * kernelSHalf n h k β a μ j γ| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun γ => ?_)
    (hf.mul_right (kernelBudget n k * phaseLogMoment β a (μ + 1 / 2) n 0))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_kernelSHalf_le n h k hk β a hβ hμ j γ) (abs_nonneg _)

/-- **Kernel transport with constant phase**:
`S_K(μ+1,j;a) = (μ S(μ,j;a) − (j+1) S(μ,j+1;a))/β + (a/2) S^{1/2}(μ,j;a)`. -/
theorem kernelS_add_two_k_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (a : ℝ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    kernelS n (fun i => h i + 2 * k i) k β a 0 (μ + 1) j γ =
      (μ * kernelS n h k β a 0 μ j γ - ((j : ℝ) + 1) * kernelS n h k β a 0 μ (j + 1) γ) / β +
        a / 2 * kernelSHalf n h k β a μ j γ := by
  have hw : monoWeights ((fun i => h i + 2 * k i) + γ) k =
      fun i => monoWeights (h + γ) k i + 1 := by
    have : ((fun i => h i + 2 * k i) + γ : Fin (n + 1) → ℕ) = fun i => (h + γ) i + 2 * k i := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [this, monoWeights_add_two_k (h + γ) k hk]
  unfold kernelS kernelSHalf
  rw [hw, stateDensityRep_shift]
  simp only [PowLogRep.coeffAt_shift]
  set c : ℕ → ℝ := fun q => PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q
    with hc
  have hM : ∀ q ∈ Finset.Ico j (n + 1),
      c q * (q.choose j : ℝ) * fluctMoment β a 0 (μ + 1) (q - j) =
        (μ * (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j - 1))) / β +
        a / 2 * (c q * (q.choose j : ℝ) * fluctMoment β a 0 (μ + 1 / 2) (q - j)) := by
    intro q _
    rw [fluctMoment_succ_exponent_phase hβ hμ a (q - j)]
    field_simp
  have hsecond : ∑ q ∈ Finset.Ico j (n + 1),
      ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j - 1)) =
      ((j : ℝ) + 1) * ∑ q ∈ Finset.Ico (j + 1) (n + 1),
        c q * (q.choose (j + 1) : ℝ) * fluctMoment β a 0 μ (q - (j + 1)) := by
    rcases le_or_gt j n with hjn | hjn
    · rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hcast : ((q - j : ℕ) : ℝ) * (q.choose j : ℝ) =
          ((j : ℝ) + 1) * (q.choose (j + 1) : ℝ) := by
        have h2 : ((q.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((q.choose j * (q - j) : ℕ) : ℝ) := by
          rw [Nat.choose_succ_right_eq]
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_succ] at h2
        linarith
      rw [Nat.sub_sub, show ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) *
          fluctMoment β a 0 μ (q - (j + 1))) = (((q - j : ℕ) : ℝ) * (q.choose j : ℝ)) *
          (c q * fluctMoment β a 0 μ (q - (j + 1))) by ring, hcast]
      ring
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
      simp
  calc ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β a 0 (μ + 1) (q - j)
      = ∑ q ∈ Finset.Ico j (n + 1), ((μ * (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j - 1))) / β +
          a / 2 * (c q * (q.choose j : ℝ) * fluctMoment β a 0 (μ + 1 / 2) (q - j))) :=
        Finset.sum_congr rfl hM
    _ = (μ * ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j) -
          ∑ q ∈ Finset.Ico j (n + 1), ((q - j : ℕ) : ℝ) *
            (c q * (q.choose j : ℝ) * fluctMoment β a 0 μ (q - j - 1))) / β +
        a / 2 * ∑ q ∈ Finset.Ico j (n + 1),
          c q * (q.choose j : ℝ) * fluctMoment β a 0 (μ + 1 / 2) (q - j) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.mul_sum,
          Finset.mul_sum]
    _ = _ := by rw [hsecond]

/-- **Kernel-functional transport with constant phase.** -/
theorem kernelFunctional_add_two_k_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (a : ℝ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) :
    kernelFunctional n (fun i => h i + 2 * k i) k β a 0 (μ + 1) j f =
      (μ * kernelFunctional n h k β a 0 μ j f -
        ((j : ℝ) + 1) * kernelFunctional n h k β a 0 μ (j + 1) f) / β +
        a / 2 * kernelFunctionalHalf n h k β a μ j f := by
  unfold kernelFunctional kernelFunctionalHalf
  simp only [kernelS_add_two_k_phase n h k hk hβ hμ a _ _]
  have h1 : Summable fun γ => f γ * kernelS n h k β a 0 μ j γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β a hβ 0 hμ j hf
  have h2 : Summable fun γ => f γ * kernelS n h k β a 0 μ (j + 1) γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β a hβ 0 hμ (j + 1) hf
  have h3 : Summable fun γ => f γ * kernelSHalf n h k β a μ j γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernelHalf_term n h k hk β a hβ hμ j hf
  have hfun : (fun γ => f γ * ((μ * kernelS n h k β a 0 μ j γ -
      ((j : ℝ) + 1) * kernelS n h k β a 0 μ (j + 1) γ) / β +
        a / 2 * kernelSHalf n h k β a μ j γ)) =
      fun γ => (1 / β) * (μ * (f γ * kernelS n h k β a 0 μ j γ) -
        ((j : ℝ) + 1) * (f γ * kernelS n h k β a 0 μ (j + 1) γ)) +
        a / 2 * (f γ * kernelSHalf n h k β a μ j γ) := by
    funext γ
    field_simp
  rw [hfun, Summable.tsum_add (((h1.mul_left μ).sub (h2.mul_left _)).mul_left _) (h3.mul_left _),
    tsum_mul_left, Summable.tsum_sub (h1.mul_left μ) (h2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left]
  field_simp

/-- **Constant-phase coefficient transport**
`C_K(μ+1, j; a) = (μ C(μ,j;a) − (j+1) C(μ,j+1;a))/β + (a/2) H(μ,j;a)`. -/
theorem population_coeff_add_two_k_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (μ + 1) j =
      (μ * familySpectralCoeff n h k β (constFamily a) cη μ j -
        ((j : ℝ) + 1) * familySpectralCoeff n h k β (constFamily a) cη μ (j + 1)) / β +
        a / 2 * kernelFunctionalHalf n h k β a μ j cη := by
  rw [familySpectralCoeff_constPhase n _ k hk hβ a hη (by linarith) j,
    familySpectralCoeff_constPhase n h k hk hβ a hη hμ j,
    familySpectralCoeff_constPhase n h k hk hβ a hη hμ (j + 1)]
  exact kernelFunctional_add_two_k_phase n h k hk hβ hμ a j hη

/-- **The half-shifted kernel is the phase derivative of the kernel**: `∂_a S = β S^{1/2}`. -/
theorem hasDerivAt_kernelS_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) (a₀ : ℝ) :
    HasDerivAt (fun a => kernelS n h k β a 0 μ j γ) (β * kernelSHalf n h k β a₀ μ j γ) a₀ := by
  unfold kernelS kernelSHalf
  rw [Finset.mul_sum]
  have hsum : HasDerivAt (∑ q ∈ Finset.Ico j (n + 1), fun a =>
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
        fluctMoment β a 0 μ (q - j))
      (∑ q ∈ Finset.Ico j (n + 1), β *
        (PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a₀ 0 (μ + 1 / 2) (q - j))) a₀ := by
    refine HasDerivAt.sum fun q _ => ?_
    have := (hasDerivAt_fluctMoment_phase hβ hμ (q - j) a₀).const_mul
      (PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ))
    refine this.congr_deriv ?_
    ring
  convert hsum using 1
  funext a
  simp [Finset.sum_apply]

end Grammar
