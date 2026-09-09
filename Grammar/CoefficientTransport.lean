/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MomentRecurrence
import Grammar.PowLogShift
import Grammar.PopulationCoefficient

/-!
# Coefficient transport under the energy insertion (Programme Q, N2, unit 315)

Inserting the energy `K∘π = u^{2k}` into a population integral shifts the weight `h ↦ h + 2k`. At
the level of the Taylor-tree coefficient formula this shifts the state-density exponents by one
(`stateDensityRep_shift`, `coeffAt_shift`) and the kernel moments by one in the exponent
(`fluctMoment_succ_exponent`). The binomial identity `C(q,j)(q−j) = (j+1) C(q,j+1)` then gives, for
every `μ > 0` and every log degree `j`,
```
C_K(μ+1, j) = (μ C(μ, j) − (j+1) C(μ, j+1)) / β                 (population_coeff_add_two_k)
```
where `C` are the population coefficients of `(h, η)` and `C_K` those of `(h + 2k, η)` (both as
`familySpectralCoeff … 0 cη`, the canonical Taylor-tree coefficients at `b = 1`). This is Route B of
Astra #38: the transport is proved by coefficient algebra, never by differentiating a remainder.
At the first candidate `(λ, m−1)` it recovers `A_K = (λ/β) A` (unit 304), using the leading-support
vanishing `C(λ, m) = 0` (from `population_leadingCoeff_of_conclusion` for `m ≤ n` and
`population_coeff_eq_zero_of_gt_degree` for `m > n`; `m ≥ 1`), and for `m ≥ 2` at `(λ, m−2)` it
gives the log-correction coefficient `B_K = (λ B − (m−1) A)/β` with `B = C(λ, m−2)`. The ambient
degree bound `j > n ⇒ C(μ,j) = 0` is not the leading-support statement. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Kernel transport**: the zero-phase kernel of the shifted weight at `(μ+1, j)`. -/
theorem kernelS_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
    {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    kernelS n (fun i => h i + 2 * k i) k β 0 0 (μ + 1) j γ =
      (μ * kernelS n h k β 0 0 μ j γ - ((j : ℝ) + 1) * kernelS n h k β 0 0 μ (j + 1) γ) / β := by
  have hw : monoWeights ((fun i => h i + 2 * k i) + γ) k =
      fun i => monoWeights (h + γ) k i + 1 := by
    have : ((fun i => h i + 2 * k i) + γ : Fin (n + 1) → ℕ) = fun i => (h + γ) i + 2 * k i := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [this, monoWeights_add_two_k (h + γ) k hk]
  unfold kernelS
  rw [hw, stateDensityRep_shift]
  simp only [PowLogRep.coeffAt_shift]
  set c : ℕ → ℝ := fun q => PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q
    with hc
  have hM : ∀ q ∈ Finset.Ico j (n + 1),
      c q * (q.choose j : ℝ) * fluctMoment β 0 0 (μ + 1) (q - j) =
        (μ * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β := by
    intro q _
    rw [fluctMoment_succ_exponent hβ hμ (q - j)]
    field_simp
  have hsecond : ∑ q ∈ Finset.Ico j (n + 1),
      ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1)) =
      ((j : ℝ) + 1) * ∑ q ∈ Finset.Ico (j + 1) (n + 1),
        c q * (q.choose (j + 1) : ℝ) * fluctMoment β 0 0 μ (q - (j + 1)) := by
    rcases le_or_gt j n with hjn | hjn
    · rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hcast : ((q - j : ℕ) : ℝ) * (q.choose j : ℝ) = ((j : ℝ) + 1) * (q.choose (j + 1) : ℝ) :=
by
        have h2 : ((q.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((q.choose j * (q - j) : ℕ) : ℝ) := by
          rw [Nat.choose_succ_right_eq]
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_succ] at h2
        linarith
      rw [Nat.sub_sub, show ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) *
          fluctMoment β 0 0 μ (q - (j + 1))) = (((q - j : ℕ) : ℝ) * (q.choose j : ℝ)) *
          (c q * fluctMoment β 0 0 μ (q - (j + 1))) by ring, hcast]
      ring
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
      simp
  calc ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β 0 0 (μ + 1) (q - j)
      = ∑ q ∈ Finset.Ico j (n + 1), (μ * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β :=
        Finset.sum_congr rfl hM
    _ = (μ * ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j) -
          ∑ q ∈ Finset.Ico j (n + 1), ((q - j : ℕ) : ℝ) *
            (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hsecond]

/-- The zero-phase kernel vanishes above the top log degree. -/
theorem kernelS_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) {j : ℕ}
    (hj : n < j) (γ : Fin (n + 1) → ℕ) : kernelS n h k β a p μ j γ = 0 := by
  unfold kernelS
  rw [Finset.Ico_eq_empty_of_le (by omega)]
  rfl

/-- **Kernel-functional transport.** -/
theorem kernelFunctional_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    kernelFunctional n (fun i => h i + 2 * k i) k β 0 0 (μ + 1) j f =
      (μ * kernelFunctional n h k β 0 0 μ j f -
        ((j : ℝ) + 1) * kernelFunctional n h k β 0 0 μ (j + 1) f) / β := by
  unfold kernelFunctional
  simp only [kernelS_add_two_k n h k hk hβ hμ _ _]
  have h1 : Summable fun γ => f γ * kernelS n h k β 0 0 μ j γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β 0 hβ 0 hμ j hf
  have h2 : Summable fun γ => f γ * kernelS n h k β 0 0 μ (j + 1) γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β 0 hβ 0 hμ (j + 1) hf
  have hfun : (fun γ => f γ * ((μ * kernelS n h k β 0 0 μ j γ -
      ((j : ℝ) + 1) * kernelS n h k β 0 0 μ (j + 1) γ) / β)) =
      fun γ => (1 / β) * (μ * (f γ * kernelS n h k β 0 0 μ j γ) -
        ((j : ℝ) + 1) * (f γ * kernelS n h k β 0 0 μ (j + 1) γ)) := by
    funext γ
    field_simp
  rw [hfun, tsum_mul_left, Summable.tsum_sub (h1.mul_left μ) (h2.mul_left _), tsum_mul_left,
    tsum_mul_left]
  field_simp

/-- **Coefficient transport under the energy insertion**: for the population coefficients of an
admissible amplitude family, `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` (`μ > 0`). -/
theorem population_coeff_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n (fun i => h i + 2 * k i) k β 0 cη (μ + 1) j =
      (μ * familySpectralCoeff n h k β 0 cη μ j -
        ((j : ℝ) + 1) * familySpectralCoeff n h k β 0 cη μ (j + 1)) / β := by
  rw [familySpectralCoeff_population n _ k hk β hβ hη (by linarith) j,
    familySpectralCoeff_population n h k hk β hβ hη hμ j,
    familySpectralCoeff_population n h k hk β hβ hη hμ (j + 1)]
  exact kernelFunctional_add_two_k n h k hk hβ hμ j hη

/-- Population coefficients vanish above the top log degree. -/
theorem population_coeff_eq_zero_of_gt_degree (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
{β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) {j : ℕ}
    (hj : n < j) : familySpectralCoeff n h k β 0 cη μ j = 0 := by
  rw [familySpectralCoeff_population n h k hk β hβ hη hμ j]
  unfold kernelFunctional
  simp [kernelS_eq_zero_of_lt n h k β 0 0 μ hj]

end Grammar
