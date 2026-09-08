/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FamilyCoeffSeries

/-!
# Collapse of the population coefficient series (grammar §3 rewrite, Astra #37 P1, unit 291)

At zero phase the Taylor-tree coefficient series `A_{μ,j}(cξ,cη) = ∑_p β^p/p! T_p(cη * J^{*p})`
(Headline XXIX) collapses to its `p = 0` term: the constant-free part `J` of the zero family is
zero, its positive convolution powers vanish, and the `p = 0` convolution power is the delta at
`γ = 0`, so `cη * J^{*0} = cη`. Hence
```
familyCoeffSeries n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη
                                   = K_k ∑_γ cη_γ S_0(μ,j;γ),
```
the paper's dressed-moment expansion `∑_γ (η_γ/γ!)·[coefficient of N^{-μ}(log N)^j in M_{h+γ}]`
(`eq:tubular_expansion`) with `S_0(μ,j;γ) = ∑_{q≥j} coeffAt(ρ_{h+γ},μ,q) C(q,j)
fluctMoment β 0 0 μ (q−j)` (`kernelS`). Under absolute summability of `cη` and `μ > 0` this is the
canonical (limit-defined) family coefficient (`familySpectralCoeff_population`).

These are algebraic identities; they do not by themselves assert convergence of the inner
amplitude series (`kernelFunctional` is a `tsum`), which is supplied by the admissibility
hypotheses of the Taylor tree. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- The constant-free part of the zero family is zero. -/
theorem CoeffFamily.fluctFamily_zero : fluctFamily (0 : CoeffFamily d) = 0 := by
  funext γ
  unfold fluctFamily
  split_ifs <;> rfl

/-- Convolution with the zero family on the left. -/
theorem CoeffFamily.conv_zero_left (e : CoeffFamily d) : conv (0 : CoeffFamily d) e = 0 := by
  funext γ
  simp [conv]

/-- Convolution with the zero family on the right. -/
theorem CoeffFamily.conv_zero_right (c : CoeffFamily d) : conv c (0 : CoeffFamily d) = 0 := by
  funext γ
  simp [conv]

/-- Positive convolution powers of the zero family vanish. -/
theorem CoeffFamily.convPow_zero_family {p : ℕ} (hp : p ≠ 0) :
    convPow (0 : CoeffFamily d) p = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  simp [convPow, conv_zero_left]

/-- Convolution with the zeroth convolution power (the delta family at `γ = 0`) is the
identity. -/
theorem CoeffFamily.conv_convPow_zero (c e : CoeffFamily d) : conv c (convPow e 0) = c := by
  funext γ
  simp only [convPow, conv]
  rw [Finset.sum_eq_single γ]
  · simp
  · intro α hα hne
    have hle : α ≤ γ := Finset.mem_Iic.1 hα
    have hsub : γ - α ≠ 0 := by
      intro h0
      apply hne
      refine le_antisymm hle fun i => ?_
      have hi := congrFun h0 i
      simp only [Pi.sub_apply, Pi.zero_apply] at hi
      exact Nat.sub_eq_zero_iff_le.1 hi
    simp [hsub]
  · intro hγ
    exact absurd (Finset.mem_Iic.2 le_rfl) hγ

/-- The kernel functional of the zero family vanishes. -/
theorem kernelFunctional_zero_family (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) : kernelFunctional n h k β a p μ j (0 : CoeffFamily (n + 1)) = 0 := by
  simp [kernelFunctional]

/-- At zero phase every coefficient term of positive fluctuation order vanishes. -/
theorem familyCoeffTerm_population_ne (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) {p : ℕ} (hp : p ≠ 0) :
    familyCoeffTerm n h k β 0 cη μ j p = 0 := by
  unfold familyCoeffTerm
  rw [fluctFamily_zero, convPow_zero_family hp, conv_zero_right, kernelFunctional_zero_family,
    mul_zero]

/-- At zero phase the `p = 0` coefficient term is the kernel functional of the amplitude family
with zero constant phase: `K_k ∑_γ cη_γ S_0(μ,j;γ)`. -/
theorem familyCoeffTerm_population_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffTerm n h k β 0 cη μ j 0 = kernelFunctional n h k β 0 0 μ j cη := by
  unfold familyCoeffTerm
  rw [fluctFamily_zero, conv_convPow_zero]
  simp

/-- **Collapse of the population coefficient series**: at zero phase the Taylor-tree coefficient
series is its `p = 0` term. -/
theorem familyCoeffSeries_population_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffSeries n h k β 0 cη μ j = familyCoeffTerm n h k β 0 cη μ j 0 := by
  unfold familyCoeffSeries
  exact tsum_eq_single 0 fun p hp => familyCoeffTerm_population_ne n h k β cη μ j hp

/-- The population coefficient series is the dressed-moment kernel functional
`K_k ∑_γ cη_γ S_0(μ,j;γ)` of the amplitude family. -/
theorem familyCoeffSeries_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffSeries n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη := by
  rw [familyCoeffSeries_population_term, familyCoeffTerm_population_zero]

/-- The canonical population coefficient (the limit-defined family spectral coefficient at zero
phase) is the dressed-moment kernel functional, for absolutely summable amplitude data and
`μ > 0`. -/
theorem familySpectralCoeff_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη := by
  have h0 : AbsSummable (0 : CoeffFamily (n + 1)) := by
    simp [AbsSummable]
  rw [familySpectralCoeff_eq_series n h k hk β hβ h0 hη hμ j, familyCoeffSeries_population]

end Grammar
