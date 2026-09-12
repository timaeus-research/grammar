/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.JetFamilyOfSeries

/-!
# Polynomial observables in every dimension: series and Taylor family (CCCXI)

The `d`-variable companion of CCCVI. A polynomial observable `P(u) = ∑_γ f_γ u^γ` given by a
finitely supported coefficient family `f : CoeffFamily d` has the power series
`polySeriesD f m = ∑_{|γ|=m} f_γ • (du)^γ_sym` (the normalised symmetric monomials
`symMonomial` of `SymmetricWeights`, whose diagonal values are `u^γ`), of infinite radius,
representing `P` on the whole space (`hasFPowerSeriesOnBall_polyD`); its monomial coefficient
family is `f` (`monoFamily_polySeriesD`: on the words of weight `γ` the symmetric monomial `(du)^γ`
takes the value `1/multinomial(γ)`, and there are `multinomial(γ)` such words), so by CCCIX

* ★ `jetFamily_polyD : jetFamily n (polyD f) = f` — **the Taylor family of a polynomial observable
  is its coefficient family**, in every dimension;
* `absSummableAt_of_finite_support` — finitely supported families are `b`-weighted ℓ¹.

These are the analytic inputs for coefficient certificates with polynomial observables in any
dimension (the tied-crossing instance in dimension two, next).
-/

open Set Filter Topology
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

variable {d : ℕ} (f : CoeffFamily d)

/-- The polynomial `P(u) = ∑_γ f_γ u^γ`. -/
noncomputable def polyD : (Fin d → ℝ) → ℝ := evalF f

/-- The power series `m ↦ ∑_{|γ|=m} f_γ • (du)^γ_sym` of the polynomial. -/
noncomputable def polySeriesD : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ :=
  fun m => ∑ γ ∈ Finset.Nat.antidiagonalTuple d m, f γ • symMonomial (r := m) γ

theorem polySeriesD_apply_diag (m : ℕ) (u : Fin d → ℝ) :
    polySeriesD f m (fun _ => u) = ∑ γ ∈ Finset.Nat.antidiagonalTuple d m, f γ * mono γ u := by
  unfold polySeriesD
  rw [sum_apply]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [smul_apply, smul_eq_mul, symMonomial_apply_diag γ (Finset.Nat.mem_antidiagonalTuple.1 hγ)]

variable {supp : Finset (Fin d → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0)
include hf

theorem absSummableAt_of_finite_support (b : ℝ) : AbsSummableAt f b :=
  summable_of_ne_finset_zero (s := supp) fun γ hγ => by rw [hf γ hγ, abs_zero, zero_mul]

theorem summable_term_polyD (u : Fin d → ℝ) : Summable fun γ => f γ * mono γ u :=
  summable_of_ne_finset_zero (s := supp) fun γ hγ => by rw [hf γ hγ, zero_mul]

theorem polySeriesD_eq_zero (m : ℕ) :
    polySeriesD f (m + (supp.sup fun γ => ∑ i, γ i) + 1) = 0 := by
  unfold polySeriesD
  refine Finset.sum_eq_zero fun γ hγ => ?_
  have hdeg := Finset.Nat.mem_antidiagonalTuple.1 hγ
  rw [hf γ, zero_smul]
  intro hmem
  have : ∑ i, γ i ≤ supp.sup fun γ => ∑ i, γ i :=
    Finset.le_sup (f := fun γ : Fin d → ℕ => ∑ i, γ i) hmem
  omega

theorem radius_polySeriesD : (polySeriesD f).radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _
    ((supp.sup fun γ => ∑ i, γ i) + 1) fun m => by
      rw [← add_assoc]
      exact polySeriesD_eq_zero f hf m

/-- **The polynomial is represented by its series on the whole space.** -/
theorem hasFPowerSeriesOnBall_polyD : HasFPowerSeriesOnBall (polyD f) (polySeriesD f) 0 ⊤ where
  r_le := by rw [radius_polySeriesD f hf]
  r_pos := ENNReal.zero_lt_top
  hasSum := by
    intro y _
    rw [zero_add]
    have hsum := summable_term_polyD f hf y
    have hdeg : HasSum (fun x : Σ r : ℕ, {γ : Fin d → ℕ // ∑ i, γ i = r} =>
        f x.2.1 * mono x.2.1 y) (polyD f y) := by
      have := (degreeEquiv (Fin d)).hasSum_iff.2 hsum.hasSum
      exact this.congr_fun fun x => rfl
    refine hdeg.sigma fun m => ?_
    rw [polySeriesD_apply_diag]
    have hs : HasSum (fun γ : {γ : Fin d → ℕ // ∑ i, γ i = m} => f γ.1 * mono γ.1 y)
        (∑ γ ∈ (Finset.Nat.antidiagonalTuple d m).subtype (fun γ => ∑ i, γ i = m),
          f γ.1 * mono γ.1 y) :=
      hasSum_sum_of_ne_finset_zero fun γ hγ =>
        absurd (Finset.mem_subtype.2 (Finset.Nat.mem_antidiagonalTuple.2 γ.2)) hγ
    convert hs using 1
    rw [Finset.sum_subtype_eq_sum_filter (f := fun γ => f γ * mono γ y),
      Finset.filter_true_of_mem fun γ hγ => Finset.Nat.mem_antidiagonalTuple.1 hγ]

omit hf

/-! ### The monomial coefficient family of the series -/

theorem symMonomial_apply_word {m : ℕ} (γ : Fin d → ℕ) (w : Fin m → Fin d) :
    symMonomial (r := m) γ (fun j => Pi.single (w j) 1) =
      if weightOf w = γ then (Nat.multinomial Finset.univ γ : ℝ)⁻¹ else 0 := by
  unfold symMonomial
  rw [smul_apply, smul_eq_mul]
  have := jetComponent_weightForm (r := m) γ w
  unfold jetComponent at this
  rw [this]
  split_ifs <;> simp

theorem polySeriesD_apply_word {m : ℕ} (w : Fin m → Fin d) :
    polySeriesD f m (fun j => Pi.single (w j) 1) =
      f (weightOf w) * (Nat.multinomial Finset.univ (weightOf w) : ℝ)⁻¹ := by
  unfold polySeriesD
  rw [sum_apply]
  simp_rw [smul_apply, smul_eq_mul, symMonomial_apply_word]
  rw [Finset.sum_eq_single (weightOf w)]
  · rw [if_pos rfl]
  · intro γ _ hγ
    rw [if_neg (Ne.symm hγ), mul_zero]
  · intro h
    exact absurd (Finset.Nat.mem_antidiagonalTuple.2 (sum_weightOf w)) h

/-- ★ **The monomial coefficient family of the polynomial series is the coefficient family.** -/
theorem monoFamily_polySeriesD : monoFamily (polySeriesD f) = f := by
  funext γ
  unfold monoFamily monoCoeff
  simp_rw [polySeriesD_apply_word]
  have hfib : (Finset.univ : Finset (Fin (∑ i, γ i) → Fin d)).filter (fun w => wordMult w = γ) =
      weightFibre γ := rfl
  rw [hfib, Finset.sum_congr rfl fun w hw => by
    rw [(mem_weightFibre.1 hw : weightOf w = γ)]]
  rw [Finset.sum_const, card_weightFibre γ rfl, nsmul_eq_mul]
  have hM : (Nat.multinomial Finset.univ γ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  field_simp

/-- ★ **The Taylor family of a polynomial observable is its coefficient family** (every
dimension). -/
theorem jetFamily_polyD {n : ℕ} (f : CoeffFamily (n + 1)) {supp : Finset (Fin (n + 1) → ℕ)}
    (hf : ∀ γ ∉ supp, f γ = 0) : jetFamily n (polyD f) = f := by
  rw [jetFamily_eq_monoFamily (hasFPowerSeriesOnBall_polyD f hf), monoFamily_polySeriesD]

end Grammar
