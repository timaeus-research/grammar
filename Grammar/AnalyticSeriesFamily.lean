/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PolynomialTaylorFamily

/-!
# Weighted-ℓ¹ coefficient families define analytic functions on the box (CCCXVII)

Consult #95 unit 2, analytic input. A `b'`-weighted ℓ¹ coefficient family `f`
(`∑_γ |f_γ| b'^{|γ|} < ∞`) defines the function `evalF f u = ∑_γ f_γ u^γ`, which is represented by
the symmetric-monomial power series `polySeriesD f` on the ball of radius `b'`
(`hasFPowerSeriesOnBall_evalF`: the series terms have norm at most the degree-`m`
mass,
`norm_polySeriesD_le`, since `‖(du)^γ_sym‖ ≤ 1`, `norm_symMonomial_le_one`; the diagonal sums
are the
degree fibration of the absolutely convergent monomial series). Consequently the Taylor family of
`evalF f` is `f` itself (`jetFamily_evalF`, via CCCIX), and the product of two such functions on
the box has the Cauchy-product family (`evalF_conv_of_absSummableAt`, the scaled `evalF_conv`).

These are exactly the analytic inputs of a coefficient certificate for series data on a box of
side `b < b'`: the density family, the observable family, and their Cauchy product as the
amplitude datum.
-/

open Set Filter Topology
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

variable {d : ℕ}

/-! ### Norms of the symmetric monomials -/

theorem norm_monomialForm_le_one {r : ℕ} (m : Fin r → Fin d) : ‖monomialForm m‖ ≤ 1 := by
  unfold monomialForm
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hproj : ∀ j : Fin r, ‖(ContinuousLinearMap.proj (m j) : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    intro j
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact norm_le_pi_norm x (m j)
  have hprod : ∏ j : Fin r, ‖(ContinuousLinearMap.proj (m j) : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => hproj j
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · rw [ContinuousMultilinearMap.norm_mkPiAlgebra_of_empty, norm_one, one_mul]
    exact hprod
  · calc ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ *
          ∏ j, ‖(ContinuousLinearMap.proj (m j) : (Fin d → ℝ) →L[ℝ] ℝ)‖
        ≤ 1 * 1 := mul_le_mul ContinuousMultilinearMap.norm_mkPiAlgebra_le hprod
          (Finset.prod_nonneg fun j _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_symMonomial_le_one {r : ℕ} (γ : Fin d → ℕ) (hγ : ∑ i, γ i = r) :
    ‖symMonomial (r := r) γ‖ ≤ 1 := by
  unfold symMonomial weightForm
  rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  have hM : (0 : ℝ) < Nat.multinomial Finset.univ γ := by exact_mod_cast Nat.multinomial_pos _ _
  calc (Nat.multinomial Finset.univ γ : ℝ)⁻¹ * ‖∑ m ∈ weightFibre γ, monomialForm m‖
      ≤ (Nat.multinomial Finset.univ γ : ℝ)⁻¹ * ∑ m ∈ weightFibre γ, ‖monomialForm m‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hM.le)
    _ ≤ (Nat.multinomial Finset.univ γ : ℝ)⁻¹ * ∑ _m ∈ weightFibre γ, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => norm_monomialForm_le_one m)
          (inv_nonneg.2 hM.le)
    _ = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_weightFibre γ hγ, inv_mul_cancel₀ hM.ne']

/-! ### The series of a weighted-ℓ¹ family -/

variable (f : CoeffFamily d) {b' : ℝ} (hb' : 0 < b') (hf : AbsSummableAt f b')
include hb' hf

/-- The degree-`m` mass `∑_{|γ|=m} |f_γ| b'^m` is at most the total weighted mass. -/
theorem norm_polySeriesD_le (m : ℕ) :
    ‖polySeriesD f m‖ * b' ^ m ≤ ∑' γ, |f γ| * b' ^ (∑ i, γ i) := by
  unfold polySeriesD
  have h1 : ‖∑ γ ∈ Finset.Nat.antidiagonalTuple d m, f γ • symMonomial (r := m) γ‖ ≤
      ∑ γ ∈ Finset.Nat.antidiagonalTuple d m, |f γ| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ hγ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (norm_symMonomial_le_one γ (Finset.Nat.mem_antidiagonalTuple.1 hγ))
  calc ‖∑ γ ∈ Finset.Nat.antidiagonalTuple d m, f γ • symMonomial (r := m) γ‖ * b' ^ m
      ≤ (∑ γ ∈ Finset.Nat.antidiagonalTuple d m, |f γ|) * b' ^ m :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hb'.le _)
    _ = ∑ γ ∈ Finset.Nat.antidiagonalTuple d m, |f γ| * b' ^ (∑ i, γ i) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun γ hγ => by
          rw [Finset.Nat.mem_antidiagonalTuple.1 hγ]
    _ ≤ ∑' γ, |f γ| * b' ^ (∑ i, γ i) :=
        hf.sum_le_tsum _ (fun γ _ => by positivity)

/-- The radius of the series is at least `b'`. -/
theorem le_radius_polySeriesD : ENNReal.ofReal b' ≤ (polySeriesD f).radius := by
  have h := (polySeriesD f).le_radius_of_bound (∑' γ, |f γ| * b' ^ (∑ i, γ i))
    (r := ⟨b', hb'.le⟩) fun m => norm_polySeriesD_le f hb' hf m
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hb'.le]
  exact h

omit hb' in
theorem summable_term_evalF {y : Fin d → ℝ} (hy : ‖y‖ ≤ b') : Summable fun γ => f γ * mono γ y := by
  refine Summable.of_norm_bounded hf fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold mono
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm y i).trans hy) _

/-- ★ **A weighted-ℓ¹ family defines an analytic function on the ball of radius `b'`**,
represented by its symmetric-monomial series. -/
theorem hasFPowerSeriesOnBall_evalF :
    HasFPowerSeriesOnBall (evalF f) (polySeriesD f) 0 (ENNReal.ofReal b') where
  r_le := le_radius_polySeriesD f hb' hf
  r_pos := by rwa [ENNReal.ofReal_pos]
  hasSum := by
    intro y hy
    rw [zero_add]
    have hy' : ‖y‖ ≤ b' := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 hy).le
    have hsum := summable_term_evalF f hf hy'
    have hdeg : HasSum (fun x : Σ r : ℕ, {γ : Fin d → ℕ // ∑ i, γ i = r} =>
        f x.2.1 * mono x.2.1 y) (evalF f y) := by
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

omit hb' hf in
/-- ★ **The Taylor family of `evalF f` is `f`** (every dimension, weighted-ℓ¹ family). -/
theorem jetFamily_evalF {n : ℕ} (f : CoeffFamily (n + 1)) {b' : ℝ} (hb' : 0 < b')
    (hf : AbsSummableAt f b') : jetFamily n (evalF f) = f := by
  rw [jetFamily_eq_monoFamily (hasFPowerSeriesOnBall_evalF f hb' hf), monoFamily_polySeriesD]

/-! ### Products on the box -/

omit hb' hf in
/-- **The scaled product rule**: on the box `0 ≤ u_i ≤ b`, `evalF (f ⋆ g) = evalF f · evalF g` for
`b`-weighted ℓ¹ families. -/
theorem evalF_conv_of_absSummableAt {f g : CoeffFamily d} {b : ℝ} (hb : 0 < b)
    (hf : AbsSummableAt f b) (hg : AbsSummableAt g b) {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ b) :
    evalF (CoeffFamily.conv f g) u = evalF f u * evalF g u := by
  set v : Fin d → ℝ := b⁻¹ • u with hv
  have hbv : b • v = u := by rw [hv, smul_inv_smul₀ hb.ne']
  have hvc : v ∈ closedCube d := by
    intro i _
    simp only [hv, Pi.smul_apply, smul_eq_mul, mem_Icc]
    obtain ⟨h0, h1⟩ := hu i
    constructor
    · exact mul_nonneg (inv_nonneg.2 hb.le) h0
    · rw [inv_mul_le_iff₀ hb, mul_one]
      exact h1
  have hsf : AbsSummable (scale f b) := AbsSummable.of_scale hb.le hf
  have hsg : AbsSummable (scale g b) := AbsSummable.of_scale hb.le hg
  calc evalF (CoeffFamily.conv f g) u
      = evalF (scale (CoeffFamily.conv f g) b) v := by rw [evalF_scale, hbv]
    _ = evalF (CoeffFamily.conv (scale f b) (scale g b)) v := by rw [scale_conv]
    _ = evalF (scale f b) v * evalF (scale g b) v := evalF_conv hsf hsg hvc
    _ = evalF f u * evalF g u := by rw [evalF_scale, evalF_scale, hbv]

end Grammar
