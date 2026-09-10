/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.LaplaceExponentBounds

/-!
# The dominant exponent pair of a finite positive family

Finitely many nonnegative contributions with two-sided power–log growth
`L_i ≍ N^{−λ_i}(log N)^{q_i}` sum to a contribution with the **dominant pair**: the smallest `λ`
and, among the contributions attaining it, the largest log degree `q`
(`finset_sum_isTheta_powerLogRate`).  The comparison of
rates is `powerLogRate_isBigO`: `N^{−λ}(log N)^q = O(N^{−λ₀}(log N)^{q₀})` when `λ₀ < λ`, or
`λ = λ₀` and `q ≤ q₀`.  Applied to finitely many localisation data (the chart contributions of a
resolved population integral) this identifies the exponent pair of the total
(`LocalisationData.sum_Z_isTheta`).

Non-claims: identification with the first nonzero canonical coefficient pair; anything about
signed or cancelling contributions.
-/

open MeasureTheory Filter Topology Asymptotics

namespace Grammar

theorem one_le_log_of_exp_le {N : ℝ} (hN : Real.exp 1 ≤ N) : 1 ≤ Real.log N := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos _) hN

theorem one_lt_of_exp_le {N : ℝ} (hN : Real.exp 1 ≤ N) : 1 < N :=
  lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hN

/-- **Comparison of power–log rates**: `N^{−λ}(log N)^q = O(N^{−λ₀}(log N)^{q₀})` when `λ₀ ≤ λ` and,
if `λ = λ₀`, `q ≤ q₀`. -/
theorem powerLogRate_isBigO {lam lam₀ : ℝ} {q q₀ : ℕ} (hle : lam₀ ≤ lam)
    (hq : lam = lam₀ → q ≤ q₀) : powerLogRate lam q =O[atTop] powerLogRate lam₀ q₀ := by
  rcases hle.lt_or_eq with hlt | heq
  · have h1 : (fun N : ℝ => Real.log N ^ q) =o[atTop] fun N => N ^ (lam - lam₀) := by
      have := isLittleO_log_rpow_rpow_atTop (q : ℝ) (sub_pos.2 hlt)
      refine this.congr' ?_ EventuallyEq.rfl
      exact Eventually.of_forall fun N => Real.rpow_natCast _ _
    have h2 : (fun N : ℝ => N ^ (-lam) * N ^ (lam - lam₀)) =ᶠ[atTop] fun N => N ^ (-lam₀) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [← Real.rpow_add hN]
      congr 1; ring
    have h3 : powerLogRate lam q =o[atTop] fun N => N ^ (-lam₀) := by
      have := (isBigO_refl (fun N : ℝ => N ^ (-lam)) atTop).mul_isLittleO h1
      unfold powerLogRate
      exact this.congr' EventuallyEq.rfl h2
    have h4 : (fun N : ℝ => N ^ (-lam₀)) =O[atTop] powerLogRate lam₀ q₀ := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
      have hN1 : 1 ≤ N := (one_lt_of_exp_le hN).le
      rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
        Real.norm_of_nonneg (powerLogRate_nonneg hN1)]
      unfold powerLogRate
      exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _)
        (one_le_pow₀ (one_le_log_of_exp_le hN))
    exact h3.isBigO.trans h4
  · subst heq
    have hq' := hq rfl
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN1 : 1 ≤ N := (one_lt_of_exp_le hN).le
    rw [one_mul, Real.norm_of_nonneg (powerLogRate_nonneg hN1),
      Real.norm_of_nonneg (powerLogRate_nonneg hN1)]
    unfold powerLogRate
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_log_of_exp_le hN) hq')
      (Real.rpow_nonneg (by linarith) _)

/-- **The dominant exponent pair**: finitely many eventually nonnegative contributions
`L_i ≍ N^{−λ_i}(log N)^{q_i}` sum to `≍ N^{−λ₀}(log N)^{q₀}` where `λ₀ = min λ_i` and `q₀` is the
largest `q_i` among the `i` attaining the minimum. -/
theorem finset_sum_isTheta_powerLogRate {ι : Type*} [Fintype ι] (L : ι → ℝ → ℝ) (lam : ι → ℝ)
    (q : ι → ℕ) {lam₀ : ℝ} {q₀ : ℕ} (hL : ∀ i, L i =Θ[atTop] powerLogRate (lam i) (q i))
    (hnn : ∀ i, ∀ᶠ N in atTop, 0 ≤ L i N) (hmin : ∀ i, lam₀ ≤ lam i)
    (hq : ∀ i, lam i = lam₀ → q i ≤ q₀) (hatt : ∃ i, lam i = lam₀ ∧ q i = q₀) :
    (fun N => ∑ i, L i N) =Θ[atTop] powerLogRate lam₀ q₀ := by
  constructor
  · have h : ∀ i ∈ Finset.univ, L i =O[atTop] powerLogRate lam₀ q₀ := fun i _ =>
      (hL i).1.trans (powerLogRate_isBigO (hmin i) (hq i))
    exact (IsBigO.sum h).congr_left fun N => Finset.sum_apply N _ _
  · obtain ⟨i₀, hl, hq0⟩ := hatt
    have h1 : powerLogRate lam₀ q₀ =O[atTop] L i₀ := by rw [← hl, ← hq0]; exact (hL i₀).2
    refine h1.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_all.2 hnn] with N hN
    rw [one_mul, Real.norm_of_nonneg (hN i₀),
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hN i)]
    exact Finset.single_le_sum (fun i _ => hN i) (Finset.mem_univ i₀)

namespace LocalisationData

/-- **The exponent pair of a finite sum of population integrals**: chart contributions with
two-sided sublevel growth and positive bounded observables sum to the dominant pair. -/
theorem sum_Z_isTheta {ι : Type*} [Fintype ι] {U : ι → Type*} [∀ i, MeasurableSpace (U i)]
    (D : ∀ i, LocalisationData (U i)) [∀ i, IsFiniteMeasure (D i).μ] (lam : ι → ℝ) (q : ι → ℕ)
    (h : ∀ i, SublevelTheta (D i).μ (D i).phase (lam i) (q i)) (c C δ : ι → ℝ)
    (hc : ∀ i, 0 < c i) (hδ : ∀ i, 0 < δ i) (hobs0 : ∀ i, 0 ≤ᵐ[(D i).μ] (D i).obs)
    (hobsC : ∀ i, ∀ᵐ z ∂(D i).μ, (D i).obs z ≤ C i)
    (hobsc : ∀ i, ∀ᵐ z ∂(D i).μ, (D i).phase z ≤ δ i → c i ≤ (D i).obs z) {lam₀ : ℝ} {q₀ : ℕ}
    (hmin : ∀ i, lam₀ ≤ lam i) (hq : ∀ i, lam i = lam₀ → q i ≤ q₀)
    (hatt : ∃ i, lam i = lam₀ ∧ q i = q₀) :
    (fun N => ∑ i, (D i).Z N) =Θ[atTop] powerLogRate lam₀ q₀ :=
  finset_sum_isTheta_powerLogRate (fun i => (D i).Z) lam q
    (fun i => (D i).Z_isTheta (h i) (hc i) (hδ i) (hobs0 i) (hobsC i) (hobsc i))
    (fun i => Eventually.of_forall fun N => integral_nonneg_of_ae (by
      filter_upwards [hobs0 i] with z hz
      exact mul_nonneg hz (Real.exp_pos _).le))
    hmin hq hatt

end LocalisationData

end Grammar
