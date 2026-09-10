import Grammar.ExpGapLocalisation
import Grammar.SamplingIdentity

/-!
# The positive-gap remainder for the empirical phase

Away from the zero set of the phase, `K = φ² ≥ κ > 0`, the sampling exponent
`−βnφ² + β√n φ ξ_n` is dominated by `−βnκ/2` as soon as the fluctuation is bounded by
`sup |ξ_n| ≤ ½√(nκ)` (`empirical_phase_le`): the cross term `β√n φ ξ_n` is at most half the
Gaussian term. Hence, for an integrable amplitude envelope `g ≥ ‖a‖`,

`‖∫_S a(u) e^{−βnφ(u)² + β√n φ(u) ξ(u)} du‖ ≤ e^{−βnκ/2} ∫_S g`

(`norm_setIntegral_empirical_exp_gap_le`), also written for the sampling exponent
`−β ∑ᵢ f(Xᵢ, u)` itself through the sampling identity `N = n`, `ξ_n = −ζ_n`
(`norm_setIntegral_sampling_exp_gap_le`), and in `O(e^{−βNκ/2})` form along a family with an
eventual fluctuation bound (`empirical_exp_gap_isBigO`); combined with
`exp_gap_isLittleO_powLog` the remainder is `o` of every power–log scale.

Non-claim: a pathwise bound `B_n = o(√n)`, or `B_n = O_P(1)`, does not by itself give an
exponentially small *expected* remainder; that needs a tail estimate on the exceptional datasets.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- **The empirical phase is dominated by half the population phase** on the gap region: if
`κ ≤ φ²`, `|ξ| ≤ B` and `2B ≤ √(Nκ)`, then `−βNφ² + β√N φ ξ ≤ −βNκ/2`. -/
theorem empirical_phase_le {β N κ φ ξ B : ℝ} (hβ : 0 ≤ β) (hN : 0 ≤ N)
    (hφ : κ ≤ φ ^ 2) (hξ : |ξ| ≤ B) (hB : 2 * B ≤ Real.sqrt (N * κ)) :
    -β * N * φ ^ 2 + β * Real.sqrt N * φ * ξ ≤ -(β * N * κ / 2) := by
  have hsq : Real.sqrt (N * κ) ≤ Real.sqrt N * |φ| := by
    rw [Real.sqrt_mul hN, ← Real.sqrt_sq_eq_abs]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hφ) (Real.sqrt_nonneg _)
  have hN' : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hcross : φ * ξ ≤ |φ| * B := by
    calc φ * ξ ≤ |φ * ξ| := le_abs_self _
      _ = |φ| * |ξ| := abs_mul _ _
      _ ≤ |φ| * B := mul_le_mul_of_nonneg_left hξ (abs_nonneg _)
  have h1 : β * Real.sqrt N * φ * ξ ≤ β * Real.sqrt N * (|φ| * B) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcross (mul_nonneg hβ (Real.sqrt_nonneg _))
  have h2 : Real.sqrt N * (|φ| * B) ≤ N * φ ^ 2 / 2 := by
    have : 2 * (Real.sqrt N * (|φ| * B)) ≤ Real.sqrt N * |φ| * (Real.sqrt N * |φ|) := by
      calc 2 * (Real.sqrt N * (|φ| * B)) = Real.sqrt N * |φ| * (2 * B) := by ring
        _ ≤ Real.sqrt N * |φ| * Real.sqrt (N * κ) :=
          mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        _ ≤ Real.sqrt N * |φ| * (Real.sqrt N * |φ|) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    have hsqφ : Real.sqrt N * |φ| * (Real.sqrt N * |φ|) = N * φ ^ 2 := by
      rw [show Real.sqrt N * |φ| * (Real.sqrt N * |φ|) = (Real.sqrt N * Real.sqrt N) * (|φ| * |φ|)
        by ring, hN', abs_mul_abs_self, sq]
    linarith
  have h3 : β * (Real.sqrt N * (|φ| * B)) ≤ β * (N * φ ^ 2 / 2) := mul_le_mul_of_nonneg_left h2 hβ
  have h4 : β * N * κ ≤ β * N * φ ^ 2 := mul_le_mul_of_nonneg_left hφ (mul_nonneg hβ hN)
  nlinarith [h1, h3, h4]

/-- The empirical exponent as a population exponent with phase `φ² − φξ/√N`, for `N > 0`. -/
theorem empirical_exponent_eq {β N φ ξ : ℝ} (hN : 0 < N) :
    -β * N * φ ^ 2 + β * Real.sqrt N * φ * ξ = -(β * N * (φ ^ 2 - φ * ξ / Real.sqrt N)) := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have hN' : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have h : N / Real.sqrt N = Real.sqrt N := by
    rw [div_eq_iff hs]
    exact hN'.symm
  calc -β * N * φ ^ 2 + β * Real.sqrt N * φ * ξ
      = -(β * N * φ ^ 2) + β * φ * ξ * (N / Real.sqrt N) := by rw [h]; ring
    _ = -(β * N * (φ ^ 2 - φ * ξ / Real.sqrt N)) := by ring

/-- **The positive-gap remainder for the empirical phase.** On a region where `κ ≤ φ²` and
`|ξ| ≤ B` with `2B ≤ √(Nκ)`, `‖∫_S a e^{−βNφ² + β√N φ ξ}‖ ≤ e^{−βNκ/2} ∫_S g` whenever `‖a‖ ≤ g`. -/
theorem norm_setIntegral_empirical_exp_gap_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (S : Set X) (hS : MeasurableSet S) (a g φ ξ : X → ℝ) (β N κ B : ℝ) (hβ : 0 ≤ β) (hN : 0 < N)
    (ha : AEStronglyMeasurable a (μ.restrict S))
    (hφ : AEStronglyMeasurable φ (μ.restrict S)) (hξ : AEStronglyMeasurable ξ (μ.restrict S))
    (hg : IntegrableOn g S μ) (hbound : ∀ x ∈ S, ‖a x‖ ≤ g x) (hgap : ∀ x ∈ S, κ ≤ φ x ^ 2)
    (hfl : ∀ x ∈ S, |ξ x| ≤ B) (hB : 2 * B ≤ Real.sqrt (N * κ)) :
    ‖∫ x in S, a x * Real.exp (-β * N * φ x ^ 2 + β * Real.sqrt N * φ x * ξ x) ∂μ‖ ≤
      Real.exp (-(β * N * (κ / 2))) * ∫ x in S, g x ∂μ := by
  have hf : ∀ x, -β * N * φ x ^ 2 + β * Real.sqrt N * φ x * ξ x =
      -(β * N * (φ x ^ 2 - φ x * ξ x / Real.sqrt N)) := fun x => empirical_exponent_eq hN
  simp_rw [hf]
  refine norm_setIntegral_exp_gap_le S hS a g (fun x => φ x ^ 2 - φ x * ξ x / Real.sqrt N) β N
    (κ / 2) (mul_nonneg hβ hN.le) ha ?_ hg hbound fun x hx => ?_
  · simp only [div_eq_mul_inv]
    exact (hφ.pow 2).sub ((hφ.mul hξ).mul_const (Real.sqrt N)⁻¹)
  · -- `φ² − φξ/√N ≥ κ/2` from `empirical_phase_le` with `β = 1`
    have h := empirical_phase_le (β := 1) zero_le_one hN.le (hgap x hx) (hfl x hx) hB
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hN' : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
    have hdiv : φ x * ξ x / Real.sqrt N ≤ φ x ^ 2 - κ / 2 := by
      rw [div_le_iff₀ hs0]
      have h' : Real.sqrt N * (φ x * ξ x) ≤ Real.sqrt N * ((φ x ^ 2 - κ / 2) * Real.sqrt N) := by
        have e : Real.sqrt N * ((φ x ^ 2 - κ / 2) * Real.sqrt N) = N * φ x ^ 2 - N * κ / 2 := by
          rw [show Real.sqrt N * ((φ x ^ 2 - κ / 2) * Real.sqrt N) =
            (Real.sqrt N * Real.sqrt N) * (φ x ^ 2 - κ / 2) by ring, hN']
          ring
        rw [e]
        linarith
      exact le_of_mul_le_mul_left h' hs0
    linarith

/-- **The positive-gap remainder for the sampling exponent.** With `f(x,u) = φ(u) a(x,u)` and the
empirical fluctuation `ζ_n(u) = n^{−1/2} ∑ᵢ (a(Xᵢ,u) − φ(u))`, on a region where `κ ≤ φ²` and
`|ζ_n| ≤ B` with `2B ≤ √(nκ)`:
`‖∫_S η(u) e^{−β ∑ᵢ f(Xᵢ,u)} du‖ ≤ e^{−βnκ/2} ∫_S g`. -/
theorem norm_setIntegral_sampling_exp_gap_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (S : Set X) (hS : MeasurableSet S) (η g φ : X → ℝ) (a : ℕ → X → ℝ) (n : ℕ) (hn : 0 < n)
    (β κ B : ℝ) (hβ : 0 ≤ β) (hη : AEStronglyMeasurable η (μ.restrict S))
    (hφ : AEStronglyMeasurable φ (μ.restrict S))
    (hζ : AEStronglyMeasurable (fun x => zetaEmp n (fun i => a i x) (φ x)) (μ.restrict S))
    (hg : IntegrableOn g S μ) (hbound : ∀ x ∈ S, ‖η x‖ ≤ g x) (hgap : ∀ x ∈ S, κ ≤ φ x ^ 2)
    (hfl : ∀ x ∈ S, |zetaEmp n (fun i => a i x) (φ x)| ≤ B) (hB : 2 * B ≤ Real.sqrt (n * κ)) :
    ‖∫ x in S, η x * Real.exp (-β * ∑ i ∈ Finset.range n, φ x * a i x) ∂μ‖ ≤
      Real.exp (-(β * n * (κ / 2))) * ∫ x in S, g x ∂μ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [sampling_exponent_eq n hn _ _ β]
  exact norm_setIntegral_empirical_exp_gap_le S hS η g φ
    (fun x => -zetaEmp n (fun i => a i x) (φ x)) β n κ B hβ hn' hη hφ hζ.neg hg hbound hgap
    (fun x hx => by rw [abs_neg]; exact hfl x hx) hB

/-- **Big-O form**: along a family of amplitudes dominated by a fixed integrable `g` on the gap
region, with fluctuations eventually bounded by `½√(Nκ)`, the remainder is `O(e^{−βNκ/2})`. -/
theorem empirical_exp_gap_isBigO {X : Type*} [MeasurableSpace X] {μ : Measure X} (S : Set X)
    (hS : MeasurableSet S) (a : ℝ → X → ℝ) (g φ : X → ℝ) (ξ : ℝ → X → ℝ) (β κ : ℝ) (hβ : 0 ≤ β)
    (ha : ∀ N, AEStronglyMeasurable (a N) (μ.restrict S))
    (hφ : AEStronglyMeasurable φ (μ.restrict S))
    (hξ : ∀ N, AEStronglyMeasurable (ξ N) (μ.restrict S))
    (hg : IntegrableOn g S μ) (hbound : ∀ N, ∀ x ∈ S, ‖a N x‖ ≤ g x)
    (hgap : ∀ x ∈ S, κ ≤ φ x ^ 2)
    (hfl : ∀ᶠ N in atTop, ∀ x ∈ S, |ξ N x| ≤ Real.sqrt (N * κ) / 2) :
    (fun N => ∫ x in S, a N x * Real.exp (-β * N * φ x ^ 2 + β * Real.sqrt N * φ x * ξ N x) ∂μ)
      =O[atTop] fun N => Real.exp (-(β * N * (κ / 2))) := by
  refine IsBigO.of_bound (∫ x in S, g x ∂μ) ?_
  filter_upwards [hfl, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  rw [Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  exact (norm_setIntegral_empirical_exp_gap_le S hS (a N) g φ (ξ N) β N κ (Real.sqrt (N * κ) / 2)
    hβ hN0 (ha N) hφ (hξ N) hg (hbound N) hgap hN (by linarith)).trans (le_of_eq (mul_comm _ _))

end Grammar
