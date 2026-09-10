/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation

/-!
# The variance normalisation on the divisor

In the standard form `f = φ a` with `E e^{−f} = 1` (likelihood normalisation) and `E f = φ² h`, the
coefficient `a` has second moment `E a² = 2h + O(|φ|)`: explicitly (`abs_integral_sq_sub_le`)

  `|E[a²] − 2h| ≤ 2 |φ| E[|a|³ e^{|φ a|}]`,

from the pointwise exponential remainder bound `|e^{−z} − (1 − z + z²/2)| ≤ |z|³ e^{|z|}`
(`abs_exp_neg_sub_le`, Mathlib's `Complex.norm_exp_sub_sum_le_norm_mul_exp`).  Consequently, along
any approach to a divisor point (`φ → 0`, `h → h₀`) with a uniform cubic envelope, `E a² → 2h₀`
(`tendsto_integral_sq`), and if the coefficients converge in `L²` the divisor coefficient has
`E a₀² = 2h₀` exactly (`integral_sq_eq_of_tendsto`): with `K = φ²` (`h = 1`) the covariance
diagonal on the divisor is `2`.  The statement with merely `φ → 0` and arbitrary `K = E f` is
false (consult #56, B1), so `h` is carried explicitly.
-/

open MeasureTheory Filter Topology

namespace Grammar

/-- **The exponential remainder bound**: `|e^{−z} − (1 − z + z²/2)| ≤ |z|³ e^{|z|}`. -/
theorem abs_exp_neg_sub_le (z : ℝ) :
    |Real.exp (-z) - (1 - z + z ^ 2 / 2)| ≤ |z| ^ 3 * Real.exp |z| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(z : ℂ)) 3
  have hsum : ∑ m ∈ Finset.range 3, (-(z : ℂ)) ^ m / (m.factorial : ℂ) =
      ((1 - z + z ^ 2 / 2 : ℝ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  have hexp : Complex.exp (-(z : ℂ)) = ((Real.exp (-z) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_exp]
  rw [hsum, hexp, ← Complex.ofReal_sub, Complex.norm_real, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The variance normalisation**: if `E e^{−φ a} = 1`, `E a = φ h` and the cubic envelope
`|a|³ e^{|φ a|}` is integrable, then `|E a² − 2h| ≤ 2|φ| E[|a|³ e^{|φ a|}]`. -/
theorem abs_integral_sq_sub_le {a : Ω → ℝ} {φ h : ℝ} (hφ : φ ≠ 0)
    (hexp : ∫ ω, Real.exp (-(φ * a ω)) ∂P = 1) (hmean : ∫ ω, a ω ∂P = φ * h)
    (hint1 : Integrable a P) (hint2 : Integrable (fun ω => a ω ^ 2) P)
    (hint3 : Integrable (fun ω => Real.exp (-(φ * a ω))) P)
    (hint4 : Integrable (fun ω => |a ω| ^ 3 * Real.exp |φ * a ω|) P) :
    |(∫ ω, a ω ^ 2 ∂P) - 2 * h| ≤ 2 * |φ| * ∫ ω, |a ω| ^ 3 * Real.exp |φ * a ω| ∂P := by
  -- the remainder `r = e^{−φa} − (1 − φa + φ²a²/2)`
  set r : Ω → ℝ := fun ω => Real.exp (-(φ * a ω)) - (1 - φ * a ω + (φ * a ω) ^ 2 / 2) with hr
  have hrint : Integrable r P := by
    refine hint3.sub ((integrable_const 1).sub (hint1.const_mul φ) |>.add ?_)
    have := hint2.const_mul (φ ^ 2 / 2)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hrbound : ∀ ω, |r ω| ≤ |φ| ^ 3 * (|a ω| ^ 3 * Real.exp |φ * a ω|) := by
    intro ω
    calc |r ω| = |Real.exp (-(φ * a ω)) - (1 - φ * a ω + (φ * a ω) ^ 2 / 2)| := rfl
      _ ≤ |φ * a ω| ^ 3 * Real.exp |φ * a ω| := abs_exp_neg_sub_le (φ * a ω)
      _ = |φ| ^ 3 * (|a ω| ^ 3 * Real.exp |φ * a ω|) := by rw [abs_mul, mul_pow]; ring
  -- `∫ r = φ² (h − E a²/2)`
  have hrint_eq : ∫ ω, r ω ∂P = φ ^ 2 * (h - (∫ ω, a ω ^ 2 ∂P) / 2) := by
    have h1 : Integrable (fun ω => 1 - φ * a ω + (φ * a ω) ^ 2 / 2) P := by
      refine ((integrable_const 1).sub (hint1.const_mul φ)).add ?_
      have := hint2.const_mul (φ ^ 2 / 2)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only; ring
    have h2 : Integrable (fun ω => 1 - φ * a ω) P := (integrable_const 1).sub (hint1.const_mul φ)
    have h3 : Integrable (fun ω => (φ * a ω) ^ 2 / 2) P := by
      have := hint2.const_mul (φ ^ 2 / 2)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only; ring
    have hsq : ∫ ω, (φ * a ω) ^ 2 / 2 ∂P = φ ^ 2 / 2 * ∫ ω, a ω ^ 2 ∂P := by
      rw [← integral_const_mul]
      congr 1; funext ω; ring
    calc ∫ ω, r ω ∂P
        = (∫ ω, Real.exp (-(φ * a ω)) ∂P) - ((∫ ω, (1 : ℝ) ∂P) - φ * ∫ ω, a ω ∂P) -
            ∫ ω, (φ * a ω) ^ 2 / 2 ∂P := by
          simp only [hr]
          rw [integral_sub hint3 h1, integral_add h2 h3, integral_sub (integrable_const 1)
            (hint1.const_mul φ), integral_const_mul]
          ring
      _ = φ ^ 2 * (h - (∫ ω, a ω ^ 2 ∂P) / 2) := by
          rw [hexp, hmean, hsq, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
            one_smul]
          ring
  -- the bound
  have hbound : |∫ ω, r ω ∂P| ≤ |φ| ^ 3 * ∫ ω, |a ω| ^ 3 * Real.exp |φ * a ω| ∂P := by
    calc |∫ ω, r ω ∂P| ≤ ∫ ω, |r ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |φ| ^ 3 * (|a ω| ^ 3 * Real.exp |φ * a ω|) ∂P :=
          integral_mono hrint.abs (hint4.const_mul _) hrbound
      _ = _ := integral_const_mul _ _
  rw [hrint_eq, abs_mul, abs_of_nonneg (sq_nonneg φ)] at hbound
  have hφ2 : 0 < φ ^ 2 := by positivity
  have hφ3 : |φ| ^ 3 = φ ^ 2 * |φ| := by
    rw [pow_succ, sq_abs]
  rw [hφ3, mul_assoc] at hbound
  have h' := le_of_mul_le_mul_left hbound hφ2
  have : |(∫ ω, a ω ^ 2 ∂P) - 2 * h| = 2 * |h - (∫ ω, a ω ^ 2 ∂P) / 2| := by
    rw [abs_sub_comm, ← abs_two, ← abs_mul]
    congr 1; ring
  rw [this]
  nlinarith [h']

/-- **`E a² → 2h₀` along an approach to the divisor** (`φ → 0`, `h → h₀`) with a uniform cubic
envelope `E[|a_t|³ e^{|φ_t a_t|}] ≤ M`. -/
theorem tendsto_integral_sq {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {φ h : ι → ℝ} {h₀ M : ℝ}
    (hφ0 : ∀ᶠ t in l, φ t ≠ 0) (hφ : Tendsto φ l (𝓝 0)) (hh : Tendsto h l (𝓝 h₀))
    (hexp : ∀ t, ∫ ω, Real.exp (-(φ t * a t ω)) ∂P = 1) (hmean : ∀ t, ∫ ω, a t ω ∂P = φ t * h t)
    (hint1 : ∀ t, Integrable (a t) P) (hint2 : ∀ t, Integrable (fun ω => a t ω ^ 2) P)
    (hint3 : ∀ t, Integrable (fun ω => Real.exp (-(φ t * a t ω))) P)
    (hint4 : ∀ t, Integrable (fun ω => |a t ω| ^ 3 * Real.exp |φ t * a t ω|) P)
    (hM : ∀ t, ∫ ω, |a t ω| ^ 3 * Real.exp |φ t * a t ω| ∂P ≤ M) :
    Tendsto (fun t => ∫ ω, a t ω ^ 2 ∂P) l (𝓝 (2 * h₀)) := by
  have hM0 : ∀ t, 0 ≤ M := fun t => (integral_nonneg fun ω => by positivity).trans (hM t)
  -- `|E a_t² − 2h_t| ≤ 2M|φ_t| → 0`
  have hdiff : Tendsto (fun t => (∫ ω, a t ω ^ 2 ∂P) - 2 * h t) l (𝓝 0) := by
    have hbound : Tendsto (fun t => 2 * M * |φ t|) l (𝓝 0) := by
      have := (hφ.abs).const_mul (2 * M)
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hφ0] with t ht
    rw [Real.norm_eq_abs]
    calc |(∫ ω, a t ω ^ 2 ∂P) - 2 * h t|
        ≤ 2 * |φ t| * ∫ ω, |a t ω| ^ 3 * Real.exp |φ t * a t ω| ∂P :=
          abs_integral_sq_sub_le ht (hexp t) (hmean t) (hint1 t) (hint2 t) (hint3 t) (hint4 t)
      _ ≤ 2 * |φ t| * M := mul_le_mul_of_nonneg_left (hM t) (by positivity)
      _ = 2 * M * |φ t| := by ring
  have := hdiff.add (hh.const_mul 2)
  simpa using this

/-- **The divisor coefficient has `E a₀² = 2h₀`**: if in addition the second moments converge to
that of a limit coefficient `a₀` (e.g. `a_t → a₀` in `L²`), then `E a₀² = 2h₀`. -/
theorem integral_sq_eq_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {a : ι → Ω → ℝ}
    {a₀ : Ω → ℝ} {φ h : ι → ℝ} {h₀ M : ℝ}
    (hφ0 : ∀ᶠ t in l, φ t ≠ 0) (hφ : Tendsto φ l (𝓝 0)) (hh : Tendsto h l (𝓝 h₀))
    (hexp : ∀ t, ∫ ω, Real.exp (-(φ t * a t ω)) ∂P = 1) (hmean : ∀ t, ∫ ω, a t ω ∂P = φ t * h t)
    (hint1 : ∀ t, Integrable (a t) P) (hint2 : ∀ t, Integrable (fun ω => a t ω ^ 2) P)
    (hint3 : ∀ t, Integrable (fun ω => Real.exp (-(φ t * a t ω))) P)
    (hint4 : ∀ t, Integrable (fun ω => |a t ω| ^ 3 * Real.exp |φ t * a t ω|) P)
    (hM : ∀ t, ∫ ω, |a t ω| ^ 3 * Real.exp |φ t * a t ω| ∂P ≤ M)
    (hlim : Tendsto (fun t => ∫ ω, a t ω ^ 2 ∂P) l (𝓝 (∫ ω, a₀ ω ^ 2 ∂P))) :
    ∫ ω, a₀ ω ^ 2 ∂P = 2 * h₀ :=
  tendsto_nhds_unique hlim
    (tendsto_integral_sq hφ0 hφ hh hexp hmean hint1 hint2 hint3 hint4 hM)

end Variance

end Grammar
