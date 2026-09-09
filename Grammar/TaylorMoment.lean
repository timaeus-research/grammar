/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MomentFunctional
import Grammar.CoeffFamily
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# The Taylor–moment contraction and the Taylor–moment representation

For an observable `F` with a convergent power series `p` at the origin of the normal space, the
homogeneous Taylor term is the degree-`r` diagonal of the series (`homogeneousTaylor_eq_series`,
from Mathlib's `HasFPowerSeriesOnBall.factorial_smul`), hence the **finite-degree contraction**
`(1/r!) ⟨Moment_{η,r}, D^r F(0)⟩ = ∫ p_r(u,…,u) dη` (`moment_contraction`), and, summing over the
degree with a moment domination, the **absolutely convergent Taylor–moment representation**
`∫ F dη = ∑_r (1/r!) ⟨Moment_{η,r}, D^r F(0)⟩` (`integral_eq_tsum_moment`).  A measure carried by a
ball of radius below the radius of convergence supplies the domination
(`summable_norm_mul_integral_of_ae_le`).

In coordinates (`E = ℝ^d`), when `p` realises a coefficient family `c` — its degree-`r` diagonal
is `∑_{|γ|=r} c_γ u^γ` (`RealisesCoeff`) — the contraction is the paper's
`∑_{|γ|=r} D_γF · M̃_γ` with the **dressed moments** `M̃_γ = ∫ u^γ dη`
(`moment_contraction_coeff`), and `∫ F dη = ∑_r ∑_{|γ|=r} c_γ M̃_γ`
(`integral_eq_tsum_coeff_moment`).

Non-claim (the paper's `eq:tubular_expansion` trap): the degree grading is not the asymptotic
grading — for a phase such as `x²y²` higher normal degrees contribute at the same power of `N`.  The
theorems here are exact convergent identities; the power–log asymptotics are those of the chart
theorem, obtained from the same integral.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open MonoRep

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
  {p : FormalMultilinearSeries ℝ E ℝ} {R : ℝ≥0∞}

/-- The homogeneous Taylor term of an analytic function is the diagonal of its series. -/
theorem homogeneousTaylor_eq_series (hp : HasFPowerSeriesOnBall F p 0 R) (r : ℕ) (u : E) :
    homogeneousTaylor F r u = p r fun _ => u := by
  unfold homogeneousTaylor normalJet
  rw [← hp.factorial_smul u r, nsmul_eq_mul, inv_mul_cancel_left₀ (by positivity)]

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Finite-degree contraction**: `(1/r!) ⟨Moment_{η,r}, D^r F(0)⟩ = ∫ p_r(u,…,u) dη`. -/
theorem moment_contraction (hp : HasFPowerSeriesOnBall F p 0 R) (η : Measure E) {r : ℕ}
    (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    (r.factorial : ℝ)⁻¹ * momentFunctional η hr (normalJet F r) = ∫ u, p r (fun _ => u) ∂η := by
  rw [momentFunctional_apply, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => homogeneousTaylor_eq_series hp r u)

/-- **The Taylor–moment representation**: for a measure carried by the ball of convergence with
finite moments dominated by the series, `∫ F dη = ∑_r (1/r!) ⟨Moment_{η,r}, D^r F(0)⟩`,
absolutely convergent. -/
theorem integral_eq_tsum_moment (hp : HasFPowerSeriesOnBall F p 0 R) (η : Measure E)
    (hη : ∀ᵐ u ∂η, u ∈ Metric.eball (0 : E) R) (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) η)
    (hdom : Summable fun r => ‖p r‖ * ∫ u, ‖u‖ ^ r ∂η) :
    ∫ u, F u ∂η = ∑' r, (r.factorial : ℝ)⁻¹ * momentFunctional η (hr r) (normalJet F r) := by
  have h1 : ∫ u, F u ∂η = ∫ u, ∑' r, p r (fun _ => u) ∂η := by
    refine integral_congr_ae ?_
    filter_upwards [hη] with u hu
    have := hp.hasSum hu
    rw [zero_add] at this
    exact this.tsum_eq.symm
  have hnn : ∀ r, 0 ≤ ‖p r‖ * ∫ u, ‖u‖ ^ r ∂η := fun r =>
    mul_nonneg (norm_nonneg _) (integral_nonneg fun u => pow_nonneg (norm_nonneg u) r)
  rw [h1, integral_tsum (fun r => (continuous_diagEval (p r)).aestronglyMeasurable) ?_]
  · exact tsum_congr fun r => (moment_contraction hp η (hr r)).symm
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' r, ‖p r‖ * ∫ u, ‖u‖ ^ r ∂η)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hdom]
    refine ENNReal.tsum_le_tsum fun r => ?_
    calc ∫⁻ u, ‖p r fun _ => u‖ₑ ∂η ≤ ∫⁻ u, ENNReal.ofReal (‖p r‖ * ‖u‖ ^ r) ∂η := by
          refine lintegral_mono fun u => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_diagEval_le (p r) u)
      _ = ENNReal.ofReal (‖p r‖ * ∫ u, ‖u‖ ^ r ∂η) := by
          rw [← integral_const_mul,
            ofReal_integral_eq_lintegral_ofReal ((hr r).const_mul _)
              (Eventually.of_forall fun u => by positivity)]

omit [NormedSpace ℝ E] in
/-- Bounded support gives every moment. -/
theorem integrable_norm_pow_of_ae_le (η : Measure E) [IsFiniteMeasure η] {ρ : ℝ}
    (hρ : ∀ᵐ (u : E) ∂η, ‖u‖ ≤ ρ) (r : ℕ) : Integrable (fun u => ‖u‖ ^ r) η := by
  refine (integrable_const (ρ ^ r)).mono' (continuous_norm.pow r).aestronglyMeasurable ?_
  filter_upwards [hρ] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg u) hu r

/-- A measure carried by a ball of radius below the radius of convergence satisfies the moment
domination of `integral_eq_tsum_moment`. -/
theorem summable_norm_mul_integral_of_ae_le (η : Measure E) [IsFiniteMeasure η] {ρ : ℝ≥0}
    (hρ : ∀ᵐ (u : E) ∂η, ‖u‖ ≤ ρ) (hR : (ρ : ℝ≥0∞) < p.radius) :
    Summable fun r => ‖p r‖ * ∫ u, ‖u‖ ^ r ∂η := by
  have hs := (p.summable_norm_mul_pow hR).mul_right (η univ).toReal
  refine Summable.of_nonneg_of_le (fun r =>
    mul_nonneg (norm_nonneg _) (integral_nonneg fun u => pow_nonneg (norm_nonneg u) r))
    (fun r => ?_) hs
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (p r))
  calc ∫ u : E, ‖u‖ ^ r ∂η ≤ ∫ _u : E, (ρ : ℝ) ^ r ∂η := by
        refine integral_mono_ae (integrable_norm_pow_of_ae_le η hρ r) (integrable_const _) ?_
        filter_upwards [hρ] with u hu
        exact pow_le_pow_left₀ (norm_nonneg u) hu r
    _ = (ρ : ℝ) ^ r * (η univ).toReal := by rw [integral_const, smul_eq_mul, mul_comm]; rfl

end General

/-! ### Coordinates: dressed moments and the coefficient form -/

section Coeff

variable {d : ℕ}

theorem abs_mono_le_norm_pow (γ : Fin d → ℕ) (u : Fin d → ℝ) : |mono γ u| ≤ ‖u‖ ^ (∑ i, γ i) := by
  unfold mono
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm u i

theorem continuous_mono (γ : Fin d → ℕ) : Continuous (mono γ) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

variable (η : Measure (Fin d → ℝ))

/-- The dressed moment `M̃_γ = ∫ u^γ dη`. -/
noncomputable def dressedMoment (γ : Fin d → ℕ) : ℝ := ∫ u, mono γ u ∂η

theorem integrable_mono (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) η) (γ : Fin d → ℕ) :
    Integrable (mono γ) η :=
  (hr _).mono' (continuous_mono γ).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact abs_mono_le_norm_pow γ u)

/-- A power series realises the coefficient family `c` when its degree-`r` diagonal is the
degree-`r` part `∑_{|γ|=r} c_γ u^γ` of `∑ c_γ u^γ`. -/
def RealisesCoeff (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) (c : CoeffFamily d) : Prop :=
  ∀ (r : ℕ) (u : Fin d → ℝ),
    p r (fun _ => u) = ∑ γ ∈ Finset.Nat.antidiagonalTuple d r, c γ * mono γ u

variable {F : (Fin d → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞}
  {c : CoeffFamily d}

/-- **The contraction in coordinates**: `(1/r!) ⟨Moment_{η,r}, D^rF(0)⟩ = ∑_{|γ|=r} c_γ M̃_γ`. -/
theorem moment_contraction_coeff (hp : HasFPowerSeriesOnBall F p 0 R) (hpc : RealisesCoeff p c)
    (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) η) (r : ℕ) :
    (r.factorial : ℝ)⁻¹ * momentFunctional η (hr r) (normalJet F r) =
      ∑ γ ∈ Finset.Nat.antidiagonalTuple d r, c γ * dressedMoment η γ := by
  rw [moment_contraction hp η (hr r), integral_congr_ae (Eventually.of_forall fun u => hpc r u),
    integral_finsetSum _ fun γ _ => (integrable_mono η hr γ).const_mul _]
  simp_rw [integral_const_mul]
  rfl

/-- **The Taylor–moment representation in coordinates**: `∫ F dη = ∑_r ∑_{|γ|=r} c_γ M̃_γ`. -/
theorem integral_eq_tsum_coeff_moment (hp : HasFPowerSeriesOnBall F p 0 R)
    (hpc : RealisesCoeff p c) (hη : ∀ᵐ u ∂η, u ∈ Metric.eball (0 : Fin d → ℝ) R)
    (hr : ∀ r, Integrable (fun u => ‖u‖ ^ r) η)
    (hdom : Summable fun r => ‖p r‖ * ∫ u, ‖u‖ ^ r ∂η) :
    ∫ u, F u ∂η = ∑' r, ∑ γ ∈ Finset.Nat.antidiagonalTuple d r, c γ * dressedMoment η γ := by
  rw [integral_eq_tsum_moment hp η hη hr hdom]
  exact tsum_congr fun r => moment_contraction_coeff η hp hpc hr r

end Coeff

end Grammar
