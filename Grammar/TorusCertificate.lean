/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolyCoeffMeasurable
import Grammar.SampleExpansion

/-!
# The torus `L²` certificate and the chart moment certificate

The chart moment certificate of the `ℓ¹` CLT (`SampleDatum.lean`) follows from a **torus `L²`
envelope**: a jointly measurable family `a : 𝓧 → (Fin d → ℂ) → ℂ` of chart functions with
`‖a x w‖ ≤ M x` on the torus of radius `R` and `M ∘ X₀ ∈ L²(P)`.  The chart coefficients are the
real Cauchy coefficients `c x γ := polyRealCoeff d R (a x) γ`; they are measurable in `x`
(`measurable_polyCoeff_param`), bounded by `M x R^{−|γ|}` (Cauchy estimate `norm_polyCoeff_le`),
absolutely summable at every radius `b < R` (`absSummableAt_certCoeff`), in `L²` along the sample
(`memLp_certCoeff`), with the envelope `‖c_γ(X₀)‖_{L²} ≤ ‖M(X₀)‖_{L²} R^{−|γ|}`
(`sqrt_integral_certCoeff_sq_le`), hence the chart moment certificate (`summable_certCoeff`) and
the stochastic expansion at the sample datum (`sample_stochastic_expansion_of_torus`).

No holomorphy is used: the coefficient moment argument needs only measurable torus data and an
envelope.  Holomorphy enters only for the analytic identification of the coefficients with the
Taylor coefficients of `a` (next unit).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

/-- A torus `L²` certificate for a family of chart functions: joint measurability and a torus
envelope at radius `R`. -/
structure TorusCertificate (𝓧 : Type*) [MeasurableSpace 𝓧] (d : ℕ) (R : ℝ) where
  /-- the chart functions -/
  a : 𝓧 → (Fin d → ℂ) → ℂ
  /-- the envelope -/
  M : 𝓧 → ℝ
  R_pos : 0 < R
  measurable_a : Measurable fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2
  measurable_M : Measurable M
  M_nonneg : ∀ x, 0 ≤ M x
  torus_bound : ∀ x w, w ∈ torusSet d R → ‖a x w‖ ≤ M x

namespace TorusCertificate

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {d : ℕ} {R : ℝ} (C : TorusCertificate 𝓧 d R)

/-- The chart coefficient family of a sample point: real Cauchy coefficients at radius `R`. -/
noncomputable def coeff (x : 𝓧) : CoeffFamily d := polyRealCoeff d R (C.a x)

theorem measurable_coeff (γ : Fin d → ℕ) : Measurable fun x => C.coeff x γ :=
  measurable_polyRealCoeff_param R C.measurable_a γ

/-- The Cauchy estimate `|c_γ(x)| ≤ M x R^{−|γ|}`. -/
theorem abs_coeff_le (x : 𝓧) (γ : Fin d → ℕ) : |C.coeff x γ| ≤ C.M x * R⁻¹ ^ (∑ i, γ i) :=
  (Complex.abs_re_le_norm _).trans (norm_polyCoeff_le C.R_pos (C.torus_bound x) γ)

/-- Absolute summability at every radius `b < R`. -/
theorem absSummableAt_coeff {b : ℝ} (hb : 0 < b) (hbR : b < R) (x : 𝓧) :
    AbsSummableAt (C.coeff x) b := by
  unfold AbsSummableAt
  have hgeom := (summable_prodGeom d (q := fun _ => b / R) (fun _ => (div_pos hb C.R_pos).le)
    (fun _ => (div_lt_one C.R_pos).2 hbR)).mul_left (C.M x)
  refine Summable.of_nonneg_of_le (fun γ => mul_nonneg (abs_nonneg _) (pow_nonneg hb.le _))
    (fun γ => ?_) hgeom
  calc |C.coeff x γ| * b ^ (∑ i, γ i) ≤ C.M x * R⁻¹ ^ (∑ i, γ i) * b ^ (∑ i, γ i) :=
        mul_le_mul_of_nonneg_right (C.abs_coeff_le x γ) (pow_nonneg hb.le _)
    _ = C.M x * ∏ i, (b / R) ^ γ i := by
        rw [Finset.prod_pow_eq_pow_sum, div_pow, div_eq_mul_inv, inv_pow]; ring

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → 𝓧)
  (hX₀ : Measurable X₀) (hM : MemLp (fun ω => C.M (X₀ ω)) 2 P)
include hX₀ hM

omit [IsProbabilityMeasure P] in
/-- The chart coefficients of the sample are in `L²`. -/
theorem memLp_coeff (γ : Fin d → ℕ) : MemLp (fun ω => C.coeff (X₀ ω) γ) 2 P := by
  refine (hM.const_mul (R⁻¹ ^ (∑ i, γ i))).mono'
    ((C.measurable_coeff γ).comp hX₀).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, mul_comm]
  exact C.abs_coeff_le (X₀ ω) γ

omit [IsProbabilityMeasure P] in
/-- The `L²` envelope `‖c_γ(X₀)‖_{L²} ≤ ‖M(X₀)‖_{L²} R^{−|γ|}`. -/
theorem sqrt_integral_coeff_sq_le (γ : Fin d → ℕ) :
    Real.sqrt (∫ ω, (C.coeff (X₀ ω) γ) ^ 2 ∂P) ≤
      Real.sqrt (∫ ω, (C.M (X₀ ω)) ^ 2 ∂P) * R⁻¹ ^ (∑ i, γ i) := by
  have h1 : ∫ ω, (C.coeff (X₀ ω) γ) ^ 2 ∂P ≤ ∫ ω, (C.M (X₀ ω) * R⁻¹ ^ (∑ i, γ i)) ^ 2 ∂P := by
    refine integral_mono_ae (C.memLp_coeff P X₀ hX₀ hM γ).integrable_sq
      (hM.const_mul (R⁻¹ ^ (∑ i, γ i)) |>.integrable_sq.congr ?_) (Eventually.of_forall fun ω => ?_)
    · exact Eventually.of_forall fun ω => by simp [mul_comm]
    · have := C.abs_coeff_le (X₀ ω) γ
      calc (C.coeff (X₀ ω) γ) ^ 2 = |C.coeff (X₀ ω) γ| ^ 2 := (sq_abs _).symm
        _ ≤ (C.M (X₀ ω) * R⁻¹ ^ (∑ i, γ i)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) this 2
  calc Real.sqrt (∫ ω, (C.coeff (X₀ ω) γ) ^ 2 ∂P)
      ≤ Real.sqrt (∫ ω, (C.M (X₀ ω) * R⁻¹ ^ (∑ i, γ i)) ^ 2 ∂P) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (∫ ω, (C.M (X₀ ω)) ^ 2 ∂P) * R⁻¹ ^ (∑ i, γ i) := by
        simp_rw [mul_pow]
        rw [integral_mul_const, Real.sqrt_mul' _ (sq_nonneg _),
          Real.sqrt_sq (pow_nonneg (inv_nonneg.2 C.R_pos.le) _)]

/-- **The chart moment certificate** from the torus `L²` certificate, at every radius `b < R`. -/
theorem summable_coeff {b : ℝ} (hb : 0 < b) (hbR : b < R) :
    Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (C.coeff (X₀ ω) γ) ^ 2 ∂P) :=
  summable_of_cauchy_envelope b hb C.coeff (X := fun _ => X₀) (P := P) C.R_pos hbR fun γ =>
    C.sqrt_integral_coeff_sq_le P X₀ hX₀ hM γ

end Sample

end TorusCertificate

/-- **The stochastic expansion at the sample datum under a torus `L²` certificate**: for an i.i.d.
sample `X` with `M ∘ X₀ ∈ L²` and a box radius `b < R`, the conclusions of
`sample_stochastic_expansion` hold for the chart coefficients `c x = polyRealCoeff d R (a x)`. -/
theorem sample_stochastic_expansion_of_torus {n : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] {R : ℝ}
    (C : TorusCertificate 𝓧 (n + 1) R) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {b : ℝ} (hb : 0 < b) (hbR : b < R) (X : ℕ → Ω → 𝓧)
    (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hM : MemLp (fun ω => C.M (X 0 ω)) 2 P) (A : DataSpace (n + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      TendstoInDistribution (sampleDatum b hb C.coeff (C.absSummableAt_coeff hb hbR) P X A) atTop
        (fun x => x + A) (fun _ => P) (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      (∀ {m : ℕ} (F : Fin m → ℝ × ℕ),
        TendstoInDistribution (fun i => dataCoeffVec n h k β b F ∘
          sampleDatum b hb C.coeff (C.absSummableAt_coeff hb hbR) P X A i)
          atTop (dataCoeffVec n h k β b F ∘ fun x => x + A) (fun _ => P)
          (ν : Measure (L1Seq (DataIdx (n + 1))))) ∧
      (∀ {m : ℕ} (F : Fin m → ℝ × ℕ),
        (∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n) →
        ∀ (Nseq : ℕ → ℝ), (∀ i, 0 ≤ Nseq i) → Tendsto Nseq atTop atTop →
        TendstoInDistribution (fun i ω => orderedRemainderVec n h k β b F
            (sampleDatum b hb C.coeff (C.absSummableAt_coeff hb hbR) P X A i ω) (Nseq i))
          atTop (fun x => dataCoeffVec n h k β b F (x + A)) (fun _ => P)
          (ν : Measure (L1Seq (DataIdx (n + 1))))) ∧
      ∀ F : Finset (DataIdx (n + 1)), (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F
          (sampleObs b hb C.coeff (C.absSummableAt_coeff hb hbR) X 0 ω)) P :=
  sample_stochastic_expansion P b hb C.coeff (C.absSummableAt_coeff hb hbR) X h k hk β hβ
    C.measurable_coeff hXm hXind hXid (C.memLp_coeff P (X 0) (hXm 0) hM)
    (C.summable_coeff P (X 0) (hXm 0) hM hb hbR) A

end Grammar
