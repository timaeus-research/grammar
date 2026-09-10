import Grammar.CompactBaseFinite
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The Gaussian Banach-law adapter: Fernique discharges the second sup-norm moment

The record `GaussianField 𝒞 P` carries an explicit hypothesis `E‖G‖²_∞ < ∞`. For a random element
`G : Ω → C(K,ℝ)` that is Borel measurable for the sup-norm topology and whose law `P.map G` is a
Gaussian measure in Mathlib's sense (`ProbabilityTheory.IsGaussian`: every continuous linear
functional has a real Gaussian law), Fernique's theorem — available in Mathlib as
`IsGaussian.memLp_id`, the finiteness of all moments of the identity — supplies that hypothesis
(`integrable_sq_norm_of_isGaussian`, `integrable_sq_norm_comp_of_isGaussian`), and continuity of
the evaluations supplies their measurability. The constructor `GaussianField.ofIsGaussian` builds
the record from the Gaussian Banach law together with the finite-dimensional-law certificate.

Non-claims: Gaussianity of the Banach law does not fix the mean, so the evaluation-law certificate
(which is a *centred* Gaussian vector law with the kernel covariance) is kept as an input; the
Gaussian law on `C(K,ℝ)` is a hypothesis, not constructed from the kernel; the Borel σ-algebra on
`C(K,ℝ)` is declared locally (Mathlib does not provide a global instance).
-/

open MeasureTheory ProbabilityTheory

namespace Grammar

section Fernique

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-- The Borel σ-algebra of the sup-norm topology on `C(K,ℝ)`. -/
local instance instMeasurableSpaceContinuousMap : MeasurableSpace C(K, ℝ) := borel _

local instance instBorelSpaceContinuousMap : BorelSpace C(K, ℝ) := ⟨rfl⟩

/-- **Fernique (via Mathlib)**: a Gaussian Borel law on `C(K,ℝ)` has a finite second sup-norm
moment. -/
theorem integrable_sq_norm_of_isGaussian (μ : Measure C(K, ℝ)) [IsGaussian μ] :
    Integrable (fun f : C(K, ℝ) => ‖f‖ ^ 2) μ := by
  have h := (IsGaussian.memLp_id μ 2 (by norm_num)).integrable_norm_rpow (by norm_num)
    (by norm_num)
  simpa [Real.rpow_two] using h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [CompactSpace K] in
/-- Evaluations of a Borel-measurable random continuous function are measurable. -/
theorem measurable_eval_comp {G : Ω → C(K, ℝ)} (hG : Measurable G) (x : K) :
    Measurable fun ω => G ω x :=
  (ContinuousMap.evalCLM ℝ x).continuous.measurable.comp hG

/-- Pullback of the Fernique moment along a random element with Gaussian law. -/
theorem integrable_sq_norm_comp_of_isGaussian {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] : Integrable (fun ω => ‖G ω‖ ^ 2) P :=
  (integrable_map_measure (continuous_norm.pow 2).measurable.aestronglyMeasurable
    hG.aemeasurable).1 (integrable_sq_norm_of_isGaussian (P.map G))

/-- **The Gaussian Banach-law adapter**: a Borel-measurable `C(K,ℝ)`-valued random element with a
Gaussian law and the finite-dimensional-law certificate is a `GaussianField`; the second sup-norm
moment is discharged by Fernique. -/
noncomputable def GaussianField.ofIsGaussian (𝒞 : PSDKernel K) (P : Measure Ω) (G : Ω → C(K, ℝ))
    (hG : Measurable G) [IsGaussian (P.map G)]
    (law : ∀ (m : ℕ) (x : Fin m → K), ∃ (n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ),
      A * A.transpose = 𝒞.kernelMatrix x ∧
        P.map (fun ω => fun i => G ω (x i)) = gaussianVector A) :
    GaussianField 𝒞 P where
  G := G
  measurable_eval := measurable_eval_comp hG
  integrable_sq_norm := integrable_sq_norm_comp_of_isGaussian hG
  law := law

@[simp] theorem GaussianField.ofIsGaussian_G (𝒞 : PSDKernel K) (P : Measure Ω)
    (G : Ω → C(K, ℝ)) (hG : Measurable G) [IsGaussian (P.map G)] (law) :
    (GaussianField.ofIsGaussian 𝒞 P G hG law).G = G := rfl

end Fernique

end Grammar
