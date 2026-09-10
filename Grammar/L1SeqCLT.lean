/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1SeqGaussianLimit

/-!
# The central limit theorem in `ℓ¹` under summable coordinate `L²` norms

For i.i.d. `ℓ¹(ι, ℝ)`-valued observations `Y_i` (countable `ι`) with coordinates in `L²` and
summable coordinate `L²` norms `∑_j ‖Y_{0,j}‖_{L²} < ∞`, the normalised centred empirical sums
`S_n = n^{−1/2} ∑_{i<n} (Y_i − E Y_0)` converge in distribution in `ℓ¹` to a probability law `ν`
whose finite coordinate marginals are the centred Gaussians with the covariance of the
corresponding coordinates of `Y_0`, and which carries the tail bounds `∫ ‖x − T_F x‖ dν ≤
∑_{j∉F} σ_j` (`clt_l1`).  The proof assembles the `ℓ¹` upgrade (finite coordinate convergence plus
uniform tails), the finite-dimensional CLT, the uniform empirical tail estimates, and the Gaussian
limit extracted by tightness.

Non-claim: this is not an `ℓ¹` CLT under `MemLp Y 2` alone — `ℓ¹` is not of type 2, and the
summable coordinate `L²` norms are the essential extra hypothesis.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} [Countable ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0))
  (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
  (hYm : ∀ i, Measurable (Y i))
include hY hindep hident hYm

/-- Finite coordinate projections of the empirical sums converge in distribution to the
corresponding marginal of a law `ν` with Gaussian finite marginals. -/
theorem tendstoInDistribution_finiteCoords_empiricalSum {ν : ProbabilityMeasure (L1Seq ι)}
    (F : Finset ι) (hν : (ν : Measure (L1Seq ι)).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P) :
    TendstoInDistribution (fun n ω => finiteCoords F (empiricalSum Y P n ω)) atTop
      (fun x => finiteCoords F x) (fun _ => P) (ν : Measure (L1Seq ι)) := by
  have h := tendstoInDistribution_normalisedSum_gaussian (memLp_finiteCoords_comp hY F)
    (iIndepFun_finiteCoords_comp hindep F) (identDistrib_finiteCoords_comp hident F)
  have hXm : ∀ n, AEMeasurable (fun ω => finiteCoords F (empiricalSum Y P n ω)) P := fun n =>
    ((finiteCoords F).continuous.measurable.comp (measurable_empiricalSum hY hYm n)).aemeasurable
  refine ⟨hXm, (finiteCoords F).continuous.measurable.aemeasurable, ?_⟩
  have h2 := h.tendsto
  have e1 : ∀ n, P.map (fun ω => finiteCoords F (empiricalSum Y P n ω)) =
      P.map (normalisedSum (fun i ω => finiteCoords F (Y i ω)) P n) := fun n => by
    congr 1
    funext ω
    exact finiteCoords_empiricalSum (integrable_of_summableCoordL2 P hY) F n ω
  have e2 : (ν : Measure (L1Seq ι)).map (finiteCoords F) =
      (gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P).map id := by
    rw [Measure.map_id, hν]
  refine Iff.mpr ProbabilityMeasure.tendsto_iff_forall_integral_tendsto fun f => ?_
  have h3 := Iff.mp ProbabilityMeasure.tendsto_iff_forall_integral_tendsto h2 f
  simp only [ProbabilityMeasure.coe_mk] at h3 ⊢
  simp_rw [e1, e2]
  exact h3

/-- **The central limit theorem in `ℓ¹`**: under summable coordinate `L²` norms, the normalised
centred empirical sums converge in distribution in `ℓ¹` to a law `ν` with centred Gaussian finite
coordinate marginals (covariance of `Y_0`) and tails `∫ ‖x − T_F x‖ dν ≤ ∑_{j∉F} σ_j`. -/
theorem clt_l1 : ∃ ν : ProbabilityMeasure (L1Seq ι),
    TendstoInDistribution (empiricalSum Y P) atTop id (fun _ => P) (ν : Measure (L1Seq ι)) ∧
    (∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P) ∧
    ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
      ENNReal.ofReal (sigmaTail P (Y 0) F) := by
  obtain ⟨ν, hmarg, htails⟩ := exists_gaussianLimit hY hindep hident hYm
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  refine ⟨ν, ?_, hmarg, htails⟩
  refine tendstoInDistribution_of_finiteCoords (F := F) (measurable_empiricalSum hY hYm)
    measurable_id (fun k => ?_) (fun k => sigmaTail_nonneg (Y 0) (F k))
    (tendsto_sigmaTail (Y 0) hF hcov)
    (fun k n => lintegral_enorm_sub_truncate_empirical_le hY hindep hident hYm (F k) n)
    (fun k => htails (F k))
  exact tendstoInDistribution_finiteCoords_empiricalSum hY hindep hident hYm (F k) (hmarg (F k))

end Grammar
