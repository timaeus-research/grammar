/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TaylorTreeDerivatives
import Grammar.EmpiricalBoxScaling

/-!
# The canonical empirical coefficients are the Taylor-tree series (§20, explicit coefficients)

The smooth engine's canonical cube coefficients `empCoeffRect η ξ h k b μ j` (§20 Stage 6) and the
Taylor tree's explicit series coefficients `boxCoeff n h k β b cξ cη μ j` (Headline XXVIII/XXXIII)
are both cutoff-independent coefficient systems of the same standard integral
`Z(N) = ∫_{(0,b]^d} η u^h e^{−N u^{2k} + √N u^k ξ(u)} du` whenever `ξ, η` have holomorphic
extensions to a polydisc of radius `R > b`.  By the uniqueness of cutoff expansions they agree:

* `empIntegralRect_eq_origPhaseIntegral`: the rectangular empirical integral on the cube at
  `β = 1` is the Taylor-tree programme's original standard integral;
* `cutoffExpansion_of_taylorTreeConclusion`: a Taylor-tree conclusion is a `CutoffExpansion` with
  the box coefficients;
* ★★ `empCoeffRect_eq_boxCoeff`: under the paper's holomorphic-polydisc hypothesis, on the common
  lattice and for every log degree `≤ d − 1`, `empCoeffRect η ξ h k b μ j = boxCoeff … μ j`;
* ★★ `empCoeffRect_eq_taylorSeries`: the same with the box coefficient unfolded to the paper's
  explicit absolutely convergent series `∑_p β^p/p! T_p(cη ∗ J^{∗p})` (`familyCoeffSeries`) of the
  scaled Taylor-derivative families of the extensions, with the binomial re-expansion of the box
  scale — `eq:ExpansionCoefficient` for the canonical coefficients.

No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics
open scoped ContDiff

namespace Grammar

variable {n : ℕ}

/-- The rectangular empirical integral on the cube `(0,b]^{n+1}` at `β = 1` is the Taylor-tree
programme's original standard integral. -/
theorem empIntegralRect_eq_origPhaseIntegral (η ξ : (Fin (n + 1) → ℝ) → ℝ)
    (h k : Fin (n + 1) → ℕ) (b N : ℝ) :
    SmoothEngine.empIntegralRect η ξ h k (fun _ => b) N = origPhaseIntegral n h k 1 N b ξ η := by
  unfold SmoothEngine.empIntegralRect origPhaseIntegral
  have hset : SmoothEngine.rect (fun _ : Fin (n + 1) => b) = piBox (n + 1) (Ioc 0 b) := by
    ext z
    simp [SmoothEngine.rect, piBox, Set.mem_pi]
  rw [hset]
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u _ => ?_
  unfold SmoothEngine.mono
  simp only [one_mul]
  congr 2
  ring

/-- A Taylor-tree conclusion is a cutoff expansion of the family integral with the box
coefficients. -/
theorem cutoffExpansion_of_taylorTreeConclusion {h k : Fin (n + 1) → ℕ} {β b : ℝ} (hb : 0 < b)
    {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ} (hC : TaylorTreeConclusion n h k β b cξ cη C) :
    CutoffExpansion (latticeQ k) n (fun N => familyPhaseIntegralBox n h k β N b cξ cη)
      (boxCoeff n h k β b cξ cη) := by
  intro L hL
  obtain ⟨c, hc⟩ := (hC.isBigO L hL).bound
  refine ⟨c, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnn : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (pow_nonneg (by linarith) _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn] at hN
  unfold absSpectralSum
  rw [← boxSpectralSum_eq n h k β L hb cξ cη hN0]
  exact hN

/-- ★★ **The canonical empirical coefficients are the Taylor-tree box coefficients.**  For real
`ξ, η` on the cube with holomorphic extensions `Fξ, Fη` to the polydisc of radius `R > b`
(real-part agreement on the positive box), on the lattice `(2∏kᵢ)⁻¹ℕ` and for `j ≤ d − 1`,
the smooth engine's canonical coefficient of `∫ η u^h e^{−N u^{2k} + √N u^k ξ} du` is the
Taylor tree's box coefficient of the Taylor-derivative families of the extensions. -/
theorem empCoeffRect_eq_boxCoeff (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {b R : ℝ}
    (hb : 0 < b) (hbR : b < R) {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u)
    (hξs : ContDiff ℝ ∞ ξ) (hηs : ContDiff ℝ ∞ η) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / SmoothEngine.Qamb k) {j : ℕ} (hj : j ≤ n) :
    SmoothEngine.empCoeffRect η ξ h k (fun _ => b) μ j =
      boxCoeff n h k 1 b (taylorFamily (n + 1) Fξ) (taylorFamily (n + 1) Fη) μ j := by
  obtain ⟨C, hC, hZ⟩ := thm_TaylorTree_taylor n h k hk 1 one_pos hb hbR hFξ hFη hξ hη
  have hcut := cutoffExpansion_of_taylorTreeConclusion hb hC
  have hfun : (fun N => familyPhaseIntegralBox n h k 1 N b (taylorFamily (n + 1) Fξ)
      (taylorFamily (n + 1) Fη)) = SmoothEngine.empIntegralRect η ξ h k (fun _ => b) :=
    funext fun N => by rw [hZ N, empIntegralRect_eq_origPhaseIntegral]
  rw [hfun] at hcut
  exact (SmoothEngine.empCoeffRect_unique hηs hξs hk (fun _ => hb) hcut hμ hj).symm

/-- The box coefficient of a Taylor-tree conclusion, unfolded to the paper's explicit series. -/
theorem boxCoeff_eq_series {h k : Fin (n + 1) → ℕ} {β b : ℝ} {cξ cη : CoeffFamily (n + 1)}
    {C : ℝ → ℕ → ℝ} (hC : TaylorTreeConclusion n h k β b cξ cη C) (μ : ℝ) (j : ℕ) :
    boxCoeff n h k β b cξ cη μ j =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
        ∑ q ∈ Finset.Ico j (n + 1),
          familyCoeffSeries n h k β (CoeffFamily.scale cξ b) (CoeffFamily.scale cη b) μ q *
            (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) := by
  unfold boxCoeff
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← hC.coeff_eq μ q, hC.series μ q]

/-- ★★ **The canonical empirical coefficients as the paper's explicit series**
(`eq:ExpansionCoefficient`): under the holomorphic-polydisc hypothesis the canonical coefficient
`empCoeffRect η ξ h k b μ j` is the box-scale binomial re-expansion of the absolutely convergent
Taylor-tree series `∑_p 1/p! T_p(cη ∗ J^{∗p})` of the scaled Taylor-derivative families
`γ ↦ Re(∂^γ Fξ(0)/γ!)`, `γ ↦ Re(∂^γ Fη(0)/γ!)`. -/
theorem empCoeffRect_eq_taylorSeries (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {b R : ℝ}
    (hb : 0 < b) (hbR : b < R) {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u)
    (hξs : ContDiff ℝ ∞ ξ) (hηs : ContDiff ℝ ∞ η) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / SmoothEngine.Qamb k) {j : ℕ} (hj : j ≤ n) :
    SmoothEngine.empCoeffRect η ξ h k (fun _ => b) μ j =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
        ∑ q ∈ Finset.Ico j (n + 1),
          familyCoeffSeries n h k 1 (CoeffFamily.scale (taylorFamily (n + 1) Fξ) b)
            (CoeffFamily.scale (taylorFamily (n + 1) Fη) b) μ q *
            (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) := by
  obtain ⟨C, hC, -⟩ := thm_TaylorTree_taylor n h k hk 1 one_pos hb hbR hFξ hFη hξ hη
  rw [empCoeffRect_eq_boxCoeff h k hk hb hbR hFξ hFη hξ hη hξs hηs hμ hj, boxCoeff_eq_series hC]

end Grammar
