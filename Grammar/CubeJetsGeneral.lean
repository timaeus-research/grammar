/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpCoeffLipschitz

/-!
# Every cube coefficient as a continuous function of the closed realizable cube jets

`CubeJets` did this for the top coefficient (through the replacement rule). With the general
Lipschitz estimate `exists_empCoeffRect_sub_le` the same construction applies to EVERY canonical
coefficient `empCoeffRect η ζ h k b μ q`: it depends only on the cube jet of order
`cubeOrder h k μ` of the field, is Lipschitz on bounded parts of the realizable jets, extends
continuously (hence Borel) to the closed realizable cube jets, and convergence in distribution of
random closed cube jets transfers to it. No deep vanishing and no positivity of `μ` is assumed.
-/

open Filter Topology Set MeasureTheory
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- Two smooth fields with the same cube jets of order `≥ cubeOrder h k μ` have the same
coefficient at `(μ, q)`. -/
theorem empCoeffRect_eq_of_cubeJet_eq (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) {ζ₁ ζ₂ : (Fin d → ℝ) → ℝ}
    (hζ₁ : ContDiff ℝ ∞ ζ₁) (hζ₂ : ContDiff ℝ ∞ ζ₂)
    (heq : cubeJet R b ζ₁ hζ₁ = cubeJet R b ζ₂ hζ₂) :
    empCoeffRect η ζ₁ h k (fun _ => b) μ q = empCoeffRect η ζ₂ h k (fun _ => b) μ q := by
  obtain ⟨K, -, hK⟩ := exists_empCoeffRect_sub_le hη hk hb μ q (norm_nonneg (cubeJet R b ζ₂ hζ₂))
  have hclose : JetClose (cubeOrder h k μ) (closedBox d b) ζ₁ ζ₂ 0 :=
    (jetClose_of_norm_cubeJet_sub_le (by rw [heq, sub_self, norm_zero])).of_le_order hR
  have hbound : JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ₂ ‖cubeJet R b ζ₂ hζ₂‖ :=
    (jetBoundOn_of_norm_cubeJet_le le_rfl).of_le_order hR
  have := hK ζ₁ ζ₂ hζ₁ hζ₂ hbound 0 le_rfl zero_le_one hclose
  rw [mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

open Classical in
/-- The coefficient at `(μ, q)` as a function of the jets (`0` off the realizable jets). -/
noncomputable def cubeCoeffGen' (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ) (b μ : ℝ)
    (q : ℕ) (z : CubeJetSpace d R b) : ℝ :=
  if hz : z ∈ cubeRealizable d R b then
    empCoeffRect η (Classical.choose hz).1 h k (fun _ => b) μ q else 0

theorem cubeCoeffGen'_cubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) (ζ : (Fin d → ℝ) → ℝ)
    (hζ : ContDiff ℝ ∞ ζ) :
    cubeCoeffGen' η h k R b μ q (cubeJet R b ζ hζ) = empCoeffRect η ζ h k (fun _ => b) μ q := by
  have hz := cubeJet_mem_cubeRealizable R b ζ hζ
  rw [cubeCoeffGen', dif_pos hz]
  exact empCoeffRect_eq_of_cubeJet_eq hη hk hb μ q hR _ hζ (Classical.choose_spec hz)

/-- The coefficient at `(μ, q)` is Lipschitz on bounded parts of the realizable jets. -/
theorem lipschitzOnBounded_cubeCoeffGen' (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) :
    LipschitzOnBounded (cubeRealizable d R b) (cubeCoeffGen' η h k R b μ q) := by
  intro B hB
  obtain ⟨K, hK0, hK⟩ := exists_empCoeffRect_sub_le hη hk hb μ q hB
  refine ⟨K, hK0, ?_⟩
  rintro x ⟨ζ₁, rfl⟩ y ⟨ζ₂, rfl⟩ hy hxy
  rw [dist_eq_norm] at hxy ⊢
  rw [cubeCoeffGen'_cubeJet hη hk hb μ q hR, cubeCoeffGen'_cubeJet hη hk hb μ q hR]
  exact hK ζ₁.1 ζ₂.1 ζ₁.2 ζ₂.2 ((jetBoundOn_of_norm_cubeJet_le hy).of_le_order hR) _
    (norm_nonneg _) hxy ((jetClose_of_norm_cubeJet_sub_le le_rfl).of_le_order hR)

/-- The coefficient at `(μ, q)` extended to the closed realizable jets. -/
noncomputable def cubeCoeffGenOnClosedJets (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ)
    (b μ : ℝ) (q : ℕ) (z : ClosedCubeJets d R b) : ℝ :=
  closureExtend (cubeRealizable d R b) (cubeCoeffGen' η h k R b μ q) z

theorem cubeCoeffGenOnClosedJets_closedCubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) (ζ : (Fin d → ℝ) → ℝ)
    (hζ : ContDiff ℝ ∞ ζ) :
    cubeCoeffGenOnClosedJets η h k R b μ q (closedCubeJet R b ζ hζ) =
      empCoeffRect η ζ h k (fun _ => b) μ q := by
  rw [cubeCoeffGenOnClosedJets, closedCubeJet,
    (lipschitzOnBounded_cubeCoeffGen' hη hk hb μ q hR).closureExtend_of_mem
      (cubeJet_mem_cubeRealizable R b ζ hζ)]
  exact cubeCoeffGen'_cubeJet hη hk hb μ q hR ζ hζ

/-- ★ **Every extended cube coefficient is continuous on the closed realizable jets.** -/
theorem continuous_cubeCoeffGenOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) :
    Continuous (cubeCoeffGenOnClosedJets η h k R b μ q) :=
  (lipschitzOnBounded_cubeCoeffGen' hη hk hb μ q hR).continuous_closureExtend

theorem measurable_cubeCoeffGenOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) :
    Measurable (cubeCoeffGenOnClosedJets η h k R b μ q) :=
  (continuous_cubeCoeffGenOnClosedJets hη hk hb μ q hR).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★ **Convergence in distribution of random closed cube jets transfers to every cube
coefficient.** -/
theorem tendstoInDistribution_cubeCoeffGen_closed (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    {b : ℝ} (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    {Z : ℕ → Ω → ClosedCubeJets d R b} {G : Ω' → ClosedCubeJets d R b}
    (hZG : TendstoInDistribution Z atTop G (fun _ => P) P') :
    TendstoInDistribution (fun n w => cubeCoeffGenOnClosedJets η h k R b μ q (Z n w)) atTop
      (fun w' => cubeCoeffGenOnClosedJets η h k R b μ q (G w')) (fun _ => P) P' :=
  hZG.continuous_comp (continuous_cubeCoeffGenOnClosedJets hη hk hb μ q hR)

end Grammar
