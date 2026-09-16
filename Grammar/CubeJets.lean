/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CubeCoeffLipschitz
import Grammar.LipschitzClosureExtension
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Jets on a cube and the top cube coefficient on the closed realizable jets

`CubeJetSpace d R b`: for every order `r ≤ R`, a continuous `r`-multilinear-map-valued function
on the closed box `[0,b]^d` (a `def` with one normed-group instance). `cubeJet R b ζ hζ` is the jet
of a smooth field; `cubeRealizable` its range. The top coefficient of the cube expansion is a
well-defined function of the realizable jets of order `R ≥ R₀ = ∑ depthOf h k (cutoffOf h μ)`,
Lipschitz on bounded parts (`exists_empCoeffRect_top_bound`), hence extends continuously to the
closed realizable jets (`cubeCoeffOnClosedJets`, via `closureExtend`), and convergence in
distribution of random closed cube jets transfers to the coefficient
(`tendstoInDistribution_cubeCoeff_top_closed`).

This is the single-cube analogue of `EmpiricalBranchJets`/`EmpiricalClosedJets`, the target of the
grey-book bridge (consult #151, M5).
-/

open Filter Topology Set MeasureTheory
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

instance instCompactSpaceClosedBox (b : ℝ) : CompactSpace (closedBox d b) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBox b)

/-- The jets of order `≤ R` on the closed cube `[0,b]^d`. -/
def CubeJetSpace (d R : ℕ) (b : ℝ) : Type :=
  ∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)

noncomputable instance instNormedAddCommGroupCubeJetSpace (R : ℕ) (b : ℝ) :
    NormedAddCommGroup (CubeJetSpace d R b) :=
  inferInstanceAs (NormedAddCommGroup (∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

noncomputable instance instMeasurableSpaceCubeJetSpace (R : ℕ) (b : ℝ) :
    MeasurableSpace (CubeJetSpace d R b) :=
  borel _

instance instBorelSpaceCubeJetSpace (R : ℕ) (b : ℝ) : BorelSpace (CubeJetSpace d R b) := ⟨rfl⟩

/-- The underlying family of continuous maps. -/
def CubeJetSpace.toPi {R : ℕ} {b : ℝ} (f : CubeJetSpace d R b) :
    ∀ r : Fin (R + 1),
      ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ) :=
  f

/-- The cube jet of a smooth field. -/
noncomputable def cubeJet (R : ℕ) (b : ℝ) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    CubeJetSpace d R b :=
  fun r => ⟨fun x => iteratedFDeriv ℝ r.1 ζ x.1,
    (hζ.continuous_iteratedFDeriv (natCast_le_infty _)).comp continuous_subtype_val⟩

theorem cubeJet_apply (R : ℕ) (b : ℝ) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ)
    (r : Fin (R + 1)) (x : closedBox d b) :
    CubeJetSpace.toPi (cubeJet R b ζ hζ) r x = iteratedFDeriv ℝ r.1 ζ x.1 := rfl

theorem jetClose_of_norm_cubeJet_sub_le {R : ℕ} {b : ℝ} {ζ₁ ζ₂ : (Fin d → ℝ) → ℝ}
    {hζ₁ : ContDiff ℝ ∞ ζ₁} {hζ₂ : ContDiff ℝ ∞ ζ₂} {ε : ℝ}
    (h : ‖cubeJet R b ζ₁ hζ₁ - cubeJet R b ζ₂ hζ₂‖ ≤ ε) :
    JetClose R (closedBox d b) ζ₁ ζ₂ ε := by
  intro r hr x hx
  set D := CubeJetSpace.toPi (cubeJet R b ζ₁ hζ₁ - cubeJet R b ζ₂ hζ₂) with hD
  have hval : iteratedFDeriv ℝ r ζ₁ x - iteratedFDeriv ℝ r ζ₂ x =
      D ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ := rfl
  rw [hval]
  exact ((ContinuousMap.norm_coe_le_norm _ _).trans (norm_le_pi_norm _ _)).trans h

theorem jetBoundOn_of_norm_cubeJet_le {R : ℕ} {b : ℝ} {ζ : (Fin d → ℝ) → ℝ}
    {hζ : ContDiff ℝ ∞ ζ} {B : ℝ} (h : ‖cubeJet R b ζ hζ‖ ≤ B) :
    JetBoundOn R (closedBox d b) ζ B := by
  intro r hr x hx
  set D := CubeJetSpace.toPi (cubeJet R b ζ hζ) with hD
  have hval : iteratedFDeriv ℝ r ζ x = D ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ := rfl
  rw [hval]
  exact ((ContinuousMap.norm_coe_le_norm _ _).trans (norm_le_pi_norm _ _)).trans h

/-- The realizable cube jets: the jets of smooth fields. -/
def cubeRealizable (d R : ℕ) (b : ℝ) : Set (CubeJetSpace d R b) :=
  Set.range fun ζ : {ζ : (Fin d → ℝ) → ℝ // ContDiff ℝ ∞ ζ} => cubeJet R b ζ.1 ζ.2

theorem cubeJet_mem_cubeRealizable (R : ℕ) (b : ℝ) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    cubeJet R b ζ hζ ∈ cubeRealizable d R b :=
  ⟨⟨ζ, hζ⟩, rfl⟩

section Coeff

variable {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The canonical order of the top coefficient at `μ`. -/
noncomputable def cubeOrder (h k : Fin d → ℕ) (μ : ℝ) : ℕ := ∑ i, depthOf h k (cutoffOf h μ) i

theorem JetClose.of_le_order {R R' : ℕ} {K : Set (Fin d → ℝ)} {f₁ f₂ : (Fin d → ℝ) → ℝ} {ε : ℝ}
    (hc : JetClose R' K f₁ f₂ ε) (hR : R ≤ R') : JetClose R K f₁ f₂ ε :=
  fun r hr x hx => hc r (hr.trans hR) x hx

theorem JetBoundOn.of_le_order {R R' : ℕ} {K : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hb : JetBoundOn R' K f B) (hR : R ≤ R') : JetBoundOn R K f B :=
  fun r hr x hx => hb r (hr.trans hR) x hx

/-- Two smooth fields with the same cube jets of order `≥ R₀` have the same top coefficient. -/
theorem empCoeffRect_top_eq_of_cubeJet_eq (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) {ζ₁ ζ₂ : (Fin d → ℝ) → ℝ} (hζ₁ : ContDiff ℝ ∞ ζ₁)
    (hζ₂ : ContDiff ℝ ∞ ζ₂) (heq : cubeJet R b ζ₁ hζ₁ = cubeJet R b ζ₂ hζ₂) :
    empCoeffRect η ζ₁ h k (fun _ => b) μ (c - 1) =
      empCoeffRect η ζ₂ h k (fun _ => b) μ (c - 1) := by
  obtain ⟨K, -, hK⟩ := exists_empCoeffRect_top_bound hη hk hb hμ hc hdeep
    (norm_nonneg (cubeJet R b ζ₂ hζ₂))
  have hclose : JetClose (cubeOrder h k μ) (closedBox d b) ζ₁ ζ₂ 0 :=
    (jetClose_of_norm_cubeJet_sub_le (by rw [heq, sub_self, norm_zero])).of_le_order hR
  have hbound : JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ₂ ‖cubeJet R b ζ₂ hζ₂‖ :=
    (jetBoundOn_of_norm_cubeJet_le le_rfl).of_le_order hR
  have := hK ζ₁ ζ₂ hζ₁ hζ₂ hbound 0 le_rfl zero_le_one hclose
  rw [mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

open Classical in
/-- The top cube coefficient as a function of the jets (`0` off the realizable jets). -/
noncomputable def cubeCoeff' (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ) (b μ : ℝ) (c : ℕ)
    (z : CubeJetSpace d R b) : ℝ :=
  if hz : z ∈ cubeRealizable d R b then
    empCoeffRect η (Classical.choose hz).1 h k (fun _ => b) μ (c - 1) else 0

theorem cubeCoeff'_cubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    cubeCoeff' η h k R b μ c (cubeJet R b ζ hζ) = empCoeffRect η ζ h k (fun _ => b) μ (c - 1) := by
  have hz := cubeJet_mem_cubeRealizable R b ζ hζ
  rw [cubeCoeff', dif_pos hz]
  exact empCoeffRect_top_eq_of_cubeJet_eq hη hk hb hμ hc hdeep hR _ hζ (Classical.choose_spec hz)

/-- The top coefficient is Lipschitz on bounded parts of the realizable jets. -/
theorem lipschitzOnBounded_cubeCoeff' (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) :
    LipschitzOnBounded (cubeRealizable d R b) (cubeCoeff' η h k R b μ c) := by
  intro B hB
  obtain ⟨K, hK0, hK⟩ := exists_empCoeffRect_top_bound hη hk hb hμ hc hdeep hB
  refine ⟨K, hK0, ?_⟩
  rintro x ⟨ζ₁, rfl⟩ y ⟨ζ₂, rfl⟩ hy hxy
  rw [dist_eq_norm] at hxy ⊢
  rw [cubeCoeff'_cubeJet hη hk hb hμ hc hdeep hR, cubeCoeff'_cubeJet hη hk hb hμ hc hdeep hR]
  exact hK ζ₁.1 ζ₂.1 ζ₁.2 ζ₂.2 ((jetBoundOn_of_norm_cubeJet_le hy).of_le_order hR) _
    (norm_nonneg _) hxy ((jetClose_of_norm_cubeJet_sub_le le_rfl).of_le_order hR)

/-- The closed realizable cube jets. -/
abbrev ClosedCubeJets (d R : ℕ) (b : ℝ) : Type := closure (cubeRealizable d R b)

/-- The top cube coefficient extended to the closed realizable jets. -/
noncomputable def cubeCoeffOnClosedJets (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ) (b μ : ℝ)
    (c : ℕ) (z : ClosedCubeJets d R b) : ℝ :=
  closureExtend (cubeRealizable d R b) (cubeCoeff' η h k R b μ c) z

/-- The cube jet of a smooth field as a closed realizable jet. -/
noncomputable def closedCubeJet (R : ℕ) (b : ℝ) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    ClosedCubeJets d R b :=
  ⟨cubeJet R b ζ hζ, subset_closure (cubeJet_mem_cubeRealizable R b ζ hζ)⟩

theorem cubeCoeffOnClosedJets_closedCubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    cubeCoeffOnClosedJets η h k R b μ c (closedCubeJet R b ζ hζ) =
      empCoeffRect η ζ h k (fun _ => b) μ (c - 1) := by
  rw [cubeCoeffOnClosedJets, closedCubeJet,
    (lipschitzOnBounded_cubeCoeff' hη hk hb hμ hc hdeep hR).closureExtend_of_mem
      (cubeJet_mem_cubeRealizable R b ζ hζ)]
  exact cubeCoeff'_cubeJet hη hk hb hμ hc hdeep hR ζ hζ

/-- ★ **The extended top cube coefficient is continuous on the closed realizable jets.** -/
theorem continuous_cubeCoeffOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) : Continuous (cubeCoeffOnClosedJets η h k R b μ c) :=
  (lipschitzOnBounded_cubeCoeff' hη hk hb hμ hc hdeep hR).continuous_closureExtend

theorem measurable_cubeCoeffOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {R : ℕ}
    (hR : cubeOrder h k μ ≤ R) : Measurable (cubeCoeffOnClosedJets η h k R b μ c) :=
  (continuous_cubeCoeffOnClosedJets hη hk hb hμ hc hdeep hR).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★ **Convergence in distribution of random closed cube jets transfers to the top cube
coefficient.** -/
theorem tendstoInDistribution_cubeCoeff_top_closed (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c)
    {R : ℕ} (hR : cubeOrder h k μ ≤ R) {Z : ℕ → Ω → ClosedCubeJets d R b}
    {G : Ω' → ClosedCubeJets d R b} (hZG : TendstoInDistribution Z atTop G (fun _ => P) P') :
    TendstoInDistribution (fun n w => cubeCoeffOnClosedJets η h k R b μ c (Z n w)) atTop
      (fun w' => cubeCoeffOnClosedJets η h k R b μ c (G w')) (fun _ => P) P' :=
  hZG.continuous_comp (continuous_cubeCoeffOnClosedJets hη hk hb hμ hc hdeep hR)

end Coeff

end Grammar
