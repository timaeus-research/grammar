/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalResolvedContinuity

/-!
# The branch-jet topology and the coefficient map (§20, consult #145 interface)

The fixed-index topology on smooth root fields in which the resolved coefficient at `(μ, c − 1)` is
continuous: the **branch jets** `branchJet μ ξ` — for every piece `p` and every order `r ≤ R_p(μ)`
the continuous map `x ↦ D^r L_p(x)` on the compact chart image `K_p` — living in the finite product
`BranchJetSpace μ` of the Banach spaces `C(K_p, CMM_r)` (sup norms). Closeness of the jets is
exactly the `JetClose` hypothesis of the continuity theorem (`jetClose_of_norm_branchJet_sub_le`,
`norm_branchJet_sub_le`), and jet bounds are norm bounds (`jetBoundOn_of_norm_branchJet_le`). The
coefficient factors through the jets (`resolvedCoeff_eq_of_branchJet_eq`, from the local Lipschitz
bound with `ε = 0`), defining `coeffOnJets` on the REALIZABLE jets `range (branchJet μ)`; it is
continuous there (★★ `continuous_coeffOnJets`) hence Borel measurable (`measurable_coeffOnJets`) —
the interface for a continuous-mapping theorem for random branch representatives. Non-claims: the
topology depends on `μ`; different fields may have the same restricted jets (a pseudometric on
fields); no extension to arbitrary jet tuples or to the closure of the realizable image is
asserted. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

instance instCompactSpaceChartImage (p : (Ξ.X Y).PIdx) : CompactSpace (Ξ.chartImage Y p) :=
  isCompact_iff_compactSpace.1 (Ξ.isCompact_chartImage Y p)

/-- The branch-jet space at index `μ`: for every piece and every order `r ≤ R_p(μ)`, a continuous
`r`-multilinear-map-valued function on the compact chart image. A `def` (not an abbreviation), so
that all its structure comes from the single normed-group instance below. -/
def BranchJetSpace (μ : ℝ) : Type :=
  ∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
    ContinuousMap (Ξ.chartImage Y p) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)

noncomputable instance instNormedAddCommGroupBranchJetSpace (μ : ℝ) :
    NormedAddCommGroup (Ξ.BranchJetSpace Y μ) :=
  inferInstanceAs (NormedAddCommGroup (∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
    ContinuousMap (Ξ.chartImage Y p) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

noncomputable instance instMeasurableSpaceBranchJetSpace (μ : ℝ) :
    MeasurableSpace (Ξ.BranchJetSpace Y μ) :=
  borel _

instance instBorelSpaceBranchJetSpace (μ : ℝ) : BorelSpace (Ξ.BranchJetSpace Y μ) := ⟨rfl⟩

/-- The underlying family of continuous maps. -/
def BranchJetSpace.toPi {μ : ℝ} (f : Ξ.BranchJetSpace Y μ) :
    ∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
      ContinuousMap (Ξ.chartImage Y p)
        (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ) := f

theorem BranchJetSpace.norm_toPi {μ : ℝ} (f : Ξ.BranchJetSpace Y μ) :
    ‖BranchJetSpace.toPi Ξ Y f‖ = ‖f‖ := rfl

theorem BranchJetSpace.toPi_sub {μ : ℝ} (f g : Ξ.BranchJetSpace Y μ) :
    BranchJetSpace.toPi Ξ Y (f - g) = BranchJetSpace.toPi Ξ Y f - BranchJetSpace.toPi Ξ Y g := rfl

/-- The restricted branch jets of a smooth root field. -/
noncomputable def branchJet (μ : ℝ) (ξ : Ξ.SmoothRootField Y) : Ξ.BranchJetSpace Y μ :=
  fun p r => ⟨fun x => iteratedFDeriv ℝ r.1 (ξ.Lψ p) x.1,
    ((ξ.Lψ_smooth p).continuous_iteratedFDeriv (natCast_le_infty _)).comp continuous_subtype_val⟩

theorem branchJet_toPi_apply (μ : ℝ) (ξ : Ξ.SmoothRootField Y) (p : (Ξ.X Y).PIdx)
    (r : Fin (Ξ.pieceOrder Y p μ + 1)) (x : Ξ.chartImage Y p) :
    BranchJetSpace.toPi Ξ Y (Ξ.branchJet Y μ ξ) p r x = iteratedFDeriv ℝ r.1 (ξ.Lψ p) x.1 := rfl

/-! ### Jet closeness and jet bounds are norm statements -/

theorem jetClose_of_norm_branchJet_sub_le {μ : ℝ} {ξ₁ ξ₂ : Ξ.SmoothRootField Y} {ε : ℝ}
    (h : ‖Ξ.branchJet Y μ ξ₁ - Ξ.branchJet Y μ ξ₂‖ ≤ ε) (p : (Ξ.X Y).PIdx) :
    JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₁.Lψ p) (ξ₂.Lψ p) ε := by
  intro r hr x hx
  set D := BranchJetSpace.toPi Ξ Y (Ξ.branchJet Y μ ξ₁ - Ξ.branchJet Y μ ξ₂) with hD
  have hval : iteratedFDeriv ℝ r (ξ₁.Lψ p) x - iteratedFDeriv ℝ r (ξ₂.Lψ p) x =
      D p ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ := rfl
  rw [hval]
  refine le_trans ?_ h
  rw [← BranchJetSpace.norm_toPi]
  exact (ContinuousMap.norm_coe_le_norm _ _).trans
    ((norm_le_pi_norm (D p) _).trans (norm_le_pi_norm D p))

theorem norm_branchJet_sub_le {μ : ℝ} {ξ₁ ξ₂ : Ξ.SmoothRootField Y} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₁.Lψ p) (ξ₂.Lψ p) ε) :
    ‖Ξ.branchJet Y μ ξ₁ - Ξ.branchJet Y μ ξ₂‖ ≤ ε := by
  rw [← BranchJetSpace.norm_toPi, pi_norm_le_iff_of_nonneg hε]
  intro p
  rw [pi_norm_le_iff_of_nonneg hε]
  intro r
  rw [ContinuousMap.norm_le _ hε]
  intro x
  exact h p r.1 (Nat.lt_succ_iff.1 r.2) x.1 x.2

theorem jetBoundOn_of_norm_branchJet_le {μ : ℝ} {ξ : Ξ.SmoothRootField Y} {B : ℝ}
    (h : ‖Ξ.branchJet Y μ ξ‖ ≤ B) (p : (Ξ.X Y).PIdx) :
    JetBoundOn (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ.Lψ p) B := by
  intro r hr x hx
  set D := BranchJetSpace.toPi Ξ Y (Ξ.branchJet Y μ ξ) with hD
  have hval : iteratedFDeriv ℝ r (ξ.Lψ p) x = D p ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ := rfl
  rw [hval]
  refine le_trans ?_ h
  rw [← BranchJetSpace.norm_toPi]
  exact (ContinuousMap.norm_coe_le_norm _ _).trans
    ((norm_le_pi_norm (D p) _).trans (norm_le_pi_norm D p))

/-! ### The coefficient factors through the jets -/

/-- Fields with the same restricted branch jets have the same coefficient. -/
theorem resolvedCoeff_eq_of_branchJet_eq {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    {ξ₁ ξ₂ : Ξ.SmoothRootField Y} (h : Ξ.branchJet Y μ ξ₁ = Ξ.branchJet Y μ ξ₂) :
    ξ₁.resolvedCoeff μ (c - 1) = ξ₂.resolvedCoeff μ (c - 1) := by
  obtain ⟨K, -, hK⟩ :=
    Ξ.exists_resolvedCoeff_top_bound Y hc hF hμ (norm_nonneg (Ξ.branchJet Y μ ξ₂))
  have hclose : ∀ p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₁.Lψ p) (ξ₂.Lψ p) 0 := by
    intro p r hr x hx
    have hx' : BranchJetSpace.toPi Ξ Y (Ξ.branchJet Y μ ξ₁) p ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ =
        BranchJetSpace.toPi Ξ Y (Ξ.branchJet Y μ ξ₂) p ⟨r, Nat.lt_succ_of_le hr⟩ ⟨x, hx⟩ := by
      rw [h]
    rw [branchJet_toPi_apply, branchJet_toPi_apply] at hx'
    rw [hx', sub_self, norm_zero]
  have := hK ξ₁ ξ₂ (Ξ.jetBoundOn_of_norm_branchJet_le Y le_rfl) 0 le_rfl zero_le_one hclose
  rw [mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- The resolved coefficient at `(μ, c − 1)` as a function on the realizable branch jets. -/
noncomputable def coeffOnJets (μ : ℝ) (c : ℕ) (x : Set.range (Ξ.branchJet Y μ)) : ℝ :=
  (Classical.choose x.2).resolvedCoeff μ (c - 1)

theorem coeffOnJets_eq {c : ℕ} (hc : 1 ≤ c) (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    {μ : ℝ} (hμ : 0 < μ) (x : Set.range (Ξ.branchJet Y μ)) (ξ : Ξ.SmoothRootField Y)
    (h : Ξ.branchJet Y μ ξ = x.1) : Ξ.coeffOnJets Y μ c x = ξ.resolvedCoeff μ (c - 1) :=
  Ξ.resolvedCoeff_eq_of_branchJet_eq Y hc hF hμ ((Classical.choose_spec x.2).trans h.symm)

theorem coeffOnJets_branchJet {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : Ξ.SmoothRootField Y) :
    Ξ.coeffOnJets Y μ c ⟨Ξ.branchJet Y μ ξ, ⟨ξ, rfl⟩⟩ = ξ.resolvedCoeff μ (c - 1) :=
  Ξ.coeffOnJets_eq Y hc hF hμ _ ξ rfl

/-- ★★ **The coefficient map is continuous on the realizable branch jets.** -/
theorem continuous_coeffOnJets {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    Continuous (Ξ.coeffOnJets Y μ c) := by
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  obtain ⟨ξ₀, hξ₀⟩ := x.2
  obtain ⟨K, hK0, hK⟩ :=
    Ξ.exists_resolvedCoeff_top_bound Y hc hF hμ (norm_nonneg (Ξ.branchJet Y μ ξ₀))
  refine ⟨min 1 (ε / (K + 1)), lt_min one_pos (div_pos hε (by linarith)), fun y hy => ?_⟩
  obtain ⟨ξ₁, hξ₁⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm, ← hξ₁, ← hξ₀] at hy
  rw [Real.dist_eq, Ξ.coeffOnJets_eq Y hc hF hμ y ξ₁ hξ₁, Ξ.coeffOnJets_eq Y hc hF hμ x ξ₀ hξ₀]
  set δ := ‖Ξ.branchJet Y μ ξ₁ - Ξ.branchJet Y μ ξ₀‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδ1 : δ ≤ 1 := (hy.trans_le (min_le_left _ _)).le
  have hδε : δ < ε / (K + 1) := hy.trans_le (min_le_right _ _)
  have h1 := hK ξ₁ ξ₀ (Ξ.jetBoundOn_of_norm_branchJet_le Y le_rfl) δ hδ0 hδ1
    (Ξ.jetClose_of_norm_branchJet_sub_le Y le_rfl)
  calc |ξ₁.resolvedCoeff μ (c - 1) - ξ₀.resolvedCoeff μ (c - 1)| ≤ K * δ := h1
    _ ≤ (K + 1) * δ := by nlinarith
    _ < (K + 1) * (ε / (K + 1)) := by
        exact mul_lt_mul_of_pos_left hδε (by linarith)
    _ = ε := by field_simp

/-- The coefficient map is Borel measurable on the realizable branch jets. -/
theorem measurable_coeffOnJets {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    Measurable (Ξ.coeffOnJets Y μ c) :=
  (Ξ.continuous_coeffOnJets Y hc hF hμ).measurable

/-- The jets of a convergent sequence of fields converge in the jet space. -/
theorem tendsto_branchJet {μ : ℝ} {ξ : ℕ → Ξ.SmoothRootField Y} {ξ₀ : Ξ.SmoothRootField Y}
    {M : ℕ → ℝ} (hM0' : ∀ n, 0 ≤ M n)
    (hM : ∀ n p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) ((ξ n).Lψ p) (ξ₀.Lψ p) (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun n => Ξ.branchJet Y μ (ξ n)) atTop (𝓝 (Ξ.branchJet Y μ ξ₀)) := by
  have hn : ∀ n, ‖Ξ.branchJet Y μ (ξ n) - Ξ.branchJet Y μ ξ₀‖ ≤ M n := fun n =>
    Ξ.norm_branchJet_sub_le Y (hM0' n) (hM n)
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hn hM0)

end ResolvedData

end SmoothEngine

end Grammar
