/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalBranchJets
import Grammar.UniformCompactTransfer

/-!
# The conditional random-field theorem for the subleading coefficients (§20, consult #145 (3))

For random smooth root fields `ξₙ : Ω → SmoothRootField` whose realizable branch jets
`realizableJet μ (ξₙ ω)` converge in distribution, in the metric space of realizable jets
`RealizableJets μ ⊆ BranchJetSpace μ`, to a random realizable jet `G`, the resolved empirical
coefficients at the top pair `(μ, c − 1)` of an observable vanishing near `D_{c+1}` converge in
distribution to `coeffOnJets μ c ∘ G` (★★ `tendstoInDistribution_resolvedCoeff_top`) — the
continuous-mapping theorem applied to the continuous coefficient map on the realizable jets. The
statement is conditional: the substantive probabilistic input, convergence in distribution of the
branch jets of the empirical root fields in this finite-order topology (with joint convergence
across pieces), is a hypothesis, not a theorem of this development. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The realizable branch jets at index `μ`, as a metric space. -/
abbrev RealizableJets (μ : ℝ) : Type := Set.range (Ξ.branchJet Y μ)

/-- The branch jets of a field as a realizable jet. -/
noncomputable def realizableJet (μ : ℝ) (ξ : Ξ.SmoothRootField Y) : Ξ.RealizableJets Y μ :=
  ⟨Ξ.branchJet Y μ ξ, ⟨ξ, rfl⟩⟩

theorem coeffOnJets_realizableJet {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : Ξ.SmoothRootField Y) :
    Ξ.coeffOnJets Y μ c (Ξ.realizableJet Y μ ξ) = ξ.resolvedCoeff μ (c - 1) :=
  Ξ.coeffOnJets_branchJet Y hc hF hμ ξ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★ **The conditional random-field theorem**: if the realizable branch jets of random smooth
root fields converge in distribution to a random realizable jet `G`, the resolved coefficients
at `(μ, c − 1)` converge in distribution to `coeffOnJets μ c ∘ G`. -/
theorem tendstoInDistribution_resolvedCoeff_top {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : ℕ → Ω → Ξ.SmoothRootField Y) {G : Ω' → Ξ.RealizableJets Y μ}
    (hLG : TendstoInDistribution (fun n w => Ξ.realizableJet Y μ (ξ n w)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution (fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1)) atTop
      (fun w' => Ξ.coeffOnJets Y μ c (G w')) (fun _ => P) P' := by
  have h := hLG.continuous_comp (Ξ.continuous_coeffOnJets Y hc hF hμ)
  have heq : (fun n : ℕ => Ξ.coeffOnJets Y μ c ∘ fun w => Ξ.realizableJet Y μ (ξ n w)) =
      fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1) :=
    funext fun n => funext fun w => Ξ.coeffOnJets_realizableJet Y hc hF hμ (ξ n w)
  rw [heq] at h
  exact h

end ResolvedData

end SmoothEngine

end Grammar
