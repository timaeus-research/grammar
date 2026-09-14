/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedLeadingOne

/-!
# Independence of the resolved coefficients from the modification on pull-backs

Consult #128 follow-up (3). Two resolved data sets `Ξ, Ξ'` with the same phase and prior but
different Watanabe modifications (over possibly different open sets `W, W'`) have the same
partition functions on pull-back observables, `Z^U_N[f ∘ π] = Z_N[f] = Z^{U'}_N[f ∘ π']`, so by
the uniqueness of expansion coefficients (`SmoothExpansionCertificate.coeff_eq`) the resolved
coefficients agree:

  `𝒯^U_{μ,q}[f ∘ π] = 𝒯^{U'}_{μ,q}[f ∘ π']`  (`coeff_comp_gv_eq_of_modifications`).

In particular the coefficients of the constant observable, and hence the leading-index
hypothesis `IsLeadingIndexOne` (CDXXXIV) and the RLCT data it encodes, are intrinsic to
`(K, prior)`: they do not depend on the choice of modification
(`coeff_one_eq_of_modifications`, `isLeadingIndexOne_iff_of_modifications`). The general
mechanism is `coeff_eq_of_Z_eventuallyEq`: resolved data with eventually equal partition
functions have equal coefficients, whatever their modifications and transports.

Non-claims: nothing is asserted for observables on `U` that are not pull-backs (the
comparison of `𝒯^U` and `𝒯^{U'}` on general observables would need a common refinement, D7,
deferred); the modifications are compared only through their partition functions.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ Ξ' : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
  (Y' : ResolvedCoreTransport Ξ'.R Ξ'.hKc Ξ'.prior)

/-- ★★ **Uniqueness across resolved data**: resolved data with eventually equal partition
functions have equal coefficients, whatever their modifications and transports. -/
theorem coeff_eq_of_Z_eventuallyEq (h : Ξ.Z =ᶠ[atTop] Ξ'.Z) (μ : ℝ) (q : ℕ) :
    Ξ.coeff Y μ q = Ξ'.coeff Y' μ q :=
  SmoothExpansionCertificate.coeff_eq ((Ξ.certificate Y).congr h) (Ξ'.certificate Y') μ q

/-- ★★★ **Independence from the modification on pull-backs**: for the same phase and prior,
`𝒯^U_{μ,q}[f ∘ π] = 𝒯^{U'}_{μ,q}[f ∘ π']` for any two Watanabe modifications. -/
theorem coeff_comp_gv_eq_of_modifications (hK : Ξ.K = Ξ'.K) (hp : Ξ.prior = Ξ'.prior)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y μ q =
      (Ξ'.withF (fun P => f (Ξ'.R.gv P)) (Ξ'.contMDiff_comp_gv hf)).coeff Y' μ q :=
  coeff_eq_of_Z_eventuallyEq (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf))
    (Ξ'.withF (fun P => f (Ξ'.R.gv P)) (Ξ'.contMDiff_comp_gv hf)) Y Y'
    (Eventually.of_forall fun N => by
      rw [Ξ.Z_withF_comp_gv hf N, Ξ'.Z_withF_comp_gv hf N, hK, hp]) μ q

/-- The partition function of the constant observable is the Euclidean partition function
`∫ prior · e^{−NK}`. -/
theorem Z_one (N : ℝ) :
    (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N =
      partitionObs Ξ.K Ξ.prior (fun _ => (1 : ℝ)) N :=
  Ξ.Z_withF_comp_gv contDiff_const N

/-- ★★ **The coefficients of the constant observable are intrinsic to `(K, prior)`**. -/
theorem coeff_one_eq_of_modifications (hK : Ξ.K = Ξ'.K) (hp : Ξ.prior = Ξ'.prior) (μ : ℝ)
    (q : ℕ) :
    (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ q =
      (Ξ'.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y' μ q :=
  coeff_eq_of_Z_eventuallyEq (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const)
    (Ξ'.withF (fun _ => (1 : ℝ)) contMDiff_const) Y Y'
    (Eventually.of_forall fun N => by rw [Ξ.Z_one N, Ξ'.Z_one N, hK, hp]) μ q

/-- ★★ **The leading-index hypothesis is intrinsic to `(K, prior)`**: it holds for one
modification iff it holds for any other. -/
theorem isLeadingIndexOne_iff_of_modifications (hK : Ξ.K = Ξ'.K) (hp : Ξ.prior = Ξ'.prior)
    (μ₀ : ℝ) (q₀ : ℕ) : Ξ.IsLeadingIndexOne Y μ₀ q₀ ↔ Ξ'.IsLeadingIndexOne Y' μ₀ q₀ := by
  unfold IsLeadingIndexOne
  simp only [Ξ.coeff_one_eq_of_modifications Ξ' Y Y' hK hp]

end ResolvedData

end SmoothEngine

end Grammar
