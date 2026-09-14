/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoreDecomposition
import Grammar.SmoothExpansionCertificate

/-!
# The scalar certificate of a smooth core decomposition (consult #117 §6, U6a closure)

A smooth core decomposition yields a `SmoothExpansionCertificate` of the population integral
(`toCertificate`), hence the paper's little-o statement ★★★ `hasSmoothCoordFreeExpansion`, and
its scalar coefficients are INTRINSIC: any two smooth core decompositions of the same
localisation datum have the same global coefficients (★★ `coeff_eq_of_decompositions`), and they
agree with the analytic engine's assembled coefficients whenever an analytic core decomposition
exists (★★ `coeff_eq_gCoeff`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology

namespace Grammar

namespace SmoothEngine

namespace SmoothCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  [∀ I, CompactSpace (S I)] [∀ I, FirstCountableTopology (S I)] [∀ I, OpensMeasurableSpace (S I)]
  (A : SmoothCoreDecomposition D M S dim)

/-- ★ The scalar expansion certificate of the population integral. -/
noncomputable def toCertificate : SmoothExpansionCertificate D.Z where
  Q := A.commonQ
  Q_pos := A.commonQ_pos
  D := A.commonD
  coeff := A.coeff
  coeff_support μ q hne := by
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hne (A.coeff_eq_zero_of_not_lattice (fun m hm => h ⟨m, hm⟩) q)
    · by_contra h
      exact hne (A.coeff_eq_zero_of_degree_gt (lt_of_not_ge h))
  expansion := A.cutoffExpansion

/-- ★★★ **The smooth coordinate-free expansion of the population integral**: for every `A`,
`Z(N) − ∑_{exponent ≤ A} coeff · N^{−α}(log N)^j = o(N^{−A})`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion D.Z A.coeff A.commonQ A.commonD :=
  A.toCertificate.hasSmoothCoordFreeExpansion

/-- ★★ **Presentation independence**: two smooth core decompositions of the same localisation
datum have the same global coefficients at every index. -/
theorem coeff_eq_of_decompositions {M' : ℕ} {S' : Fin M' → Type*} [∀ I, TopologicalSpace (S' I)]
    [∀ I, MeasurableSpace (S' I)] {dim' : Fin M' → ℕ} [∀ I, CompactSpace (S' I)]
    [∀ I, FirstCountableTopology (S' I)] [∀ I, OpensMeasurableSpace (S' I)]
    (B : SmoothCoreDecomposition D M' S' dim') (μ : ℝ) (q : ℕ) : A.coeff μ q = B.coeff μ q :=
  SmoothExpansionCertificate.coeff_eq A.toCertificate B.toCertificate μ q

/-- ★★ **Analytic compatibility**: the smooth global coefficients agree with the analytic engine's
assembled coefficients whenever an analytic core decomposition of the same datum exists. -/
theorem coeff_eq_gCoeff {M' : ℕ} {K : Fin M' → Type*} [∀ I, TopologicalSpace (K I)]
    [∀ I, MeasurableSpace (K I)] {n : Fin M' → ℕ} {β : ℝ} [∀ I, CompactSpace (K I)]
    [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
    (B : AnalyticCoreDecomposition D M' K n β) (hβ : 0 < β) (μ : ℝ) (j : ℕ) :
    A.coeff μ j = gCoeff B.ν B.h B.k β B.b B.x μ j :=
  A.toCertificate.coeff_eq_gCoeff B hβ μ j

end SmoothCoreDecomposition

end SmoothEngine

end Grammar
