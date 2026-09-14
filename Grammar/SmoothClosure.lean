/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoefficientLinearity

/-!
# Closure of the smooth route (consult #118 audit): two conveniences

Astra's audit (#118) of the completed smooth-amplitude route asked for two inexpensive additions
before closing the programme.

* **Zero-phase components.** A component of the domain on which the phase vanishes identically
  contributes a CONSTANT `∫ obs dμ` to the partition function; it is not represented by the
  positive-unit monomial cores (`SmoothCorePresentation` has `βf > 0`, so an active dimension `0`
  core is exponentially small, not constant). `SmoothExpansionCertificate.const` is the certificate
  of a constant function: lattice `1`, degree `0`, the single coefficient `c_{0,0} = c`. Together
  with `SmoothExpansionCertificate.add` it covers `Z = Z_cores + const`.
* **Chart-wise support.** `SmoothCoreDecomposition.coeff_support_chartwise`: a nonzero global
  coefficient `c_{μ,q}` comes from some chart `I` with `μ ∈ (2∏ᵢ k_{I,i})⁻¹ℕ` and
  `q ≤ dim I − 1` — the union-of-chart-lattices statement (an upper bound on the intrinsic support;
  the union itself is presentation dependent).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### The constant certificate -/

/-- The coefficient system of a constant: `c` at `(0, 0)`, zero elsewhere. -/
noncomputable def constCoeff (c : ℝ) (μ : ℝ) (q : ℕ) : ℝ := if μ = 0 ∧ q = 0 then c else 0

theorem absSpectralSum_constCoeff (c : ℝ) {L : ℝ} (hL : 0 < L) (N : ℝ) :
    absSpectralSum 1 0 (constCoeff c) L N = c := by
  unfold absSpectralSum
  have h0 : (0 : ℝ) ∈ latticeBelow 1 L := by
    have := mem_latticeBelow (Q := 1) one_pos (L := L) (m := 0) (by simpa using hL)
    simpa using this
  rw [Finset.sum_eq_single (0 : ℝ)]
  · simp [constCoeff, Real.rpow_zero]
  · intro μ _ hμ
    simp [constCoeff, hμ]
  · intro h; exact absurd h0 h

theorem CutoffExpansion.const (c : ℝ) : CutoffExpansion 1 0 (fun _ => c) (constCoeff c) := by
  intro L hL
  refine ⟨0, Eventually.of_forall fun N => ?_⟩
  rw [absSpectralSum_constCoeff c hL N, sub_self, abs_zero, zero_mul]

/-- The certificate of a constant function (a zero-phase component of the domain). -/
noncomputable def SmoothExpansionCertificate.const (c : ℝ) :
    SmoothExpansionCertificate fun _ => c where
  Q := 1
  Q_pos := one_pos
  D := 0
  coeff := constCoeff c
  coeff_support := by
    intro μ q hne
    by_cases h : μ = 0 ∧ q = 0
    · exact ⟨⟨0, by rw [h.1]; simp⟩, h.2.le⟩
    · exact absurd (by simp [constCoeff, h]) hne
  expansion := CutoffExpansion.const c

/-- The constant `c` has intrinsic coefficient `c` at `(0, 0)` and zero elsewhere. -/
theorem SmoothExpansionCertificate.coeff_eq_constCoeff (C : SmoothExpansionCertificate fun _ => c)
    (μ : ℝ) (q : ℕ) : C.coeff μ q = constCoeff c μ q :=
  SmoothExpansionCertificate.coeff_eq C (SmoothExpansionCertificate.const c) μ q

/-! ### Chart-wise support of the global smooth coefficients -/

namespace SmoothEngine

namespace SmoothCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  (A : SmoothCoreDecomposition D M S dim)

/-- A nonzero global coefficient comes from some chart, on that chart's lattice and below that
chart's degree. -/
theorem coeff_support_chartwise {μ : ℝ} {q : ℕ} (hc : A.coeff μ q ≠ 0) :
    ∃ I, (∃ m : ℕ, μ = (m : ℝ) / Qamb (A.chart I).k) ∧ q ≤ dim I - 1 := by
  obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  refine ⟨I, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hI ((A.chart I).familyCoeff_eq_zero_of_not_lattice (fun m hm => h m hm) q)
  · by_contra h
    exact hI ((A.chart I).familyCoeff_eq_zero_of_degree_gt (not_le.1 h))

end SmoothCoreDecomposition

end SmoothEngine

end Grammar
