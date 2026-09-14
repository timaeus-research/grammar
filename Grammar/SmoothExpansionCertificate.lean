/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CutoffExpansionUniqueness
import Grammar.CoordFreeExpansionCompletion
import Grammar.SmoothTimeRescale
import Grammar.AnalyticCorePresentation

/-!
# Scalar expansion certificates and their coordinate-free content (consult #117 §6; U6a)

A **scalar expansion certificate** for `Z : ℝ → ℝ` (`SmoothExpansionCertificate Z`) packages a
lattice `Q⁻¹ℕ`, a logarithmic degree bound `D`, coefficients supported on the lattice and below the
degree, and the finite-cutoff expansion `CutoffExpansion Q D Z c`. The smooth-amplitude engine
produces one (`SmoothExpansionCertificate.ofSmooth`).

* ★★ **Presentation independence** (`SmoothExpansionCertificate.coeff_eq`): two certificates for the
  same function have the same coefficients at EVERY `(μ, q)` — lattice, degree bound and
  construction may all differ. Consequently "the coefficient of `N^{−μ}(log N)^q` in `Z`" is a
  function of `Z` alone.
* ★ **The paper's coordinate-free form** (`HasSmoothCoordFreeExpansion`,
  `CutoffExpansion.hasSmoothCoordFreeExpansion`): for every `A`,
  `Z(N) − ∑_{α ∈ Q⁻¹ℕ, α ≤ A, j ≤ D} c_{α,j} N^{−α}(log N)^j = o(N^{−A})`, with the same
  little-o shape as `ResolvedNormalData.HasCoordFreeExpansion`.
* ★★ **Analytic compatibility** (`SmoothExpansionCertificate.coeff_eq_of_cutoffExpansion`,
  `SmoothExpansionCertificate.coeff_eq_gCoeff`): a smooth certificate for the population integral of
  an analytic core decomposition has the analytic engine's assembled coefficients `gCoeff`.
-/

open Filter Topology Asymptotics
open scoped ContDiff

namespace Grammar

/-- A scalar power–log expansion certificate: a lattice `Q⁻¹ℕ`, a logarithmic degree bound `D`,
coefficients supported on the lattice and below the degree, and the cutoff expansion. -/
structure SmoothExpansionCertificate (Z : ℝ → ℝ) where
  /-- the lattice denominator -/
  Q : ℕ
  Q_pos : 0 < Q
  /-- the logarithmic degree bound -/
  D : ℕ
  /-- the coefficients `c_{μ,q}` of `N^{−μ}(log N)^q` -/
  coeff : ℝ → ℕ → ℝ
  coeff_support : ∀ μ q, coeff μ q ≠ 0 → (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D
  expansion : CutoffExpansion Q D Z coeff

namespace SmoothExpansionCertificate

variable {Z : ℝ → ℝ} (C : SmoothExpansionCertificate Z)

theorem coeff_eq_zero_of_not_lattice {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / C.Q) (q : ℕ) :
    C.coeff μ q = 0 := by
  by_contra hne
  obtain ⟨⟨m, hm⟩, -⟩ := C.coeff_support μ q hne
  exact hμ m hm

theorem coeff_eq_zero_of_degree_gt {μ : ℝ} {q : ℕ} (hq : C.D < q) : C.coeff μ q = 0 := by
  by_contra hne
  exact absurd (C.coeff_support μ q hne).2 (not_le.2 hq)

/-- ★★ **Analytic compatibility, generic form**: a certificate agrees everywhere with any cutoff
expansion of the same function whose coefficients are supported on their own lattice and degree
range. -/
theorem coeff_eq_of_cutoffExpansion {Q' D' : ℕ} (hQ' : 0 < Q') {c' : ℝ → ℕ → ℝ}
    (h' : CutoffExpansion Q' D' Z c') (hc' : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q') → ∀ j, c' μ j = 0)
    (hcD' : ∀ μ j, D' < j → c' μ j = 0) (μ : ℝ) (j : ℕ) : C.coeff μ j = c' μ j :=
  CutoffExpansion.coeff_eq_of_lattices C.Q_pos hQ' C.expansion h'
    (fun _ hμ j => C.coeff_eq_zero_of_not_lattice hμ j)
    (fun _ _ hj => C.coeff_eq_zero_of_degree_gt hj) hc' hcD' μ j

/-- ★★ **Presentation independence**: two certificates for the same function have the same
coefficients at every `(μ, q)`. -/
theorem coeff_eq (C₁ C₂ : SmoothExpansionCertificate Z) (μ : ℝ) (q : ℕ) :
    C₁.coeff μ q = C₂.coeff μ q :=
  C₁.coeff_eq_of_cutoffExpansion C₂.Q_pos C₂.expansion
    (fun _ hμ j => C₂.coeff_eq_zero_of_not_lattice hμ j)
    (fun _ _ hj => C₂.coeff_eq_zero_of_degree_gt hj) μ q

/-- The certificate produced by the smooth-amplitude engine: lattice `Q = 2∏kᵢ`, degree bound
`d − 1`, the canonical coefficients `smoothCoeff`. -/
noncomputable def ofSmooth {d : ℕ} {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}
    (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) :
    SmoothExpansionCertificate (SmoothEngine.smoothIntegral F h k β b) where
  Q := SmoothEngine.Qamb k
  Q_pos := SmoothEngine.Qamb_pos k hk
  D := d - 1
  coeff := SmoothEngine.smoothCoeff F h k β b
  coeff_support := fun μ q hne => by
    refine ⟨?_, ?_⟩
    · by_contra hμ
      exact hne (SmoothEngine.smoothCoeff_eq_zero_of_not_lattice hk hβ hb
        (fun m hm => hμ ⟨m, hm⟩) q)
    · by_contra hq
      exact hne (SmoothEngine.smoothCoeff_eq_zero_of_degree_gt (not_le.1 hq))
  expansion := SmoothEngine.smooth_cutoffExpansion hF hk hβ hb

end SmoothExpansionCertificate

/-! ### The coordinate-free little-o form -/

/-- The paper's form: for every `A`,
`Z(N) − ∑_{q : exponent ≤ A} c_q N^{−α}(log N)^j = o(N^{−A})`. -/
def HasSmoothCoordFreeExpansion (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (Q D : ℕ) : Prop :=
  ∀ A : ℝ, (fun N : ℝ => Z N - ∑ q ∈ spectrumLe Q D A, c q.exponent q.logDegree * q.scale N)
    =o[atTop] fun N : ℝ => N ^ (-A)

/-- A cutoff expansion, read at the cutoff `max (A+1) 1`, is `o(N^{−A})` after subtracting the
spectrum below that cutoff. -/
theorem CutoffExpansion.isLittleO_sub_spectrumBelow {Q D : ℕ} {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hc : CutoffExpansion Q D Z c) (A : ℝ) :
    (fun N : ℝ => Z N - ∑ q ∈ spectrumBelow Q D A, c q.exponent q.logDegree * q.scale N)
      =o[atTop] fun N : ℝ => N ^ (-A) := by
  have hcut : 0 < cutoffExponent A := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K, hK⟩ := hc (cutoffExponent A) hcut
  simp_rw [sum_spectrumBelow]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound K ?_) (isLittleO_rpow_cutoff_mul A D)
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))]
  exact hN

/-- ★ **Cutoff expansion ⇒ coordinate-free little-o form**: the terms with exponent in
`(A, max(A+1,1))` are individually `o(N^{−A})`, so the truncation to exponents `≤ A` suffices. -/
theorem CutoffExpansion.hasSmoothCoordFreeExpansion {Q D : ℕ} {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hc : CutoffExpansion Q D Z c) : HasSmoothCoordFreeExpansion Z c Q D := by
  intro A
  have h := hc.isLittleO_sub_spectrumBelow A
  have hsplit : ∀ N : ℝ, ∑ q ∈ spectrumBelow Q D A, c q.exponent q.logDegree * q.scale N =
      ∑ q ∈ spectrumLe Q D A, c q.exponent q.logDegree * q.scale N +
      ∑ q ∈ (spectrumBelow Q D A).filter (fun q => ¬ q.exponent ≤ A),
        c q.exponent q.logDegree * q.scale N := fun N =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have htail : (fun N : ℝ => ∑ q ∈ (spectrumBelow Q D A).filter (fun q => ¬ q.exponent ≤ A),
      c q.exponent q.logDegree * q.scale N) =o[atTop] fun N : ℝ => N ^ (-A) := by
    have hsum := IsLittleO.sum (l := atTop) (g' := fun N : ℝ => N ^ (-A))
      (A := fun q : PowerLogIndex => fun N : ℝ => c q.exponent q.logDegree * q.scale N)
      (s := (spectrumBelow Q D A).filter fun q => ¬ q.exponent ≤ A) fun q hq => by
      have hq' : A < q.exponent := not_le.1 (Finset.mem_filter.1 hq).2
      exact ((isLittleO_scale_of_lt hq' q.logDegree).congr_left fun N =>
        (PowerLogIndex.scale_def q N).symm).const_mul_left _
    refine hsum.congr_left fun N => ?_
    rw [Finset.sum_apply]
  have hfun : (fun N : ℝ => Z N - ∑ q ∈ spectrumLe Q D A, c q.exponent q.logDegree * q.scale N) =
      fun N : ℝ => (Z N - ∑ q ∈ spectrumBelow Q D A, c q.exponent q.logDegree * q.scale N) +
        ∑ q ∈ (spectrumBelow Q D A).filter (fun q => ¬ q.exponent ≤ A),
          c q.exponent q.logDegree * q.scale N := by
    funext N
    rw [hsplit N]
    ring
  rw [hfun]
  exact h.add htail

theorem SmoothExpansionCertificate.hasSmoothCoordFreeExpansion {Z : ℝ → ℝ}
    (C : SmoothExpansionCertificate Z) : HasSmoothCoordFreeExpansion Z C.coeff C.Q C.D :=
  C.expansion.hasSmoothCoordFreeExpansion

/-- The smooth-amplitude integral in the paper's coordinate-free form. -/
theorem hasSmoothCoordFreeExpansion_of_smooth {d : ℕ} {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
    {β b : ℝ} (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) :
    HasSmoothCoordFreeExpansion (SmoothEngine.smoothIntegral F h k β b)
      (SmoothEngine.smoothCoeff F h k β b) (SmoothEngine.Qamb k) (d - 1) :=
  (SmoothEngine.smooth_cutoffExpansion hF hk hβ hb).hasSmoothCoordFreeExpansion

/-! ### Compatibility with the analytic engine -/

section Analytic

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- ★★ **Smooth certificates of a population integral carry the analytic coefficients**: for an
analytic core decomposition `A` of `D`, every certificate `C` for `D.Z` has
`C.coeff μ j = gCoeff … μ j` at every `(μ, j)`. -/
theorem SmoothExpansionCertificate.coeff_eq_gCoeff (A : AnalyticCoreDecomposition D M K n β)
    (hβ : 0 < β) (C : SmoothExpansionCertificate D.Z) (μ : ℝ) (j : ℕ) :
    C.coeff μ j = gCoeff A.ν A.h A.k β A.b A.x μ j :=
  C.coeff_eq_of_cutoffExpansion (commonQ_pos A.k A.k_pos) (A.cutoffExpansion hβ)
    (fun _ hμ j => gCoeff_eq_zero_of_not_lattice _ _ _ _ _ _ A.k_pos hβ A.b_pos hμ j)
    (fun _ _ hj => gCoeff_eq_zero_of_lt _ _ _ _ _ _ hj) μ j

end Analytic

end Grammar
