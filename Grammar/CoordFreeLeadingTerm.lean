/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CutoffExpansionUniqueness
import Grammar.GlobalLaplaceMeasureBasic
import Grammar.FirstNonzeroAsymptotic

/-!
# The leading term of the coordinate-free expansion and the leading measure (CCCX)

Plan unit 10 / consult #93 C. From the certified coordinate-free expansion (CCCIII):

* `CutoffExpansion.hasLeadingTerm_of_first` — at an admissible pair all of whose predecessors
  (smaller exponent, or equal exponent and larger log degree) carry zero coefficient, a
  finite-cutoff expansion has the leading term `c_{μ,j} · N^{−μ}(log N)^j` (the ordered normalised
  remainder converges and the predecessor sum vanishes);
* ★★ `hasLeadingTerm_expansionCoefficient` — **the leading term of `∫_W φ ϕ e^{−nK}` in
  coordinate-free form**: if the coordinate-free coefficients `∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥(φ∘π),
  B_{I,r,q'}⟩ dν_I` vanish at every admissible index preceding `q = (λ, j)`, then
  `∫_W φ ϕ e^{−nK} / (n^{−λ}(log n)^j) → ∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥(φ∘π), B_{I,r,λ,j}⟩ dν_I`,
  and (`isEquivalent_expansionCoefficient`) the integral is asymptotically equivalent to that term
  when the coefficient is nonzero; `exists_first_nonzero_expansionCoefficient` selects the first
  nonzero admissible index;
* ★★ `expansionCoefficient_eq_integral_leadingMeasure` — **the bridge to the leading measure of
  CCXC**: if `W` has the leading measure `σ` at `(λ, j)` and `φ ϕ` is (represented by) a bounded
  continuous test, the coordinate-free leading coefficient at `(λ, j)` is `∫ φ ϕ dσ`.

Non-claims: no functional-level (observable-independent) identification of the coefficient
fields with the leading measure — the certificates depend on the observable; the leading pair is
not identified with an RLCT here.
-/

open Filter Topology Asymptotics MeasureTheory
open scoped BoundedContinuousFunction

namespace Grammar

/-- **Leading term at a first admissible pair**: the ordered normalised remainder converges to
the coefficient and the predecessor sum vanishes. -/
theorem CutoffExpansion.hasLeadingTerm_of_first {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ}
    (hj : j ≤ D) (hfirst : ∀ q ∈ admissible D Q, precedes q (μ, j) → c q.1 q.2 = 0) :
    HasLeadingTerm Z (c μ j) μ j := by
  have ht := tendsto_abstractRemainder hQ h hμ hj
  unfold HasLeadingTerm
  refine ht.congr' (Eventually.of_forall fun N => ?_)
  unfold abstractRemainder powLogScale
  have hz : absPredSum Q D c μ j N = 0 :=
    absPredSum_eq_zero_of_first hQ c (p := (μ, j)) hfirst N
  rw [hz, sub_zero]

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}

/-- The asymptotic order on power–log indices: `q'` precedes `q` when its exponent is smaller, or
equal with a larger log degree. -/
def PowerLogIndex.Precedes (q' q : PowerLogIndex) : Prop :=
  precedes (q'.exponent, q'.logDegree) (q.exponent, q.logDegree)

namespace ResolvedCertificate

variable (C : ResolvedCertificate R D W K ϕ φ)

/-- The admissible power–log indices of a certificate: exponents in `commonQ⁻¹ℕ`, log degrees
`≤ commonD`. -/
def AdmissibleIndex (q : PowerLogIndex) : Prop :=
  (∃ m : ℕ, q.exponent = (m : ℝ) / commonQ C.adapted.k) ∧ q.logDegree ≤ commonD C.n

namespace CoefficientCertificate

variable {C} (Cc : C.CoefficientCertificate)

/-- ★★ **The leading term of the coordinate-free expansion**: at an admissible index all of whose
predecessors carry zero coordinate-free coefficient,
`∫_W φ ϕ e^{−nK} / (n^{−λ}(log n)^j) →
∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥(φ∘π)(s), B_{I,r,λ,j}(s)⟩ dν_I`. -/
theorem hasLeadingTerm_expansionCoefficient (hK : Measurable K) (hϕ : Measurable ϕ)
    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ) (q : PowerLogIndex) (hq : C.AdmissibleIndex q)
    (hfirst : ∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
      D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0) :
    HasLeadingTerm (globalLaplace W K fun w => φ w * ϕ w)
      (D.expansionCoefficient C.stratumMeasure Cc.field φ q) q.exponent q.logDegree := by
  rw [Cc.expansionCoefficient_eq_gCoeff]
  refine CutoffExpansion.hasLeadingTerm_of_first (commonQ_pos _ C.adapted.k_pos)
    (C.cutoffExpansion_globalLaplace hK hϕ hϕ0 hφ) hq.1 hq.2 fun p hp hpre => ?_
  have := hfirst ⟨p.1, p.2⟩ ⟨hp.1, hp.2⟩ hpre
  rwa [Cc.expansionCoefficient_eq_gCoeff] at this

/-- **Asymptotic equivalence** with the coordinate-free leading term when it is nonzero. -/
theorem isEquivalent_expansionCoefficient (hK : Measurable K) (hϕ : Measurable ϕ)
    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ) (q : PowerLogIndex) (hq : C.AdmissibleIndex q)
    (hfirst : ∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
      D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0)
    (hne : D.expansionCoefficient C.stratumMeasure Cc.field φ q ≠ 0) :
    (globalLaplace W K fun w => φ w * ϕ w) ~[atTop] fun N =>
      D.expansionCoefficient C.stratumMeasure Cc.field φ q * powLogScale q.exponent q.logDegree N :=
  (Cc.hasLeadingTerm_expansionCoefficient hK hϕ hϕ0 hφ q hq hfirst).isEquivalent hne

/-- **The first nonzero coordinate-free coefficient gives the leading term.** -/
theorem exists_first_nonzero_expansionCoefficient (hK : Measurable K) (hϕ : Measurable ϕ)
    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ)
    (hne : ∃ q : PowerLogIndex, C.AdmissibleIndex q ∧
      D.expansionCoefficient C.stratumMeasure Cc.field φ q ≠ 0) :
    ∃ q : PowerLogIndex, C.AdmissibleIndex q ∧
      D.expansionCoefficient C.stratumMeasure Cc.field φ q ≠ 0 ∧
      (∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
        D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0) ∧
      (globalLaplace W K fun w => φ w * ϕ w) ~[atTop] fun N =>
        D.expansionCoefficient C.stratumMeasure Cc.field φ q *
          powLogScale q.exponent q.logDegree N := by
  obtain ⟨q, hq, hq0⟩ := hne
  have hQ := commonQ_pos _ C.adapted.k_pos
  set c := gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x with hc
  have hmem : (q.exponent, q.logDegree) ∈ indexSet (commonD C.n) (commonQ C.adapted.k)
      (q.exponent + 1) := by
    unfold indexSet
    obtain ⟨⟨m, hm⟩, hj⟩ := hq
    rw [hm]
    exact Finset.mem_product.2 ⟨mem_latticeBelow hQ (by linarith), Finset.mem_range.2
      (Nat.lt_succ_of_le hj)⟩
  have hq0' : c q.exponent q.logDegree ≠ 0 := by
    rwa [Cc.expansionCoefficient_eq_gCoeff] at hq0
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ c ⟨(q.exponent, q.logDegree), hmem, hq0'⟩
  refine ⟨⟨p.1, p.2⟩, ⟨hp.1, hp.2⟩, ?_, ?_, ?_⟩
  · rwa [Cc.expansionCoefficient_eq_gCoeff]
  · intro q' hq' hpre
    rw [Cc.expansionCoefficient_eq_gCoeff]
    exact hfirst (q'.exponent, q'.logDegree) ⟨hq'.1, hq'.2⟩ hpre
  · refine Cc.isEquivalent_expansionCoefficient hK hϕ hϕ0 hφ ⟨p.1, p.2⟩ ⟨hp.1, hp.2⟩ ?_ ?_
    · intro q' hq' hpre
      rw [Cc.expansionCoefficient_eq_gCoeff]
      exact hfirst (q'.exponent, q'.logDegree) ⟨hq'.1, hq'.2⟩ hpre
    · rwa [Cc.expansionCoefficient_eq_gCoeff]

/-- ★★ **Bridge to the leading measure** (CCXC): if `W` has the leading measure `σ` at `(λ, j)`
and the amplitude `φ ϕ` is a bounded continuous test, the coordinate-free leading coefficient at
`(λ, j)` is `∫ φ ϕ dσ`. -/
theorem expansionCoefficient_eq_integral_leadingMeasure (hK : Measurable K) (hϕ : Measurable ϕ)
    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ) (q : PowerLogIndex) (hq : C.AdmissibleIndex q)
    (hfirst : ∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
      D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0)
    {σ : Measure (Fin d → ℝ)} (hσ : HasLeadingMeasure W K q.exponent q.logDegree σ)
    (a : (Fin d → ℝ) →ᵇ ℝ) (ha : ∀ w, a w = φ w * ϕ w) :
    D.expansionCoefficient C.stratumMeasure Cc.field φ q = ∫ w, a w ∂σ := by
  have h1 := Cc.hasLeadingTerm_expansionCoefficient hK hϕ hϕ0 hφ q hq hfirst
  have h2 := hσ a
  have heq : globalLaplace W K a = globalLaplace W K fun w => φ w * ϕ w := by
    unfold globalLaplace
    funext t
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [ha w]
  rw [heq] at h2
  exact tendsto_nhds_unique h1 h2

end CoefficientCertificate

end ResolvedCertificate

end Grammar
