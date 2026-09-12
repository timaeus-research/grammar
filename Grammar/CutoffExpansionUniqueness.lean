/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FirstNonzeroAsymptotic
import Grammar.ChartExpansion
import Grammar.ResolvedCoordFreeExpansion

/-!
# Uniqueness of cutoff-expansion coefficients and canonicity of the assembled coefficients (CCCVIII)

Plan unit 11 / consult #93 D. A finite-cutoff expansion determines its coefficients on the
declared lattice and below the declared log degree:

* `CutoffExpansion.coeff_eq_zero_of_zero` — an expansion of the zero function has no nonzero
  admissible coefficient (its first nonzero term would be asymptotically equivalent to `0`);
* ★★ `CutoffExpansion.coeff_unique` — two expansions of the same function on the same lattice and
  degree bound agree at every admissible pair; `coeff_unique_of_lattices` — on different lattices
  and degree bounds, after refinement to the common lattice `Q·Q'` and padding to `max D D'`
  (coefficient systems supported on their own lattice and degree range);
* `gCoeff_eq_zero_of_not_lattice`, `gCoeff_eq_zero_of_lt` — the assembled canonical coefficients
  are supported on `commonQ⁻¹ℕ × {0..commonD}`;
* ★★★ `expansionCoefficient_eq_of_certificates` — **canonicity of the assembled scalar
  coefficients**: two pairs of certificates for the SAME original integral `∫_W φ ϕ e^{−nK}`
  (possibly different resolved geometries' presentations, charts, frames, densities, lattices)
  give the SAME coordinate-free expansion coefficients at every power–log index. The individual
  tensor fields `B_{I,r,α,j}` remain chosen; the scalar coefficient functionals are intrinsic.

Non-claims: coefficients outside the declared lattice/degree range are not constrained by
`CutoffExpansion` (they never enter its sums); nothing about observable-independent functionals.
-/

open Filter Asymptotics Topology MeasureTheory

namespace Grammar

/-! ### Negation, subtraction -/

theorem CutoffExpansion.neg {Q D : ℕ} {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) :
    CutoffExpansion Q D (fun N => -Z N) (fun μ j => -c μ j) := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨K, hK.mono fun N hN => ?_⟩
  have hsum : absSpectralSum Q D (fun μ j => -c μ j) L N = -absSpectralSum Q D c L N := by
    unfold absSpectralSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, show -Z N - -absSpectralSum Q D c L N = -(Z N - absSpectralSum Q D c L N) by ring,
    abs_neg]
  exact hN

theorem CutoffExpansion.sub {Q D : ℕ} {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂) :
    CutoffExpansion Q D (fun N => Z₁ N - Z₂ N) (fun μ j => c₁ μ j - c₂ μ j) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-! ### Uniqueness -/

theorem powLog_term_ne_zero {a μ : ℝ} (ha : a ≠ 0) (j : ℕ) :
    ∀ᶠ N in atTop, a * (N ^ (-μ) * Real.log N ^ j) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 1] with N hN
  have h1 : 0 < N := by linarith
  have h2 : 0 < Real.log N := Real.log_pos hN
  exact mul_ne_zero ha (mul_ne_zero (Real.rpow_pos_of_pos h1 _).ne' (pow_pos h2 _).ne')

/-- **An expansion of the zero function has no nonzero admissible coefficient.** -/
theorem CutoffExpansion.coeff_eq_zero_of_zero {Q D : ℕ} (hQ : 0 < Q) {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D (fun _ => 0) c) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ}
    (hj : j ≤ D) : c μ j = 0 := by
  by_contra hne
  have hmem : (μ, j) ∈ indexSet D Q (μ + 1) := by
    unfold indexSet
    obtain ⟨m, rfl⟩ := hμ
    exact Finset.mem_product.2 ⟨mem_latticeBelow hQ (by linarith), Finset.mem_range.2
      (Nat.lt_succ_of_le hj)⟩
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ c ⟨(μ, j), hmem, hne⟩
  have hequiv := isEquivalent_first_nonzero_of_cutoffExpansion hQ h hp hcp hfirst
  have hlo : (fun N => c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)) =o[atTop]
      fun N => c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
    have h2 := hequiv.neg_left
    refine h2.congr_left fun N => ?_
    simp
  exact isLittleO_irrefl (powLog_term_ne_zero hcp p.2).frequently hlo

/-- ★★ **Uniqueness of cutoff-expansion coefficients** on the declared lattice and degrees. -/
theorem CutoffExpansion.coeff_unique {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c c' : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) (h' : CutoffExpansion Q D Z c') {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) : c μ j = c' μ j := by
  have hsub := h.sub h'
  have hz : (fun N => Z N - Z N) = fun _ => (0 : ℝ) := funext fun N => sub_self _
  rw [hz] at hsub
  exact sub_eq_zero.1 (CutoffExpansion.coeff_eq_zero_of_zero hQ hsub hμ hj)

/-- **Uniqueness across lattices and degree bounds**, for coefficient systems supported on their
own lattice and degree range. -/
theorem CutoffExpansion.coeff_unique_of_lattices {Q Q' D D' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q')
    {Z : ℝ → ℝ} {c c' : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) (h' : CutoffExpansion Q' D' Z c')
    (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (hcD : ∀ μ j, D < j → c μ j = 0)
    (hc' : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q') → ∀ j, c' μ j = 0)
    (hcD' : ∀ μ j, D' < j → c' μ j = 0) {μ : ℝ}
    (hμ : (∃ m : ℕ, μ = (m : ℝ) / Q) ∨ ∃ m : ℕ, μ = (m : ℝ) / Q') {j : ℕ} (hj : j ≤ max D D') :
    c μ j = c' μ j := by
  have hQQ : 0 < Q * Q' := Nat.mul_pos hQ hQ'
  have h1 : CutoffExpansion (Q * Q') (max D D') Z c :=
    (h.refine hQ hQQ (dvd_mul_right Q Q') hc).pad (le_max_left _ _) hcD
  have h2 : CutoffExpansion (Q * Q') (max D D') Z c' :=
    (h'.refine hQ' hQQ (dvd_mul_left Q' Q) hc').pad (le_max_right _ _) hcD'
  refine CutoffExpansion.coeff_unique hQQ h1 h2 ?_ hj
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hQr' : (Q' : ℝ) ≠ 0 := by exact_mod_cast hQ'.ne'
  rcases hμ with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨m * Q', ?_⟩
    push_cast
    field_simp
  · refine ⟨m * Q, ?_⟩
    push_cast
    field_simp

/-- **Every coefficient is determined**: off both lattices or above both degree bounds the two
systems vanish, on them they agree. -/
theorem CutoffExpansion.coeff_eq_of_lattices {Q Q' D D' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q')
    {Z : ℝ → ℝ} {c c' : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) (h' : CutoffExpansion Q' D' Z c')
    (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (hcD : ∀ μ j, D < j → c μ j = 0)
    (hc' : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q') → ∀ j, c' μ j = 0)
    (hcD' : ∀ μ j, D' < j → c' μ j = 0) (μ : ℝ) (j : ℕ) : c μ j = c' μ j := by
  by_cases hj : j ≤ max D D'
  · by_cases hμ : (∃ m : ℕ, μ = (m : ℝ) / Q) ∨ ∃ m : ℕ, μ = (m : ℝ) / Q'
    · exact CutoffExpansion.coeff_unique_of_lattices hQ hQ' h h' hc hcD hc' hcD' hμ hj
    · obtain ⟨h1, h2⟩ := not_or.1 hμ
      rw [hc μ (fun m hm => h1 ⟨m, hm⟩) j, hc' μ (fun m hm => h2 ⟨m, hm⟩) j]
  · have hj' := not_le.1 hj
    rw [hcD μ j (lt_of_le_of_lt (le_max_left _ _) hj'), hcD' μ j
      (lt_of_le_of_lt (le_max_right _ _) hj')]

/-! ### Support of the assembled canonical coefficients -/

section Assembled

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ) (x : JointData K n)

theorem gCoeff_eq_zero_of_not_lattice (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / commonQ k) (j : ℕ) : gCoeff ν h k β b x μ j = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  refine tanCoeff_eq_zero_of_not_lattice (ν I) (n I) (h I) (k I) (hk I) β hβ (hb I) _
    (fun m hm => ?_) j
  obtain ⟨c, hc⟩ := latticeQ_dvd_commonQ k I
  have hQ0 : (latticeQ (k I) : ℝ) ≠ 0 := by exact_mod_cast (latticeQ_pos (k I) (hk I)).ne'
  have hc0 : (c : ℝ) ≠ 0 := by
    have hpos := commonQ_pos k hk
    rw [hc] at hpos
    exact_mod_cast (Nat.pos_of_mul_pos_left hpos).ne'
  refine hμ (m * c) ?_
  rw [hm, hc]
  push_cast
  field_simp

theorem gCoeff_eq_zero_of_lt {μ : ℝ} {j : ℕ} (hj : commonD n < j) :
    gCoeff ν h k β b x μ j = 0 := by
  unfold gCoeff
  exact Finset.sum_eq_zero fun I _ =>
    tanCoeff_eq_zero_of_lt (ν I) (n I) (h I) (k I) β (b I) _ μ (lt_of_le_of_lt (le_commonD I) hj)

end Assembled

/-! ### Canonicity of the assembled coordinate-free coefficients -/

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}

/-- ★★★ **Canonicity of the assembled coefficients**: two certificate pairs for the same original
integral give the same coordinate-free expansion coefficients at every power–log index. -/
theorem ResolvedCertificate.CoefficientCertificate.expansionCoefficient_eq_of_certificates
    {C C' : ResolvedCertificate R D W K ϕ φ} (Cc : C.CoefficientCertificate)
    (Cc' : C'.CoefficientCertificate) (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
    (hφ : Measurable φ) (q : PowerLogIndex) :
    D.expansionCoefficient C.stratumMeasure Cc.field φ q =
      D.expansionCoefficient C'.stratumMeasure Cc'.field φ q := by
  rw [Cc.expansionCoefficient_eq_gCoeff, Cc'.expansionCoefficient_eq_gCoeff]
  exact CutoffExpansion.coeff_eq_of_lattices (commonQ_pos C.cores.k C.cores.k_pos)
    (commonQ_pos C'.cores.k C'.cores.k_pos) (C.cutoffExpansion_globalLaplace hK hϕ hϕ0 hφ)
    (C'.cutoffExpansion_globalLaplace hK hϕ hϕ0 hφ)
    (fun μ hμ j => gCoeff_eq_zero_of_not_lattice _ _ _ _ _ _ C.cores.k_pos C.β_pos
      C.cores.b_pos hμ j)
    (fun μ j hj => gCoeff_eq_zero_of_lt _ _ _ _ _ _ hj)
    (fun μ hμ j => gCoeff_eq_zero_of_not_lattice _ _ _ _ _ _ C'.cores.k_pos C'.β_pos
      C'.cores.b_pos hμ j)
    (fun μ j hj => gCoeff_eq_zero_of_lt _ _ _ _ _ _ hj) q.exponent q.logDegree

end Grammar
