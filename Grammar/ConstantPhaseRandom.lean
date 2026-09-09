/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Grammar.ConstantPhaseCorrection
import Grammar.PhaseLeadingTerm

/-!
# A random constant phase (unit 338; Astra #40 unit 4)

If the fluctuation is a random constant `X : Ω → ℝ` (e.g. the Gaussian `ξ(0) = X` of the paper's
`rem:pop_vs_emp`), the deterministic constant-phase results compose pointwise: the normalised energy
`Q_N(X) = N 𝒵_N[K∘π η; X]/𝒵_N[η; X]` converges almost surely to `c₁(X) = λ/β + (X/2β) ∂_a log A(X)`
and `log N (Q_N(X) − c₁(X))` converges almost surely to `c₂(X)`, hence both converge in distribution
(`constPhase_energy_random`, `constPhase_energy_correction_random`). The measurability inputs are
the continuity of the constant-phase integral in the phase (`continuous_constPhase_integral`,
dominated convergence on the unit box) and the measurability of derivatives (`measurable_deriv`).
Under a positive face witness the nonvanishing `A(X) ≠ 0` is automatic. Not claimed: convergence of
expectations over `X` (that needs uniform integrability); anything for a phase moving with `N`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Continuity of the constant-phase integral in the phase** (`β > 0`, `N ≥ 0`). -/
theorem continuous_constPhase_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {N : ℝ} (hN : 0 ≤ N) (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) :
    Continuous fun a => origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  refine continuous_iff_continuousAt.2 fun a₀ => ?_
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  simp only [hset]
  have hF : ∀ a, Continuous fun u : Fin (n + 1) → ℝ => η u * (∏ i, u i ^ h i) *
      Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a) := by
    intro a
    fun_prop
  have hbc : Continuous fun u : Fin (n + 1) → ℝ => |η u| * |∏ i, u i ^ h i| *
      Real.exp (β * Real.sqrt N * (|a₀| + 1)) := by
    fun_prop
  refine continuousAt_of_dominated (bound := fun u => |η u| * |∏ i, u i ^ h i| *
      Real.exp (β * Real.sqrt N * (|a₀| + 1)))
    (Eventually.of_forall fun a => (hF a).aestronglyMeasurable) ?_
    (integrableOn_unitBox_of_continuous _ hbc) (Eventually.of_forall fun u => ?_)
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds a₀ one_pos) fun a ha => ?_
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu => ?_
    have ha' : |a| ≤ |a₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at ha
      have := abs_sub_abs_le_abs_sub a a₀
      linarith
    have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
    have hQ0 : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
    have hQ1 : ∏ i, u i ^ k i ≤ 1 :=
      Finset.prod_le_one (fun i _ => pow_nonneg (hu' i).1.le _)
        (fun i _ => pow_le_one₀ (hu' i).1.le (hu' i).2)
    have hP0 : 0 ≤ ∏ i, u i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
    have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
    have hexp : Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a)
        ≤ Real.exp (β * Real.sqrt N * (|a₀| + 1)) := by
      rw [Real.exp_le_exp]
      have h0 : 0 ≤ β * N * ∏ i, u i ^ (2 * k i) := by positivity
      have h1 : β * (Real.sqrt N * ∏ i, u i ^ k i) * a ≤ β * Real.sqrt N * (|a₀| + 1) := by
        calc β * (Real.sqrt N * ∏ i, u i ^ k i) * a ≤ β * (Real.sqrt N * ∏ i, u i ^ k i) * |a| :=
              mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity)
          _ ≤ β * (Real.sqrt N * 1) * (|a₀| + 1) := by gcongr
          _ = β * Real.sqrt N * (|a₀| + 1) := by ring
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  · have hc : Continuous fun a : ℝ => η u * (∏ i, u i ^ h i) *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a) := by
      fun_prop
    exact hc.continuousAt

/-- The normalised constant-phase energy `Q_N(a) = N 𝒵_N[K∘π η; a]/𝒵_N[η; a]`. -/
noncomputable def constPhaseEnergy (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) : ℝ :=
  N * (origPhaseIntegral n h k β N 1 (fun _ => a) (fun u => (∏ i, u i ^ (2 * k i)) * η u) /
    origPhaseIntegral n h k β N 1 (fun _ => a) η)

/-- The leading constant-phase energy `c₁(a) = λ/β + (a/2β) A'(a)/A(a)`. -/
noncomputable def constPhaseC1 (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cη : CoeffFamily (n + 1))
    (l a : ℝ) : ℝ :=
  l / β + a / (2 * β) *
    deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
      (multCount (ratioExp h k) l - 1)) a /
    familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)

/-- The first log correction `c₂(a) = −(m−1)/β + (a/2β)(B'A − BA')/A²`. -/
noncomputable def constPhaseC2 (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cη : CoeffFamily (n + 1))
    (l a : ℝ) : ℝ :=
  -((multCount (ratioExp h k) l : ℝ) - 1) / β + a / (2 * β) *
    (deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a *
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) -
      constPhaseSecondCoeff n h k β cη a l *
      deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
        (multCount (ratioExp h k) l - 1)) a) /
    familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2

theorem measurable_constPhaseEnergy (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {N : ℝ} (hN : 0 ≤ N) (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) :
    Measurable (constPhaseEnergy n h k β N η) := by
  unfold constPhaseEnergy
  have hη' : Continuous fun u : Fin (n + 1) → ℝ => (∏ i, u i ^ (2 * k i)) * η u := by fun_prop
  exact ((continuous_constPhase_integral n h k hβ hN _ hη').measurable.div
    (continuous_constPhase_integral n h k hβ hN η hηc).measurable).const_mul N

theorem measurable_constPhaseCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) (j : ℕ) :
    Measurable fun a => familySpectralCoeff n h k β (constFamily a) cη l j :=
  (continuous_iff_continuousAt.2 fun a =>
    (hasDerivAt_constPhase_coeff n h k hk hβ hη hl j a).continuousAt).measurable

theorem measurable_constPhaseSecondCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) :
    Measurable fun a => constPhaseSecondCoeff n h k β cη a l := by
  unfold constPhaseSecondCoeff
  split_ifs
  · exact measurable_constPhaseCoeff n h k hk hβ hη hl _
  · exact measurable_const

theorem measurable_constPhaseC1 (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) :
    Measurable (constPhaseC1 n h k β cη l) := by
  unfold constPhaseC1
  exact measurable_const.add (((measurable_id.div_const _).mul (measurable_deriv _)).div
    (measurable_constPhaseCoeff n h k hk hβ hη hl _))

theorem measurable_constPhaseC2 (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) :
    Measurable (constPhaseC2 n h k β cη l) := by
  unfold constPhaseC2
  have hA := measurable_constPhaseCoeff n h k hk hβ hη hl (multCount (ratioExp h k) l - 1)
  have hB := measurable_constPhaseSecondCoeff n h k hk hβ hη hl
  exact measurable_const.add (((measurable_id.div_const _).mul
    (((measurable_deriv _).mul hA).sub (hB.mul (measurable_deriv _)))).div (hA.pow_const 2))

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {l : Filter ι} [l.IsCountablyGenerated]

/-- **Random constant phase, leading order**: for a random constant phase `X` with `A(X) ≠ 0`,
`Q_N(X) → c₁(X)` almost surely and in distribution. -/
theorem constPhase_energy_random (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {lam : ℝ}
    (hmin : ∀ i, lam ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = lam)
    (X : Ω → ℝ) (hXm : Measurable X)
    (hA : ∀ ω, familySpectralCoeff n h k β (constFamily (X ω)) cη lam
      (multCount (ratioExp h k) lam - 1) ≠ 0)
    (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) :
    (∀ ω, Tendsto (fun i => constPhaseEnergy n h k β (Nseq i) η (X ω)) l
      (𝓝 (constPhaseC1 n h k β cη lam (X ω)))) ∧
    TendstoInDistribution (fun i ω => constPhaseEnergy n h k β (Nseq i) η (X ω)) l
      (fun ω => constPhaseC1 n h k β cη lam (X ω)) (fun _ => μ) μ := by
  have hl0 : 0 < lam := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hpt : ∀ ω, Tendsto (fun i => constPhaseEnergy n h k β (Nseq i) η (X ω)) l
      (𝓝 (constPhaseC1 n h k β cη lam (X ω))) := fun ω =>
    (constPhase_energy_ratio_chart n h k hk hβ (X ω) hη hηc hev hmin hatt (hA ω)).comp hN
  refine ⟨hpt, tendstoInDistribution_of_ae_tendsto (fun i => ?_) ?_ (Eventually.of_forall hpt)⟩
  · exact ((measurable_constPhaseEnergy n h k hβ (hN0 i) η hηc).comp hXm).aemeasurable
  · exact ((measurable_constPhaseC1 n h k hk hβ hη hl0).comp hXm).aemeasurable

/-- **Random constant phase, first log correction**: `log N (Q_N(X) − c₁(X)) → c₂(X)` almost surely
and in distribution. -/
theorem constPhase_energy_correction_random (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {lam : ℝ}
    (hmin : ∀ i, lam ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = lam)
    (X : Ω → ℝ) (hXm : Measurable X)
    (hA : ∀ ω, familySpectralCoeff n h k β (constFamily (X ω)) cη lam
      (multCount (ratioExp h k) lam - 1) ≠ 0)
    (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) :
    (∀ ω, Tendsto (fun i => Real.log (Nseq i) *
      (constPhaseEnergy n h k β (Nseq i) η (X ω) - constPhaseC1 n h k β cη lam (X ω))) l
      (𝓝 (constPhaseC2 n h k β cη lam (X ω)))) ∧
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
      (constPhaseEnergy n h k β (Nseq i) η (X ω) - constPhaseC1 n h k β cη lam (X ω))) l
      (fun ω => constPhaseC2 n h k β cη lam (X ω)) (fun _ => μ) μ := by
  have hl0 : 0 < lam := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hpt : ∀ ω, Tendsto (fun i => Real.log (Nseq i) *
      (constPhaseEnergy n h k β (Nseq i) η (X ω) - constPhaseC1 n h k β cη lam (X ω))) l
      (𝓝 (constPhaseC2 n h k β cη lam (X ω))) := fun ω =>
    (constPhase_energy_correction_chart n h k hk hβ (X ω) hη hηc hev hmin hatt (hA ω)).comp hN
  refine ⟨hpt, tendstoInDistribution_of_ae_tendsto (fun i => ?_) ?_ (Eventually.of_forall hpt)⟩
  · exact ((((measurable_constPhaseEnergy n h k hβ (hN0 i) η hηc).comp hXm).sub
      ((measurable_constPhaseC1 n h k hk hβ hη hl0).comp hXm)).const_mul _).aemeasurable
  · exact ((measurable_constPhaseC2 n h k hk hβ hη hl0).comp hXm).aemeasurable

end Grammar
