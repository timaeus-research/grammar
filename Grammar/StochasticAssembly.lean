/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartAssemblyGlobal

/-!
# The stochastic Taylor tree after finite chart assembly (Stage S15 — Headline XXXVII)

Unit 284 (Astra #34, tranche A3). Let `X_ℓ : Ω → JointData K n` be measurable random joint
tangential Taylor data of finitely many charts converging in distribution to `X`, let
`N_ℓ → ∞` (`N_ℓ ≥ 0`), and let the **external chart decomposition** hold: the global normalised
partition function `Z^0_ℓ` equals `∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` with a residual `E_ℓ` that is
`o_p(N_ℓ^{-μ}(log N_ℓ)^j)` at the target. Then for every target `(μ, j)` with `μ` on the common
lattice `Q⁻¹ℕ` and `j ≤ D`:

* the global coefficients converge in distribution, `C^{glob}_{μ,j}(X_ℓ) ⇒ C^{glob}_{μ,j}(X)`
  (`tendstoInDistribution_gCoeff`; joint finite vectors likewise);
* the global ordered normalised remainder of the assembled integral converges in distribution
  to the limiting global coefficient (`tendstoInDistribution_gRemainder`), and so does the ordered
  normalised remainder of `Z^0_ℓ` itself (`tendstoInDistribution_assembled`, **Headline XXXVII**):
  `(Z^0_ℓ − ∑_{(ν,q) ≺ (μ,j)} C^{glob}_{ν,q}(X_ℓ) N_ℓ^{-ν}(log N_ℓ)^q) / (N_ℓ^{-μ}(log N_ℓ)^j)`
  `  ⇒ C^{glob}_{μ,j}(X)`.

This is the convergence-in-distribution clause of `thm:strataempiricalexpansion` assembled over
finitely many charts in arbitrary normal dimensions, conditional on (i) joint convergence in
distribution of the chart data in `∏_I C(K_I, E_{b_I} × E_{b_I})`, and (ii) the external
decomposition with a residual negligible at the target scale. Non-claims: (i) and (ii) are not
derived (the resolution, the partition of unity, the away-from-minimum contribution, the
empirical-process convergence and the standard-form identity are external inputs); the common
lattice is an indexing superset of the paper's `Λ^*` (coefficients may cancel across charts); no
Gaussianity; `N_ℓ` deterministic.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- **Global coefficients converge in distribution** when the joint chart data do. -/
theorem tendstoInDistribution_gCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (μ₀ : ℝ) (j : ℕ) (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => gCoeff ν h k β b (X i ω) μ₀ j) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  hX.continuous_comp (g := fun x => gCoeff ν h k β b x μ₀ j)
    (continuous_gCoeff ν h k β b hk hβ hb μ₀ j)

/-- A finite vector of global coefficients. -/
noncomputable def gCoeffVec {m : ℕ} (F : Fin m → ℝ × ℕ) (x : JointData K n) : Fin m → ℝ :=
  fun i => gCoeff ν h k β b x (F i).1 (F i).2

theorem tendstoInDistribution_gCoeffVec (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {m : ℕ} (F : Fin m → ℝ × ℕ) (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i => gCoeffVec ν h k β b F ∘ X i) l (gCoeffVec ν h k β b F ∘ Z)
      (fun _ => μ) μ' :=
  hX.continuous_comp (continuous_pi fun i => continuous_gCoeff ν h k β b hk hβ hb (F i).1 (F i).2)

/-- The global remainder minus the global coefficient tends to zero in probability. -/
theorem tendstoInMeasure_gRemainder_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i) -
      gCoeff ν h k β b (X i ω) μ₀ j) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun R hR ε hε => ?_)
    (normBounded_of_tendstoInDistribution' X Z hX)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ hj R) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have := hi (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  simpa [Real.norm_eq_abs] using this.le

variable [l.IsCountablyGenerated]

/-- **The assembled ordered remainder converges in distribution** to the limiting global
coefficient. -/
theorem tendstoInDistribution_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_gCoeff ν h k β b hk hβ hb μ₀ j X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_gRemainder ν h k β b hk hβ hb μ₀ j (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_gRemainder_sub ν h k β b hk hβ hb hμ hj X Z hX Nseq hN

/-- **Headline XXXVII — the stochastic Taylor tree after finite chart assembly.** Under the
external decomposition `Z^0_ℓ = ∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` with the residual `E_ℓ` negligible in
probability at the target scale `N_ℓ^{-μ}(log N_ℓ)^j`, the ordered normalised remainder of `Z^0_ℓ`
converges in distribution to the limiting global coefficient `C^{glob}_{μ,j}(X)`. -/
theorem tendstoInDistribution_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ) (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun _ => 0)) :
    TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hR := tendstoInDistribution_gRemainder ν h k β b hk hβ hb hμ hj X hXm Z hX Nseq hN0 hN
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hR ?_ fun i => ?_
  · -- the difference is the normalised residual
    have heq : (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) -
        (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i)) =
        fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j) := by
      funext i ω
      simp only [Pi.sub_apply]
      unfold gRemainder abstractRemainder
      rw [hdecomp i ω]
      ring
    rw [heq]; exact hE
  · -- measurability of the normalised remainder of `Z^0`
    refine Measurable.aemeasurable (Measurable.div_const (Measurable.sub (hZm i) ?_) _)
    unfold absPredSum absTerm
    exact Finset.measurable_sum _ fun p _ =>
      (((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).comp (hXm i)).mul_const _

end Grammar
