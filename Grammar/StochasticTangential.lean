/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TangentialRemainder

/-!
# The stochastic Taylor tree after tangential integration (Stage S11 — Headline XXXVI)

Unit 280 (Astra #34, unit 3 of tranche A3). Let `X_ℓ : Ω → C(K, DataSpace (n+1))` be measurable
random tangential Taylor data (phase and amplitude, weighted-ℓ¹ at the box radius `b`, continuous
in the tangential parameter `v ∈ K`, `K` compact) converging in distribution to `X`, and let
`N_ℓ → ∞` be sample sizes (`N_ℓ ≥ 0`). Then for the stratum integral
`𝒵(N; x) = ∫_K Z(N; x v) dν`:

* every finite vector of integrated coefficients converges in distribution,
  `(𝒞_{μ_i,j_i}(X_ℓ))_i ⇒ (𝒞_{μ_i,j_i}(X))_i` (`tendstoInDistribution_tanCoeffVec`);
* for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ n`, the integrated ordered normalised remainder
  satisfies `ℛ_{N_ℓ}^{μ,j}(X_ℓ) − 𝒞_{μ,j}(X_ℓ) → 0` in probability
  (`tendstoInMeasure_tanRemainder_sub`) and `ℛ_{N_ℓ}^{μ,j}(X_ℓ) ⇒ 𝒞_{μ,j}(X)`
  (`tendstoInDistribution_tanRemainder`, **Headline XXXVI**), jointly for finitely many targets
  (`tendstoInDistribution_tanRemainderVec`).

This is `thm:strataempiricalexpansion` for one stratum in arbitrary normal dimension: the
tangential integration of the paper's proof (`lemma:AsymInt`) is done with explicit domination,
conditional on convergence in distribution of the tangential data in `C(K, E_b × E_b)`.
Non-claims: the `C(K, ·)`-regularity and the convergence of the tangential data are hypotheses (not
derived from Hypothesis I or from pointwise analyticity); the partition weight is absorbed into the
amplitude; one stratum (no assembly); no Gaussianity; `N_ℓ` deterministic.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- A finite vector of integrated coefficients. -/
noncomputable def tanCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {m : ℕ}
    (F : Fin m → ℝ × ℕ) (x : TangentialData K (n + 1)) : Fin m → ℝ :=
  fun i => tanCoeff ν n h k β b x (F i).1 (F i).2

theorem continuous_tanCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) :
    Continuous (tanCoeffVec ν n h k β b F) :=
  continuous_pi fun i => continuous_tanCoeff ν n h k hk β hβ hb (F i).1 (F i).2

/-- **Headline XXXVI (coefficients)**: finite vectors of integrated coefficients converge in
distribution when the tangential data do. -/
theorem tendstoInDistribution_tanCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (X : ι → Ω → TangentialData K (n + 1)) (Z : Ω' → TangentialData K (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i => tanCoeffVec ν n h k β b F ∘ X i) l
      (tanCoeffVec ν n h k β b F ∘ Z) (fun _ => μ) μ' :=
  hX.continuous_comp (continuous_tanCoeffVec ν n h k hk β hβ hb F)

theorem tendstoInDistribution_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ)
    (X : ι → Ω → TangentialData K (n + 1)) (Z : Ω' → TangentialData K (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => tanCoeff ν n h k β b (X i ω) μ₀ j) l
      (fun ω => tanCoeff ν n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  hX.continuous_comp (g := fun x => tanCoeff ν n h k β b x μ₀ j)
    (continuous_tanCoeff ν n h k hk β hβ hb μ₀ j)

/-- The integrated ordered remainder is measurable in the tangential data (`N ≥ 0`). -/
theorem measurable_tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : TangentialData K (n + 1) => tanRemainder ν n h k β b x μ₀ j N := by
  unfold tanRemainder tanPredSum
  refine Measurable.div_const (Measurable.sub (measurable_tanIntegral ν n h k hβ.le hN hb) ?_) _
  exact Finset.measurable_sum _ fun p _ =>
    (measurable_tanCoeff ν n h k hk β hβ hb p.1 p.2).mul_const _

/-- The vector of integrated ordered remainders at the targets `F i`. -/
noncomputable def tanRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {m : ℕ}
    (F : Fin m → ℝ × ℕ) (x : TangentialData K (n + 1)) (N : ℝ) : Fin m → ℝ :=
  fun i => tanRemainder ν n h k β b x (F i).1 (F i).2 N

theorem measurable_tanRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : TangentialData K (n + 1) => tanRemainderVec ν n h k β b F x N :=
  measurable_pi_lambda _ fun i => measurable_tanRemainder ν n h k hk β hβ hb (F i).1 (F i).2 hN

/-- **The integrated remainder minus the integrated coefficient tends to zero in probability.** -/
theorem tendstoInMeasure_tanRemainder_sub (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → TangentialData K (n + 1)) (Z : Ω' → TangentialData K (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => tanRemainder ν n h k β b (X i ω) μ₀ j (Nseq i) -
      tanCoeff ν n h k β b (X i ω) μ₀ j) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_)
    (normBounded_of_tendstoInDistribution' X Z hX)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_tanRemainder ν n h k hk β hβ hb hμ hj M) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have := hi (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  simpa [Real.norm_eq_abs] using this.le

/-- The vector of integrated remainders minus the vector of coefficients tends to zero in
probability. -/
theorem tendstoInMeasure_tanRemainderVec_sub (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (hF : ∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n)
    (X : ι → Ω → TangentialData K (n + 1)) (Z : Ω' → TangentialData K (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => tanRemainderVec ν n h k β b F (X i ω) (Nseq i) -
      tanCoeffVec ν n h k β b F (X i ω)) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_)
    (normBounded_of_tendstoInDistribution' X Z hX)
  have hall : ∀ i : Fin m, ∀ᶠ N in atTop, ∀ x ∈ Metric.closedBall (0 : TangentialData K (n + 1)) M,
      dist (tanCoeff ν n h k β b x (F i).1 (F i).2)
        (tanRemainder ν n h k β b x (F i).1 (F i).2 N) < ε := fun i =>
    Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_tanRemainder ν n h k hk β hβ hb (hF i).1 (hF i).2 M) ε hε
  have hev := hN.eventually (Filter.eventually_all.2 hall)
  filter_upwards [hev] with i hi ω hω
  rw [pi_norm_le_iff_of_nonneg hε.le]
  intro t
  have := hi t (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  simpa [tanRemainderVec, tanCoeffVec, Real.norm_eq_abs] using this.le

variable [l.IsCountablyGenerated]

/-- **Headline XXXVI — the stochastic Taylor tree after tangential integration.** If the random
tangential Taylor data `X_ℓ ⇒ X` in `C(K, E_b × E_b)` and `N_ℓ → ∞` (`N_ℓ ≥ 0`), then for every
target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ n`, the integrated ordered normalised remainder converges in
distribution to the limiting integrated coefficient: `ℛ_{N_ℓ}^{μ,j}(X_ℓ) ⇒ 𝒞_{μ,j}(X)`. -/
theorem tendstoInDistribution_tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → TangentialData K (n + 1)) (hXm : ∀ i, Measurable (X i))
    (Z : Ω' → TangentialData K (n + 1)) (hX : TendstoInDistribution X l Z (fun _ => μ) μ')
    (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => tanRemainder ν n h k β b (X i ω) μ₀ j (Nseq i)) l
      (fun ω => tanCoeff ν n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_tanCoeff ν n h k hk β hβ hb μ₀ j X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_tanRemainder ν n h k hk β hβ hb μ₀ j (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_tanRemainder_sub ν n h k hk β hβ hb hμ hj X Z hX Nseq hN

/-- **Headline XXXVI (joint form)**: finitely many integrated ordered remainders converge jointly
in distribution to the vector of limiting integrated coefficients. -/
theorem tendstoInDistribution_tanRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (hF : ∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n)
    (X : ι → Ω → TangentialData K (n + 1)) (hXm : ∀ i, Measurable (X i))
    (Z : Ω' → TangentialData K (n + 1)) (hX : TendstoInDistribution X l Z (fun _ => μ) μ')
    (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => tanRemainderVec ν n h k β b F (X i ω) (Nseq i)) l
      (fun ω => tanCoeffVec ν n h k β b F (Z ω)) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_tanCoeffVec ν n h k hk β hβ hb F X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_tanRemainderVec ν n h k hk β hβ hb F (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_tanRemainderVec_sub ν n h k hk β hβ hb F hF X Z hX Nseq hN

end Grammar
