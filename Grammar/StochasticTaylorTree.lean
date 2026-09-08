/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.OrderedRemainder

/-!
# The stochastic Taylor tree, one chart, every positive dimension (Stage S7 — Headline XXXV)

Unit 276 (Astra #33 A2). Let `X_n : Ω → DataSpace (n+1)` be measurable random Taylor data
(phase and amplitude, weighted-ℓ¹ at the box radius `b`) converging in distribution to `Z`, and
let `N_n → ∞` be sample sizes. Then

* **coefficients**: every finite vector of canonical coefficients converges in distribution,
  `(C_{μ_i,j_i}(X_n))_i ⇒ (C_{μ_i,j_i}(Z))_i` (`tendstoInDistribution_dataCoeffVec`; continuous
  mapping with Headline XXXIV);
* **ordered normalised remainders**: for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ n`,
  `R_{N_n}^{μ,j}(X_n) − C_{μ,j}(X_n) → 0` in probability (`tendstoInMeasure_orderedRemainder_sub`)
  and hence `R_{N_n}^{μ,j}(X_n) ⇒ C_{μ,j}(Z)` (`tendstoInDistribution_orderedRemainder`,
  **Headline XXXV**): the uniform-on-balls convergence of unit 275, the boundedness in
  probability of `‖X_n‖` (portmanteau on the closed sets `{‖·‖ ≥ m}`,
  `dataNormBounded_of_tendstoInDistribution`), and Slutsky's lemma
  (`tendstoInDistribution_of_tendstoInMeasure_sub`).

This is `thm:strataempiricalexpansion` at chart level in arbitrary normal dimension, conditional
on convergence in distribution of the weighted Taylor data. Non-claims: no derivation from
Hypothesis I (resolution, empirical-process convergence and the standard-form identity are
external); the data are `E_b`-valued by hypothesis (no common analytic radius is manufactured);
the limit need not be Gaussian; `N` is the paper's sample size; sample sizes are taken `≥ 0`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

section NormBounded

variable {d : ℕ}

/-- The tail probabilities of the norm of a random data element tend to zero. -/
theorem tendsto_measure_dataNorm_ge_atTop (Z : Ω' → DataSpace d) (hZ : AEMeasurable Z μ') :
    Tendsto (fun m : ℕ => μ' ((fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ))) atTop (𝓝 0) := by
  have hnull : ∀ m : ℕ, NullMeasurableSet ((fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ)) μ' :=
    fun m => hZ.norm.nullMeasurableSet_preimage measurableSet_Ici
  have hanti : Antitone fun m : ℕ => (fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ) := by
    intro m m' hmm' ω hω
    simp only [mem_preimage, mem_Ici] at hω ⊢
    exact le_trans (by exact_mod_cast hmm') hω
  have h := tendsto_measure_iInter_atTop (μ := μ') hnull hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ m : ℕ, (fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ)) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_nat_gt _
  rw [hempty, measure_empty] at h
  exact h

/-- **Norm-boundedness in probability** of random data converging in distribution. -/
theorem dataNormBounded_of_tendstoInDistribution (X : ι → Ω → DataSpace d) (Z : Ω' → DataSpace d)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η := by
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, le_rfl, Eventually.of_forall fun n => by rw [hηtop]; exact le_top⟩
  have hZ : AEMeasurable Z μ' := hX.aemeasurable_limit
  have hhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨m, hm⟩ :=
    ((tendsto_measure_dataNorm_ge_atTop Z hZ).eventually (gt_mem_nhds hhalf)).exists
  set F : Set (DataSpace d) := {a | (m : ℝ) ≤ ‖a‖} with hFdef
  have hF : IsClosed F := isClosed_le continuous_const continuous_norm
  have hFm : MeasurableSet F := hF.measurableSet
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto hF
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ n, (μ.map (X n)) F = μ (X n ⁻¹' F) := fun n =>
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hFm
  simp only [hmap, Measure.map_apply_of_aemeasurable hZ hFm] at hport
  have hZF : μ' (Z ⁻¹' F) < η / 2 := hm
  have hlt : limsup (fun n => μ (X n ⁻¹' F)) l < η :=
    lt_of_le_of_lt hport (lt_of_lt_of_le hZF ENNReal.half_le_self)
  refine ⟨m, Nat.cast_nonneg m, (eventually_lt_of_limsup_lt hlt).mono fun n hn => ?_⟩
  refine le_trans (measure_mono ?_) hn.le
  intro ω hω
  exact le_of_lt (show (m : ℝ) < ‖X n ω‖ from hω)

/-- **Uniform smallness on balls plus norm-boundedness in probability gives convergence in
probability to zero.** -/
theorem tendstoInMeasure_zero_of_uniform_on_balls (f : ι → Ω → ℝ) (X : ι → Ω → DataSpace d)
    (hf : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ ω, ‖X n ω‖ ≤ M → |f n ω| ≤ ε)
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  filter_upwards [hev, hf M hM (ε / 2) (half_pos hε)] with n hn hfn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra hcon
  have := hfn ω (not_lt.1 hcon)
  linarith

end NormBounded

/-- **Headline XXXV (coefficients)**: finite vectors of canonical coefficients converge in
distribution when the data do. -/
theorem tendstoInDistribution_dataCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (X : ι → Ω → DataSpace (n + 1)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i => dataCoeffVec n h k β b F ∘ X i) l
      (dataCoeffVec n h k β b F ∘ Z) (fun _ => μ) μ' :=
  hX.continuous_comp (continuous_taylorTree_coeffVec n h k hk β hβ hb F)

/-- A single canonical coefficient converges in distribution. -/
theorem tendstoInDistribution_dataBoxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ) (X : ι → Ω → DataSpace (n + 1))
    (Z : Ω' → DataSpace (n + 1)) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => dataBoxCoeff n h k β b (X i ω) μ₀ j) l
      (fun ω => dataBoxCoeff n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  hX.continuous_comp (g := fun x => dataBoxCoeff n h k β b x μ₀ j)
    (continuous_taylorTree_coeff n h k hk β hβ hb μ₀ j)

/-- The ordered remainder is a measurable function of the data (`N ≥ 0`). -/
theorem measurable_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : DataSpace (n + 1) => orderedRemainder n h k β b x μ₀ j N := by
  unfold orderedRemainder predSum expTerm
  refine Measurable.div_const (Measurable.sub (measurable_dataBoxIntegral n h k hβ.le hN hb) ?_) _
  exact Finset.measurable_sum _ fun p _ =>
    (measurable_taylorTree_coeff n h k hk β hβ hb p.1 p.2).mul_const _

/-- **The remainder minus the coefficient tends to zero in probability.** -/
theorem tendstoInMeasure_orderedRemainder_sub (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => orderedRemainder n h k β b (X i ω) μ₀ j (Nseq i) -
      dataBoxCoeff n h k β b (X i ω) μ₀ j) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls _ X (fun M hM ε hε => ?_)
    (dataNormBounded_of_tendstoInDistribution X Z hX)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_orderedRemainder n h k hk β hβ hb hμ hj M) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have := hi (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

variable [l.IsCountablyGenerated]

/-- **Headline XXXV — the stochastic Taylor tree, one chart, every positive dimension.** If the
random weighted Taylor data `X_n ⇒ Z` in `E_b × E_b` and `N_n → ∞` (`N_n ≥ 0`), then for every
target `(μ, j)` with `μ ∈ Q⁻¹ℕ` and `j ≤ n` the ordered normalised remainder converges in
distribution to the limiting coefficient:
`(Z(N_n; X_n) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(X_n) N_n^{-ν} (log N_n)^q) / (N_n^{-μ} (log N_n)^j)`
`  ⇒ C_{μ,j}(Z)`. -/
theorem tendstoInDistribution_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => orderedRemainder n h k β b (X i ω) μ₀ j (Nseq i)) l
      (fun ω => dataBoxCoeff n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_dataBoxCoeff n h k hk β hβ hb μ₀ j X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_orderedRemainder n h k hk β hβ hb μ₀ j (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_orderedRemainder_sub n h k hk β hβ hb hμ hj X Z hX Nseq hN

end Grammar
