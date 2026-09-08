/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticTaylorTreeJoint

/-!
# Tangential data and the integrated Taylor tree (Stage S9 — A3 statement lock)

Unit 278 (Astra #34, unit 1 of tranche A3). On a stratum the standard integral is integrated over
the tangential parameter `v ∈ K` against a finite measure `ν` (the paper's `∫_{S_I} … ρ_I(v) dv`;
**convention**: the partition-of-unity weight `ρ_I(v)` is absorbed into the amplitude family, so
the measure is the unweighted `dv`). The tangential data are continuous maps
`x : C(K, DataSpace d)` from a compact parameter space into the weighted-ℓ¹ data space
(`TangentialData`), with the sup norm: `‖x v‖ ≤ ‖x‖`. Definitions: the integrated standard
integral `𝒵(N; x) = ∫_K Z(N; x v) dν`, the integrated canonical coefficients
`𝒞_{μ,j}(x) = ∫_K C_{μ,j}(x v) dν`, the integrated predecessor sum and ordered normalised
remainder `ℛ_N^{μ,j}(x)`.

Results of this unit: integrability of all integrands (continuity on the compact `K`), and the
**integrated cutoff theorem** (`tanTaylorTree_cutoff_bound`): for `‖x‖ ≤ R`,
`|𝒵(N;x) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} 𝒞_{μ,j}(x) (log N)^j|`
`  ≤ ν(K) · b^{|h|+d} dataCutoffConst(R) · (N b^{2|k|})^{-L}(1+log(N b^{2|k|}))^n`
— the paper's cited-but-unstated `lemma:AsymInt` in its finite-cutoff form: no interchange of an
infinite series with the integral is needed, the finite cutoff estimate is integrated and
normalised. Also here: the generic probability lemmas of A2 (norm-boundedness in probability,
uniform-on-balls ⇒ in probability) restated for an arbitrary Borel normed group, so that they
apply to `C(K, DataSpace d)` in unit 280. Non-claims: `C(K, E)`-regularity of the tangential
Taylor data is a hypothesis (it is not inferred from pointwise analyticity in `u`); compact
support alone is not the domination.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-! ### Generic probability lemmas (Borel normed groups) -/

section Generic

variable {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem tendsto_measure_norm_ge_atTop' (Z : Ω' → E) (hZ : AEMeasurable Z μ') :
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

/-- **Norm-boundedness in probability** of a sequence converging in distribution (generic). -/
theorem normBounded_of_tendstoInDistribution' (X : ι → Ω → E) (Z : Ω' → E)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η := by
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, le_rfl, Eventually.of_forall fun n => by rw [hηtop]; exact le_top⟩
  have hZ : AEMeasurable Z μ' := hX.aemeasurable_limit
  have hhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨m, hm⟩ := ((tendsto_measure_norm_ge_atTop' Z hZ).eventually (gt_mem_nhds hhalf)).exists
  set F : Set E := {a | (m : ℝ) ≤ ‖a‖} with hFdef
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

/-- Uniform smallness on norm balls plus norm-boundedness in probability gives convergence in
probability to zero (generic in the data space and the error space). -/
theorem tendstoInMeasure_zero_of_uniform_on_balls'' {G : Type*} [NormedAddCommGroup G]
    (f : ι → Ω → G) (X : ι → Ω → E)
    (hf : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ ω, ‖X n ω‖ ≤ M → ‖f n ω‖ ≤ ε)
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
  simp only [mem_setOf_eq, sub_zero] at hω ⊢
  by_contra hcon
  have := hfn ω (not_lt.1 hcon)
  linarith

end Generic

/-! ### Tangential data -/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]

/-- Tangential data: continuous maps from the compact tangential parameter space into the data
space, with the sup norm. -/
abbrev TangentialData (K : Type*) [TopologicalSpace K] (d : ℕ) := C(K, DataSpace d)

noncomputable instance {d : ℕ} : MeasurableSpace (TangentialData K d) := borel (TangentialData K d)
instance {d : ℕ} : BorelSpace (TangentialData K d) := ⟨rfl⟩

theorem norm_tan_apply_le {d : ℕ} (x : TangentialData K d) (v : K) : ‖x v‖ ≤ ‖x‖ :=
  ContinuousMap.norm_coe_le_norm x v

theorem norm_tan_apply_sub_le {d : ℕ} (x y : TangentialData K d) (v : K) :
    ‖x v - y v‖ ≤ ‖x - y‖ := by
  have := ContinuousMap.norm_coe_le_norm (x - y) v
  simpa using this

variable (ν : Measure K) [IsFiniteMeasure ν]

/-- The integrated standard integral `𝒵(N; x) = ∫_K Z(N; x v) dν`. -/
noncomputable def tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (x : TangentialData K (n + 1)) : ℝ :=
  ∫ v, dataBoxIntegral n h k β N b (x v) ∂ν

/-- The integrated canonical coefficient `𝒞_{μ,j}(x) = ∫_K C_{μ,j}(x v) dν`. -/
noncomputable def tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : TangentialData K (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  ∫ v, dataBoxCoeff n h k β b (x v) μ j ∂ν

/-- The integrated predecessor sum. -/
noncomputable def tanPredSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  ∑ p ∈ predSet n (latticeQ k) μ j,
    tanCoeff ν n h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)

/-- The integrated ordered normalised remainder `ℛ_N^{μ,j}(x)`. -/
noncomputable def tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  (tanIntegral ν n h k β N b x - tanPredSum ν n h k β b x μ j N) / (N ^ (-μ) * Real.log N ^ j)

variable [OpensMeasurableSpace K]

/-- A continuous real function on the compact `K` is `ν`-integrable. -/
theorem integrable_of_continuous_compact {f : K → ℝ} (hf : Continuous f) : Integrable f ν :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem integrable_dataBoxIntegral_tan (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) (x : TangentialData K (n + 1)) :
    Integrable (fun v => dataBoxIntegral n h k β N b (x v)) ν :=
  integrable_of_continuous_compact ν ((continuous_dataBoxIntegral n h k hβ hN hb).comp x.continuous)

theorem integrable_dataBoxCoeff_tan (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) :
    Integrable (fun v => dataBoxCoeff n h k β b (x v) μ j) ν :=
  integrable_of_continuous_compact ν
    ((continuous_taylorTree_coeff n h k hk β hβ hb μ j).comp x.continuous)

/-- The integrated spectral sum is the integral of the pointwise spectral sum. -/
theorem integral_spectralSum_tan (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) (L N : ℝ) :
    ∫ v, (∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b (x v) μ j * Real.log N ^ j) ∂ν =
      ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), tanCoeff ν n h k β b x μ j * Real.log N ^ j := by
  unfold tanCoeff
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [integral_const_mul, integral_finset_sum]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · intro j _
      exact (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j).mul_const _
  · intro μ _
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun j _ =>
      (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j).mul_const _

/-- **The integrated cutoff theorem (`lemma:AsymInt`, finite-cutoff form)**: for `‖x‖ ≤ R`,
`|𝒵(N;x) − ∑_{Λ_L} N^{-μ} ∑_j 𝒞_{μ,j}(x) (log N)^j| ≤ ν(K) · b^{|h|+d} dataCutoffConst(R) ·
(N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^n`. -/
theorem tanTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 0 < N)
    (hN' : 1 ≤ boxScale k b N) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) :
    |tanIntegral ν n h k β N b x - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), tanCoeff ν n h k β b x μ j * Real.log N ^ j| ≤
      (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)) := by
  unfold tanIntegral
  rw [← integral_spectralSum_tan ν n h k hk β hβ hb x L N,
    ← integral_sub (integrable_dataBoxIntegral_tan ν n h k hβ.le hN.le hb x)]
  · have hbound : ∀ v, ‖dataBoxIntegral n h k β N b (x v) - ∑ μ ∈ latticeBelow (latticeQ k) L,
        N ^ (-μ) * ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b (x v) μ j *
          Real.log N ^ j‖ ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
            (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by
      intro v
      rw [Real.norm_eq_abs]
      exact dataTaylorTree_cutoff_bound n h k hk β hβ hL hb hN hN'
        ((norm_tan_apply_le x v).trans hx)
    have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
    rw [Real.norm_eq_abs] at this
    rw [mul_comm]
    simpa [measureReal_def] using this
  · refine integrable_finset_sum _ fun μ _ => Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun j _ =>
      (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j).mul_const _

end Grammar
