# Fidelity review v29 — Programme S tranche A3, units 278–280: tangential data, the integrated cutoff/remainder (`lemma:AsymInt`), Headline XXXVI

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (repository `timaeus-research/grammar`, branch `tide/stochastic-taylor-tree`, pin `b624506`) of the grammar paper's §4.3 (`thm:strataempiricalexpansion`). Reviews v27/v28 passed tranche A1–A2 (Headline XXXIV: canonical coefficients `dataBoxCoeff n h k β b x μ j` are Lipschitz on balls / continuous / measurable on the weighted-ℓ¹ data space `DataSpace d = ℓ¹((Fin d → ℕ) ⊕ (Fin d → ℕ))`; Headline XXXV: for `X_ℓ ⇒ Z` in `DataSpace` and `N_ℓ → ∞`, coefficient vectors and ordered normalised remainders `orderedRemainder n h k β b x μ j N = (Z(N;x) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(x) N^{-ν}(log N)^q)/(N^{-μ}(log N)^j)` converge in distribution, with the explicit majorant `abs_orderedRemainder_sub_le : ‖x‖ ≤ R → e ≤ N → 1 ≤ N b^{2|k|} → |R_N^{μ,j}(x) − C_{μ,j}(x)| ≤ remainderMajorant n h k β b μ j R N`, `remainderMajorant → 0`). Astra consult #34 authorised tranche A3 (tangential integration and finite chart assembly; 12–16 units, hard review after unit 3) with the design: a finite-measure integration core plus the public interface `C(K, DataSpace)` for compact `K`; the partition-of-unity weight `ρ_I(v)` absorbed into the amplitude family. Units 278–280 are the first three units. Please review the STATEMENTS (mechanical excerpts: docstring + statement up to `:=`; the extractor may truncate/duplicate — the source has exactly one of each; everything compiles with zero `sorry` and no additional axioms; ambient `variable` declarations are listed per file) and the one proof reproduced in full.

## The paper's proof step being formalised
`Z_n[β;ξ_n,η;I] = ∫_{S_I} Z(β,n;ξ_n(·,v),η(·,v)) ρ_I(v) dv ∼ ∑_{μ∈Λ_I} ∑_{m} (∫_{S_I} C_{μ,m,I}(ξ_n,v) dv) n^{-μ}(log n)^{m-1}` "by `\cref{lemma:AsymInt}`" (no such lemma in the source); then the sum over strata and convergence in distribution of the coefficients.

## Statements

### Grammar/TangentialData.lean

Ambient `variable` declarations:
```lean
variable {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
variable (ν : Measure K) [IsFiniteMeasure ν]
variable [OpensMeasurableSpace K]
```

```lean
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

```
### Grammar/TangentialRemainder.lean

Ambient `variable` declarations:
```lean
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
```

```lean
/-!
# The integrated ordered remainder: continuity and uniform convergence (Stage S10)

Unit 279 (Astra #34, unit 2 of tranche A3). The integrated canonical coefficients
`𝒞_{μ,j}(x) = ∫_K C_{μ,j}(x v) dν` and, for fixed `N ≥ 0`, the integrated integral
`𝒵(N; x)` are Lipschitz on sup-norm balls of `C(K, DataSpace)` with constants
`ν(K) · dataLipConst`, resp. `ν(K) ·` (the ballwise constant of unit 274), hence continuous and
Borel measurable (`continuous_tanCoeff`, `continuous_tanIntegral`). The integrated ordered
normalised remainder is the integral of the pointwise one,
`ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x) = ∫_K (R_N^{μ,j}(x v) − C_{μ,j}(x v)) dν` (`tanRemainder_sub_tanCoeff`),
so on the sup-norm ball of radius `R`, `|ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x)| ≤ ν(K) · remainderMajorant N`
(`abs_tanRemainder_sub_le`) and `ℛ_N^{μ,j} → 𝒞_{μ,j}` uniformly on the ball
(`tendstoUniformlyOn_tanRemainder`). This is the deterministic `lemma:AsymInt` in ordered-remainder
form, with explicit domination.
-/

theorem abs_tanCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x y : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |tanCoeff ν n h k β b y μ j - tanCoeff ν n h k β b x μ j| ≤
      (ν univ).toReal * dataLipConst n h k β b μ j R * ‖y - x‖ := by
  unfold tanCoeff
  rw [← integral_sub (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb y μ j)
    (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j)]
  have hbound : ∀ v, ‖dataBoxCoeff n h k β b (y v) μ j - dataBoxCoeff n h k β b (x v) μ j‖ ≤
      dataLipConst n h k β b μ j R * ‖y - x‖ := by
    intro v
    rw [Real.norm_eq_abs]
    refine (abs_dataBoxCoeff_sub_le n h k hk β hβ hb ((norm_tan_apply_le x v).trans hx)
      ((norm_tan_apply_le y v).trans hy) μ j).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_tan_apply_sub_le y x v)
      (dataLipConst_nonneg n h k β hβ hb μ j ((norm_nonneg x).trans hx))
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The integrated coefficient is continuous on `C(K, DataSpace)`. -/
theorem continuous_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Continuous fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : TangentialData K (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hC0 : 0 ≤ (ν univ).toReal * dataLipConst n h k β b μ j R :=
    mul_nonneg ENNReal.toReal_nonneg (dataLipConst_nonneg n h k β hβ hb μ j hR0)
  have hlip : LipschitzOnWith (Real.toNNReal ((ν univ).toReal * dataLipConst n h k β b μ j R))
      (fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j)
      (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_tanCoeff_sub_le ν n h k hk β hβ hb hz' hy' μ j
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Measurable fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j :=
  (continuous_tanCoeff ν n h k hk β hβ hb μ j).measurable

theorem abs_tanIntegral_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) {R : ℝ} {x y : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) :
    |tanIntegral ν n h k β N b y - tanIntegral ν n h k β N b x| ≤
      (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) *
        (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
          (1 + R * (β * Real.sqrt (boxScale k b N))))) * ‖y - x‖ := by
  unfold tanIntegral
  rw [← integral_sub (integrable_dataBoxIntegral_tan ν n h k hβ hN hb y)
    (integrable_dataBoxIntegral_tan ν n h k hβ hN hb x)]
  have hK0 : 0 ≤ b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
      (1 + R * (β * Real.sqrt (boxScale k b N)))) := by
    have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    positivity
  have hbound : ∀ v, ‖dataBoxIntegral n h k β N b (y v) - dataBoxIntegral n h k β N b (x v)‖ ≤
      b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
        (1 + R * (β * Real.sqrt (boxScale k b N)))) * ‖y - x‖ := by
    intro v
    rw [Real.norm_eq_abs]
    refine (abs_dataBoxIntegral_sub_le n h k hβ hN hb ((norm_tan_apply_le x v).trans hx)
      ((norm_tan_apply_le y v).trans hy)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_tan_apply_sub_le y x v) hK0
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The integrated integral is continuous on `C(K, DataSpace)` (fixed `N ≥ 0`). -/
theorem continuous_tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Continuous fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : TangentialData K (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set C := (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) *
    (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
      (1 + R * (β * Real.sqrt (boxScale k b N))))) with hC
  have hC0 : 0 ≤ C := by
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    have := ENNReal.toReal_nonneg (a := ν univ)
    positivity
  have hlip : LipschitzOnWith (Real.toNNReal C)
      (fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x)
      (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_tanIntegral_sub_le ν n h k hβ hN hb hz' hy'
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Measurable fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x :=
  (continuous_tanIntegral ν n h k hβ hN hb).measurable

/-! ### The integrated ordered remainder -/

/-- The integrated ordered remainder minus the integrated coefficient is the integral of the
pointwise difference (`N ≥ 0`). -/
theorem tanRemainder_sub_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) {N : ℝ}
    (hN : 0 ≤ N) :
    tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j =
      ∫ v, (orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j) ∂ν := by
  have hC := integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j
  have hZ := integrable_dataBoxIntegral_tan ν n h k hβ.le hN hb x
  have hP : Integrable (fun v => predSum n h k β b (x v) μ j N) ν := by
    unfold predSum expTerm
    exact integrable_finset_sum _ fun p _ =>
      (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _
  have hR : Integrable (fun v => orderedRemainder n h k β b (x v) μ j N) ν := by
    unfold orderedRemainder
    exact (hZ.sub hP).div_const _
  rw [integral_sub hR hC]
  congr 1
  unfold tanRemainder orderedRemainder tanIntegral tanPredSum tanCoeff
  rw [integral_div, integral_sub hZ hP]
  congr 2
  unfold predSum expTerm
  rw [integral_finset_sum _ fun p _ =>
    (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_mul_const]

/-- **The integrated majorant estimate** (`lemma:AsymInt` in ordered-remainder form): on the
sup-norm ball of radius `R`, for `N ≥ e` and `N b^{2|k|} ≥ 1`,
`|ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x)| ≤ ν(K) · remainderMajorant n h k β b μ j R N`. -/
theorem abs_tanRemainder_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k) {j : ℕ}
    (hj : j ≤ n) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) {N : ℝ}
    (hNe : Real.exp 1 ≤ N) (hNb : 1 ≤ boxScale k b N) :
    |tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j| ≤
      (ν univ).toReal * remainderMajorant n h k β b μ j R N := by
  have hN0 : 0 ≤ N := le_trans (Real.exp_pos 1).le hNe
  rw [tanRemainder_sub_tanCoeff ν n h k hk β hβ hb x μ j hN0]
  have hbound : ∀ v, ‖orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j‖ ≤
      remainderMajorant n h k β b μ j R N := by
    intro v
    rw [Real.norm_eq_abs]
    exact abs_orderedRemainder_sub_le n h k hk β hβ hb hμ hj ((norm_tan_apply_le x v).trans hx)
      hNe hNb
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- **Integrated ordered remainders converge uniformly on sup-norm balls.** -/
theorem tendstoUniformlyOn_tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => tanRemainder ν n h k β b x μ j N)
      (fun x => tanCoeff ν n h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_remainderMajorant n h k β b μ j R).const_mul (ν univ).toReal
  rw [mul_zero] at hmaj
  have hev : ∀ᶠ N in atTop, (ν univ).toReal * remainderMajorant n h k β b μ j R N < ε :=
    hmaj.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 / c)] with N hNε hNe
    hNc x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_tanRemainder_sub_le ν n h k hk β hβ hb hμ hj hx' hNe hscale) hNε

end Grammar

```
### Grammar/StochasticTangential.lean

Ambient `variable` declarations:
```lean
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
variable [l.IsCountablyGenerated]
```

```lean
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

```


## Full proof of the integrated remainder identity (unit 279)

```lean
/-- The integrated ordered remainder minus the integrated coefficient is the integral of the
pointwise difference (`N ≥ 0`). -/
theorem tanRemainder_sub_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) {N : ℝ}
    (hN : 0 ≤ N) :
    tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j =
      ∫ v, (orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j) ∂ν := by
  have hC := integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j
  have hZ := integrable_dataBoxIntegral_tan ν n h k hβ.le hN hb x
  have hP : Integrable (fun v => predSum n h k β b (x v) μ j N) ν := by
    unfold predSum expTerm
    exact integrable_finset_sum _ fun p _ =>
      (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _
  have hR : Integrable (fun v => orderedRemainder n h k β b (x v) μ j N) ν := by
    unfold orderedRemainder
    exact (hZ.sub hP).div_const _
  rw [integral_sub hR hC]
  congr 1
  unfold tanRemainder orderedRemainder tanIntegral tanPredSum tanCoeff
  rw [integral_div, integral_sub hZ hP]
  congr 2
  unfold predSum expTerm
  rw [integral_finset_sum _ fun p _ =>
    (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_mul_const]

/-- **The integrated majorant estimate** (`lemma:AsymInt` in ordered-remainder form): on the
sup-norm ball of radius `R`, for `N ≥ e` and `N b^{2|k|} ≥ 1`,
`|ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x)| ≤ ν(K) · remainderMajorant n h k β b μ j R N`. -/
theorem abs_tanRemainder_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k) {j : ℕ}
    (hj : j ≤ n) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) {N : ℝ}
    (hNe : Real.exp 1 ≤ N) (hNb : 1 ≤ boxScale k b N) :
    |tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j| ≤
      (ν univ).toReal * remainderMajorant n h k β b μ j R N := by
  have hN0 : 0 ≤ N := le_trans (Real.exp_pos 1).le hNe
  rw [tanRemainder_sub_tanCoeff ν n h k hk β hβ hb x μ j hN0]
  have hbound : ∀ v, ‖orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j‖ ≤
      remainderMajorant n h k β b μ j R N := by
    intro v
    rw [Real.norm_eq_abs]
    exact abs_orderedRemainder_sub_le n h k hk β hβ hb hμ hj ((norm_tan_apply_le x v).trans hx)
      hNe hNb
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring


```

## Questions
1. **u278 (data type and integrated cutoff).** Is `TangentialData K d = C(K, DataSpace d)` (compact Hausdorff `K`, sup norm, Borel σ-algebra `borel`) an honest model of the tangential Taylor data `v ↦ (c_ξ(·,v), c_η(·,v))` on a stratum, with the weight `ρ_I` absorbed into the amplitude? Is the integrated cutoff theorem `tanTaylorTree_cutoff_bound` a correct finite-cutoff `lemma:AsymInt` (integrating the pointwise estimate under the uniform bound `‖x v‖ ≤ ‖x‖ ≤ R`, `ν(K) = (ν univ).toReal`)? Are the hypotheses on `K` (`CompactSpace`, `T2Space`, `MeasurableSpace`, `OpensMeasurableSpace`) and `ν` (`IsFiniteMeasure`) the right minimal set?
2. **u279 (integrated remainder).** Check the Lipschitz constants `ν(K)·dataLipConst` and `ν(K)·(u274 constant)`, the identity `ℛ − 𝒞 = ∫ (R − C)` (integrability of each piece; division by the fixed scalar `N^{-μ}(log N)^j` passes through the integral by `integral_div`), the majorant `|ℛ − 𝒞| ≤ ν(K)·remainderMajorant` and the `TendstoUniformlyOn` on sup-norm balls. Note the integrated predecessor sum uses the same `predSet` (per-chart lattice) — correct for one stratum?
3. **u280 (Headline XXXVI).** Is `tendstoInDistribution_tanRemainder` a faithful one-stratum rendering of the paper's stochastic statement including the tangential integration, conditional on `X_ℓ ⇒ X` in `C(K, E_b × E_b)`? Is the route (continuous mapping on `C(K, E)`; norm-boundedness in probability from portmanteau on `{‖·‖ ≥ m}` closed in `C(K,E)`; uniform-on-balls ⇒ in probability; Slutsky) sound in this non-locally-compact Banach space? What non-claims must accompany XXXVI (function-space regularity of the data as hypothesis; compact `K` and finite `ν`; the weight convention; no assembly; no Gaussianity)?
4. **Before assembly (units 281+).** Astra #34's design: dependent product over a finite chart index `∀ I, C(K_I, DataSpace (d_I))`, common lattice `Q⁻¹ℕ` with zero padding for charts whose lattice misses `μ` or whose log degree is exceeded, sum of the integrated cutoff theorems at one cutoff `L > μ`, global coefficient `∑_I 𝒞^I_{μ,j}`, external decomposition `Z^{global}_ℓ = ∑_I 𝒵^I_{N_ℓ}(X_{ℓ,I}) + E_ℓ` with residual `E_ℓ/(N_ℓ^{-μ}(log N_ℓ)^j) → 0` in probability as hypothesis, joint convergence of the chart data as hypothesis. Any statement-level trap (e.g. different `β`? — no, common; different `b_I` — yes; the ordering across charts; the zero-coefficient padding vs the paper's `Λ^*`; whether `tanRemainder` of each chart at a GLOBAL target is meaningful when the target is not on that chart's lattice)?
5. Verdict per unit, overall verdict, should-fix list (blocking vs nonblocking) before continuing to assembly.
