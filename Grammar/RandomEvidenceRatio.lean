/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomNextLogFreeEnergy

/-!
# Evidence ratios under a joint random data law

On the product domain `D × D₊` (numerator datum first, admissible denominator datum second) the
evidence ratio `R_N(x', x) = Z_N(x')/Z_N(x)` has the uniform next-log expansion
`log N (R_N − F(x')/F(x)) → (B(x')F(x) − F(x')B(x))/F(x)²` on compact sets
(`tendstoUniformlyOn_evidenceRatio`: the uniform two-term theorem for each factor through the
projections, the quotient theorem, the positive minimum of `F(x)` on the compact), hence continuous
convergence (`continuouslyConverges_evidenceRatio`) and, for a **jointly** convergent random pair
`Y_m = (X'_m, X_m) ⇒ Y` on the Polish product domain, the random evidence ratio jointly with its
data (`randomEvidenceRatio_graphLaw_tendsto`).  The fixed-numerator case `x' = x⋆` is the corollary
`randomEvidenceRatio_fixed_graphLaw_tendsto` (push the denominator law forward by `x ↦ (x⋆, x)`).

Traps recorded: marginal convergence of the two data is insufficient (joint convergence is the
hypothesis); numerator and denominator share `λ` and `m`; signed numerator data give an algebraic
ratio theorem, not a physical evidence comparison.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)

/-- The product domain: an arbitrary numerator datum and an admissible denominator datum. -/
abbrev RatioDomain : Type := DataSpace (n + 1) × AdmissibleData n h k (β := β) l

/-- The evidence ratio `Z_N(x')/Z_N(x)` (as a quotient of normalised evidences). -/
noncomputable def evidenceRatio (N : ℝ) (y : RatioDomain n h k (β := β) l) : ℝ :=
  energyDen n h k (β := β) l N y.1 / energyDen n h k (β := β) l N y.2.1

/-- The leading ratio `F(x')/F(x)`. -/
noncomputable def ratioLead (y : RatioDomain n h k (β := β) l) : ℝ :=
  dataLead n h k (β := β) l y.1 / dataLead n h k (β := β) l y.2.1

/-- The next-log ratio correction `(B(x')F(x) − F(x')B(x))/F(x)²`. -/
noncomputable def ratioCorrection (y : RatioDomain n h k (β := β) l) : ℝ :=
  (dataSecond n h k (β := β) l y.1 * dataLead n h k (β := β) l y.2.1 -
    dataLead n h k (β := β) l y.1 * dataSecond n h k (β := β) l y.2.1) /
      dataLead n h k (β := β) l y.2.1 ^ 2

/-- The evidence ratio is the ratio of the chart integrals. -/
theorem evidenceRatio_eq {N : ℝ} (hN : 1 < N) (y : RatioDomain n h k (β := β) l) :
    evidenceRatio n h k (β := β) l N y =
      dataBoxIntegral n h k β N 1 y.1 / dataBoxIntegral n h k β N 1 y.2.1 := by
  unfold evidenceRatio energyDen
  have hden : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  rw [div_div_div_cancel_right₀ hden]

/-- The centred, log-amplified ratio statistic. -/
noncomputable def ratioStat (N : ℝ) (y : RatioDomain n h k (β := β) l) : ℝ :=
  Real.log N * (evidenceRatio n h k (β := β) l N y - ratioLead n h k (β := β) l y)

include hβ in
theorem measurable_ratioStat (hk : ∀ i, 0 < k i) {N : ℝ} (hN : 0 ≤ N) :
    Measurable (ratioStat n h k (β := β) l N) := by
  unfold ratioStat evidenceRatio ratioLead energyDen
  have hZ : Measurable fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N 1 x /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) :=
    (measurable_dataBoxIntegral n h k hβ.le hN one_pos).div_const _
  have hF := (continuous_dataLead n h k hk hβ l).measurable
  exact measurable_const.mul (((hZ.comp measurable_fst).div
    (hZ.comp (measurable_subtype_coe.comp measurable_snd))).sub
    ((hF.comp measurable_fst).div (hF.comp (measurable_subtype_coe.comp measurable_snd))))

include hk hβ in
theorem continuous_ratioCorrection : Continuous (ratioCorrection n h k (β := β) l) := by
  unfold ratioCorrection
  have hF2 : Continuous fun y : RatioDomain n h k (β := β) l => dataLead n h k (β := β) l y.2.1 :=
    (continuous_dataLead n h k hk hβ l).comp (continuous_subtype_val.comp continuous_snd)
  refine Continuous.div ?_ (hF2.pow 2) fun y => pow_ne_zero _ y.2.2.ne'
  exact (((continuous_dataSecond n h k hk hβ l).comp continuous_fst).mul hF2).sub
    (((continuous_dataLead n h k hk hβ l).comp continuous_fst).mul
      ((continuous_dataSecond n h k hk hβ l).comp (continuous_subtype_val.comp continuous_snd)))

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l)

include hk hβ hmin hatt hm in
/-- **Uniform next-log expansion of the evidence ratio** on compact subsets of the product
domain. -/
theorem tendstoUniformlyOn_evidenceRatio {K : Set (RatioDomain n h k (β := β) l)}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun N y => ratioStat n h k (β := β) l N y)
      (ratioCorrection n h k (β := β) l) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    simp [TendstoUniformlyOn]
  -- the two projections
  have hK1 : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hK2 : IsCompact ((fun y : RatioDomain n h k (β := β) l => y.2.1) '' K) :=
    hK.image (continuous_subtype_val.comp continuous_snd)
  obtain ⟨R1, hR1⟩ := hK1.isBounded.subset_closedBall 0
  obtain ⟨R2, hR2⟩ := hK2.isBounded.subset_closedBall 0
  have hA : TendstoUniformlyOn (fun N (y : RatioDomain n h k (β := β) l) =>
      Real.log N * (energyDen n h k (β := β) l N y.1 - dataLead n h k (β := β) l y.1))
      (fun y => dataSecond n h k (β := β) l y.1) atTop K :=
    ((tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm R1).comp Prod.fst).mono
      fun y hy => hR1 (mem_image_of_mem _ hy)
  have hZ : TendstoUniformlyOn (fun N (y : RatioDomain n h k (β := β) l) =>
      Real.log N * (energyDen n h k (β := β) l N y.2.1 - dataLead n h k (β := β) l y.2.1))
      (fun y => dataSecond n h k (β := β) l y.2.1) atTop K :=
    ((tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm R2).comp
      (fun y : RatioDomain n h k (β := β) l => y.2.1)).mono fun y hy => hR2 (mem_image_of_mem _ hy)
  -- bounds and floor
  have hc1 : Continuous fun y : RatioDomain n h k (β := β) l => dataLead n h k (β := β) l y.1 :=
    (continuous_dataLead n h k hk hβ l).comp continuous_fst
  have hc2 : Continuous fun y : RatioDomain n h k (β := β) l => dataLead n h k (β := β) l y.2.1 :=
    (continuous_dataLead n h k hk hβ l).comp (continuous_subtype_val.comp continuous_snd)
  have hc3 : Continuous fun y : RatioDomain n h k (β := β) l => dataSecond n h k (β := β) l y.1 :=
    (continuous_dataSecond n h k hk hβ l).comp continuous_fst
  have hc4 : Continuous fun y : RatioDomain n h k (β := β) l => dataSecond n h k (β := β) l y.2.1 :=
    (continuous_dataSecond n h k hk hβ l).comp (continuous_subtype_val.comp continuous_snd)
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn hc3.continuousOn
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn hc4.continuousOn
  obtain ⟨y₀, hy₀, hmin₀⟩ := hK.exists_isMinOn hKne hc2.continuousOn
  exact tendstoUniformlyOn_nextLog_div (S := K) hA hZ (MA := max M1 M2) (MB := max M3 M4)
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le ((hM1 y hy).trans (le_max_left _ _)))
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le ((hM2 y hy).trans (le_max_right _ _)))
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le ((hM3 y hy).trans (le_max_left _ _)))
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le ((hM4 y hy).trans (le_max_right _ _)))
    y₀.2.2 fun y hy => hmin₀ hy

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hm hN in
theorem continuouslyConverges_evidenceRatio :
    ContinuouslyConverges (fun m => ratioStat n h k (β := β) l (Nseq m))
      (ratioCorrection n h k (β := β) l) :=
  continuouslyConverges_of_tendstoUniformlyOn_compacts (continuous_ratioCorrection n h k hk hβ l)
    fun _ hK => tendstoUniformlyOn_comp_seq
      (tendstoUniformlyOn_evidenceRatio n h k hk hβ l hmin hatt hm hK) hN

include hk hβ hmin hatt hm hN1 hN in
/-- **Random evidence ratio, jointly with its data**: for a jointly convergent random pair
`Y_m = (X'_m, X_m) ⇒ Y` on the product domain and `N_m → ∞`,
`(Y_m, log N_m (Z_{N_m}(X'_m)/Z_{N_m}(X_m) − F(X'_m)/F(X_m))) ⇒ (Y, R₁(Y))`. -/
theorem randomEvidenceRatio_graphLaw_tendsto
    {μ : ℕ → ProbabilityMeasure (RatioDomain n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (RatioDomain n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_ratioStat n h k hβ l hk (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_ratioCorrection n h k hk hβ l).measurable)) :=
  haveI := polishSpace_admissibleData n h k hk hβ l
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto_polish hμ)
    (fun m => measurable_ratioStat n h k hβ l hk (zero_le_one.trans (hN1 m).le))
    (continuouslyConverges_evidenceRatio n h k hk hβ l hmin hatt hm Nseq hN)

include hk hβ hmin hatt hm hN1 hN in
/-- The fixed-numerator corollary: for a deterministic `x⋆` and random admissible `X_m ⇒ X`, the
random evidence ratio `Z_{N_m}(x⋆)/Z_{N_m}(X_m)` converges jointly with `X_m` (the pair law is the
push-forward of the denominator law by `x ↦ (x⋆, x)`). -/
theorem randomEvidenceRatio_fixed_graphLaw_tendsto (xs : DataSpace (n + 1))
    {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw ((μ m).map (measurable_const.prodMk measurable_id).aemeasurable
        (f := fun x : AdmissibleData n h k (β := β) l => (xs, x)))
        (measurable_ratioStat n h k hβ l hk (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw (μ₀.map (measurable_const.prodMk measurable_id).aemeasurable
        (f := fun x : AdmissibleData n h k (β := β) l => (xs, x)))
        (continuous_ratioCorrection n h k hk hβ l).measurable)) :=
  randomEvidenceRatio_graphLaw_tendsto n h k hk hβ l hmin hatt hm Nseq hN1 hN
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
      (continuous_const.prodMk continuous_id))

end Grammar
