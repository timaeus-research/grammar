/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomNextLogPosterior

/-!
# The data space is Polish

`ℓ¹(ι, ℝ)` over a countable index is second countable (`secondCountableTopology_lp_one`: finitely
supported rational sequences are dense — `lp.hasSum_single` truncates, `exists_rat_near`
approximates), so the weighted-ℓ¹ data space is a Polish space, and tightness of a weakly convergent
sequence of data laws is automatic (`tight_of_tendsto_polish`, also on the open admissible domain
`{F > 0}`).  The random next-log theorems of XCVI–XCVII therefore hold without the tightness
hypothesis (`randomNextLog_graphLaw_tendsto'`, `randomEnergyMean_graphLaw_tendsto'`).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- **`ℓ¹` over a countable index is second countable**: finitely supported rational sequences are
dense. -/
theorem secondCountableTopology_lp_one {ι : Type*} [Countable ι] :
    SecondCountableTopology (lp (fun _ : ι => ℝ) 1) := by
  classical
  refine Metric.secondCountable_of_almost_dense_set fun ε hε => ?_
  refine ⟨Set.range (fun p : Σ F : Finset ι, (↥F → ℚ) =>
    ∑ i ∈ p.1.attach, lp.single 1 (i : ι) ((p.2 i : ℚ) : ℝ)), Set.countable_range _, fun f => ?_⟩
  have hsum := lp.hasSum_single (E := fun _ : ι => ℝ) (p := 1) ENNReal.one_ne_top f
  obtain ⟨F, hF⟩ := (Metric.tendsto_nhds.1 hsum (ε / 2) (half_pos hε)).exists
  have hε' : 0 < ε / (2 * ((F.card : ℝ) + 1)) := by positivity
  have hq : ∀ i : ↥F, ∃ q : ℚ, |f (i : ι) - q| < ε / (2 * ((F.card : ℝ) + 1)) := fun i =>
    exists_rat_near _ hε'
  choose q hq using hq
  refine ⟨∑ i ∈ F.attach, lp.single 1 (i : ι) ((q i : ℚ) : ℝ), ⟨⟨F, q⟩, rfl⟩, ?_⟩
  have h2 : dist (∑ i ∈ F, lp.single 1 i (f i))
      (∑ i ∈ F.attach, lp.single 1 (i : ι) ((q i : ℚ) : ℝ)) ≤ ε / 2 := by
    rw [dist_eq_norm, ← Finset.sum_attach F (fun i => lp.single 1 i (f i)),
      ← Finset.sum_sub_distrib]
    simp_rw [← lp.single_sub]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [lp.norm_single zero_lt_one, Real.norm_eq_abs]
    calc ∑ i ∈ F.attach, |f (i : ι) - (q i : ℝ)|
        ≤ ∑ _i ∈ F.attach, ε / (2 * ((F.card : ℝ) + 1)) :=
          Finset.sum_le_sum fun i _ => (hq i).le
      _ = (F.card : ℝ) * (ε / (2 * ((F.card : ℝ) + 1))) := by
          rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
      _ ≤ ((F.card : ℝ) + 1) * (ε / (2 * ((F.card : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) hε'.le
      _ = ε / 2 := by field_simp
  calc dist f (∑ i ∈ F.attach, lp.single 1 (i : ι) ((q i : ℚ) : ℝ))
      ≤ dist f (∑ i ∈ F, lp.single 1 i (f i)) +
        dist (∑ i ∈ F, lp.single 1 i (f i)) (∑ i ∈ F.attach, lp.single 1 (i : ι) ((q i : ℚ) : ℝ)) :=
        dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (by rw [dist_comm]; exact hF.le) h2
    _ = ε := add_halves ε

instance instSecondCountableDataSpace (d : ℕ) : SecondCountableTopology (DataSpace d) :=
  secondCountableTopology_lp_one

/-- Tightness of a weakly convergent sequence of laws on a Polish space (any compatible metric). -/
theorem tight_of_tendsto_polish {P : Type*} [TopologicalSpace P] [PolishSpace P]
    [MeasurableSpace P] [BorelSpace P] {μ : ℕ → ProbabilityMeasure P} {μ₀ : ProbabilityMeasure P}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    ∀ δ : ℝ, 0 < δ → ∃ C : Set P, IsCompact C ∧ ∀ n, ((μ n : Measure P) Cᶜ).toReal ≤ δ := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable P
  exact tight_of_tendsto hμ

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)
  (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hN1 hN in
/-- **Random next-log evidence, jointly with its data**, on the Polish data space: no tightness
hypothesis. -/
theorem randomNextLog_graphLaw_tendsto' (hm : 2 ≤ multCount (ratioExp h k) l)
    {μ : ℕ → ProbabilityMeasure (DataSpace (n + 1))} {μ₀ : ProbabilityMeasure (DataSpace (n + 1))}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (continuous_nextLogStat n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable) atTop
      (𝓝 (graphLaw μ₀ (continuous_dataBoxCoeff_one n h k hk hβ l
        (multCount (ratioExp h k) l - 2)).measurable)) :=
  randomNextLog_graphLaw_tendsto n h k hk hβ l hmin hatt Nseq hN1 hN hμ hm
    (tight_of_tendsto_polish hμ)

include hk hβ in
/-- The admissible domain `{F > 0}` is an open subset of a Polish space, hence Polish. -/
theorem polishSpace_admissibleData : PolishSpace (AdmissibleData n h k (β := β) l) :=
  (isOpen_lt continuous_const (continuous_dataLead n h k hk hβ l)).polishSpace

include hk hβ hmin hatt hN1 hN in
/-- **Random next-log posterior energy correction** on the Polish admissible domain: no tightness
hypothesis. -/
theorem randomEnergyMean_graphLaw_tendsto' (hm : 2 ≤ multCount (ratioExp h k) l)
    {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_energyCorrectionU n h k hk hβ l).measurable)) :=
  haveI := polishSpace_admissibleData n h k hk hβ l
  randomEnergyMean_graphLaw_tendsto n h k hk hβ l hmin hatt hm Nseq hN1 hN hμ
    (tight_of_tendsto_polish hμ)

end Grammar
