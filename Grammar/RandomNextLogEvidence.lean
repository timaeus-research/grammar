/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.UniformSpatialTwoTerm
import Grammar.UniformNextLogQuotient
import Grammar.GraphLawTransfer

/-!
# Random next-log evidence, jointly with its data

Uniform convergence on compact sets to a continuous limit gives continuous convergence on a metric
space (`continuouslyConverges_of_tendstoUniformlyOn_compacts`: only the compact
`{p} ∪ {x_j}` of a convergent sequence is needed).  Hence the next-log statistic
`T_N(x) = log N (Z_N(x)/(N^{−λ} log^{m−1} N) − F(x))` converges continuously on the data space to
`B(x) = C_{λ,m−2}(x)` (`continuouslyConverges_nextLogStat`), and for random data `X_m ⇒ X` (laws
`μ_m ⇒ μ₀` on the data space, uniformly tight) the **random next-log evidence converges jointly
with its data**: `(X_m, T_{N_m}(X_m)) ⇒ (X, B(X))` (`randomNextLog_graphLaw_tendsto`), with the
marginal `T_{N_m}(X_m) ⇒ B(X)`.  For `m = 1` the second coordinate converges to `0`
(`randomNextLog_graphLaw_tendsto_one`).

No positivity floor, no common probability space, no coupling and no phase-field CLT are needed.
Tightness of the data laws is an explicit hypothesis because Mathlib has no separability instance
for `ℓ¹` over a countable index; under `SecondCountableTopology (DataSpace (n+1))` it is automatic
(`randomNextLog_graphLaw_tendsto_of_secondCountable`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-! ### Uniform convergence on compacts gives continuous convergence -/

/-- **Compact-uniform to continuous convergence** on a pseudo-metric domain: if `Tn → B` uniformly
on every compact set and `B` is continuous, then `Tn → B` continuously. -/
theorem continuouslyConverges_of_tendstoUniformlyOn_compacts {P V : Type*} [PseudoMetricSpace P]
    [PseudoMetricSpace V] {Tn : ℕ → P → V} {B : P → V} (hB : Continuous B)
    (hT : ∀ K : Set P, IsCompact K → TendstoUniformlyOn Tn B atTop K) :
    ContinuouslyConverges Tn B := by
  refine continuouslyConverges_of_seq fun p κ x hκ hx => ?_
  have hK : IsCompact (insert p (Set.range x)) := hx.isCompact_insert_range
  have hu := Metric.tendstoUniformlyOn_iff.1 (hT _ hK)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := hκ.eventually (hu (ε / 2) (half_pos hε))
  have h2 := (Metric.tendsto_nhds.1 ((hB.tendsto p).comp hx)) (ε / 2) (half_pos hε)
  filter_upwards [h1, h2] with j hj1 hj2
  calc dist (Tn (κ j) (x j)) (B p)
      ≤ dist (Tn (κ j) (x j)) (B (x j)) + dist (B (x j)) (B p) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by
        rw [dist_comm]
        exact hj1 (x j) (mem_insert_of_mem _ (mem_range_self j))) hj2
    _ = ε := add_halves ε

/-- Uniform convergence along `N → ∞` restricts to any sequence `N_m → ∞`. -/
theorem tendstoUniformlyOn_comp_seq {P : Type*} {F : ℝ → P → ℝ} {f : P → ℝ} {K : Set P}
    (hF : TendstoUniformlyOn F f atTop K) {Nseq : ℕ → ℝ} (hN : Tendsto Nseq atTop atTop) :
    TendstoUniformlyOn (fun m => F (Nseq m)) f atTop K :=
  fun u hu => hN.eventually (hF u hu)

/-! ### The next-log statistic on the data space -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)

/-- The next-log evidence statistic `T_N(x) = log N (Z_N(x)/(N^{−λ} log^{m−1} N) − F(x))`. -/
noncomputable def nextLogStat (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  Real.log N * (dataBoxIntegral n h k β N 1 x /
    (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
    dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1))

/-- The `m = 1` statistic `log N (N^λ Z_N(x) − F(x))`. -/
noncomputable def nextLogStatOne (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  Real.log N * (dataBoxIntegral n h k β N 1 x / N ^ (-l) - dataBoxCoeff n h k β 1 x l 0)

include hk hβ in
theorem continuous_nextLogStat {N : ℝ} (hN : 0 ≤ N) :
    Continuous (nextLogStat n h k (β := β) l N) := by
  unfold nextLogStat
  exact continuous_const.mul (((continuous_dataBoxIntegral n h k hβ.le hN one_pos).div_const _).sub
    (continuous_dataBoxCoeff_one n h k hk hβ l _))

include hk hβ in
theorem continuous_nextLogStatOne {N : ℝ} (hN : 0 ≤ N) :
    Continuous (nextLogStatOne n h k (β := β) l N) := by
  unfold nextLogStatOne
  exact continuous_const.mul (((continuous_dataBoxIntegral n h k hβ.le hN one_pos).div_const _).sub
    (continuous_dataBoxCoeff_one n h k hk hβ l _))

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hN in
/-- **Continuous convergence of the next-log statistic** on the data space (`m ≥ 2`). -/
theorem continuouslyConverges_nextLogStat (hm : 2 ≤ multCount (ratioExp h k) l) :
    ContinuouslyConverges (fun m => nextLogStat n h k (β := β) l (Nseq m))
      fun x => dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 2) :=
  continuouslyConverges_of_tendstoUniformlyOn_compacts (continuous_dataBoxCoeff_one n h k hk hβ l _)
    fun _ hK => tendstoUniformlyOn_comp_seq
      (tendstoUniformlyOn_spatialTwoTerm_compact n h k hk hβ hmin hatt hm hK) hN

include hk hβ hmin hatt hN in
/-- Continuous convergence of the `m = 1` statistic to `0`. -/
theorem continuouslyConverges_nextLogStatOne (hm : multCount (ratioExp h k) l = 1) :
    ContinuouslyConverges (fun m => nextLogStatOne n h k (β := β) l (Nseq m))
      fun _ : DataSpace (n + 1) => (0 : ℝ) :=
  continuouslyConverges_of_tendstoUniformlyOn_compacts continuous_const fun K hK => by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact tendstoUniformlyOn_comp_seq
      ((tendstoUniformlyOn_spatialTwoTerm_one n h k hk hβ hmin hatt hm R).mono hR) hN

variable {μ : ℕ → ProbabilityMeasure (DataSpace (n + 1))}
  {μ₀ : ProbabilityMeasure (DataSpace (n + 1))} (hμ : Tendsto μ atTop (𝓝 μ₀))

include hk hβ hmin hatt hN1 hN hμ in
/-- **Random next-log evidence, jointly with its data** (`m ≥ 2`): for random data `X_m ⇒ X`
(uniformly tight laws) and `N_m → ∞`,
`(X_m, log N_m (Z_{N_m}(X_m)/(N_m^{−λ} log^{m−1} N_m) − F(X_m))) ⇒ (X, B(X))`. -/
theorem randomNextLog_graphLaw_tendsto (hm : 2 ≤ multCount (ratioExp h k) l)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ C : Set (DataSpace (n + 1)), IsCompact C ∧
      ∀ m, ((μ m : Measure (DataSpace (n + 1))) Cᶜ).toReal ≤ δ) :
    Tendsto (fun m => graphLaw (μ m)
        (continuous_nextLogStat n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable) atTop
      (𝓝 (graphLaw μ₀ (continuous_dataBoxCoeff_one n h k hk hβ l
        (multCount (ratioExp h k) l - 2)).measurable)) :=
  tendsto_graphLaw_of_continuouslyConverges hμ htight
    (fun m => (continuous_nextLogStat n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable)
    (continuouslyConverges_nextLogStat n h k hk hβ l hmin hatt Nseq hN hm)

include hk hβ hmin hatt hN1 hN hμ in
/-- The Polish form: with `ℓ¹` second countable, tightness of `μ_m ⇒ μ₀` is automatic. -/
theorem randomNextLog_graphLaw_tendsto_of_secondCountable
    [SecondCountableTopology (DataSpace (n + 1))] (hm : 2 ≤ multCount (ratioExp h k) l) :
    Tendsto (fun m => graphLaw (μ m)
        (continuous_nextLogStat n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable) atTop
      (𝓝 (graphLaw μ₀ (continuous_dataBoxCoeff_one n h k hk hβ l
        (multCount (ratioExp h k) l - 2)).measurable)) :=
  tendsto_graphLaw_of_polish hμ
    (fun m => (continuous_nextLogStat n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable)
    (continuouslyConverges_nextLogStat n h k hk hβ l hmin hatt Nseq hN hm)

include hk hβ hmin hatt hN1 hN hμ in
/-- The marginal: the random next-log evidence converges in law, `T_{N_m}(X_m) ⇒ B(X)`. -/
theorem randomNextLog_tendsto (hm : 2 ≤ multCount (ratioExp h k) l)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ C : Set (DataSpace (n + 1)), IsCompact C ∧
      ∀ m, ((μ m : Measure (DataSpace (n + 1))) Cᶜ).toReal ≤ δ) :
    Tendsto (fun m => (μ m).map (continuous_nextLogStat n h k hk hβ l
        (zero_le_one.trans (hN1 m).le)).measurable.aemeasurable) atTop
      (𝓝 (μ₀.map (continuous_dataBoxCoeff_one n h k hk hβ l
        (multCount (ratioExp h k) l - 2)).measurable.aemeasurable)) := by
  have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (randomNextLog_graphLaw_tendsto n h k hk hβ l hmin hatt Nseq hN1 hN hμ hm htight)
    (continuous_snd (X := DataSpace (n + 1)) (Y := ℝ))
  have hmap : ∀ (ν : ProbabilityMeasure (DataSpace (n + 1))) {S : DataSpace (n + 1) → ℝ}
      (hS : Measurable S), (graphLaw ν hS).map (continuous_snd.measurable.aemeasurable) =
        ν.map hS.aemeasurable := fun ν S hS => by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, graphLaw]
    rw [Measure.map_map measurable_snd (measurable_id.prodMk hS)]
    rfl
  simpa only [hmap] using this

include hk hβ hmin hatt hN1 hN hμ in
/-- The `m = 1` case: the log-amplified evidence remainder converges to `0` jointly with the data,
`(X_m, log N_m (N_m^λ Z_{N_m}(X_m) − F(X_m))) ⇒ (X, 0)`. -/
theorem randomNextLog_graphLaw_tendsto_one (hm : multCount (ratioExp h k) l = 1)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ C : Set (DataSpace (n + 1)), IsCompact C ∧
      ∀ m, ((μ m : Measure (DataSpace (n + 1))) Cᶜ).toReal ≤ δ) :
    Tendsto (fun m => graphLaw (μ m)
        (continuous_nextLogStatOne n h k hk hβ l (zero_le_one.trans (hN1 m).le)).measurable) atTop
      (𝓝 (graphLaw μ₀ (measurable_const (a := (0 : ℝ))))) :=
  tendsto_graphLaw_of_continuouslyConverges hμ htight
    (fun m => (continuous_nextLogStatOne n h k hk hβ l
      (zero_le_one.trans (hN1 m).le)).measurable)
    (continuouslyConverges_nextLogStatOne n h k hk hβ l hmin hatt Nseq hN hm)

end Grammar
