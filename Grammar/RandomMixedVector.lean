/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomEvidenceRatio

/-!
# One finite-vector random-observable theorem

Continuous convergence is coordinatewise (`continuouslyConverges_pi`) and stable under
precomposition with a continuous map (`ContinuouslyConverges.comp_continuous`), so the deterministic
next-log maps of the evidence, the posterior energy mean, the free energy and any finite list of
posterior Laplace transforms assemble into one vector-valued map on the admissible domain
(`mixedStat`), which converges continuously to the vector of corrections (`mixedCorrection`).
One application of the graph-law transfer then gives the **joint random next-log
posterior-observable theorem**: for random admissible data `X_m ⇒ X` and `N_m → ∞`,
`(X_m, mixedStat_{N_m}(X_m)) ⇒ (X, mixedCorrection(X))` (`randomMixed_graphLaw_tendsto`) — all
coordinates jointly, under one weak-convergence hypothesis.

Assembling already-proved marginal limits would not give joint convergence; the deterministic maps
are assembled first and the transfer applied once.  No independence of coordinates and no process
convergence in the Laplace parameter is claimed.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-! ### Vector-valued continuous convergence -/

/-- Coordinatewise continuous convergence gives continuous convergence of the vector. -/
theorem continuouslyConverges_pi {P : Type*} [TopologicalSpace P] {ι : Type*} {V : ι → Type*}
    [∀ i, TopologicalSpace (V i)] {Tn : ℕ → P → ∀ i, V i} {T : P → ∀ i, V i}
    (h : ∀ i, ContinuouslyConverges (fun n x => Tn n x i) fun x => T x i) :
    ContinuouslyConverges Tn T :=
  fun p => tendsto_pi_nhds.2 fun i => h i p

/-- Continuous convergence is stable under precomposition with a continuous map. -/
theorem ContinuouslyConverges.comp_continuous {P Q V : Type*} [TopologicalSpace P]
    [TopologicalSpace Q] [TopologicalSpace V] {Tn : ℕ → P → V} {T : P → V}
    (hcc : ContinuouslyConverges Tn T) {g : Q → P} (hg : Continuous g) :
    ContinuouslyConverges (fun n q => Tn n (g q)) fun q => T (g q) := fun q =>
  (hcc (g q)).comp (tendsto_fst.prodMk ((hg.tendsto q).comp tendsto_snd))

/-! ### The mixed vector on the admissible domain -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)
  {r : ℕ} (sv : Fin r → ℝ)

/-- The mixed statistic: evidence remainder, energy-mean correction, free-energy correction, and
the Laplace corrections at the parameters `sv i`. -/
noncomputable def mixedStat (N : ℝ) (x : AdmissibleData n h k (β := β) l) : Fin 3 ⊕ Fin r → ℝ :=
  Sum.elim ![nextLogStat n h k (β := β) l N x.1, energyStatU n h k (β := β) l N x,
    freeEnergyStatU n h k (β := β) l N x] fun i => laplaceStatU n h k (β := β) l (sv i) N x

/-- The vector of limiting corrections. -/
noncomputable def mixedCorrection (x : AdmissibleData n h k (β := β) l) : Fin 3 ⊕ Fin r → ℝ :=
  Sum.elim ![dataSecond n h k (β := β) l x.1, energyCorrection n h k (β := β) l x.1,
    -(dataSecond n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1)]
    fun i => laplaceCorrection n h k (β := β) l (sv i) x.1

include hk hβ in
theorem measurable_mixedStat (hsv : ∀ i, 0 ≤ sv i) {N : ℝ} (hN : 0 ≤ N) :
    Measurable (mixedStat n h k (β := β) l sv N) := by
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact (continuous_nextLogStat n h k hk hβ l hN).measurable.comp measurable_subtype_coe
    · exact measurable_energyStatU n h k hk hβ l hN
    · exact measurable_freeEnergyStatU n h k hk hβ l hN
  · exact measurable_laplaceStatU n h k hk hβ l (sv i) (hsv i) hN

include hk hβ in
theorem continuous_mixedCorrection (hsv : ∀ i, 0 ≤ sv i) :
    Continuous (mixedCorrection n h k (β := β) l sv) := by
  refine continuous_pi fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact (continuous_dataSecond n h k hk hβ l).comp continuous_subtype_val
    · exact continuous_energyCorrectionU n h k hk hβ l
    · exact continuous_freeEnergyCorrectionU n h k hk hβ l
  · exact continuous_laplaceCorrectionU n h k hk hβ l (sv i) (hsv i)

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m)
  (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hm hN in
/-- **Continuous convergence of the mixed vector** on the admissible domain. -/
theorem continuouslyConverges_mixedStat (hsv : ∀ i, 0 ≤ sv i) :
    ContinuouslyConverges (fun m => mixedStat n h k (β := β) l sv (Nseq m))
      (mixedCorrection n h k (β := β) l sv) := by
  refine continuouslyConverges_pi fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact (continuouslyConverges_nextLogStat n h k hk hβ l hmin hatt Nseq hN hm).comp_continuous
        continuous_subtype_val
    · exact continuouslyConverges_energyStatU n h k hk hβ l hmin hatt hm Nseq hN
    · exact continuouslyConverges_freeEnergyStatU n h k hk hβ l hmin hatt hm Nseq hN
  · exact continuouslyConverges_laplaceStatU n h k hk hβ l (sv i) hmin hatt hm Nseq hN (hsv i)

include hk hβ hmin hatt hm hN1 hN in
/-- **The joint random next-log posterior-observable theorem**: for random admissible data
`X_m ⇒ X` and `N_m → ∞`, the vector of next-log statistics (evidence, posterior energy mean, free
energy, posterior Laplace transforms at `s_1, …, s_r`) converges jointly with the data,
`(X_m, mixedStat_{N_m}(X_m)) ⇒ (X, mixedCorrection(X))`. -/
theorem randomMixed_graphLaw_tendsto (hsv : ∀ i, 0 ≤ sv i)
    {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_mixedStat n h k hk hβ l sv hsv (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_mixedCorrection n h k hk hβ l sv hsv).measurable)) :=
  haveI := polishSpace_admissibleData n h k hk hβ l
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto_polish hμ)
    (fun m => measurable_mixedStat n h k hk hβ l sv hsv (zero_le_one.trans (hN1 m).le))
    (continuouslyConverges_mixedStat n h k hk hβ l sv hmin hatt hm Nseq hN hsv)

end Grammar
