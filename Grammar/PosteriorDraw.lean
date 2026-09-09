/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomFieldTransfer
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The random field jointly with a posterior draw

A weakly continuous family `Q : P → ProbabilityMeasure Z` of laws on a Polish space `Z` is a
Markov kernel (`kernelOfContinuous`: Giry measurability from the lower semicontinuity of open-set
masses and the π–λ theorem), so the marked mixture `μ(dp) Q(p, dz)` is a probability measure on
`P × Z` (`jointKernelLaw`, via `Measure.compProd`), with
`∫ f d(jointKernelLaw μ Q) = ∫ (∫ f(p, z) dQ(p)) dμ` (`integral_jointKernelLaw`).

The **marked-integral continuity** `p_j → p`, `q_j ⇒ q ⇒ ∫ f(p_j, z) dq_j → ∫ f(p, z) dq`
(`tendsto_integral_marked`: tightness of `{q_j}` plus uniform continuity of `f` on the compact
`({p} ∪ {p_j}) × C`) upgrades continuous convergence of law-valued maps `Q_n → Q` to continuous
convergence of the scalar maps `p ↦ ∫ f(p, z) dQ_n(p)`, and the graph-law transfer (LXXXIX) then
gives the **kernel-law transfer** `μ_n ⇒ μ₀ ⇒ μ_n(dp) Q_n(p, dz) ⇒ μ₀(dp) Q(p, dz)`
(`tendsto_jointKernelLaw`).

Instantiated for the chart posterior: `posteriorMap N p = Q_N(ext p)` converges continuously to
`limitPosteriorMap p = Q̃(ext p)` (`continuouslyConverges_posteriorMap`), the limit map is
continuous (`continuous_limitPosteriorMap`), and for random phases `X_m ⇒ X` in `C(K, ℝ)` the joint
law of the environment with one posterior draw converges,
`μ_m(dp) Q_{N_m}(ext p)(dz) ⇒ μ₀(dp) Q̃(ext p)(dz)` on `C(K, ℝ) × ℝ × ℝ^d`
(`randomField_posteriorDraw_tendsto`), as does the annealed posterior-draw marginal
(`randomField_posteriorDraw_marginal_tendsto`).

Not claimed: the original-space posterior; stable convergence relative to an external σ-algebra;
convergence in law of the phase field itself.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Grammar

open BoundedContinuousFunction

/-! ### Weakly continuous families are Markov kernels -/

section kernel

variable {P Z : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [TopologicalSpace Z] [TopologicalSpace.PseudoMetrizableSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- **Giry measurability of a weakly continuous family**: open-set masses are lower
semicontinuous (portmanteau), and the class of sets with measurable mass is a Dynkin system. -/
theorem measurable_toMeasure_of_continuous {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q) :
    Measurable fun p => (Q p : Measure Z) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable fun p => (Q p : Measure Z) s)
    (h_eq := BorelSpace.measurable_eq) isPiSystem_isOpen ?_ ?_ ?_ ?_ s hs
  · simp
  · intro U hU
    refine LowerSemicontinuous.measurable ?_
    rw [lowerSemicontinuous_iff_le_liminf]
    intro p
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hQ.tendsto p) hU
  · intro t ht ih
    have : (fun p => (Q p : Measure Z) tᶜ) = fun p => 1 - (Q p : Measure Z) t := funext fun p => by
      rw [measure_compl ht (measure_ne_top _ _), measure_univ]
    rw [this]
    exact measurable_const.sub ih
  · intro f hdisj hf ih
    have : (fun p => (Q p : Measure Z) (⋃ i, f i)) = fun p => ∑' i, (Q p : Measure Z) (f i) :=
      funext fun p => measure_iUnion hdisj hf
    rw [this]
    exact Measurable.tsum ih

/-- The Markov kernel of a weakly continuous family of laws. -/
noncomputable def kernelOfContinuous {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q) :
    Kernel P Z :=
  ⟨fun p => (Q p : Measure Z), measurable_toMeasure_of_continuous hQ⟩

theorem kernelOfContinuous_apply {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q) (p : P) :
    kernelOfContinuous hQ p = (Q p : Measure Z) := rfl

instance isMarkovKernel_kernelOfContinuous {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q) :
    IsMarkovKernel (kernelOfContinuous hQ) :=
  ⟨fun p => by rw [kernelOfContinuous_apply]; infer_instance⟩

/-- The joint law `μ(dp) Q(p, dz)` of an environment and one draw from the kernel. -/
noncomputable def jointKernelLaw (μ : ProbabilityMeasure P) {Q : P → ProbabilityMeasure Z}
    (hQ : Continuous Q) : ProbabilityMeasure (P × Z) :=
  ⟨(μ : Measure P) ⊗ₘ kernelOfContinuous hQ, inferInstance⟩

theorem integral_jointKernelLaw [SecondCountableTopology Z]
    (μ : ProbabilityMeasure P) {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q)
    (f : (P × Z) →ᵇ ℝ) :
    ∫ x, f x ∂(jointKernelLaw μ hQ : Measure (P × Z)) =
      ∫ p, ∫ z, f (p, z) ∂(Q p : Measure Z) ∂(μ : Measure P) := by
  change ∫ x, f x ∂((μ : Measure P) ⊗ₘ kernelOfContinuous hQ) = _
  rw [Measure.integral_compProd (Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (Eventually.of_forall fun x => f.norm_coe_le_norm x))]
  rfl

/-- The annealed marginal `∫ Q(p, ·) dμ(p)` of the joint kernel law integrates as an iterated
integral. -/
theorem integral_jointKernelLaw_snd [SecondCountableTopology Z]
    (μ : ProbabilityMeasure P) {Q : P → ProbabilityMeasure Z} (hQ : Continuous Q) (g : Z →ᵇ ℝ) :
    ∫ z, g z ∂((jointKernelLaw μ hQ).map measurable_snd.aemeasurable : Measure Z) =
      ∫ p, ∫ z, g z ∂(Q p : Measure Z) ∂(μ : Measure P) := by
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map measurable_snd.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  exact integral_jointKernelLaw μ hQ (g.compContinuous ⟨Prod.snd, continuous_snd⟩)

end kernel

/-! ### Marked integrals -/

section sections

variable {P Z : Type*} [TopologicalSpace P] [MetricSpace Z]

/-- The section `z ↦ f (p, z)` of a bounded continuous function. -/
noncomputable def sectionBCF (f : (P × Z) →ᵇ ℝ) (p : P) : Z →ᵇ ℝ :=
  f.compContinuous ⟨fun z => (p, z), continuous_const.prodMk continuous_id⟩

theorem sectionBCF_apply (f : (P × Z) →ᵇ ℝ) (p : P) (z : Z) : sectionBCF f p z = f (p, z) := rfl

theorem norm_sectionBCF_le (f : (P × Z) →ᵇ ℝ) (p : P) : ‖sectionBCF f p‖ ≤ ‖f‖ :=
  f.norm_compContinuous_le _

variable [MeasurableSpace Z] [OpensMeasurableSpace Z]

theorem abs_integral_section_le (f : (P × Z) →ᵇ ℝ) (p : P) (q : ProbabilityMeasure Z) :
    |∫ z, f (p, z) ∂(q : Measure Z)| ≤ ‖f‖ := by
  have := norm_integral_le_norm (q : Measure Z) (sectionBCF f p)
  simp only [sectionBCF_apply, Real.norm_eq_abs] at this
  exact this.trans (norm_sectionBCF_le f p)

/-- The comparison `|∫ g dμ − ∫ g' dμ| ≤ δ + 2B μ(Cᶜ)` for measurable `|g|, |g'| ≤ B` with
`|g − g'| < δ` on the compact `C`. -/
theorem abs_integral_sub_le_of_close_on_compact {μ : Measure Z} [IsProbabilityMeasure μ]
    {g g' : Z → ℝ} (hg : Measurable g) (hg' : Measurable g') {B : ℝ} (hgB : ∀ z, |g z| ≤ B)
    (hg'B : ∀ z, |g' z| ≤ B) {C : Set Z} (hC : IsCompact C) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ z ∈ C, |g z - g' z| < δ) :
    |∫ z, g z ∂μ - ∫ z, g' z ∂μ| ≤ δ + 2 * B * (μ Cᶜ).toReal := by
  have hCm : MeasurableSet Cᶜ := hC.isClosed.measurableSet.compl
  have hi1 : Integrable g μ :=
    Integrable.of_bound hg.aestronglyMeasurable B (Eventually.of_forall fun z => hgB z)
  have hi2 : Integrable g' μ :=
    Integrable.of_bound hg'.aestronglyMeasurable B (Eventually.of_forall fun z => hg'B z)
  rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  have hind : Integrable (fun z => δ + 2 * B * Cᶜ.indicator (fun _ => (1 : ℝ)) z) μ :=
    (integrable_const δ).add (((integrable_const (1 : ℝ)).indicator hCm).const_mul _)
  refine (norm_integral_le_of_norm_le hind (Eventually.of_forall fun z => ?_)).trans (le_of_eq ?_)
  · by_cases hz : z ∈ C
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hz), mul_zero, add_zero, Real.norm_eq_abs]
      exact (hclose z hz).le
    · rw [Set.indicator_of_mem (Set.mem_compl hz), mul_one, Real.norm_eq_abs]
      have := abs_sub (g z) (g' z)
      have := hgB z
      have := hg'B z
      linarith
  · rw [integral_add (integrable_const δ) (((integrable_const (1 : ℝ)).indicator hCm).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    congr 2
    exact integral_indicator_one hCm

end sections

section marked

variable {P Z : Type*} [MetricSpace P] [MetricSpace Z] [CompleteSpace Z]
  [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]

/-- **Continuity of marked integrals**: if `p_j → p` in `P` and `q_j ⇒ q` on the Polish space `Z`,
then `∫ f(p_j, z) dq_j → ∫ f(p, z) dq` for every bounded continuous `f` on `P × Z`. -/
theorem tendsto_integral_marked (f : (P × Z) →ᵇ ℝ) {x : ℕ → P} {p : P}
    (hx : Tendsto x atTop (𝓝 p)) {q : ℕ → ProbabilityMeasure Z} {q₀ : ProbabilityMeasure Z}
    (hq : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun j => ∫ z, f (x j, z) ∂(q j : Measure Z)) atTop
      (𝓝 (∫ z, f (p, z) ∂(q₀ : Measure Z))) := by
  have h2 : Tendsto (fun j => ∫ z, f (p, z) ∂(q j : Measure Z)) atTop
      (𝓝 (∫ z, f (p, z) ∂(q₀ : Measure Z))) := by
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hq (sectionBCF f p)
    simpa only [sectionBCF_apply] using this
  have h1 : Tendsto (fun j => ∫ z, f (x j, z) ∂(q j : Measure Z) -
      ∫ z, f (p, z) ∂(q j : Measure Z)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    set δ := ε / (2 * (1 + 2 * ‖f‖)) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨C, hC, hqC⟩ := tight_of_tendsto hq δ hδ0
    have hS : IsCompact (insert p (range x)) := hx.isCompact_insert_range
    obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.1
      ((hS.prod hC).uniformContinuousOn_of_continuous f.continuous.continuousOn) δ hδ0
    filter_upwards [Metric.tendsto_nhds.1 hx η hη] with j hj
    rw [dist_zero_right, Real.norm_eq_abs]
    have hclose : ∀ z ∈ C, |f (x j, z) - f (p, z)| < δ := fun z hz => by
      rw [← Real.dist_eq]
      refine hunif (x j, z) ⟨mem_insert_of_mem _ (mem_range_self j), hz⟩ (p, z)
        ⟨mem_insert _ _, hz⟩ ?_
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hj
    calc |∫ z, f (x j, z) ∂(q j : Measure Z) - ∫ z, f (p, z) ∂(q j : Measure Z)|
        ≤ δ + 2 * ‖f‖ * ((q j : Measure Z) Cᶜ).toReal :=
          abs_integral_sub_le_of_close_on_compact
            (f.continuous.comp (continuous_const.prodMk continuous_id)).measurable
            (f.continuous.comp (continuous_const.prodMk continuous_id)).measurable
            (fun z => (Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm _))
            (fun z => (Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm _)) hC hδ0.le hclose
      _ ≤ δ + 2 * ‖f‖ * δ := by gcongr; exact hqC j
      _ = ε / 2 := by rw [hδ]; field_simp
      _ < ε := half_lt_self hε
  have := h1.add h2
  rw [zero_add] at this
  exact this.congr' (Eventually.of_forall fun j => by simp only [sub_add_cancel])

end marked

/-! ### The kernel-law transfer -/

section transfer

variable {P Z : Type*} [MetricSpace P] [MetricSpace Z] [CompleteSpace Z]
  [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]

/-- Scalar continuous convergence of the marked integrals of a continuously convergent family of
laws. -/
theorem continuouslyConverges_integral_marked (f : (P × Z) →ᵇ ℝ)
    {Qn : ℕ → P → ProbabilityMeasure Z} {Q : P → ProbabilityMeasure Z}
    (hcc : ContinuouslyConverges Qn Q) :
    ContinuouslyConverges (fun n p => ∫ z, f (p, z) ∂(Qn n p : Measure Z))
      fun p => ∫ z, f (p, z) ∂(Q p : Measure Z) :=
  continuouslyConverges_of_seq fun p κ x hκ hx =>
    tendsto_integral_marked f hx (hcc.tendsto_seq κ hκ x p hx)

theorem continuous_integral_marked (f : (P × Z) →ᵇ ℝ) {Q : P → ProbabilityMeasure Z}
    (hQ : Continuous Q) : Continuous fun p => ∫ z, f (p, z) ∂(Q p : Measure Z) :=
  continuous_iff_seqContinuous.2 fun _ p hx =>
    tendsto_integral_marked f hx ((hQ.tendsto p).comp hx)

variable [CompleteSpace P] [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]

/-- **Kernel-law transfer**: if `μ_n ⇒ μ₀` on the Polish space `P` and the weakly continuous
families `Q_n → Q` converge continuously, then `μ_n(dp) Q_n(p, dz) ⇒ μ₀(dp) Q(p, dz)` on
`P × Z`. -/
theorem tendsto_jointKernelLaw {μ : ℕ → ProbabilityMeasure P} {μ₀ : ProbabilityMeasure P}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) {Qn : ℕ → P → ProbabilityMeasure Z}
    {Q : P → ProbabilityMeasure Z} (hQn : ∀ n, Continuous (Qn n)) (hQ : Continuous Q)
    (hcc : ContinuouslyConverges Qn Q) :
    Tendsto (fun n => jointKernelLaw (μ n) (hQn n)) atTop (𝓝 (jointKernelLaw μ₀ hQ)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  simp_rw [integral_jointKernelLaw]
  have hccF := continuouslyConverges_integral_marked f hcc
  have hFm : ∀ n, Measurable fun p => ∫ z, f (p, z) ∂(Qn n p : Measure Z) := fun n =>
    (continuous_integral_marked f (hQn n)).measurable
  have hgraph := tendsto_graphLaw_of_polish hμ hFm hccF
  have hc : Continuous fun z : P × ℝ => clipTo ‖f‖ z.2 := (continuous_clipTo _).comp continuous_snd
  let G : (P × ℝ) →ᵇ ℝ := mkOfBound ⟨fun z => clipTo ‖f‖ z.2, hc⟩ (2 * ‖f‖) fun x y => by
    change dist (clipTo ‖f‖ x.2) (clipTo ‖f‖ y.2) ≤ _
    rw [Real.dist_eq]
    have := abs_sub (clipTo ‖f‖ x.2) (clipTo ‖f‖ y.2)
    have := abs_clipTo_le (norm_nonneg f) x.2
    have := abs_clipTo_le (norm_nonneg f) y.2
    linarith
  have hGapp : ∀ (p : P) (v : ℝ), G (p, v) = clipTo ‖f‖ v := fun _ _ => rfl
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hgraph G
  simp_rw [integral_graphLaw, hGapp] at this
  have e1 : ∀ (n : ℕ) (p : P), clipTo ‖f‖ (∫ z, f (p, z) ∂(Qn n p : Measure Z)) =
      ∫ z, f (p, z) ∂(Qn n p : Measure Z) := fun n p =>
    clipTo_of_abs_le (abs_integral_section_le f p (Qn n p))
  have e2 : ∀ p : P, clipTo ‖f‖ (∫ z, f (p, z) ∂(Q p : Measure Z)) =
      ∫ z, f (p, z) ∂(Q p : Measure Z) := fun p =>
    clipTo_of_abs_le (abs_integral_section_le f p (Q p))
  simp_rw [e1, e2] at this
  exact this

end transfer

/-! ### The spatial posterior: random field jointly with one posterior draw -/

section spatial

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)

/-- The limiting posterior law `Q̃(ext p)` as a probability-measure-valued function of the
phase. -/
noncomputable def limitPosteriorMap (p : C(PhaseDomain n, ℝ)) :
    ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ)) :=
  ⟨spatialJointFaceLaw h k l β (extPhase p) η, spatialJointFaceLaw_isProbabilityMeasure h k hk
    (ratioExp_min_pos h k hk hatt) hβ hmin (continuous_extPhase p) hηc hηnn
    (spatialMass_pos_of_face h k hk l β _ η (spatialFace_pos_of_faceWeight h k hk
      (ratioExp_min_pos h k hk hatt) hβ hmin (continuous_extPhase p) hηc hηnn hW))⟩

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hN1 hN in
/-- Arbitrary-index sequential convergence of the posterior laws: `Q_{N_{κ_j}}(ext x_j) ⇒ Q̃(ext p)`
for `x_j → p` in `C(K, ℝ)`. -/
theorem posteriorMap_tendsto_seq (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (x : ℕ → C(PhaseDomain n, ℝ)) (p : C(PhaseDomain n, ℝ)) (hx : Tendsto x atTop (𝓝 p)) :
    Tendsto (fun j => phaseJointLawP n h k (Nseq (κ j)) hβ.le hηc hηnn hW (x j)) atTop
      (𝓝 (limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW p)) :=
  movingPhaseJointLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hW (continuous_extPhase p)
    (fun j => Nseq (κ j)) (fun _ => hN1 _) (hN.comp hκ) (fun j => extPhase (x j))
    (fun j => (continuous_extPhase (x j)).measurable) (fun j => ‖x j - p‖)
    (tendsto_iff_norm_sub_tendsto_zero.1 hx) (fun j u _ => abs_extPhase_sub_le (x j) p u)
    (fun j => origPhaseIntegral_pos n h k β _ hηc hηnn hW (continuous_extPhase (x j)))
    (fun _ => origPhaseIntegral_pos n h k β _ hηc hηnn hW (continuous_extPhase p))

include hN1 hN in
/-- **Continuous convergence of the posterior laws** `Q_{N_m}(ext ·) → Q̃(ext ·)` on `C(K, ℝ)`. -/
theorem continuouslyConverges_posteriorMap :
    ContinuouslyConverges (fun m => phaseJointLawP n h k (Nseq m) hβ.le hηc hηnn hW)
      (limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW) :=
  continuouslyConverges_of_seq fun p κ x hκ hx =>
    posteriorMap_tendsto_seq n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN κ hκ x p hx

/-- **Continuity of the limiting posterior law in the phase**, `p ↦ Q̃(ext p)`. -/
theorem continuous_limitPosteriorMap :
    Continuous (limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW) :=
  continuous_iff_seqContinuous.2 fun x p hx =>
    spatialJointFaceLaw_tendsto_of_uniform n h k hk hβ hηc hηnn hmin hatt hW
      (continuous_extPhase p) (fun j => extPhase (x j)) (fun j => continuous_extPhase (x j))
      (fun j => ‖x j - p‖) (tendsto_iff_norm_sub_tendsto_zero.1 hx)
      (fun j u _ => abs_extPhase_sub_le (x j) p u)

variable {μ : ℕ → ProbabilityMeasure C(PhaseDomain n, ℝ)}
  {μ₀ : ProbabilityMeasure C(PhaseDomain n, ℝ)} (hμ : Tendsto μ atTop (𝓝 μ₀))

include hN1 hN hμ in
/-- **Random field jointly with one posterior draw**: if the random phases converge in law,
`X_m ⇒ X` in `C(K, ℝ)`, then the joint law of the environment and a draw from the chart posterior
converges, `μ_m(dp) Q_{N_m}(ext p)(dz) ⇒ μ₀(dp) Q̃(ext p)(dz)` on `C(K, ℝ) × ℝ × ℝ^d`. -/
theorem randomField_posteriorDraw_tendsto :
    Tendsto (fun m => jointKernelLaw (μ m)
        (continuous_phaseJointLawP n h k (Nseq m) hβ.le hηc hηnn hW)) atTop
      (𝓝 (jointKernelLaw μ₀ (continuous_limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW))) :=
  tendsto_jointKernelLaw hμ _ _ (continuouslyConverges_posteriorMap n h k hk hβ hηc hηnn hmin hatt
    hW Nseq hN1 hN)

include hN1 hN hμ in
/-- The annealed posterior-draw marginal `∫ Q_{N_m}(ext p) dμ_m(p) ⇒ ∫ Q̃(ext p) dμ₀(p)`. -/
theorem randomField_posteriorDraw_marginal_tendsto :
    Tendsto (fun m => (jointKernelLaw (μ m)
        (continuous_phaseJointLawP n h k (Nseq m) hβ.le hηc hηnn hW)).map
          measurable_snd.aemeasurable) atTop
      (𝓝 ((jointKernelLaw μ₀ (continuous_limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW)).map
        measurable_snd.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (randomField_posteriorDraw_tendsto n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN hμ)
    continuous_snd

end spatial

end Grammar
