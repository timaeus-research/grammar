/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalClosedJets
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tightness of random branch jets from envelopes (§20, consult #147 follow-up (a))

The conditional random-field theorem needs convergence in distribution of the random branch jets
in `BranchJetSpace μ`. The compactness half of such a statement is proved here without any data
model: if the jets of a sequence of random fields are, almost surely, bounded and Lipschitz with a
random envelope `A n` whose second moments are uniformly bounded, then the laws of the jets are
tight (★★ `isTightMeasureSet_of_jetEnvelope`). Route: the `M`-bounded, `M`-Lipschitz functions in
`C(K, V)` form a compact set for compact `K` and finite-dimensional `V` (Arzelà–Ascoli,
★ `isCompact_lipBall`); finite products of these are compact in the jet space (`jetBall`,
`isCompact_jetBall`); Markov's inequality bounds the probability that the envelope exceeds `M` by
`C/M²`. No Prokhorov theorem is used, and no independence is assumed. What remains for a genuine
limit theorem, and is NOT proved, is finite-dimensional convergence of the jet evaluations (which
would identify the limit) and, for the empirical root fields, the envelopes themselves.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Metric BoundedContinuousFunction
open scoped ENNReal NNReal
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

/-! ### Finite-dimensionality of continuous multilinear maps -/

section FinDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem finiteDimensional_continuousMultilinearMap :
    ∀ r : ℕ, FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F)
  | 0 => (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearEquiv.finiteDimensional
  | r + 1 => by
      have : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
        finiteDimensional_continuousMultilinearMap r
      have : FiniteDimensional ℝ (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
        (LinearMap.toContinuousLinearMap (E := E)
          (F' := ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F)).finiteDimensional
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) F).symm
        |>.toLinearEquiv.finiteDimensional

end FinDim

/-! ### The Lipschitz ball in `C(K, V)` is compact -/

section LipBall

variable {K V : Type*} [MetricSpace K] [CompactSpace K] [NormedAddCommGroup V] [ProperSpace V]

/-- The continuous maps bounded by `M` and `M`-Lipschitz. -/
def lipBall (K V : Type*) [MetricSpace K] [NormedAddCommGroup V] (M : ℝ≥0) : Set C(K, V) :=
  {f | (∀ x, ‖f x‖ ≤ M) ∧ LipschitzWith M f}

omit [CompactSpace K] [ProperSpace V] in
/-- Uniformly Lipschitz families are equicontinuous. -/
theorem equicontinuous_of_lipschitzWith {ι : Type*} {F : ι → K → V} (M : ℝ≥0)
    (h : ∀ i, LipschitzWith M (F i)) : Equicontinuous F := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hδ : 0 < ε / (M + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx i
  have hx' : dist x₀ x < ε / (M + 1) := by rwa [dist_comm]
  have hlt : (M : ℝ) / (M + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  calc dist (F i x₀) (F i x) ≤ M * dist x₀ x := (h i).dist_le_mul x₀ x
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hx'.le M.coe_nonneg
    _ = ε * (M / (M + 1)) := by ring
    _ < ε := mul_lt_of_lt_one_right hε hlt

/-- ★ **Arzelà–Ascoli for the Lipschitz ball**: `lipBall K V M` is compact for compact `K` and
finite-dimensional `V`. -/
theorem isCompact_lipBall (M : ℝ≥0) : IsCompact (lipBall K V M) := by
  set e := ContinuousMap.isometryEquivBoundedOfCompact K V with he
  let A : Set (K →ᵇ V) := {g | (∀ x, ‖g x‖ ≤ M) ∧ LipschitzWith M g}
  have hA : IsCompact A := by
    refine arzela_ascoli₂ (closedBall (0 : V) M) (isCompact_closedBall _ _) A ?_ ?_ ?_
    · have h1 : IsClosed {g : K →ᵇ V | ∀ x, ‖g x‖ ≤ M} := by
        rw [Set.ofPred_forall]
        exact isClosed_iInter fun x => isClosed_le
          (continuous_norm.comp ((continuous_apply x).comp continuous_coe)) continuous_const
      have h2 : IsClosed ((fun g : K →ᵇ V => (⇑g : K → V)) ⁻¹' {φ : K → V | LipschitzWith M φ}) :=
        (isClosed_setOfPred_lipschitzWith M).preimage continuous_coe
      exact h1.inter h2
    · intro g x hg
      exact mem_closedBall_zero_iff.2 (hg.1 x)
    · exact equicontinuous_of_lipschitzWith M fun g => g.2.2
  have hpre : lipBall K V M = e ⁻¹' A := by
    ext f
    have hcoe : (⇑(mkOfCompact f) : K → V) = ⇑f := funext fun x => mkOfCompact_apply f x
    show ((∀ x, ‖f x‖ ≤ M) ∧ LipschitzWith M ⇑f) ↔
      ((∀ x, ‖mkOfCompact f x‖ ≤ M) ∧ LipschitzWith M ⇑(mkOfCompact f))
    rw [hcoe]
  rw [hpre]
  exact e.toHomeomorph.isCompact_preimage.2 hA

end LipBall

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

instance instProperSpaceCMM (r : ℕ) :
    ProperSpace (ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin d → ℝ) ℝ) :=
  haveI := finiteDimensional_continuousMultilinearMap (E := Fin d → ℝ) (F := ℝ) r
  FiniteDimensional.proper ℝ _

/-- Jets all of whose coordinates are bounded by `M` and `M`-Lipschitz. -/
def jetBall (μ : ℝ) (M : ℝ≥0) : Set (Ξ.BranchJetSpace Y μ) :=
  {z | ∀ p r, BranchJetSpace.toPi Ξ Y z p r ∈ lipBall (Ξ.chartImage Y p) _ M}

/-- `toPi` as a homeomorphism (the jet space carries the product topology by definition). -/
def toPiHomeo (μ : ℝ) : Ξ.BranchJetSpace Y μ ≃ₜ
    (∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
      ContinuousMap (Ξ.chartImage Y p)
        (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) where
  toEquiv := Equiv.refl _
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem isCompact_jetBall (μ : ℝ) (M : ℝ≥0) : IsCompact (Ξ.jetBall Y μ M) := by
  have h : Ξ.jetBall Y μ M = (Ξ.toPiHomeo Y μ) ⁻¹'
      (Set.pi univ fun p => Set.pi univ fun r => lipBall (Ξ.chartImage Y p) _ M) := by
    ext z
    simp only [jetBall, Set.mem_ofPred_eq, mem_preimage, mem_univ_pi]
    rfl
  rw [h]
  exact (Ξ.toPiHomeo Y μ).isCompact_preimage.2
    (isCompact_univ_pi fun p => isCompact_univ_pi fun r => isCompact_lipBall M)

/-- ★★ **Tightness of random branch jets from a second-moment envelope**: if almost surely every
jet coordinate is bounded by `A n ω` and `A n ω`-Lipschitz, and `∫ (A n)² ≤ C` uniformly, the laws
of the jets are tight. -/
theorem isTightMeasureSet_of_jetEnvelope {μ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → Ξ.BranchJetSpace Y μ) (hX : ∀ n, Measurable (X n))
    (A : ℕ → Ω → ℝ≥0) (hA : ∀ n, Measurable (A n)) (C : ℝ≥0)
    (hmom : ∀ n, ∫⁻ ω, ((A n ω : ℝ≥0∞)) ^ 2 ∂P ≤ C)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ p r x, ‖BranchJetSpace.toPi Ξ Y (X n ω) p r x‖ ≤ A n ω)
    (hlip : ∀ n, ∀ᵐ ω ∂P, ∀ p r, LipschitzWith (A n ω) (BranchJetSpace.toPi Ξ Y (X n ω) p r)) :
    IsTightMeasureSet (Set.range fun n => P.map (X n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  -- a radius `M ≥ 1` with `C ≤ ε M²`
  obtain ⟨M, hM1, hMε⟩ : ∃ M : ℝ≥0, 1 ≤ M ∧ (C : ℝ≥0∞) ≤ ε * (M : ℝ≥0∞) ^ 2 := by
    rcases eq_or_ne ε ⊤ with h | h
    · refine ⟨1, le_rfl, ?_⟩
      rw [h, ENNReal.top_mul (by simp)]
      exact le_top
    · lift ε to ℝ≥0 using h
      have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      refine ⟨C / ε + 1, le_add_self, ?_⟩
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      push_cast
      have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
      have heq : (ε : ℝ) * ((C : ℝ) / ε + 1) ^ 2 = ((C : ℝ) + ε) ^ 2 / ε := by
        field_simp
      rw [heq, le_div_iff₀ hε']
      nlinarith [sq_nonneg (C : ℝ), sq_nonneg (ε : ℝ)]
  refine ⟨Ξ.jetBall Y μ M, Ξ.isCompact_jetBall Y μ M, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hK := (Ξ.isCompact_jetBall Y μ M).isClosed.measurableSet
  rw [Measure.map_apply (hX n) hK.compl]
  have hM0 : ((M : ℝ≥0∞) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (zero_lt_one.trans_le hM1).ne')
  have hMtop : ((M : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hsub : (X n ⁻¹' (Ξ.jetBall Y μ M)ᶜ) ≤ᵐ[P]
      {ω | (M : ℝ≥0∞) ^ 2 ≤ ((A n ω : ℝ≥0∞)) ^ 2} := by
    filter_upwards [hbound n, hlip n] with ω hb hl hω
    rcases le_or_gt (A n ω) M with hle | hlt
    · exfalso
      apply hω
      intro p r
      refine ⟨fun x => (hb p r x).trans (by exact_mod_cast hle), (hl p r).weaken hle⟩
    · exact pow_le_pow_left₀ zero_le (ENNReal.coe_le_coe.2 hlt.le) 2
  have hmeas : AEMeasurable (fun ω => ((A n ω : ℝ≥0∞)) ^ 2) P :=
    ((hA n).coe_nnreal_ennreal.pow_const 2).aemeasurable
  calc P (X n ⁻¹' (Ξ.jetBall Y μ M)ᶜ)
      ≤ P {ω | (M : ℝ≥0∞) ^ 2 ≤ ((A n ω : ℝ≥0∞)) ^ 2} := measure_mono_ae hsub
    _ ≤ (∫⁻ ω, ((A n ω : ℝ≥0∞)) ^ 2 ∂P) / (M : ℝ≥0∞) ^ 2 :=
        meas_ge_le_lintegral_div hmeas hM0 hMtop
    _ ≤ (C : ℝ≥0∞) / (M : ℝ≥0∞) ^ 2 := ENNReal.div_le_div_right (hmom n) _
    _ ≤ ε := (ENNReal.div_le_iff hM0 hMtop).2 hMε

end ResolvedData

end SmoothEngine

end Grammar
