/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1Seq

/-!
# The `ℓ¹` upgrade: finite-dimensional convergence plus uniform tails

Convergence in distribution in `ℓ¹(ι, ℝ)` from convergence of all finite coordinate projections and
uniform smallness of the truncation tails (`tendstoInDistribution_of_finiteCoords`):
if `finiteCoords F_k ∘ S_n ⇒ finiteCoords F_k ∘ G` for every `k`, and
`E‖S_n − T_k S_n‖ ≤ t_k`, `E‖G − T_k G‖ ≤ t_k` with `t_k → 0`, then `S_n ⇒ G` in `ℓ¹`.

The proof is the bounded-Lipschitz portmanteau (`tendsto_iff_forall_lipschitz_integral_tendsto`):
`|E f(S_n) − E f(G)| ≤ L t_k + |E f(T_kS_n) − E f(T_kG)| + L t_k`, the middle term tending to `0`
by the finite-dimensional hypothesis composed with the continuous embedding `ℝ^F → ℓ¹`.

Non-claim: this is the upgrade with a *supplied* target; the existence of the target and the
finite-dimensional CLTs are separate theorems.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} [DecidableEq ι]

/-- The embedding `ℝ^F → ℓ¹`, `v ↦ ∑_{j∈F} v_j e_j`. -/
noncomputable def embedF (F : Finset ι) : EuclideanSpace ℝ F →L[ℝ] L1Seq ι :=
  ∑ j : F, (singleCLM (j : ι)).comp (EuclideanSpace.proj j)

theorem embedF_finiteCoords (F : Finset ι) (x : L1Seq ι) :
    embedF F (finiteCoords F x) = truncate F x := by
  rw [truncate_eq_sum, ← Finset.sum_coe_sort F]
  simp [embedF]

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

omit [DecidableEq ι] in
theorem integrable_comp_of_bounded_lipschitz {X : Ω → L1Seq ι} (hX : Measurable X)
    {f : L1Seq ι → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {L : ℝ≥0}
    (hL : LipschitzWith L f) : Integrable (fun ω => f (X ω)) Q := by
  refine Integrable.of_bound (hL.continuous.measurable.comp hX).aestronglyMeasurable (|f 0| + C)
    (Eventually.of_forall fun ω => ?_)
  have := hC (X ω) 0
  rw [Real.dist_eq] at this
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (f (X ω)) (f 0)]

/-- The truncation error of a bounded Lipschitz test function is controlled by the `L¹` tail. -/
theorem abs_integral_sub_truncate_le {X : Ω → L1Seq ι} (hX : Measurable X) {f : L1Seq ι → ℝ}
    {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {L : ℝ≥0} (hL : LipschitzWith L f) (F : Finset ι)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ∫⁻ ω, ‖X ω - truncate F (X ω)‖ₑ ∂Q ≤ ENNReal.ofReal t) :
    |∫ ω, f (X ω) ∂Q - ∫ ω, f (truncate F (X ω)) ∂Q| ≤ L * t := by
  have hTX : Measurable fun ω => truncate F (X ω) := (truncate F).continuous.measurable.comp hX
  have hD : Measurable fun ω => X ω - truncate F (X ω) :=
    (continuous_id.sub (truncate F).continuous).measurable.comp hX
  rw [← integral_sub (integrable_comp_of_bounded_lipschitz hX hC hL)
    (integrable_comp_of_bounded_lipschitz hTX hC hL), ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  simp_rw [ofReal_norm]
  have h1 : ∫⁻ ω, ‖f (X ω) - f (truncate F (X ω))‖ₑ ∂Q ≤ L * ENNReal.ofReal t := by
    calc ∫⁻ ω, ‖f (X ω) - f (truncate F (X ω))‖ₑ ∂Q
        ≤ ∫⁻ ω, (L : ℝ≥0∞) * ‖X ω - truncate F (X ω)‖ₑ ∂Q := by
          refine lintegral_mono fun ω => ?_
          rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
          exact hL.edist_le_mul _ _
      _ = L * ∫⁻ ω, ‖X ω - truncate F (X ω)‖ₑ ∂Q := lintegral_const_mul _ hD.enorm
      _ ≤ L * ENNReal.ofReal t := mul_le_mul' le_rfl ht
  calc (∫⁻ ω, ‖f (X ω) - f (truncate F (X ω))‖ₑ ∂Q).toReal
      ≤ ((L : ℝ≥0∞) * ENNReal.ofReal t).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) h1
    _ = L * t := by rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal ht0]

end Bound

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **The `ℓ¹` upgrade**: convergence in distribution of every finite coordinate projection, plus
uniform `L¹` smallness of the truncation tails of the sequence and of the target, gives convergence
in distribution in `ℓ¹`. -/
theorem tendstoInDistribution_of_finiteCoords {F : ℕ → Finset ι} {S : ℕ → Ω → L1Seq ι}
    {G : Ω' → L1Seq ι} (hS : ∀ n, Measurable (S n)) (hG : Measurable G)
    (hfd : ∀ k, TendstoInDistribution (fun n ω => finiteCoords (F k) (S n ω)) atTop
      (fun ω' => finiteCoords (F k) (G ω')) (fun _ => P) P')
    {t : ℕ → ℝ} (ht0 : ∀ k, 0 ≤ t k) (ht : Tendsto t atTop (𝓝 0))
    (htailS : ∀ k n, ∫⁻ ω, ‖S n ω - truncate (F k) (S n ω)‖ₑ ∂P ≤ ENNReal.ofReal (t k))
    (htailG : ∀ k, ∫⁻ ω, ‖G ω - truncate (F k) (G ω)‖ₑ ∂P' ≤ ENNReal.ofReal (t k)) :
    TendstoInDistribution S atTop G (fun _ => P) P' := by
  refine ⟨fun n => (hS n).aemeasurable, hG.aemeasurable, ?_⟩
  refine Iff.mpr tendsto_iff_forall_lipschitz_integral_tendsto ?_
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  have hfm : Measurable f := hL.continuous.measurable
  simp only [ProbabilityMeasure.coe_mk]
  simp_rw [integral_map (hS _).aemeasurable hfm.aestronglyMeasurable,
    integral_map hG.aemeasurable hfm.aestronglyMeasurable]
  -- the middle term: truncations converge by the finite-dimensional hypothesis
  have hmid : ∀ k, Tendsto (fun n => ∫ ω, f (truncate (F k) (S n ω)) ∂P) atTop
      (𝓝 (∫ ω, f (truncate (F k) (G ω)) ∂P')) := by
    intro k
    have h := (hfd k).continuous_comp (embedF (F k)).continuous
    have h2 := (Iff.mp tendsto_iff_forall_lipschitz_integral_tendsto h.tendsto) f ⟨C, hC⟩ ⟨L, hL⟩
    simp only [ProbabilityMeasure.coe_mk] at h2
    simp_rw [integral_map (h.forall_aemeasurable _) hfm.aestronglyMeasurable,
      integral_map h.aemeasurable_limit hfm.aestronglyMeasurable, Function.comp,
      embedF_finiteCoords] at h2
    exact h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hLt : Tendsto (fun k => (L : ℝ) * t k) atTop (𝓝 0) := by
    simpa using ht.const_mul (L : ℝ)
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hLt (ε / 3) (by positivity)).imp fun k hk =>
    hk k le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg L) (ht0 k))] at hk
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hmid k) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := abs_integral_sub_truncate_le (Q := P) (hS n) hC hL (F k) (ht0 k) (htailS k n)
  have h3 := abs_integral_sub_truncate_le (Q := P') hG hC hL (F k) (ht0 k) (htailG k)
  have h2 := hN n hn
  rw [Real.dist_eq] at h2 ⊢
  calc |∫ ω, f (S n ω) ∂P - ∫ ω, f (G ω) ∂P'|
      ≤ |∫ ω, f (S n ω) ∂P - ∫ ω, f (truncate (F k) (S n ω)) ∂P| +
        |∫ ω, f (truncate (F k) (S n ω)) ∂P - ∫ ω, f (truncate (F k) (G ω)) ∂P'| +
        |∫ ω, f (truncate (F k) (G ω)) ∂P' - ∫ ω, f (G ω) ∂P'| := by
          have := abs_sub_le (∫ ω, f (S n ω) ∂P) (∫ ω, f (truncate (F k) (S n ω)) ∂P)
            (∫ ω, f (G ω) ∂P')
          have := abs_sub_le (∫ ω, f (truncate (F k) (S n ω)) ∂P)
            (∫ ω, f (truncate (F k) (G ω)) ∂P') (∫ ω, f (G ω) ∂P')
          linarith
    _ < ε := by
          rw [abs_sub_comm] at h3
          linarith

end Grammar
