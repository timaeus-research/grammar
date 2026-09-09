/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.IsolatedRemainderUniform

/-!
# The stochastic second-order quotient from four statistics; multiplicity one (unit 333)

`tendstoInDistribution_secondOrder_of_stats` isolates the probabilistic core of Headline L: if
`Z¹_ℓ = D_ℓ (A_ℓ log N_ℓ + R_ℓ)` and `Z^φ_ℓ = D'_ℓ (A'_ℓ log N_ℓ + R'_ℓ)` exactly, with
deterministic nonzero normalisers `D_ℓ, D'_ℓ`, and the statistics
`(R_ℓ, A_ℓ, R'_ℓ, A'_ℓ) ⇒ (B, A, B', A')` jointly with `P(A = 0) = 0`, then `log N_ℓ
(Z^φ_ℓ/Z¹_ℓ · D_ℓ/D'_ℓ − A'_ℓ/A_ℓ) ⇒ (AB' − A'B)/A²`. With
`D = N^{-μ₀}L^{s}` this is the Headline L situation; with `D = N^{-μ₀}/L` and the log-weighted
remainder `R = L (Z/N^{-μ₀} − A) → 0` of `IsolatedRemainderUniform` it gives the **multiplicity-one
case** (`tendstoInDistribution_posterior_second_order_one`): both leading log degrees zero,
`log N_ℓ (Z^φ_ℓ/Z¹_ℓ · N_ℓ^{μ₀'−μ₀} − A'_ℓ/A_ℓ) ⇒ 0`, i.e. no `1/log N` correction, under
a.e. vanishing predecessor sums at `(μ₀, 0)`, `(μ₀', 0)`, residuals `E log N / N^{-μ₀} → 0` in
probability and `P(A = 0) = 0`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Second-order quotient from four statistics** (deterministic normalisers `D, D'`). -/
theorem tendstoInDistribution_secondOrder_of_stats (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i)
    (hN : Tendsto Nseq l atTop) (A R A' R' Zφ Z1 : ι → Ω → ℝ) (D D' : ι → ℝ)
    (hD : ∀ i, D i ≠ 0) (hD' : ∀ i, D' i ≠ 0)
    (hAm : ∀ i, Measurable (A i)) (hRm : ∀ i, Measurable (R i))
    (hA'm : ∀ i, Measurable (A' i)) (hR'm : ∀ i, Measurable (R' i))
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hZ1 : ∀ i ω, Z1 i ω = D i * (A i ω * Real.log (Nseq i) + R i ω))
    (hZφ : ∀ i ω, Zφ i ω = D' i * (A' i ω * Real.log (Nseq i) + R' i ω))
    (Az Bz A'z B'z : Ω' → ℝ) (hAzm : Measurable Az) (hBzm : Measurable Bz)
    (hA'zm : Measurable A'z) (hB'zm : Measurable B'z)
    (hV : TendstoInDistribution (fun i ω => (![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ)) l
      (fun ω => (![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ)) (fun _ => μ) μ')
    (hB : μ' {ω | Az ω = 0} = 0) :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
        (Zφ i ω / Z1 i ω * (D i / D' i) - A' i ω / A i ω)) l
      (fun ω => (Az ω * B'z ω - A'z ω * Bz ω) / Az ω ^ 2) (fun _ => μ) μ' := by
  have hVm : ∀ i, Measurable fun ω => (![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ) := fun i =>
    measurable_vec4 (hRm i) (hAm i) (hR'm i) (hA'm i)
  have hCzm : Measurable fun ω => (![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ) :=
    measurable_vec4 hBzm hAzm hB'zm hA'zm
  have hVc : TendstoInDistribution
      (fun i ω => ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹)) l
      (fun ω => ((![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ), (0 : ℝ))) (fun _ => μ) μ' :=
    hV.prodMk_of_tendstoInMeasure_const _ (fun i _ => (Real.log (Nseq i))⁻¹) _
      (tendstoInMeasure_const_of_tendsto (fun i => (Real.log (Nseq i))⁻¹) 0
        (tendsto_inv_log.comp hN)) (fun _ => aemeasurable_const)
  have hUW := hVc.continuous_comp continuous_secondOrderPair
  have hpairm : ∀ i, Measurable fun ω =>
      secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹) :=
    fun i => continuous_secondOrderPair.measurable.comp ((hVm i).prodMk measurable_const)
  have hpairzm : Measurable fun ω =>
      secondOrderPair ((![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ), (0 : ℝ)) :=
    continuous_secondOrderPair.measurable.comp (hCzm.prodMk measurable_const)
  have hW0 : μ' {ω | (secondOrderPair ((![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ), (0 : ℝ))).2 = 0}
      = 0 := by
    convert hB using 2
    ext ω
    simp [secondOrderPair]
  have hdiv0 := tendstoInDistribution_div
    (fun i ω => (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ),
      (Real.log (Nseq i))⁻¹)).1)
    (fun i ω => (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ),
      (Real.log (Nseq i))⁻¹)).2)
    (fun i => measurable_fst.comp (hpairm i)) (fun i => measurable_snd.comp (hpairm i))
    (fun ω => (secondOrderPair ((![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ), (0 : ℝ))).1)
    (fun ω => (secondOrderPair ((![Bz ω, Az ω, B'z ω, A'z ω] : Fin 4 → ℝ), (0 : ℝ))).2)
    (measurable_fst.comp hpairzm) (measurable_snd.comp hpairzm) hUW hW0
  have hdiv : TendstoInDistribution (fun i ω =>
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹)).1 /
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹)).2) l
      (fun ω => (Az ω * B'z ω - A'z ω * Bz ω) / Az ω ^ 2) (fun _ => μ) μ' := by
    convert hdiv0 using 2
    simp only [secondOrderPair]
    simp
    try ring
  have hTm : ∀ i, Measurable fun ω => Real.log (Nseq i) *
      (Zφ i ω / Z1 i ω * (D i / D' i) - A' i ω / A i ω) := fun i =>
    ((((hZφm i).div (hZ1m i)).mul_const _).sub ((hA'm i).div (hAm i))).const_mul _
  have hlimm : Measurable fun ω => (Az ω * B'z ω - A'z ω * Bz ω) / Az ω ^ 2 :=
    ((hAzm.mul hB'zm).sub (hA'zm.mul hBzm)).div (hAzm.pow_const 2)
  have hAdist : TendstoInDistribution A l Az (fun _ => μ) μ' := by
    have := hV.continuous_comp (g := fun v : Fin 4 → ℝ => v 1) (continuous_apply 1)
    convert this using 2 <;> simp [Function.comp_def]
  have hARdist : TendstoInDistribution (fun i ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹) l Az
      (fun _ => μ) μ' := by
    have := hVc.continuous_comp (g := fun q : (Fin 4 → ℝ) × ℝ => q.1 1 + q.1 0 * q.2)
      (by fun_prop)
    convert this using 2 <;> simp [Function.comp_def]
  have hARm : ∀ i, Measurable fun ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹ := fun i =>
    (hAm i).add ((hRm i).mul_const _)
  refine tendstoInDistribution_of_approx _ _ hTm hlimm fun η hη => ?_
  refine ⟨_, _, fun i => (measurable_fst.comp (hpairm i)).div (measurable_snd.comp (hpairm i)),
    hlimm, hdiv, ?_, by simp⟩
  obtain ⟨m, hm⟩ := ((tendsto_measure_abs_le_of_ae_ne_zero _ hAzm hB).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hη)))).exists
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hF : IsClosed {x : ℝ | |x| ≤ δ} := isClosed_le continuous_abs continuous_const
  have hmapz : (μ'.map Az) {x | |x| ≤ δ} = μ' {ω | |Az ω| ≤ δ} :=
    Measure.map_apply hAzm hF.measurableSet
  have hev1 : ∀ᶠ i in l, μ {ω | |A i ω| ≤ δ} < ENNReal.ofReal (η / 2) := by
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hAdist.tendsto hF
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hmap : ∀ i, (μ.map (A i)) {x | |x| ≤ δ} = μ {ω | |A i ω| ≤ δ} := fun i =>
      Measure.map_apply (hAm i) hF.measurableSet
    simp only [hmap, hmapz] at hport
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hport hm)
  have hev2 : ∀ᶠ i in l, μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} <
      ENNReal.ofReal (η / 2) := by
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hARdist.tendsto hF
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hmap : ∀ i, (μ.map fun ω => A i ω + R i ω * (Real.log (Nseq i))⁻¹) {x | |x| ≤ δ} =
        μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} := fun i =>
      Measure.map_apply (hARm i) hF.measurableSet
    simp only [hmap, hmapz] at hport
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hport hm)
  filter_upwards [hev1, hev2] with i hi1 hi2
  have hL : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
  have hsub : {ω | Real.log (Nseq i) * (Zφ i ω / Z1 i ω * (D i / D' i) - A' i ω / A i ω) ≠
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹)).1 /
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ),
        (Real.log (Nseq i))⁻¹)).2} ⊆
      {ω | |A i ω| ≤ δ} ∪ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} := by
    intro ω hω
    simp only [mem_setOf_eq, mem_union]
    by_contra hcon
    push_neg at hcon
    apply hω
    have hA0 : A i ω ≠ 0 := by
      intro h0
      have := hcon.1
      rw [h0, abs_zero] at this
      linarith
    have hAR0 : A i ω + R i ω * (Real.log (Nseq i))⁻¹ ≠ 0 := by
      intro h0
      have := hcon.2
      rw [h0, abs_zero] at this
      linarith
    have hRA2 : Real.log (Nseq i) * A i ω + R i ω ≠ 0 := by
      intro h0
      apply hAR0
      field_simp
      linear_combination h0
    have hinv : (Real.log (Nseq i) * A i ω + R i ω) * (Real.log (Nseq i) * A i ω + R i ω)⁻¹ = 1 :=
      mul_inv_cancel₀ hRA2
    have hq : Zφ i ω / Z1 i ω * (D i / D' i) =
        (A' i ω * Real.log (Nseq i) + R' i ω) / (A i ω * Real.log (Nseq i) + R i ω) := by
      rw [hZ1, hZφ]
      have hAL : A i ω * Real.log (Nseq i) + R i ω ≠ 0 := by
        intro h0
        apply hRA2
        linear_combination h0
      have hinvD : D i * (D i)⁻¹ = 1 := mul_inv_cancel₀ (hD i)
      have hinvD' : D' i * (D' i)⁻¹ = 1 := mul_inv_cancel₀ (hD' i)
      field_simp
      linear_combination (A' i ω * Real.log (Nseq i) + R' i ω) * (D i * (D i)⁻¹) * hinvD' +
        (A' i ω * Real.log (Nseq i) + R' i ω) * hinvD
    rw [hq]
    simp only [secondOrderPair]
    simp
    have hL0 : Real.log (Nseq i) ≠ 0 := hL.ne'
    have hAL : A i ω * Real.log (Nseq i) + R i ω ≠ 0 := by
      intro h0
      apply hRA2
      linear_combination h0
    have hden : A i ω * (A i ω + R i ω * (Real.log (Nseq i))⁻¹) =
        A i ω * (A i ω * Real.log (Nseq i) + R i ω) / Real.log (Nseq i) := by
      field_simp
      try ring
    rw [hden, div_sub_div _ _ hAL hA0, div_div_eq_mul_div, mul_div_assoc',
      div_eq_div_iff (mul_ne_zero hAL hA0) (mul_ne_zero hA0 hAL)]
    ring
  calc μ {ω | Real.log (Nseq i) * (Zφ i ω / Z1 i ω * (D i / D' i) - A' i ω / A i ω) ≠
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ), (Real.log (Nseq i))⁻¹)).1 /
      (secondOrderPair ((![R i ω, A i ω, R' i ω, A' i ω] : Fin 4 → ℝ),
        (Real.log (Nseq i))⁻¹)).2}
      ≤ μ ({ω | |A i ω| ≤ δ} ∪ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ}) :=
        measure_mono hsub
    _ ≤ μ {ω | |A i ω| ≤ δ} + μ {ω | |A i ω + R i ω * (Real.log (Nseq i))⁻¹| ≤ δ} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hi1.le hi2.le
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **The stochastic second-order quotient at multiplicity one**: both leading log degrees zero;
no `1/log N` correction. -/
theorem tendstoInDistribution_posterior_second_order_one (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    {μ₀ : ℝ} {a : ℕ} (hμ : μ₀ = (a : ℝ) / commonQ k) {μ₀' : ℝ} {a' : ℕ}
    (hμ' : μ₀' = (a' : ℝ) / commonQ k) (XY : ι → Ω → PairData K n)
    (hXYm : ∀ i, Measurable (XY i)) (Z : Ω' → PairData K n) (hZm : Measurable Z)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β (fun _ => 1) (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β (fun _ => 1) (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω * Real.log (Nseq i) / Nseq i ^ (-μ₀')) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω * Real.log (Nseq i) / Nseq i ^ (-μ₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ, absPredSum (commonQ k) (commonD n)
      (gCoeff ν h k β (fun _ => 1) (XY i ω).num) μ₀' 0 (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ, absPredSum (commonQ k) (commonD n)
      (gCoeff ν h k β (fun _ => 1) (XY i ω).den) μ₀ 0 (Nseq i) = 0)
    (hB : μ' {ω | gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0 = 0} = 0) :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω * Nseq i ^ (μ₀' - μ₀) -
        gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0 /
          gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0)) l
      (fun _ => (0 : ℝ)) (fun _ => μ) μ' := by
  have hden : TendstoInDistribution (fun i ω => (XY i ω).den) l (fun ω => (Z ω).den)
      (fun _ => μ) μ' := hXY.continuous_comp continuous_den
  have hnum : TendstoInDistribution (fun i ω => (XY i ω).num) l (fun ω => (Z ω).num)
      (fun _ => μ) μ' := hXY.continuous_comp continuous_num
  have hAc : Continuous fun p : PairData K n => gCoeff ν h k β (fun _ => 1) p.den μ₀ 0 :=
    (continuous_gCoeff ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) μ₀ 0).comp continuous_den
  have hA'c : Continuous fun p : PairData K n => gCoeff ν h k β (fun _ => 1) p.num μ₀' 0 :=
    (continuous_gCoeff ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) μ₀' 0).comp continuous_num
  have hAm : ∀ i, Measurable fun ω => gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0 := fun i =>
    hAc.measurable.comp (hXYm i)
  have hA'm : ∀ i, Measurable fun ω => gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0 := fun i =>
    hA'c.measurable.comp (hXYm i)
  -- the log-weighted remainders
  have hRm := tendstoInMeasure_randomOneTerm ν h k β hk hβ hμ _ _ hden Nseq hN1 hN Z1 E1 hd1 hE1 hp1
  have hR'm := tendstoInMeasure_randomOneTerm ν h k β hk hβ hμ' _ _ hnum Nseq hN1 hN Zφ Eφ hdφ hEφ
    hpφ
  -- the statistics vector converges to `(0, A, 0, A')`
  have hC : TendstoInDistribution (fun i ω => (![(0 : ℝ),
      gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0, (0 : ℝ),
      gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0] : Fin 4 → ℝ)) l
      (fun ω => (![(0 : ℝ), gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0, (0 : ℝ),
        gCoeff ν h k β (fun _ => 1) (Z ω).num μ₀' 0] : Fin 4 → ℝ)) (fun _ => μ) μ' :=
    hXY.continuous_comp (g := fun p : PairData K n => (![(0 : ℝ),
      gCoeff ν h k β (fun _ => 1) p.den μ₀ 0, (0 : ℝ),
      gCoeff ν h k β (fun _ => 1) p.num μ₀' 0] : Fin 4 → ℝ))
      (continuous_vec4 continuous_const hAc continuous_const hA'c)
  have hV : TendstoInDistribution (fun i ω => (![Real.log (Nseq i) *
      (Z1 i ω / Nseq i ^ (-μ₀) - gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0),
      gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0,
      Real.log (Nseq i) *
        (Zφ i ω / Nseq i ^ (-μ₀') - gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0),
      gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0] : Fin 4 → ℝ)) l
      (fun ω => (![(0 : ℝ), gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0, (0 : ℝ),
        gCoeff ν h k β (fun _ => 1) (Z ω).num μ₀' 0] : Fin 4 → ℝ)) (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
      (measurable_vec4 (((hZ1m i).div_const _).sub (hAm i) |>.const_mul _) (hAm i)
        (((hZφm i).div_const _).sub (hA'm i) |>.const_mul _) (hA'm i)).aemeasurable
    have hzero : TendstoInMeasure μ (fun i ω => (0 : ℝ)) l (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto (fun _ => (0 : ℝ)) 0 tendsto_const_nhds
    have hpi := tendstoInMeasure_pi_zero (μ := μ) (L := l) (κ := Fin 4) (E := ℝ)
      ![fun i ω => Real.log (Nseq i) *
          (Z1 i ω / Nseq i ^ (-μ₀) - gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0),
        fun _ _ => (0 : ℝ),
        fun i ω => Real.log (Nseq i) *
          (Zφ i ω / Nseq i ^ (-μ₀') - gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0),
        fun _ _ => (0 : ℝ)]
      (fun a => by fin_cases a <;> simp <;> first | exact hRm | exact hR'm | exact hzero)
    refine hpi.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    funext a
    simp only [Pi.sub_apply]
    fin_cases a <;> simp
  have hmain := tendstoInDistribution_secondOrder_of_stats Nseq hN1 hN
    (fun i ω => gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0)
    (fun i ω => Real.log (Nseq i) *
      (Z1 i ω / Nseq i ^ (-μ₀) - gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0))
    (fun i ω => gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0)
    (fun i ω => Real.log (Nseq i) *
      (Zφ i ω / Nseq i ^ (-μ₀') - gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0))
    Zφ Z1 (fun i => Nseq i ^ (-μ₀) / Real.log (Nseq i))
    (fun i => Nseq i ^ (-μ₀') / Real.log (Nseq i))
    (fun i => div_ne_zero (Real.rpow_pos_of_pos (by linarith [hN1 i]) _).ne'
      (Real.log_pos (hN1 i)).ne')
    (fun i => div_ne_zero (Real.rpow_pos_of_pos (by linarith [hN1 i]) _).ne'
      (Real.log_pos (hN1 i)).ne')
    hAm (fun i => (((hZ1m i).div_const _).sub (hAm i)).const_mul _) hA'm
    (fun i => (((hZφm i).div_const _).sub (hA'm i)).const_mul _) hZφm hZ1m
    (fun i ω => by
      have hN0 : 0 < Nseq i := by linarith [hN1 i]
      have hpow : Nseq i ^ (-μ₀) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
      have hlog : Real.log (Nseq i) ≠ 0 := (Real.log_pos (hN1 i)).ne'
      field_simp
      ring)
    (fun i ω => by
      have hN0 : 0 < Nseq i := by linarith [hN1 i]
      have hpow : Nseq i ^ (-μ₀') ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
      have hlog : Real.log (Nseq i) ≠ 0 := (Real.log_pos (hN1 i)).ne'
      field_simp
      ring)
    (fun ω => gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0) (fun _ => (0 : ℝ))
    (fun ω => gCoeff ν h k β (fun _ => 1) (Z ω).num μ₀' 0) (fun _ => (0 : ℝ))
    (hAc.measurable.comp hZm) measurable_const (hA'c.measurable.comp hZm) measurable_const hV hB
  have e1 : (fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω * Nseq i ^ (μ₀' - μ₀) -
      gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0 /
        gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0)) =
      fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω *
        (Nseq i ^ (-μ₀) / Real.log (Nseq i) / (Nseq i ^ (-μ₀') / Real.log (Nseq i))) -
        gCoeff ν h k β (fun _ => 1) (XY i ω).num μ₀' 0 /
          gCoeff ν h k β (fun _ => 1) (XY i ω).den μ₀ 0) := by
    funext i ω
    have hN0 : 0 < Nseq i := by linarith [hN1 i]
    have hlog : Real.log (Nseq i) ≠ 0 := (Real.log_pos (hN1 i)).ne'
    have hpow' : Nseq i ^ (-μ₀') ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    rw [show Nseq i ^ (μ₀' - μ₀) = Nseq i ^ (-μ₀) / Nseq i ^ (-μ₀') by
      rw [← Real.rpow_sub hN0]; congr 1; ring]
    congr 2
    field_simp
  have e2 : (fun _ : Ω' => (0 : ℝ)) = fun ω =>
      (gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0 * 0 -
        gCoeff ν h k β (fun _ => 1) (Z ω).num μ₀' 0 * 0) /
        gCoeff ν h k β (fun _ => 1) (Z ω).den μ₀ 0 ^ 2 := by
    funext ω
    simp
  rw [e1, e2]
  exact hmain

end Grammar
