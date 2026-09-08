/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.QuotientInDistribution

/-!
# The leading-order posterior quotient after chart assembly (Stage S18 — Headline XXXVIII)

Unit 287 (Astra #35, tranche A4-L; review v31: pass). Numerator and denominator of the posterior
expectation `E[φ] = Z^0[φ]/Z^0[1]` are the assembled integrals of two amplitude families on the
same charts; their joint tangential data form `PairData K n = JointData K n × JointData K n`
(denominator first, numerator second; sup norm; Borel σ-algebra by the declared instances;
`.den`, `.num`). **The type does not enforce a shared phase or the relation `η_φ = φ·η_1`**: the
paper's common-phase, amplitude-linked posterior model is a specialisation of the pair model, and
the joint convergence `(X_ℓ, Y_ℓ) ⇒ (X, Y)` is a hypothesis retaining whatever dependence the
pair has. Let `N_ℓ → ∞` with `N_ℓ > 1`, and let the external a.e. decompositions
`Z^0_ℓ[1] = 𝒵^{glob}(N_ℓ; X_ℓ) + E¹_ℓ`, `Z^0_ℓ[φ] = 𝒵^{glob}(N_ℓ; Y_ℓ) + E^φ_ℓ` hold with
residuals negligible in probability at the leading scale `a_ℓ = N_ℓ^{-μ₀}(log N_ℓ)^{j₀}`. Suppose
the target `(μ₀, j₀)` is **leading at the source**: the aggregate predecessor sums of both
families vanish a.s. at every source index (individual predecessor coefficients need not vanish;
the numerator coefficient itself may vanish), and the limiting denominator coefficient is a.s.
nonzero, `P(C¹_{μ₀,j₀}(X) = 0) = 0` (not positivity). Then

`Z^0_ℓ[φ] / Z^0_ℓ[1] ⇒ C^φ_{μ₀,j₀}(Y) / C¹_{μ₀,j₀}(X)`

(`tendstoInDistribution_posterior_leading`, **Headline XXXVIII**): the leading-order clause of
`cor:empirical_expectation` after finite chart assembly in arbitrary normal dimensions. Route: the
pair of assembled remainders **minus the coefficients evaluated at the same source datum** tends
to zero in probability (uniform on joint balls + norm-boundedness in probability), the residual
pair tends to zero in probability, so the normalised pair `(Z^0[φ]/a_ℓ, Z^0[1]/a_ℓ)` converges
jointly to `(C^φ(Y), C¹(X))` by vector Slutsky, and the generic quotient theorem of unit 286
finishes. Non-claims: no all-orders quotient expansion; the leading target is deterministic and
given; predecessor vanishing at the LIMIT alone would not suffice (source vanishing is a
sufficient hypothesis, not the weakest); finite-sample positivity of `Z^0[1]` is a separate
application fact; no random leading index; no convergence of expectations or moments follows
from the convergence in distribution.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-! ### Two small in-measure lemmas -/

theorem tendstoInMeasure_add_zero {E : Type*} [NormedAddCommGroup E] {f g : ι → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω + g i ω) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h1 := hf (ε / 2) (half_pos hε)
  have h2 := hg (ε / 2) (half_pos hε)
  have := h1.add h2
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => ?_)
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_setOf_eq, sub_zero, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := norm_add_le (f i ω) (g i ω)
  linarith [hcon.1, hcon.2]

theorem tendstoInMeasure_prodMk_zero' {f g : ι → Ω → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => (f i ω, g i ω)) l (fun _ => (0 : ℝ × ℝ)) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have := (hf ε hε).add (hg ε hε)
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => ?_)
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_setOf_eq, sub_zero, mem_union, Prod.norm_def, Prod.fst_zero, Prod.snd_zero] at hω ⊢
  rcases le_max_iff.1 hω with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Pair data -/

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ}

/-- Joint tangential data of the denominator (first) and numerator (second) families. -/
def PairData (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] (n : Fin M → ℕ) :=
  JointData K n × JointData K n

noncomputable instance : NormedAddCommGroup (PairData K n) :=
  inferInstanceAs (NormedAddCommGroup (JointData K n × JointData K n))
noncomputable instance : MeasurableSpace (PairData K n) := borel (PairData K n)
instance : BorelSpace (PairData K n) := ⟨rfl⟩

/-- The denominator datum. -/
def PairData.den (p : PairData K n) : JointData K n := p.1
/-- The numerator datum. -/
def PairData.num (p : PairData K n) : JointData K n := p.2

theorem continuous_den : Continuous fun p : PairData K n => p.den :=
  (continuous_fst : Continuous fun p : JointData K n × JointData K n => p.1)

theorem continuous_num : Continuous fun p : PairData K n => p.num :=
  (continuous_snd : Continuous fun p : JointData K n × JointData K n => p.2)

theorem norm_den_le (p : PairData K n) : ‖p.den‖ ≤ ‖p‖ :=
  norm_fst_le (p : JointData K n × JointData K n)

theorem norm_num_le (p : PairData K n) : ‖p.num‖ ≤ ‖p‖ :=
  norm_snd_le (p : JointData K n × JointData K n)

variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The pair of leading coefficients `(C^φ_{μ,j}(num), C¹_{μ,j}(den))`. -/
noncomputable def pairCoeff (p : PairData K n) (μ₀ : ℝ) (j : ℕ) : ℝ × ℝ :=
  (gCoeff ν h k β b p.num μ₀ j, gCoeff ν h k β b p.den μ₀ j)

theorem continuous_pairCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ₀ : ℝ)
    (j : ℕ) : Continuous fun p : PairData K n => pairCoeff ν h k β b p μ₀ j :=
  ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j).comp continuous_num).prodMk
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j).comp continuous_den)

/-- The pair of assembled remainders minus the pair of coefficients **at the same source datum**
tends to zero in probability. -/
theorem tendstoInMeasure_pairRemainder_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (XY : ι → Ω → PairData K n) (Z : Ω' → PairData K n)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω =>
      (gRemainder ν h k β b (XY i ω).num μ₀ j (Nseq i) - gCoeff ν h k β b (XY i ω).num μ₀ j,
       gRemainder ν h k β b (XY i ω).den μ₀ j (Nseq i) - gCoeff ν h k β b (XY i ω).den μ₀ j))
      l (fun _ => (0 : ℝ × ℝ)) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ XY (fun R hR ε hε => ?_)
    (normBounded_of_tendstoInDistribution' XY Z hXY)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ hj R) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have h1 := hi (XY i ω).num (by simpa using (norm_num_le (XY i ω)).trans hω)
  have h2 := hi (XY i ω).den (by simpa using (norm_den_le (XY i ω)).trans hω)
  rw [Real.dist_eq, abs_sub_comm] at h1 h2
  rw [Prod.norm_def]
  exact max_le (by simpa [Real.norm_eq_abs] using h1.le) (by simpa [Real.norm_eq_abs] using h2.le)

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  [l.IsCountablyGenerated]

/-- **Joint convergence of the normalised numerator and denominator** at a source-leading target. -/
theorem tendstoInDistribution_pair_normalised (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j₀ : ℕ}
    (hj : j₀ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀ j₀ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀ j₀ (Nseq i) = 0) :
    TendstoInDistribution (fun i ω => (Zφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀),
        Z1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀))) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' := by
  have hC : TendstoInDistribution (fun i ω => pairCoeff ν h k β b (XY i ω) μ₀ j₀) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' :=
    hXY.continuous_comp (g := fun p => pairCoeff ν h k β b p μ₀ j₀)
      (continuous_pairCoeff ν h k β b hk hβ hb μ₀ j₀)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => ?_
  · -- the difference is a.e. the pair of (remainder − coefficient) plus the normalised residuals
    have hsum := tendstoInMeasure_add_zero
      (tendstoInMeasure_pairRemainder_sub ν h k β b hk hβ hb hμ hj XY Z hXY Nseq hN)
      (tendstoInMeasure_prodMk_zero' hEφ hE1)
    refine TendstoInMeasure.congr (fun i => ?_) (Eventually.of_forall fun _ => rfl) hsum
    filter_upwards [hdφ i, hd1 i, hpφ i, hp1 i] with ω hφ h1 hpφ' hp1'
    simp only [Pi.sub_apply, pairCoeff, Prod.mk_add_mk, Prod.mk_sub_mk]
    unfold gRemainder abstractRemainder
    rw [hφ, h1, hpφ', hp1']
    ext <;> simp only <;> ring
  · exact ((hZφm i).div_const _).prodMk ((hZ1m i).div_const _) |>.aemeasurable

/-- **Headline XXXVIII — the leading-order posterior quotient after chart assembly.** Under the
hypotheses of `tendstoInDistribution_pair_normalised` and `P(C¹_{μ₀,j₀}(X) = 0) = 0`,
`Z^0_ℓ[φ] / Z^0_ℓ[1] ⇒ C^φ_{μ₀,j₀}(Y) / C¹_{μ₀,j₀}(X)`. -/
theorem tendstoInDistribution_posterior_leading (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j₀ : ℕ}
    (hj : j₀ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hZm : Measurable Z)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀ j₀ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀ j₀ (Nseq i) = 0)
    (hB : μ' {ω | gCoeff ν h k β b (Z ω).den μ₀ j₀ = 0} = 0) :
    TendstoInDistribution (fun i ω => Zφ i ω / Z1 i ω) l
      (fun ω => gCoeff ν h k β b (Z ω).num μ₀ j₀ / gCoeff ν h k β b (Z ω).den μ₀ j₀)
      (fun _ => μ) μ' := by
  have hpair := tendstoInDistribution_pair_normalised ν h k β b hk hβ hb hμ hj XY hXYm Z hXY Nseq
    hN1 hN Zφ Z1 Eφ E1 hZφm hZ1m hdφ hd1 hEφ hE1 hpφ hp1
  have ha : ∀ i, Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀ ≠ 0 := fun i => by
    have h0 : 0 < Nseq i := lt_trans one_pos (hN1 i)
    have hl : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
    positivity
  have hAm : Measurable fun ω => gCoeff ν h k β b (Z ω).num μ₀ j₀ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j₀).comp continuous_num).measurable.comp hZm
  have hBm : Measurable fun ω => gCoeff ν h k β b (Z ω).den μ₀ j₀ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j₀).comp continuous_den).measurable.comp hZm
  exact tendstoInDistribution_div_of_scaled Zφ Z1 _ ha hZφm hZ1m _ _ hAm hBm hpair hB

end Grammar
