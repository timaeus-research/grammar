/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SecondOrderStochastic
import Grammar.IsolatedRemainder

/-!
# Uniform log-weighted isolated remainders for random data (unit 332)

For the multiplicity-one stochastic second-order quotient the two-term remainder is the
log-weighted quantity `log N · (Z/N^{-μ₀} − A)`, which the ordered remainders at natural log degrees
do not control. Here it is obtained from the quantitative global cutoff bound, whose constant is
uniform on norm balls (`gCutoff_bound`): below the cutoff `μ₀ + 1/Q` only the exponent `μ₀`
survives once the predecessor sum at `(μ₀, 0)` vanishes (`absSpectralSum_eq_predSum_add`), so
`|(𝒵(N;x) − A(x) N^{-μ₀}) log N / N^{-μ₀}| ≤ C_R N^{-1/Q}(1 + log N)^{D+1}` for `‖x‖ ≤ R`
(`gInt_isolated_bound`), and for random data with `‖X_ℓ‖` bounded in probability the log-weighted
remainder tends to zero in probability (`tendstoInMeasure_randomOneTerm`), the a.e. predecessor
vanishing being handled by an a.e. variant of the uniform-on-balls lemma. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Below the cutoff `μ₀ + 1/Q` the index set is the predecessor set of `(μ₀, 0)` together with
`(μ₀, 0)` itself. -/
theorem indexSet_eq_insert_predSet {D Q : ℕ} (hQ : 0 < Q) (a : ℕ) :
    indexSet D Q ((a : ℝ) / Q + 1 / Q) =
      insert ((a : ℝ) / Q, 0) (predSet D Q ((a : ℝ) / Q) 0) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / Q := by positivity
  ext p
  simp only [Finset.mem_insert, mem_predSet_iff, mem_indexSet_iff, mem_latticeBelow_iff hQ,
    precedes]
  constructor
  · rintro ⟨⟨⟨m, hm⟩, hlt⟩, hp2⟩
    have hlt' : (m : ℝ) < a + 1 := by
      rw [hm, ← add_div, div_lt_div_iff_of_pos_right hQ'] at hlt
      exact hlt
    have hma : m ≤ a := by
      have : m < a + 1 := by exact_mod_cast hlt'
      omega
    rcases Nat.lt_or_ge m a with hma' | hma'
    · have hlt2 : p.1 < (a : ℝ) / Q := by
        rw [hm, div_lt_div_iff_of_pos_right hQ']
        exact_mod_cast hma'
      exact Or.inr ⟨⟨⟨⟨m, hm⟩, by linarith⟩, hp2⟩, Or.inl hlt2⟩
    · have hmeq : m = a := le_antisymm hma hma'
      have hp1 : p.1 = (a : ℝ) / Q := by rw [hm, hmeq]
      rcases Nat.eq_zero_or_pos p.2 with h0 | h0
      · exact Or.inl (Prod.ext hp1 h0)
      · exact Or.inr ⟨⟨⟨⟨m, hm⟩, by rw [hp1]; linarith⟩, hp2⟩, Or.inr ⟨hp1, h0⟩⟩
  · rintro (rfl | ⟨⟨⟨⟨m, hm⟩, -⟩, hp2⟩, hprec⟩)
    · exact ⟨⟨⟨a, rfl⟩, by linarith⟩, by omega⟩
    · refine ⟨⟨⟨m, hm⟩, ?_⟩, hp2⟩
      rcases hprec with hlt | ⟨heq, -⟩
      · linarith
      · rw [heq]
        linarith

/-- **Spectral sum below `μ₀ + 1/Q`** `=` predecessor sum at `(μ₀, 0)` `+` the `(μ₀, 0)` term. -/
theorem absSpectralSum_eq_predSum_add {D Q : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) (a : ℕ) (N : ℝ) :
    absSpectralSum Q D c ((a : ℝ) / Q + 1 / Q) N =
      absPredSum Q D c ((a : ℝ) / Q) 0 N + c ((a : ℝ) / Q) 0 * N ^ (-((a : ℝ) / Q)) := by
  rw [absSpectralSum_eq_sum_indexSet, indexSet_eq_insert_predSet hQ a, Finset.sum_insert]
  · unfold absPredSum absTerm
    simp only [pow_zero, mul_one]
    ring
  · rw [mem_predSet_iff]
    rintro ⟨-, h⟩
    simp [precedes] at h

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **Uniform log-weighted isolated remainder on norm balls**: for `‖x‖ ≤ R`, `N ≥ 1` and a
vanishing predecessor sum at `(μ₀, 0)`,
`|(𝒵(N;x) − A(x) N^{-μ₀}) log N / N^{-μ₀}| ≤ C_R N^{-1/Q}(1 + log N)^{D+1}`. -/
theorem gInt_isolated_bound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) {a : ℕ} {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) {N : ℝ} (hN : 1 ≤ N)
    (hp : absPredSum (commonQ k) (commonD n) (gCoeff ν h k β (fun _ => 1) x)
      ((a : ℝ) / commonQ k) 0 N = 0) :
    |(gInt ν h k β (fun _ => 1) x N - gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) 0 *
        N ^ (-((a : ℝ) / commonQ k))) * Real.log N / N ^ (-((a : ℝ) / commonQ k))| ≤
      gCutoffConst ν h k β (fun _ => 1) ((a : ℝ) / commonQ k + 1 / commonQ k) R *
        (N ^ (-(1 / (commonQ k : ℝ))) * (1 + Real.log N) ^ (commonD n + 1)) := by
  have hQ : 0 < commonQ k := commonQ_pos k hk
  have hQ' : (0 : ℝ) < commonQ k := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / commonQ k := by positivity
  have hN0 : 0 < N := by linarith
  have hb := gCutoff_bound ν h k β (fun _ => 1) hk hβ (fun _ => one_pos)
    (L := (a : ℝ) / commonQ k + 1 / commonQ k) (by positivity) hN
    (fun I => by rw [boxScale_one]; exact hN) hx
  rw [absSpectralSum_eq_predSum_add hQ _ a N, hp, zero_add] at hb
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hpow : 0 < N ^ (-((a : ℝ) / commonQ k)) := Real.rpow_pos_of_pos hN0 _
  have hsplit : N ^ (-((a : ℝ) / commonQ k + 1 / commonQ k)) =
      N ^ (-((a : ℝ) / commonQ k)) * N ^ (-(1 / (commonQ k : ℝ))) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hL1 : Real.log N ≤ 1 + Real.log N := by linarith
  rw [abs_div, abs_of_pos hpow, abs_mul, abs_of_nonneg hlog, div_le_iff₀ hpow]
  calc |gInt ν h k β (fun _ => 1) x N - gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) 0 *
        N ^ (-((a : ℝ) / commonQ k))| * Real.log N
      ≤ gCutoffConst ν h k β (fun _ => 1) ((a : ℝ) / commonQ k + 1 / commonQ k) R *
        (N ^ (-((a : ℝ) / commonQ k + 1 / commonQ k)) * (1 + Real.log N) ^ commonD n) *
        (1 + Real.log N) := mul_le_mul hb hL1 hlog (le_trans (abs_nonneg _) hb)
    _ = _ := by
        rw [hsplit, pow_succ]
        ring

/-- A.e. variant of the uniform-on-balls lemma: bounds holding a.e. on `{‖X n‖ ≤ M}`. -/
theorem tendstoInMeasure_zero_of_uniform_on_balls_ae {ι Ω E G : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : ι → Ω → G) (X : ι → Ω → E)
    (hf : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ M → ‖f n ω‖ ≤ ε)
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  filter_upwards [hev, hf M hM (ε / 2) (half_pos hε)] with n hn hfn
  refine le_trans (measure_mono_ae ?_) hn
  filter_upwards [hfn] with ω hω hmem
  have hmem' : ε ≤ ‖f n ω - 0‖ := hmem
  rw [sub_zero] at hmem'
  by_contra hcon
  have hcon' : ¬ (M < ‖X n ω‖) := hcon
  have := hω (not_lt.1 hcon')
  linarith

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- **The log-weighted one-term remainder of random data vanishes in probability**: with a.e.
vanishing predecessor sum at `(μ₀, 0)` and a residual `E log N / N^{-μ₀} → 0` in probability,
`log N · (Z_ℓ/N^{-μ₀} − A_ℓ) → 0` in probability. -/
theorem tendstoInMeasure_randomOneTerm (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) {μ₀ : ℝ} {a : ℕ}
    (hμ : μ₀ = (a : ℝ) / commonQ k) (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i)
    (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ)
    (hdecomp : ∀ i, ∀ᵐ ω ∂μ, Zg i ω = gInt ν h k β (fun _ => 1) (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω * Real.log (Nseq i) / Nseq i ^ (-μ₀)) l
      (fun _ => 0))
    (hp : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β (fun _ => 1) (X i ω)) μ₀ 0 (Nseq i) = 0) :
    TendstoInMeasure μ (fun i ω => Real.log (Nseq i) * (Zg i ω / Nseq i ^ (-μ₀) -
      gCoeff ν h k β (fun _ => 1) (X i ω) μ₀ 0)) l (fun _ => 0) := by
  have hQ : 0 < commonQ k := commonQ_pos k hk
  have hQ' : (0 : ℝ) < commonQ k := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / commonQ k := by positivity
  -- the isolated part tends to zero in probability
  have hiso : TendstoInMeasure μ (fun i ω => (gInt ν h k β (fun _ => 1) (X i ω) (Nseq i) -
      gCoeff ν h k β (fun _ => 1) (X i ω) μ₀ 0 * Nseq i ^ (-μ₀)) * Real.log (Nseq i) /
      Nseq i ^ (-μ₀)) l (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls_ae _ X (fun R hR ε hε => ?_)
      (normBounded_of_tendstoInDistribution' X Z hX)
    have hrate : Tendsto (fun N : ℝ => gCutoffConst ν h k β (fun _ => 1) (μ₀ + 1 / commonQ k) R *
        (N ^ (-(1 / (commonQ k : ℝ))) * (1 + Real.log N) ^ (commonD n + 1))) atTop (𝓝 0) := by
      have := (tendsto_cutoff_ratio (commonD n + 1) (μ := 0) (L := 1 / commonQ k) h1Q).const_mul
        (gCutoffConst ν h k β (fun _ => 1) (μ₀ + 1 / commonQ k) R)
      rw [mul_zero] at this
      refine this.congr' (Eventually.of_forall fun N => ?_)
      simp
    filter_upwards [hN.eventually (hrate.eventually (gt_mem_nhds hε)),
      hN.eventually (eventually_ge_atTop (1 : ℝ))] with i hi hN1' 
    filter_upwards [hp i] with ω hpω hω
    subst hμ
    have := gInt_isolated_bound ν h k β hk hβ (a := a) (R := R) hω hN1' hpω
    rw [Real.norm_eq_abs]
    exact this.trans hi.le
  have hsum := tendstoInMeasure_add_zero hiso hE
  refine hsum.congr' (Eventually.of_forall fun i => ?_) (Eventually.of_forall fun _ => rfl)
  filter_upwards [hdecomp i] with ω hd
  have hN0 : 0 < Nseq i := by linarith [hN1 i]
  have hpow : Nseq i ^ (-μ₀) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [hd]
  field_simp
  ring

end Grammar
