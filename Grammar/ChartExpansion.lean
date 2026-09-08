/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AbstractExpansion

/-!
# The chart-level Taylor tree as an abstract expansion (Stage S13)

Unit 282 (Astra #34 / review v29, assembly prerequisites). Padding support theorems for the
canonical coefficients — `C_{μ,j} = 0` for `j > n` (`dataBoxCoeff_eq_zero_of_lt`), for `μ` off
the candidate set (`dataBoxCoeff_eq_zero_of_not_candidate`), hence for `μ ∉ Q⁻¹ℕ`
(`dataBoxCoeff_eq_zero_of_not_lattice`), and the same for the integrated coefficients `𝒞_{μ,j}` —
and the **uniform chart cutoff bound in the sample size** (`tanCutoff_bound_N`): for `‖x‖ ≤ R`,
`N ≥ 1`, `N b^{2|k|} ≥ 1`,
`|𝒵(N;x) − ∑_{Λ_L} N^{-μ} ∑_j 𝒞_{μ,j}(x)(log N)^j| ≤ chartCutoffConst · N^{-L}(1+log N)^n`
with `chartCutoffConst n h k β b ν L R = ν(K) b^{|h|+d} dataCutoffConst(R) c^{-L} (1+|log c|)^n`,
`c = b^{2|k|}`. Consequently the integrated chart integral of every tangential datum is a
finite-cutoff expansion on its own lattice `Q⁻¹ℕ = (2∏kᵢ)⁻¹ℕ` with degrees `≤ n`
(`cutoffExpansion_tan`), which is what the chart assembly of the next unit sums.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-! ### Support of the canonical coefficients -/

theorem dataBoxCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) : dataBoxCoeff n h k β b x μ j = 0 := by
  unfold dataBoxCoeff boxCoeff
  have : Finset.Ico j (n + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
  simp [this]

theorem dataBoxCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {μ : ℝ}
    (hμ : ¬ candidateExp h k μ) (j : ℕ) : dataBoxCoeff n h k β b x μ j = 0 := by
  rw [dataBoxCoeff_eq n h k β hb]
  have hz : ∀ q, familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q = 0 := fun q =>
    familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ (absSummable_xiCoord x)
      (absSummable_etaCoord x) hμ q
  simp [hz]

/-- The canonical coefficients vanish off the lattice `(2∏kᵢ)⁻¹ℕ`. -/
theorem dataBoxCoeff_eq_zero_of_not_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ k) (j : ℕ) : dataBoxCoeff n h k β b x μ j = 0 := by
  refine dataBoxCoeff_eq_zero_of_not_candidate n h k hk β hβ hb x (fun hc => ?_) j
  obtain ⟨m, hm⟩ := candidateExp_mem_lattice hk hc
  exact hμ m hm

section Tangential

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

theorem tanCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : TangentialData K (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) :
    tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_lt n h k β b _ μ hj]

theorem tanCoeff_eq_zero_of_not_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ k) (j : ℕ) : tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_not_lattice n h k hk β hβ hb _ hμ j]

/-! ### The chart cutoff bound in the sample size -/

/-- The chart cutoff constant in the sample size: `ν(K) b^{|h|+d} dataCutoffConst(R) c^{-L}
(1+|log c|)^n`, `c = b^{2|k|}`. -/
noncomputable def chartCutoffConst (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (L R : ℝ) : ℝ :=
  (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
    ((b ^ (2 * ∑ i, k i)) ^ (-L) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n)

theorem chartCutoffConst_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {b : ℝ}
    (hb : 0 < b) (L : ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ chartCutoffConst ν n h k β b L R := by
  unfold chartCutoffConst
  have h1 := dataCutoffConst_nonneg n k β hβ L hR
  have h2 : 0 ≤ (b ^ (2 * ∑ i, k i)) ^ (-L) := Real.rpow_nonneg (by positivity) _
  have h3 := ENNReal.toReal_nonneg (a := ν univ)
  positivity

/-- **The uniform chart cutoff bound in the sample size**: for `‖x‖ ≤ R`, `N ≥ 1`,
`N b^{2|k|} ≥ 1`, `L > 0`. -/
theorem tanCutoff_bound_N (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 1 ≤ N)
    (hN' : 1 ≤ boxScale k b N) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) :
    |tanIntegral ν n h k β N b x - absSpectralSum (latticeQ k) n (tanCoeff ν n h k β b x) L N| ≤
      chartCutoffConst ν n h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have hN0 : 0 < N := by linarith
  have hcut := tanTaylorTree_cutoff_bound ν n h k hk β hβ hL hb hN0 hN' hx
  unfold absSpectralSum
  refine hcut.trans ?_
  unfold chartCutoffConst
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  have hbs : boxScale k b N = N * c := by unfold boxScale; rw [hc]
  have hK0 : 0 ≤ (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) :=
    mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by positivity) (dataCutoffConst_nonneg n k β hβ L ((norm_nonneg x).trans hx)))
  have h1 : boxScale k b N ^ (-L) = N ^ (-L) * c ^ (-L) := by
    rw [hbs, Real.mul_rpow hN0.le hc0.le]
  have h2 : (1 + Real.log (boxScale k b N)) ^ n ≤
      (1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n := by
    rw [hbs, ← mul_pow]
    exact pow_le_pow_left₀ (by have := Real.log_nonneg (show 1 ≤ N * c by rwa [← hbs]); linarith)
      (one_add_log_mul_le hN hc0) n
  have hr0 : 0 ≤ N ^ (-L) := Real.rpow_nonneg hN0.le _
  have hcr0 : 0 ≤ c ^ (-L) := Real.rpow_nonneg hc0.le _
  calc (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n))
      = (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by ring
    _ ≤ (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
        (N ^ (-L) * c ^ (-L) * ((1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n)) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hcr0)) hK0
    _ = _ := by ring

/-- **Every chart integral is a finite-cutoff expansion** on the chart lattice with degrees `≤ n`,
with coefficients the integrated canonical coefficients. -/
theorem cutoffExpansion_tan (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) :
    CutoffExpansion (latticeQ k) n (fun N => tanIntegral ν n h k β N b x)
      (tanCoeff ν n h k β b x) := by
  intro L hL
  refine ⟨chartCutoffConst ν n h k β b L ‖x‖, ?_⟩
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / c)] with N hN1 hNc
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  exact tanCutoff_bound_N ν n h k hk β hβ hL hb hN1 hscale le_rfl

end Tangential

end Grammar
