/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothAmplitudeFamily
import Grammar.SmoothTimeRescale

/-!
# Integrating smooth amplitude families over a compact base (consult #117 §2.5, §3.2; U4d–U4e)

★ `cutoffExpansion_integral_of_uniform`: a family of cutoff expansions with constants uniform in
the parameter integrates, against a finite base measure, to a cutoff expansion with the
integrated coefficients (finite-sum/integral interchange and `|∫ E_s| ≤ ν(S) sup |E_s|`). Applied
to a `SmoothAmplitudeFamily` on a compact base this gives ★★ `cutoffExpansion_integral`:
`N ↦ ∫_S ∫_{(0,b]^d} F_s(v) v^h e^{−Nβ v^{2k}} dv dν(s)` is a `CutoffExpansion` on the lattice
`(2∏k)⁻¹ℕ` with degree `≤ d − 1` and coefficients `∫_S smoothCoeff (F_s) dν`, and with a
continuous positive TANGENTIAL PHASE UNIT `β(s)` (★★ `cutoffExpansion_integral_beta`): the unit is
absorbed by rescaling the Laplace parameter, `smoothIntegral F h k β b N = smoothIntegral F h k 1 b
(βN)`, and the coefficients transform by `scaleCoeff` (log-degree mixing), so no uniformity of the
box engine in `β` is needed. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### The generic integration lemma -/

/-- Integrating coefficient systems commutes with the finite spectral sums. -/
theorem absSpectralSum_integral {S : Type*} [MeasurableSpace S] (ν : Measure S) {Q D : ℕ}
    {c : S → ℝ → ℕ → ℝ} (hc : ∀ μ q, Integrable (fun s => c s μ q) ν) (L N : ℝ) :
    absSpectralSum Q D (fun μ q => ∫ s, c s μ q ∂ν) L N =
      ∫ s, absSpectralSum Q D (c s) L N ∂ν := by
  unfold absSpectralSum
  rw [integral_finsetSum _ fun μ _ => (integrable_finsetSum _ fun j _ =>
    (hc μ j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_finsetSum _ fun j _ => (hc μ j).mul_const _]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]

theorem integrable_absSpectralSum {S : Type*} [MeasurableSpace S] (ν : Measure S) {Q D : ℕ}
    {c : S → ℝ → ℕ → ℝ} (hc : ∀ μ q, Integrable (fun s => c s μ q) ν) (L N : ℝ) :
    Integrable (fun s => absSpectralSum Q D (c s) L N) ν := by
  unfold absSpectralSum
  exact integrable_finsetSum _ fun μ _ =>
    (integrable_finsetSum _ fun j _ => (hc μ j).mul_const _).const_mul _

/-- ★ **Integrating a uniformly bounded family of cutoff expansions.** -/
theorem cutoffExpansion_integral_of_uniform {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [IsFiniteMeasure ν] {Q D : ℕ} {Z : S → ℝ → ℝ} {c : S → ℝ → ℕ → ℝ}
    (hZ : ∀ N : ℝ, 1 ≤ N → Integrable (fun s => Z s N) ν)
    (hc : ∀ μ q, Integrable (fun s => c s μ q) ν)
    (hunif : ∀ L : ℝ, 0 < L → ∃ C N₀ : ℝ, 1 ≤ N₀ ∧ ∀ s, ∀ N : ℝ, N₀ ≤ N →
      |Z s N - absSpectralSum Q D (c s) L N| ≤ C * (N ^ (-L) * (1 + log N) ^ D)) :
    CutoffExpansion Q D (fun N => ∫ s, Z s N ∂ν) (fun μ q => ∫ s, c s μ q ∂ν) := by
  intro L hL
  obtain ⟨C, N₀, hN₀, hC⟩ := hunif L hL
  refine ⟨C * ν.real univ, ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN1 : 1 ≤ N := hN₀.trans hN
  rw [absSpectralSum_integral ν hc, ← integral_sub (hZ N hN1) (integrable_absSpectralSum ν hc L N)]
  have hbound : ∀ᵐ s ∂ν, ‖Z s N - absSpectralSum Q D (c s) L N‖ ≤
      C * (N ^ (-L) * (1 + log N) ^ D) :=
    ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hC s N hN
  have := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

/-! ### Smooth amplitude families over a compact base -/

variable {d : ℕ} {S : Type*} [TopologicalSpace S] [CompactSpace S] [FirstCountableTopology S]
  [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν] {b : ℝ}
  (F : SmoothAmplitudeFamily S d b)

omit [FirstCountableTopology S] in
/-- Continuous functions on a compact space are integrable for a finite measure. -/
theorem integrable_of_continuous_compactSpace {f : S → ℝ} (hf : Continuous f) :
    Integrable f ν := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.mono' (integrable_const B) hf.measurable.aestronglyMeasurable
    (ae_of_all _ fun s => hB s (Set.mem_univ s))

variable {h k : Fin d → ℕ}

/-- The integral of the family over the base: `∫_S ∫_{(0,b]^d} F_s v^h e^{−Nβ(s) v^{2k}} dν`. -/
noncomputable def familyIntegral (h k : Fin d → ℕ) (βf : S → ℝ) (b N : ℝ) : ℝ :=
  ∫ s, smoothIntegral (F s) h k (βf s) b N ∂ν

/-- The integrated canonical coefficients. -/
noncomputable def familyCoeff (h k : Fin d → ℕ) (βf : S → ℝ) (b : ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  ∫ s, smoothCoeff (F s) h k (βf s) b μ q ∂ν

/-- ★★ **The integrated expansion with a constant phase scale.** -/
theorem cutoffExpansion_integral (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (familyIntegral ν F h k (fun _ => β) b)
      (familyCoeff ν F h k (fun _ => β) b) := by
  refine cutoffExpansion_integral_of_uniform ν (fun N hN => ?_) (fun μ q => ?_) fun L _ => ?_
  · exact integrable_of_continuous_compactSpace ν
      (F.continuous_smoothIntegral hβ.le (by linarith : (0 : ℝ) ≤ N))
  · exact integrable_of_continuous_compactSpace ν (F.continuous_smoothCoeff hk hb μ q)
  · obtain ⟨C, hC⟩ := F.uniform_cutoff hk hβ hb L
    exact ⟨C, 1, le_rfl, hC⟩

/-! ### A continuous positive tangential phase unit -/

omit [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- The rescaled coefficients are continuous in the parameter. -/
theorem continuous_smoothCoeff_beta (hk : ∀ i, 0 < k i) (hb : 0 < b) {βf : S → ℝ}
    (hβ : Continuous βf) (hβpos : ∀ s, 0 < βf s) (μ : ℝ) (q : ℕ) :
    Continuous fun s => smoothCoeff (F s) h k (βf s) b μ q := by
  have heq : ∀ s, smoothCoeff (F s) h k (βf s) b μ q =
      scaleCoeff (d - 1) (βf s) (smoothCoeff (F s) h k 1 b) μ q := fun s =>
    smoothCoeff_beta_eq_scaleCoeff (F.smooth s) hk (hβpos s) hb μ q
  simp only [heq, scaleCoeff]
  refine (hβ.rpow_const fun s => Or.inl (hβpos s).ne').mul
    (continuous_finsetSum _ fun j _ => ((F.continuous_smoothCoeff hk hb μ j).mul
      continuous_const).mul ((hβ.log fun s => (hβpos s).ne').pow _))

/-- `1 + log (βN) ≤ (1 + |log β|)(1 + log N)` for `N ≥ 1`, `β > 0`. -/
theorem one_add_log_mul_le' {β N : ℝ} (hβ : 0 < β) (hN : 1 ≤ N) :
    1 + log (β * N) ≤ (1 + |log β|) * (1 + log N) := by
  rw [Real.log_mul hβ.ne' (by linarith)]
  have h1 := log_nonneg hN
  have h2 := le_abs_self (log β)
  have h3 := abs_nonneg (log β)
  nlinarith

/-- ★★ **The integrated expansion with a continuous positive tangential phase unit `β(s)`**:
the unit is absorbed by rescaling the Laplace parameter, the coefficients by `scaleCoeff`. -/
theorem cutoffExpansion_integral_beta (hk : ∀ i, 0 < k i) (hb : 0 < b) {βf : S → ℝ}
    (hβ : Continuous βf) (hβpos : ∀ s, 0 < βf s) :
    CutoffExpansion (Qamb k) (d - 1) (familyIntegral ν F h k βf b) (familyCoeff ν F h k βf b) := by
  -- bounds on the unit
  obtain ⟨β₁, hβ₁⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn hβ.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn
    (hβ.inv₀ fun s => (hβpos s).ne').continuousOn
  obtain ⟨Lg, hLg⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn
    (hβ.log fun s => (hβpos s).ne').continuousOn
  have hβle : ∀ s, βf s ≤ β₁ := fun s => (le_abs_self _).trans (by
    have := hβ₁ s (Set.mem_univ s); rwa [Real.norm_eq_abs] at this)
  have hβinv : ∀ s, (βf s)⁻¹ ≤ B := fun s => (le_abs_self _).trans (by
    have := hB s (Set.mem_univ s); rwa [Real.norm_eq_abs] at this)
  have hlogle : ∀ s, |log (βf s)| ≤ Lg := fun s => by
    have := hLg s (Set.mem_univ s); rwa [Real.norm_eq_abs] at this
  refine cutoffExpansion_integral_of_uniform ν (fun N hN => ?_) (fun μ q => ?_) fun L hL => ?_
  · exact integrable_of_continuous_compactSpace ν
      (F.continuous_smoothIntegral_beta hβ (fun s => (hβpos s).le) (by linarith : (0 : ℝ) ≤ N))
  · exact integrable_of_continuous_compactSpace ν (continuous_smoothCoeff_beta F hk hb hβ hβpos μ q)
  · obtain ⟨C, hC⟩ := F.uniform_cutoff hk one_pos hb L
    refine ⟨C * B ^ L * (1 + Lg) ^ (d - 1), max 1 B, le_max_left _ _, fun s N hN => ?_⟩
    have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hNB : B ≤ N := (le_max_right _ _).trans hN
    have hβs := hβpos s
    have hβN : 1 ≤ βf s * N := by
      have h1 : (βf s)⁻¹ ≤ N := (hβinv s).trans hNB
      calc (1 : ℝ) = βf s * (βf s)⁻¹ := (mul_inv_cancel₀ hβs.ne').symm
        _ ≤ βf s * N := mul_le_mul_of_nonneg_left h1 hβs.le
    have hC0 : 0 ≤ C := by
      have := hC s 1 le_rfl
      simp only [Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] at this
      exact (abs_nonneg _).trans this
    have hkey := hC s (βf s * N) hβN
    have hZ : smoothIntegral (F s) h k (βf s) b N = smoothIntegral (F s) h k 1 b (βf s * N) :=
      smoothIntegral_beta_eq _ _ _ _ _ _
    have hcoef : absSpectralSum (Qamb k) (d - 1) (smoothCoeff (F s) h k (βf s) b) L N =
        absSpectralSum (Qamb k) (d - 1) (smoothCoeff (F s) h k 1 b) L (βf s * N) := by
      rw [absSpectralSum_mul_pos _ L hβs (by linarith)]
      unfold absSpectralSum
      refine Finset.sum_congr rfl fun μ _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smoothCoeff_beta_eq_scaleCoeff (F.smooth s) hk hβs hb]
    rw [hZ, hcoef]
    refine hkey.trans ?_
    have hrp : (βf s * N) ^ (-L) = (βf s)⁻¹ ^ L * N ^ (-L) := by
      rw [Real.mul_rpow hβs.le (by linarith), Real.rpow_neg hβs.le, ← Real.inv_rpow hβs.le]
    have hB0 : 0 ≤ B := (inv_pos.2 hβs).le.trans (hβinv s)
    have h1 : (βf s)⁻¹ ^ L ≤ B ^ L := Real.rpow_le_rpow (inv_pos.2 hβs).le (hβinv s) hL.le
    have hlogN := log_nonneg hN1
    have hlogβN := log_nonneg hβN
    have h2 : (1 + log (βf s * N)) ^ (d - 1) ≤ (1 + Lg) ^ (d - 1) * (1 + log N) ^ (d - 1) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by linarith) ?_ _
      refine (one_add_log_mul_le' hβs hN1).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hlogle s]) (by linarith)
    calc C * ((βf s * N) ^ (-L) * (1 + log (βf s * N)) ^ (d - 1))
        ≤ C * ((B ^ L * N ^ (-L)) * ((1 + Lg) ^ (d - 1) * (1 + log N) ^ (d - 1))) := by
          rw [hrp]
          refine mul_le_mul_of_nonneg_left ?_ hC0
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (rpow_nonneg (by linarith) _)) h2
            (pow_nonneg (by linarith) _)
            (mul_nonneg (rpow_nonneg hB0 _) (rpow_nonneg (by linarith) _))
      _ = _ := by ring

end SmoothEngine

end Grammar
