/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FieldJetUniform
import Grammar.EmpiricalUniform
import Grammar.EmpiricalBoxScaling

/-!
# The cube remainder, uniform on jet balls

For a cube `[0,b]^d`, a smooth amplitude `η` and a cutoff `U`, there is ONE remainder constant `K`
and a threshold `N₀` such that for every smooth field `ζ` whose jets of the required order are
bounded by `B` on the closed cube and every `N ≥ N₀`,
`|empIntegralRect η ζ h k b N − absSpectralSum (Qamb k) (d−1) (empCoeffRect η ζ h k b) U N|
  ≤ K · N^{−U} (1 + log N)^{d−1}`.
This is the unit-box uniform expansion (`emp_cutoffExpansion_uniform`) transported by the exact
dilation `empIntegralRect_eq`, with the field-family jet bound made uniform on bounded jets
(`fieldJetBound_of_jetBoundOn`) and the jets of `ζ ∘ diag b` controlled by those of `ζ`
(consult #152, deliverable 2).
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The dilation `diag (fun _ => b)` is the continuous linear map `b • id`. -/
theorem diag_const_eq (b : ℝ) :
    diag (fun _ : Fin d => b) = ⇑(b • ContinuousLinearMap.id ℝ (Fin d → ℝ)) := by
  funext v
  have h1 : diag (fun _ : Fin d => b) v = b • v := funext fun _ => rfl
  rw [h1]
  simp

theorem diag_const_mem_closedBox {b : ℝ} (hb : 0 ≤ b) {x : Fin d → ℝ} (hx : x ∈ closedBox d 1) :
    diag (fun _ : Fin d => b) x ∈ closedBox d b := by
  rw [mem_closedBox] at hx ⊢
  intro i
  obtain ⟨h0, h1⟩ := hx i
  change b * x i ∈ Set.Icc 0 b
  exact ⟨mul_nonneg hb h0, by simpa using mul_le_mul_of_nonneg_left h1 hb⟩

/-- Jets of the dilated field on the unit box are controlled by the jets of the field on the
cube. -/
theorem jetBoundOn_comp_diag (hζ : ContDiff ℝ ∞ ζ) {b : ℝ} (hb : 0 < b) {P : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hζB : JetBoundOn P (closedBox d b) ζ B) :
    JetBoundOn P (closedBox d 1) (ζ ∘ diag (fun _ : Fin d => b)) ((max 1 b) ^ P * B) := by
  intro r hr x hx
  set g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := b • ContinuousLinearMap.id ℝ (Fin d → ℝ) with hg
  have hgn : ‖g‖ ≤ b := by
    calc ‖g‖ ≤ ‖b‖ * ‖ContinuousLinearMap.id ℝ (Fin d → ℝ)‖ := norm_smul_le _ _
      _ ≤ b * 1 := by
          rw [Real.norm_of_nonneg hb.le]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hb.le
      _ = b := mul_one b
  rw [diag_const_eq, ← hg,
    ContinuousLinearMap.iteratedFDeriv_comp_right g hζ x (natCast_le_infty r)]
  have hgx : g x ∈ closedBox d b := by
    have := diag_const_mem_closedBox hb.le hx
    rwa [diag_const_eq, ← hg] at this
  calc ‖(iteratedFDeriv ℝ r ζ (g x)).compContinuousLinearMap fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ r ζ (g x)‖ * ∏ _i : Fin r, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * (max 1 b) ^ P := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul (hζB r hr (g x) hgx) ?_ (by positivity) hB
        calc ‖g‖ ^ r ≤ (max 1 b) ^ r :=
              pow_le_pow_left₀ (norm_nonneg _) (hgn.trans (le_max_right _ _)) r
          _ ≤ (max 1 b) ^ P := pow_le_pow_right₀ (le_max_left _ _) hr
    _ = (max 1 b) ^ P * B := mul_comm _ _

/-- ★★ **The cube remainder is uniform on jet balls**: one constant and one threshold for all
smooth fields with jets of the required order bounded by `B` on the closed cube. -/
theorem empRect_remainder_uniform_on_jetBall (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (U : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K N₀ : ℝ, 0 ≤ K ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (∑ i, depthOf h k (max ⌈U⌉₊ (L₀ h)) i) (closedBox d b) ζ B → ∀ N : ℝ, N₀ ≤ N →
        |empIntegralRect η ζ h k (fun _ => b) N -
          absSpectralSum (Qamb k) (d - 1) (empCoeffRect η ζ h k (fun _ => b)) U N| ≤
        K * (N ^ (-U) * (1 + log N) ^ (d - 1)) := by
  set p : Fin d → ℕ := depthOf h k (max ⌈U⌉₊ (L₀ h)) with hp
  set P : ℕ := ∑ i, p i with hP
  set B' : ℝ := (max 1 b) ^ P * B with hB'
  have hB'0 : 0 ≤ B' := by positivity
  set β : ℝ := mono (fun i => 2 * k i) (fun _ : Fin d => b) with hβdef
  have hβ : 0 < β := mono_pos _ fun _ => hb
  set A : ℝ := (∏ _i : Fin d, b) * mono h (fun _ : Fin d => b) with hA
  have hA0 : 0 < A := mul_pos (Finset.prod_pos fun _ _ => hb) (mono_pos _ fun _ => hb)
  have hηD : ContDiff ℝ ∞ (η ∘ diag (fun _ : Fin d => b)) := hη.comp (contDiff_diag _)
  obtain ⟨C, hC0, hC⟩ := fieldJetBound_of_jetBoundOn hηD p (b := 1) hB'0
  obtain ⟨K₀, hK₀0, hK₀⟩ := emp_cutoffExpansion_uniform (h := h) (k := k) hk U B'
  refine ⟨A * C * K₀ * β ^ (-U) * (1 + |log β|) ^ (d - 1), max 1 β⁻¹, by positivity,
    fun ζ hζ hζB N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hβN : 1 ≤ β * N := by
    have : β⁻¹ ≤ N := (le_max_right _ _).trans hN
    calc (1 : ℝ) = β * β⁻¹ := (mul_inv_cancel₀ hβ.ne').symm
      _ ≤ β * N := mul_le_mul_of_nonneg_left this hβ.le
  have hζD : ContDiff ℝ ∞ (ζ ∘ diag (fun _ : Fin d => b)) := hζ.comp (contDiff_diag _)
  have hjet := hC _ hζD (jetBoundOn_comp_diag hζ hb hB hζB)
  have hrem := hK₀ _ _ hηD hζD C hjet (β * N) hβN
  -- the dilation identities
  have hI : empIntegralRect η ζ h k (fun _ => b) N =
      A * empIntegral (η ∘ diag (fun _ : Fin d => b)) (ζ ∘ diag (fun _ : Fin d => b)) h k (β * N) :=
    empIntegralRect_eq η ζ h k (fun _ => hb) N
  have hS : absSpectralSum (Qamb k) (d - 1) (empCoeffRect η ζ h k (fun _ => b)) U N =
      A * absSpectralSum (Qamb k) (d - 1)
        (empCoeff (η ∘ diag (fun _ : Fin d => b)) (ζ ∘ diag (fun _ : Fin d => b)) h k) U
        (β * N) := by
    rw [absSpectralSum_mul_pos _ _ hβ hN0]
    have : empCoeffRect η ζ h k (fun _ => b) = fun μ q => A * scaleCoeff (d - 1) β
        (empCoeff (η ∘ diag (fun _ : Fin d => b)) (ζ ∘ diag (fun _ : Fin d => b)) h k) μ q := rfl
    rw [this, absSpectralSum_const_mul]
  rw [hI, hS, ← mul_sub, abs_mul, abs_of_pos hA0]
  -- the rate at `β N`
  have hlogN : 0 ≤ log N := log_nonneg hN1
  have hlogβN : 0 ≤ 1 + log (β * N) := by
    have := log_nonneg hβN
    linarith
  have hlog : (1 + log (β * N)) ^ (d - 1) ≤ ((1 + |log β|) * (1 + log N)) ^ (d - 1) := by
    refine pow_le_pow_left₀ hlogβN ?_ _
    rw [log_mul hβ.ne' hN0.ne']
    have h1 := le_abs_self (log β)
    have h2 : 0 ≤ |log β| * log N := mul_nonneg (abs_nonneg _) hlogN
    nlinarith
  have hrpow : (β * N) ^ (-U) = β ^ (-U) * N ^ (-U) := Real.mul_rpow hβ.le hN0.le
  calc A * |empIntegral (η ∘ diag fun _ => b) (ζ ∘ diag fun _ => b) h k (β * N) -
        absSpectralSum (Qamb k) (d - 1)
          (empCoeff (η ∘ diag fun _ => b) (ζ ∘ diag fun _ => b) h k) U (β * N)|
      ≤ A * (C * K₀ * ((β * N) ^ (-U) * (1 + log (β * N)) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left hrem hA0.le
    _ ≤ A * (C * K₀ * ((β ^ (-U) * N ^ (-U)) * ((1 + |log β|) * (1 + log N)) ^ (d - 1))) := by
        rw [hrpow]
        gcongr
    _ = A * C * K₀ * β ^ (-U) * (1 + |log β|) ^ (d - 1) * (N ^ (-U) * (1 + log N) ^ (d - 1)) := by
        rw [mul_pow]
        ring

end SmoothEngine

end Grammar
