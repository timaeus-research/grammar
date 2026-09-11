/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PositiveScalarCoefficient

/-!
# Unrestricted certificate ratios and signed symmetric moments

Unit 5 of consult #77 (`tide-log/gpt6_bigpicture_v77.md`). The certificate ratio of CCXXXV required
the log degrees to be ordered (`k₂ ≤ k₁`), which excludes ordinary normalised moments whose log
degree DROPS under the exponent shift (e.g. `h = (0,0)`, `k = (1,1)`, insertion `u₁²`: the
normalised moment is of order `1/log N`). The repair is at the limit level: for two certificates
with `c₂ ≠ 0`, `(Z₁/Z₂) / (s_{λ₁,k₁}/s_{λ₂,k₂}) → c₁/c₂` with no ordering
(`HasLeadingTerm.tendsto_div_ratio`), and when `k₁ ≤ k₂` the quotient multiplied by
`N^{λ₁−λ₂}(log N)^{k₂−k₁}` converges to `c₁/c₂` (`HasLeadingTerm.tendsto_div_mul_log`).

**Signed symmetric moments**: on the two-sided box the moment `∫ A u^α ∏|u|^h e^{−Nq∏u^{2k}}` is the
sum over orthants of the positive-cube moment kernels of the reflected amplitudes with the
**orthant multiplier** `∏_j sgn(σ_j)^{α_j}` (`symMomentKernel_eq_sum`), hence has a leading-term
certificate at the shifted pair with coefficient `∑_σ (∏_j sgn(σ_j)^{α_j}) c_σ`
(`hasLeadingTerm_symMomentKernel`) — a signed sum that CAN cancel (an odd insertion on a symmetric
amplitude gives coefficient zero); a zero certificate does not identify the next nonzero term.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Unrestricted certificate ratios -/

section Ratio

variable {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ lam₁ lam₂ : ℝ} {k₁ k₂ : ℕ}

/-- **The unrestricted certificate ratio**: `(Z₁/Z₂) / (s₁/s₂) → c₁/c₂`, no ordering of the log
degrees. -/
theorem HasLeadingTerm.tendsto_div_ratio (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
    Tendsto (fun N => (Z₁ N / Z₂ N) / (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N)) atTop
      (𝓝 (c₁ / c₂)) := by
  have h := Tendsto.div h₁ h₂ hc₂
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only [Pi.div_apply]
  rw [div_div_div_comm]

theorem powLogScale_div_powLogScale_of_le {N : ℝ} (hN : 1 < N) (hk : k₁ ≤ k₂) :
    powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N =
      (N ^ (lam₁ - lam₂) * Real.log N ^ (k₂ - k₁))⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  unfold powLogScale
  rw [mul_div_mul_comm, ← Real.rpow_sub hN0, show -lam₁ - -lam₂ = -(lam₁ - lam₂) by ring,
    Real.rpow_neg hN0.le, mul_inv, pow_sub₀ _ hlog hk, mul_inv, inv_inv, div_eq_mul_inv,
    mul_comm (Real.log N ^ k₂)⁻¹]

/-- **The dropping-log-degree case**: for `k₁ ≤ k₂`,
`(Z₁/Z₂) · N^{λ₁−λ₂} (log N)^{k₂−k₁} → c₁/c₂`. -/
theorem HasLeadingTerm.tendsto_div_mul_log (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) (hk : k₁ ≤ k₂) :
    Tendsto (fun N => Z₁ N / Z₂ N * (N ^ (lam₁ - lam₂) * Real.log N ^ (k₂ - k₁))) atTop
      (𝓝 (c₁ / c₂)) := by
  refine (h₁.tendsto_div_ratio h₂ hc₂).congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  rw [powLogScale_div_powLogScale_of_le hN hk, div_inv_eq_mul]

end Ratio

/-! ### Signed symmetric moments -/

section Symmetric

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (b : ℝ) {t : ℕ} (q : (Fin t → ℝ) → ℝ)
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **The signed symmetric moment kernel**
`∫_{(−b,b]^{n+1}} A(z,u) u^α ∏|u_i|^{h_i} e^{−Nq∏u^{2k}}`. -/
noncomputable def symMomentKernel (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  symScalarKernel n h k b q (fun z u => A z u * ∏ i, u i ^ α i) z N

/-- The orthant multiplier `∏_j sgn(σ_j)^{α_j}`. -/
def orthantSign (α : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → Bool) : ℝ := ∏ i, sgn (σ i) ^ α i

theorem reflect_pow_prod (σ : Fin (n + 1) → Bool) (α : Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ) :
    ∏ i, reflect σ u i ^ α i = orthantSign n α σ * ∏ i, u i ^ α i := by
  unfold orthantSign
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by simp only [reflect, mul_pow]

/-- A constant factor in the amplitude comes out of the scalar-unit kernel. -/
theorem scalarBoxKernel_const_mul (c : ℝ) (z : Fin t → ℝ) (N : ℝ) :
    scalarBoxKernel n h k b q (fun z u => c * A z u) z N = c * scalarBoxKernel n h k b q A z N := by
  unfold scalarBoxKernel boxKernel origPhaseIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  ring

/-- **Orthant assembly of the signed moment**: the symmetric moment kernel is the signed sum of the
positive-cube moment kernels of the reflected amplitudes. -/
theorem symMomentKernel_eq_sum (hb : 0 < b) (hA : Continuous (Function.uncurry A))
    (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) (N : ℝ) :
    symMomentKernel n h k b q A α z N = ∑ σ : Fin (n + 1) → Bool, orthantSign n α σ *
      scalarBoxKernel n h k b q (fun z u => reflectAmp n A σ z u * ∏ i, u i ^ α i) z N := by
  unfold symMomentKernel
  rw [symScalarKernel_eq_sum n h k b q _ hb (continuous_monomialAmp n A hA α)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← scalarBoxKernel_const_mul]
  congr 1
  funext z u
  simp only [reflectAmp, reflect_pow_prod]
  ring

variable {n h k b}

/-- **The certificate of the signed symmetric moment** at the shifted pair, with the signed sum of
the orthant coefficients (which may cancel). -/
theorem hasLeadingTerm_symMomentKernel (hk : ∀ i, 0 < k i) (hb : 0 < b)
    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) {z : Fin t → ℝ} (hqz : 0 < q z) :
    HasLeadingTerm (symMomentKernel n h k b q A α z)
      (∑ σ : Fin (n + 1) → Bool, orthantSign n α σ *
        scalarBoxFaceCoeff n (fun i => h i + α i) k b q (reflectAmp n A σ)
          (minRatio (fun i => h i + α i) k) z)
      (minRatio (fun i => h i + α i) k)
      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) := by
  have hcell : ∀ σ : Fin (n + 1) → Bool, HasLeadingTerm
      (fun N => orthantSign n α σ *
        scalarBoxKernel n h k b q (fun z u => reflectAmp n A σ z u * ∏ i, u i ^ α i) z N)
      (orthantSign n α σ * scalarBoxFaceCoeff n (fun i => h i + α i) k b q (reflectAmp n A σ)
        (minRatio (fun i => h i + α i) k) z)
      (minRatio (fun i => h i + α i) k)
      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) := by
    intro σ
    refine HasLeadingTerm.const_mul ?_ _
    have hcert := hasLeadingTerm_scalarBoxKernel q (reflectAmp n A σ) hk hb
      (minRatio_le (fun i => h i + α i) k) (exists_ratioExp_eq_minRatio (fun i => h i + α i) k)
      (continuous_reflectAmp n A hA σ) hqz
    refine hcert.congr' (Eventually.of_forall fun N => ?_)
    exact scalarBoxKernel_shift n h k b (reflectAmp n A σ) q α z N
  have hsum := HasLeadingTerm.sum Finset.univ fun σ _ => hcell σ
  refine hsum.congr' (Eventually.of_forall fun N => ?_)
  exact (symMomentKernel_eq_sum n h k b q A hb hA α z N).symm

end Symmetric

end Grammar
