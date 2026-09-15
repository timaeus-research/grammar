/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.JetCloseness
import Grammar.EmpiricalRectReplacement

/-!
# Continuity of the cube replacement rule in the field (§20, consult #144 unit B)

For a fixed amplitude `η` vanishing near the deep set of the cube (relative to the closed box),
the empirical top coefficient `empCoeffRect η ζ h k b μ (c−1)` depends continuously on the field
`ζ` for `C^{|p|}` convergence on the closed box, `|p| = Σ(2kᵢ·cutoffOf h μ − hᵢ)` the canonical
depth of the population coefficient at `μ` (★★★ `tendsto_empCoeffRect_top`). Route: the cube
replacement rule turns the coefficient into the population coefficient of `η·S_μ(ζ)/Γ(μ)`
(`empCoeffRect_top_eq_smoothCoeff`); the replaced amplitudes are `C^{|p|}`-close when the fields
are (`jetClose_replaced`: composition with the smooth fluctuation function `S_μ`, product with the
fixed factor `η`, scalar `1/Γ(μ)`); the population coefficient is continuous for that closeness
(`tendsto_smoothCoeff_of_jetClose`). Deterministic and sequential; no wall agreement, no random
field. Zero `sorry`/`axiom`.
-/

open Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The replaced amplitude `η · S_μ(ζ) / Γ(μ)` as a scalar multiple of a product. -/
theorem replaced_eq_smul (η ζ : (Fin d → ℝ) → ℝ) (μ : ℝ) :
    (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) =
      fun v => (Real.Gamma μ)⁻¹ • (η v * (fluctuation 1 μ ∘ ζ) v) := by
  funext v
  rw [smul_eq_mul, div_eq_inv_mul]
  rfl

/-- ★★ **The replaced amplitudes are `C^R`-close when the fields are**: for `η` smooth with jets
bounded on the closed box and a jet bound `B` of the limit field, there is `C` with
`JetClose R [0,b]^d ζ₁ ζ₂ ε → JetClose R [0,b]^d (η S_μ(ζ₁)/Γ) (η S_μ(ζ₂)/Γ) (C ε)` for `ε ≤ 1`. -/
theorem exists_jetClose_replaced (hη : ContDiff ℝ ∞ η) {μ : ℝ} (hμ : 0 < μ) (R : ℕ) (b : ℝ)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn R (closedBox d b) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ 1 →
      JetClose R (closedBox d b) ζ₁ ζ₂ ε →
      JetClose R (closedBox d b) (fun v => η v * fluctuation 1 μ (ζ₁ v) / Real.Gamma μ)
        (fun v => η v * fluctuation 1 μ (ζ₂ v) / Real.Gamma μ) (C * ε) := by
  have hS : ContDiff ℝ ∞ (fluctuation 1 μ) := contDiff_fluctuation 1 μ one_pos hμ
  obtain ⟨Bη, hBη0, hBη⟩ := exists_jetBoundOn hη R (isCompact_closedBox b)
  obtain ⟨C₀, hC₀, hcomp⟩ := exists_jetClose_comp hS R (closedBox d b) hB
  refine ⟨|(Real.Gamma μ)⁻¹| * (2 ^ R * Bη * C₀), by positivity, ?_⟩
  intro ζ₁ ζ₂ hζ₁ hζ₂ hB₂ ε hε0 hε1 hc
  have h1 := hcomp ζ₁ ζ₂ hζ₁ hζ₂ hB₂ ε hε0 hε1 hc
  have h2 := JetClose.mul_left hη hBη hBη0 (hS.comp hζ₁) (hS.comp hζ₂) (mul_nonneg hC₀ hε0) h1
  have h3 := JetClose.const_smul (hη.mul (hS.comp hζ₁)) (hη.mul (hS.comp hζ₂)) h2
    (Real.Gamma μ)⁻¹
  rw [replaced_eq_smul, replaced_eq_smul]
  refine h3.mono_eps (le_of_eq ?_)
  ring

/-- ★★★ **Continuity of the cube replacement rule in the field**: for `η` smooth and vanishing
near the deep set of the cube relative to the closed box, `ζₙ → ζ` in `C^{|p|}` on the closed box
(`|p| = Σ(2kᵢ·cutoffOf h μ − hᵢ)`) implies
`empCoeffRect η ζₙ h k b μ (c−1) → empCoeffRect η ζ h k b μ (c−1)`. -/
theorem tendsto_empCoeffRect_top (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c)
    {ζ : ℕ → (Fin d → ℝ) → ℝ} {ζ₀ : (Fin d → ℝ) → ℝ} (hζ : ∀ n, ContDiff ℝ ∞ (ζ n))
    (hζ₀ : ContDiff ℝ ∞ ζ₀) {M : ℕ → ℝ} (hM0' : ∀ n, 0 ≤ M n)
    (hM : ∀ n, JetClose (∑ i, depthOf h k (cutoffOf h μ) i) (closedBox d b) (ζ n) ζ₀ (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun n => empCoeffRect η (ζ n) h k (fun _ => b) μ (c - 1)) atTop
      (𝓝 (empCoeffRect η ζ₀ h k (fun _ => b) μ (c - 1))) := by
  set R := ∑ i, depthOf h k (cutoffOf h μ) i with hR
  have hS : ContDiff ℝ ∞ (fluctuation 1 μ) := contDiff_fluctuation 1 μ one_pos hμ
  obtain ⟨B, hB0, hB⟩ := exists_jetBoundOn hζ₀ R (isCompact_closedBox b)
  obtain ⟨C, hC0, hrep⟩ := exists_jetClose_replaced hη hμ R b hB0
  have hfun : (fun n => empCoeffRect η (ζ n) h k (fun _ => b) μ (c - 1)) = fun n =>
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ n v) / Real.Gamma μ) h k 1 b μ (c - 1) :=
    funext fun n => empCoeffRect_top_eq_smoothCoeff hη (hζ n) hk hb hμ hc hdeep
  rw [hfun, empCoeffRect_top_eq_smoothCoeff hη hζ₀ hk hb hμ hc hdeep]
  have hev : ∀ᶠ n in atTop, M n ≤ 1 := hM0.eventually (Iic_mem_nhds zero_lt_one)
  refine tendsto_smoothCoeff_of_jetClose (M := fun n => C * M n)
    (fun n => (contDiff_mul_fluctuation hη (hζ n) hμ).div_const _)
    ((contDiff_mul_fluctuation hη hζ₀ hμ).div_const _) hk one_pos hb (hev.mono fun n hn => ?_)
    (by simpa using hM0.const_mul C) (c - 1)
  exact hrep (ζ n) ζ₀ (hζ n) hζ₀ hB (M n) (hM0' n) hn (hM n)

end SmoothEngine

end Grammar
