/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.NormalTaylorForm

/-!
# The normal differential: convention (CCXCVII)

Unit 1 of the coordinate-free programme (consult #92). The paper's coordinate-free expansion
`𝒵_n[φ; I] ~ Σ_r (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩ τ_*|μ_I|` uses the UNNORMALISED normal
differential `D^r_⊥ F = D^r (F ∘ Φ_s)(0)` together with an explicit `1/r!`. The library's
`normalTaylorForm` already carries the `1/r!` (`T_r = J_r / r!`), so the two must not be combined.
This unit fixes the convention: `normalDifferential N Φ F s r := rawNormalJet N Φ F s r`
(the paper's `D^r_⊥ F` relative to the chosen normal family), with
`r! • normalTaylorForm = normalDifferential` (`factorial_smul_normalTaylorForm`), its dependence on
the germ of the tubular map at the zero section only (`normalDifferential_congr`), the degree-zero
value (restriction to the stratum), the diagonal Taylor-term identity
`D^r_⊥ F (n,…,n) = r! · (homogeneous Taylor term of degree r)`, and linearity in `F` at the level
of `C^r` functions of the fibre (`normalDifferential_add`, `normalDifferential_smul`).
-/

open Filter Topology

namespace Grammar

section Family

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
  (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)

/-- **The normal differential** `D^r_⊥ F (s) = D^r (F ∘ Φ_s)(0)` of the paper (`defn:normal_diff`),
UNNORMALISED: the raw normal jet of the chosen normal family. -/
noncomputable def normalDifferential (r : ℕ) : JetForm (N s) r := rawNormalJet N Φ F s r

theorem normalDifferential_eq_rawNormalJet (r : ℕ) :
    normalDifferential N Φ F s r = rawNormalJet N Φ F s r := rfl

/-- **The convention**: `r! · T_r F = D^r_⊥ F`. -/
theorem factorial_smul_normalTaylorForm (r : ℕ) :
    (r.factorial : ℝ) • normalTaylorForm N Φ F s r = normalDifferential N Φ F s r := by
  unfold normalTaylorForm normalDifferential
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast r.factorial_ne_zero), one_smul]

/-- `T_r F = D^r_⊥ F / r!`. -/
theorem normalTaylorForm_eq_inv_factorial_smul (r : ℕ) :
    normalTaylorForm N Φ F s r = (r.factorial : ℝ)⁻¹ • normalDifferential N Φ F s r := rfl

/-- The normal differential depends only on the germ of the tubular map at the zero section. -/
theorem normalDifferential_congr {Φ' : ∀ s, N s → M} (h : Φ s =ᶠ[nhds (0 : N s)] Φ' s) (r : ℕ) :
    normalDifferential N Φ F s r = normalDifferential N Φ' F s r :=
  rawNormalJet_congr N Φ F s h r

/-- Degree zero is restriction to the stratum. -/
theorem normalDifferential_zero_apply (m : Fin 0 → N s) :
    normalDifferential N Φ F s 0 m = F (Φ s 0) := by
  simp [normalDifferential, rawNormalJet, iteratedFDeriv_zero_apply]

/-- The diagonal values are `r!` times the homogeneous Taylor terms. -/
theorem normalDifferential_apply_diag (r : ℕ) (n : N s) :
    normalDifferential N Φ F s r (fun _ => n) =
      (r.factorial : ℝ) * homogeneousTaylor (fun n : N s => F (Φ s n)) r n := by
  rw [← factorial_smul_normalTaylorForm, smul_apply,
    normalTaylorForm_apply_diag, smul_eq_mul]

end Family

section Linear

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
  (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (s : S)

/-- **Additivity in the observable** for fibre maps of class `C^r`. -/
theorem normalDifferential_add {F G : M → ℝ} {r : ℕ} (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (hG : ContDiff ℝ r (fun n : N s => G (Φ s n))) :
    normalDifferential N Φ (fun m => F m + G m) s r =
      normalDifferential N Φ F s r + normalDifferential N Φ G s r := by
  unfold normalDifferential rawNormalJet
  have h := iteratedFDeriv_add_apply (i := r) (x := (0 : N s)) hF.contDiffAt hG.contDiffAt
  simpa [Pi.add_def] using h

/-- **Homogeneity in the observable** for fibre maps of class `C^r`. -/
theorem normalDifferential_smul (c : ℝ) {F : M → ℝ} {r : ℕ}
    (hF : ContDiff ℝ r (fun n : N s => F (Φ s n))) :
    normalDifferential N Φ (fun m => c * F m) s r = c • normalDifferential N Φ F s r := by
  unfold normalDifferential rawNormalJet
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := r) (x := (0 : N s)) (a := c)
    hF.contDiffAt
  simpa [smul_eq_mul, Pi.smul_def] using h

end Linear

end Grammar
