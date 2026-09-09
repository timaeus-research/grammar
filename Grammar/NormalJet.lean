/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normal jets and fibre-linear covariance

The paper's normal Taylor tensors are the iterated derivatives at the origin of the normal
fibre of a tubular chart.  We model them as continuous multilinear forms (`JetForm E r`), define the
**normal jet** `normalJet F r = D^r F(0)` and the homogeneous Taylor term
`homogeneousTaylor F r u = D^r F(0)[u,…,u]/r!`, and prove the covariance under fibre-linear changes
of frame (`lem:normal_deriv`):

* `normalJet_comp_linear`: `D^r (F ∘ L)(0) = D^r F(0) ∘ (L,…,L)` for a continuous linear `L`;
* `homogeneousTaylor_comp_linear`: `T_r(F ∘ L)(u) = T_r F (L u)`;
* for a diagonal scaling `u ↦ (g_i u_i)` on `ℝ^d`, the multi-index derivative components scale by
  `∏_j g_{m_j}` (`jetComponent_normalJet_comp_diagScale`), and in the paper's convention
  `F'(u') = F(u)`, `u' = g·u`, by `∏_j g_{m_j}⁻¹` (`jetComponent_normalJet_comp_diagScale_inv`).

For a base parameter, apply these pointwise in the fibre (`normalJet_comp_linear_family`): no
derivatives of `L` in the base appear because these are fibre derivatives.

Non-claim: normal jets are relative to a fixed tubular identification and are invariant only under
fibre-**linear** changes of frame.  A nonlinear fibre change `u' = u + a u²` changes the second
Taylor coefficient whenever the first derivative is nonzero; nothing here removes that dependence.
-/

open scoped ContDiff

namespace Grammar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous `r`-linear forms on `E`: the home of the `r`-th normal Taylor tensor. -/
abbrev JetForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ

/-- The normal jet `D^r F(0)`. -/
noncomputable def normalJet (F : E → ℝ) (r : ℕ) : JetForm E r := iteratedFDeriv ℝ r F 0

/-- The homogeneous Taylor term `D^r F(0)[u,…,u] / r!`. -/
noncomputable def homogeneousTaylor (F : E → ℝ) (r : ℕ) (u : E) : ℝ :=
  (r.factorial : ℝ)⁻¹ * normalJet F r (fun _ => u)

/-- **Fibre-linear covariance of normal jets**: `D^r (F ∘ L)(0) = D^r F(0) ∘ (L,…,L)`. -/
theorem normalJet_comp_linear {F : E → ℝ} {r : ℕ} (hF : ContDiff ℝ r F) (L : E →L[ℝ] E) :
    normalJet (F ∘ L) r = (normalJet F r).compContinuousLinearMap fun _ => L := by
  unfold normalJet
  rw [L.iteratedFDeriv_comp_right hF 0 le_rfl, map_zero]

theorem normalJet_comp_equiv {F : E → ℝ} {r : ℕ} (hF : ContDiff ℝ r F) (L : E ≃L[ℝ] E) :
    normalJet (F ∘ L) r = (normalJet F r).compContinuousLinearMap fun _ => (L : E →L[ℝ] E) :=
  normalJet_comp_linear hF (L : E →L[ℝ] E)

/-- **Covariance of the homogeneous Taylor terms**: `T_r(F ∘ L)(u) = T_r F(L u)`. -/
theorem homogeneousTaylor_comp_linear {F : E → ℝ} {r : ℕ} (hF : ContDiff ℝ r F) (L : E →L[ℝ] E)
    (u : E) : homogeneousTaylor (F ∘ L) r u = homogeneousTaylor F r (L u) := by
  unfold homogeneousTaylor
  rw [normalJet_comp_linear hF L, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- The base-parametrised form: fibrewise linear frame changes act fibrewise on the jets. -/
theorem normalJet_comp_linear_family {V : Type*} {F : V → E → ℝ} {L : V → E →L[ℝ] E} {r : ℕ}
    (hF : ∀ v, ContDiff ℝ r (F v)) (v : V) :
    normalJet (fun u => F v (L v u)) r = (normalJet (F v) r).compContinuousLinearMap fun _ => L v :=
  normalJet_comp_linear (hF v) (L v)

/-! ### Diagonal scalings on `ℝ^d` and derivative components -/

/-- The diagonal scaling `u ↦ (g_i u_i)_i`. -/
noncomputable def diagScale {d : ℕ} (g : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => g i • ContinuousLinearMap.proj i

@[simp] theorem diagScale_apply {d : ℕ} (g u : Fin d → ℝ) (i : Fin d) :
    diagScale g u i = g i * u i := by
  simp [diagScale]

theorem diagScale_single {d : ℕ} (g : Fin d → ℝ) (i : Fin d) :
    diagScale g (Pi.single i 1) = g i • Pi.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem diagScale_inv_apply {d : ℕ} {g : Fin d → ℝ} (hg : ∀ i, g i ≠ 0) (u : Fin d → ℝ) :
    diagScale g⁻¹ (diagScale g u) = u := by
  ext i
  simp [Pi.inv_apply, ← mul_assoc, inv_mul_cancel₀ (hg i)]

/-- The derivative component `A(e_{m 0}, …, e_{m (r-1)})` of an `r`-form on `ℝ^d`. -/
noncomputable def jetComponent {d r : ℕ} (A : JetForm (Fin d → ℝ) r) (m : Fin r → Fin d) : ℝ :=
  A fun j => Pi.single (m j) 1

theorem jetComponent_compDiag {d r : ℕ} (A : JetForm (Fin d → ℝ) r) (g : Fin d → ℝ)
    (m : Fin r → Fin d) :
    jetComponent (A.compContinuousLinearMap fun _ => diagScale g) m =
      (∏ j, g (m j)) * jetComponent A m := by
  unfold jetComponent
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [diagScale_single]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-- **`lem:normal_deriv`, derivative form**: the multi-index derivative components of
`F ∘ diag(g)` at `0` are those of `F` scaled by `∏_j g_{m_j}`. -/
theorem jetComponent_normalJet_comp_diagScale {d r : ℕ} {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ r F) (g : Fin d → ℝ) (m : Fin r → Fin d) :
    jetComponent (normalJet (F ∘ diagScale g) r) m =
      (∏ j, g (m j)) * jetComponent (normalJet F r) m := by
  rw [normalJet_comp_linear hF, jetComponent_compDiag]

/-- **`lem:normal_deriv`, paper's convention**: in the new fibre coordinates `u' = g·u` the same
function `F' = F ∘ diag(g)⁻¹` (so `F'(u') = F(u)`) has derivative components scaled by
`∏_j g_{m_j}⁻¹`. -/
theorem jetComponent_normalJet_comp_diagScale_inv {d r : ℕ} {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ r F) (g : Fin d → ℝ) (m : Fin r → Fin d) :
    jetComponent (normalJet (F ∘ diagScale g⁻¹) r) m =
      (∏ j, (g (m j))⁻¹) * jetComponent (normalJet F r) m := by
  rw [jetComponent_normalJet_comp_diagScale hF]
  simp only [Pi.inv_apply]

/-- The reparametrised function agrees with the original: `F'(g·u) = F(u)`. -/
theorem comp_diagScale_inv_apply {d : ℕ} {F : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ}
    (hg : ∀ i, g i ≠ 0) (u : Fin d → ℝ) : (F ∘ diagScale g⁻¹) (diagScale g u) = F u := by
  simp only [Function.comp, diagScale_inv_apply hg]

end Grammar
