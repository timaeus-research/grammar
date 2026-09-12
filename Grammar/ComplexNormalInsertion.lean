/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxInputs

/-!
# Complexification and the complex normal insertion (CCCXXIX; phase 3, unit P2)

Consult #98 §3.1–3.2. `complexify w = (w_j : ℂ)_j` embeds `ℝ^d` into `ℂ^d` (sup norms); for a
nonempty coordinate set `I` the complex normal insertion `complexInsert I : ℂ^{|I|} →L[ℂ] ℂ^d` puts
`z_{σ⁻¹ j}` in the coordinates `j ∈ I` and `0` elsewhere; it is norm-nonincreasing (sup norm — no
dimensional constant) and compatible with the real insertion:
`complexify (originalNormalMap I s u) = complexify s + complexInsert I (complexify u)`. The closed
faces `X_I` are compact. Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

variable {d : ℕ}

/-- Coordinatewise complexification `ℝ^d → ℂ^d`. -/
def complexify (w : Fin d → ℝ) : Fin d → ℂ := fun j => (w j : ℂ)

theorem complexify_apply (w : Fin d → ℝ) (j : Fin d) : complexify w j = (w j : ℂ) := rfl

theorem continuous_complexify : Continuous (complexify (d := d)) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

theorem complexify_add (w v : Fin d → ℝ) : complexify (w + v) = complexify w + complexify v := by
  funext j
  simp [complexify]

/-- The complex normal insertion `z ↦ Σ_i z_i e_{σ i}` as a continuous linear map. -/
noncomputable def complexInsert (I : NonemptyIdx d) :
    (Fin (nI I + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun j : Fin d =>
    if h : j ∈ I.1 then ContinuousLinearMap.proj ((σI I).symm ⟨j, h⟩) else 0

theorem complexInsert_apply (I : NonemptyIdx d) (z : Fin (nI I + 1) → ℂ) (j : Fin d) :
    complexInsert I z j = if h : j ∈ I.1 then z ((σI I).symm ⟨j, h⟩) else 0 := by
  rw [complexInsert, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- The insertion is norm-nonincreasing for the sup norms. -/
theorem norm_complexInsert_le (I : NonemptyIdx d) (z : Fin (nI I + 1) → ℂ) :
    ‖complexInsert I z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  rw [complexInsert_apply]
  split_ifs
  · exact norm_le_pi_norm z _
  · rw [norm_zero]
    exact norm_nonneg z

/-- Compatibility with the real insertion:
`complexify (Ψ_I(s, u)) = complexify s + complexInsert I (complexify u)`. -/
theorem complexify_originalNormalMap (I : NonemptyIdx d) (s : Fin d → ℝ)
    (u : Fin (nI I + 1) → ℝ) :
    complexify (originalNormalMap I s u) = complexify s + complexInsert I (complexify u) := by
  funext j
  rw [Pi.add_apply, complexInsert_apply, complexify_apply, complexify_apply, originalNormalMap]
  by_cases hj : j ∈ I.1
  · rw [dif_pos hj, dif_pos hj, Complex.ofReal_add]
    rfl
  · rw [dif_neg hj, dif_neg hj, add_zero]

variable (a : ℝ)

/-- The closed faces are compact. -/
theorem isCompact_faceSet (I : Finset (Fin d)) : IsCompact (faceSet a I) := by
  have hbox : IsCompact (piBox d (Icc 0 a)) := isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ fun w hw => hw.1
  have : faceSet a I = piBox d (Icc 0 a) ∩ ⋂ i ∈ I, {w : Fin d → ℝ | w i = 0} := by
    ext w
    simp only [faceSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [this]
  refine (isClosed_set_pi fun _ _ => isClosed_Icc).inter (isClosed_biInter fun i _ => ?_)
  exact isClosed_eq (continuous_apply i) continuous_const

/-- Points of the closed face lie in the box. -/
theorem mem_piBox_of_mem_faceSet {I : Finset (Fin d)} {w : Fin d → ℝ} (hw : w ∈ faceSet a I) :
    w ∈ piBox d (Icc 0 a) := hw.1

end WaterFilling

end Grammar
