/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RankOneGeneralPosition

/-!
# Rank-one matrix factorisation: the invariant tangent projection

The orthogonal projection of `ℝ^{(M+1)×(N+1)}` onto the tangent space `T_A = {x ηᵀ + ξ yᵀ}` of the
rank-one variety at `A = x yᵀ` (`x, y ≠ 0`) is

  `P_{x,y}(B) = P_x B + B P_y − P_x B P_y`,  `P_x = x xᵀ/‖x‖²`  (`tanProj`),

an expression independent of coordinates.  This file identifies it with the cross restriction of
`Grammar.RankOneNormalTilt` transported by `Grammar.RankOneGeneralPosition`: for orthogonal `U, V`
and `x = U(αe₀)`, `y = V(βe₀)`, `α, β ≠ 0`,

  `P_{x,y}(Ξ) = U · cross(UᵀΞV) · Vᵀ`  (`tanProj_conj_axis`),  hence
  `‖P_{x,y}Ξ‖²_F = crossNormSq(UᵀΞV)`  (★★★ `frobSq_tanProj_eq_crossNormSq`),

so the tilt of `integral_rankOne_normal_tilt_general` is `e^{‖P_{x,y}Ξ‖²/2}` in invariant form
(examples_slop §5; Astra round-8 fidelity item).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset Matrix

namespace Grammar

variable {M N : ℕ}

/-- The rank-one projection `x xᵀ/‖x‖²`. -/
noncomputable def projMat {m : ℕ} (x : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => x i * x j / ∑ k, x k ^ 2

/-- The tangent projection `P_{x,y}(B) = P_x B + B P_y − P_x B P_y`. -/
noncomputable def tanProj (x : Fin (M + 1) → ℝ) (y : Fin (N + 1) → ℝ)
    (B : Fin (M + 1) → Fin (N + 1) → ℝ) : Fin (M + 1) → Fin (N + 1) → ℝ :=
  fun i j => (projMat x * Matrix.of B + Matrix.of B * projMat y -
    projMat x * Matrix.of B * projMat y) i j

/-! ### Transport of the rank-one projection -/

/-- `‖Ua‖² = ‖a‖²` for `UᵀU = 1`. -/
theorem sum_sq_mulVec {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ} (hU : Uᵀ * U = 1)
    (a : Fin m → ℝ) : ∑ i, (U.mulVec a) i ^ 2 = ∑ k, a k ^ 2 := by
  have h : ∑ i, (U.mulVec a) i ^ 2 = dotProduct (U.mulVec a) (U.mulVec a) := by
    simp only [dotProduct, sq]
  rw [h, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]
  simp only [dotProduct, sq]

/-- `P_{Ua} = U P_a Uᵀ` for `UᵀU = 1`. -/
theorem projMat_mulVec {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ} (hU : Uᵀ * U = 1)
    (a : Fin m → ℝ) : projMat (U.mulVec a) = U * projMat a * Uᵀ := by
  ext i j
  simp only [projMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    sum_sq_mulVec hU]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `P_{Ua,Vb}(U B Vᵀ) = U P_{a,b}(B) Vᵀ` for orthogonal `U, V`. -/
theorem tanProj_conj {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (a : Fin (M + 1) → ℝ) (b : Fin (N + 1) → ℝ) (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (U.mulVec a) (V.mulVec b) (conjMat U V B) = conjMat U V (tanProj a b B) := by
  funext i j
  simp only [tanProj, conjMat, of_conjMat, projMat_mulVec hU, projMat_mulVec hV]
  have e : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) +
      U * Matrix.of B * Vᵀ * (V * projMat b * Vᵀ) -
      U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) * (V * projMat b * Vᵀ) =
      U * (projMat a * Matrix.of B + Matrix.of B * projMat b -
        projMat a * Matrix.of B * projMat b) * Vᵀ := by
    have h1 : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) = U * (projMat a * Matrix.of B) * Vᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    have h2 : U * Matrix.of B * Vᵀ * (V * projMat b * Vᵀ) = U * (Matrix.of B * projMat b) * Vᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
    have h3 : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) * (V * projMat b * Vᵀ) =
        U * (projMat a * Matrix.of B * projMat b) * Vᵀ := by
      rw [h1]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
    rw [h3, h1, h2]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  rw [e]
  rfl

/-! ### The aligned point: the tangent projection is the cross restriction -/

/-- `P_{αe₀} = E₀₀` for `α ≠ 0`. -/
theorem projMat_axisVec {α : ℝ} (hα : α ≠ 0) :
    projMat (axisVec (M := M) α) = Matrix.of fun i j => if i = 0 ∧ j = 0 then (1 : ℝ) else 0 := by
  ext i j
  have hsum : ∑ k, axisVec (M := M) α k ^ 2 = α ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp
  simp only [projMat, Matrix.of_apply, hsum]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Fin.succ_ne_zero, ← sq, hα]

/-- At the aligned point the tangent projection is the cross restriction. -/
theorem tanProj_axis {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (axisVec α) (axisVec β) B = cross B := by
  funext i j
  simp only [tanProj, projMat_axisVec hα, projMat_axisVec hβ, cross, Matrix.add_apply,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Fin.succ_ne_zero]

/-- ★★ `P_{x,y}(Ξ) = U · cross(UᵀΞV) · Vᵀ` at `x = U(αe₀)`, `y = V(βe₀)`. -/
theorem tanProj_conj_axis {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (U.mulVec (axisVec α)) (V.mulVec (axisVec β)) Ξ =
      conjMat U V (cross (conjMat Uᵀ Vᵀ Ξ)) := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.1 hU
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hV
  have hΞ : Ξ = conjMat U V (conjMat Uᵀ Vᵀ Ξ) := by
    funext i j
    simp only [conjMat, of_conjMat, Matrix.transpose_transpose]
    rw [show U * (Uᵀ * Matrix.of Ξ * V) * Vᵀ = (U * Uᵀ) * Matrix.of Ξ * (V * Vᵀ) by
      simp only [Matrix.mul_assoc], hU', hV', Matrix.one_mul, Matrix.mul_one]
    rfl
  conv_lhs => rw [hΞ]
  rw [tanProj_conj hU hV, tanProj_axis hα hβ]

/-- ★★★ **The invariant tilt norm**: `‖P_{x,y}Ξ‖²_F = crossNormSq(UᵀΞV)` at `x = U(αe₀)`,
`y = V(βe₀)`, `α, β ≠ 0`. -/
theorem frobSq_tanProj_eq_crossNormSq {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobSq (tanProj (U.mulVec (axisVec α)) (V.mulVec (axisVec β)) Ξ) =
      crossNormSq (conjMat Uᵀ Vᵀ Ξ) := by
  rw [tanProj_conj_axis hU hV hα hβ, frobSq_conj hU hV, crossNormSq_eq]

end Grammar
