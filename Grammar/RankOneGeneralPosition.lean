/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RankOneNormalTilt

/-!
# Rank-one matrix factorisation: the normal tilt at a general orbit point

`Grammar.RankOneNormalTilt` computes the normal Gaussian integral of the rank-one model at the
aligned orbit point `x = α e₀`, `y = β e₀`.  A general orbit point is `x = U(α e₀)`,
`y = V(β e₀)` with orthogonal `U, V`, and the Gauss–Newton differential
`D_{x,y}(ξ, η) = x ηᵀ + ξ yᵀ` (`gnDGen`) transports as `D_{x,y}(Uξ', Vη') = U D_{α,β}(ξ', η') Vᵀ`
(`gnDGen_eq_conj`).  Since the Frobenius norm is orthogonally invariant (`frobSq_conj`) and the
Frobenius pairing transports the field, `⟨U B Vᵀ, Ξ⟩ = ⟨B, Uᵀ Ξ V⟩` (`frobInner_conj`), the
normal integral at the general point is the aligned one with the field `Uᵀ Ξ V`:

  `∫ e^{−n ‖D_{x,y}(Uξ', Vη')‖²/2 + √n ⟨D_{x,y}(Uξ', Vη'), Ξ⟩} = (2π/n)^{(M+N+1)/2}/(β^M α^N ρ) ·
    e^{‖P(UᵀΞV)‖²/2}`  (★★★ `integral_rankOne_normal_tilt_general`),

so the tilt at a general orbit point is `e^{‖P_{(x,y)}Ξ‖²/2}` with `P_{(x,y)}` the projection onto
the tangent space `U (cross) Vᵀ = range D_{x,y}` (examples_slop §5; Astra round-7 target 2: no
Gaussian change of variables is needed, the transport is pointwise in the integrand).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset Matrix

namespace Grammar

variable {M N : ℕ}

/-- The Gauss–Newton differential `D_{x,y}(ξ, η) = x ηᵀ + ξ yᵀ` at a general point. -/
def gnDGen (x ξ : Fin (M + 1) → ℝ) (y η : Fin (N + 1) → ℝ) (i : Fin (M + 1))
    (j : Fin (N + 1)) : ℝ :=
  x i * η j + ξ i * y j

theorem gnDGen_axis (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) :
    gnDGen (axisVec α) ξ (axisVec β) η = gnD α β ξ η := rfl

/-! ### Frobenius invariance -/

/-- `‖B‖² = tr(Bᵀ B)`. -/
theorem frobSq_eq_trace (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobSq B = Matrix.trace ((Matrix.of B)ᵀ * Matrix.of B) := by
  unfold frobSq Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, sq]
  exact Finset.sum_comm

/-- `⟨B, Ξ⟩ = tr(Bᵀ Ξ)`. -/
theorem frobInner_eq_trace (B Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobInner B Ξ = Matrix.trace ((Matrix.of B)ᵀ * Matrix.of Ξ) := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_comm

/-- The conjugate `U B Vᵀ` as a function. -/
def conjMat (U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ) (V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (B : Fin (M + 1) → Fin (N + 1) → ℝ) : Fin (M + 1) → Fin (N + 1) → ℝ :=
  fun i j => (U * Matrix.of B * Vᵀ) i j

theorem of_conjMat (U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    Matrix.of (conjMat U V B) = U * Matrix.of B * Vᵀ := by
  ext i j; rfl

/-- ★ **Orthogonal invariance of the Frobenius norm**: `‖U B Vᵀ‖² = ‖B‖²` for `UᵀU = 1`,
`VᵀV = 1`. -/
theorem frobSq_conj {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (B : Fin (M + 1) → Fin (N + 1) → ℝ) : frobSq (conjMat U V B) = frobSq B := by
  rw [frobSq_eq_trace, frobSq_eq_trace, of_conjMat, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  -- `tr(V Bᵀ Uᵀ U B Vᵀ) = tr(V Bᵀ B Vᵀ) = tr(Bᵀ B Vᵀ V) = tr(Bᵀ B)`
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hV, Matrix.mul_one]

/-- ★ **Transport of the Frobenius pairing**: `⟨U B Vᵀ, Ξ⟩ = ⟨B, Uᵀ Ξ V⟩`. -/
theorem frobInner_conj (U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (B Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobInner (conjMat U V B) Ξ = frobInner B (conjMat Uᵀ Vᵀ Ξ) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, of_conjMat, of_conjMat, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  -- `tr(V Bᵀ Uᵀ Ξ) = tr(Bᵀ Uᵀ Ξ V)`
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-! ### Transport of the differential -/

/-- ★★ `D_{Ua, Vb}(Uξ, Vη) = U D_{a,b}(ξ, η) Vᵀ`: the differential at the transported point. -/
theorem gnDGen_conj (U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (a ξ : Fin (M + 1) → ℝ) (b η : Fin (N + 1) → ℝ) :
    gnDGen (U.mulVec a) (U.mulVec ξ) (V.mulVec b) (V.mulVec η) =
      conjMat U V (gnDGen a ξ b η) := by
  funext i j
  simp only [gnDGen, conjMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
    mul_add, add_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- ★★ `D_{x,y}(Uξ', Vη') = U D_{α,β}(ξ', η') Vᵀ` at the orbit point `x = U(αe₀)`, `y = V(βe₀)`. -/
theorem gnDGen_eq_conj (U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (α β : ℝ) (ξ : Fin (M + 1) → ℝ)
    (η : Fin (N + 1) → ℝ) :
    gnDGen (U.mulVec (axisVec α)) (U.mulVec ξ) (V.mulVec (axisVec β)) (V.mulVec η) =
      conjMat U V (gnD α β ξ η) := by
  rw [gnDGen_conj, gnDGen_axis]

/-! ### The normal tilt integral at a general orbit point -/

/-- ★★★ **The normal tilt at a general orbit point** `x = U(αe₀)`, `y = V(βe₀)`, `UᵀU = VᵀV = 1`:
in the transported normal coordinates the integral is the aligned one with the field `UᵀΞV`,
`(2π/n)^{(M+N+1)/2}/(β^M α^N ρ) · e^{‖P(UᵀΞV)‖²/2}`. -/
theorem integral_rankOne_normal_tilt_general {n α β ρ : ℝ} (hn : 0 < n) (hα : 0 < α)
    (hβ : 0 < β) (hρ : 0 < ρ) (hρ2 : ρ ^ 2 = α ^ 2 + β ^ 2)
    {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ} {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    ∫ v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ,
        Real.exp (-n * frobSq (gnDGen (U.mulVec (axisVec α))
            (U.mulVec (normalCoord α β ρ v).1) (V.mulVec (axisVec β))
            (V.mulVec (normalCoord α β ρ v).2)) / 2 +
          Real.sqrt n * frobInner (gnDGen (U.mulVec (axisVec α))
            (U.mulVec (normalCoord α β ρ v).1) (V.mulVec (axisVec β))
            (V.mulVec (normalCoord α β ρ v).2)) Ξ) =
      Real.sqrt (2 * Real.pi / n) ^ (M + N + 1) / (β ^ M * α ^ N * ρ) *
        Real.exp (crossNormSq (conjMat Uᵀ Vᵀ Ξ) / 2) := by
  rw [← integral_rankOne_normal_tilt hn hα hβ hρ hρ2 (conjMat Uᵀ Vᵀ Ξ)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [gnDGen_eq_conj, frobSq_conj hU hV, frobInner_conj]

end Grammar
