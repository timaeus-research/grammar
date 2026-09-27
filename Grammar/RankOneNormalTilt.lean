/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RankOneGauss

/-!
# Rank-one matrix factorisation: the normal Gaussian integral and the tilt `e^{‖PΞ‖²/2}`

At a point `(x, y)` of the gauge orbit `{x yᵀ = A}` of the rank-one model, the Gauss–Newton
differential is `D(ξ, η) = x ηᵀ + ξ yᵀ` and `K = ½‖D(ξ, η)‖² + O(3)` (examples_slop §5).  In
coordinates adapted to the orbit point, `x = α e₀ ∈ ℝ^{M+1}` and `y = β e₀ ∈ ℝ^{N+1}`, the
quadratic form is

  `‖D(ξ, η)‖² = β² Σ_{i ≥ 1} ξᵢ² + α² Σ_{j ≥ 1} ηⱼ² + (β ξ₀ + α η₀)²`  (`frobSq_gnD`),

with normal eigenvalues `|y|² = β²` (`M` times), `|x|² = α²` (`N` times) and `|x|² + |y|²`
(once), and the kernel is the tangent line `(α e₀, −β e₀)` of the orbit (`gnD_tangent`).
The normal coordinates `(ξ⊥, η⊥, w)` put `(ξ₀, η₀) = w (β, α)/ρ`, `ρ² = α² + β²`
(`normalCoord`), and the normal Gaussian integral with the linear field `√n ⟨D u, Ξ⟩` is

  `∫ e^{−n ‖D u‖²/2 + √n ⟨D u, Ξ⟩} du = (2π/n)^{(M+N+1)/2} / (β^M α^N ρ) · e^{‖PΞ‖²/2}`

(★★★ `integral_rankOne_normal_tilt`), where `‖PΞ‖² = Σ_{i ≥ 1} Ξᵢ₀² + Σ_{j ≥ 1} Ξ₀ⱼ² + Ξ₀₀²`
(`crossNormSq`) is the squared Frobenius norm of the restriction of `Ξ` to the cross
`{i = 0} ∪ {j = 0}`: that cross is the range of `D`, the tangent space `T_A = {a ηᵀ + ξ bᵀ}`
of the rank-one variety (`cross_eq_gnD`, `gnD_succ_succ`), and the restriction is the
orthogonal projection onto it (`frobInner_gnD_sub_cross`).  The tilt depends on `Ξ` only through
`PΞ`, and not on the orbit position `(α, β)`: the fluctuation function of the regular case,
constant along the orbit.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace Grammar

variable {M N : ℕ}

/-- The axis vector `α e₀`. -/
def axisVec (α : ℝ) : Fin (M + 1) → ℝ := Fin.cons α 0

/-- The Gauss–Newton differential `D(ξ, η) = x ηᵀ + ξ yᵀ` at the orbit point
`x = α e₀`, `y = β e₀`. -/
def gnD (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) (i : Fin (M + 1))
    (j : Fin (N + 1)) : ℝ :=
  axisVec α i * η j + ξ i * axisVec β j

/-- The squared Frobenius norm. -/
def frobSq (B : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ := ∑ i, ∑ j, B i j ^ 2

/-- The Frobenius inner product. -/
def frobInner (B Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ := ∑ i, ∑ j, B i j * Ξ i j

/-- The squared norm of the restriction of `Ξ` to the cross `{i = 0} ∪ {j = 0}`: `‖PΞ‖²`. -/
def crossNormSq (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) : ℝ :=
  ∑ i : Fin M, Ξ i.succ 0 ^ 2 + ∑ j : Fin N, Ξ 0 j.succ ^ 2 + Ξ 0 0 ^ 2

/-- The restriction of `Ξ` to the cross: the orthogonal projection `PΞ` onto `T_A`. -/
def cross (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) (i : Fin (M + 1)) (j : Fin (N + 1)) : ℝ :=
  if i = 0 ∨ j = 0 then Ξ i j else 0

@[simp] theorem axisVec_zero (α : ℝ) : axisVec (M := M) α 0 = α := by simp [axisVec]

@[simp] theorem axisVec_succ (α : ℝ) (i : Fin M) : axisVec α i.succ = 0 := by simp [axisVec]

theorem gnD_zero_zero (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) :
    gnD α β ξ η 0 0 = α * η 0 + ξ 0 * β := by simp [gnD]

theorem gnD_zero_succ (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) (j : Fin N) :
    gnD α β ξ η 0 j.succ = α * η j.succ := by simp [gnD]

theorem gnD_succ_zero (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) (i : Fin M) :
    gnD α β ξ η i.succ 0 = ξ i.succ * β := by simp [gnD]

/-- `D` has no component off the cross: its range lies in `T_A`. -/
theorem gnD_succ_succ (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) (i : Fin M)
    (j : Fin N) : gnD α β ξ η i.succ j.succ = 0 := by simp [gnD]

/-- The tangent line of the orbit `t ↦ (t a, b/t)` is the kernel of `D`. -/
theorem gnD_tangent (α β : ℝ) :
    gnD (M := M) (N := N) α β (axisVec α) (axisVec (-β)) = 0 := by
  funext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [gnD]

/-- The Gauss–Newton quadratic form in adapted coordinates: normal eigenvalues `β²` (`M` times),
`α²` (`N` times) and `α² + β²` on the normal direction `(β, α)` of the `(ξ₀, η₀)`-plane. -/
theorem frobSq_gnD (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ) :
    frobSq (gnD α β ξ η) =
      β ^ 2 * ∑ i : Fin M, ξ i.succ ^ 2 + α ^ 2 * ∑ j : Fin N, η j.succ ^ 2 +
        (β * ξ 0 + α * η 0) ^ 2 := by
  unfold frobSq
  simp only [Fin.sum_univ_succ, gnD_zero_zero, gnD_zero_succ, gnD_succ_zero, gnD_succ_succ]
  simp only [mul_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero, Finset.mul_sum]
  ring_nf

/-- The linear field in adapted coordinates. -/
theorem frobInner_gnD (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ)
    (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobInner (gnD α β ξ η) Ξ =
      β * ∑ i : Fin M, ξ i.succ * Ξ i.succ 0 + α * ∑ j : Fin N, η j.succ * Ξ 0 j.succ +
        (β * ξ 0 + α * η 0) * Ξ 0 0 := by
  unfold frobInner
  simp only [Fin.sum_univ_succ, gnD_zero_zero, gnD_zero_succ, gnD_succ_zero, gnD_succ_succ,
    zero_mul, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum, mul_assoc]
  ring_nf

/-- `‖PΞ‖²` is the squared Frobenius norm of the cross restriction. -/
theorem crossNormSq_eq (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    crossNormSq Ξ = frobSq (cross Ξ) := by
  unfold frobSq crossNormSq
  simp only [Fin.sum_univ_succ, cross, true_or, or_true, if_true, Fin.succ_ne_zero, or_self,
    if_false, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    add_zero]
  ring

/-- The cross is the range of `D`: every matrix supported on the cross is a Gauss–Newton
image (for `α, β ≠ 0`), so the cross is the tangent space `T_A`. -/
theorem cross_eq_gnD {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    cross Ξ = gnD α β (fun i => Ξ i 0 / β) (Fin.cons 0 fun j => Ξ 0 j.succ / α) := by
  funext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [gnD, cross, Fin.succ_ne_zero]
  · field_simp
  · field_simp
  · field_simp

/-- The complement `Ξ − PΞ` is orthogonal to the range of `D`: `P` is the orthogonal
projection onto `T_A`. -/
theorem frobInner_gnD_sub_cross (α β : ℝ) (ξ : Fin (M + 1) → ℝ) (η : Fin (N + 1) → ℝ)
    (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobInner (gnD α β ξ η) (fun i j => Ξ i j - cross Ξ i j) = 0 := by
  unfold frobInner
  simp only [Fin.sum_univ_succ, gnD_zero_succ, gnD_succ_succ, cross, true_or, or_true, if_true,
    Fin.succ_ne_zero, or_self, if_false, sub_self, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero]

/-- The normal coordinates `(ξ⊥, η⊥, w) ↦ (ξ, η)` with `(ξ₀, η₀) = w (β, α)/ρ`. -/
noncomputable def normalCoord (α β ρ : ℝ) (v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ) :
    (Fin (M + 1) → ℝ) × (Fin (N + 1) → ℝ) :=
  (Fin.cons (β * v.2.2 / ρ) v.1, Fin.cons (α * v.2.2 / ρ) v.2.1)

/-- The one-dimensional normal integral with a linear field: for `n, c > 0`,
`∫ e^{−n c² t²/2 + √n c d t} dt = √(2π/n)/c · e^{d²/2}`. -/
theorem integral_normal_line {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (d : ℝ) :
    ∫ t : ℝ, Real.exp (-(n * c ^ 2 / 2) * t ^ 2 + Real.sqrt n * c * d * t) =
      Real.sqrt (2 * Real.pi / n) / c * Real.exp (d ^ 2 / 2) := by
  have h := integral_exp_quadratic_real (α := n * c ^ 2 / 2) (by positivity)
    (Real.sqrt n * c * d) 0
  simp only [sub_zero] at h
  rw [h]
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have h1 : Real.pi / (n * c ^ 2 / 2) = (2 * Real.pi / n) / c ^ 2 := by
    field_simp
  rw [h1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc.le]
  congr 2
  field_simp
  rw [hs]
  ring

/-- ★★★ **The normal Gaussian integral of the rank-one model with the linear field**: in the
normal coordinates at the orbit point `(α e₀, β e₀)`,
`∫ e^{−n‖D u‖²/2 + √n⟨D u, Ξ⟩} du = (2π/n)^{(M+N+1)/2} / (β^M α^N ρ) · e^{‖PΞ‖²/2}`,
`ρ = √(α² + β²)`; the tilt is `e^{‖PΞ‖²/2}`, independent of the orbit position. -/
theorem integral_rankOne_normal_tilt {n α β ρ : ℝ} (hn : 0 < n) (hα : 0 < α) (hβ : 0 < β)
    (hρ : 0 < ρ) (hρ2 : ρ ^ 2 = α ^ 2 + β ^ 2) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    ∫ v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ,
        Real.exp (-n * frobSq (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) / 2 +
          Real.sqrt n * frobInner (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) Ξ) =
      Real.sqrt (2 * Real.pi / n) ^ (M + N + 1) / (β ^ M * α ^ N * ρ) *
        Real.exp (crossNormSq Ξ / 2) := by
  have hpt : ∀ v : (Fin M → ℝ) × (Fin N → ℝ) × ℝ,
      Real.exp (-n * frobSq (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) / 2 +
        Real.sqrt n * frobInner (gnD α β (normalCoord α β ρ v).1 (normalCoord α β ρ v).2) Ξ) =
      (∏ i : Fin M, Real.exp (-(n * β ^ 2 / 2) * v.1 i ^ 2 +
          Real.sqrt n * β * Ξ i.succ 0 * v.1 i)) *
        ((∏ j : Fin N, Real.exp (-(n * α ^ 2 / 2) * v.2.1 j ^ 2 +
          Real.sqrt n * α * Ξ 0 j.succ * v.2.1 j)) *
        Real.exp (-(n * ρ ^ 2 / 2) * v.2.2 ^ 2 + Real.sqrt n * ρ * Ξ 0 0 * v.2.2)) := by
    intro v
    rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [frobSq_gnD, frobInner_gnD]
    simp only [normalCoord, Fin.cons_succ, Fin.cons_zero]
    have hw : β * (β * v.2.2 / ρ) + α * (α * v.2.2 / ρ) = ρ * v.2.2 := by
      rw [show β * (β * v.2.2 / ρ) + α * (α * v.2.2 / ρ) = (α ^ 2 + β ^ 2) * v.2.2 / ρ by ring,
        ← hρ2, div_eq_iff hρ.ne']
      ring
    rw [hw]
    have e1 : ∑ i : Fin M, (-(n * β ^ 2 / 2) * v.1 i ^ 2 + Real.sqrt n * β * Ξ i.succ 0 * v.1 i) =
        -(n / 2) * (β ^ 2 * ∑ i, v.1 i ^ 2) + Real.sqrt n * (β * ∑ i, v.1 i * Ξ i.succ 0) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ j : Fin N, (-(n * α ^ 2 / 2) * v.2.1 j ^ 2 +
          Real.sqrt n * α * Ξ 0 j.succ * v.2.1 j) =
        -(n / 2) * (α ^ 2 * ∑ j, v.2.1 j ^ 2) + Real.sqrt n * (α * ∑ j, v.2.1 j * Ξ 0 j.succ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    ring
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (f := fun u : Fin M → ℝ => ∏ i, Real.exp (-(n * β ^ 2 / 2) * u i ^ 2 +
      Real.sqrt n * β * Ξ i.succ 0 * u i))
    (g := fun q : (Fin N → ℝ) × ℝ => (∏ j : Fin N, Real.exp (-(n * α ^ 2 / 2) * q.1 j ^ 2 +
      Real.sqrt n * α * Ξ 0 j.succ * q.1 j)) *
        Real.exp (-(n * ρ ^ 2 / 2) * q.2 ^ 2 + Real.sqrt n * ρ * Ξ 0 0 * q.2)),
    Measure.volume_eq_prod, integral_prod_mul
    (f := fun u : Fin N → ℝ => ∏ j, Real.exp (-(n * α ^ 2 / 2) * u j ^ 2 +
      Real.sqrt n * α * Ξ 0 j.succ * u j))
    (g := fun t : ℝ => Real.exp (-(n * ρ ^ 2 / 2) * t ^ 2 + Real.sqrt n * ρ * Ξ 0 0 * t))]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin M) (t : ℝ) =>
      Real.exp (-(n * β ^ 2 / 2) * t ^ 2 + Real.sqrt n * β * Ξ i.succ 0 * t)),
    integral_fintype_prod_volume_eq_prod (fun (j : Fin N) (t : ℝ) =>
      Real.exp (-(n * α ^ 2 / 2) * t ^ 2 + Real.sqrt n * α * Ξ 0 j.succ * t))]
  simp_rw [integral_normal_line hn hβ, integral_normal_line hn hα, integral_normal_line hn hρ]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    ← Real.exp_sum, ← Real.exp_sum]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hc : Real.exp (crossNormSq Ξ / 2) = Real.exp (∑ i : Fin M, Ξ i.succ 0 ^ 2 / 2) *
      Real.exp (∑ j : Fin N, Ξ 0 j.succ ^ 2 / 2) * Real.exp (Ξ 0 0 ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold crossNormSq
    rw [← Finset.sum_div, ← Finset.sum_div]
    ring
  rw [hc, pow_add, pow_add, div_pow, div_pow]
  field_simp

end Grammar
