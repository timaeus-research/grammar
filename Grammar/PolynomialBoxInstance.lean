/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LocalAnalyticInputs

/-!
# Polynomial instances of the holomorphic-data expansion (CCCXXXV; consult #99 stopping gate 5)

Real polynomials on `ℝ^d` are the real parts of their complexifications on all of `ℂ^d`
(`eval_complexify_map`), and polynomial functions are entire (`differentiable_eval`), so a real
polynomial prior and a real polynomial observable form a `HolomorphicBoxExtension` with `Ω = ℂ^d`
(`HolomorphicBoxExtension.ofPolynomials`; the flat prior `ϕ = 1`:
`HolomorphicBoxExtension.flatPolynomial`). The local-input theorem (CCCXXXIV) then gives the
coordinate-free expansion of `∫_{[0,a]^d} Q(w) P(w) e^{−nK} dw` for every real polynomial `P`
nonnegative on the box and every real polynomial `Q` (★★ `hasCoordFreeExpansion_polynomial`),
in particular of `∫_{[0,a]^d} Q(w) e^{−nK} dw` for every real polynomial `Q`
(★★ `hasCoordFreeExpansion_flat_polynomial`), with the produced certificates of CCCXXXIV.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology MvPolynomial

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} (a : ℝ)

/-- A real polynomial is the real part of its complexification along `complexify`. -/
theorem eval_complexify_map (P : MvPolynomial (Fin d) ℝ) (w : Fin d → ℝ) :
    eval (complexify w) (map (algebraMap ℝ ℂ) P) = ((eval w P : ℝ) : ℂ) := by
  change eval (fun i => (w i : ℂ)) (map (algebraMap ℝ ℂ) P) = ((eval w P : ℝ) : ℂ)
  have := eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ) w P
  simpa [Function.comp_def, eval_map] using this.symm

/-- Polynomial functions on `ℂ^d` are entire. -/
theorem differentiable_eval (Q : MvPolynomial (Fin d) ℂ) :
    Differentiable ℂ fun z : Fin d → ℂ => eval z Q := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [eval_C]
    exact differentiable_const c
  | add p q hp hq =>
    have h : (fun z : Fin d → ℂ => eval z (p + q)) = fun z => eval z p + eval z q :=
      funext fun z => eval_add
    rw [h]
    exact hp.add hq
  | mul_X p i hp =>
    have h : (fun z : Fin d → ℂ => eval z (p * X i)) = fun z => eval z p * z i :=
      funext fun z => by rw [eval_mul, eval_X]
    rw [h]
    exact hp.mul (differentiable_apply i)

/-- ★ **The polynomial packet**: a real polynomial prior and observable, extended by their
complexifications on `Ω = ℂ^d`. -/
noncomputable def HolomorphicBoxExtension.ofPolynomials (P Q : MvPolynomial (Fin d) ℝ) :
    HolomorphicBoxExtension a (fun w => eval w P) (fun w => eval w Q) where
  Ω := univ
  isOpen_Ω := isOpen_univ
  box_subset := fun _ _ => mem_univ _
  Hϕ := fun z => eval z (map (algebraMap ℝ ℂ) P)
  Hφ := fun z => eval z (map (algebraMap ℝ ℂ) Q)
  holϕ := (differentiable_eval _).differentiableOn
  holφ := (differentiable_eval _).differentiableOn
  eqϕ := fun w _ => by rw [eval_complexify_map, Complex.ofReal_re]
  eqφ := fun w _ => by rw [eval_complexify_map, Complex.ofReal_re]

/-- **The flat prior with a polynomial observable.** -/
noncomputable def HolomorphicBoxExtension.flatPolynomial (Q : MvPolynomial (Fin d) ℝ) :
    HolomorphicBoxExtension a (fun _ => (1 : ℝ)) (fun w => eval w Q) where
  Ω := univ
  isOpen_Ω := isOpen_univ
  box_subset := fun _ _ => mem_univ _
  Hϕ := fun _ => 1
  Hφ := fun z => eval z (map (algebraMap ℝ ℂ) Q)
  holϕ := differentiableOn_const 1
  holφ := (differentiable_eval _).differentiableOn
  eqϕ := fun _ _ => by simp
  eqφ := fun w _ => by rw [eval_complexify_map, Complex.ofReal_re]

variable {a} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hd : 0 < d) (ha : 0 < a)

/-- ★★ **Polynomial prior and observable**: for real polynomials `P ≥ 0` on the box and `Q`, the
integral `∫_{[0,a]^d} Q P e^{−nK}` has the coordinate-free expansion for some collar level, with
produced certificates. -/
theorem hasCoordFreeExpansion_polynomial (P Q : MvPolynomial (Fin d) ℝ)
    (hP : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ eval w P) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
          ((HolomorphicBoxExtension.ofPolynomials a P Q).toRep.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (producedCertificate k hk (HolomorphicBoxExtension.ofPolynomials a P Q) hd ha hP δ hδ hδa
          hsmall).stratumMeasure
        (producedCoeffCertificate k hk (HolomorphicBoxExtension.ofPolynomials a P Q) hd ha hP δ hδ
          hδa hsmall).field
        (spectrumLe (commonQ (producedCertificate k hk (HolomorphicBoxExtension.ofPolynomials a P Q)
          hd ha hP δ hδ hδa hsmall).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) (fun w => eval w P) (fun w => eval w Q) :=
  hasCoordFreeExpansion_of_holomorphicBoxExtension_local k hk
    (HolomorphicBoxExtension.ofPolynomials a P Q) hd ha hP

/-- ★★ **Flat prior, polynomial observable**: `∫_{[0,a]^d} Q e^{−nK}` has the coordinate-free
expansion for every real polynomial `Q`, with produced certificates. -/
theorem hasCoordFreeExpansion_flat_polynomial (Q : MvPolynomial (Fin d) ℝ) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
          ((HolomorphicBoxExtension.flatPolynomial a Q).toRep.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (producedCertificate k hk (HolomorphicBoxExtension.flatPolynomial a Q) hd ha
          (fun _ _ => zero_le_one) δ hδ hδa hsmall).stratumMeasure
        (producedCoeffCertificate k hk (HolomorphicBoxExtension.flatPolynomial a Q) hd ha
          (fun _ _ => zero_le_one) δ hδ hδa hsmall).field
        (spectrumLe (commonQ (producedCertificate k hk (HolomorphicBoxExtension.flatPolynomial a Q)
          hd ha (fun _ _ => zero_le_one) δ hδ hδa hsmall).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) (fun _ => (1 : ℝ)) (fun w => eval w Q) :=
  hasCoordFreeExpansion_of_holomorphicBoxExtension_local k hk
    (HolomorphicBoxExtension.flatPolynomial a Q) hd ha fun _ _ => zero_le_one

end WaterFilling

end Grammar
