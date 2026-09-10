import Grammar.BoxPerm
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tangential/normal splitting of the weighted box integral

For a resolved box with exponents `(h, k)`, split the coordinates into the normal ones
`N = {i | p i}` (where the phase exponent `kᵢ` may be positive) and the tangential ones
`T = {i | ¬ p i}` (where `kᵢ = 0`). Along the coordinate equivalence
`(0,b]^d ≅ (0,b]^N × (0,b]^T` the box measure is a product measure
(`measurePreserving_boxMeasure_split`), the monomial phase depends only on the normal
coordinates (`prod_pow_eq_prod_subtype_of_zero`), and the weighted box integral factors as

`∫ u^h e^{−β(c u^k)² + βa(c u^k)} du = (∏_{i∈T} b^{hᵢ+1}/(hᵢ+1)) · ∫_{(0,b]^N} w^h e^{…} dw`

(`boxIntegralFin_split`, `boxIntegralFin_split_eq`). This is the bookkeeping behind the paper's
tangential/normal decomposition of a weighted box: the tangential monomial weights integrate to
an explicit constant and the normal block carries the standard integral. The monomial weights are
kept in the integrand (as everywhere in the box files); a coordinate bounded away from zero is not
treated here — that is a change of variables, not a split.
-/

open MeasureTheory Set

namespace Grammar

/-- Lebesgue measure on the box `(0,b]^ι` for a general finite index type. -/
noncomputable def boxMeasureOn (ι : Type*) [Fintype ι] (b : ℝ) : Measure (ι → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 b)

theorem boxMeasureOn_fin (b : ℝ) (d : ℕ) : boxMeasureOn (Fin d) b = boxMeasure b d := rfl

instance boxMeasureOn_sigmaFinite (ι : Type*) [Fintype ι] (b : ℝ) :
    SigmaFinite (boxMeasureOn ι b) := by
  unfold boxMeasureOn
  infer_instance

variable {d : ℕ} (p : Fin d → Prop) [DecidablePred p]

/-- **The box measure splits as a product** along `(0,b]^d ≅ (0,b]^N × (0,b]^T`. -/
theorem measurePreserving_boxMeasure_split (b : ℝ) :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p)
      (boxMeasure b d) ((boxMeasureOn {i // p i} b).prod (boxMeasureOn {i // ¬ p i} b)) :=
  measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b)) p

/-- A monomial whose exponents vanish off `p` depends only on the `p`-coordinates. -/
theorem prod_pow_eq_prod_subtype_of_zero (k : Fin d → ℕ) (hk : ∀ i, ¬ p i → k i = 0)
    (u : Fin d → ℝ) : ∏ i, u i ^ k i = ∏ i : {i // p i}, u i ^ k i := by
  have h0 : ∏ i : {i // ¬ p i}, u i ^ k i = 1 :=
    Finset.prod_eq_one fun i _ => by rw [hk i i.2, pow_zero]
  rw [← Fintype.prod_subtype_mul_prod_subtype p fun i => u i ^ k i, h0, mul_one]

/-- The monomial weight splits into its normal and tangential factors. -/
theorem prod_pow_eq_prod_subtype_mul (h : Fin d → ℕ) (u : Fin d → ℝ) :
    ∏ i, u i ^ h i = (∏ i : {i // p i}, u i ^ h i) * ∏ i : {i // ¬ p i}, u i ^ h i :=
  (Fintype.prod_subtype_mul_prod_subtype p fun i => u i ^ h i).symm

/-- **Tangential/normal factorisation of the box integral.** If the phase exponents vanish on the
tangential coordinates, the weighted box integral is the tangential monomial integral times the
normal box integral. -/
theorem boxIntegralFin_split (β a b c : ℝ) (k h : Fin d → ℕ) (hk : ∀ i, ¬ p i → k i = 0) :
    boxIntegralFin β a b c k h =
      (∫ v : {i // ¬ p i} → ℝ, ∏ i, v i ^ h i ∂boxMeasureOn {i // ¬ p i} b) *
        ∫ w : {i // p i} → ℝ, (∏ i, w i ^ h i) * quadKernel β a (c * ∏ i, w i ^ k i)
          ∂boxMeasureOn {i // p i} b := by
  have hmp := measurePreserving_boxMeasure_split p b
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  unfold boxIntegralFin
  have hG : ∀ u : Fin d → ℝ, (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i) =
      ((∏ i, (e u).1 i ^ h i) * quadKernel β a (c * ∏ i, (e u).1 i ^ k i)) *
        ∏ i, (e u).2 i ^ h i := by
    intro u
    change (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i) =
      ((∏ i : {i // p i}, u i ^ h i) * quadKernel β a (c * ∏ i : {i // p i}, u i ^ k i)) *
        ∏ i : {i // ¬ p i}, u i ^ h i
    rw [prod_pow_eq_prod_subtype_mul p h u, prod_pow_eq_prod_subtype_of_zero p k hk u]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hG), hmp.integral_comp'
      (fun y : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) =>
        ((∏ i, y.1 i ^ h i) * quadKernel β a (c * ∏ i, y.1 i ^ k i)) * ∏ i, y.2 i ^ h i),
    integral_prod_mul (fun w : {i // p i} → ℝ => (∏ i, w i ^ h i) *
      quadKernel β a (c * ∏ i, w i ^ k i)) (fun v : {i // ¬ p i} → ℝ => ∏ i, v i ^ h i),
    mul_comm]

/-- **The tangential factor**: `∫_{(0,b]^T} ∏ vᵢ^{hᵢ} dv = ∏_{i∈T} b^{hᵢ+1}/(hᵢ+1)` for `b ≥ 0`. -/
theorem integral_boxMeasureOn_prod_pow (ι : Type*) [Fintype ι] {b : ℝ} (hb : 0 ≤ b)
    (h : ι → ℕ) :
    ∫ v : ι → ℝ, ∏ i, v i ^ h i ∂boxMeasureOn ι b = ∏ i : ι, b ^ (h i + 1) / ((h i : ℝ) + 1) := by
  unfold boxMeasureOn
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => t ^ h i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_of_le hb, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]

/-- **Tangential/normal factorisation with the explicit tangential constant.** -/
theorem boxIntegralFin_split_eq (β a c : ℝ) {b : ℝ} (hb : 0 ≤ b) (k h : Fin d → ℕ)
    (hk : ∀ i, ¬ p i → k i = 0) :
    boxIntegralFin β a b c k h =
      (∏ i : {i // ¬ p i}, b ^ (h i + 1) / ((h i : ℝ) + 1)) *
        ∫ w : {i // p i} → ℝ, (∏ i, w i ^ h i) * quadKernel β a (c * ∏ i, w i ^ k i)
          ∂boxMeasureOn {i // p i} b := by
  rw [boxIntegralFin_split p β a b c k h hk, integral_boxMeasureOn_prod_pow _ hb]

end Grammar
