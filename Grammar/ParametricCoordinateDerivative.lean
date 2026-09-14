/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateFrechetBridge

/-!
# Parametric coordinate derivatives are Fréchet derivatives of the joint function
(consult #124 unit C5g)

The smooth engine differentiates an amplitude `F : ℝ^d → ℝ` with coordinate partials
`pd i F v = d/dt F(v with v_i := t)|_{t = v_i}`, iterated to `pdPow` and `pdMulti m l`. The
chart-face distributions of consult #124 apply the engine to a SLICE `v ↦ G (s, v)` of a smooth
JOINT function `G : B × ℝ^d → ℝ` of a parameter `s : B` (a real normed space, e.g. `ι → ℝ`) and
the engine variable `v`. Downstream one needs to know how the coordinate derivatives of the slice
depend on `(s, v)` jointly — not merely, as in `SmoothAmplitudeFamily`, that they are continuous
for each fixed `s`.

## The slice is a translate of a linear embedding

Writing `(s, v) = (s, 0) + inr v` with `inr : ℝ^d →L[ℝ] B × ℝ^d`, `v ↦ 0 ⊕ v`, the slice is the
composite `G ∘ (z ↦ (s, 0) + z) ∘ inr` (`slice_eq_comp`). Iterated Fréchet derivatives commute
with translation (`iteratedFDeriv_comp_add_left`) and with a continuous linear map on the right
(`ContinuousLinearMap.iteratedFDeriv_comp_right`), so

★ `iteratedFDeriv_slice_apply`: `D^n (v ↦ G (s, v)) v (w) = D^n G (s, v) (j ↦ (0, w j))`

for every word `w : Fin n → ℝ^d`. Combined with the coordinate–Fréchet bridge of
`CoordinateFrechetBridge` (`pdMulti_eq_iteratedFDeriv`: `∂^m_l F = D^{|m|} F (coordWord m l)`) this
gives the parametric bridge

★★ `pdMulti_slice_eq_iteratedFDeriv`:
  `∂^m_l (v ↦ G (s, v)) v = D^{|m|} G (s, v) (j ↦ (0, coordWord m l j))`,

with the first-order case `pd_slice_eq_fderiv`: `∂_i (v ↦ G (s, v)) v = D G (s, v) (0, e_i)`, proved
directly from the chain rule along the path `t ↦ (s, v with v_i := t)`, whose velocity is
`(0, e_i)` (`hasDerivAt_slice_update`).

## Consequences

The right-hand side is the continuous map `z ↦ D^{|m|} G z` (`ContDiff.continuous_iteratedFDeriv`)
followed by evaluation at the FIXED word `j ↦ (0, coordWord m l j)`, which is continuous linear
on the space of multilinear maps. Hence every mixed coordinate derivative of the slice is
★★ JOINTLY continuous in `(s, v)` (`continuous_pdMulti_slice`), and the word vectors have
sup-norm one (`norm_zero_prod_mk`, `norm_coordWord`), so the multilinear operator-norm
inequality gives

★ `abs_pdMulti_slice_le`: `|∂^m_l (v ↦ G (s, v)) v| ≤ ‖D^{|m|} G (s, v)‖`.

Finally, for a topological parameter space `S` with a continuous map `σ : S → B`, the slices
`s ↦ (v ↦ G (σ s, v))` form a `SmoothAmplitudeFamily S d b` for every box size `b`
(★ `SmoothAmplitudeFamily.ofSlice`, `ofSlice_apply`), whose joint-continuity field is exactly
`continuous_pdMulti_slice` composed with `(s, v) ↦ (σ s, v)`. Zero `sorry`/`axiom`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {G : B × (Fin d → ℝ) → ℝ}

/-! ### The slice as a translate of a linear embedding -/

variable (G) in
/-- The slice `v ↦ G (s, v)` is `G` composed with the translation by `(s, 0)` and the linear
embedding `inr : v ↦ (0, v)`. -/
theorem slice_eq_comp (s : B) :
    (fun v => G (s, v)) =
      (fun z => G ((s, 0) + z)) ∘ (ContinuousLinearMap.inr ℝ B (Fin d → ℝ)) := by
  funext v
  simp only [Function.comp, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

theorem contDiff_slice {n : WithTop ℕ∞} (hG : ContDiff ℝ n G) (s : B) :
    ContDiff ℝ n fun v => G (s, v) :=
  hG.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_translate {n : WithTop ℕ∞} (hG : ContDiff ℝ n G) (a : B × (Fin d → ℝ)) :
    ContDiff ℝ n fun z => G (a + z) :=
  hG.comp (contDiff_const.add contDiff_id)

/-- ★ The `n`-th Fréchet derivative of the slice `v ↦ G (s, v)` on a word `w` is the `n`-th
Fréchet derivative of the joint function at `(s, v)` on the word `j ↦ (0, w j)`. -/
theorem iteratedFDeriv_slice_apply {n : ℕ} (hG : ContDiff ℝ n G) (s : B) (v : Fin d → ℝ)
    (w : Fin n → Fin d → ℝ) :
    iteratedFDeriv ℝ n (fun v => G (s, v)) v w =
      iteratedFDeriv ℝ n G (s, v) fun j => ((0 : B), w j) := by
  rw [slice_eq_comp G s,
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ B (Fin d → ℝ))
      (contDiff_translate hG (s, 0)) v le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

/-! ### First order: the chain rule along a coordinate path -/

/-- The path `t ↦ (s, v with v_i := t)` has velocity `(0, e_i)`, so `t ↦ G (s, v with v_i := t)`
has derivative `D G (s, ·) (0, e_i)`. -/
theorem hasDerivAt_slice_update (hG : ContDiff ℝ 1 G) (i : Fin d) (s : B) (v : Fin d → ℝ)
    (t : ℝ) :
    HasDerivAt (fun t => G (s, Function.update v i t))
      (fderiv ℝ G (s, Function.update v i t) ((0 : B), Pi.single i 1)) t :=
  (hG.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_update v i t))

/-- ★ `∂_i (v ↦ G (s, v)) v = D G (s, v) (0, e_i)` for `G` of class `C¹`. -/
theorem pd_slice_eq_fderiv (hG : ContDiff ℝ 1 G) (i : Fin d) (s : B) (v : Fin d → ℝ) :
    pd i (fun v => G (s, v)) v = fderiv ℝ G (s, v) ((0 : B), Pi.single i 1) := by
  have h := hasDerivAt_slice_update hG i s v (v i)
  rw [Function.update_eq_self] at h
  unfold pd line
  exact h.deriv

/-! ### All orders: the parametric coordinate–Fréchet bridge -/

/-- ★★ The mixed coordinate derivative of the slice is the Fréchet derivative of the JOINT
function at `(s, v)` on the word `j ↦ (0, coordWord m l j)`. -/
theorem pdMulti_slice_eq_iteratedFDeriv (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (l : List (Fin d))
    (s : B) (v : Fin d → ℝ) :
    pdMulti m l (fun v => G (s, v)) v =
      iteratedFDeriv ℝ (wordLen m l) G (s, v) fun j => ((0 : B), coordWord m l j) := by
  rw [pdMulti_eq_iteratedFDeriv (contDiff_slice hG s) m l]
  exact iteratedFDeriv_slice_apply (hG.of_le (mod_cast le_top)) s v (coordWord m l)

theorem pdPow_slice_eq_iteratedFDeriv (hG : ContDiff ℝ ∞ G) (i : Fin d) (k : ℕ) (s : B)
    (v : Fin d → ℝ) :
    pdPow i k (fun v => G (s, v)) v =
      iteratedFDeriv ℝ k G (s, v) fun _ => ((0 : B), Pi.single i 1) := by
  rw [pdPow_eq_iteratedFDeriv (contDiff_slice hG s) i k]
  exact iteratedFDeriv_slice_apply (hG.of_le (mod_cast le_top)) s v _

/-! ### Joint continuity in the parameter and the variable -/

/-- Evaluation of the `n`-th derivative at a fixed word is continuous in the base point. -/
theorem continuous_iteratedFDeriv_apply_const {n : ℕ} (hG : ContDiff ℝ n G)
    (W : Fin n → B × (Fin d → ℝ)) : Continuous fun z => iteratedFDeriv ℝ n G z W :=
  (continuous_eval_const W).comp (hG.continuous_iteratedFDeriv le_rfl)

/-- ★★ Every mixed coordinate derivative of the slice is jointly continuous in `(s, v)`. -/
theorem continuous_pdMulti_slice (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (l : List (Fin d)) :
    Continuous fun z : B × (Fin d → ℝ) => pdMulti m l (fun v => G (z.1, v)) z.2 := by
  have h : (fun z : B × (Fin d → ℝ) => pdMulti m l (fun v => G (z.1, v)) z.2) =
      fun z => iteratedFDeriv ℝ (wordLen m l) G z fun j => ((0 : B), coordWord m l j) :=
    funext fun z => pdMulti_slice_eq_iteratedFDeriv hG m l z.1 z.2
  rw [h]
  exact continuous_iteratedFDeriv_apply_const (hG.of_le (mod_cast le_top)) _

theorem continuous_pd_slice (hG : ContDiff ℝ ∞ G) (i : Fin d) :
    Continuous fun z : B × (Fin d → ℝ) => pd i (fun v => G (z.1, v)) z.2 := by
  have h : (fun z : B × (Fin d → ℝ) => pd i (fun v => G (z.1, v)) z.2) =
      fun z => fderiv ℝ G z ((0 : B), Pi.single i 1) :=
    funext fun z => pd_slice_eq_fderiv (hG.of_le (mod_cast le_top)) i z.1 z.2
  rw [h]
  exact (hG.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ### The norm bound -/

omit [NormedSpace ℝ B] in
theorem norm_zero_prod_mk (x : Fin d → ℝ) : ‖((0 : B), x)‖ = ‖x‖ := by
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]

omit [NormedSpace ℝ B] in
theorem prod_norm_zero_prod_mk_coordWord (m : Fin d → ℕ) (l : List (Fin d)) :
    ∏ j, ‖((0 : B), coordWord m l j)‖ = 1 :=
  Finset.prod_eq_one fun j _ => by rw [norm_zero_prod_mk, norm_coordWord]

/-- ★ `|∂^m_l (v ↦ G (s, v)) v| ≤ ‖D^{|m|} G (s, v)‖`. -/
theorem abs_pdMulti_slice_le (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (l : List (Fin d)) (s : B)
    (v : Fin d → ℝ) :
    |pdMulti m l (fun v => G (s, v)) v| ≤ ‖iteratedFDeriv ℝ (wordLen m l) G (s, v)‖ := by
  rw [pdMulti_slice_eq_iteratedFDeriv hG m l s v, ← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ (wordLen m l) G (s, v) fun j => ((0 : B), coordWord m l j)‖
      ≤ ‖iteratedFDeriv ℝ (wordLen m l) G (s, v)‖ * ∏ j, ‖((0 : B), coordWord m l j)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (wordLen m l) G (s, v)‖ := by
        rw [prod_norm_zero_prod_mk_coordWord, mul_one]

/-- Over all coordinates, the order is `Σ_i m i`. -/
theorem abs_pdMulti_finRange_slice_le (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (s : B)
    (v : Fin d → ℝ) :
    |pdMulti m (List.finRange d) (fun v => G (s, v)) v| ≤
      ‖iteratedFDeriv ℝ (∑ i, m i) G (s, v)‖ := by
  rw [← wordLen_finRange]
  exact abs_pdMulti_slice_le hG m _ s v

/-! ### Packaging as a smooth amplitude family -/

namespace SmoothAmplitudeFamily

variable {S : Type*} [TopologicalSpace S]

/-- ★ The slices `v ↦ G (σ s, v)` of a smooth joint function along a continuous parameter map
`σ : S → B` form a smooth amplitude family on every box `[0, b]^d`. -/
def ofSlice {σ : S → B} (hσ : Continuous σ) (hG : ContDiff ℝ ∞ G) (b : ℝ) :
    SmoothAmplitudeFamily S d b where
  amp s v := G (σ s, v)
  smooth s := contDiff_slice hG (σ s)
  deriv_cont m :=
    ((continuous_pdMulti_slice hG m (List.finRange d)).comp
      ((hσ.comp continuous_fst).prodMk continuous_snd)).continuousOn

theorem ofSlice_apply {σ : S → B} (hσ : Continuous σ) (hG : ContDiff ℝ ∞ G) (b : ℝ) (s : S)
    (v : Fin d → ℝ) : ofSlice hσ hG b s v = G (σ s, v) := rfl

end SmoothAmplitudeFamily

end SmoothEngine

end Grammar
