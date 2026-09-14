/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothAmplitudeFamily
import Grammar.SignedBoxPackets
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Smooth amplitude families from affine chart coordinates (consult #117 U6b.1)

The affine chart-coordinate map of a face of the box: given an enumeration
`e : Fin da ≃ {i // i ∈ J}` of the active coordinates, a sign pattern `σ` and fixed complementary
coordinates `s`, the map `affineMap e σ s : ℝ^{da} → ℝ^d` sends `v` to the point whose
`J`-coordinates are `σ_i · v_{e⁻¹ i}` and whose other coordinates are `s`. It is smooth
(`contDiff_affineMap`), jointly continuous in `(s, v)` (`continuous_affineMap_pair`), and the
coordinate derivatives of a pullback `G ∘ affineMap` are the reflected pushed-forward derivatives
(★ `pd_comp_affineMap`, `pdPow_comp_affineMap`, ★★ `pdMulti_comp_affineMap`:
`∂^m (G ∘ A) = (∏ σ_{e j}^{m_j}) · (∂^{extendIdx e m} G) ∘ A`). Consequently the pullback of a
smooth `G` along a continuous family of complementary coordinates is a `SmoothAmplitudeFamily`
(★★★ `SmoothAmplitudeFamily.ofAffine`). Zero `sorry`/`axiom`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d da : ℕ} {J : Finset (Fin d)}

/-! ### The affine chart-coordinate map -/

/-- The affine chart-coordinate map: face coordinates `v ∘ e.symm` reflected by `σ`,
complementary coordinates fixed at `s`. -/
def affineMap (e : Fin da ≃ {i // inJ J i}) (σ : WaterFilling.CoordSign d)
    (s : {i // ¬ inJ J i} → ℝ) (v : Fin da → ℝ) : Fin d → ℝ :=
  glue J (fun i => WaterFilling.sgn σ i * v (e.symm i)) s

variable (e : Fin da ≃ {i // inJ J i}) (σ : WaterFilling.CoordSign d) (s : {i // ¬ inJ J i} → ℝ)

theorem affineMap_apply_of_mem (v : Fin da → ℝ) {i : Fin d} (hi : i ∈ J) :
    affineMap e σ s v i = WaterFilling.sgn σ i * v (e.symm ⟨i, hi⟩) :=
  glue_apply_of_mem J _ _ hi

theorem affineMap_apply_face (v : Fin da → ℝ) (j : Fin da) :
    affineMap e σ s v (e j).1 = WaterFilling.sgn σ (e j).1 * v j := by
  unfold affineMap
  rw [glue_apply_subtype, Equiv.symm_apply_apply]

theorem affineMap_apply_of_not_mem (v : Fin da → ℝ) {i : Fin d} (hi : i ∉ J) :
    affineMap e σ s v i = s ⟨i, hi⟩ :=
  glue_apply_of_not_mem J _ _ hi

theorem affineMap_update (v : Fin da → ℝ) (j : Fin da) (t : ℝ) :
    affineMap e σ s (Function.update v j t) =
      Function.update (affineMap e σ s v) (e j).1 (WaterFilling.sgn σ (e j).1 * t) := by
  funext i
  by_cases hij : i = (e j).1
  · subst hij
    simp only [affineMap_apply_face, Function.update_self]
  · rw [Function.update_of_ne hij]
    by_cases hi : i ∈ J
    · rw [affineMap_apply_of_mem e σ s _ hi, affineMap_apply_of_mem e σ s _ hi,
        Function.update_of_ne]
      intro h
      apply hij
      have : (⟨i, hi⟩ : {i // inJ J i}) = e j := by rw [← h, Equiv.apply_symm_apply]
      exact congrArg Subtype.val this
    · rw [affineMap_apply_of_not_mem e σ s _ hi, affineMap_apply_of_not_mem e σ s _ hi]

theorem contDiff_affineMap : ContDiff ℝ ∞ (affineMap e σ s) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i ∈ J
  · simp only [affineMap_apply_of_mem e σ s _ hi]
    exact contDiff_const.mul (contDiff_apply ℝ ℝ _)
  · simp only [affineMap_apply_of_not_mem e σ s _ hi]
    exact contDiff_const

theorem continuous_affineMap_pair :
    Continuous fun z : ({i // ¬ inJ J i} → ℝ) × (Fin da → ℝ) => affineMap e σ z.1 z.2 :=
  (continuous_glue J).comp <| Continuous.prodMk
    (continuous_pi fun i => continuous_const.mul ((continuous_apply (e.symm i)).comp
      continuous_snd)) continuous_fst

/-! ### Constants and coordinate derivatives -/

theorem pd_const_mul {n : ℕ} (c : ℝ) (H : (Fin n → ℝ) → ℝ) (j : Fin n) :
    pd j (fun v => c * H v) = fun v => c * pd j H v := by
  funext v
  simp only [pd]
  exact deriv_const_mul_field c

theorem pdPow_const_mul {n : ℕ} (c : ℝ) (H : (Fin n → ℝ) → ℝ) (j : Fin n) (q : ℕ) :
    pdPow j q (fun v => c * H v) = fun v => c * pdPow j q H v := by
  induction q with
  | zero => rfl
  | succ q ih => rw [pdPow_succ', ih, pd_const_mul, pdPow_succ']

/-! ### The chain rule along the affine map -/

theorem line_comp_affineMap (G : (Fin d → ℝ) → ℝ) (j : Fin da) (v : Fin da → ℝ) :
    line (fun v => G (affineMap e σ s v)) j v =
      fun t => line G (e j).1 (affineMap e σ s v) (WaterFilling.sgn σ (e j).1 * t) := by
  funext t
  simp only [line, affineMap_update]

theorem pd_comp_affineMap (G : (Fin d → ℝ) → ℝ) (j : Fin da) :
    pd j (fun v => G (affineMap e σ s v)) =
      fun v => WaterFilling.sgn σ (e j).1 * pd (e j).1 G (affineMap e σ s v) := by
  funext v
  change deriv (line (fun v => G (affineMap e σ s v)) j v) (v j) = _
  rw [line_comp_affineMap, deriv_comp_mul_left, smul_eq_mul]
  simp only [pd, affineMap_apply_face]

theorem pdPow_comp_affineMap (G : (Fin d → ℝ) → ℝ) (j : Fin da) (q : ℕ) :
    pdPow j q (fun v => G (affineMap e σ s v)) =
      fun v => WaterFilling.sgn σ (e j).1 ^ q * pdPow (e j).1 q G (affineMap e σ s v) := by
  induction q with
  | zero => funext v; simp [pdPow_zero]
  | succ q ih =>
    rw [pdPow_succ', ih, pd_const_mul, pd_comp_affineMap, pdPow_succ']
    funext v
    ring

/-- The multi-index on `ℝ^d` extending `m` on the face coordinates by zero. -/
def extendIdx (e : Fin da ≃ {i // inJ J i}) (m : Fin da → ℕ) : Fin d → ℕ :=
  fun i => if h : inJ J i then m (e.symm ⟨i, h⟩) else 0

theorem extendIdx_face (m : Fin da → ℕ) (j : Fin da) : extendIdx e m (e j).1 = m j := by
  simp only [extendIdx, dif_pos (e j).2, Subtype.coe_eta, Equiv.symm_apply_apply]

theorem extendIdx_of_not_mem (m : Fin da → ℕ) {i : Fin d} (hi : i ∉ J) : extendIdx e m i = 0 :=
  dif_neg hi

theorem pdMulti_comp_affineMap (G : (Fin d → ℝ) → ℝ) (m : Fin da → ℕ) (l : List (Fin da)) :
    pdMulti m l (fun v => G (affineMap e σ s v)) =
      fun v => (l.map fun j => WaterFilling.sgn σ (e j).1 ^ m j).prod *
        pdMulti (extendIdx e m) (l.map fun j => (e j).1) G (affineMap e σ s v) := by
  induction l with
  | nil => funext v; simp [pdMulti_nil]
  | cons j l ih =>
    rw [pdMulti_cons, ih, pdPow_const_mul, pdPow_comp_affineMap]
    simp only [List.map_cons, List.prod_cons, pdMulti_cons, extendIdx_face]
    funext v
    ring

theorem pdMulti_finRange_comp_affineMap (G : (Fin d → ℝ) → ℝ) (m : Fin da → ℕ) :
    pdMulti m (List.finRange da) (fun v => G (affineMap e σ s v)) =
      fun v => (∏ j, WaterFilling.sgn σ (e j).1 ^ m j) *
        pdMulti (extendIdx e m) ((List.finRange da).map fun j => (e j).1) G
          (affineMap e σ s v) := by
  rw [pdMulti_comp_affineMap, Fin.prod_univ_def]

/-! ### The amplitude family -/

/-- The pullback of a smooth `G` along the affine chart maps of a continuous family
`s ↦ sc s` of complementary coordinates, as a smooth amplitude family on `ℝ^{da}`. -/
noncomputable def SmoothAmplitudeFamily.ofAffine {S : Type*} [TopologicalSpace S]
    {sc : S → {i // ¬ inJ J i} → ℝ} (hsc : Continuous sc) (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (b : ℝ) :
    SmoothAmplitudeFamily S da b where
  amp s v := G (affineMap e σ (sc s) v)
  smooth s := hG.comp (contDiff_affineMap e σ (sc s))
  deriv_cont m := by
    simp only [pdMulti_comp_affineMap]
    exact (continuous_const.mul ((contDiff_pdMulti hG _ _).continuous.comp
      ((continuous_affineMap_pair e σ).comp
        ((hsc.comp continuous_fst).prodMk continuous_snd)))).continuousOn

theorem SmoothAmplitudeFamily.ofAffine_amp {S : Type*} [TopologicalSpace S]
    {sc : S → {i // ¬ inJ J i} → ℝ} (hsc : Continuous sc) {G : (Fin d → ℝ) → ℝ}
    (hG : ContDiff ℝ ∞ G) (b : ℝ) (s : S) (v : Fin da → ℝ) :
    (SmoothAmplitudeFamily.ofAffine hsc e σ hG b) s v = G (affineMap e σ (sc s) v) := rfl

end SmoothEngine

end Grammar
