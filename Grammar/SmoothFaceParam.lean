/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceTheorem

/-!
# The parametrised face theorem: inner functions depending on the outer point

The generic face theorem `face_expansion` integrates ONE inner function `Z(t)` against a flat outer
amplitude. In the empirical engine the inner kernel depends on the outer point `w` (through the
field factor `G(w;·)`), so the power–log coefficients are FUNCTIONS `c(w) μ j` of `w` and the
two-regime remainder carries the flatness factor `∏ wᵢ^{pᵢ}` itself:
`|Z(w,t) − ∑ c(w) μ j t^{−μ} (log t)^j| ≤ C ∏ wᵢ^{pᵢ} t^{−L} (1+|log t|)^D`,
`|c(w) μ j| ≤ M ∏ wᵢ^{pᵢ}`.
★★ `face_expansion_param`: then
`∫ w^h Z(w, N w^a) dw = ∑_μ N^{−μ} ∑_j ∑_q C(j,q)(log N)^q ∫ c(w) μ j w^h (w^a)^{−μ} S(w)^{j−q} dw`
`  + O(C (1+log N)^D N^{−L} faceRemWeight)` under `aᵢ L < pᵢ + hᵢ + 1`. The original face theorem
is the case `Z(w,t) = G(w) Z'(t)`, `c(w) = G(w) c`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset

namespace Grammar

namespace SmoothEngine

variable {ι : Type*} [Fintype ι]

/-- Pointwise: the `w`-dependent power–log sum at `t = N w^a` as a triple sum of coefficient
integrands. -/
theorem mul_powLog_param_eq (h a : ι → ℕ) (Λ : Finset ℝ) (D : ℕ) (c : (ι → ℝ) → ℝ → ℕ → ℝ)
    {N : ℝ} (hN : 1 ≤ N) {w : ι → ℝ} (hpos : ∀ i, 0 < w i) :
    mono h w * powLog Λ D (c w) (N * mono a w) =
      ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (N ^ (-μ) * (j.choose q) * log N ^ q) *
          (c w μ j * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q)) := by
  unfold powLog
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.mul_rpow (by linarith) (mono_pos a hpos).le,
    Real.log_mul (by linarith) (mono_pos a hpos).ne', log_mono a hpos, add_pow, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The `w`-dependent power–log main term is a.e.-strongly measurable on the box. -/
theorem aestronglyMeasurable_powLog_param {b : ℝ} (a : ι → ℕ) (Λ : Finset ℝ) (D : ℕ)
    {c : (ι → ℝ) → ℝ → ℕ → ℝ}
    (hcm : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1),
      AEStronglyMeasurable (fun w => c w μ j) (volume.restrict (box ι b))) {N : ℝ} :
    AEStronglyMeasurable (fun w => powLog Λ D (c w) (N * mono a w))
      (volume.restrict (box ι b)) := by
  unfold powLog
  have hT : Measurable fun w : ι → ℝ => N * mono a w := measurable_const.mul (measurable_mono a)
  refine Finset.aestronglyMeasurable_fun_sum Λ (f := fun μ w => ∑ j ∈ range (D + 1),
    c w μ j * (N * mono a w) ^ (-μ) * log (N * mono a w) ^ j) fun μ hμ => ?_
  refine Finset.aestronglyMeasurable_fun_sum (range (D + 1)) (f := fun j w =>
    c w μ j * (N * mono a w) ^ (-μ) * log (N * mono a w) ^ j) fun j hj => ?_
  exact ((hcm μ hμ j hj).mul (hT.pow_const _).aestronglyMeasurable).mul
    ((measurable_log.comp hT).pow_const _).aestronglyMeasurable

/-- The integral of the `w`-dependent main term. -/
theorem integral_main_param {c : (ι → ℝ) → ℝ → ℕ → ℝ} {p h a : ι → ℕ} {b M : ℝ} (hb : 0 < b)
    {Λ : Finset ℝ} {D : ℕ}
    (hcm : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1),
      AEStronglyMeasurable (fun w => c w μ j) (volume.restrict (box ι b)))
    (hcM : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1), ∀ w ∈ box ι b, |c w μ j| ≤ M * mono p w)
    (hΛ : ∀ μ ∈ Λ, ∀ i, (a i : ℝ) * μ < p i + h i + 1) {N : ℝ} (hN : 1 ≤ N) :
    ∫ w in box ι b, mono h w * powLog Λ D (c w) (N * mono a w) =
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (j.choose q) * log N ^ q * faceCoeffInt (fun w => c w μ j) h a b μ (j - q) := by
  have hint : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1), ∀ q ∈ range (j + 1),
      IntegrableOn (fun w => (N ^ (-μ) * (j.choose q) * log N ^ q) *
        (c w μ j * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q))) (box ι b) :=
    fun μ hμ j hj q _ => (integrable_faceCoeff hb (hcm μ hμ j hj) (hcM μ hμ j hj) (hΛ μ hμ)
      (by have := mem_range.1 hj; omega : j - q ≤ D)).const_mul _
  calc ∫ w in box ι b, mono h w * powLog Λ D (c w) (N * mono a w)
      = ∫ w in box ι b, ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
          (N ^ (-μ) * (j.choose q) * log N ^ q) *
            (c w μ j * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q)) :=
        setIntegral_congr_fun (measurableSet_box b) fun w hw =>
          mul_powLog_param_eq h a Λ D c hN (pos_of_mem_box hw)
    _ = ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
          (N ^ (-μ) * (j.choose q) * log N ^ q) *
            faceCoeffInt (fun w => c w μ j) h a b μ (j - q) := by
        rw [integral_finsetSum _ fun μ hμ => integrable_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [integral_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [integral_finsetSum _ fun q hq => hint μ hμ j hj q hq]
        refine Finset.sum_congr rfl fun q _ => ?_
        exact MeasureTheory.integral_const_mul _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring

/-- The pointwise remainder bound on the box, with the flatness carried by the inner estimate. -/
theorem rem_bound_param {Z : (ι → ℝ) → ℝ → ℝ} {c : (ι → ℝ) → ℝ → ℕ → ℝ} {p h a : ι → ℕ}
    {b C L N : ℝ} {Λ : Finset ℝ} {D : ℕ} (hC : 0 ≤ C)
    (hZ2 : ∀ w ∈ box ι b, ∀ t : ℝ, 0 < t →
      |Z w t - powLog Λ D (c w) t| ≤ C * mono p w * t ^ (-L) * (1 + |log t|) ^ D)
    (hN : 1 ≤ N) {w : ι → ℝ} (hw : w ∈ box ι b) :
    |mono h w * (Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w))| ≤
      C * (1 + log N) ^ D * N ^ (-L) *
        ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D) := by
  have hpos := pos_of_mem_box hw
  have hm := mono_pos a hpos
  have hp := mono_pos p hpos
  have ht : 0 < N * mono a w := by positivity
  have hrp : (N * mono a w) ^ (-L) = N ^ (-L) * mono a w ^ (-L) :=
    Real.mul_rpow (by linarith) hm.le
  have hlog : 1 + |log (N * mono a w)| ≤ (1 + log N) * (1 + |logSum a w|) := by
    rw [Real.log_mul (by linarith) hm.ne', log_mono a hpos]
    exact one_add_abs_log_add_le hN
  have hpow : (1 + |log (N * mono a w)|) ^ D ≤ (1 + log N) ^ D * (1 + |logSum a w|) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlog D
  have hZ' : |Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w)| ≤
      C * mono p w * (N ^ (-L) * mono a w ^ (-L)) *
        ((1 + log N) ^ D * (1 + |logSum a w|) ^ D) := by
    refine (hZ2 w hw _ ht).trans ?_
    rw [hrp]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hmh := mono_pos h hpos
  rw [abs_mul, abs_of_pos hmh]
  calc mono h w * |Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w)|
      ≤ mono h w * (C * mono p w * (N ^ (-L) * mono a w ^ (-L)) *
          ((1 + log N) ^ D * (1 + |logSum a w|) ^ D)) := mul_le_mul_of_nonneg_left hZ' hmh.le
    _ = C * (1 + log N) ^ D * N ^ (-L) *
          ((mono p w * mono h w * mono a w ^ (-L)) * (1 + |logSum a w|) ^ D) := by ring
    _ = _ := by rw [mono_mul_mono_mul_rpow p h a L hpos]

/-- ★★ **The parametrised face theorem**: an outer-point-dependent inner function `Z(w,t)` with
a global power–log estimate whose constant carries the flatness `∏ wᵢ^{pᵢ}`, and whose coefficient
functions `c(w) μ j` are flat and measurable, integrated on the box `(0,b]^ι` against `w^h` at the
effective parameter `N w^a`, has the power–log expansion with coefficients the face coefficient
integrals of the coefficient functions and remainder `≤ C (1 + log N)^D N^{−L} faceRemWeight`
for `N ≥ 1`, under `aᵢ L < pᵢ + hᵢ + 1`. -/
theorem face_expansion_param {Z : (ι → ℝ) → ℝ → ℝ} {c : (ι → ℝ) → ℝ → ℕ → ℝ} {p h a : ι → ℕ}
    {b M C L N : ℝ} {Λ : Finset ℝ} {D : ℕ} (hb : 0 < b) (hC : 0 ≤ C)
    (hZm : AEStronglyMeasurable (fun w => Z w (N * mono a w)) (volume.restrict (box ι b)))
    (hcm : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1),
      AEStronglyMeasurable (fun w => c w μ j) (volume.restrict (box ι b)))
    (hcM : ∀ μ ∈ Λ, ∀ j ∈ range (D + 1), ∀ w ∈ box ι b, |c w μ j| ≤ M * mono p w)
    (hZ2 : ∀ w ∈ box ι b, ∀ t : ℝ, 0 < t →
      |Z w t - powLog Λ D (c w) t| ≤ C * mono p w * t ^ (-L) * (1 + |log t|) ^ D)
    (hΛ : ∀ μ ∈ Λ, μ ≤ L) (hA : ∀ i, (a i : ℝ) * L < p i + h i + 1) (hN : 1 ≤ N) :
    |(∫ w in box ι b, mono h w * Z w (N * mono a w)) -
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (j.choose q) * log N ^ q * faceCoeffInt (fun w => c w μ j) h a b μ (j - q)| ≤
      C * (1 + log N) ^ D * N ^ (-L) * faceRemWeight p h a b L D := by
  have hΛ' : ∀ μ ∈ Λ, ∀ i, (a i : ℝ) * μ < p i + h i + 1 := fun μ hμ i =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hΛ μ hμ) (Nat.cast_nonneg _)) (hA i)
  have hmain : IntegrableOn (fun w => mono h w * powLog Λ D (c w) (N * mono a w)) (box ι b) := by
    have hsum : IntegrableOn (fun w => ∑ μ ∈ Λ, ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        (N ^ (-μ) * (j.choose q) * log N ^ q) *
          (c w μ j * mono h w * mono a w ^ (-μ) * logSum a w ^ (j - q))) (box ι b) :=
      integrable_finsetSum _ fun μ hμ => integrable_finsetSum _ fun j hj =>
        integrable_finsetSum _ fun q _ => (integrable_faceCoeff hb (hcm μ hμ j hj)
          (hcM μ hμ j hj) (hΛ' μ hμ) (by have := mem_range.1 hj; omega : j - q ≤ D)).const_mul _
    exact hsum.congr ((ae_restrict_mem (measurableSet_box b)).mono fun w hw =>
      (mul_powLog_param_eq h a Λ D c hN (pos_of_mem_box hw)).symm)
  have hremW : IntegrableOn (fun w => C * (1 + log N) ^ D * N ^ (-L) *
      ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D)) (box ι b) :=
    (integrableOn_prod_rpow_mul_log_pow (c := fun i => (p i + h i : ℝ) - a i * L)
      (fun i => by have := hA i; linarith) (fun i => (a i : ℝ)) D hb.le).const_mul _
  have hremb : ∀ᵐ w ∂(volume.restrict (box ι b)),
      ‖mono h w * (Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w))‖ ≤
        C * (1 + log N) ^ D * N ^ (-L) *
          ((∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D) :=
    (ae_restrict_mem (measurableSet_box b)).mono fun w hw => by
      rw [Real.norm_eq_abs]; exact rem_bound_param hC hZ2 hN hw
  have hrem : IntegrableOn
      (fun w => mono h w * (Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w))) (box ι b) := by
    refine Integrable.mono' hremW ?_ hremb
    exact (measurable_mono h).aestronglyMeasurable.mul
      (hZm.sub (aestronglyMeasurable_powLog_param a Λ D hcm))
  have htot : IntegrableOn (fun w => mono h w * Z w (N * mono a w)) (box ι b) := by
    refine (hmain.add hrem).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]; ring
  rw [← integral_main_param hb hcm hcM hΛ' hN, ← integral_sub htot hmain]
  have heq : (fun w => mono h w * Z w (N * mono a w) -
      mono h w * powLog Λ D (c w) (N * mono a w)) =
      fun w => mono h w * (Z w (N * mono a w) - powLog Λ D (c w) (N * mono a w)) := by
    funext w; ring
  rw [heq, faceRemWeight, ← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hremW hremb

end SmoothEngine

end Grammar
