/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeCharts
import Grammar.PartitionAssemblyRegression

/-!
# The Gaussian identification of the blow-up coefficient (CCLXXXIV)

The fourth unit of the derived-certificate programme (consult #86, A4): for `F = p = 1` the
assembled coefficient of the `d` blow-up charts of the unit cube (CCLXXXIII) is `π^{d/2}`:

* the one-dimensional truncated Gaussian `∫_{−1}^{1} e^{−N t²} dt ~ √π N^{−1/2}`, transported from
  the two-chart regression CCLXXII (`integral_Icc_exp_isEquivalent`);
* Fubini on the cube: `∫_{[−1,1]^d} e^{−N ∑ x_i²} = (∫_{−1}^{1} e^{−N t²} dt)^d`
  (`cubeIntegral_eq_pow`, `integral_fintype_prod_volume_eq_prod`), hence the Gaussian certificate
  `∫_{[−1,1]^d} e^{−N ∑ x_i²} ~ π^{d/2} N^{−d/2}` (`cubeIntegral_isEquivalent_gaussian`);
* ★★★ `coeff_eq_pi_rpow`: by uniqueness of certificates, the sum of the `d` whole-box source
  coefficients of the blow-up charts equals `π^{d/2}` — the classical constant recovered from the
  resolution, `d/2 = λ*` from `(h+1)/e = d/2`, `k* = 0`.

The Gaussian factorisation is used only to identify the constant; the leading pair and the
positivity of the coefficient come from the resolution (CCLXXXIII).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

namespace BlowUpCube

variable {d : ℕ}

/-- **The truncated one-dimensional Gaussian**: `∫_{−1}^{1} e^{−N t²} dt ~ √π N^{−1/2}` (CCLXXII on
the real line). -/
theorem integral_Icc_exp_isEquivalent :
    (fun N : ℝ => ∫ t in Icc (-1 : ℝ) 1, Real.exp (-N * t ^ 2)) ~[atTop]
      fun N => Real.sqrt Real.pi * N ^ (-(1 / 2 : ℝ)) := by
  have hS : TwoChartExample.interval 1 =
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Icc (-1 : ℝ) 1 := by
    ext x
    simp only [TwoChartExample.mem_interval, mem_preimage, MeasurableEquiv.funUnique_apply,
      mem_Icc, abs_le]
    exact Iff.rfl
  have heq : ∀ N : ℝ, ∫ x in TwoChartExample.interval 1, Real.exp (-N * x 0 ^ 2) =
      ∫ t in Icc (-1 : ℝ) 1, Real.exp (-N * t ^ 2) := fun N => by
    rw [hS]
    exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
      (MeasurableEquiv.funUnique _ _).measurableEmbedding (fun t => Real.exp (-N * t ^ 2))
      (Icc (-1) 1)
  exact TwoChartExample.integral_isEquivalent.congr_left (Eventually.of_forall heq)

/-- **Fubini on the cube**: `∫_{[−1,1]^d} e^{−N ∑ x_i²} = (∫_{−1}^{1} e^{−N t²} dt)^d`. -/
theorem cubeIntegral_eq_pow (N : ℝ) :
    targetIntegral (cube d) (fun _ => (1 : ℝ)) K (TubeWeight.one d) N =
      (∫ t in Icc (-1 : ℝ) 1, Real.exp (-N * t ^ 2)) ^ d := by
  unfold targetIntegral
  have h1 : ∀ x : Fin d → ℝ, (fun _ : Fin d → ℝ => (1 : ℝ)) x * (TubeWeight.one d).w x *
      Real.exp (-N * K x) = ∏ i, Real.exp (-N * x i ^ 2) := fun x => by
    rw [TubeWeight.one_w, one_mul, one_mul, K, Finset.mul_sum, Real.exp_sum]
  have h2 : ∀ x : Fin d → ℝ, (cube d).indicator (fun x => ∏ i, Real.exp (-N * x i ^ 2)) x =
      ∏ i, (Icc (-1 : ℝ) 1).indicator (fun t => Real.exp (-N * t ^ 2)) (x i) := fun x => by
    by_cases hx : x ∈ cube d
    · rw [indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem]
      have := mem_cube.1 hx i
      rw [abs_le] at this
      exact ⟨this.1, this.2⟩
    · rw [indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ Icc (-1 : ℝ) 1 := by
        by_contra hcon
        push_neg at hcon
        exact hx (mem_cube.2 fun j => abs_le.2 ⟨(hcon j).1, (hcon j).2⟩)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [setIntegral_congr_fun isCompact_cube.isClosed.measurableSet fun x _ => h1 x,
    ← integral_indicator isCompact_cube.isClosed.measurableSet,
    integral_congr_ae (Eventually.of_forall h2),
    integral_fintype_prod_volume_eq_prod
      (fun (_ : Fin d) (t : ℝ) => (Icc (-1 : ℝ) 1).indicator (fun t => Real.exp (-N * t ^ 2)) t),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, integral_indicator measurableSet_Icc]

/-- **The Gaussian certificate of the cube integral**:
`∫_{[−1,1]^d} e^{−N ∑ x_i²} ~ π^{d/2} N^{−d/2}`. -/
theorem cubeIntegral_isEquivalent_gaussian :
    targetIntegral (cube d) (fun _ => (1 : ℝ)) K (TubeWeight.one d) ~[atTop]
      fun N => Real.pi ^ (d / 2 : ℝ) * N ^ (-(d / 2 : ℝ)) := by
  have h := (integral_Icc_exp_isEquivalent).pow d
  refine (h.congr_left (Eventually.of_forall fun N => ?_)).congr_right ?_
  · exact (cubeIntegral_eq_pow N).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    simp only [Pi.pow_apply]
    rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_natCast (N ^ _), ← Real.rpow_mul hN.le]
    congr 1 <;> ring_nf

variable (hd : 1 < d) [NeZero d]

include hd in
/-- ★★★ **The blow-up coefficient of the unit cube is `π^{d/2}`**: the sum of the `d` whole-box
source coefficients of the blow-up charts (CCLXXXIII) equals the Gaussian constant, by uniqueness
of certificates. -/
theorem coeff_eq_pi_rpow :
    coeff hd (F := fun _ => (1 : ℝ)) (p := TubeWeight.one d) continuous_const continuous_const =
      Real.pi ^ (d / 2 : ℝ) := by
  have h1 := (cubeIntegral_isEquivalent hd (F := fun _ => (1 : ℝ)) (p := TubeWeight.one d)
    continuous_const continuous_const (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ _ => ⟨one_pos, one_pos⟩)).2
  have hpow : ∀ c : ℝ, (fun N : ℝ => c * N ^ (-(d / 2 : ℝ))) =
      fun N => c * powLogScale (d / 2) 0 N := by
    intro c
    funext N
    simp [powLogScale]
  rw [hpow] at h1
  have h2 := cubeIntegral_isEquivalent_gaussian (d := d)
  rw [hpow] at h2
  exact (hasLeadingTerm_of_isEquivalent h1).coeff_unique (hasLeadingTerm_of_isEquivalent h2)

include hd in
/-- ★★★ **The d-dimensional Gaussian through the resolution**: `∫_{[−1,1]^d} e^{−N ∑ x_i²} ~ π^{d/2}
N^{−d/2}`, with the pair `(d/2, 0)` and the positivity of the constant from the `d` blow-up charts
and the constant identified. -/
theorem cubeIntegral_isEquivalent_pi :
    (fun N : ℝ => ∫ x in cube d, Real.exp (-N * K x)) ~[atTop]
      fun N => Real.pi ^ (d / 2 : ℝ) * N ^ (-(d / 2 : ℝ)) := by
  have h := (cubeIntegral_isEquivalent hd (F := fun _ => (1 : ℝ)) (p := TubeWeight.one d)
    continuous_const continuous_const (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ _ => ⟨one_pos, one_pos⟩)).2
  rw [coeff_eq_pi_rpow hd] at h
  refine h.congr_left (Eventually.of_forall fun N => ?_)
  unfold targetIntegral
  refine setIntegral_congr_fun isCompact_cube.isClosed.measurableSet fun x _ => ?_
  simp

end BlowUpCube

end Grammar
