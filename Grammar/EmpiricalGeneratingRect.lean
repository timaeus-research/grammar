/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneratingIdentity
import Grammar.EmpiricalBoxScaling

/-!
# The generating identity on rectangles (§20, coordinate-free programme)

Transport of `hasSum_empCoeff_population_mono` to the rectangular chart coefficients
`empCoeffRect`: for smooth `η, ζ`, a box `b > 0` and `μ ∈ Q⁻¹ℕ`,

★★★ `hasSum_empCoeffRect_population` (every log degree `q`):
`Σ_{r ≥ 0} (1/r!) · empCoeffRect (η (u^k ζ)^r) 0 h k b (μ + r/2) q = empCoeffRect η ζ h k b μ q`.

The half-integer shift of the exponent is absorbed by the rescaling: `scaleCoeff` carries
`β^{−(μ+r/2)}` with `β = b^{2k}`, which cancels the factor `(b^k)^r` produced by the insertion
`(u^k ζ)^r ∘ diag b`.  Also the homogeneity `empCoeff_const_mul` of the canonical coefficients in
the weight (by uniqueness of cutoff expansions).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} (h k : Fin d → ℕ)

/-- Homogeneity of the canonical coefficients in the weight. -/
theorem empCoeff_const_mul {F ξ : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hξ : ContDiff ℝ ∞ ξ)
    (hk : ∀ i, 0 < k i) (c : ℝ) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ}
    (hj : j ≤ d - 1) :
    empCoeff (fun v => c * F v) ξ h k μ j = c * empCoeff F ξ h k μ j := by
  have hI : empIntegral (fun v => c * F v) ξ h k = fun N => c * empIntegral F ξ h k N := by
    funext N
    unfold empIntegral fieldFam
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
    ring
  have hc : CutoffExpansion (Qamb k) (d - 1) (empIntegral (fun v => c * F v) ξ h k)
      (fun μ j => c * empCoeff F ξ h k μ j) := by
    rw [hI]
    exact (emp_cutoffExpansion hF hξ hk).const_mul c
  exact (empCoeff_unique (contDiff_const.mul hF) hξ hk hc hμ hj).symm

/-- The rectangular coefficient as the rescaled finite combination of the unit-box coefficients of
`(η ∘ diag b, ζ ∘ diag b)`. -/
theorem empCoeffRect_eq_scale_sum (η ζ : (Fin d → ℝ) → ℝ) (b : Fin d → ℝ) (μ : ℝ) (q : ℕ) :
    empCoeffRect η ζ h k b μ q = ((∏ i, b i) * mono h b) * mono (fun i => 2 * k i) b ^ (-μ) *
      ∑ j ∈ Finset.Ico q (d - 1 + 1),
        ((j.choose q : ℝ) * Real.log (mono (fun i => 2 * k i) b) ^ (j - q)) *
          empCoeff (η ∘ diag b) (ζ ∘ diag b) h k μ j := by
  unfold empCoeffRect scaleCoeff
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- ★ **The population term on a rectangle**: the `β^{−r/2}` of the rescaling cancels the `(b^k)^r`
of the insertion `(u^k ζ)^r ∘ diag b`. -/
theorem inv_factorial_mul_empCoeffRect_pow_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (q r : ℕ) :
    (1 / (r.factorial : ℝ)) *
      empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k b (μ + r / 2) q =
      ((∏ i, b i) * mono h b) * mono (fun i => 2 * k i) b ^ (-μ) *
        ∑ j ∈ Finset.Ico q (d - 1 + 1),
          ((j.choose q : ℝ) * Real.log (mono (fun i => 2 * k i) b) ^ (j - q)) *
            ((1 / (r.factorial : ℝ)) *
              empCoeff (fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r)
                (fun _ => 0) h k (μ + r / 2) j) := by
  set β : ℝ := mono (fun i => 2 * k i) b with hβ
  set A : ℝ := (∏ i, b i) * mono h b with hA
  have hβpos : 0 < β := mono_pos _ hb
  have hkb : 0 < mono k b := mono_pos _ hb
  have hβsq : β = mono k b ^ 2 := by
    rw [hβ, mono_pow]
    congr 1
    funext i
    ring
  have hηd : ContDiff ℝ ∞ (η ∘ diag b) := hη.comp (contDiff_diag b)
  have hζd : ContDiff ℝ ∞ (ζ ∘ diag b) := hζ.comp (contDiff_diag b)
  have hμr : ∃ m : ℕ, μ + (r : ℝ) / 2 = (m : ℝ) / Qamb k := by
    obtain ⟨m, hm⟩ := hμ
    obtain ⟨m₀, hm₀⟩ := half_mem_lattice k hk r
    exact ⟨m + m₀, by rw [hm, hm₀]; push_cast; ring⟩
  have hcomp : (fun v => η v * (mono k v * ζ v) ^ r) ∘ diag b =
      fun v => mono k b ^ r * ((η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r) := by
    funext v
    simp only [Function.comp, mono_diag]
    ring
  have hzero : ((fun _ : Fin d → ℝ => (0 : ℝ)) ∘ diag b) = fun _ => 0 := rfl
  have hF : ContDiff ℝ ∞ fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r :=
    hηd.mul (((contDiff_mono k).mul hζd).pow r)
  have hrp : β ^ (-(μ + (r : ℝ) / 2)) * mono k b ^ r = β ^ (-μ) := by
    have h1 : β ^ (-(μ + (r : ℝ) / 2)) = β ^ (-μ) * β ^ (-((r : ℝ) / 2)) := by
      rw [← Real.rpow_add hβpos]
      ring_nf
    have h2 : β ^ (-((r : ℝ) / 2)) = (mono k b ^ r)⁻¹ := by
      rw [hβsq, ← Real.rpow_natCast (mono k b) 2, ← Real.rpow_mul hkb.le,
        ← Real.rpow_natCast (mono k b) r, ← Real.rpow_neg hkb.le]
      congr 1
      push_cast
      ring
    rw [h1, h2, mul_assoc, inv_mul_cancel₀ (pow_pos hkb r).ne', mul_one]
  unfold empCoeffRect scaleCoeff
  rw [hcomp, hzero, ← hβ, ← hA]
  have hsum : ∑ j ∈ Finset.Ico q (d - 1 + 1),
      empCoeff (fun v => mono k b ^ r * ((η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r))
        (fun _ => 0) h k (μ + r / 2) j * (j.choose q : ℝ) * Real.log β ^ (j - q) =
      mono k b ^ r * ∑ j ∈ Finset.Ico q (d - 1 + 1),
        empCoeff (fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r)
          (fun _ => 0) h k (μ + r / 2) j * (j.choose q : ℝ) * Real.log β ^ (j - q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [empCoeff_const_mul h k hF contDiff_const hk _ hμr
      (Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2)]
    ring
  rw [hsum]
  set S := ∑ j ∈ Finset.Ico q (d - 1 + 1),
    empCoeff (fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r)
      (fun _ => 0) h k (μ + r / 2) j * (j.choose q : ℝ) * Real.log β ^ (j - q) with hS
  calc _ = A * (β ^ (-(μ + (r : ℝ) / 2)) * mono k b ^ r) * ((1 / (r.factorial : ℝ)) * S) := by
        ring
    _ = A * β ^ (-μ) * ((1 / (r.factorial : ℝ)) * S) := by rw [hrp]
    _ = _ := by
        rw [hS]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- ★★★ **The all-orders generating identity on a rectangle**: for `μ ∈ Q⁻¹ℕ` and every log
degree `q`,
`Σ_{r ≥ 0} (1/r!) · empCoeffRect (η (u^k ζ)^r) 0 h k b (μ + r/2) q = empCoeffRect η ζ h k b μ q`
(unconditionally convergent). -/
theorem hasSum_empCoeffRect_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (q : ℕ) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k b (μ + r / 2) q)
      (empCoeffRect η ζ h k b μ q) := by
  set β : ℝ := mono (fun i => 2 * k i) b with hβ
  set A : ℝ := (∏ i, b i) * mono h b with hA
  have hηd : ContDiff ℝ ∞ (η ∘ diag b) := hη.comp (contDiff_diag b)
  have hζd : ContDiff ℝ ∞ (ζ ∘ diag b) := hζ.comp (contDiff_diag b)
  have hj_sum : ∀ j ∈ Finset.Ico q (d - 1 + 1), HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
      empCoeff (fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r) (fun _ => 0) h k
        (μ + r / 2) j) (empCoeff (η ∘ diag b) (ζ ∘ diag b) h k μ j) := fun j hj =>
    hasSum_empCoeff_population_mono h k hηd hζd hk hμ (Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2)
  have hfin := hasSum_sum fun j hj =>
    (hj_sum j hj).mul_left ((j.choose q : ℝ) * Real.log β ^ (j - q))
  have hall := hfin.mul_left (A * β ^ (-μ))
  have hfun : (fun r : ℕ => (1 / (r.factorial : ℝ)) *
      empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k b (μ + r / 2) q) =
      fun r : ℕ => A * β ^ (-μ) * ∑ j ∈ Finset.Ico q (d - 1 + 1),
        ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ((1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag b) v * (mono k v * (ζ ∘ diag b) v) ^ r)
            (fun _ => 0) h k (μ + r / 2) j) :=
    funext fun r => inv_factorial_mul_empCoeffRect_pow_eq h k hη hζ hk hb hμ q r
  rw [hfun, empCoeffRect_eq_scale_sum h k η ζ b μ q]
  exact hall

/-- The `tsum` form of `hasSum_empCoeffRect_population`. -/
theorem empCoeffRect_eq_tsum_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (q : ℕ) :
    empCoeffRect η ζ h k b μ q = ∑' r : ℕ, (1 / (r.factorial : ℝ)) *
      empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k b (μ + r / 2) q :=
  (hasSum_empCoeffRect_population h k hη hζ hk hb hμ q).tsum_eq.symm

end SmoothEngine

end Grammar
