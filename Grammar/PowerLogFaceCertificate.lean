/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.LogWeightedPrim

/-!
# The generic power/log face certificate

The analytic building block behind the naive-Bayes envelope certificate (DCXVII): on a face chart
the domination envelope is a product of one-dimensional weights `x^a (1 + |log x|)^k` with `a > −1`,
and such weights are integrable on `(0,1)` (★★ `integrableOn_rpow_mul_logWeight`, absorbing the
logarithm into a small negative power: `(1 + |log x|)^k ≤ (1 + 1/ε)^k x^{−kε}`,
`ε = (a+1)/(2(k+1))`),
so their finite products are integrable on the cube (★★★ `integrable_powerLogFaceWeight`,
`Integrable.fintype_prod`).  The domination adapter `integrable_of_le_powerLogFaceWeight` turns any
a.e.-strongly-measurable `f` with `‖f‖ ≤ C·W` into an integrable one.  Not included (Astra
round 14): that the actual naive-Bayes envelope has these exponents on each face, chart Jacobians,
or the joint measurability of the fibre family (examples_slop §6).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `(1 + |log x|)^k ≤ (1 + 1/ε)^k x^{−kε}` on `(0,1]` for `ε > 0`. -/
theorem one_add_abs_log_pow_le {x ε : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) (k : ℕ) :
    (1 + |Real.log x|) ^ k ≤ (1 + 1 / ε) ^ k * x ^ (-(k * ε)) := by
  have h1 : 1 ≤ x ^ (-ε) := by
    rw [Real.rpow_neg hx0.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hx0 ε) |>.2 (Real.rpow_le_one hx0.le hx1 hε.le)
  have hlog := abs_log_le_rpow_neg_div x ε hx0 hx1 hε
  have hb : 1 + |Real.log x| ≤ (1 + 1 / ε) * x ^ (-ε) := by
    calc 1 + |Real.log x| ≤ x ^ (-ε) + x ^ (-ε) / ε := add_le_add h1 hlog
      _ = (1 + 1 / ε) * x ^ (-ε) := by ring
  calc (1 + |Real.log x|) ^ k ≤ ((1 + 1 / ε) * x ^ (-ε)) ^ k :=
        pow_le_pow_left₀ (by positivity) hb k
    _ = (1 + 1 / ε) ^ k * x ^ (-(k * ε)) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (-ε)) k, ← Real.rpow_mul hx0.le]
        congr 2
        ring

/-- ★★ `x^a (1 + |log x|)^k` is integrable on `(0,1)` for `a > −1`. -/
theorem integrableOn_rpow_mul_logWeight {a : ℝ} (ha : -1 < a) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ a * (1 + |Real.log x|) ^ k) (Ioo 0 1) := by
  set ε : ℝ := (a + 1) / (2 * (k + 1)) with hε
  have ha1 : 0 < a + 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; exact div_pos ha1 (by positivity)
  have hexp : -1 < a + -(k * ε) := by
    rw [hε]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have ha1 : 0 < a + 1 := by linarith
    have : (k : ℝ) * ((a + 1) / (2 * (k + 1))) ≤ (a + 1) / 2 := by
      calc (k : ℝ) * ((a + 1) / (2 * (k + 1))) = (a + 1) / 2 * ((k : ℝ) / (k + 1)) := by
            field_simp
        _ ≤ (a + 1) / 2 * 1 := by
            gcongr
            exact div_le_one_of_le₀ (by linarith) (by positivity)
        _ = (a + 1) / 2 := mul_one _
    linarith
  have hI : IntegrableOn (fun x : ℝ => (1 + 1 / ε) ^ k * x ^ (a + -(k * ε))) (Ioo 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hexp
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
    exact this.const_mul _
  refine hI.mono' ((measurable_id.pow_const _).mul
    ((measurable_const.add (continuous_abs.measurable.comp Real.measurable_log)).pow_const
      k)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x hx => ?_
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add hx0]
  have := one_add_abs_log_pow_le hx0 hx1 hε0 k
  calc x ^ a * (1 + |Real.log x|) ^ k ≤ x ^ a * ((1 + 1 / ε) ^ k * x ^ (-(k * ε))) := by gcongr
    _ = (1 + 1 / ε) ^ k * (x ^ a * x ^ (-(k * ε))) := by ring

/-- The face weight `W(x) = ∏ᵢ (xᵢ)^{aᵢ} (1 + |log xᵢ|)^{kᵢ}` on the cube `(0,1)^d`. -/
noncomputable def powerLogFaceWeight {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (x : Fin d → ℝ) : ℝ :=
  ∏ i, (x i) ^ (a i) * (1 + |Real.log (x i)|) ^ (k i)

/-- ★★★ **The face certificate**: `W` is integrable on `(0,1)^d` when every `aᵢ > −1`. -/
theorem integrable_powerLogFaceWeight {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (ha : ∀ i, -1 < a i) :
    Integrable (powerLogFaceWeight a k)
      (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) :=
  Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ (a i) * (1 + |Real.log t|) ^ (k i))
    fun i => integrableOn_rpow_mul_logWeight (ha i) (k i)

/-- The domination adapter: a measurable `f` with `‖f‖ ≤ C · W` is integrable on the cube. -/
theorem integrable_of_le_powerLogFaceWeight {d : ℕ} {a : Fin d → ℝ} {k : Fin d → ℕ}
    (ha : ∀ i, -1 < a i)
    {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C * powerLogFaceWeight a k x) :
    Integrable f (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) :=
  ((integrable_powerLogFaceWeight a k ha).const_mul C).mono' hf (Eventually.of_forall hC)

end Grammar
