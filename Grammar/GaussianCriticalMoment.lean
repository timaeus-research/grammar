import Grammar.FluctuationSharpUpper
import Grammar.GaussianPMoment

/-!
# The critical line of the `p`-th moment: `pβv = 2`

For `X ~ N(0,v)` the strict thresholds (`GaussianPMoment.lean`) leave the line `pβv = 2` open. With
the two-sided bounds `S_λ(a) ≍ a^{2λ−1}e^{βa²/4}` for `a ≥ 2` (`le_fluctuation_of_two_le`,
`fluctuation_le_polynomial_mul_gaussian`), the Gaussian exponential cancels exactly against the
density on the critical line and the tail test is `∫_2^∞ a^{p(2λ−1)} da`:

**`E[S_λ(X)^p] < ∞ ⟺ p(2λ − 1) < −1`** at `pβv = 2`
(`integrable_fluctuation_rpow_gaussianReal_iff_of_critical`).

In particular critical moments are finite only for `p > 1` (`λ < (p−1)/(2p)`); for `p ≤ 1` they
always diverge. The finite mixture `D(G) = ∑ρᵢS_λ(Gᵢ)` at the critical line is not classified
here; the compact-base critical classification is not attempted.
-/

open Real MeasureTheory ProbabilityTheory Set

namespace Grammar

/-- `S_λ` is nondecreasing in the phase. -/
theorem fluctuation_mono (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) {a b : ℝ} (hab : a ≤ b) :
    fluctuation β lam a ≤ fluctuation β lam b := by
  unfold fluctuation
  refine setIntegral_mono_on (fluctuation_integrableOn β lam hβ hlam a)
    (fluctuation_integrableOn β lam hβ hlam b) measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht0.le _)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hβ.le) (Real.sqrt_nonneg t)
  linarith

/-- Integrability against `N(0,v)` is integrability of the product with the density. -/
theorem integrable_gaussianReal_iff {v : NNReal} (hv : 0 < (v : ℝ)) {g : ℝ → ℝ} :
    Integrable g (gaussianReal 0 v) ↔ Integrable (fun x => g x * gaussianPDFReal 0 v x) := by
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  rw [gaussianReal_of_var_ne_zero 0 hv0, integrable_withDensity_iff (measurable_gaussianPDF 0 v)
    (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/-- **The critical line**: at `pβv = 2`, `E[S_λ(X)^p] < ∞ ⟺ p(2λ−1) < −1`. -/
theorem integrable_fluctuation_rpow_gaussianReal_iff_of_critical (β lam p : ℝ) (hβ : 0 < β)
    (hlam : 0 < lam) (hp : 0 < p) {v : NNReal} (hv : 0 < (v : ℝ)) (h : p * β * v = 2) :
    Integrable (fun x => fluctuation β lam x ^ p) (gaussianReal 0 v) ↔ p * (2 * lam - 1) < -1 := by
  rw [integrable_gaussianReal_iff hv]
  set r : ℝ := p * (2 * lam - 1) with hr
  have hS0 : ∀ x, 0 < fluctuation β lam x := fun x => fluctuation_pos β lam x hβ hlam
  have hcrit : ∀ x : ℝ, Real.exp (p * (β * x ^ 2 / 4)) * Real.exp (-x ^ 2 / (2 * v)) = 1 := by
    intro x
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    have : p * β = 2 / v := by field_simp; linarith
    rw [show p * (β * x ^ 2 / 4) = p * β * x ^ 2 / 4 by ring, this]
    field_simp
    ring
  have hmeas : Measurable fun x => fluctuation β lam x ^ p * gaussianPDFReal 0 v x :=
    (((continuous_fluctuation β lam hβ hlam).rpow_const fun x => Or.inr hp.le).measurable).mul
      (measurable_gaussianPDFReal 0 v)
  have hdens : ∀ x, gaussianPDFReal 0 v x = (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-x ^ 2 / (2 * v)) := fun x => by simp [gaussianPDFReal_def]
  set c0 : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hc0
  have hc00 : 0 < c0 := by positivity
  constructor
  · -- finite ⇒ `r < −1`: the lower bound gives `c a^r ≤` integrand on `[2,∞)`
    intro hint
    by_contra hge
    have hge' : -1 ≤ r := not_lt.1 hge
    set C : ℝ := Real.exp (-β) * (4 : ℝ) ^ (-(max (lam - 1) 0)) with hC
    have hC0 : 0 < C := by positivity
    have hlow : ∀ x ∈ Ioi (2 : ℝ), C ^ p * c0 * x ^ r ≤
        fluctuation β lam x ^ p * gaussianPDFReal 0 v x := by
      intro x hx
      have hx2 : (2 : ℝ) ≤ x := le_of_lt hx
      have hx0 : 0 < x := by linarith
      have hle := le_fluctuation_of_two_le β lam hβ hlam hx2
      rw [hdens]
      calc C ^ p * c0 * x ^ r
          = (C * x ^ (2 * lam - 1) * Real.exp (β * x ^ 2 / 4)) ^ p *
            (c0 * Real.exp (-x ^ 2 / (2 * v))) := by
            rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
              Real.mul_rpow hC0.le (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
              mul_comm (2 * lam - 1) p, ← hr, ← Real.exp_mul, mul_comm (β * x ^ 2 / 4) p]
            have := hcrit x
            linear_combination (-(C ^ p * c0 * x ^ r)) * this
        _ ≤ fluctuation β lam x ^ p * (c0 * Real.exp (-x ^ 2 / (2 * v))) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity)
              (by rw [hC]; linarith [hle]) hp.le) (by positivity)
    have hint2 : IntegrableOn (fun x : ℝ => C ^ p * c0 * x ^ r) (Ioi 2) := by
      refine Integrable.mono' (hint.integrableOn) (by fun_prop) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      rw [Real.norm_of_nonneg (by
        have : 0 < x := lt_trans two_pos hx
        positivity)]
      exact hlow x hx
    have hint3 : IntegrableOn (fun x : ℝ => x ^ r) (Ioi 2) := by
      have hpos : 0 < C ^ p * c0 := by positivity
      have this : IntegrableOn (fun x : ℝ => (C ^ p * c0)⁻¹ * (C ^ p * c0 * x ^ r)) (Ioi 2) :=
        hint2.const_mul _
      refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
      exact inv_mul_cancel_left₀ hpos.ne' _
    exact absurd ((integrableOn_Ioi_rpow_iff two_pos).1 hint3) hge
  · -- `r < −1` ⇒ finite: bounded on `(−∞, 2]`, dominated by `c a^r` on `(2, ∞)`
    intro hr1
    obtain ⟨C, hC0, hC⟩ := fluctuation_le_polynomial_mul_gaussian β lam hβ hlam
    have hleft : IntegrableOn (fun x => fluctuation β lam x ^ p * gaussianPDFReal 0 v x)
        (Iic 2) := by
      have hb : IntegrableOn (fun x => fluctuation β lam 2 ^ p * gaussianPDFReal 0 v x) (Iic 2) :=
        ((integrable_gaussianPDFReal 0 v).const_mul _).integrableOn
      refine hb.mono' hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hS0 x).le _)
        (gaussianPDFReal_nonneg _ _ _))]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hS0 x).le
        (fluctuation_mono β lam hβ hlam hx) hp.le) (gaussianPDFReal_nonneg _ _ _)
    have hright : IntegrableOn (fun x => fluctuation β lam x ^ p * gaussianPDFReal 0 v x)
        (Ioi 2) := by
      have hb : IntegrableOn (fun x : ℝ => C ^ p * c0 * x ^ r) (Ioi 2) :=
        (integrableOn_Ioi_rpow_of_lt hr1 two_pos).const_mul _
      refine hb.mono' hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have hx2 : (2 : ℝ) ≤ x := le_of_lt hx
      have hx0 : 0 < x := by linarith
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hS0 x).le _)
        (gaussianPDFReal_nonneg _ _ _)), hdens]
      calc fluctuation β lam x ^ p * (c0 * Real.exp (-x ^ 2 / (2 * v)))
          ≤ (C * x ^ (2 * lam - 1) * Real.exp (β * x ^ 2 / 4)) ^ p *
            (c0 * Real.exp (-x ^ 2 / (2 * v))) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hS0 x).le (hC x hx2) hp.le)
              (by positivity)
        _ = C ^ p * c0 * x ^ r := by
            rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
              Real.mul_rpow hC0.le (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
              mul_comm (2 * lam - 1) p, ← hr, ← Real.exp_mul, mul_comm (β * x ^ 2 / 4) p]
            have := hcrit x
            linear_combination (C ^ p * c0 * x ^ r) * this
    have := hleft.union hright
    rwa [Iic_union_Ioi, integrableOn_univ] at this

end Grammar
