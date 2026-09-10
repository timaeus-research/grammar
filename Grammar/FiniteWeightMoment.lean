import Grammar.UniformMomentSubgaussian

/-!
# Uniform moments of exponential integrals against deterministic finite-`n` weights

The Hölder–Tonelli argument of `UniformMomentSubgaussian.lean` does not depend on the Gamma weight:
for a probability space `(Ω, P)`, a finite measure `ν`, `p ≥ 1`, and a jointly measurable
`H : Ω × U → ℝ` with `E e^{pH(·,u)} ≤ 1` for `ν`-a.e. `u`,

**`E[(∫ e^{H(ω,u)} dν(u))^p] ≤ ν(U)^p`**   (`lintegral_rpow_lintegral_exp_le_mass_rpow`),

including the zero-mass case. Applied to a finite-`n` chart integral with a deterministic weight,
`J_n(ω) = ∫_U w(u) a(ω,u) e^{−βr_n(u)² + βr_n(u)ξ_n(ω,u)} dμ(u)` with `w ≥ 0`, a bounded (possibly
random) amplitude `|a| ≤ M`, `r_n ≥ 0`
and the **full-domain** pointwise bound `E e^{tξ_n(·,u)} ≤ e^{ct²/2}` (`t ≥ 0`): with
`α = β(1 − pβc/2) > 0` and the population mass at the reduced temperature
`B_n(α) = A_n ∫_U w e^{−αr_n²} dμ`,

**`E|A_n J_n|^p ≤ (M B_n(α))^p`**   (`moment_scaled_integral_le_population_mass`),

because `−p(β−α)r_n² + (c/2)(pβr_n)² = 0`. This reduces the uniform-moment input of the expectation
assembly to a bound on a deterministic population integral at temperature `α` — no pathwise
comparison with the limiting compact-base coefficient is needed. Non-claims: a sufficient bound,
not a sharp classification; the full-domain exponential-moment bound on the finite-`n` field is a
hypothesis (a bound for the limiting face field alone does not give it).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

section Generic

variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] (P : Measure Ω)
  [IsProbabilityMeasure P] (ν : Measure U) [IsFiniteMeasure ν]

/-- **Hölder–Tonelli for exponential integrals**: if `E e^{pH(·,u)} ≤ 1` for `ν`-a.e. `u` then
`E[(∫ e^{H} dν)^p] ≤ ν(U)^p` (`p ≥ 1`). -/
theorem lintegral_rpow_lintegral_exp_le_mass_rpow {p : ℝ} (hp : 1 ≤ p) (H : Ω → U → ℝ)
    (hH : Measurable (Function.uncurry H))
    (hmgf : ∀ᵐ u ∂ν, ∫⁻ ω, ENNReal.ofReal (Real.exp (p * H ω u)) ∂P ≤ 1) :
    ∫⁻ ω, (∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν) ^ p ∂P ≤ ν univ ^ p := by
  set e : Ω → U → ℝ≥0∞ := fun ω u => ENNReal.ofReal (Real.exp (H ω u)) with he
  have he_meas : Measurable (Function.uncurry e) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hH)
  have he_meas_ω : ∀ ω, Measurable (e ω) := fun ω =>
    he_meas.comp (measurable_const.prodMk measurable_id)
  have hp0 : 0 < p := by linarith
  -- Hölder pointwise in `ω`
  have hHolder : ∀ ω, (∫⁻ u, e ω u ∂ν) ^ p ≤ (∫⁻ u, e ω u ^ p ∂ν) * (ν univ) ^ (p - 1) := by
    intro ω
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1]
      simp
    · have hpq := Real.HolderConjugate.conjExponent hp1
      set q : ℝ := Real.conjExponent p with hq
      have hqp : 1 / q * p = p - 1 := by
        have h1 := hpq.one_div_add_one_div
        rw [div_one] at h1
        have : 1 / q = 1 - 1 / p := by linarith
        rw [this, sub_mul, one_mul, one_div_mul_cancel hp0.ne']
      have hH' := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (he_meas_ω ω).aemeasurable
        (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hH'
      calc (∫⁻ u, e ω u ∂ν) ^ p
          ≤ ((∫⁻ u, e ω u ^ p ∂ν) ^ (1 / p) * (ν univ) ^ (1 / q)) ^ p :=
            ENNReal.rpow_le_rpow hH' hp0.le
        _ = (∫⁻ u, e ω u ^ p ∂ν) * (ν univ) ^ (p - 1) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
              one_div_mul_cancel hp0.ne', ENNReal.rpow_one, hqp]
  -- the inner expectation is at most `1`
  have hpt : ∀ᵐ u ∂ν, ∫⁻ ω, e ω u ^ p ∂P ≤ 1 := by
    filter_upwards [hmgf] with u hu
    refine le_trans (le_of_eq ?_) hu
    refine lintegral_congr fun ω => ?_
    rw [he]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le, ← Real.exp_mul, mul_comm]
  have hswap : ∫⁻ ω, ∫⁻ u, e ω u ^ p ∂ν ∂P = ∫⁻ u, ∫⁻ ω, e ω u ^ p ∂P ∂ν :=
    lintegral_lintegral_swap (he_meas.pow_const p).aemeasurable
  calc ∫⁻ ω, (∫⁻ u, e ω u ∂ν) ^ p ∂P
      ≤ ∫⁻ ω, (∫⁻ u, e ω u ^ p ∂ν) * (ν univ) ^ (p - 1) ∂P := lintegral_mono hHolder
    _ = (∫⁻ ω, ∫⁻ u, e ω u ^ p ∂ν ∂P) * (ν univ) ^ (p - 1) :=
        lintegral_mul_const _ (he_meas.pow_const p).lintegral_prod_right'
    _ = (∫⁻ u, ∫⁻ ω, e ω u ^ p ∂P ∂ν) * (ν univ) ^ (p - 1) := by rw [hswap]
    _ ≤ (∫⁻ _u, (1 : ℝ≥0∞) ∂ν) * (ν univ) ^ (p - 1) :=
        mul_le_mul' (lintegral_mono_ae hpt) le_rfl
    _ = ν univ * (ν univ) ^ (p - 1) := by rw [lintegral_const, one_mul]
    _ = ν univ ^ p := by
        rcases eq_or_ne (ν univ) 0 with h0 | h0
        · rw [h0, zero_mul, ENNReal.zero_rpow_of_pos hp0]
        · have : ν univ * ν univ ^ (p - 1) = ν univ ^ (1 + (p - 1)) := by
            rw [ENNReal.rpow_add _ _ h0 (measure_ne_top _ _), ENNReal.rpow_one]
          rw [this]
          congr 1
          ring

end Generic

section Application

variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] (P : Measure Ω)
  [IsProbabilityMeasure P] (μ : Measure U) [IsFiniteMeasure μ]

/-- The deterministic weight at the reduced temperature `α`: `dν = A w e^{−αr²} dμ`. -/
noncomputable def reducedWeight (A α : ℝ) (w r : U → ℝ) : Measure U :=
  μ.withDensity fun u => ENNReal.ofReal (A * w u * Real.exp (-α * r u ^ 2))

omit [IsFiniteMeasure μ] in
theorem reducedWeight_univ (A α : ℝ) {w r : U → ℝ} (hA : 0 ≤ A) (hw0 : ∀ u, 0 ≤ w u)
    (hint : Integrable (fun u => w u * Real.exp (-α * r u ^ 2)) μ) :
    reducedWeight μ A α w r univ =
      ENNReal.ofReal (A * ∫ u, w u * Real.exp (-α * r u ^ 2) ∂μ) := by
  rw [reducedWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul A)
      (Filter.Eventually.of_forall fun u => by
        have := hw0 u
        positivity)]
  refine lintegral_congr fun u => ?_
  rw [mul_assoc]

omit [IsFiniteMeasure μ] in
/-- **Uniform `p`-th moment of a scaled finite-`n` chart integral from the population mass at the
reduced temperature**: with `w ≥ 0`, `|a| ≤ M`, `r ≥ 0`, the full-domain bound
`E e^{tξ(·,u)} ≤ e^{ct²/2}` for `t ≥ 0`, `p ≥ 1`, `pβc < 2`, and `α = β(1 − pβc/2)`,
`E |A ∫ w a e^{−βr² + βrξ} dμ|^p ≤ (M · A ∫ w e^{−αr²} dμ)^p`. -/
theorem moment_scaled_integral_le_population_mass {β c p A M : ℝ} (hβ : 0 < β) (hp : 1 ≤ p)
    (h : p * β * c < 2) (hA : 0 ≤ A) (hM : 0 ≤ M) {w r : U → ℝ} {a : Ω → U → ℝ}
    (hw : Measurable w) (hr : Measurable r) (hw0 : ∀ u, 0 ≤ w u) (haM : ∀ ω u, |a ω u| ≤ M)
    (hr0 : ∀ u, 0 ≤ r u) (ξ : Ω → U → ℝ) (hξ : Measurable (Function.uncurry ξ))
    (hmgf : ∀ u, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ξ ω u)) ∂P ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    (hint : Integrable (fun u => w u * Real.exp (-(β * (1 - p * β * c / 2)) * r u ^ 2)) μ) :
    ∫⁻ ω, ENNReal.ofReal (|A * ∫ u, w u * a ω u *
        Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ| ^ p) ∂P ≤
      ENNReal.ofReal (M * (A * ∫ u, w u *
        Real.exp (-(β * (1 - p * β * c / 2)) * r u ^ 2) ∂μ)) ^ p := by
  set α : ℝ := β * (1 - p * β * c / 2) with hα
  have hα0 : 0 < α := mul_pos hβ (by linarith)
  have hp0 : 0 < p := by linarith
  set ν : Measure U := reducedWeight μ A α w r with hν
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, reducedWeight_univ μ A α hA hw0 hint]
    exact ENNReal.ofReal_lt_top
  have hν_univ : ν univ = ENNReal.ofReal (A * ∫ u, w u * Real.exp (-α * r u ^ 2) ∂μ) :=
    reducedWeight_univ μ A α hA hw0 hint
  -- the exponent `H = −(β−α)r² + βrξ`
  set H : Ω → U → ℝ := fun ω u => -(β - α) * r u ^ 2 + β * r u * ξ ω u with hH
  have hHm : Measurable (Function.uncurry H) := by
    refine Measurable.add ?_ ?_
    · exact (measurable_const.mul ((hr.comp measurable_snd).pow_const 2))
    · exact (measurable_const.mul (hr.comp measurable_snd)).mul hξ
  have hmgfH : ∀ᵐ u ∂ν, ∫⁻ ω, ENNReal.ofReal (Real.exp (p * H ω u)) ∂P ≤ 1 := by
    refine Filter.Eventually.of_forall fun u => ?_
    have hrew : ∀ ω, ENNReal.ofReal (Real.exp (p * H ω u)) =
        ENNReal.ofReal (Real.exp (-(p * (β - α)) * r u ^ 2)) *
          ENNReal.ofReal (Real.exp ((p * β * r u) * ξ ω u)) := by
      intro ω
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hH]
      congr 2
      ring
    simp_rw [hrew]
    have hm : Measurable fun ω => ENNReal.ofReal (Real.exp ((p * β * r u) * ξ ω u)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hξ.comp (measurable_id.prodMk measurable_const))))
    rw [lintegral_const_mul _ hm]
    calc ENNReal.ofReal (Real.exp (-(p * (β - α)) * r u ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((p * β * r u) * ξ ω u)) ∂P
        ≤ ENNReal.ofReal (Real.exp (-(p * (β - α)) * r u ^ 2)) *
          ENNReal.ofReal (Real.exp (c * (p * β * r u) ^ 2 / 2)) :=
          mul_le_mul' le_rfl (hmgf u _ (by have := hr0 u; positivity))
      _ = ENNReal.ofReal (Real.exp (-(p * (β - α)) * r u ^ 2 + c * (p * β * r u) ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      _ = 1 := by
          rw [show -(p * (β - α)) * r u ^ 2 + c * (p * β * r u) ^ 2 / 2 = 0 by rw [hα]; ring,
            Real.exp_zero, ENNReal.ofReal_one]
  have hgen := lintegral_rpow_lintegral_exp_le_mass_rpow P ν hp H hHm hmgfH
  rw [hν_univ] at hgen
  -- pointwise: `ofReal |A J(ω)| ≤ M ∫ e^{H(ω,u)} dν`
  have hpt : ∀ ω, ENNReal.ofReal (|A * ∫ u, w u * a ω u *
      Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ| ^ p) ≤
      ENNReal.ofReal M ^ p * (∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν) ^ p := by
    intro ω
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le,
      ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    -- `ofReal |A J| ≤ A ∫⁻ ‖w a e‖ₑ ≤ ofReal M * ∫⁻ e^H dν`
    have hJ : ENNReal.ofReal (|A * ∫ u, w u * a ω u *
        Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ|) ≤
        ENNReal.ofReal A * ∫⁻ u, ENNReal.ofReal (w u * |a ω u| *
          Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) ∂μ := by
      rw [abs_mul, abs_of_nonneg hA, ENNReal.ofReal_mul hA]
      refine mul_le_mul' le_rfl ?_
      rw [← Real.norm_eq_abs, ofReal_norm]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun u => ?_
      rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw0 u),
        abs_of_pos (Real.exp_pos _)]
    have hdens : ∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν =
        ∫⁻ u, ENNReal.ofReal (A * w u * Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) ∂μ := by
      have hf : Measurable fun u => ENNReal.ofReal (A * w u * Real.exp (-α * r u ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((measurable_const.mul hw).mul
          (Real.measurable_exp.comp (measurable_const.mul (hr.pow_const 2))))
      have hg : Measurable fun u => ENNReal.ofReal (Real.exp (H ω u)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (hHm.comp (measurable_const.prodMk measurable_id)))
      rw [hν, reducedWeight, lintegral_withDensity_eq_lintegral_mul _ hf hg]
      refine lintegral_congr fun u => ?_
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (by have := hw0 u; positivity)]
      congr 1
      rw [hH]
      simp only
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    calc ENNReal.ofReal (|A * ∫ u, w u * a ω u *
          Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ|)
        ≤ ENNReal.ofReal A * ∫⁻ u, ENNReal.ofReal (w u * |a ω u| *
            Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) ∂μ := hJ
      _ ≤ ENNReal.ofReal A * ∫⁻ u, ENNReal.ofReal (M * (w u *
            Real.exp (-β * r u ^ 2 + β * r u * ξ ω u))) ∂μ := by
          refine mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_)
          have := haM ω u
          have := hw0 u
          have := Real.exp_pos (-β * r u ^ 2 + β * r u * ξ ω u)
          nlinarith [mul_le_mul_of_nonneg_left (haM ω u) (hw0 u)]
      _ = ENNReal.ofReal M * ∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν := by
          rw [hdens]
          have hmw : Measurable fun u => ENNReal.ofReal (w u *
              Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) :=
            ENNReal.measurable_ofReal.comp (hw.mul (Real.measurable_exp.comp
              ((measurable_const.mul (hr.pow_const 2)).add
                ((measurable_const.mul hr).mul (hξ.comp (measurable_const.prodMk measurable_id))))))
          simp_rw [ENNReal.ofReal_mul hM]
          rw [lintegral_const_mul _ hmw]
          have : ∀ u, ENNReal.ofReal (A * w u * Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) =
              ENNReal.ofReal A * ENNReal.ofReal (w u * Real.exp (-β * r u ^ 2 + β * r u * ξ ω u)) :=
            fun u => by rw [mul_assoc, ENNReal.ofReal_mul hA]
          simp_rw [this]
          rw [lintegral_const_mul _ hmw]
          ring
  calc ∫⁻ ω, ENNReal.ofReal (|A * ∫ u, w u * a ω u *
        Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ| ^ p) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal M ^ p * (∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν) ^ p ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal M ^ p * ∫⁻ ω, (∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν) ^ p ∂P := by
        have hq : Measurable fun q : Ω × U => ENNReal.ofReal (Real.exp (H q.1 q.2)) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hHm)
        have hmω : Measurable fun ω => (∫⁻ u, ENNReal.ofReal (Real.exp (H ω u)) ∂ν) ^ p :=
          hq.lintegral_prod_right'.pow_const p
        rw [lintegral_const_mul _ hmω]
    _ ≤ ENNReal.ofReal M ^ p * ENNReal.ofReal (A * ∫ u, w u * Real.exp (-α * r u ^ 2) ∂μ) ^ p :=
        mul_le_mul' le_rfl hgen
    _ = ENNReal.ofReal (M * (A * ∫ u, w u * Real.exp (-α * r u ^ 2) ∂μ)) ^ p := by
        rw [ENNReal.ofReal_mul hM, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]

end Application

end Grammar
