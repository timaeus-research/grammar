/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseLaplace

/-!
# The limiting posterior law of `NK` at constant phase (unit 343; Astra #41 units 1–3)

The phase-dressed moment scales as `M_{rβ}(p; a/r) = r^{-p/2} M_β(p; a/√r)`, so the constant-phase
leading coefficient at temperature `β+t` and phase `aβ/(β+t)` is `r^{-λ}` times the coefficient at
temperature `β` and phase `a/√r`, `r = (β+t)/β`.  Hence the posterior Laplace transform of `NK`
converges to `T(a,t) = r^{-λ} M_β(2λ; a/√r)/M_β(2λ; a)`, which is the Laplace transform of the
probability law on `(0,∞)` with density proportional to `y^{λ-1} e^{-βy + βa√y}` — the square-root
exponential tilt of the Gamma law of shape `λ` and rate `β` (recovered at `a = 0`).
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### Scaling of the phase-dressed moment and of the leading coefficient -/

/-- `M_{rβ}(p; a/r) = r^{-p/2} M_β(p; a/√r)`. -/
theorem phaseMoment_scale (β p a : ℝ) {r : ℝ} (hr : 0 < r) :
    phaseMoment (r * β) p (a / r) = r ^ (-(p / 2)) * phaseMoment β p (a / Real.sqrt r) := by
  unfold phaseMoment
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have key := integral_comp_mul_left_Ioi
    (fun x => x ^ (p - 1) * quadKernel β (a / Real.sqrt r) x) 0 hsr
  simp only [smul_eq_mul, mul_zero] at key
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (Real.sqrt r * s) ^ (p - 1) *
      quadKernel β (a / Real.sqrt r) (Real.sqrt r * s) =
      Real.sqrt r ^ (p - 1) * (s ^ (p - 1) * quadKernel (r * β) (a / r) s) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have e1 : a / Real.sqrt r * (Real.sqrt r * s) = a * s := by field_simp
    have e2 : r * β * (a / r) = β * a := by field_simp
    rw [Real.mul_rpow hsr.le hs0, mul_assoc]
    congr 2
    unfold quadKernel
    congr 1
    rw [mul_pow, Real.sq_sqrt hr.le, mul_assoc β, e1, e2]
    ring
  have hI : Real.sqrt r ^ (p - 1) * ∫ s in Ioi 0, s ^ (p - 1) * quadKernel (r * β) (a / r) s =
      (Real.sqrt r)⁻¹ * ∫ x in Ioi 0, x ^ (p - 1) * quadKernel β (a / Real.sqrt r) x := by
    rw [← integral_const_mul, ← key]
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs => (hpt s hs).symm
  have hpow : Real.sqrt r ^ (p - 1) * Real.sqrt r = r ^ (p / 2) := by
    rw [← Real.rpow_add_one hsr.ne', sub_add_cancel, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hne : Real.sqrt r ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos hsr _).ne'
  rw [Real.rpow_neg hr.le, ← hpow, mul_inv, mul_assoc, ← hI, inv_mul_cancel_left₀ hne]

/-- The scaling in the temperature-change form: `M_{β+t}(p; aβ/(β+t)) = r^{-p/2} M_β(p; a/√r)`. -/
theorem phaseMoment_temperature (β p a : ℝ) (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    phaseMoment (β + t) p (a * (β / (β + t))) =
      ((β + t) / β) ^ (-(p / 2)) * phaseMoment β p (a / Real.sqrt ((β + t) / β)) := by
  have hr : 0 < (β + t) / β := by positivity
  have := phaseMoment_scale β p a hr
  rw [show (β + t) / β * β = β + t by field_simp,
    show a / ((β + t) / β) = a * (β / (β + t)) by field_simp] at this
  exact this

/-- **Temperature scaling of the leading constant-phase coefficient**:
`A_{β+t}(aβ/(β+t)) = r^{-λ} A_β(a/√r)`. -/
theorem constPhase_coeff_temperature (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
        (multCount (ratioExp h k) l - 1) =
      ((β + t) / β) ^ (-l) * familySpectralCoeff n h k β
        (constFamily (a / Real.sqrt ((β + t) / β))) cη l (multCount (ratioExp h k) l - 1) := by
  have hβt : 0 < β + t := by linarith
  rw [(constPhase_leadingCoeff n h k hk hβt _ hη hηc hev hmin hatt).2,
    (constPhase_leadingCoeff n h k hk hβ _ hη hηc hev hmin hatt).2, phaseFace_eq_mul,
    phaseFace_eq_mul, phaseMoment_temperature β (2 * l) a hβ ht,
    show -(2 * l / 2) = -l by ring]
  ring

/-- The limit of the constant-phase posterior Laplace transform in closed form:
`T(a,t) = r^{-λ} M_β(2λ; a/√r)/M_β(2λ; a)`. -/
theorem constPhaseLaplace_limit_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
        (multCount (ratioExp h k) l - 1) /
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) =
      ((β + t) / β) ^ (-l) * phaseMoment β (2 * l) (a / Real.sqrt ((β + t) / β)) /
        phaseMoment β (2 * l) a := by
  rw [constPhase_coeff_temperature n h k hk hβ ht a hη hηc hev hmin hatt]
  rw [(constPhase_leadingCoeff n h k hk hβ _ hη hηc hev hmin hatt).2, phaseFace_eq_mul] at hA ⊢
  rw [(constPhase_leadingCoeff n h k hk hβ _ hη hηc hev hmin hatt).2, phaseFace_eq_mul]
  have hH : phaseFaceFactor h k l η ≠ 0 := right_ne_zero_of_mul hA
  have hM : phaseMoment β (2 * l) a ≠ 0 := left_ne_zero_of_mul hA
  field_simp

/-- At `a = 0` the limit is the Gamma Laplace transform `(β/(β+t))^λ`. -/
theorem constPhaseLaplace_limit_zero (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) {t : ℝ} (ht : 0 ≤ t) :
    ((β + t) / β) ^ (-l) * phaseMoment β (2 * l) (0 / Real.sqrt ((β + t) / β)) /
        phaseMoment β (2 * l) 0 = (β / (β + t)) ^ l := by
  have hβt : 0 < β + t := by linarith
  rw [zero_div, mul_div_assoc, div_self (phaseMoment_pos β (2 * l) 0 hβ (by linarith)).ne', mul_one,
    Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]

/-! ### The limiting law -/

/-- The unnormalised density `y^{λ-1} e^{-βy + βa√y}` of the limiting law on `(0,∞)`. -/
noncomputable def phaseLawKernel (β a l y : ℝ) : ℝ := y ^ (l - 1) * phaseKernel β a 0 y

theorem phaseLawKernel_nonneg (β a l : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ phaseLawKernel β a l y :=
  mul_nonneg (Real.rpow_nonneg hy _) (phaseKernel_nonneg β a 0 y)

theorem measurable_phaseLawKernel (β a l : ℝ) : Measurable (phaseLawKernel β a l) :=
  (measurable_id.pow_const _).mul (continuous_phaseKernel β a 0).measurable

/-- The mass of the kernel is the phase-dressed moment `J_λ(a) = ∫₀^∞ y^{λ-1} e^{-βy+βa√y} dy`. -/
theorem integral_phaseLawKernel (β a l : ℝ) :
    ∫ y in Ioi (0 : ℝ), phaseLawKernel β a l y = fluctMoment β a 0 l 0 := by
  unfold phaseLawKernel fluctMoment
  simp only [pow_zero, mul_one]

theorem integrableOn_phaseLawKernel (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    IntegrableOn (phaseLawKernel β a l) (Ioi 0) := by
  refine (integrableOn_fluct β a hβ 0 hl 0).congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [phaseLawKernel, pow_zero, mul_one]

/-- `J_λ(a) = 2 M_β(2λ; a)`: the two conventions for the phase-dressed moment. -/
theorem fluctMoment_eq_two_mul_phaseMoment (β a l : ℝ) :
    fluctMoment β a 0 l 0 = 2 * phaseMoment β (2 * l) a := by
  unfold fluctMoment phaseMoment
  have key := integral_comp_rpow_Ioi_of_pos
    (g := fun y => y ^ (l - 1) * (-Real.log y) ^ 0 * phaseKernel β a 0 y) (p := 2) two_pos
  rw [← key, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  simp only [smul_eq_mul, pow_zero, mul_one]
  unfold phaseKernel quadKernel
  have e : (s ^ 2) ^ (l - 1) = s ^ (2 * l - 1) / s := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le, eq_div_iff hs0.ne',
      ← Real.rpow_add_one hs0.ne']
    congr 1
    push_cast
    ring
  rw [Real.rpow_two, Real.sqrt_sq hs0.le, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, e,
    show -(β * s ^ 2) + β * s * a = -β * s ^ 2 + β * a * s by ring]
  simp only [pow_zero, one_mul]
  field_simp

theorem fluctMoment_pos (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) : 0 < fluctMoment β a 0 l 0 := by
  rw [fluctMoment_eq_two_mul_phaseMoment β a l]
  exact mul_pos two_pos (phaseMoment_pos β (2 * l) a hβ (by linarith))

/-- **The limiting posterior law of `NK` at constant phase `a`**: the probability measure on
`(0,∞)` with density `y^{λ-1} e^{-βy + βa√y}/J_λ(a)`. -/
noncomputable def phaseLaw (β a l : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun y =>
    ENNReal.ofReal (phaseLawKernel β a l y / fluctMoment β a 0 l 0)

theorem phaseLaw_integral (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) (g : ℝ → ℝ) :
    ∫ y, g y ∂(phaseLaw β a l) =
      (∫ y in Ioi (0 : ℝ), phaseLawKernel β a l y * g y) / fluctMoment β a 0 l 0 := by
  unfold phaseLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (((measurable_phaseLawKernel β a l).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 ≤ y := le_of_lt hy
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal
    (div_nonneg (phaseLawKernel_nonneg β a l hy0) (fluctMoment_pos β a l hβ hl).le)]
  ring

instance phaseLaw_isProbabilityMeasure (β a l : ℝ) [Fact (0 < β)] [Fact (0 < l)] :
    IsProbabilityMeasure (phaseLaw β a l) := by
  have hβ : 0 < β := Fact.out
  have hl : 0 < l := Fact.out
  constructor
  unfold phaseLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, integral_phaseLawKernel, div_self (fluctMoment_pos β a l hβ hl).ne',
      ENNReal.ofReal_one]
  · exact (integrableOn_phaseLawKernel β a l hβ hl).div_const _
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy =>
      div_nonneg (phaseLawKernel_nonneg β a l (le_of_lt hy)) (fluctMoment_pos β a l hβ hl).le

/-- The Laplace transform of the kernel: temperature change rescales the phase,
`∫₀^∞ e^{-ty} y^{λ-1} e^{-βy+βa√y} dy = r^{-λ} J_λ(a/√r)`, `r = (β+t)/β`. -/
theorem integral_phaseLawKernel_exp (β a l : ℝ) (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Ioi (0 : ℝ), phaseLawKernel β a l y * Real.exp (-(t * y)) =
      ((β + t) / β) ^ (-l) * fluctMoment β (a / Real.sqrt ((β + t) / β)) 0 l 0 := by
  have hr : 0 < (β + t) / β := by positivity
  have hsr : 0 < Real.sqrt ((β + t) / β) := Real.sqrt_pos.2 hr
  rw [← integral_phaseLawKernel]
  have key := integral_comp_mul_left_Ioi
    (fun x => phaseLawKernel β (a / Real.sqrt ((β + t) / β)) l x) 0 hr
  simp only [smul_eq_mul, mul_zero] at key
  have hpt : ∀ y ∈ Ioi (0 : ℝ),
      phaseLawKernel β (a / Real.sqrt ((β + t) / β)) l ((β + t) / β * y) =
      ((β + t) / β) ^ (l - 1) * (phaseLawKernel β a l y * Real.exp (-(t * y))) := by
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt hy
    unfold phaseLawKernel phaseKernel
    rw [Real.mul_rpow hr.le hy0, Real.sqrt_mul hr.le]
    simp only [pow_zero, one_mul]
    have e1 : β * (Real.sqrt ((β + t) / β) * Real.sqrt y) * (a / Real.sqrt ((β + t) / β)) =
        β * Real.sqrt y * a := by field_simp
    have e2 : β * ((β + t) / β * y) = (β + t) * y := by field_simp
    rw [mul_assoc (y ^ (l - 1)), ← Real.exp_add, mul_assoc, e1, e2,
      show -((β + t) * y) + β * Real.sqrt y * a = -(β * y) + β * Real.sqrt y * a + -(t * y) by
        ring]
  have hI : ((β + t) / β) ^ (l - 1) * ∫ y in Ioi 0, phaseLawKernel β a l y * Real.exp (-(t * y)) =
      ((β + t) / β)⁻¹ * ∫ x in Ioi 0, phaseLawKernel β (a / Real.sqrt ((β + t) / β)) l x := by
    rw [← integral_const_mul, ← key]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).symm
  have hne : ((β + t) / β) ^ (l - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hpow : ((β + t) / β) ^ (l - 1) * ((β + t) / β) = ((β + t) / β) ^ l := by
    rw [← Real.rpow_add_one hr.ne', sub_add_cancel]
  rw [Real.rpow_neg hr.le, ← hpow, mul_inv, mul_assoc, ← hI, inv_mul_cancel_left₀ hne]

/-- **Laplace transform of the limiting law**: `∫ e^{-ty} dρ_a = r^{-λ} J_λ(a/√r)/J_λ(a)`. -/
theorem phaseLaw_laplace (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, Real.exp (-(t * y)) ∂(phaseLaw β a l) =
      ((β + t) / β) ^ (-l) * fluctMoment β (a / Real.sqrt ((β + t) / β)) 0 l 0 /
        fluctMoment β a 0 l 0 := by
  rw [phaseLaw_integral β a l hβ hl, integral_phaseLawKernel_exp β a l hβ ht]

/-- **The posterior Laplace transform of `NK` at constant phase converges to that of `ρ_a`**:
`T_N(a,t) → ∫ e^{-ty} dρ_a(y)`, with `ρ_a ∝ y^{λ-1} e^{-βy + βa√y} dy`. -/
theorem constPhaseLaplace_tendsto_law (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) {cη : CoeffFamily (n + 1)}
    (hη : AbsSummable cη) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => constPhaseLaplace n h k β N η a t) atTop
      (𝓝 (∫ y, Real.exp (-(t * y)) ∂(phaseLaw β a l))) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have := constPhaseLaplace_tendsto n h k hk hβ ht a hη hηc hev hmin hatt hA
  rw [constPhaseLaplace_limit_eq n h k hk hβ ht a hη hηc hev hmin hatt hA] at this
  rw [phaseLaw_laplace β a l hβ hl0 ht, fluctMoment_eq_two_mul_phaseMoment β _ l,
    fluctMoment_eq_two_mul_phaseMoment β _ l]
  have hM : phaseMoment β (2 * l) a ≠ 0 := (phaseMoment_pos β (2 * l) a hβ (by linarith)).ne'
  convert this using 2
  field_simp

end Grammar
