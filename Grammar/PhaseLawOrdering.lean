/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialObservables

/-!
# Stochastic ordering of the limiting family and moving constant phases (unit 354; Astra #43
units 3 and 6)

`ρ_b` is the tilt of `ρ_a` by the increasing weight `w = e^{β(b−a)√y}`:
`∫ g dρ_b = ∫ g w dρ_a / ∫ w dρ_a`.  For `a ≤ b` and every bounded measurable monotone `g`,
`∫ g dρ_a ≤ ∫ g dρ_b` (`phaseLaw_integral_mono`): with `W = ∫ w dρ_a` and `y*` the point where
`w(y*) = W`, the integrand `(g(y) − g(y*))(w(y)/W − 1)` is pointwise nonnegative and integrates to
`∫ g dρ_b − ∫ g dρ_a`.  In particular the tails `ρ_a((t,∞))` increase with the phase
(`phaseLaw_Ioi_mono`).  The stability theorem also yields the moving deterministic phase
statement `a_m → a ⇒ law_{N_m}(a_m) ⇒ ρ_a` (`energyLaw_tendsto_of_phase_tendsto`).
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### The tilt structure of the family -/

/-- `K_b(y) = K_a(y) e^{β(b−a)√y}`. -/
theorem phaseLawKernel_tilt (β a b l y : ℝ) :
    phaseLawKernel β b l y =
      phaseLawKernel β a l y * Real.exp (β * (b - a) * Real.sqrt y) := by
  unfold phaseLawKernel phaseKernel
  simp only [pow_zero, one_mul]
  rw [mul_assoc (y ^ (l - 1)), ← Real.exp_add]
  congr 2
  ring

/-- Integrability against `ρ_a` from integrability of `K_a · f` on `(0,∞)`. -/
theorem phaseLaw_integrable_of_kernel (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun y => phaseLawKernel β a l y * f y) (Ioi 0)) :
    Integrable f (phaseLaw β a l) := by
  unfold phaseLaw
  rw [integrable_withDensity_iff (((measurable_phaseLawKernel β a l).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hf.div_const (fluctMoment β a 0 l 0)).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun y hy => ?_
  have hy0 : 0 < y := hy
  rw [ENNReal.toReal_ofReal (div_nonneg (phaseLawKernel_nonneg β a l hy0.le)
    (fluctMoment_pos β a l hβ hl).le)]
  ring

theorem phaseLaw_integrable_tilt (β a b l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    Integrable (fun y => Real.exp (β * (b - a) * Real.sqrt y)) (phaseLaw β a l) :=
  phaseLaw_integrable_of_kernel β a l hβ hl
    ((integrableOn_phaseLawKernel β b l hβ hl).congr_fun
      (fun y _ => phaseLawKernel_tilt β a b l y) measurableSet_Ioi)

theorem phaseLaw_integral_tilt_weight (β a b l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    ∫ y, Real.exp (β * (b - a) * Real.sqrt y) ∂(phaseLaw β a l) =
      fluctMoment β b 0 l 0 / fluctMoment β a 0 l 0 := by
  rw [phaseLaw_integral β a l hβ hl, ← integral_phaseLawKernel β b l]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun y _ => (phaseLawKernel_tilt β a b l y).symm

/-- `∫ g dρ_b = ∫ g w dρ_a / ∫ w dρ_a` with `w = e^{β(b−a)√y}`. -/
theorem phaseLaw_integral_tilt (β a b l : ℝ) (hβ : 0 < β) (hl : 0 < l) (g : ℝ → ℝ) :
    ∫ y, g y ∂(phaseLaw β b l) =
      (∫ y, g y * Real.exp (β * (b - a) * Real.sqrt y) ∂(phaseLaw β a l)) /
        ∫ y, Real.exp (β * (b - a) * Real.sqrt y) ∂(phaseLaw β a l) := by
  rw [phaseLaw_integral_tilt_weight β a b l hβ hl, phaseLaw_integral β a l hβ hl,
    phaseLaw_integral β b l hβ hl, div_div_div_cancel_right₀ (fluctMoment_pos β a l hβ hl).ne']
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [phaseLawKernel_tilt β a b l y]
  ring

/-! ### Stochastic ordering -/

/-- **Stochastic ordering in the phase**: for `a ≤ b` and bounded measurable monotone `g`,
`∫ g dρ_a ≤ ∫ g dρ_b`. -/
theorem phaseLaw_integral_mono (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g) {G : ℝ} (hG : ∀ y, |g y| ≤ G) :
    ∫ y, g y ∂(phaseLaw β a l) ≤ ∫ y, g y ∂(phaseLaw β b l) := by
  have _ : Fact (0 < β) := ⟨hβ⟩
  have _ : Fact (0 < l) := ⟨hl⟩
  set w : ℝ → ℝ := fun y => Real.exp (β * (b - a) * Real.sqrt y) with hw
  have hw1 : ∀ y, 1 ≤ w y := fun y => by
    rw [hw]
    exact Real.one_le_exp (by positivity)
  have hwmono : Monotone w := fun y y' hyy' => by
    rw [hw]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hyy') (by
      nlinarith))
  have hwint : Integrable w (phaseLaw β a l) := phaseLaw_integrable_tilt β a b l hβ hl
  have hgint : Integrable g (phaseLaw β a l) :=
    (integrable_const G).mono' hgm.aestronglyMeasurable
      (Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hG y))
  have hgwint : Integrable (fun y => g y * w y) (phaseLaw β a l) :=
    Integrable.bdd_mul (c := G) hwint hgm.aestronglyMeasurable
      (Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hG y))
  set W := ∫ y, w y ∂(phaseLaw β a l) with hW
  have hW1 : 1 ≤ W := by
    have : ∫ y, (1 : ℝ) ∂(phaseLaw β a l) ≤ W :=
      integral_mono (integrable_const 1) hwint fun y => hw1 y
    simpa using this
  have hW0 : 0 < W := by linarith
  rw [phaseLaw_integral_tilt β a b l hβ hl g]
  change ∫ y, g y ∂(phaseLaw β a l) ≤ (∫ y, g y * w y ∂(phaseLaw β a l)) / W
  rw [le_div_iff₀ hW0]
  -- the crossing point `y*` of `w` and `W`
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have : w = fun _ => 1 := funext fun y => by rw [hw]; simp
    rw [this] at hW ⊢
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hW ⊢
    rw [hW]
    simp
  have hc : 0 < β * (b - a) := by nlinarith
  set ystar : ℝ := (Real.log W / (β * (b - a))) ^ 2 with hystar
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hwstar : w ystar = W := by
    rw [hw]
    simp only
    rw [hystar, Real.sqrt_sq (div_nonneg hlogW hc.le), mul_div_cancel₀ _ hc.ne', Real.exp_log hW0]
  -- pointwise nonnegativity of `(g y − g y*)(w y − W)`
  have hpt : ∀ y, 0 ≤ (g y - g ystar) * (w y - W) := fun y => by
    rcases le_total y ystar with hy | hy
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hg hy]) (by linarith [hwmono hy, hwstar])
    · exact mul_nonneg (by linarith [hg hy]) (by linarith [hwmono hy, hwstar])
  have hint : Integrable (fun y => (g y - g ystar) * (w y - W)) (phaseLaw β a l) := by
    have : (fun y => (g y - g ystar) * (w y - W)) =
        fun y => g y * w y - g ystar * w y - W * g y + g ystar * W := by
      funext y
      ring
    rw [this]
    exact ((hgwint.sub (hwint.const_mul _)).sub (hgint.const_mul _)).add (integrable_const _)
  have hnn := integral_nonneg_of_ae (μ := phaseLaw β a l) (Eventually.of_forall hpt)
  have hexp : ∫ y, (g y - g ystar) * (w y - W) ∂(phaseLaw β a l) =
      (∫ y, g y * w y ∂(phaseLaw β a l)) - W * ∫ y, g y ∂(phaseLaw β a l) := by
    have : (fun y => (g y - g ystar) * (w y - W)) =
        fun y => g y * w y - g ystar * w y - W * g y + g ystar * W := by
      funext y
      ring
    have i1 : Integrable (fun y => g y * w y - g ystar * w y) (phaseLaw β a l) :=
      hgwint.sub (hwint.const_mul _)
    have i2 : Integrable (fun y => g y * w y - g ystar * w y - W * g y) (phaseLaw β a l) :=
      i1.sub (hgint.const_mul _)
    rw [this, integral_add i2 (integrable_const _), integral_sub i1 (hgint.const_mul _),
      integral_sub hgwint (hwint.const_mul _), integral_const_mul, integral_const_mul,
      integral_const, probReal_univ, one_smul, ← hW]
    ring
  rw [hexp] at hnn
  linarith

/-- The tails of `ρ_a` increase with the phase: `ρ_a((t,∞)) ≤ ρ_b((t,∞))` for `a ≤ b`. -/
theorem phaseLaw_Ioi_mono (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    phaseLaw β a l (Ioi t) ≤ phaseLaw β b l (Ioi t) := by
  have _ : Fact (0 < β) := ⟨hβ⟩
  have _ : Fact (0 < l) := ⟨hl⟩
  have hmono : Monotone ((Ioi t).indicator (1 : ℝ → ℝ)) := fun y y' hyy' => by
    by_cases hy : y ∈ Ioi t
    · have hy' : y' ∈ Ioi t := lt_of_lt_of_le hy hyy'
      rw [indicator_of_mem hy, indicator_of_mem hy']
      exact le_rfl
    · rw [indicator_of_notMem hy]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hbd : ∀ y, |(Ioi t).indicator (1 : ℝ → ℝ) y| ≤ 1 := fun y => by
    by_cases hy : y ∈ Ioi t
    · rw [indicator_of_mem hy]
      simp
    · rw [indicator_of_notMem hy]
      simp
  have := phaseLaw_integral_mono β l hβ hl hab hmono
    ((measurable_const (a := (1 : ℝ))).indicator measurableSet_Ioi) hbd
  rw [integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Ioi,
    measureReal_def, measureReal_def] at this
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-! ### Moving deterministic constant phases -/

/-- **Moving constant phase**: `a_m → a` and `N_m → ∞` give `law_{N_m}(a_m) ⇒ ρ_a`. -/
theorem energyLaw_tendsto_of_phase_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
    (aseq : ℕ → ℝ) (ha : Tendsto aseq atTop (𝓝 a))
    (hZ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (fun _ => aseq m) η)
    (hZa : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (fun _ => a) η) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun m => ⟨energyLaw n h k β (Nseq m) η (aseq m),
        energyLaw_isProbabilityMeasure n h k β (Nseq m) hηc hηnn (aseq m) (hZ m)⟩) atTop
      (𝓝 ⟨phaseLaw β a l, @phaseLaw_isProbabilityMeasure β a l ⟨hβ⟩
        ⟨ratioExp_min_pos h k hk hatt⟩⟩) := by
  have hε : Tendsto (fun m => |aseq m - a|) atTop (𝓝 0) := by
    have := (ha.sub_const a).abs
    simpa using this
  exact perturbedEnergyLaw_tendsto_phaseLaw n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq
    hN1 hN (fun m _ => aseq m) (fun m => measurable_const) (fun m => |aseq m - a|) hε
    (fun m u _ => le_rfl) hZ hZa

end Grammar
