/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseMomentHierarchy

/-!
# Structure of the limiting energy law `ρ_a` (unit 349; Astra #42 units 3–4)

`ρ_a ∝ y^{λ-1} e^{-βy + βa√y}` is an exponential family in the phase with sufficient statistic
`√y`: `∂_a log J_λ(a) = β E_{ρ_a}[√Y]`, and the mean `μ(a) = E_{ρ_a}[Y] = J_{λ+1}(a)/J_λ(a)` has
derivative `β Cov_{ρ_a}(Y, √Y)`, which is strictly positive because `(y − μ)(√y − √μ) ≥ 0` with
strict inequality off `{μ}`.  Hence **the limiting mean energy is a strictly increasing function
of the phase**.  Closed forms: `μ(a) = (λ + (a/2) ℓ'(a))/β` with `ℓ = log J_λ`, identified with
the leading energy `c₁(a)`; the variance `v(a) = (λ + (3a/4)ℓ' + (a²/4)ℓ'')/β²`; and the Laplace
consistency check `−∂_t T(a,t)|_{t=0} = μ(a)`, all obtained by differentiating the limiting
integrals (never the asymptotic expansion).
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### Moments of `√Y` and the log-derivative -/

theorem phaseLaw_integral_sqrt (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    ∫ y, Real.sqrt y ∂(phaseLaw β a l) =
      fluctMoment β a 0 (l + 1 / 2) 0 / fluctMoment β a 0 l 0 := by
  rw [phaseLaw_integral β a l hβ hl, ← integral_phaseLawKernel β a (l + 1 / 2)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 < y := hy
  unfold phaseLawKernel
  rw [mul_right_comm, Real.sqrt_eq_rpow, ← Real.rpow_add hy0]
  congr 2
  ring

/-- `∂_a log J_λ(a) = β J_{λ+1/2}(a)/J_λ(a) = β E_{ρ_a}[√Y]`. -/
theorem hasDerivAt_log_fluctMoment (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    HasDerivAt (fun a => Real.log (fluctMoment β a 0 l 0))
      (β * fluctMoment β a 0 (l + 1 / 2) 0 / fluctMoment β a 0 l 0) a := by
  have h := hasDerivAt_fluctMoment_phase hβ hl 0 a
  have := (Real.hasDerivAt_log (fluctMoment_pos β a l hβ hl).ne').comp a h
  exact this.congr_deriv (by rw [mul_comm, ← div_eq_mul_inv])

/-! ### The mean and its strict monotonicity in the phase -/

/-- The mean `μ(a) = J_{λ+1}(a)/J_λ(a)` of `ρ_a`. -/
noncomputable def phaseLawMean (β l a : ℝ) : ℝ :=
  fluctMoment β a 0 (l + 1) 0 / fluctMoment β a 0 l 0

theorem phaseLaw_mean (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    ∫ y, y ∂(phaseLaw β a l) = phaseLawMean β l a := by
  have := phaseLaw_moment β a l hβ hl 1
  simpa [phaseLawMean] using this

theorem hasDerivAt_phaseLawMean (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    HasDerivAt (phaseLawMean β l)
      (β * (fluctMoment β a 0 (l + 1 + 1 / 2) 0 * fluctMoment β a 0 l 0 -
        fluctMoment β a 0 (l + 1) 0 * fluctMoment β a 0 (l + 1 / 2) 0) /
        fluctMoment β a 0 l 0 ^ 2) a := by
  have h1 := hasDerivAt_fluctMoment_phase hβ (by linarith : 0 < l + 1) 0 a
  have h0 := hasDerivAt_fluctMoment_phase hβ hl 0 a
  refine (h1.div h0 (fluctMoment_pos β a l hβ hl).ne').congr_deriv ?_
  ring

theorem phaseLawKernel_pos (β a l : ℝ) {y : ℝ} (hy : 0 < y) : 0 < phaseLawKernel β a l y := by
  unfold phaseLawKernel phaseKernel
  positivity

/-- **Positivity of `Cov_{ρ_a}(Y, √Y)`**: `J_{λ+3/2} J_λ − J_{λ+1} J_{λ+1/2} > 0`. -/
theorem phaseLaw_cov_pos (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    0 < fluctMoment β a 0 (l + 1 + 1 / 2) 0 * fluctMoment β a 0 l 0 -
      fluctMoment β a 0 (l + 1) 0 * fluctMoment β a 0 (l + 1 / 2) 0 := by
  have hJ := fluctMoment_pos β a l hβ hl
  have hJ1 := fluctMoment_pos β a (l + 1) hβ (by linarith)
  set m := fluctMoment β a 0 (l + 1) 0 / fluctMoment β a 0 l 0 with hm
  have hm0 : 0 < m := div_pos hJ1 hJ
  -- pointwise expansion of the covariance integrand
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (y - m) * (Real.sqrt y - Real.sqrt m) * phaseLawKernel β a l y =
      phaseLawKernel β a (l + 1 + 1 / 2) y - Real.sqrt m * phaseLawKernel β a (l + 1) y -
        m * phaseLawKernel β a (l + 1 / 2) y + m * Real.sqrt m * phaseLawKernel β a l y := by
    intro y hy
    have hy0 : 0 < y := hy
    unfold phaseLawKernel
    have e1 : y ^ (l + 1 - 1) = y * y ^ (l - 1) := by
      rw [show l + 1 - 1 = 1 + (l - 1) by ring, Real.rpow_add hy0, Real.rpow_one]
    have e2 : y ^ (l + 1 / 2 - 1) = Real.sqrt y * y ^ (l - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]
      congr 1
      ring
    have e3 : y ^ (l + 1 + 1 / 2 - 1) = Real.sqrt y * y ^ (l - 1) * y := by
      rw [show l + 1 + 1 / 2 - 1 = (l + 1 / 2 - 1) + 1 by ring, Real.rpow_add_one hy0.ne', e2]
    rw [e1, e2, e3]
    ring
  have i0 := integrableOn_phaseLawKernel β a l hβ hl
  have i1 := integrableOn_phaseLawKernel β a (l + 1) hβ (by linarith)
  have i2 := integrableOn_phaseLawKernel β a (l + 1 / 2) hβ (by linarith)
  have i3 := integrableOn_phaseLawKernel β a (l + 1 + 1 / 2) hβ (by linarith)
  have hI1 : IntegrableOn (fun y => phaseLawKernel β a (l + 1 + 1 / 2) y -
      Real.sqrt m * phaseLawKernel β a (l + 1) y) (Ioi 0) :=
    Integrable.sub i3 (Integrable.const_mul i1 _)
  have hI2 : IntegrableOn (fun y => phaseLawKernel β a (l + 1 + 1 / 2) y -
      Real.sqrt m * phaseLawKernel β a (l + 1) y - m * phaseLawKernel β a (l + 1 / 2) y) (Ioi 0) :=
    Integrable.sub hI1 (Integrable.const_mul i2 _)
  have hI : IntegrableOn (fun y => phaseLawKernel β a (l + 1 + 1 / 2) y -
      Real.sqrt m * phaseLawKernel β a (l + 1) y - m * phaseLawKernel β a (l + 1 / 2) y +
      m * Real.sqrt m * phaseLawKernel β a l y) (Ioi 0) :=
    Integrable.add hI2 (Integrable.const_mul i0 _)
  -- the covariance integral in closed form
  have hint : ∫ y in Ioi (0 : ℝ), (y - m) * (Real.sqrt y - Real.sqrt m) * phaseLawKernel β a l y =
      fluctMoment β a 0 (l + 1 + 1 / 2) 0 - Real.sqrt m * fluctMoment β a 0 (l + 1) 0 -
        m * fluctMoment β a 0 (l + 1 / 2) 0 + m * Real.sqrt m * fluctMoment β a 0 l 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hI2 (Integrable.const_mul i0 _),
      integral_sub hI1 (Integrable.const_mul i2 _), integral_sub i3 (Integrable.const_mul i1 _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_phaseLawKernel,
      integral_phaseLawKernel, integral_phaseLawKernel, integral_phaseLawKernel]
  -- the covariance integral is positive
  have hpos : 0 < ∫ y in Ioi (0 : ℝ), (y - m) * (Real.sqrt y - Real.sqrt m) *
      phaseLawKernel β a l y := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae ?_
      (hI.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioi)]
    · refine lt_of_lt_of_le ?_ (measure_mono (show Ioi (0 : ℝ) \ {m} ⊆
        Function.support (fun y => (y - m) * (Real.sqrt y - Real.sqrt m) *
          phaseLawKernel β a l y) ∩ Ioi 0 from ?_))
      · rw [measure_sdiff_null (measure_singleton m), Real.volume_Ioi]
        exact ENNReal.zero_lt_top
      · rintro y ⟨hy, hym⟩
        refine ⟨?_, hy⟩
        rw [Function.mem_support]
        have hy0 : 0 < y := hy
        have hK := phaseLawKernel_pos β a l hy0
        have hne : y ≠ m := hym
        rcases lt_or_gt_of_ne hne with h | h
        · have := Real.sqrt_lt_sqrt hy0.le h
          exact (mul_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) hK).ne'
        · have := Real.sqrt_lt_sqrt hm0.le h
          exact (mul_pos (mul_pos (by linarith) (by linarith)) hK).ne'
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun y hy => ?_
      have hy0 : 0 < y := hy
      have hK := (phaseLawKernel_pos β a l hy0).le
      rcases le_total y m with h | h
      · exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (by linarith [Real.sqrt_le_sqrt h])) hK
      · exact mul_nonneg (mul_nonneg (by linarith) (by linarith [Real.sqrt_le_sqrt h])) hK
  rw [hint] at hpos
  have key : fluctMoment β a 0 (l + 1 + 1 / 2) 0 * fluctMoment β a 0 l 0 -
      fluctMoment β a 0 (l + 1) 0 * fluctMoment β a 0 (l + 1 / 2) 0 =
      fluctMoment β a 0 l 0 * (fluctMoment β a 0 (l + 1 + 1 / 2) 0 -
        Real.sqrt m * fluctMoment β a 0 (l + 1) 0 - m * fluctMoment β a 0 (l + 1 / 2) 0 +
        m * Real.sqrt m * fluctMoment β a 0 l 0) := by
    rw [hm]
    field_simp
    ring
  rw [key]
  exact mul_pos hJ hpos

/-- **The limiting mean energy is strictly increasing in the phase.** -/
theorem phaseLawMean_strictMono (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    StrictMono (phaseLawMean β l) :=
  strictMono_of_deriv_pos fun a => by
    rw [(hasDerivAt_phaseLawMean β l hβ hl a).deriv]
    exact div_pos (mul_pos hβ (phaseLaw_cov_pos β l hβ hl a))
      (pow_pos (fluctMoment_pos β a l hβ hl) 2)

/-! ### Closed forms -/

/-- `μ(a) = (λ + (a/2) ℓ'(a))/β`, `ℓ = log J_λ`. -/
theorem phaseLawMean_eq (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    phaseLawMean β l a =
      (l + a / 2 * deriv (fun a => Real.log (fluctMoment β a 0 l 0)) a) / β := by
  have hJ := (fluctMoment_pos β a l hβ hl).ne'
  rw [(hasDerivAt_log_fluctMoment β l hβ hl a).deriv]
  unfold phaseLawMean
  rw [fluctMoment_succ_exponent_phase hβ hl a 0]
  simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
  field_simp

/-- The mean of `ρ_a` is the leading constant-phase energy `c₁(a)`. -/
theorem constPhaseC1_eq_phaseLawMean (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l
      (multCount (ratioExp h k) l - 1) ≠ 0) :
    constPhaseC1 n h k β cη l a = phaseLawMean β l a := by
  rw [constPhaseC1_eq_div n h k hk hβ a hη hηc hev hmin hatt hA]
  have h1 : familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (l + 1)
      (multCount (ratioExp h k) l - 1) =
      phaseFaceFactor h k l η / 2 * fluctMoment β a 0 (l + 1) 0 := by
    simpa using constPhase_momentCoeff_eq n h k hk hβ hη hηc hev hmin hatt 1 a
  have h0 : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) =
      phaseFaceFactor h k l η / 2 * fluctMoment β a 0 l 0 := by
    simpa using constPhase_momentCoeff_eq n h k hk hβ hη hηc hev hmin hatt 0 a
  rw [h0] at hA
  have hH : phaseFaceFactor h k l η / 2 ≠ 0 := left_ne_zero_of_mul hA
  rw [h1, h0]
  unfold phaseLawMean
  rw [mul_div_mul_left _ _ hH]

/-- The variance `v(a) = J_{λ+2}/J_λ − μ(a)²` of `ρ_a`. -/
noncomputable def phaseLawVar (β l a : ℝ) : ℝ :=
  fluctMoment β a 0 (l + 2) 0 / fluctMoment β a 0 l 0 - phaseLawMean β l a ^ 2

theorem phaseLaw_var (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) :
    ∫ y, y ^ 2 ∂(phaseLaw β a l) - (∫ y, y ∂(phaseLaw β a l)) ^ 2 = phaseLawVar β l a := by
  rw [phaseLaw_mean β a l hβ hl, phaseLaw_moment β a l hβ hl 2]
  simp only [phaseLawVar, Nat.cast_ofNat]

/-- `v(a) = (λ + (3a/4) ℓ'(a) + (a²/4) ℓ''(a))/β²`, `ℓ = log J_λ`. -/
theorem phaseLawVar_eq (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    phaseLawVar β l a =
      (l + 3 * a / 4 * deriv (fun a => Real.log (fluctMoment β a 0 l 0)) a +
        a ^ 2 / 4 * deriv (deriv (fun a => Real.log (fluctMoment β a 0 l 0))) a) / β ^ 2 := by
  have hJ := fluctMoment_pos β a l hβ hl
  have hl' : 0 < l + 1 / 2 := by linarith
  -- the first and second log-derivatives in terms of `J_λ, J_{λ+1/2}, J_{λ+1}`
  have hd1 : deriv (fun a => Real.log (fluctMoment β a 0 l 0)) =
      fun a => β * fluctMoment β a 0 (l + 1 / 2) 0 / fluctMoment β a 0 l 0 :=
    funext fun a => (hasDerivAt_log_fluctMoment β l hβ hl a).deriv
  have hd2 := ((hasDerivAt_fluctMoment_phase hβ hl' 0 a).const_mul β).div
    (hasDerivAt_fluctMoment_phase hβ hl 0 a) hJ.ne'
  rw [hd1, show (fun a => β * fluctMoment β a 0 (l + 1 / 2) 0 / fluctMoment β a 0 l 0) =
    (fun a => β * fluctMoment β a 0 (l + 1 / 2) 0) / (fun a => fluctMoment β a 0 l 0) from rfl,
    hd2.deriv]
  simp only [Pi.div_apply]
  rw [show l + 1 / 2 + 1 / 2 = l + 1 by ring]
  -- the recurrences
  have r1 := fluctMoment_succ_exponent_phase hβ hl a 0
  have r2 := fluctMoment_succ_exponent_phase hβ hl' a 0
  have r3 := fluctMoment_succ_exponent_phase hβ (by linarith : 0 < l + 1) a 0
  simp only [CharP.cast_eq_zero, zero_mul, sub_zero] at r1 r2 r3
  rw [show l + 1 / 2 + 1 = l + 1 + 1 / 2 by ring, show l + 1 / 2 + 1 / 2 = l + 1 by ring] at r2
  rw [show l + 1 + 1 = l + 2 by ring] at r3
  unfold phaseLawVar phaseLawMean
  rw [r3, r2, r1]
  field_simp
  ring

/-! ### Laplace consistency: `−∂_t T(a,t)|_{t=0} = μ(a)` -/

/-- The limiting Laplace transform `T(a,t) = r^{-λ} J_λ(a/√r)/J_λ(a)`, `r = (β+t)/β`. -/
noncomputable def phaseLawLaplace (β l a t : ℝ) : ℝ :=
  ((β + t) / β) ^ (-l) * fluctMoment β (a / Real.sqrt ((β + t) / β)) 0 l 0 /
    fluctMoment β a 0 l 0

theorem phaseLaw_laplace_eq (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, Real.exp (-(t * y)) ∂(phaseLaw β a l) = phaseLawLaplace β l a t :=
  phaseLaw_laplace β a l hβ hl ht

/-- **Laplace consistency**: the derivative of the limiting transform at `t = 0` is `−μ(a)`. -/
theorem hasDerivAt_phaseLawLaplace_zero (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (a : ℝ) :
    HasDerivAt (phaseLawLaplace β l a) (-phaseLawMean β l a) 0 := by
  have hJ := fluctMoment_pos β a l hβ hl
  -- `r(t) = (β+t)/β`, `r(0) = 1`
  have hr : HasDerivAt (fun t : ℝ => (β + t) / β) (1 / β) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add β).div_const β
    simpa using this
  have hr0 : (β + 0) / β = 1 := by rw [add_zero, div_self hβ.ne']
  have hpow : HasDerivAt (fun t : ℝ => ((β + t) / β) ^ (-l)) (1 / β * (-l) * 1 ^ (-l - 1)) 0 := by
    have := hr.rpow_const (p := -l) (Or.inl (by rw [hr0]; exact one_ne_zero))
    rwa [hr0] at this
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt ((β + t) / β)) (1 / β / (2 * Real.sqrt 1)) 0 := by
    have := hr.sqrt (by rw [hr0]; exact one_ne_zero)
    rwa [hr0] at this
  have hdiv : HasDerivAt (fun t : ℝ => a / Real.sqrt ((β + t) / β))
      ((0 * Real.sqrt 1 - a * (1 / β / (2 * Real.sqrt 1))) / Real.sqrt 1 ^ 2) 0 := by
    have := (hasDerivAt_const (0 : ℝ) a).div hsqrt (by rw [hr0, Real.sqrt_one]; exact one_ne_zero)
    rwa [hr0] at this
  have hJc : HasDerivAt (fun t : ℝ => fluctMoment β (a / Real.sqrt ((β + t) / β)) 0 l 0)
      (β * fluctMoment β (a / Real.sqrt 1) 0 (l + 1 / 2) 0 *
        ((0 * Real.sqrt 1 - a * (1 / β / (2 * Real.sqrt 1))) / Real.sqrt 1 ^ 2)) 0 := by
    have := (hasDerivAt_fluctMoment_phase hβ hl 0 (a / Real.sqrt ((β + 0) / β))).comp 0 hdiv
    rw [hr0] at this
    exact this
  have := (hpow.mul hJc).div_const (fluctMoment β a 0 l 0)
  refine this.congr_deriv ?_
  simp only [Real.sqrt_one, Real.one_rpow, div_one, hr0, zero_mul, zero_sub, one_pow]
  unfold phaseLawMean
  rw [fluctMoment_succ_exponent_phase hβ hl a 0]
  simp only [CharP.cast_eq_zero, zero_mul, sub_zero]
  field_simp
  ring

end Grammar
