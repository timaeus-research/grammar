import Grammar.BilocalGaussian

/-!
# The cross-pairing series of the bilocal two-point function

With `a = β(1 − βB_ii/2)`, `b = β(1 − βB_jj/2)`, `h = β²B_ij` and `|h| < 2√(ab)`,

`E[S_λ(G_i) S_λ(G_j)] = ∑_{r ≥ 0} (h^r / r!) Γ(λ + r/2)² (ab)^{−(λ + r/2)}`

(`integral_fluctuation_mul_fluctuation_eq_tsum`), the series converging absolutely
(`summable_bilocalCoeff`). The `r = 0` term is the disconnected part `Γ(λ)²(ab)^{−λ}`, so the
covariance is the sum over `r ≥ 1` (`cov_fluctuation_eq_tsum`), and in integral form it is
`∬ t^{λ−1}s^{λ−1} e^{−at−bs} (e^{h√(ts)} − 1)` (`cov_fluctuation_eq_connected`).

The route: expand `e^{h√(ts)}` into its exponential series on the quadrant `(0,∞)²`, integrate
term by term (`integral_tsum`, whose absolute-convergence hypothesis is exactly the Tonelli
computation for `|h|`, finite by `lintegral_bilocalIntegrand_lt_top`), and evaluate each term by
`integral_prod_mul` and two Gamma integrals. Signed series convergence is thereby derived from the
integrability of the positive integrand at `|h|`, never the other way round.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The quadrant measure `(0,∞) × (0,∞)`. -/
local notation "P₊" =>
  Measure.prod (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioi (0 : ℝ)))

/-- The bilocal integrand as a function on `ℝ × ℝ`. -/
noncomputable def bilocalFn (lam a b h : ℝ) (p : ℝ × ℝ) : ℝ := bilocalIntegrand lam a b h p.1 p.2

/-- The `r`-th cross-pairing term `t^{λ−1}s^{λ−1}e^{−at−bs} (h√(ts))^r / r!`. -/
noncomputable def bilocalTerm (lam a b h : ℝ) (r : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ (lam - 1) * p.2 ^ (lam - 1) * Real.exp (-a * p.1 - b * p.2) *
    ((h * Real.sqrt (p.1 * p.2)) ^ r / (r.factorial : ℝ))

/-- The `r`-th coefficient `(h^r / r!) Γ(λ + r/2)² (ab)^{−(λ + r/2)}`. -/
noncomputable def bilocalCoeff (lam a b h : ℝ) (r : ℕ) : ℝ :=
  h ^ r / (r.factorial : ℝ) * (Real.Gamma (lam + r / 2) ^ 2 * (a * b) ^ (-(lam + r / 2)))

theorem measurableSet_quadrant : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  measurableSet_Ioi.prod measurableSet_Ioi

theorem measurable_bilocalFn (lam a b h : ℝ) : Measurable (bilocalFn lam a b h) := by
  unfold bilocalFn bilocalIntegrand
  fun_prop

theorem measurable_bilocalTerm (lam a b h : ℝ) (r : ℕ) : Measurable (bilocalTerm lam a b h r) := by
  unfold bilocalTerm
  fun_prop

theorem exp_eq_tsum_pow_div (x : ℝ) : Real.exp x = ∑' r : ℕ, x ^ r / (r.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun NormedSpace.exp_eq_tsum_div x

/-- Pointwise expansion `bilocalFn = ∑_r bilocalTerm r` (everywhere on `ℝ × ℝ`). -/
theorem bilocalFn_eq_tsum (lam a b h : ℝ) (p : ℝ × ℝ) :
    bilocalFn lam a b h p = ∑' r : ℕ, bilocalTerm lam a b h r p := by
  unfold bilocalFn bilocalIntegrand bilocalTerm
  rw [Real.exp_add, exp_eq_tsum_pow_div (h * Real.sqrt (p.1 * p.2))]
  simp only [← tsum_mul_left]
  exact tsum_congr fun r => by ring

theorem summable_bilocalTerm (lam a b h : ℝ) (p : ℝ × ℝ) :
    Summable fun r : ℕ => bilocalTerm lam a b h r p :=
  (Real.summable_pow_div_factorial (h * Real.sqrt (p.1 * p.2))).mul_left _

theorem bilocalTerm_nonneg {lam a b h : ℝ} (hh : 0 ≤ h) {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (r : ℕ) : 0 ≤ bilocalTerm lam a b h r p := by
  have ht : 0 < p.1 := hp.1
  have hs : 0 < p.2 := hp.2
  unfold bilocalTerm
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hs.le _))
    (Real.exp_pos _).le) (div_nonneg (pow_nonneg (mul_nonneg hh (Real.sqrt_nonneg _)) _)
      (Nat.cast_nonneg _))

theorem bilocalFn_nonneg {lam a b h : ℝ} {p : ℝ × ℝ} (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    0 ≤ bilocalFn lam a b h p := by
  have ht : 0 < p.1 := hp.1
  have hs : 0 < p.2 := hp.2
  unfold bilocalFn bilocalIntegrand
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hs.le _))
    (Real.exp_pos _).le

theorem abs_bilocalTerm {lam a b h : ℝ} {p : ℝ × ℝ} (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
    (r : ℕ) :
    |bilocalTerm lam a b h r p| = bilocalTerm lam a b |h| r p := by
  have ht : 0 < p.1 := hp.1
  have hs : 0 < p.2 := hp.2
  unfold bilocalTerm
  rw [abs_mul, abs_of_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hs _))
    (Real.exp_pos _)), abs_div, abs_pow, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Nat.abs_cast]

/-! ### Tonelli for the absolute series -/

theorem lintegral_ofReal_bilocalFn (lam a b h : ℝ) :
    ∫⁻ p, ENNReal.ofReal (bilocalFn lam a b h p) ∂P₊ =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b h t s) :=
  lintegral_prod _ (measurable_bilocalFn lam a b h).ennreal_ofReal.aemeasurable

/-- For `h ≥ 0`, `∑_r ∫ bilocalTerm r = ∬ bilocalIntegrand` in `ℝ≥0∞`. -/
theorem tsum_lintegral_bilocalTerm (lam a b h : ℝ) (hh : 0 ≤ h) :
    ∑' r : ℕ, ∫⁻ p, ENNReal.ofReal (bilocalTerm lam a b h r p) ∂P₊ =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b h t s) := by
  rw [← lintegral_tsum fun r => (measurable_bilocalTerm lam a b h r).ennreal_ofReal.aemeasurable,
    ← lintegral_ofReal_bilocalFn, Measure.prod_restrict]
  refine setLIntegral_congr_fun measurableSet_quadrant fun p hp => ?_
  rw [bilocalFn_eq_tsum, ENNReal.ofReal_tsum_of_nonneg (bilocalTerm_nonneg hh hp)
    (summable_bilocalTerm lam a b h p)]

theorem lintegral_enorm_bilocalTerm (lam a b h : ℝ) (r : ℕ) :
    ∫⁻ p, ‖bilocalTerm lam a b h r p‖ₑ ∂P₊ =
      ∫⁻ p, ENNReal.ofReal (bilocalTerm lam a b |h| r p) ∂P₊ := by
  rw [Measure.prod_restrict]
  refine setLIntegral_congr_fun measurableSet_quadrant fun p hp => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_bilocalTerm hp]

/-- Absolute convergence of the term integrals for `|h| < 2√(ab)`. -/
theorem tsum_lintegral_enorm_bilocalTerm_ne_top (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a)
    (hb : 0 < b) (hh : |h| < 2 * Real.sqrt (a * b)) :
    ∑' r : ℕ, ∫⁻ p, ‖bilocalTerm lam a b h r p‖ₑ ∂P₊ ≠ ⊤ := by
  simp_rw [lintegral_enorm_bilocalTerm]
  rw [tsum_lintegral_bilocalTerm lam a b |h| (abs_nonneg h)]
  exact (lintegral_bilocalIntegrand_lt_top lam a b |h| hlam ha hb hh).ne

/-! ### The term integrals -/

theorem sqrt_pow_eq_rpow {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    Real.sqrt t ^ r = t ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  ring

theorem bilocalTerm_eq_prod {lam a b h : ℝ} (r : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    bilocalTerm lam a b h r p = h ^ r / (r.factorial : ℝ) *
      (p.1 ^ (lam + r / 2 - 1) * Real.exp (-(a * p.1)) *
        (p.2 ^ (lam + r / 2 - 1) * Real.exp (-(b * p.2)))) := by
  have ht : 0 < p.1 := hp.1
  have hs : 0 < p.2 := hp.2
  unfold bilocalTerm
  rw [Real.sqrt_mul ht.le, mul_pow, mul_pow, sqrt_pow_eq_rpow ht.le, sqrt_pow_eq_rpow hs.le,
    show lam + (r : ℝ) / 2 - 1 = (lam - 1) + (r : ℝ) / 2 by ring, Real.rpow_add ht,
    Real.rpow_add hs, show Real.exp (-a * p.1 - b * p.2) =
      Real.exp (-(a * p.1)) * Real.exp (-(b * p.2)) by rw [← Real.exp_add]; congr 1; ring]
  ring

/-- `∫ bilocalTerm r = (h^r/r!) Γ(λ + r/2)² (ab)^{−(λ + r/2)}`. -/
theorem integral_bilocalTerm (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (r : ℕ) : ∫ p, bilocalTerm lam a b h r p ∂P₊ = bilocalCoeff lam a b h r := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : ∫ p, bilocalTerm lam a b h r p ∂P₊ = ∫ p, h ^ r / (r.factorial : ℝ) *
      (p.1 ^ (lam + r / 2 - 1) * Real.exp (-(a * p.1)) *
        (p.2 ^ (lam + r / 2 - 1) * Real.exp (-(b * p.2)))) ∂P₊ := by
    rw [Measure.prod_restrict]
    exact setIntegral_congr_fun measurableSet_quadrant fun p hp => bilocalTerm_eq_prod r hp
  rw [h1, integral_const_mul, integral_prod_mul
      (fun t : ℝ => t ^ (lam + r / 2 - 1) * Real.exp (-(a * t)))
      (fun s : ℝ => s ^ (lam + r / 2 - 1) * Real.exp (-(b * s))),
    integral_rpow_mul_exp_neg_mul _ _ (by linarith) ha,
    integral_rpow_mul_exp_neg_mul _ _ (by linarith) hb, bilocalCoeff,
    Real.mul_rpow ha.le hb.le]
  ring

/-! ### The series -/

/-- **Cross-pairing series** for `|h| < 2√(ab)`:
`∬ bilocalIntegrand = ∑_r (h^r/r!) Γ(λ + r/2)² (ab)^{−(λ + r/2)}`. -/
theorem integral_bilocalFn_eq_tsum (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hh : |h| < 2 * Real.sqrt (a * b)) :
    ∫ p, bilocalFn lam a b h p ∂P₊ = ∑' r : ℕ, bilocalCoeff lam a b h r := by
  simp_rw [bilocalFn_eq_tsum]
  rw [integral_tsum (fun r => (measurable_bilocalTerm lam a b h r).aestronglyMeasurable)
    (tsum_lintegral_enorm_bilocalTerm_ne_top lam a b h hlam ha hb hh)]
  exact tsum_congr fun r => integral_bilocalTerm lam a b h hlam ha hb r

/-- **Absolute convergence** of the cross-pairing series for `|h| < 2√(ab)`. -/
theorem summable_bilocalCoeff (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hh : |h| < 2 * Real.sqrt (a * b)) : Summable (bilocalCoeff lam a b h) := by
  have hsum : Summable fun r : ℕ => (∫⁻ p, ‖bilocalTerm lam a b h r p‖ₑ ∂P₊).toReal :=
    ENNReal.summable_toReal (tsum_lintegral_enorm_bilocalTerm_ne_top lam a b h hlam ha hb hh)
  refine Summable.of_norm_bounded hsum fun r => ?_
  rw [← integral_bilocalTerm lam a b h hlam ha hb r]
  simp_rw [← ofReal_norm]
  exact norm_integral_le_lintegral_norm _

theorem integral_bilocalFn_eq_toReal (lam a b h : ℝ) :
    ∫ p, bilocalFn lam a b h p ∂P₊ =
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b h t s)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae ?_ (measurable_bilocalFn lam a b h).aestronglyMeasurable,
    lintegral_ofReal_bilocalFn]
  rw [Measure.prod_restrict]
  exact ae_restrict_of_forall_mem measurableSet_quadrant fun p hp => bilocalFn_nonneg hp

/-- `∫ bilocalFn` at `h = 0` is the disconnected part `Γ(λ)²(ab)^{−λ}`. -/
theorem integral_bilocalFn_zero (lam a b : ℝ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) :
    ∫ p, bilocalFn lam a b 0 p ∂P₊ = Real.Gamma lam ^ 2 * (a * b) ^ (-lam) := by
  have h0 : ∀ p : ℝ × ℝ, bilocalFn lam a b 0 p = bilocalTerm lam a b 0 0 p := fun p => by
    simp [bilocalFn, bilocalIntegrand, bilocalTerm]
  simp_rw [h0]
  rw [integral_bilocalTerm lam a b 0 hlam ha hb 0]
  simp [bilocalCoeff]

theorem integrable_bilocalFn (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hh : h < 2 * Real.sqrt (a * b)) : Integrable (bilocalFn lam a b h) P₊ := by
  refine ⟨(measurable_bilocalFn lam a b h).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have : ∫⁻ p, ‖bilocalFn lam a b h p‖ₑ ∂P₊ = ∫⁻ p, ENNReal.ofReal (bilocalFn lam a b h p) ∂P₊ := by
    rw [Measure.prod_restrict]
    exact setLIntegral_congr_fun measurableSet_quadrant fun p hp =>
      Real.enorm_eq_ofReal (bilocalFn_nonneg hp)
  rw [this, lintegral_ofReal_bilocalFn]
  exact lintegral_bilocalIntegrand_lt_top lam a b h hlam ha hb hh

/-! ### For the Gaussian vector -/

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

theorem integral_fluctuation_mul_fluctuation_eq_quadrant (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A =
      ∫ p, bilocalFn lam (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) p ∂P₊ := by
  rw [integral_fluctuation_mul_fluctuation A β lam hβ hlam i j, integral_bilocalFn_eq_toReal]

/-- **The cross-pairing series for `E[S_λ(G_i) S_λ(G_j)]`**: for `a, b > 0` and `|h| < 2√(ab)`,
`E[S_λ(G_i) S_λ(G_j)] = ∑_r (h^r/r!) Γ(λ + r/2)² (ab)^{−(λ + r/2)}`. -/
theorem integral_fluctuation_mul_fluctuation_eq_tsum (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : |β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j| <
      2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)))) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A =
      ∑' r : ℕ, bilocalCoeff lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) r := by
  rw [integral_fluctuation_mul_fluctuation_eq_quadrant A β lam hβ hlam i j]
  exact integral_bilocalFn_eq_tsum _ _ _ _ hlam (mul_pos hβ hi) (mul_pos hβ hj) hh

/-- **Covariance as the connected series**: `Cov(S_λ(G_i), S_λ(G_j)) = ∑_{r ≥ 1} c_r`. -/
theorem cov_fluctuation_eq_tsum (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : |β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j| <
      2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)))) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A -
      (∫ g, fluctuation β lam (g i) ∂gaussianVector A) *
        ∫ g, fluctuation β lam (g j) ∂gaussianVector A =
      ∑' r : ℕ, bilocalCoeff lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) (r + 1) := by
  rw [integral_fluctuation_mul_fluctuation_eq_tsum A β lam hβ hlam i j hi hj hh,
    (summable_bilocalCoeff _ _ _ _ hlam (mul_pos hβ hi) (mul_pos hβ hj) hh).tsum_eq_zero_add,
    (integral_fluctuation_gaussianVector A β lam hβ hlam i hi).2,
    (integral_fluctuation_gaussianVector A β lam hβ hlam j hj).2]
  simp only [bilocalCoeff, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.cast_zero,
    zero_div, add_zero, one_mul]
  rw [Real.mul_rpow (mul_pos hβ hi).le (mul_pos hβ hj).le]
  ring

/-- **Covariance as the connected integral**:
`Cov(S_λ(G_i), S_λ(G_j)) = ∬ t^{λ−1}s^{λ−1} e^{−at−bs} (e^{h√(ts)} − 1)` for `h < 2√(ab)`. -/
theorem cov_fluctuation_eq_connected (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j <
      2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)))) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A -
      (∫ g, fluctuation β lam (g i) ∂gaussianVector A) *
        ∫ g, fluctuation β lam (g j) ∂gaussianVector A =
      ∫ p, p.1 ^ (lam - 1) * p.2 ^ (lam - 1) *
        Real.exp (-(β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) * p.1 -
          β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) * p.2) *
        (Real.exp (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          Real.sqrt (p.1 * p.2)) - 1) ∂P₊ := by
  have ha := mul_pos hβ hi
  have hb := mul_pos hβ hj
  rw [integral_fluctuation_mul_fluctuation_eq_quadrant A β lam hβ hlam i j,
    (integral_fluctuation_gaussianVector A β lam hβ hlam i hi).2,
    (integral_fluctuation_gaussianVector A β lam hβ hlam j hj).2,
    show Real.Gamma lam * (β * (1 - β * (A * A.transpose :
      Matrix (Fin m) (Fin m) ℝ) i i / 2)) ^ (-lam) * (Real.Gamma lam *
      (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) ^ (-lam)) =
      Real.Gamma lam ^ 2 * ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))) ^ (-lam) by
      rw [Real.mul_rpow ha.le hb.le]; ring,
    ← integral_bilocalFn_zero lam _ _ hlam ha hb,
    ← integral_sub (integrable_bilocalFn _ _ _ _ hlam ha hb hh)
      (integrable_bilocalFn _ _ _ 0 hlam ha hb
        (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos ha hb))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [bilocalFn, bilocalIntegrand]
  rw [zero_mul, add_zero, Real.exp_add]
  ring

end Grammar
