/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Algebra.Order.Chebyshev
import ResolutionCommon.Probability.GaussianMoments
import Grammar.GaussianQuadraticTilt

/-!
# The predictive remainder in the normal-location model (companion note, model test)

Discharge of the predictive-remainder certificate of the companion note in the normal-location
model `X ~ N(w, 1)` with prior `N(0, a⁻¹)` and tempered likelihood at inverse temperature `β`.

* The Gaussian `N(m, v)` is the image of the standard Gaussian under `z ↦ m + √v z`
  (`gaussianReal_eq_map`), so every integral against it is a standard-Gaussian integral
  (`integral_gaussianReal_eq_std`).
* The centred negative excess loss under `N(m, v)` is `(x − m)√v Z − (v/2)(Z² − 1)`
  (`integral_negLoss`, `negLoss_centred`), whence the absolute centred third moment is bounded
  by `4(C₃|x − m|³ v^{3/2} + C₆(v/2)³)` with `C₃ = 𝔼|Z|³`, `C₆ = 𝔼|Z² − 1|³`
  (`integral_abs_centred_negLoss_cube_le`).
* The tempered posterior after `n` observations is `N(m_n, d_n⁻¹)` with `d_n = a + βn` and
  `m_n = β∑xᵢ/d_n` (`normalPosterior_eq_gaussian`); its exponential tilts at `t ∈ [0,1]` have
  `|x − m'| ≤ |x − m_n|` and `v' ≤ d_n⁻¹`, so the tilted third moments are dominated by the
  envelope `S_n(x) = 4(C₃|x − m_n|³ d_n^{−3/2} + C₆ d_n^{−3}/8)` uniformly in `t`
  (`tiltAbsThird_negLoss_le`) and `|R_n(x)| ≤ S_n(x)/6` (`abs_predictiveRemainder_negLoss_le`).
* The remainder is a measurable function of `(m, x)` (`measurable_predictiveRemainder_negLoss`),
  and for a standard-normal training sequence and test point the expected envelope is
  `O(d_n^{−3/2})` (`integral_abs_predictiveRemainder_le`), giving both certificates
  `n·𝔼𝔼_{X*}|R_n(X*)| → 0` and `n·𝔼(1/n)∑ᵢ|R_n(Xᵢ)| → 0`
  (`normalLocation_predictive_remainder_L1`).

Only the marginal law of each data point is used; independence is not needed for the certificate.
-/

open MeasureTheory ProbabilityTheory Filter Set Real Topology
open scoped ENNReal NNReal

namespace Grammar

attribute [fun_prop] continuous_negLoss measurable_negLoss

/-! ### The Gaussian as an image of the standard Gaussian -/

/-- `N(m, v)` is the image of `N(0, 1)` under `z ↦ m + √v z`. -/
theorem gaussianReal_eq_map (m : ℝ) (v : ℝ≥0) :
    gaussianReal m v = (gaussianReal 0 1).map (fun z => m + √(v : ℝ) * z) := by
  have h1 : (gaussianReal 0 1).map (fun z => √(v : ℝ) * z) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  have h2 : (fun z => m + √(v : ℝ) * z) = (fun z => m + z) ∘ (fun z => √(v : ℝ) * z) := rfl
  rw [h2, ← Measure.map_map (measurable_const_add m) (measurable_const_mul _), h1,
    gaussianReal_map_const_add, zero_add]

/-- Integrals against `N(m, v)` are standard-Gaussian integrals of `g(m + √v z)`. -/
theorem integral_gaussianReal_eq_std (m : ℝ) (v : ℝ≥0) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal m v)) :
    ∫ w, g w ∂gaussianReal m v = ∫ z, g (m + √(v : ℝ) * z) ∂gaussianReal 0 1 := by
  rw [gaussianReal_eq_map] at hg ⊢
  exact integral_map (by fun_prop) hg

theorem integral_id_std : ∫ z, z ∂gaussianReal 0 1 = 0 := by
  simp [integral_id_gaussianReal]

theorem integral_sq_std : ∫ z, z ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at h
  simp at h
  linarith

theorem integrable_pow_std (k : ℕ) : Integrable (fun z : ℝ => z ^ k) (gaussianReal 0 1) :=
  ResolutionCommon.integrable_pow_gaussianReal 0 1 k

theorem integrable_abs_pow_std (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k) (gaussianReal 0 1) := by
  simpa [abs_pow] using (integrable_pow_std k).abs

theorem integrable_abs_sq_sub_one_cube_std :
    Integrable (fun z : ℝ => |z ^ 2 - 1| ^ 3) (gaussianReal 0 1) := by
  have h : (fun z : ℝ => |z ^ 2 - 1| ^ 3) =
      fun z => |z ^ 6 - 3 * z ^ 4 + 3 * z ^ 2 - 1| := by
    funext z
    rw [← abs_pow]
    ring_nf
  rw [h]
  exact ((((integrable_pow_std 6).sub ((integrable_pow_std 4).const_mul 3)).add
    ((integrable_pow_std 2).const_mul 3)).sub (integrable_const 1)).abs

/-- `C₃ = 𝔼|Z|³` for the standard Gaussian. -/
noncomputable def absMom3 : ℝ := ∫ z, |z| ^ 3 ∂gaussianReal 0 1

/-- `C₆ = 𝔼|Z² − 1|³` for the standard Gaussian. -/
noncomputable def absMomSq3 : ℝ := ∫ z, |z ^ 2 - 1| ^ 3 ∂gaussianReal 0 1

theorem absMom3_nonneg : 0 ≤ absMom3 := integral_nonneg fun _ => by positivity

theorem absMomSq3_nonneg : 0 ≤ absMomSq3 := integral_nonneg fun _ => by positivity

/-- A standard-Gaussian quadratic integral. -/
theorem integral_quadratic_std (c₀ c₁ c₂ : ℝ) :
    ∫ z, (c₀ + c₁ * z + c₂ * z ^ 2) ∂gaussianReal 0 1 = c₀ + c₂ := by
  have h1 : Integrable (fun z : ℝ => c₁ * z) (gaussianReal 0 1) :=
    ((integrable_pow_std 1).const_mul c₁).congr (Eventually.of_forall fun z => by simp)
  have h2 : Integrable (fun z : ℝ => c₀ + c₁ * z) (gaussianReal 0 1) := (integrable_const c₀).add h1
  rw [integral_add h2 ((integrable_pow_std 2).const_mul c₂), integral_add (integrable_const c₀) h1,
    integral_const_mul, integral_const_mul, integral_id_std, integral_sq_std]
  simp

/-! ### The negative excess loss under a Gaussian -/

/-- The mean of the negative excess loss under `N(m, v)`. -/
theorem integral_negLoss (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    ∫ w, negLoss x w ∂gaussianReal m v = -(m ^ 2 + v) / 2 + x * m := by
  rw [integral_gaussianReal_eq_std m v (continuous_negLoss x).aestronglyMeasurable]
  have hs : √(v : ℝ) * √(v : ℝ) = v := Real.mul_self_sqrt v.coe_nonneg
  have h : (fun z => negLoss x (m + √(v : ℝ) * z)) =
      fun z => (-(m ^ 2) / 2 + x * m) + ((x - m) * √(v : ℝ)) * z + (-(v : ℝ) / 2) * z ^ 2 := by
    funext z
    unfold negLoss
    linear_combination (-(z ^ 2 / 2)) * hs
  rw [h, integral_quadratic_std]
  ring

/-- The centring identity `f(x, m + √v z) − ⟨f⟩ = (x − m)√v z − (v/2)(z² − 1)`. -/
theorem negLoss_centred (m : ℝ) (v : ℝ≥0) (x z : ℝ) :
    negLoss x (m + √(v : ℝ) * z) - (-(m ^ 2 + v) / 2 + x * m) =
      (x - m) * √(v : ℝ) * z - (v : ℝ) / 2 * (z ^ 2 - 1) := by
  have hs : √(v : ℝ) * √(v : ℝ) = v := Real.mul_self_sqrt v.coe_nonneg
  unfold negLoss
  linear_combination (-(z ^ 2 / 2)) * hs

theorem add_pow_three_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) ^ 3 ≤ 4 * (p ^ 3 + q ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hp hq) (sq_nonneg (p - q))]

/-- ★ **Third-moment envelope**: the absolute centred third moment of the negative excess loss
under `N(m, v)` is at most `4(C₃|x − m|³ v^{3/2} + C₆(v/2)³)`. -/
theorem integral_abs_centred_negLoss_cube_le (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    ∫ w, |negLoss x w - ∫ w', negLoss x w' ∂gaussianReal m v| ^ 3 ∂gaussianReal m v ≤
      4 * (absMom3 * |x - m| ^ 3 * √(v : ℝ) ^ 3 + absMomSq3 * ((v : ℝ) / 2) ^ 3) := by
  rw [integral_negLoss, integral_gaussianReal_eq_std m v
    (g := fun w => |negLoss x w - (-(m ^ 2 + v) / 2 + x * m)| ^ 3)
    (Continuous.aestronglyMeasurable (by fun_prop))]
  have hint : Integrable (fun z : ℝ => 4 * (|x - m| ^ 3 * √(v : ℝ) ^ 3 * |z| ^ 3 +
      ((v : ℝ) / 2) ^ 3 * |z ^ 2 - 1| ^ 3)) (gaussianReal 0 1) :=
    (((integrable_abs_pow_std 3).const_mul _).add
      (integrable_abs_sq_sub_one_cube_std.const_mul _)).const_mul 4
  calc ∫ z, |negLoss x (m + √(v : ℝ) * z) - (-(m ^ 2 + v) / 2 + x * m)| ^ 3 ∂gaussianReal 0 1
      ≤ ∫ z, 4 * (|x - m| ^ 3 * √(v : ℝ) ^ 3 * |z| ^ 3 +
          ((v : ℝ) / 2) ^ 3 * |z ^ 2 - 1| ^ 3) ∂gaussianReal 0 1 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hint
          (Eventually.of_forall fun z => ?_)
        simp only
        rw [negLoss_centred]
        have h1 : |(x - m) * √(v : ℝ) * z - (v : ℝ) / 2 * (z ^ 2 - 1)| ≤
            |x - m| * √(v : ℝ) * |z| + (v : ℝ) / 2 * |z ^ 2 - 1| := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (v : ℝ) / 2)]
        calc |(x - m) * √(v : ℝ) * z - (v : ℝ) / 2 * (z ^ 2 - 1)| ^ 3
            ≤ (|x - m| * √(v : ℝ) * |z| + (v : ℝ) / 2 * |z ^ 2 - 1|) ^ 3 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 3
          _ ≤ 4 * ((|x - m| * √(v : ℝ) * |z|) ^ 3 + ((v : ℝ) / 2 * |z ^ 2 - 1|) ^ 3) :=
              add_pow_three_le _ _ (by positivity) (by positivity)
          _ = 4 * (|x - m| ^ 3 * √(v : ℝ) ^ 3 * |z| ^ 3 +
              ((v : ℝ) / 2) ^ 3 * |z ^ 2 - 1| ^ 3) := by ring
    _ = 4 * (absMom3 * |x - m| ^ 3 * √(v : ℝ) ^ 3 + absMomSq3 * ((v : ℝ) / 2) ^ 3) := by
        rw [integral_const_mul, integral_add ((integrable_abs_pow_std 3).const_mul _)
          (integrable_abs_sq_sub_one_cube_std.const_mul _), integral_const_mul,
          integral_const_mul]
        unfold absMom3 absMomSq3
        ring

/-! ### The normal-location model -/

/-- The prior variance `a⁻¹` as a nonnegative real. -/
noncomputable def priorVar (a : ℝ) : ℝ≥0 := Real.toNNReal a⁻¹

/-- The prior `N(0, a⁻¹)`. -/
noncomputable def normalPrior (a : ℝ) : Measure ℝ := gaussianReal 0 (priorVar a)

/-- The tempered negative log-likelihood `β ∑ᵢ (xᵢ − w)²/2` of `n` observations. -/
noncomputable def nll (β : ℝ) {n : ℕ} (x : Fin n → ℝ) (w : ℝ) : ℝ := β * ∑ i, (x i - w) ^ 2 / 2

/-- The posterior precision `d_n = a + βn`. -/
noncomputable def postPrec (a β : ℝ) (n : ℕ) : ℝ := a + β * n

/-- The posterior variance `d_n⁻¹`. -/
noncomputable def postVar (a β : ℝ) (n : ℕ) : ℝ≥0 := tiltVar (priorVar a) (β * n)

/-- The posterior mean `β∑xᵢ/d_n`. -/
noncomputable def postMean (a β : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  tiltMeanG 0 (priorVar a) (β * n) (β * ∑ i, x i)

/-- The normalising constant `∫ e^{−nll} dprior`. -/
noncomputable def normalPartition (a β : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∫ w, exp (-nll β x w) ∂normalPrior a

/-- The tempered posterior `Z⁻¹ e^{−nll} · prior`. -/
noncomputable def normalPosterior (a β : ℝ) {n : ℕ} (x : Fin n → ℝ) : Measure ℝ :=
  (ENNReal.ofReal (normalPartition a β x))⁻¹ •
    (normalPrior a).withDensity (fun w => ENNReal.ofReal (exp (-nll β x w)))

variable {a β : ℝ} {n : ℕ}

theorem coe_priorVar (ha : 0 < a) : ((priorVar a : ℝ≥0) : ℝ) = a⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 ha.le)

theorem priorVar_ne_zero (ha : 0 < a) : priorVar a ≠ 0 := by
  rw [← NNReal.coe_ne_zero, coe_priorVar ha]
  exact inv_ne_zero ha.ne'

theorem postPrec_pos (ha : 0 < a) (hβ : 0 < β) : 0 < postPrec a β n := by
  unfold postPrec
  positivity

theorem inv_priorVar_add (ha : 0 < a) (t : ℝ) : ((priorVar a : ℝ≥0) : ℝ)⁻¹ + t = a + t := by
  rw [coe_priorVar ha, inv_inv]

theorem coe_postVar (ha : 0 < a) (hβ : 0 < β) :
    ((postVar a β n : ℝ≥0) : ℝ) = (postPrec a β n)⁻¹ := by
  unfold postVar
  rw [coe_tiltVar (by rw [inv_priorVar_add ha]; exact postPrec_pos ha hβ), inv_priorVar_add ha]
  rfl

theorem postVar_ne_zero (ha : 0 < a) (hβ : 0 < β) : postVar a β n ≠ 0 := by
  rw [← NNReal.coe_ne_zero, coe_postVar ha hβ]
  exact inv_ne_zero (postPrec_pos ha hβ).ne'

theorem postMean_eq (ha : 0 < a) (x : Fin n → ℝ) :
    postMean a β x = (postPrec a β n)⁻¹ * (β * ∑ i, x i) := by
  unfold postMean tiltMeanG
  rw [inv_priorVar_add ha, zero_div, zero_add]
  rfl

theorem exp_neg_nll (β : ℝ) (x : Fin n → ℝ) (w : ℝ) :
    exp (-nll β x w) = exp (-(β * ∑ i, x i ^ 2 / 2)) *
      exp (-(β * n * w ^ 2 / 2) + (β * ∑ i, x i) * w) := by
  rw [← exp_add]
  congr 1
  unfold nll
  have h : ∑ i, (x i - w) ^ 2 / 2 = ∑ i, (x i ^ 2 / 2 - x i * w + w ^ 2 / 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- ★★ **The tempered posterior of the normal-location model is Gaussian**: `N(m_n, d_n⁻¹)`. -/
theorem normalPosterior_eq_gaussian (ha : 0 < a) (hβ : 0 < β) (x : Fin n → ℝ) :
    normalPosterior a β x = gaussianReal (postMean a β x) (postVar a β n) := by
  have hv := priorVar_ne_zero ha
  have hc : 0 < ((priorVar a : ℝ≥0) : ℝ)⁻¹ + β * n := by
    rw [inv_priorVar_add ha]
    exact postPrec_pos ha hβ
  have hK0 : 0 < exp (-(β * ∑ i, x i ^ 2 / 2)) := exp_pos _
  have hdens : (normalPrior a).withDensity (fun w => ENNReal.ofReal (exp (-nll β x w))) =
      ENNReal.ofReal (exp (-(β * ∑ i, x i ^ 2 / 2))) •
        ENNReal.ofReal (tiltConst 0 (priorVar a) (β * n) (β * ∑ i, x i)) •
          gaussianReal (postMean a β x) (postVar a β n) := by
    have h : (fun w => ENNReal.ofReal (exp (-nll β x w))) =
        ENNReal.ofReal (exp (-(β * ∑ i, x i ^ 2 / 2))) •
          fun w => ENNReal.ofReal (exp (-(β * n * w ^ 2 / 2) + (β * ∑ i, x i) * w)) := by
      funext w
      simp only [Pi.smul_apply, smul_eq_mul, exp_neg_nll, ENNReal.ofReal_mul hK0.le]
    unfold normalPrior
    rw [h, withDensity_smul _ (measurable_exp_quadratic _ _),
      gaussianReal_withDensity_quadratic hv hc]
    rfl
  have hZ : normalPartition a β x =
      exp (-(β * ∑ i, x i ^ 2 / 2)) * tiltConst 0 (priorVar a) (β * n) (β * ∑ i, x i) := by
    unfold normalPartition normalPrior
    simp_rw [exp_neg_nll]
    rw [integral_const_mul, integral_exp_quadratic_gaussianReal hv hc]
  unfold normalPosterior
  rw [hdens, hZ, smul_smul (ENNReal.ofReal _), ← ENNReal.ofReal_mul hK0.le, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (mul_pos hK0 (tiltConst_pos hv hc))).ne'
      ENNReal.ofReal_ne_top, one_smul]

/-! ### Tilts of the posterior and the pointwise remainder bound -/

/-- The third-moment envelope `S(v, m, x) = 4(C₃|x − m|³ v^{3/2} + C₆(v/2)³)`. -/
noncomputable def envelope (v m x : ℝ) : ℝ :=
  4 * (absMom3 * |x - m| ^ 3 * √v ^ 3 + absMomSq3 * (v / 2) ^ 3)

theorem envelope_mono {v v' m m' x : ℝ} (hv' : 0 ≤ v') (hv : v' ≤ v) (hm : |x - m'| ≤ |x - m|) :
    envelope v' m' x ≤ envelope v m x := by
  unfold envelope
  have h3 := absMom3_nonneg
  have h6 := absMomSq3_nonneg
  have hs : √v' ≤ √v := Real.sqrt_le_sqrt hv
  gcongr

/-- A tilt at `t ≥ 0` moves the Gaussian mean towards the tilting point `x`. -/
theorem abs_sub_tiltMeanG_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {x t : ℝ} (ht : 0 ≤ t) :
    |x - tiltMeanG m v t (t * x)| ≤ |x - m| := by
  have hv' : (0 : ℝ) < v := by positivity
  have hd : 0 < ((v : ℝ))⁻¹ := inv_pos.2 hv'
  have hdt : ((v : ℝ))⁻¹ + t ≠ 0 := by positivity
  have h : x - tiltMeanG m v t (t * x) = ((v : ℝ)⁻¹ / ((v : ℝ)⁻¹ + t)) * (x - m) := by
    unfold tiltMeanG
    field_simp
    ring
  rw [h, abs_mul, abs_of_pos (div_pos hd (by positivity))]
  exact mul_le_of_le_one_left (abs_nonneg _) (div_le_one_of_le₀ (by linarith) (by positivity))

/-- A tilt at `t ≥ 0` shrinks the Gaussian variance. -/
theorem coe_tiltVar_le {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ((tiltVar v t : ℝ≥0) : ℝ) ≤ v := by
  have hv' : (0 : ℝ) < v := by positivity
  have hd : 0 < ((v : ℝ))⁻¹ := inv_pos.2 hv'
  rw [coe_tiltVar (by positivity)]
  calc ((v : ℝ)⁻¹ + t)⁻¹ ≤ ((v : ℝ)⁻¹)⁻¹ := inv_anti₀ hd (by linarith)
    _ = v := inv_inv _

/-- ★ The tilted absolute centred third moments of the negative excess loss under `N(m, v)` are
dominated by the envelope `S(v, m, x)`, uniformly in `t ∈ [0,1]`. -/
theorem tiltAbsThird_negLoss_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    tiltAbsThird (negLoss x) (gaussianReal m v) t ≤ envelope v m x := by
  have hv' : (0 : ℝ) < v := by positivity
  have hd : 0 < ((v : ℝ))⁻¹ + t := by
    have := inv_pos.2 hv'
    linarith [ht.1]
  rw [tiltAbsThird_negLoss_eq hv hd]
  refine (integral_abs_centred_negLoss_cube_le _ _ x).trans ?_
  exact envelope_mono (tiltVar v t).coe_nonneg (coe_tiltVar_le hv ht.1)
    (abs_sub_tiltMeanG_le hv ht.1)

/-- ★★ **Pointwise remainder bound** `|R(m, v, x)| ≤ S(v, m, x)/6` for the normal-location model
under any nondegenerate Gaussian `N(m, v)`. -/
theorem abs_predictiveRemainder_negLoss_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    |predictiveRemainder (negLoss x) (gaussianReal m v)| ≤ envelope v m x / 6 :=
  abs_predictiveRemainder_le (Icc_subset_interior_integrableExpSet_negLoss hv x)
    fun _ ht => tiltAbsThird_negLoss_le hv x ht

/-- The envelope at the posterior `N(d⁻¹β∑xᵢ, d⁻¹)`, linearised in `|y|³` and `∑|xᵢ|³`. -/
theorem envelope_div_six_le {d β : ℝ} (hd : 0 < d) (hβ : 0 < β) {n : ℕ} (xs : Fin n → ℝ)
    (y : ℝ) :
    envelope d⁻¹ (d⁻¹ * (β * ∑ i, xs i)) y / 6 ≤
      16 * absMom3 * √d⁻¹ ^ 3 / 6 * |y| ^ 3 +
      16 * absMom3 * √d⁻¹ ^ 3 * ((d⁻¹ * β) ^ 3 * n ^ 2) / 6 * ∑ i, |xs i| ^ 3 +
      4 * absMomSq3 * (d⁻¹ / 2) ^ 3 / 6 := by
  have h3 := absMom3_nonneg
  have h6 := absMomSq3_nonneg
  have hcheb : (∑ i, |xs i|) ^ 3 ≤ n ^ 2 * ∑ i, |xs i| ^ 3 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have h := pow_sum_div_card_le_sum_pow (s := Finset.univ)
        (f := fun i : Fin n => |xs i|) (fun i _ => abs_nonneg _) 2
      rw [Finset.card_univ, Fintype.card_fin, div_le_iff₀ (by positivity)] at h
      norm_num at h
      linarith
  have hm : |d⁻¹ * (β * ∑ i, xs i)| ^ 3 ≤ (d⁻¹ * β) ^ 3 * n ^ 2 * ∑ i, |xs i| ^ 3 := by
    have h1 : |d⁻¹ * (β * ∑ i, xs i)| = d⁻¹ * β * |∑ i, xs i| := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hd), abs_of_pos hβ, mul_assoc]
    rw [h1, mul_pow]
    calc (d⁻¹ * β) ^ 3 * |∑ i, xs i| ^ 3
        ≤ (d⁻¹ * β) ^ 3 * (∑ i, |xs i|) ^ 3 := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (d⁻¹ * β) ^ 3 * (n ^ 2 * ∑ i, |xs i| ^ 3) := by gcongr
      _ = _ := by ring
  have hym : |y - d⁻¹ * (β * ∑ i, xs i)| ^ 3 ≤
      4 * (|y| ^ 3 + (d⁻¹ * β) ^ 3 * n ^ 2 * ∑ i, |xs i| ^ 3) := by
    calc |y - d⁻¹ * (β * ∑ i, xs i)| ^ 3 ≤ (|y| + |d⁻¹ * (β * ∑ i, xs i)|) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) 3
      _ ≤ 4 * (|y| ^ 3 + |d⁻¹ * (β * ∑ i, xs i)| ^ 3) :=
          add_pow_three_le _ _ (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := by gcongr
  unfold envelope
  have hs : 0 ≤ √d⁻¹ ^ 3 := by positivity
  calc 4 * (absMom3 * |y - d⁻¹ * (β * ∑ i, xs i)| ^ 3 * √d⁻¹ ^ 3 +
        absMomSq3 * (d⁻¹ / 2) ^ 3) / 6
      = (4 * absMom3 * √d⁻¹ ^ 3 / 6) * |y - d⁻¹ * (β * ∑ i, xs i)| ^ 3 +
        4 * absMomSq3 * (d⁻¹ / 2) ^ 3 / 6 := by ring
    _ ≤ (4 * absMom3 * √d⁻¹ ^ 3 / 6) *
          (4 * (|y| ^ 3 + (d⁻¹ * β) ^ 3 * n ^ 2 * ∑ i, |xs i| ^ 3)) +
        4 * absMomSq3 * (d⁻¹ / 2) ^ 3 / 6 := by gcongr
    _ = _ := by ring

/-! ### Measurability of the remainder in `(m, x)` -/

theorem measurable_integral_std {F : (ℝ × ℝ) × ℝ → ℝ} (hF : Measurable F) :
    Measurable fun p : ℝ × ℝ => ∫ z, F (p, z) ∂gaussianReal 0 1 :=
  hF.stronglyMeasurable.integral_prod_right'.measurable

/-- ★ The predictive remainder of the normal-location model is a measurable function of the
Gaussian mean and the test point. -/
theorem measurable_predictiveRemainder_negLoss (v : ℝ≥0) :
    Measurable fun p : ℝ × ℝ => predictiveRemainder (negLoss p.2) (gaussianReal p.1 v) := by
  have hcgf : ∀ p : ℝ × ℝ, cgf (negLoss p.2) (gaussianReal p.1 v) 1 =
      Real.log (∫ z, exp (1 * negLoss p.2 (p.1 + √(v : ℝ) * z)) ∂gaussianReal 0 1) := by
    intro p
    unfold cgf mgf
    rw [integral_gaussianReal_eq_std p.1 v (g := fun w => exp (1 * negLoss p.2 w))
      (Continuous.aestronglyMeasurable (by fun_prop))]
  have hvar : ∀ p : ℝ × ℝ, variance (negLoss p.2) (gaussianReal p.1 v) =
      ∫ z, (negLoss p.2 (p.1 + √(v : ℝ) * z) - (-(p.1 ^ 2 + v) / 2 + p.2 * p.1)) ^ 2
        ∂gaussianReal 0 1 := by
    intro p
    rw [variance_eq_integral (measurable_negLoss _).aemeasurable, integral_negLoss,
      integral_gaussianReal_eq_std p.1 v
        (g := fun w => (negLoss p.2 w - (-(p.1 ^ 2 + v) / 2 + p.2 * p.1)) ^ 2)
        (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [predictiveRemainder, hcgf, hvar, integral_negLoss]
  refine (((measurable_integral_std
    (F := fun q => exp (1 * negLoss q.1.2 (q.1.1 + √(v : ℝ) * q.2)))
    (by simp only [negLoss]; fun_prop)).log.sub
    (by fun_prop)).sub ((measurable_integral_std (F := fun q =>
      (negLoss q.1.2 (q.1.1 + √(v : ℝ) * q.2) - (-(q.1.1 ^ 2 + v) / 2 + q.1.2 * q.1.1)) ^ 2)
      (by simp only [negLoss]; fun_prop)).div_const 2))

/-! ### The L¹ certificates -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}

/-- The predictive remainder of the posterior after the first `n` training points `X₀, …, Xₙ₋₁`,
evaluated at the test point `Y`. -/
noncomputable def remainder (a β : ℝ) (n : ℕ) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  predictiveRemainder (negLoss (Y ω)) (normalPosterior a β fun i : Fin n => X i ω)

omit [MeasurableSpace Ω] in
theorem remainder_eq (ha : 0 < a) (hβ : 0 < β) (n : ℕ) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) :
    remainder a β n X Y ω = predictiveRemainder (negLoss (Y ω))
      (gaussianReal (postMean a β fun i : Fin n => X i ω) (postVar a β n)) := by
  unfold remainder
  rw [normalPosterior_eq_gaussian ha hβ]

theorem aemeasurable_postMean (ha : 0 < a) (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) :
    AEMeasurable (fun ω => postMean a β fun i : Fin n => X i ω) P := by
  simp_rw [postMean_eq ha]
  exact ((Finset.aemeasurable_fun_sum (f := fun i : Fin n => X i) Finset.univ
    fun i _ => hX i).const_mul _).const_mul _

theorem aestronglyMeasurable_remainder (ha : 0 < a) (hβ : 0 < β) (hX : ∀ i, AEMeasurable (X i) P)
    (hY : AEMeasurable Y P) (n : ℕ) : AEStronglyMeasurable (remainder a β n X Y) P := by
  have h : remainder a β n X Y = (fun p : ℝ × ℝ => predictiveRemainder (negLoss p.2)
      (gaussianReal p.1 (postVar a β n))) ∘
        fun ω => (postMean a β fun i : Fin n => X i ω, Y ω) := by
    funext ω
    exact remainder_eq ha hβ n X Y ω
  rw [h]
  exact ((measurable_predictiveRemainder_negLoss _).comp_aemeasurable
    ((aemeasurable_postMean ha hX n).prodMk hY)).aestronglyMeasurable

omit [MeasurableSpace Ω] in
/-- The pointwise majorant of `|R_n|`, linear in `|Y|³` and `∑ᵢ|Xᵢ|³`. -/
theorem abs_remainder_le (ha : 0 < a) (hβ : 0 < β) (n : ℕ) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) :
    |remainder a β n X Y ω| ≤
      16 * absMom3 * √(postPrec a β n)⁻¹ ^ 3 / 6 * |Y ω| ^ 3 +
      16 * absMom3 * √(postPrec a β n)⁻¹ ^ 3 * (((postPrec a β n)⁻¹ * β) ^ 3 * n ^ 2) / 6 *
        ∑ i : Fin n, |X i ω| ^ 3 +
      4 * absMomSq3 * ((postPrec a β n)⁻¹ / 2) ^ 3 / 6 := by
  rw [remainder_eq ha hβ]
  refine (abs_predictiveRemainder_negLoss_le (postVar_ne_zero ha hβ) _).trans ?_
  rw [coe_postVar ha hβ, postMean_eq ha]
  exact envelope_div_six_le (postPrec_pos ha hβ) hβ _ _

theorem integral_abs_cube_of_hasLaw (hY : HasLaw Y (gaussianReal 0 1) P) :
    ∫ ω, |Y ω| ^ 3 ∂P = absMom3 := by
  have h := hY.integral_comp (f := fun z => |z| ^ 3) (by fun_prop)
  unfold absMom3
  simpa [Function.comp_def] using h

theorem integrable_abs_cube_of_hasLaw (hY : HasLaw Y (gaussianReal 0 1) P) :
    Integrable (fun ω => |Y ω| ^ 3) P := by
  have h := (integrable_map_measure (f := Y) (g := fun z : ℝ => |z| ^ 3) (by fun_prop)
    hY.aemeasurable).1
  rw [hY.map_eq] at h
  exact h (integrable_abs_pow_std 3)

theorem integrable_majorant [IsProbabilityMeasure P] (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hY : HasLaw Y (gaussianReal 0 1) P) (n : ℕ) (c₁ c₂ c₀ : ℝ) :
    Integrable (fun ω => c₁ * |Y ω| ^ 3 + c₂ * ∑ i : Fin n, |X i ω| ^ 3 + c₀) P := by
  have h12 : Integrable (fun ω => c₁ * |Y ω| ^ 3 + c₂ * ∑ i : Fin n, |X i ω| ^ 3) P :=
    ((integrable_abs_cube_of_hasLaw hY).const_mul c₁).add
      ((integrable_finsetSum (f := fun i : Fin n => fun ω => |X i ω| ^ 3) Finset.univ
        fun i _ => integrable_abs_cube_of_hasLaw (hX i)).const_mul c₂)
  exact h12.add (integrable_const c₀)

theorem integrable_abs_remainder [IsProbabilityMeasure P] (ha : 0 < a) (hβ : 0 < β)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) (n : ℕ) :
    Integrable (fun ω => |remainder a β n X Y ω|) P :=
  (integrable_majorant hX hY n _ _ _).mono'
    (aestronglyMeasurable_remainder ha hβ (fun i => (hX i).aemeasurable) hY.aemeasurable n).norm
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_remainder_le ha hβ n X Y ω)

/-- The expected-remainder bound `B_n = (32 C₃² d_n^{−3/2} + C₆ d_n^{−3}/2)/6`. -/
noncomputable def remainderBound (a β : ℝ) (n : ℕ) : ℝ :=
  (32 * absMom3 ^ 2 * √(postPrec a β n)⁻¹ ^ 3 + absMomSq3 * ((postPrec a β n)⁻¹) ^ 3 / 2) / 6

theorem remainderBound_nonneg (ha : 0 < a) (hβ : 0 < β) : 0 ≤ remainderBound a β n := by
  unfold remainderBound
  have h3 := absMom3_nonneg
  have h6 := absMomSq3_nonneg
  have hd := postPrec_pos (n := n) ha hβ
  positivity

/-- ★★ **Expected remainder bound**: for standard-normal training points and a standard-normal
test point, `𝔼|R_n| ≤ B_n`. Only the marginal laws are used. -/
theorem integral_abs_remainder_le [IsProbabilityMeasure P] (ha : 0 < a) (hβ : 0 < β)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) (n : ℕ) :
    ∫ ω, |remainder a β n X Y ω| ∂P ≤ remainderBound a β n := by
  have hd0 : 0 < postPrec a β n := postPrec_pos ha hβ
  have h3 := absMom3_nonneg
  have h6 := absMomSq3_nonneg
  have hY3 := integrable_abs_cube_of_hasLaw hY
  have hXi : ∀ i : Fin n, Integrable (fun ω => |X i ω| ^ 3) P := fun i =>
    integrable_abs_cube_of_hasLaw (hX i)
  have hsum : Integrable (fun ω => ∑ i : Fin n, |X i ω| ^ 3) P :=
    integrable_finsetSum _ fun i _ => hXi i
  set c₁ := 16 * absMom3 * √(postPrec a β n)⁻¹ ^ 3 / 6 with hc₁
  set c₂ := 16 * absMom3 * √(postPrec a β n)⁻¹ ^ 3 * (((postPrec a β n)⁻¹ * β) ^ 3 * n ^ 2) / 6
    with hc₂
  set c₀ := 4 * absMomSq3 * ((postPrec a β n)⁻¹ / 2) ^ 3 / 6 with hc₀
  have h12 : Integrable (fun ω => c₁ * |Y ω| ^ 3 + c₂ * ∑ i : Fin n, |X i ω| ^ 3) P :=
    (hY3.const_mul c₁).add (hsum.const_mul c₂)
  calc ∫ ω, |remainder a β n X Y ω| ∂P
      ≤ ∫ ω, (c₁ * |Y ω| ^ 3 + c₂ * ∑ i : Fin n, |X i ω| ^ 3 + c₀) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
          (integrable_majorant hX hY n c₁ c₂ c₀)
          (Eventually.of_forall fun ω => abs_remainder_le ha hβ n X Y ω)
    _ = c₁ * absMom3 + c₂ * (n * absMom3) + c₀ := by
        rw [integral_add h12 (integrable_const c₀),
          integral_add (hY3.const_mul c₁) (hsum.const_mul c₂), integral_const_mul,
          integral_const_mul, integral_finsetSum _ fun i _ => hXi i,
          integral_abs_cube_of_hasLaw hY, integral_const]
        have hXint : ∀ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P = absMom3 := fun i =>
          integral_abs_cube_of_hasLaw (hX i)
        simp [hXint]
    _ ≤ remainderBound a β n := by
        have hKn : ((postPrec a β n)⁻¹ * β) ^ 3 * n ^ 2 * n ≤ 1 := by
          have h1 : (postPrec a β n)⁻¹ * β * n ≤ 1 := by
            rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_one hd0]
            unfold postPrec
            linarith
          calc ((postPrec a β n)⁻¹ * β) ^ 3 * n ^ 2 * n = ((postPrec a β n)⁻¹ * β * n) ^ 3 := by
                ring
            _ ≤ 1 := pow_le_one₀ (by positivity) h1
        have hc₁0 : 0 ≤ c₁ := by
          rw [hc₁]
          positivity
        have hc2 : c₂ * (n * absMom3) ≤ c₁ * absMom3 := by
          calc c₂ * (n * absMom3)
              = (c₁ * absMom3) * (((postPrec a β n)⁻¹ * β) ^ 3 * n ^ 2 * n) := by
                rw [hc₁, hc₂]
                ring
            _ ≤ (c₁ * absMom3) * 1 := mul_le_mul_of_nonneg_left hKn (mul_nonneg hc₁0 h3)
            _ = c₁ * absMom3 := mul_one _
        have hR : remainderBound a β n = 2 * (c₁ * absMom3) + c₀ := by
          unfold remainderBound
          rw [hc₁, hc₀]
          ring
        rw [hR]
        linarith

theorem tendsto_mul_sqrt_inv_postPrec_cube (ha : 0 < a) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) * √(postPrec a β n)⁻¹ ^ 3) atTop (𝓝 0) := by
  have hq : 0 < √β := Real.sqrt_pos.2 hβ
  have hlim : Tendsto (fun n : ℕ => (√β)⁻¹ ^ 3 * (√(n : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul ((√β)⁻¹ ^ 3)
    rw [mul_zero] at h
    exact h
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hd : β * n ≤ postPrec a β n := by
    unfold postPrec
    linarith
  have h1 : √(postPrec a β n)⁻¹ ≤ (√β * √(n : ℝ))⁻¹ := by
    rw [← Real.sqrt_mul hβ.le, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (inv_anti₀ (by positivity) hd)
  calc (n : ℝ) * √(postPrec a β n)⁻¹ ^ 3 ≤ (n : ℝ) * ((√β * √(n : ℝ))⁻¹) ^ 3 := by
        gcongr
    _ = (√β)⁻¹ ^ 3 * (√(n : ℝ))⁻¹ := by
        have hr2 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
        set r := √(n : ℝ) with hr_def
        rw [← hr2]
        field_simp

theorem tendsto_mul_inv_postPrec_cube (ha : 0 < a) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((postPrec a β n)⁻¹) ^ 3) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => β⁻¹ ^ 3 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (β⁻¹ ^ 3)
    rw [mul_zero] at h
    exact h
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · have := postPrec_pos (n := n) ha hβ
    positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : β * n ≤ postPrec a β n := by
    unfold postPrec
    linarith
  have hd0 := postPrec_pos (n := n) ha hβ
  calc (n : ℝ) * ((postPrec a β n)⁻¹) ^ 3 ≤ (n : ℝ) * ((β * n)⁻¹) ^ 3 := by
        gcongr
    _ = β⁻¹ ^ 3 * ((n : ℝ)⁻¹) ^ 2 := by
        field_simp
    _ ≤ β⁻¹ ^ 3 * (n : ℝ)⁻¹ := by
        gcongr
        exact pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hn1) two_ne_zero

/-- `n·B_n → 0`. -/
theorem tendsto_mul_remainderBound (ha : 0 < a) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) * remainderBound a β n) atTop (𝓝 0) := by
  have h := ((tendsto_mul_sqrt_inv_postPrec_cube ha hβ).const_mul (32 * absMom3 ^ 2 / 6)).add
    ((tendsto_mul_inv_postPrec_cube ha hβ).const_mul (absMomSq3 / 12))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  unfold remainderBound
  ring

/-- ★★★ **Predictive-remainder certificates in the normal-location model.** For `a, β > 0`, a
training sequence of standard-normal points and a standard-normal test point (measurable, with the
stated marginal laws; independence is not needed), both the generalisation certificate
`n·𝔼𝔼_{X*}|R_n(X*)| → 0` and the training certificate `n·𝔼(1/n)∑ᵢ|R_n(Xᵢ)| → 0` hold, where
`R_n` is the predictive remainder of the tempered posterior after `n` observations. -/
theorem normalLocation_predictive_remainder_L1 [IsProbabilityMeasure P] (ha : 0 < a) (hβ : 0 < β)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, |remainder a β n X Y ω| ∂P) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ ω, (1 / (n : ℝ)) * ∑ i : Fin n, |remainder a β n X (X i) ω| ∂P) atTop (𝓝 0) := by
  have hlim := tendsto_mul_remainderBound ha hβ
  constructor
  · refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n)
      (integral_nonneg fun ω => abs_nonneg _)) (fun n => ?_) hlim
    exact mul_le_mul_of_nonneg_left (integral_abs_remainder_le ha hβ hX hY n) (Nat.cast_nonneg n)
  · refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n)
      (integral_nonneg fun ω => by positivity)) (fun n => ?_) hlim
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    rw [integral_const_mul, integral_finsetSum
      (f := fun i : Fin n => fun ω => |remainder a β n X (X i) ω|) Finset.univ
      fun i _ => integrable_abs_remainder ha hβ hX (hX i) n]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, div_zero, zero_mul]
      exact remainderBound_nonneg ha hβ
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc 1 / (n : ℝ) * ∑ i : Fin n, ∫ ω, |remainder a β n X (X i) ω| ∂P
        ≤ 1 / (n : ℝ) * ∑ i : Fin n, remainderBound a β n := by
          gcongr with i _
          exact integral_abs_remainder_le ha hβ hX (hX i) n
      _ = remainderBound a β n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

end Grammar
