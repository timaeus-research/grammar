/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensityPolar
import Grammar.RankOneGauss

/-!
# The Gaussian-prior deep linear network at general depth: the product zeta function

For `L` independent standard Gaussians `Wᵢ` the zeta function of the product is exact
(examples_slop §2, eq. dln_gauss):

  `ζ_L(s) = E|W₁ ⋯ W_L|^{−2s} = (2^{−s} Γ(½ − s)/√π)^L`,   `Re s < ½`

(★★★ `gaussProductZeta_eq`), from the one-dimensional moment `E|W|^{−2s} = 2^{−s}Γ(½−s)/√π`
(★★ `gaussZeta1_eq`: the substitution `y = w²/2` turns the Gaussian moment into the Gamma integral)
and Fubini on the product.  The phase `K = (∏Wᵢ)²/2` of the model has `ζ_K(s) = 2^s ζ_L(s)`.  The
continuation has a pole of order `L` at `½` with the nonzero leading coefficient

  `(s − ½)^L ζ_L(s) → (−1)^L (2π)^{−L/2}`  (★★ `tendsto_pole_gaussZeta`),

from `Γ(½ − s) = Γ(3/2 − s)/(½ − s)` and the continuity of `Γ` at `1`.  The asymptotic transfer to
`Z_N` and the Gaussian polynomials `P_{L−1}` of the note are derivations (Astra round 3, target 3).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The one-dimensional Gaussian moment `E|W|^{−2s}`, `W ∼ N(0,1)`. -/
noncomputable def gaussZeta1 (s : ℂ) : ℂ :=
  ∫ w : ℝ, ((|w| : ℝ) : ℂ) ^ (-2 * s) * ((Real.exp (-w ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- The product zeta function `E|W₁ ⋯ W_L|^{−2s}`. -/
noncomputable def gaussProductZeta (L : ℕ) (s : ℂ) : ℂ :=
  ∫ w : Fin L → ℝ, ((|∏ i, w i| : ℝ) : ℂ) ^ (-2 * s) *
    ∏ i, ((Real.exp (-w i ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- The closed form of the one-dimensional moment. -/
noncomputable def gaussZeta1Closed (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (-s) * Complex.Gamma (1 / 2 - s) / (Real.sqrt Real.pi : ℂ)

/-! ### Complex powers of positive reals -/

theorem cpow_sq_ofReal {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x ^ 2 : ℝ) : ℂ) ^ z = (x : ℂ) ^ (2 * z) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx2 : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hx 2).ne'
  rw [Complex.cpow_def_of_ne_zero hx2, Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le,
    ← Complex.ofReal_log (pow_pos hx 2).le, Real.log_pow]
  push_cast
  ring_nf

theorem norm_cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx z

/-! ### The Gamma integral with the scaling `e^{−y/2}` -/

/-- `∫_0^∞ y^{a−1} e^{−y/2} dy = 2^a Γ(a)` for `Re a > 0`. -/
theorem integral_cpow_exp_half {a : ℂ} (ha : 0 < a.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * (Real.exp (-y / 2) : ℂ) =
      (2 : ℂ) ^ a * Complex.Gamma a := by
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => (y : ℂ) ^ (a - 1) * (Real.exp (-y / 2) : ℂ)) 0 (by norm_num : (0 : ℝ) < 2)
  rw [mul_zero] at h
  have hpt : ∀ x ∈ Ioi (0 : ℝ), (((2 : ℝ) * x : ℝ) : ℂ) ^ (a - 1) * (Real.exp (-(2 * x) / 2) : ℂ) =
      (2 : ℂ) ^ (a - 1) * ((Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hx0.le]
    push_cast
    rw [show (-(2 * (x : ℂ)) / 2 : ℂ) = -(x : ℂ) by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    ← Complex.GammaIntegral, ← Complex.Gamma_eq_integral ha, Complex.real_smul] at h
  have h2 : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * (Real.exp (-y / 2) : ℂ) =
      2 * ((2 : ℂ) ^ (a - 1) * Complex.Gamma a) := by
    rw [h]
    push_cast
    field_simp
  rw [h2, Complex.cpow_sub a 1 two_ne_zero, Complex.cpow_one]
  field_simp

/-! ### The one-dimensional moment -/

theorem integrableOn_gauss_cpow_Ioi {s : ℂ} (hs : s.re < 1 / 2) :
    IntegrableOn (fun w : ℝ => ((|w| : ℝ) : ℂ) ^ (-2 * s) *
      ((Real.exp (-w ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) (Ioi 0) := by
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -2 * s.re) (p := 2) (b := 1 / 2)
    (by linarith) two_pos (by norm_num)
  refine (hint.const_mul (1 / Real.sqrt (2 * Real.pi))).mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw0 : 0 < w := hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0,
      norm_cpow_ofReal_pos hw0, abs_of_pos (by positivity), Real.rpow_two]
    have hre : (-2 * s).re = -2 * s.re := by simp
    rw [hre]
    apply le_of_eq
    ring_nf

theorem two_cpow_half : (2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
  push_cast
  rfl

/-- ★★ **The one-dimensional Gaussian moment**: `E|W|^{−2s} = 2^{−s}Γ(½ − s)/√π` for `Re s < ½`. -/
theorem gaussZeta1_eq {s : ℂ} (hs : s.re < 1 / 2) : gaussZeta1 s = gaussZeta1Closed s := by
  set F : ℝ → ℂ := fun w => ((|w| : ℝ) : ℂ) ^ (-2 * s) *
    ((Real.exp (-w ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) with hF
  clear_value F
  have hFeven : ∀ w, F (-w) = F w := fun w => by rw [hF]; simp
  have hpos : IntegrableOn F (Ioi 0) := by rw [hF]; exact integrableOn_gauss_cpow_Ioi hs
  have hneg : IntegrableOn F (Iic 0) := by
    have := hpos.comp_neg
    rw [Set.neg_Ioi, neg_zero] at this
    have h' : IntegrableOn F (Iio 0) := this.congr_fun (fun w _ => hFeven w) measurableSet_Iio
    rwa [IntegrableOn, Measure.restrict_congr_set Iio_ae_eq_Iic] at h'
  have hint : Integrable F := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hneg, hpos⟩
  have hsplit : ∫ w, F w = (∫ w in Ioi (0 : ℝ), F w) + ∫ w in Iic (0 : ℝ), F w := by
    have := integral_add_compl (s := Ioi (0 : ℝ)) (μ := volume) measurableSet_Ioi hint
    rw [compl_Ioi] at this
    exact this.symm
  have hrefl : ∫ w in Iic (0 : ℝ), F w = ∫ w in Ioi (0 : ℝ), F w := by
    have := integral_comp_neg_Iic (0 : ℝ) F
    rw [neg_zero] at this
    rw [← this]
    exact setIntegral_congr_fun measurableSet_Iic fun w _ => (hFeven w).symm
  -- the substitution `y = w²`
  set a : ℂ := 1 / 2 - s with ha
  have ha0 : 0 < a.re := by rw [ha]; simp; linarith
  have hsub : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * (Real.exp (-y / 2) : ℂ) =
      ∫ w in Ioi (0 : ℝ), ((2 : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ)) * F w := by
    have h := integral_comp_rpow_Ioi_of_pos
      (g := fun y : ℝ => (y : ℂ) ^ (a - 1) * (Real.exp (-y / 2) : ℂ)) (p := 2) two_pos
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have hw0 : (0 : ℝ) < w := hw
    have hw0' : (w : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
    have hsq : w ^ (2 : ℝ) = w ^ 2 := Real.rpow_two w
    rw [Complex.real_smul, hsq, cpow_sq_ofReal hw0, hF]
    beta_reduce
    rw [abs_of_pos hw0, show (2 * (a - 1) : ℂ) = -2 * s + (-1) by rw [ha]; ring,
      Complex.cpow_add _ _ hw0', Complex.cpow_neg_one, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one]
    push_cast
    have hsqrt : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    field_simp
  rw [integral_cpow_exp_half ha0, integral_const_mul] at hsub
  unfold gaussZeta1
  rw [← hF, hsplit, hrefl, ← two_mul]
  have h2 : ((2 : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ)) ≠ 0 := by
    have : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    exact mul_ne_zero two_ne_zero this
  have hI : ∫ w in Ioi (0 : ℝ), F w = (2 : ℂ) ^ a * Complex.Gamma a /
      ((2 : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ)) := by
    rw [eq_div_iff h2, mul_comm, hsub]
  rw [hI]
  unfold gaussZeta1Closed
  rw [ha, show (1 / 2 - s : ℂ) = 1 / 2 + -s by ring, Complex.cpow_add _ _ (by norm_num),
    two_cpow_half, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

/-! ### The product -/

theorem cpow_finset_prod_ofReal_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (z : ℂ) :
    ((∏ i ∈ S, f i : ℝ) : ℂ) ^ z = ∏ i ∈ S, ((f i : ℝ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf j) (Finset.prod_nonneg fun i _ => hf i), ih]

/-- ★★★ **The product zeta function**: `E|W₁ ⋯ W_L|^{−2s} = (2^{−s}Γ(½−s)/√π)^L`, `Re s < ½`. -/
theorem gaussProductZeta_eq (L : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    gaussProductZeta L s = gaussZeta1Closed s ^ L := by
  unfold gaussProductZeta
  have hpt : ∀ w : Fin L → ℝ, ((|∏ i, w i| : ℝ) : ℂ) ^ (-2 * s) *
      ∏ i, ((Real.exp (-w i ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) =
      ∏ i, (((|w i| : ℝ) : ℂ) ^ (-2 * s) *
        ((Real.exp (-w i ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) := by
    intro w
    rw [Finset.abs_prod, cpow_finset_prod_ofReal_nonneg _ _ (fun i => abs_nonneg _),
      Finset.prod_mul_distrib]
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin L) (w : ℝ) => ((|w| : ℝ) : ℂ) ^ (-2 * s) *
    ((Real.exp (-w ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  exact gaussZeta1_eq hs

/-! ### The leading pole -/

/-- `(s − ½) · gaussZeta1Closed s = −2^{−s} Γ(3/2 − s)/√π` for `s ≠ ½`. -/
theorem sub_mul_gaussZeta1Closed {s : ℂ} (hs : s ≠ 1 / 2) :
    (s - 1 / 2) * gaussZeta1Closed s =
      -((2 : ℂ) ^ (-s) * Complex.Gamma (3 / 2 - s) / (Real.sqrt Real.pi : ℂ)) := by
  have h1 : (1 / 2 - s : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination -h
  have hG := Complex.Gamma_add_one (1 / 2 - s) h1
  rw [show (1 / 2 - s + 1 : ℂ) = 3 / 2 - s by ring] at hG
  unfold gaussZeta1Closed
  rw [hG]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
  ring

/-- ★★ **The leading pole of order `L`**:
`(s − ½)^L ζ_L(s) → (−1/√(2π))^L`, the coefficient `(−1)^L (2π)^{−L/2}`. -/
theorem tendsto_pole_gaussZeta (L : ℕ) :
    Tendsto (fun s : ℂ => (s - 1 / 2) ^ L * gaussZeta1Closed s ^ L) (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 ((-(1 / (Real.sqrt (2 * Real.pi) : ℂ))) ^ L)) := by
  have hcont : ContinuousAt (fun s : ℂ =>
      (-((2 : ℂ) ^ (-s) * Complex.Gamma (3 / 2 - s) / (Real.sqrt Real.pi : ℂ))) ^ L) (1 / 2) := by
    have h2 : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (-s)) (1 / 2) :=
      (continuousAt_const.cpow continuousAt_neg (Or.inl (by norm_num)))
    have hG : ContinuousAt (fun s : ℂ => Complex.Gamma (3 / 2 - s)) (1 / 2) := by
      have h1 : ContinuousAt Complex.Gamma ((fun s : ℂ => 3 / 2 - s) (1 / 2)) := by
        simp only
        rw [show (3 / 2 - 1 / 2 : ℂ) = 1 by norm_num]
        exact Complex.continuousAt_Gamma_one
      exact h1.comp (continuousAt_const.sub continuousAt_id)
    exact ((h2.mul hG).div_const _).neg.pow L
  have hval : (fun s : ℂ =>
      (-((2 : ℂ) ^ (-s) * Complex.Gamma (3 / 2 - s) / (Real.sqrt Real.pi : ℂ))) ^ L) (1 / 2) =
      (-(1 / (Real.sqrt (2 * Real.pi) : ℂ))) ^ L := by
    simp only
    rw [show (3 / 2 - 1 / 2 : ℂ) = 1 by norm_num, Complex.Gamma_one, mul_one,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), show (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) from rfl]
    congr 2
    rw [Complex.cpow_neg, two_cpow_half]
    push_cast
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
    have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
  rw [← hval]
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  simp only
  rw [← mul_pow, sub_mul_gaussZeta1Closed hs]


end Grammar
