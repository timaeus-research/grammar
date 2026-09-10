import Grammar.GaussianInsertion
import Grammar.GaussianQuartetDet

/-!
# The bilocal two-point function `E₊[S_λ(G_i) S_λ(G_j)]`

For the Gaussian vector `G = A Z` with covariance `B = A Aᵀ`, put

* `a = β (1 − β B_ii / 2)`, `b = β (1 − β B_jj / 2)`, `h = β² B_ij`.

Tonelli and the joint moment generating function give, in `ℝ≥0∞`,

`E₊[S_λ(G_i) S_λ(G_j)] = ∫₀^∞ ∫₀^∞ t^{λ-1} s^{λ-1} e^{−at − bs + h√(ts)} dt ds`

(`lintegral_fluctuation_mul_fluctuation`). For `a, b > 0` and `h < 2√(ab)` the right-hand side is
finite (`lintegral_bilocalIntegrand_lt_top`, by the AM–GM bound
`h√(ts) ≤ ρ(at + bs)` with `ρ = max(h,0)/(2√(ab)) < 1`), so `S_λ(G_i) S_λ(G_j)` is integrable
(`integrable_fluctuation_mul_fluctuation`) and its expectation is the double integral
(`integral_fluctuation_mul_fluctuation`); the covariance is the double integral minus
`Γ(λ)² (ab)^{−λ}` (`cov_fluctuation_eq`). Finiteness depends on the sign of `B_ij`: a negative
covariance never hurts. The critical line `h = 2√(ab)` and the divergent region are not treated
here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-! ### Kernel algebra -/

/-- `t^{λ-1} e^{−βt + βa√t} = K(t) e^{β√t a}`. -/
theorem radialKernel_mul_exp_eq (β μ a t : ℝ) :
    t ^ (μ - 1) * Real.exp (-β * t + β * a * Real.sqrt t) =
      radialKernel β μ t * Real.exp (β * Real.sqrt t * a) := by
  rw [radialKernel, mul_assoc (t ^ (μ - 1)), ← Real.exp_add]
  congr 2
  ring

theorem radialKernel_mul_exp_integrableOn (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (a : ℝ) :
    IntegrableOn (fun t => radialKernel β μ t * Real.exp (β * Real.sqrt t * a)) (Ioi 0) :=
  (fluctuation_integrableOn β μ hβ hμ a).congr_fun (fun t _ => radialKernel_mul_exp_eq β μ a t)
    measurableSet_Ioi

/-- `S_μ(a)` as a Lebesgue integral in `ℝ≥0∞`. -/
theorem ofReal_fluctuation_eq_lintegral (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (a : ℝ) :
    ENNReal.ofReal (fluctuation β μ a) =
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (radialKernel β μ t * Real.exp (β * Real.sqrt t * a)) := by
  rw [fluctuation_eq_integral_radialKernel]
  refine ofReal_integral_eq_lintegral_ofReal (radialKernel_mul_exp_integrableOn β μ hβ hμ a) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    mul_nonneg (radialKernel_nonneg ht) (Real.exp_pos _).le

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- `∑_k (a A_ik + b A_jk)² = a² B_ii + 2ab B_ij + b² B_jj`. -/
theorem sum_sq_two_rows (a b : ℝ) (i j : Fin m) :
    ∑ k, (a * A i k + b * A j k) ^ 2 =
      a ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i +
        2 * a * b * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j +
        b ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem two_mulVec_eq_dotW (a b : ℝ) (i j : Fin m) (z : Fin (n + 1) → ℝ) :
    a * A.mulVec z i + b * A.mulVec z j = dotW (fun k => a * A i k + b * A j k) z := by
  simp only [Matrix.mulVec, dotProduct, dotW, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Joint moment generating function** of two coordinates of `G = AZ`, in `ℝ≥0∞`:
`E₊ e^{a G_i + b G_j} = e^{(a² B_ii + 2ab B_ij + b² B_jj)/2}`. -/
theorem lintegral_ofReal_exp_two (a b : ℝ) (i j : Fin m) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (a * g i + b * g j)) ∂gaussianVector A =
      ENNReal.ofReal (Real.exp ((a ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i +
        2 * a * b * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j +
        b ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j) / 2)) := by
  have hf : Measurable fun g : Fin m → ℝ => ENNReal.ofReal (Real.exp (a * g i + b * g j)) :=
    Measurable.ennreal_ofReal (Measurable.exp ((measurable_const.mul (measurable_pi_apply i)).add
      (measurable_const.mul (measurable_pi_apply j))))
  rw [gaussianVector, lintegral_map hf (measurable_mulVec A)]
  simp_rw [two_mulVec_eq_dotW A a b i j]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_dot fun k => a * A i k + b * A j k)
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_dot,
    sum_sq_two_rows]

/-! ### The Tonelli identity -/

/-- The bilocal integrand `t^{λ-1} s^{λ-1} e^{−at − bs + h√(ts)}`. -/
noncomputable def bilocalIntegrand (lam a b h t s : ℝ) : ℝ :=
  t ^ (lam - 1) * s ^ (lam - 1) * Real.exp (-a * t - b * s + h * Real.sqrt (t * s))

/-- The product kernel `K(t) e^{β√t g_i} · K(s) e^{β√s g_j}` in `ℝ≥0∞`. -/
noncomputable def bilocalKernel (β lam : ℝ) (i j : Fin m) (t s : ℝ) (g : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (radialKernel β lam t * Real.exp (β * Real.sqrt t * g i)) *
    ENNReal.ofReal (radialKernel β lam s * Real.exp (β * Real.sqrt s * g j))

theorem measurable_bilocalKernel_gs (β lam : ℝ) (i j : Fin m) (t : ℝ) :
    Measurable (Function.uncurry fun (g : Fin m → ℝ) (s : ℝ) =>
      bilocalKernel β lam i j t s g) := by
  change Measurable fun p : (Fin m → ℝ) × ℝ =>
    ENNReal.ofReal (radialKernel β lam t * Real.exp (β * Real.sqrt t * p.1 i)) *
      ENNReal.ofReal (radialKernel β lam p.2 * Real.exp (β * Real.sqrt p.2 * p.1 j))
  exact (Measurable.ennreal_ofReal (measurable_const.mul (Measurable.exp
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))))).mul
    (Measurable.ennreal_ofReal (((measurable_radialKernel β lam).comp measurable_snd).mul
      (Measurable.exp ((measurable_const.mul measurable_snd.sqrt).mul
        ((measurable_pi_apply j).comp measurable_fst)))))

theorem measurable_bilocalKernel_gt (β lam : ℝ) (i j : Fin m) :
    Measurable (Function.uncurry fun (g : Fin m → ℝ) (t : ℝ) =>
      ∫⁻ s in Ioi (0 : ℝ), bilocalKernel β lam i j t s g) := by
  refine Measurable.lintegral_prod_right
    (f := fun (x : (Fin m → ℝ) × ℝ) (s : ℝ) => bilocalKernel β lam i j x.2 s x.1) ?_
  change Measurable fun p : ((Fin m → ℝ) × ℝ) × ℝ =>
    ENNReal.ofReal (radialKernel β lam p.1.2 * Real.exp (β * Real.sqrt p.1.2 * p.1.1 i)) *
      ENNReal.ofReal (radialKernel β lam p.2 * Real.exp (β * Real.sqrt p.2 * p.1.1 j))
  exact (Measurable.ennreal_ofReal
      (((measurable_radialKernel β lam).comp (measurable_snd.comp measurable_fst)).mul
        (Measurable.exp ((measurable_const.mul (measurable_snd.comp measurable_fst).sqrt).mul
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)))))).mul
    (Measurable.ennreal_ofReal (((measurable_radialKernel β lam).comp measurable_snd).mul
      (Measurable.exp ((measurable_const.mul measurable_snd.sqrt).mul
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))))))

theorem measurable_ofReal_radialKernel_mul_exp (β lam : ℝ) (x : ℝ) :
    Measurable fun t : ℝ =>
      ENNReal.ofReal (radialKernel β lam t * Real.exp (β * Real.sqrt t * x)) :=
  Measurable.ennreal_ofReal ((measurable_radialKernel β lam).mul
    (Measurable.exp ((measurable_const.mul measurable_id.sqrt).mul measurable_const)))

/-- `E₊ K(t)e^{β√t G_i} K(s)e^{β√s G_j}` for `t, s > 0` equals the bilocal integrand. -/
theorem lintegral_bilocalKernel (β lam : ℝ) (i j : Fin m) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    ∫⁻ g, bilocalKernel β lam i j t s g ∂gaussianVector A =
      ENNReal.ofReal (bilocalIntegrand lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) t s) := by
  have hKt := radialKernel_nonneg (β := β) (μ := lam) ht
  have hKs := radialKernel_nonneg (β := β) (μ := lam) hs
  have hg : ∀ g : Fin m → ℝ, bilocalKernel β lam i j t s g =
      ENNReal.ofReal (radialKernel β lam t * radialKernel β lam s) *
        ENNReal.ofReal (Real.exp (β * Real.sqrt t * g i + β * Real.sqrt s * g j)) := by
    intro g
    rw [bilocalKernel, ← ENNReal.ofReal_mul (mul_nonneg hKt (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg hKt hKs)]
    congr 1
    rw [Real.exp_add]
    ring
  simp_rw [hg]
  rw [lintegral_const_mul _ (Measurable.ennreal_ofReal (Measurable.exp
    ((measurable_const.mul (measurable_pi_apply i)).add
      (measurable_const.mul (measurable_pi_apply j))))),
    lintegral_ofReal_exp_two, ← ENNReal.ofReal_mul (mul_nonneg hKt hKs)]
  congr 1
  have hexp : Real.exp (-(β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) * t -
      β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) * s +
      β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j * Real.sqrt (t * s)) =
      Real.exp (-β * t) * Real.exp (-β * s) *
        Real.exp (((β * Real.sqrt t) ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i +
          2 * (β * Real.sqrt t) * (β * Real.sqrt s) *
            (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j +
          (β * Real.sqrt s) ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Real.sqrt_mul ht.le, mul_pow, mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt hs.le]
    ring
  rw [bilocalIntegrand, hexp, radialKernel, radialKernel]
  ring

/-- **Tonelli identity for the bilocal two-point function.** In `ℝ≥0∞`,
`E₊[S_λ(G_i) S_λ(G_j)] = ∫₀^∞∫₀^∞ t^{λ-1}s^{λ-1} e^{−at − bs + h√(ts)} dt ds` with
`a = β(1 − βB_ii/2)`, `b = β(1 − βB_jj/2)`, `h = β²B_ij`. -/
theorem lintegral_fluctuation_mul_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m) :
    ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g i) * fluctuation β lam (g j)) ∂gaussianVector A =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) t s) := by
  have hS : ∀ g : Fin m → ℝ,
      ENNReal.ofReal (fluctuation β lam (g i) * fluctuation β lam (g j)) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), bilocalKernel β lam i j t s g := by
    intro g
    rw [ENNReal.ofReal_mul (fluctuation_pos β lam (g i) hβ hlam).le,
      ofReal_fluctuation_eq_lintegral β lam hβ hlam, ofReal_fluctuation_eq_lintegral β lam hβ hlam,
      ← lintegral_mul_const _ (measurable_ofReal_radialKernel_mul_exp β lam (g i))]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_const_mul _ (measurable_ofReal_radialKernel_mul_exp β lam (g j))]
    rfl
  simp_rw [hS]
  rw [lintegral_lintegral_swap (measurable_bilocalKernel_gt β lam i j).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [lintegral_lintegral_swap (measurable_bilocalKernel_gs β lam i j t).aemeasurable]
  exact setLIntegral_congr_fun measurableSet_Ioi fun s hs =>
    lintegral_bilocalKernel A β lam i j ht hs

/-! ### Finiteness below the threshold -/

/-- AM–GM: `h√(ts) ≤ ρ (at + bs)` with `ρ = max(h,0)/(2√(ab))`, for `a, b > 0` and `t, s ≥ 0`. -/
theorem cross_term_le (a b h t s : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    h * Real.sqrt (t * s) ≤ max h 0 / (2 * Real.sqrt (a * b)) * (a * t + b * s) := by
  have hab : 0 < 2 * Real.sqrt (a * b) := mul_pos two_pos (Real.sqrt_pos.2 (mul_pos ha hb))
  have h1 : h * Real.sqrt (t * s) ≤ max h 0 * Real.sqrt (t * s) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have h2 : 2 * Real.sqrt (a * b) * Real.sqrt (t * s) ≤ a * t + b * s := by
    have e : Real.sqrt (a * b) * Real.sqrt (t * s) = Real.sqrt (a * t) * Real.sqrt (b * s) := by
      rw [← Real.sqrt_mul (mul_pos ha hb).le, ← Real.sqrt_mul (mul_nonneg ha.le ht)]
      congr 1
      ring
    rw [mul_assoc, e, ← mul_assoc]
    have := two_mul_le_add_sq (Real.sqrt (a * t)) (Real.sqrt (b * s))
    rwa [Real.sq_sqrt (mul_nonneg ha.le ht), Real.sq_sqrt (mul_nonneg hb.le hs)] at this
  calc h * Real.sqrt (t * s) ≤ max h 0 * Real.sqrt (t * s) := h1
    _ = max h 0 / (2 * Real.sqrt (a * b)) * (2 * Real.sqrt (a * b) * Real.sqrt (t * s)) := by
        rw [div_mul_eq_mul_div, eq_div_iff hab.ne']
        ring
    _ ≤ max h 0 / (2 * Real.sqrt (a * b)) * (a * t + b * s) :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg (le_max_right _ _) hab.le)

theorem integrableOn_rpow_mul_exp_neg_mul' (l c : ℝ) (hl : 0 < l) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (l - 1) * Real.exp (-c * t)) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_rpow (s := l - 1) (p := 1) (b := c) (by linarith) one_pos
    hc).congr_fun (fun t _ => by beta_reduce; rw [Real.rpow_one]) measurableSet_Ioi

theorem lintegral_ofReal_rpow_mul_exp_lt_top (l c : ℝ) (hl : 0 < l) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (l - 1) * Real.exp (-c * t)) < ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul' l c hl hc)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

theorem measurable_ofReal_rpow_mul_exp (l c : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (t ^ (l - 1) * Real.exp (-c * t)) :=
  Measurable.ennreal_ofReal ((measurable_id.pow_const _).mul
    (Measurable.exp (measurable_const.mul measurable_id)))

/-- **Finiteness of the bilocal integral** for `a, b > 0`, `h < 2√(ab)`, `λ > 0`. -/
theorem lintegral_bilocalIntegrand_lt_top (lam a b h : ℝ) (hlam : 0 < lam) (ha : 0 < a)
    (hb : 0 < b) (hh : h < 2 * Real.sqrt (a * b)) :
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (bilocalIntegrand lam a b h t s) < ⊤ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = max h 0 / (2 * Real.sqrt (a * b)) := ⟨_, rfl⟩
  have hab : 0 < 2 * Real.sqrt (a * b) := mul_pos two_pos (Real.sqrt_pos.2 (mul_pos ha hb))
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one hab]
    exact max_lt hh hab
  have hca : 0 < (1 - ρ) * a := mul_pos (by linarith) ha
  have hcb : 0 < (1 - ρ) * b := mul_pos (by linarith) hb
  have hdom : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (bilocalIntegrand lam a b h t s) ≤
        ENNReal.ofReal (t ^ (lam - 1) * Real.exp (-((1 - ρ) * a) * t)) *
          ENNReal.ofReal (s ^ (lam - 1) * Real.exp (-((1 - ρ) * b) * s)) := by
    intro t ht s hs
    have ht' : 0 < t := ht
    have hs' : 0 < s := hs
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [bilocalIntegrand, show t ^ (lam - 1) * Real.exp (-((1 - ρ) * a) * t) *
        (s ^ (lam - 1) * Real.exp (-((1 - ρ) * b) * s)) =
        t ^ (lam - 1) * s ^ (lam - 1) *
          Real.exp (-((1 - ρ) * a) * t + -((1 - ρ) * b) * s) by rw [Real.exp_add]; ring]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.rpow_nonneg hs'.le _))
    have := cross_term_le a b h t s ha hb ht'.le hs'.le
    rw [← hρ] at this
    nlinarith [this]
  calc ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam a b h t s)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (lam - 1) * Real.exp (-((1 - ρ) * a) * t)) *
            ENNReal.ofReal (s ^ (lam - 1) * Real.exp (-((1 - ρ) * b) * s)) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht =>
          setLIntegral_mono' measurableSet_Ioi fun s hs => hdom t ht s hs
    _ = (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (lam - 1) * Real.exp (-((1 - ρ) * a) * t))) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (lam - 1) * Real.exp (-((1 - ρ) * b) * s)) := by
        rw [← lintegral_mul_const _ (measurable_ofReal_rpow_mul_exp lam _)]
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul _ (measurable_ofReal_rpow_mul_exp lam _)]
    _ < ⊤ := ENNReal.mul_lt_top (lintegral_ofReal_rpow_mul_exp_lt_top lam _ hlam hca)
        (lintegral_ofReal_rpow_mul_exp_lt_top lam _ hlam hcb)

/-! ### Bochner consequences -/

theorem continuous_fluctuation_mul (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (i j : Fin m) :
    Continuous fun g : Fin m → ℝ => fluctuation β lam (g i) * fluctuation β lam (g j) :=
  ((continuous_fluctuation β lam hβ hlam).comp (continuous_apply i)).mul
    ((continuous_fluctuation β lam hβ hlam).comp (continuous_apply j))

/-- **Integrability of the bilocal product** for `a, b > 0` and `h < 2√(ab)`. -/
theorem integrable_fluctuation_mul_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j <
      2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)))) :
    Integrable (fun g : Fin m → ℝ => fluctuation β lam (g i) * fluctuation β lam (g j))
      (gaussianVector A) := by
  refine ⟨(continuous_fluctuation_mul β lam hβ hlam i j).measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [Real.enorm_eq_ofReal
    (mul_pos (fluctuation_pos β lam _ hβ hlam) (fluctuation_pos β lam _ hβ hlam)).le]
  rw [lintegral_fluctuation_mul_fluctuation A β lam hβ hlam i j]
  exact lintegral_bilocalIntegrand_lt_top lam _ _ _ hlam (mul_pos hβ hi) (mul_pos hβ hj) hh

/-- **The bilocal two-point function** as a Bochner integral: for `a, b > 0` and `h < 2√(ab)`,
`E[S_λ(G_i) S_λ(G_j)]` is the (finite) double integral of the bilocal integrand. -/
theorem integral_fluctuation_mul_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (i j : Fin m) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A =
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) t s)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g =>
      (mul_pos (fluctuation_pos β lam _ hβ hlam) (fluctuation_pos β lam _ hβ hlam)).le)
    (continuous_fluctuation_mul β lam hβ hlam i j).measurable.aestronglyMeasurable,
    lintegral_fluctuation_mul_fluctuation A β lam hβ hlam i j]

/-- **Covariance of `S_λ(G_i)` and `S_λ(G_j)`**: the bilocal double integral minus the
disconnected part `Γ(λ)² (ab)^{−λ}`. -/
theorem cov_fluctuation_eq (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) :
    ∫ g, fluctuation β lam (g i) * fluctuation β lam (g j) ∂gaussianVector A -
      (∫ g, fluctuation β lam (g i) ∂gaussianVector A) *
        ∫ g, fluctuation β lam (g j) ∂gaussianVector A =
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (bilocalIntegrand lam
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2))
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
        (β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j) t s)).toReal -
      Real.Gamma lam ^ 2 *
        ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
          (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))) ^ (-lam) := by
  rw [integral_fluctuation_mul_fluctuation A β lam hβ hlam i j,
    (integral_fluctuation_gaussianVector A β lam hβ hlam i hi).2,
    (integral_fluctuation_gaussianVector A β lam hβ hlam j hj).2,
    Real.mul_rpow (mul_pos hβ hi).le (mul_pos hβ hj).le]
  ring

end Grammar
