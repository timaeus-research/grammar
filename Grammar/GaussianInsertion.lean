import Grammar.GaussianTilted
import Grammar.FluctuationSelfNormalised
import Grammar.GammaLogAsymptotic

/-!
# Gaussian insertions against the fluctuation function (`Q = 0, 1, 2`)

For the centred Gaussian vector `G = A Z` with covariance `B = A Aᵀ` and the fluctuation
function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt + βa√t} dt`, put `δ = 1 − β B_jj / 2`. If `δ > 0`
then, with `θ = β√t`,

* `E S_μ(G_j) = Γ(μ) (βδ)^{-μ}`  (`integral_fluctuation_gaussianVector`);
* `E[G_i S_μ(G_j)] = β B_ij Γ(μ + 1/2) (βδ)^{-(μ + 1/2)}`  (`integral_coord_mul_fluctuation`);
* `E[G_i G_{i'} S_μ(G_j)] = B_{ii'} Γ(μ) (βδ)^{-μ} + β² B_ij B_{i'j} Γ(μ + 1) (βδ)^{-(μ + 1)}`
  (`integral_coord_mul_coord_mul_fluctuation`),

and in each case the integrand is integrable. The route is Fubini on `(0, ∞) × Ω` for the
kernel `t^{μ-1} e^{-βt} · P(g) e^{θ g_j}` (`integral_mul_fluctuation_eq`), the tilted
identities of `Grammar.GaussianTilted`, and the Gamma integral
`∫₀^∞ t^{μ-1} e^{-βt} (β√t)^k e^{β² t B_jj / 2} dt = β^k Γ(μ + k/2) (βδ)^{-(μ + k/2)}`
(`integral_radialKernel_mul_tilt`). Nothing here uses Isserlis' theorem.
-/

open MeasureTheory Set

namespace Grammar

/-! ### The radial kernel and its tilted Gamma integrals -/

/-- The radial kernel `t^{μ-1} e^{-βt}` of the fluctuation function. -/
noncomputable def radialKernel (β μ t : ℝ) : ℝ := t ^ (μ - 1) * Real.exp (-β * t)

theorem radialKernel_nonneg {β μ t : ℝ} (ht : 0 < t) : 0 ≤ radialKernel β μ t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

theorem measurable_radialKernel (β μ : ℝ) : Measurable (radialKernel β μ) :=
  (measurable_id.pow_const _).mul (Measurable.exp (measurable_const.mul measurable_id))

/-- `S_μ(a) = ∫₀^∞ K(t) e^{β√t a} dt` with `K` the radial kernel. -/
theorem fluctuation_eq_integral_radialKernel (β μ a : ℝ) :
    fluctuation β μ a =
      ∫ t in Ioi (0 : ℝ), radialKernel β μ t * Real.exp (β * Real.sqrt t * a) := by
  unfold fluctuation radialKernel
  congr 1
  funext t
  rw [mul_assoc (t ^ (μ - 1)), ← Real.exp_add]
  congr 2
  ring

/-- Pointwise for `t > 0`:
`K(t) (β√t)^k e^{(β√t)² c/2} = β^k t^{μ + k/2 - 1} e^{-β(1 - βc/2) t}`. -/
theorem radialKernel_mul_tilt_eq (β μ c : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    radialKernel β μ t *
        ((β * Real.sqrt t) ^ k * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2)) =
      β ^ k * (t ^ (μ + k / 2 - 1) * Real.exp (-(β * (1 - β * c / 2) * t))) := by
  have hsq : (β * Real.sqrt t) ^ 2 = β ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht.le]
  have hk : Real.sqrt t ^ k = t ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hexp : Real.exp (-(β * (1 - β * c / 2) * t)) =
      Real.exp (-β * t) * Real.exp (β ^ 2 * t * c / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, radialKernel, hsq, mul_pow, hk,
    show μ + (k : ℝ) / 2 - 1 = (μ - 1) + (k : ℝ) / 2 by ring, Real.rpow_add ht]
  ring

/-- The tilted kernel `K(t) (β√t)^k e^{(β√t)² c/2}` is integrable on `(0, ∞)` when
`δ = 1 − βc/2 > 0`. -/
theorem integrableOn_radialKernel_mul_tilt (β μ c : ℝ) (k : ℕ) (hβ : 0 < β) (hμ : 0 < μ)
    (hδ : 0 < 1 - β * c / 2) :
    IntegrableOn (fun t => radialKernel β μ t *
      ((β * Real.sqrt t) ^ k * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2))) (Ioi 0) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h : IntegrableOn (fun t : ℝ => β ^ k * (t ^ (μ + k / 2 - 1) *
      Real.exp (-(β * (1 - β * c / 2)) * t ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := μ + k / 2 - 1) (p := 1)
      (b := β * (1 - β * c / 2)) (by linarith) one_pos (mul_pos hβ hδ)).const_mul (β ^ k)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  beta_reduce
  rw [Real.rpow_one, neg_mul, radialKernel_mul_tilt_eq β μ c k ht]

/-- **Tilted Gamma integral.**
`∫₀^∞ K(t) (β√t)^k e^{(β√t)² c/2} dt = β^k Γ(μ + k/2) (β(1 − βc/2))^{-(μ + k/2)}`. -/
theorem integral_radialKernel_mul_tilt (β μ c : ℝ) (k : ℕ) (hβ : 0 < β) (hμ : 0 < μ)
    (hδ : 0 < 1 - β * c / 2) :
    ∫ t in Ioi (0 : ℝ), radialKernel β μ t *
        ((β * Real.sqrt t) ^ k * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2)) =
      β ^ k * Real.Gamma (μ + k / 2) * (β * (1 - β * c / 2)) ^ (-(μ + k / 2)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => radialKernel_mul_tilt_eq β μ c k ht,
    integral_const_mul,
    show ∫ t in Ioi (0 : ℝ), t ^ (μ + k / 2 - 1) * Real.exp (-(β * (1 - β * c / 2) * t)) =
      Real.Gamma (μ + k / 2) * (β * (1 - β * c / 2)) ^ (-(μ + k / 2)) from
      integral_rpow_mul_exp_neg_mul _ _ (by linarith) (mul_pos hβ hδ)]
  ring

/-! ### Fubini for a polynomial insertion against `S_μ(G_j)` -/

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- **Fubini for insertions.** If the tilted integrands `P(g) e^{θ g_j}` are integrable, the
absolute tilted moments are bounded by `M(θ)`, and `t ↦ K(t) M(β√t)` is integrable on
`(0, ∞)`, then `P(g) S_μ(g_j)` is integrable and its expectation is
`∫₀^∞ K(t) · E[P(g) e^{β√t g_j}] dt`. -/
theorem integral_mul_fluctuation_eq (β μ : ℝ) (j : Fin m) (P : (Fin m → ℝ) → ℝ)
    (hP : Measurable P) (M : ℝ → ℝ)
    (hint : ∀ θ, Integrable (fun g => P g * Real.exp (θ * g j)) (gaussianVector A))
    (hM : ∀ θ, ∫ g, |P g| * Real.exp (θ * g j) ∂gaussianVector A ≤ M θ)
    (hK : IntegrableOn (fun t => radialKernel β μ t * M (β * Real.sqrt t)) (Ioi 0)) :
    Integrable (fun g => P g * fluctuation β μ (g j)) (gaussianVector A) ∧
    ∫ g, P g * fluctuation β μ (g j) ∂gaussianVector A =
      ∫ t in Ioi (0 : ℝ), radialKernel β μ t *
        ∫ g, P g * Real.exp (β * Real.sqrt t * g j) ∂gaussianVector A := by
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (g : Fin m → ℝ) =>
      radialKernel β μ t * (P g * Real.exp (β * Real.sqrt t * g j))) := by
    change Measurable fun p : ℝ × (Fin m → ℝ) =>
      radialKernel β μ p.1 * (P p.2 * Real.exp (β * Real.sqrt p.1 * p.2 j))
    exact ((measurable_radialKernel β μ).comp measurable_fst).mul
      ((hP.comp measurable_snd).mul (Measurable.exp ((measurable_const.mul measurable_fst.sqrt).mul
        ((measurable_pi_apply j).comp measurable_snd))))
  have hpt : ∀ g : Fin m → ℝ, P g * fluctuation β μ (g j) =
      ∫ t in Ioi (0 : ℝ), radialKernel β μ t * (P g * Real.exp (β * Real.sqrt t * g j)) := by
    intro g
    rw [fluctuation_eq_integral_radialKernel, ← integral_const_mul]
    congr 1
    funext t
    ring
  have hf : Integrable (Function.uncurry fun (t : ℝ) (g : Fin m → ℝ) =>
      radialKernel β μ t * (P g * Real.exp (β * Real.sqrt t * g j)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (gaussianVector A)) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      exact (hint (β * Real.sqrt t)).const_mul _
    · refine Integrable.mono' hK hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hKn : 0 ≤ radialKernel β μ t := radialKernel_nonneg ht
      have hn : ∀ g : Fin m → ℝ,
          ‖radialKernel β μ t * (P g * Real.exp (β * Real.sqrt t * g j))‖ =
          radialKernel β μ t * (|P g| * Real.exp (β * Real.sqrt t * g j)) := fun g => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKn, Real.abs_exp]
      simp only [Function.uncurry_apply_pair, hn]
      rw [integral_const_mul, Real.norm_of_nonneg (mul_nonneg hKn
        (integral_nonneg fun g => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))]
      exact mul_le_mul_of_nonneg_left (hM _) hKn
  refine ⟨?_, ?_⟩
  · have : (fun g : Fin m → ℝ => P g * fluctuation β μ (g j)) = fun g =>
        ∫ t in Ioi (0 : ℝ), radialKernel β μ t * (P g * Real.exp (β * Real.sqrt t * g j)) :=
      funext hpt
    rw [this]
    exact hf.integral_prod_right
  · simp_rw [hpt]
    rw [← integral_integral_swap hf]
    simp_rw [integral_const_mul]

/-! ### Integrability of the tilted insertions against `G = A Z` -/

theorem integrable_exp_gaussianVector (θ : ℝ) (j : Fin m) :
    Integrable (fun g => Real.exp (θ * g j)) (gaussianVector A) := by
  refine (integrable_map_measure (measurable_exp_mulVec θ j).aestronglyMeasurable
    (measurable_mulVec A).aemeasurable).2 ?_
  change Integrable (fun z => Real.exp (θ * A.mulVec z j)) _
  simp_rw [mulVec_eq_dotW A θ j]
  exact integrable_exp_dot _

theorem integrable_coord_mul_exp_gaussianVector (θ : ℝ) (i j : Fin m) :
    Integrable (fun g => g i * Real.exp (θ * g j)) (gaussianVector A) := by
  refine (integrable_map_measure ((measurable_pi_apply i).mul
    (measurable_exp_mulVec θ j)).aestronglyMeasurable (measurable_mulVec A).aemeasurable).2 ?_
  change Integrable (fun z => A.mulVec z i * Real.exp (θ * A.mulVec z j)) _
  simp_rw [mulVec_eq_dotW A θ j]
  have : (fun z : Fin (n + 1) → ℝ => A.mulVec z i * Real.exp (dotW (fun k => θ * A j k) z)) =
      fun z => ∑ k, A i k * (z k * Real.exp (dotW (fun k => θ * A j k) z)) := by
    funext z
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  exact integrable_finsetSum _ fun k _ => (integrable_coord_mul_exp_dot _ k).const_mul _

theorem integrable_coord_mul_coord_mul_exp_gaussianVector (θ : ℝ) (i i' j : Fin m) :
    Integrable (fun g => g i * g i' * Real.exp (θ * g j)) (gaussianVector A) := by
  refine (integrable_map_measure (((measurable_pi_apply i).mul (measurable_pi_apply i')).mul
    (measurable_exp_mulVec θ j)).aestronglyMeasurable (measurable_mulVec A).aemeasurable).2 ?_
  change Integrable (fun z => A.mulVec z i * A.mulVec z i' * Real.exp (θ * A.mulVec z j)) _
  simp_rw [mulVec_eq_dotW A θ j]
  have : (fun z : Fin (n + 1) → ℝ =>
      A.mulVec z i * A.mulVec z i' * Real.exp (dotW (fun k => θ * A j k) z)) =
      fun z => ∑ k, ∑ k', A i k * A i' k' *
        (z k * z k' * Real.exp (dotW (fun k => θ * A j k) z)) := by
    funext z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k' _ => by ring
  rw [this]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ =>
    (integrable_coord_mul_coord_mul_exp_dot _ k k').const_mul _

/-! ### The insertion formulas -/

/-- The tilted second moment gives the absolute-first-moment bound
`E[|G_i| e^{θ G_j}] ≤ ½ (1 + B_ii + θ² B_ij²) e^{θ² B_jj / 2}`. -/
theorem integral_abs_coord_mul_exp_le (θ : ℝ) (i j : Fin m) :
    ∫ g, |g i| * Real.exp (θ * g j) ∂gaussianVector A ≤
      2⁻¹ * ((1 + (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i) *
          (θ ^ 0 * Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) +
        (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          (θ ^ 2 * Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))) := by
  have hpt : ∀ g : Fin m → ℝ, |g i| * Real.exp (θ * g j) ≤
      2⁻¹ * (Real.exp (θ * g j) + g i * g i * Real.exp (θ * g j)) := by
    intro g
    have h : 2 * |g i| ≤ 1 + g i * g i := by nlinarith [sq_nonneg (|g i| - 1), sq_abs (g i)]
    have he := Real.exp_pos (θ * g j)
    nlinarith
  have hI : Integrable (fun g : Fin m → ℝ =>
      2⁻¹ * (Real.exp (θ * g j) + g i * g i * Real.exp (θ * g j))) (gaussianVector A) :=
    ((integrable_exp_gaussianVector A θ j).add
      (integrable_coord_mul_coord_mul_exp_gaussianVector A θ i i j)).const_mul _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hI
    (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (integrable_exp_gaussianVector A θ j)
    (integrable_coord_mul_coord_mul_exp_gaussianVector A θ i i j),
    integral_exp_gaussianVector, integral_mul_mul_exp_gaussianVector]
  ring

/-- `E[|G_i G_{i'}| e^{θ G_j}] ≤ ½ ((B_ii + B_{i'i'}) + θ² (B_ij² + B_{i'j}²)) e^{θ² B_jj / 2}`. -/
theorem integral_abs_coord_mul_coord_mul_exp_le (θ : ℝ) (i i' j : Fin m) :
    ∫ g, |g i * g i'| * Real.exp (θ * g j) ∂gaussianVector A ≤
      2⁻¹ * (((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i +
            (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' i') *
          (θ ^ 0 * Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) +
        ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
            (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j +
          (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' j *
            (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' j) *
          (θ ^ 2 * Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))) := by
  have hpt : ∀ g : Fin m → ℝ, |g i * g i'| * Real.exp (θ * g j) ≤
      2⁻¹ * (g i * g i * Real.exp (θ * g j) + g i' * g i' * Real.exp (θ * g j)) := by
    intro g
    have h : 2 * |g i * g i'| ≤ g i * g i + g i' * g i' := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|g i| - |g i'|), sq_abs (g i), sq_abs (g i')]
    have he := Real.exp_pos (θ * g j)
    nlinarith
  have hI : Integrable (fun g : Fin m → ℝ =>
      2⁻¹ * (g i * g i * Real.exp (θ * g j) + g i' * g i' * Real.exp (θ * g j)))
      (gaussianVector A) :=
    ((integrable_coord_mul_coord_mul_exp_gaussianVector A θ i i j).add
      (integrable_coord_mul_coord_mul_exp_gaussianVector A θ i' i' j)).const_mul _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hI
    (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (integrable_coord_mul_coord_mul_exp_gaussianVector A θ i i j)
    (integrable_coord_mul_coord_mul_exp_gaussianVector A θ i' i' j),
    integral_mul_mul_exp_gaussianVector, integral_mul_mul_exp_gaussianVector]
  ring

/-- Integrability on `(0, ∞)` of `K(t) · (r (a₀ (β√t)^0 E(t) + a₂ (β√t)^2 E(t)))` with
`E(t) = e^{(β√t)² c / 2}`, the shape of every bound `M(β√t)` used below. -/
theorem integrableOn_radialKernel_mul_comb (β μ c a₀ a₂ r : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (hδ : 0 < 1 - β * c / 2) :
    IntegrableOn (fun t => radialKernel β μ t * (r *
      (a₀ * ((β * Real.sqrt t) ^ 0 * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2)) +
        a₂ * ((β * Real.sqrt t) ^ 2 * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2))))) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => r *
      (a₀ * (radialKernel β μ t *
          ((β * Real.sqrt t) ^ 0 * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2))) +
        a₂ * (radialKernel β μ t *
          ((β * Real.sqrt t) ^ 2 * Real.exp ((β * Real.sqrt t) ^ 2 * c / 2))))) (Ioi 0) :=
    (((integrableOn_radialKernel_mul_tilt β μ c 0 hβ hμ hδ).const_mul a₀).add
      ((integrableOn_radialKernel_mul_tilt β μ c 2 hβ hμ hδ).const_mul a₂)).const_mul r
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  ring

/-- **`Q = 0`, Bochner form.** For `δ = 1 − β B_jj / 2 > 0`, `S_μ(G_j)` is integrable and
`E S_μ(G_j) = Γ(μ) (βδ)^{-μ}`. -/
theorem integral_fluctuation_gaussianVector (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (j : Fin m)
    (hδ : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) :
    Integrable (fun g => fluctuation β μ (g j)) (gaussianVector A) ∧
    ∫ g, fluctuation β μ (g j) ∂gaussianVector A =
      Real.Gamma μ *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) ^ (-μ) := by
  set c := (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j with hc
  have h := integral_mul_fluctuation_eq A β μ j (fun _ => 1) measurable_const
    (fun θ => θ ^ 0 * Real.exp (θ ^ 2 * c / 2))
    (fun θ => by simpa using integrable_exp_gaussianVector A θ j)
    (fun θ => by
      simp only [abs_one, one_mul, pow_zero]
      exact (integral_exp_gaussianVector A θ j).le)
    (integrableOn_radialKernel_mul_tilt β μ c 0 hβ hμ hδ)
  simp only [one_mul] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp_rw [integral_exp_gaussianVector, ← hc]
  have := integral_radialKernel_mul_tilt β μ c 0 hβ hμ hδ
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero] at this
  exact this

/-- **`Q = 1`.** For `δ = 1 − β B_jj / 2 > 0`, `G_i S_μ(G_j)` is integrable and
`E[G_i S_μ(G_j)] = β B_ij Γ(μ + 1/2) (βδ)^{-(μ + 1/2)}`. -/
theorem integral_coord_mul_fluctuation (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (i j : Fin m)
    (hδ : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) :
    Integrable (fun g => g i * fluctuation β μ (g j)) (gaussianVector A) ∧
    ∫ g, g i * fluctuation β μ (g j) ∂gaussianVector A =
      β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j * Real.Gamma (μ + 1 / 2) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) ^ (-(μ + 1 / 2)) := by
  set B := (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) with hB
  have h := integral_mul_fluctuation_eq A β μ j (fun g => g i) (measurable_pi_apply i)
    (fun θ => 2⁻¹ * ((1 + B i i) * (θ ^ 0 * Real.exp (θ ^ 2 * B j j / 2)) +
      B i j * B i j * (θ ^ 2 * Real.exp (θ ^ 2 * B j j / 2))))
    (fun θ => integrable_coord_mul_exp_gaussianVector A θ i j)
    (fun θ => integral_abs_coord_mul_exp_le A θ i j)
    (integrableOn_radialKernel_mul_comb β μ (B j j) (1 + B i i) (B i j * B i j) 2⁻¹ hβ hμ hδ)
  refine ⟨h.1, h.2.trans ?_⟩
  simp_rw [integral_mul_exp_gaussianVector, ← hB]
  have h1 := integral_radialKernel_mul_tilt β μ (B j j) 1 hβ hμ hδ
  simp only [pow_one, Nat.cast_one] at h1
  rw [show (fun t => radialKernel β μ t *
      (β * Real.sqrt t * B i j * Real.exp ((β * Real.sqrt t) ^ 2 * B j j / 2))) =
      fun t => B i j * (radialKernel β μ t *
        (β * Real.sqrt t * Real.exp ((β * Real.sqrt t) ^ 2 * B j j / 2))) from
      funext fun t => by ring, integral_const_mul, h1]
  ring

/-- **`Q = 2`.** For `δ = 1 − β B_jj / 2 > 0`, `G_i G_{i'} S_μ(G_j)` is integrable and
`E[G_i G_{i'} S_μ(G_j)] = B_{ii'} Γ(μ) (βδ)^{-μ} + β² B_ij B_{i'j} Γ(μ + 1) (βδ)^{-(μ + 1)}`. -/
theorem integral_coord_mul_coord_mul_fluctuation (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (i i' j : Fin m)
    (hδ : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) :
    Integrable (fun g => g i * g i' * fluctuation β μ (g j)) (gaussianVector A) ∧
    ∫ g, g i * g i' * fluctuation β μ (g j) ∂gaussianVector A =
      (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i' * Real.Gamma μ *
          (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) ^ (-μ) +
        β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' j * Real.Gamma (μ + 1) *
          (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) ^ (-(μ + 1)) := by
  set B := (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) with hB
  have h := integral_mul_fluctuation_eq A β μ j (fun g => g i * g i')
    ((measurable_pi_apply i).mul (measurable_pi_apply i'))
    (fun θ => 2⁻¹ * ((B i i + B i' i') * (θ ^ 0 * Real.exp (θ ^ 2 * B j j / 2)) +
      (B i j * B i j + B i' j * B i' j) * (θ ^ 2 * Real.exp (θ ^ 2 * B j j / 2))))
    (fun θ => integrable_coord_mul_coord_mul_exp_gaussianVector A θ i i' j)
    (fun θ => integral_abs_coord_mul_coord_mul_exp_le A θ i i' j)
    (integrableOn_radialKernel_mul_comb β μ (B j j) (B i i + B i' i')
      (B i j * B i j + B i' j * B i' j) 2⁻¹ hβ hμ hδ)
  refine ⟨h.1, h.2.trans ?_⟩
  simp_rw [integral_mul_mul_exp_gaussianVector, ← hB]
  have h0 := integral_radialKernel_mul_tilt β μ (B j j) 0 hβ hμ hδ
  have h2 := integral_radialKernel_mul_tilt β μ (B j j) 2 hβ hμ hδ
  rw [show (fun t => radialKernel β μ t *
      ((B i i' + (β * Real.sqrt t) ^ 2 * B i j * B i' j) *
        Real.exp ((β * Real.sqrt t) ^ 2 * B j j / 2))) =
      fun t => B i i' * (radialKernel β μ t *
          ((β * Real.sqrt t) ^ 0 * Real.exp ((β * Real.sqrt t) ^ 2 * B j j / 2))) +
        B i j * B i' j * (radialKernel β μ t *
          ((β * Real.sqrt t) ^ 2 * Real.exp ((β * Real.sqrt t) ^ 2 * B j j / 2))) from
      funext fun t => by ring,
    integral_add ((integrableOn_radialKernel_mul_tilt β μ (B j j) 0 hβ hμ hδ).const_mul _)
      ((integrableOn_radialKernel_mul_tilt β μ (B j j) 2 hβ hμ hδ).const_mul _),
    integral_const_mul, integral_const_mul, h0, h2]
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero, Nat.cast_ofNat,
    div_self (two_ne_zero' ℝ)]
  ring

end Grammar
