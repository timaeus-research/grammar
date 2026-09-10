import Grammar.BilocalGaussian

/-!
# The Gaussian-limit denominator `D(G)` and its expectation

`E₊ S_λ(G_j) = ∫₀^∞ t^{λ−1} e^{−β(1−βB_jj/2)t} dt` in `ℝ≥0∞`
(`lintegral_fluctuation_gaussianVector`), which is `+∞` when `βB_jj ≥ 2`
(`lintegral_fluctuation_gaussianVector_eq_top`). For the quartet denominator
`D(G) = ∑ᵢ ρᵢ S_λ(Gᵢ)` with constant covariance diagonal `c`:

* if `δ = 1 − βc/2 > 0`, `D(G)` is integrable and `E D(G) = Γ(λ)(βδ)^{−λ} ∑ᵢ ρᵢ`
  (`integral_quartetD`);
* if `βc ≥ 2`, `E₊ D(G) = +∞` and `D(G)` is not integrable (`lintegral_quartetD_eq_top`,
  `not_integrable_quartetD`).

On the divisor `c = 2`, so the expected Gaussian-limit denominator is finite exactly for `β < 1`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- `E₊ e^{θ G_j} = e^{θ² B_jj / 2}` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_exp_gaussianVector (θ : ℝ) (j : Fin m) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (θ * g j)) ∂gaussianVector A =
      ENNReal.ofReal (Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_gaussianVector A θ j)
    (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le), integral_exp_gaussianVector]

theorem measurable_radialKernel_exp_uncurry (β lam : ℝ) (j : Fin m) :
    Measurable (Function.uncurry fun (g : Fin m → ℝ) (t : ℝ) =>
      ENNReal.ofReal (radialKernel β lam t * Real.exp (β * Real.sqrt t * g j))) := by
  change Measurable fun p : (Fin m → ℝ) × ℝ =>
    ENNReal.ofReal (radialKernel β lam p.2 * Real.exp (β * Real.sqrt p.2 * p.1 j))
  exact Measurable.ennreal_ofReal (((measurable_radialKernel β lam).comp measurable_snd).mul
    (Measurable.exp ((measurable_const.mul measurable_snd.sqrt).mul
      ((measurable_pi_apply j).comp measurable_fst))))

/-- **Tonelli for the one-point function**:
`E₊ S_λ(G_j) = ∫₀^∞ t^{λ−1} e^{−β(1 − βB_jj/2) t} dt` in `ℝ≥0∞`. -/
theorem lintegral_fluctuation_gaussianVector (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (j : Fin m) :
    ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g j)) ∂gaussianVector A =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (lam - 1) *
        Real.exp (-(β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)) * t)) := by
  simp_rw [ofReal_fluctuation_eq_lintegral β lam hβ hlam]
  rw [lintegral_lintegral_swap (measurable_radialKernel_exp_uncurry β lam j).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hKt := radialKernel_nonneg (β := β) (μ := lam) ht
  have hg : ∀ g : Fin m → ℝ,
      ENNReal.ofReal (radialKernel β lam t * Real.exp (β * Real.sqrt t * g j)) =
      ENNReal.ofReal (radialKernel β lam t) * ENNReal.ofReal (Real.exp (β * Real.sqrt t * g j)) :=
    fun g => ENNReal.ofReal_mul hKt
  simp_rw [hg]
  have hm : Measurable fun g : Fin m → ℝ => ENNReal.ofReal (Real.exp (β * Real.sqrt t * g j)) :=
    Measurable.ennreal_ofReal (Measurable.exp (measurable_const.mul (measurable_pi_apply j)))
  rw [lintegral_const_mul _ hm, lintegral_ofReal_exp_gaussianVector, ← ENNReal.ofReal_mul hKt]
  congr 1
  rw [radialKernel, mul_pow, Real.sq_sqrt (le_of_lt ht), mul_assoc (t ^ (lam - 1)), ← Real.exp_add]
  congr 2
  ring

/-- `∫₀^∞ t^{λ−1} dt = +∞` for `λ > 0` (the tail alone diverges). -/
theorem lintegral_ofReal_rpow_Ioi_eq_top (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (lam - 1)) = ⊤ := by
  have h1 : ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-1 : ℝ)) = ⊤ := by
    by_contra h
    have hfin : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi 1) := by
      refine ⟨(measurable_id.pow_const _).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        Real.rpow_nonneg (by linarith [mem_Ioi.1 ht]) _)]
      exact lt_top_iff_ne_top.2 h
    exact absurd ((integrableOn_Ioi_rpow_iff one_pos).1 hfin) (lt_irrefl _)
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-1 : ℝ)) := h1.symm
    _ ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (lam - 1)) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (by linarith))
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (lam - 1)) :=
        lintegral_mono_set (Ioi_subset_Ioi zero_le_one)

/-- **Divergence of the one-point function at and above threshold**: `E₊ S_λ(G_j) = +∞` when
`βB_jj ≥ 2`. -/
theorem lintegral_fluctuation_gaussianVector_eq_top (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (j : Fin m) (h : 2 ≤ β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j) :
    ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g j)) ∂gaussianVector A = ⊤ := by
  rw [lintegral_fluctuation_gaussianVector A β lam hβ hlam j, eq_top_iff,
    ← lintegral_ofReal_rpow_Ioi_eq_top lam hlam]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal ?_
  have ht' : 0 < t := ht
  have hexp : 1 ≤ Real.exp (-(β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2))
      * t) := by
    refine Real.one_le_exp ?_
    have := mul_nonneg (mul_nonneg hβ.le
      (by linarith : (0 : ℝ) ≤ β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2 - 1))
      ht'.le
    nlinarith [this]
  calc t ^ (lam - 1) = t ^ (lam - 1) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht'.le _)

/-! ### The quartet denominator -/

variable {β lam : ℝ}

/-- **The Gaussian-limit denominator below threshold**: for `δ = 1 − βc/2 > 0`, `D(G)` is
integrable and `E D(G) = Γ(λ)(βδ)^{−λ} ∑ᵢ ρᵢ`. -/
theorem integral_quartetD (hβ : 0 < β) (hlam : 0 < lam) (ρ : Fin m → ℝ) {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (hδ : 0 < 1 - β * c / 2) :
    Integrable (quartetD β lam ρ) (gaussianVector A) ∧
    ∫ g, quartetD β lam ρ g ∂gaussianVector A =
      Real.Gamma lam * (β * (1 - β * c / 2)) ^ (-lam) * ∑ i, ρ i := by
  have hi : ∀ i, 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2 := fun i => by
    rw [hc i]
    exact hδ
  have hint : ∀ i, Integrable (fun g : Fin m → ℝ => ρ i * fluctuation β lam (g i))
      (gaussianVector A) := fun i =>
    (integral_fluctuation_gaussianVector A β lam hβ hlam i (hi i)).1.const_mul _
  refine ⟨?_, ?_⟩
  · unfold quartetD
    exact integrable_finsetSum _ fun i _ => hint i
  · unfold quartetD
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, (integral_fluctuation_gaussianVector A β lam hβ hlam i (hi i)).2, hc i]
    ring

/-- **The Gaussian-limit denominator at and above threshold**: `E₊ D(G) = +∞` when `βc ≥ 2`. -/
theorem lintegral_quartetD_eq_top (hβ : 0 < β) (hlam : 0 < lam) {ρ : Fin m → ℝ}
    (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (h2 : 2 ≤ β * c) :
    ∫⁻ g, ENNReal.ofReal (quartetD β lam ρ g) ∂gaussianVector A = ⊤ := by
  obtain ⟨j⟩ := ‹Nonempty (Fin m)›
  have hSm : Measurable fun g : Fin m → ℝ => ENNReal.ofReal (fluctuation β lam (g j)) :=
    ((continuous_fluctuation β lam hβ hlam).comp (continuous_apply j)).measurable.ennreal_ofReal
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (ρ j) *
        ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g j)) ∂gaussianVector A := by
        rw [lintegral_fluctuation_gaussianVector_eq_top A β lam hβ hlam j (by rw [hc j]; exact h2),
          ENNReal.mul_top (ENNReal.ofReal_pos.2 (hρ j)).ne']
    _ = ∫⁻ g, ENNReal.ofReal (ρ j * fluctuation β lam (g j)) ∂gaussianVector A := by
        rw [← lintegral_const_mul _ hSm]
        exact lintegral_congr fun g => (ENNReal.ofReal_mul (hρ j).le).symm
    _ ≤ ∫⁻ g, ENNReal.ofReal (quartetD β lam ρ g) ∂gaussianVector A :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (f := fun i => ρ i * fluctuation β lam (g i))
            (fun i _ => (mul_pos (hρ i) (fluctuation_pos β lam (g i) hβ hlam)).le)
            (Finset.mem_univ j))

theorem not_integrable_quartetD (hβ : 0 < β) (hlam : 0 < lam) {ρ : Fin m → ℝ}
    (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (h2 : 2 ≤ β * c) :
    ¬ Integrable (quartetD β lam ρ) (gaussianVector A) := by
  intro h
  have hfin := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g =>
    (quartetD_pos hβ hlam hρ g).le), lintegral_quartetD_eq_top A hβ hlam hρ hc h2] at hfin
  exact lt_irrefl _ hfin

end Grammar
