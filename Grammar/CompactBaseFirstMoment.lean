import Grammar.CompactBaseGaussian
import Grammar.UniformMomentSubgaussian
import Grammar.GaussianDenominator

/-!
# The annealed compact-base denominator and its uniform moments

For a Gaussian field `G` with kernel `𝒞` on a compact base `(K, ρ)` (`GaussianField`), the
one-point laws `G(x) ~ N(0, C(x,x))` give the exponential moments
`E e^{tG(x)} = e^{C(x,x)t²/2}` (`GaussianField.lintegral_exp_eval`) and the one-point Tonelli
identity `E₊ S_λ(G(x)) = ∫₀^∞ t^{λ−1}e^{−β(1 − βC(x,x)/2)t}dt` (`lintegral_fluctuation_eval`).
Tonelli over `Ω × K` (joint measurability from `measurable_uncurry_eval`) then gives

* **the exact annealed denominator** `E D_ρ(G) = Γ(λ) ∫_K [β(1 − βC(x,x)/2)]^{−λ} dρ(x)` when
  `βC(x,x) < 2` everywhere (`integral_compactD_eq`), and for a constant diagonal `C(x,x) = c`
  **`E D_ρ(G) = ρ(K)Γ(λ)(β(1 − βc/2))^{−λ} = D_ρ(0)(1 − βc/2)^{−λ}`**
  (`integral_compactD_eq_of_const_diag`, `integral_compactD_eq_compactD_zero_mul`) — the continuum
  version of `cor:denominator`, exhibiting the Gaussian inflation of `E D` over `D(0)`;
* **divergence**: `E₊ D_ρ(G) = ∞` as soon as `2 ≤ βC(x,x)` on a set of positive `ρ`-measure
  (`lintegral_compactD_eq_top`); an overcritical variance on a `ρ`-null set does not force this;
* **uniform `p`-th moments** (`p ≥ 1`): with `C(x,x) ≤ c` and `pβc < 2`,
  `E[D_ρ(G)^p] ≤ [ρ(K)Γ(λ)(β(1 − pβc/2))^{−λ}]^p` (`integrable_compactD_rpow`), from the
  pointwise-MGF theorem of `UniformMomentSubgaussian.lean`.

Correlations do not enter the first-moment formula (they enter `E log D`, `Q`, `V`). The second
sup-norm moment of the field makes `E|log D|` finite for every `β`; it does not make `E D` finite.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Grammar

theorem PSDKernel.kernelMatrix_single {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K) (x : K) :
    𝒞.kernelMatrix (fun _ : Fin 1 => x) 0 0 = 𝒞.C x x := rfl

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P)

omit [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- The one-point exponential moment: `E e^{tG(x)} = e^{C(x,x)t²/2}`. -/
theorem lintegral_exp_eval (x : K) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Γ.G ω x)) ∂P =
      ENNReal.ofReal (Real.exp (𝒞.C x x * t ^ 2 / 2)) := by
  obtain ⟨n, A, hAB, hA⟩ := Γ.law 1 (fun _ => x)
  have hm : Measurable fun v : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (t * v 0)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_pi_apply 0)))
  have h := lintegral_map (μ := P) hm (Γ.measurable_evalVec (fun _ : Fin 1 => x))
  simp only at h
  rw [hA, lintegral_ofReal_exp_gaussianVector, hAB, PSDKernel.kernelMatrix_single] at h
  rw [← h]
  congr 2
  ring

omit [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- The one-point Tonelli identity for the fluctuation function of the field. -/
theorem lintegral_fluctuation_eval {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (x : K) :
    ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (lam - 1) *
        Real.exp (-(β * (1 - β * 𝒞.C x x / 2)) * t)) := by
  obtain ⟨n, A, hAB, hA⟩ := Γ.law 1 (fun _ => x)
  have hm : Measurable fun v : Fin 1 → ℝ => ENNReal.ofReal (fluctuation β lam (v 0)) :=
    ENNReal.measurable_ofReal.comp ((continuous_fluctuation β lam hβ hlam).measurable.comp
      (measurable_pi_apply 0))
  have h := lintegral_map (μ := P) hm (Γ.measurable_evalVec (fun _ : Fin 1 => x))
  simp only at h
  rw [hA, lintegral_fluctuation_gaussianVector A β lam hβ hlam 0, hAB,
    PSDKernel.kernelMatrix_single] at h
  exact h.symm

omit [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- `E₊ S_λ(G(x)) = Γ(λ)(β(1 − βC(x,x)/2))^{−λ}` below threshold. -/
theorem lintegral_fluctuation_eval_of_lt {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (x : K)
    (hx : β * 𝒞.C x x < 2) :
    ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P =
      ENNReal.ofReal (Real.Gamma lam * (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam)) := by
  rw [Γ.lintegral_fluctuation_eval hβ hlam x]
  have hα : 0 < β * (1 - β * 𝒞.C x x / 2) := mul_pos hβ (by linarith)
  have := gammaWeight_univ hlam hα
  rw [gammaWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  exact this

omit [MeasurableSpace K] [BorelSpace K] [IsProbabilityMeasure P] in
/-- `E₊ S_λ(G(x)) = ∞` at or above threshold. -/
theorem lintegral_fluctuation_eval_eq_top {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (x : K)
    (hx : 2 ≤ β * 𝒞.C x x) :
    ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P = ⊤ := by
  obtain ⟨n, A, hAB, hA⟩ := Γ.law 1 (fun _ => x)
  have hm : Measurable fun v : Fin 1 → ℝ => ENNReal.ofReal (fluctuation β lam (v 0)) :=
    ENNReal.measurable_ofReal.comp ((continuous_fluctuation β lam hβ hlam).measurable.comp
      (measurable_pi_apply 0))
  have h := lintegral_map (μ := P) hm (Γ.measurable_evalVec (fun _ : Fin 1 => x))
  simp only at h
  rw [hA, lintegral_fluctuation_gaussianVector_eq_top A β lam hβ hlam 0
    (by rw [hAB, PSDKernel.kernelMatrix_single]; exact hx)] at h
  exact h.symm

variable (ρ : Measure K) [IsFiniteMeasure ρ]

omit [IsProbabilityMeasure P] in
theorem measurable_uncurry_G : Measurable fun q : Ω × K => Γ.G q.1 q.2 :=
  measurable_uncurry_eval Γ.G Γ.measurable_eval

/-- **Tonelli for the annealed denominator**:
`E₊ D_ρ(G) = ∫_K E₊ S_λ(G(x)) dρ(x)`. -/
theorem lintegral_compactD_eq_lintegral {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    ∫⁻ ω, ENNReal.ofReal (compactD β lam ρ (Γ.G ω)) ∂P =
      ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P ∂ρ := by
  simp_rw [ofReal_compactD ρ hβ hlam]
  exact lintegral_lintegral_swap (ENNReal.measurable_ofReal.comp
    ((continuous_fluctuation β lam hβ hlam).measurable.comp Γ.measurable_uncurry_G)).aemeasurable

/-- **The exact annealed denominator on the compact base** (ENNReal form): when `βC(x,x) < 2`
for every `x`, `E₊ D_ρ(G) = ∫_K Γ(λ)(β(1 − βC(x,x)/2))^{−λ} dρ(x)`. -/
theorem lintegral_compactD_eq {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (h : ∀ x, β * 𝒞.C x x < 2) :
    ∫⁻ ω, ENNReal.ofReal (compactD β lam ρ (Γ.G ω)) ∂P =
      ∫⁻ x, ENNReal.ofReal (Real.Gamma lam * (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam)) ∂ρ := by
  rw [Γ.lintegral_compactD_eq_lintegral ρ hβ hlam]
  exact lintegral_congr fun x => Γ.lintegral_fluctuation_eval_of_lt hβ hlam x (h x)

/-- **Divergence**: `E₊ D_ρ(G) = ∞` when `2 ≤ βC(x,x)` on a set of positive `ρ`-measure. -/
theorem lintegral_compactD_eq_top {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hS : 0 < ρ {x | 2 ≤ β * 𝒞.C x x}) :
    ∫⁻ ω, ENNReal.ofReal (compactD β lam ρ (Γ.G ω)) ∂P = ⊤ := by
  rw [Γ.lintegral_compactD_eq_lintegral ρ hβ hlam]
  have hmeas : MeasurableSet {x | 2 ≤ β * 𝒞.C x x} :=
    measurableSet_le measurable_const (measurable_const.mul 𝒞.continuous_diag.measurable)
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ x in {x | 2 ≤ β * 𝒞.C x x}, (⊤ : ℝ≥0∞) ∂ρ := by
        rw [setLIntegral_const, ENNReal.top_mul hS.ne']
    _ = ∫⁻ x in {x | 2 ≤ β * 𝒞.C x x},
          ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P ∂ρ :=
        setLIntegral_congr_fun hmeas fun x hx =>
          (Γ.lintegral_fluctuation_eval_eq_top hβ hlam x hx).symm
    _ ≤ ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (fluctuation β lam (Γ.G ω x)) ∂P ∂ρ :=
        setLIntegral_le_lintegral _ _

/-- **The exact annealed denominator** (Bochner form): when `βC(x,x) < 2` everywhere,
`D_ρ(G)` is integrable and `E D_ρ(G) = Γ(λ) ∫_K [β(1 − βC(x,x)/2)]^{−λ} dρ(x)`. -/
theorem integral_compactD_eq {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (h : ∀ x, β * 𝒞.C x x < 2) :
    Integrable (fun ω => compactD β lam ρ (Γ.G ω)) P ∧
      ∫ ω, compactD β lam ρ (Γ.G ω) ∂P =
        Real.Gamma lam * ∫ x, (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam) ∂ρ := by
  have hD0 : ∀ ω, 0 ≤ compactD β lam ρ (Γ.G ω) := fun ω =>
    integral_nonneg fun x => (fluctuation_pos β lam _ hβ hlam).le
  have hcont : Continuous fun x => (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam) := by
    refine Continuous.rpow_const (continuous_const.mul (continuous_const.sub
      ((continuous_const.mul 𝒞.continuous_diag).div_const 2))) fun x => Or.inl ?_
    exact (mul_pos hβ (by linarith [h x])).ne'
  have hpos : ∀ x, 0 ≤ (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam) := fun x =>
    Real.rpow_nonneg (mul_pos hβ (by linarith [h x])).le _
  have hint : Integrable (fun x => (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam)) ρ :=
    integrable_of_continuous_compactSpace ρ hcont
  have hE := Γ.lintegral_compactD_eq ρ hβ hlam h
  have hR : ∫⁻ x, ENNReal.ofReal (Real.Gamma lam * (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam)) ∂ρ =
      ENNReal.ofReal (Real.Gamma lam * ∫ x, (β * (1 - β * 𝒞.C x x / 2)) ^ (-lam) ∂ρ) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (Filter.Eventually.of_forall fun x => mul_nonneg (Real.Gamma_pos_of_pos hlam).le (hpos x))]
  rw [hR] at hE
  have hmeas : Measurable fun ω => compactD β lam ρ (Γ.G ω) :=
    measurable_compactD_comp ρ hβ hlam Γ.G Γ.measurable_uncurry_G
  have hI : Integrable (fun ω => compactD β lam ρ (Γ.G ω)) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hD0), hE]
    exact ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hD0)
  rw [← this] at hE
  exact ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hD0)
    (mul_nonneg (Real.Gamma_pos_of_pos hlam).le (integral_nonneg hpos)) |>.1 hE

/-- **Constant diagonal**: `E D_ρ(G) = ρ(K) Γ(λ)(β(1 − βc/2))^{−λ}`. -/
theorem integral_compactD_eq_of_const_diag {β lam c : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hc : ∀ x, 𝒞.C x x = c) (h : β * c < 2) :
    ∫ ω, compactD β lam ρ (Γ.G ω) ∂P =
      ρ.real univ * (Real.Gamma lam * (β * (1 - β * c / 2)) ^ (-lam)) := by
  rw [(Γ.integral_compactD_eq ρ hβ hlam fun x => by rw [hc x]; exact h).2]
  simp only [hc, integral_const, smul_eq_mul]
  ring

/-- **The Gaussian inflation**: `E D_ρ(G) = D_ρ(0) · (1 − βc/2)^{−λ}` for a constant diagonal. -/
theorem integral_compactD_eq_compactD_zero_mul {β lam c : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hc : ∀ x, 𝒞.C x x = c) (h : β * c < 2) :
    ∫ ω, compactD β lam ρ (Γ.G ω) ∂P =
      compactD β lam ρ (0 : C(K, ℝ)) * (1 - β * c / 2) ^ (-lam) := by
  rw [Γ.integral_compactD_eq_of_const_diag ρ hβ hlam hc h, compactD_zero ρ hβ hlam,
    Real.mul_rpow hβ.le (by linarith)]
  ring

/-- **Uniform `p`-th moment of the annealed denominator** (`p ≥ 1`): with `C(x,x) ≤ c` and
`pβc < 2`, `D_ρ(G)^p` is integrable and `E[D_ρ(G)^p] ≤ [ρ(K)Γ(λ)(β(1 − pβc/2))^{−λ}]^p`. -/
theorem integrable_compactD_rpow {β lam c p : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hp : 1 ≤ p)
    (hc : ∀ x, 𝒞.C x x ≤ c) (h : p * β * c < 2) (hρ : ρ ≠ 0) :
    Integrable (fun ω => compactD β lam ρ (Γ.G ω) ^ p) P ∧
      ∫ ω, compactD β lam ρ (Γ.G ω) ^ p ∂P ≤ subgaussianBound β lam c p (ρ.real univ) ^ p :=
  integrable_compactD_rpow_of_subgaussian P ρ hβ hlam hp h hρ Γ.G Γ.measurable_uncurry_G
    fun x t _ => by
      rw [Γ.lintegral_exp_eval x t]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
        have := hc x
        have : 0 ≤ t ^ 2 := sq_nonneg t
        nlinarith))

end GaussianField

end Grammar
