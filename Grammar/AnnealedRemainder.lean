import Grammar.EmpiricalExpGap
import Mathlib.Probability.Moments.SubGaussian

/-!
# The expected positive-gap remainder from annealed exponential moments

The pathwise remainder bound of `EmpiricalExpGap` lives on the good event
`sup_gap |ξ_n| ≤ ½√(nκ)`; it says nothing about `E|Rem|`, and `‖F‖·P(bad)` is *not* a valid
complement (the empirical exponential may be large precisely on the bad event). The honest route
to an expectation-level bound is annealed: if for every gap point `y`

`E exp(β√N φ(y) ξ(·, y)) ≤ exp(θ β N φ(y)²)`, `θ ≤ 1`,

then, with `K = φ² ≥ κ` on the gap and `|a| ≤ g`, Tonelli gives

`E ‖∫_S a e^{−βNφ² + β√N φ ξ}‖ ≤ e^{−(1−θ)βNκ} ∫_S g`

(`lintegral_enorm_annealedRemainder_le`, in `ℝ≥0∞`; Bochner form
`integral_abs_annealedRemainder_le`). Only *pointwise* exponential moments enter — no supremum
tail bound. A pointwise sub-Gaussian hypothesis `E e^{tξ(y)} ≤ e^{ct²/2}` gives `θ = cβ/2`, hence
exponential decay exactly when `βc < 2` (`lintegral_enorm_annealedRemainder_le_of_subgaussian`) —
the same threshold as the Gaussian-limit dichotomy — and for bounded independent centred
observations the normalised sum `n^{−1/2}∑(Zᵢ − EZᵢ)` is sub-Gaussian with `c = (range/2)²`
uniformly in `n` by Hoeffding's lemma (`lintegral_ofReal_exp_normalisedSum_le`), giving the
expectation-level remainder bound for bounded i.i.d. coefficients
(`lintegral_enorm_annealedRemainder_le_of_bounded`).

Also the generic good/bad-event bound `E|R| ≤ A e^{−an} + B·P(bad)` under a deterministic control
`|R| ≤ B` on the bad event (`lintegral_enorm_le_of_good_bad`), which makes the missing hypothesis
of the pathwise route explicit.

Non-claims: no supremum tail bound for `ξ_n`, no chaining or covering numbers; the expectation of
the *core* terms is not addressed here.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {P : Measure Ω}
  [IsProbabilityMeasure P] {μ : Measure Y} [SFinite μ]

/-- The random remainder `R(ω) = ∫_S a(y) e^{−βNφ(y)² + β√N φ(y) ξ(ω,y)} dμ(y)`. -/
noncomputable def annealedRemainder (μ : Measure Y) (S : Set Y) (a φ : Y → ℝ) (ξ : Ω → Y → ℝ)
    (β N : ℝ) (ω : Ω) : ℝ :=
  ∫ y in S, a y * Real.exp (-β * N * φ y ^ 2 + β * Real.sqrt N * φ y * ξ ω y) ∂μ

/-! ### The generic good/bad-event bound -/

/-- **Good/bad events**: if `‖R‖ ≤ A` on the good event `Gd` and `‖R‖ ≤ B` on its complement, then
`E‖R‖ ≤ A + B·P(Gdᶜ)`. -/
theorem lintegral_enorm_le_of_good_bad {R : Ω → ℝ} {Gd : Set Ω} (hGd : MeasurableSet Gd) {A B : ℝ}
    (hgood : ∀ ω ∈ Gd, ‖R ω‖ ≤ A) (hbad : ∀ ω ∉ Gd, ‖R ω‖ ≤ B) :
    ∫⁻ ω, ‖R ω‖ₑ ∂P ≤ ENNReal.ofReal A + ENNReal.ofReal B * P Gdᶜ := by
  rw [← lintegral_add_compl _ hGd]
  refine add_le_add ?_ ?_
  · calc ∫⁻ ω in Gd, ‖R ω‖ₑ ∂P ≤ ∫⁻ _ in Gd, ENNReal.ofReal A ∂P :=
          setLIntegral_mono' hGd fun ω hω => by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hgood ω hω)
      _ ≤ ENNReal.ofReal A := by
          rw [setLIntegral_const]
          exact mul_le_of_le_one_right' prob_le_one
  · calc ∫⁻ ω in Gdᶜ, ‖R ω‖ₑ ∂P ≤ ∫⁻ _ in Gdᶜ, ENNReal.ofReal B ∂P :=
          setLIntegral_mono' hGd.compl fun ω hω => by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hbad ω hω)
      _ = ENNReal.ofReal B * P Gdᶜ := setLIntegral_const _ _

/-! ### The annealed bound -/

theorem measurable_annealedIntegrand {a φ : Y → ℝ} (ha : Measurable a) (hφ : Measurable φ)
    {ξ : Ω → Y → ℝ} (hξ : Measurable (Function.uncurry ξ)) (β N : ℝ) :
    Measurable fun p : Ω × Y =>
      a p.2 * Real.exp (-β * N * φ p.2 ^ 2 + β * Real.sqrt N * φ p.2 * ξ p.1 p.2) :=
  (ha.comp measurable_snd).mul (Measurable.exp
    (((measurable_const.mul ((hφ.comp measurable_snd).pow_const 2))).add
      ((measurable_const.mul (hφ.comp measurable_snd)).mul hξ)))

omit [IsProbabilityMeasure P] in
/-- The random remainder is a measurable function of `ω` (jointly measurable integrand). -/
theorem aestronglyMeasurable_annealedRemainder (S : Set Y) {a φ : Y → ℝ} (ha : Measurable a)
    (hφ : Measurable φ) {ξ : Ω → Y → ℝ} (hξ : Measurable (Function.uncurry ξ)) (β N : ℝ) :
    AEStronglyMeasurable (annealedRemainder μ S a φ ξ β N) P :=
  (measurable_annealedIntegrand ha hφ hξ β N).aestronglyMeasurable.integral_prod_right'
    (μ := P) (ν := μ.restrict S)

/-- **The annealed remainder bound.** On a gap `S` with `κ ≤ φ²`, `|a| ≤ g`, and pointwise
exponential moments `E e^{β√N φ(y) ξ(·,y)} ≤ e^{θβNφ(y)²}` with `θ ≤ 1`:
`E‖∫_S a e^{−βNφ² + β√N φ ξ}‖ ≤ e^{−(1−θ)βNκ} ∫_S g`. -/
theorem lintegral_enorm_annealedRemainder_le (S : Set Y) (hS : MeasurableSet S) (a g φ : Y → ℝ)
    (hφ : Measurable φ) (ξ : Ω → Y → ℝ) (hξ : Measurable (Function.uncurry ξ)) {β N κ θ : ℝ}
    (hβ : 0 ≤ β) (hN : 0 ≤ N) (hθ : θ ≤ 1) (hbound : ∀ y ∈ S, |a y| ≤ g y)
    (hgap : ∀ y ∈ S, κ ≤ φ y ^ 2) (hg : IntegrableOn g S μ)
    (hann : ∀ y ∈ S, ∫⁻ ω, ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ y * ξ ω y)) ∂P ≤
      ENNReal.ofReal (Real.exp (θ * β * N * φ y ^ 2))) :
    ∫⁻ ω, ‖annealedRemainder μ S a φ ξ β N ω‖ₑ ∂P ≤
      ENNReal.ofReal (Real.exp (-((1 - θ) * β * N * κ)) * ∫ y in S, g y ∂μ) := by
  have hg0 : ∀ y ∈ S, 0 ≤ g y := fun y hy => (abs_nonneg _).trans (hbound y hy)
  -- the dominating product kernel
  obtain ⟨F, hF⟩ : ∃ F : Ω → Y → ℝ≥0∞, F = fun ω y =>
      ENNReal.ofReal (g y * Real.exp (-β * N * φ y ^ 2)) *
        ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ y * ξ ω y)) := ⟨_, rfl⟩
  have hgm : AEMeasurable g (μ.restrict S) := hg.aestronglyMeasurable.aemeasurable
  have hFm : AEMeasurable (Function.uncurry F) (P.prod (μ.restrict S)) := by
    have h1 : AEMeasurable (fun p : Ω × Y => ENNReal.ofReal (g p.2 * Real.exp (-β * N * φ p.2 ^ 2)))
        (P.prod (μ.restrict S)) :=
      ((hgm.mul (Measurable.exp (measurable_const.mul (hφ.pow_const 2))).aemeasurable
        ).ennreal_ofReal).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEMeasurable
        (fun p : Ω × Y => ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ p.2 * ξ p.1 p.2)))
        (P.prod (μ.restrict S)) :=
      (Measurable.ennreal_ofReal (Measurable.exp
        ((measurable_const.mul (hφ.comp measurable_snd)).mul hξ))).aemeasurable
    rw [hF]
    exact h1.mul h2
  -- pointwise domination of the integrand on `S`
  have hpt : ∀ ω, ∀ y ∈ S,
      ‖a y * Real.exp (-β * N * φ y ^ 2 + β * Real.sqrt N * φ y * ξ ω y)‖ₑ ≤ F ω y := by
    intro ω y hy
    simp only [hF]
    rw [Real.enorm_eq_ofReal_abs, abs_mul, Real.abs_exp, Real.exp_add, ← ENNReal.ofReal_mul
      (mul_nonneg (hg0 y hy) (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbound y hy) (Real.exp_pos (-β * N * φ y ^ 2)).le
    nlinarith [Real.exp_pos (β * Real.sqrt N * φ y * ξ ω y), this]
  -- step 1: `E‖R‖ ≤ ∫⁻ ω ∫⁻ y F`
  have h1 : ∫⁻ ω, ‖annealedRemainder μ S a φ ξ β N ω‖ₑ ∂P ≤
      ∫⁻ ω, ∫⁻ y in S, F ω y ∂μ ∂P := by
    refine lintegral_mono fun ω => ?_
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    exact setLIntegral_mono' hS fun y hy => hpt ω y hy
  -- step 2: swap and use the annealed hypothesis
  have h2 : ∫⁻ ω, ∫⁻ y in S, F ω y ∂μ ∂P ≤
      ∫⁻ y in S, ENNReal.ofReal (g y * Real.exp (-((1 - θ) * β * N * κ))) ∂μ := by
    rw [lintegral_lintegral_swap hFm]
    refine setLIntegral_mono' hS fun y hy => ?_
    have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ y * ξ ω y)) :=
      Measurable.ennreal_ofReal (Measurable.exp (measurable_const.mul
        (hξ.comp (measurable_id.prodMk measurable_const))))
    simp only [hF]
    rw [lintegral_const_mul _ hm]
    calc ENNReal.ofReal (g y * Real.exp (-β * N * φ y ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ y * ξ ω y)) ∂P
        ≤ ENNReal.ofReal (g y * Real.exp (-β * N * φ y ^ 2)) *
          ENNReal.ofReal (Real.exp (θ * β * N * φ y ^ 2)) :=
          mul_le_mul' le_rfl (hann y hy)
      _ = ENNReal.ofReal (g y * Real.exp (-((1 - θ) * β * N * φ y ^ 2))) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (hg0 y hy) (Real.exp_pos _).le), mul_assoc,
            ← Real.exp_add]
          congr 3
          ring
      _ ≤ ENNReal.ofReal (g y * Real.exp (-((1 - θ) * β * N * κ))) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
            (hg0 y hy))
          have h0 : 0 ≤ (1 - θ) * β * N := mul_nonneg (mul_nonneg (by linarith) hβ) hN
          nlinarith [mul_le_mul_of_nonneg_left (hgap y hy) h0]
  -- step 3: pull out the constant
  refine h1.trans (h2.trans (le_of_eq ?_))
  have hgint : ∫⁻ y in S, ENNReal.ofReal (g y) ∂μ = ENNReal.ofReal (∫ y in S, g y ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hg (ae_restrict_of_forall_mem hS hg0)).symm
  have hpt2 : ∀ y, ENNReal.ofReal (g y * Real.exp (-((1 - θ) * β * N * κ))) =
      ENNReal.ofReal (Real.exp (-((1 - θ) * β * N * κ))) * ENNReal.ofReal (g y) := fun y => by
    rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt2]
  rw [lintegral_const_mul'' _ hgm.ennreal_ofReal, hgint,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Bochner form**: the random remainder is integrable and `E|R| ≤ e^{−(1−θ)βNκ} ∫_S g`. -/
theorem integral_abs_annealedRemainder_le (S : Set Y) (hS : MeasurableSet S) (a g φ : Y → ℝ)
    (ha : Measurable a) (hφ : Measurable φ) (ξ : Ω → Y → ℝ) (hξ : Measurable (Function.uncurry ξ))
    {β N κ θ : ℝ} (hβ : 0 ≤ β) (hN : 0 ≤ N) (hθ : θ ≤ 1) (hbound : ∀ y ∈ S, |a y| ≤ g y)
    (hgap : ∀ y ∈ S, κ ≤ φ y ^ 2) (hg : IntegrableOn g S μ)
    (hann : ∀ y ∈ S, ∫⁻ ω, ENNReal.ofReal (Real.exp (β * Real.sqrt N * φ y * ξ ω y)) ∂P ≤
      ENNReal.ofReal (Real.exp (θ * β * N * φ y ^ 2))) :
    Integrable (annealedRemainder μ S a φ ξ β N) P ∧
    ∫ ω, |annealedRemainder μ S a φ ξ β N ω| ∂P ≤
      Real.exp (-((1 - θ) * β * N * κ)) * ∫ y in S, g y ∂μ := by
  have hle := lintegral_enorm_annealedRemainder_le S hS a g φ hφ ξ hξ hβ hN hθ hbound hgap hg hann
  have hRm := aestronglyMeasurable_annealedRemainder (μ := μ) (P := P) S ha hφ hξ β N
  have hint : Integrable (annealedRemainder μ S a φ ξ β N) P :=
    ⟨hRm, hasFiniteIntegral_iff_enorm.2 (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have hg0 : ∀ y ∈ S, 0 ≤ g y := fun y hy => (abs_nonneg _).trans (hbound y hy)
  have hgnn : 0 ≤ ∫ y in S, g y ∂μ :=
    setIntegral_nonneg hS hg0
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    hRm.norm, ← ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hgnn)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  simpa only [← Real.enorm_eq_ofReal_abs] using hle

/-! ### Sub-Gaussian fluctuations -/

omit [IsProbabilityMeasure P] in
/-- A sub-Gaussian variable has exponential moments `E e^{tX} ≤ e^{ct²/2}` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_exp_le_of_hasSubgaussianMGF {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c P) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_mul t)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (h.mgf_le t)

/-- **Sub-Gaussian fluctuations give the annealed hypothesis with `θ = cβ/2`.** -/
theorem lintegral_enorm_annealedRemainder_le_of_subgaussian (S : Set Y) (hS : MeasurableSet S)
    (a g φ : Y → ℝ) (hφ : Measurable φ) (ξ : Ω → Y → ℝ) (hξ : Measurable (Function.uncurry ξ))
    {β N κ : ℝ} (hβ : 0 ≤ β) (hN : 0 ≤ N) (c : ℝ≥0) (hc : (c : ℝ) * β ≤ 2)
    (hsub : ∀ y ∈ S, HasSubgaussianMGF (fun ω => ξ ω y) c P) (hbound : ∀ y ∈ S, |a y| ≤ g y)
    (hgap : ∀ y ∈ S, κ ≤ φ y ^ 2) (hg : IntegrableOn g S μ) :
    ∫⁻ ω, ‖annealedRemainder μ S a φ ξ β N ω‖ₑ ∂P ≤
      ENNReal.ofReal (Real.exp (-((1 - c * β / 2) * β * N * κ)) * ∫ y in S, g y ∂μ) := by
  refine lintegral_enorm_annealedRemainder_le S hS a g φ hφ ξ hξ hβ hN (by linarith) hbound hgap hg
    fun y hy => ?_
  refine (lintegral_ofReal_exp_le_of_hasSubgaussianMGF (hsub y hy) (β * Real.sqrt N * φ y)).trans
    (le_of_eq ?_)
  congr 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hN]
  ring

/-- **Hoeffding**: for independent observations `Zᵢ ∈ [lo, hi]` a.s., the centred sum
`∑_{i<n} (Zᵢ − E Zᵢ)` is sub-Gaussian with constant `n·((hi − lo)/2)²`. -/
theorem hasSubgaussianMGF_centredSum_of_mem_Icc {Z : ℕ → Ω → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) {lo hi : ℝ} (hZ : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Icc lo hi) (n : ℕ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.range n, (Z i ω - ∫ ω', Z i ω' ∂P))
      (n • (‖hi - lo‖₊ / 2) ^ 2) P := by
  have hcent : ∀ i, HasSubgaussianMGF (fun ω => Z i ω - ∫ ω', Z i ω' ∂P) ((‖hi - lo‖₊ / 2) ^ 2) P :=
    fun i => hasSubgaussianMGF_of_mem_Icc (hZm i).aemeasurable (hZ i)
  have hind' : iIndepFun (fun i ω => Z i ω - ∫ ω', Z i ω' ∂P) P :=
    hind.comp (fun i (x : ℝ) => x - ∫ ω', Z i ω' ∂P) fun i => measurable_id.sub_const _
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind' (s := Finset.range n) fun i _ => hcent i
  simpa only [Finset.sum_const, Finset.card_range] using hsum

/-- **Exponential moments of the normalised centred sum**, uniformly in `n`:
`E exp(t · n^{−1/2} ∑_{i<n}(Zᵢ − EZᵢ)) ≤ exp(((hi − lo)/2)² t²/2)`. -/
theorem lintegral_ofReal_exp_normalisedSum_le {Z : ℕ → Ω → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) {lo hi : ℝ} (hZ : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Icc lo hi) {n : ℕ} (hn : 0 < n)
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t *
        ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Z i ω - ∫ ω', Z i ω' ∂P)))) ∂P ≤
      ENNReal.ofReal (Real.exp ((‖hi - lo‖ / 2) ^ 2 * t ^ 2 / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := lintegral_ofReal_exp_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_centredSum_of_mem_Icc hZm hind hZ n) (t * (Real.sqrt n)⁻¹)
  have e : ∀ ω, t * ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Z i ω - ∫ ω', Z i ω' ∂P)) =
      (t * (Real.sqrt n)⁻¹) * ∑ i ∈ Finset.range n, (Z i ω - ∫ ω', Z i ω' ∂P) := fun ω =>
    (mul_assoc _ _ _).symm
  simp_rw [e]
  refine h.trans (le_of_eq ?_)
  congr 2
  rw [NNReal.coe_nsmul, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat, nsmul_eq_mul,
    mul_pow, inv_pow, Real.sq_sqrt hn'.le]
  field_simp

/-- **Bounded i.i.d. coefficients**: if the fluctuation field is the normalised centred sum of
independent observations bounded in `[lo, hi]` at every gap point, the expected remainder decays
like `e^{−(1 − β((hi−lo)/2)²/2) β n κ}`, exponentially as soon as `β((hi − lo)/2)² < 2`. -/
theorem lintegral_enorm_annealedRemainder_le_of_bounded (S : Set Y) (hS : MeasurableSet S)
    (a g φ : Y → ℝ) (hφ : Measurable φ) (ξ : Ω → Y → ℝ) (hξ : Measurable (Function.uncurry ξ))
    {Z : ℕ → Ω → Y → ℝ} {lo hi : ℝ} {n : ℕ} (hn : 0 < n)
    (hZm : ∀ i y, Measurable fun ω => Z i ω y) (hind : ∀ y ∈ S, iIndepFun (fun i ω => Z i ω y) P)
    (hZ : ∀ i, ∀ y ∈ S, ∀ᵐ ω ∂P, Z i ω y ∈ Icc lo hi)
    (hξdef : ∀ ω, ∀ y ∈ S, ξ ω y =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Z i ω y - ∫ ω', Z i ω' y ∂P))
    {β κ : ℝ} (hβ : 0 ≤ β) (hc : (‖hi - lo‖ / 2) ^ 2 * β ≤ 2) (hbound : ∀ y ∈ S, |a y| ≤ g y)
    (hgap : ∀ y ∈ S, κ ≤ φ y ^ 2) (hg : IntegrableOn g S μ) :
    ∫⁻ ω, ‖annealedRemainder μ S a φ ξ β n ω‖ₑ ∂P ≤
      ENNReal.ofReal (Real.exp (-((1 - (‖hi - lo‖ / 2) ^ 2 * β / 2) * β * n * κ)) *
        ∫ y in S, g y ∂μ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine lintegral_enorm_annealedRemainder_le S hS a g φ hφ ξ hξ hβ hn'.le (by linarith) hbound
    hgap hg fun y hy => ?_
  have hpt : ∀ ω, Real.exp (β * Real.sqrt n * φ y * ξ ω y) = Real.exp ((β * Real.sqrt n * φ y) *
      ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Z i ω y - ∫ ω', Z i ω' y ∂P))) := fun ω => by
    rw [hξdef ω y hy]
  simp_rw [hpt]
  refine (lintegral_ofReal_exp_normalisedSum_le (fun i => hZm i y) (hind y hy)
    (fun i => hZ i y hy) hn (β * Real.sqrt n * φ y)).trans (le_of_eq ?_)
  congr 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hn'.le]
  ring

end Grammar
