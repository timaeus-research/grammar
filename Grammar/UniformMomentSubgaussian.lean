import Grammar.CompactBaseQuantise
import Grammar.AnnealedRemainder
import Grammar.BilocalGaussian

/-!
# Uniform `p`-th moments of the leading compact-base coefficient from pointwise exponential moments

Let `X : Ω → K → ℝ` be a jointly measurable random field on a finite measure space `(K, ρ)`, and
suppose only the **pointwise** sub-Gaussian bound `E e^{tX(x)} ≤ e^{ct²/2}` (`t ≥ 0`). Then for
`p ≥ 1` with `pβc < 2`,

`E[D_ρ(X)^p] ≤ [ρ(K) Γ(λ) (β(1 − pβc/2))^{−λ}]^p`,   `D_ρ(X) = ∫_K S_λ(X(x)) dρ(x)`

(`lintegral_compactD_rpow_le_of_subgaussian`). The proof writes `S_λ(a)` as the integral of
`e^{−(β−α)t + βa√t}` against the Gamma weight `t^{λ−1}e^{−αt}dt` with `α = β(1 − pβc/2)`
(`ofReal_fluctuation_eq_lintegral_gammaWeight`), so that `D_ρ(X)` is one integral over the finite
measure `ρ ⊗ γ_{λ,α}` of total mass `B = ρ(K)Γ(λ)α^{−λ}`; Hölder gives `D^p ≤ B^{p−1}∫ e^p`, and
Tonelli with the exponential-moment bound at `t' = pβ√t` makes the inner expectation exactly `1`
because `p(β − α) = p²β²c/2`. No Gaussian field, no supremum tail, no independence across base
points is used.

Consequences: the **empirical normalised sum** `ξ_n(x) = n^{−1/2}∑_{i<n}(Z_i(x) − E Z_i(x))` of
bounded independent observations satisfies the pointwise bound with `c = (‖hi − lo‖/2)²` (Hoeffding,
CXXXIX), so `E[D_ρ(ξ_n)^p] ≤ B^p` **uniformly in `n`**
(`lintegral_compactD_rpow_empirical_le`); for a random continuous function `G` with measurable
evaluations, `(ω,x) ↦ G ω x` is jointly measurable (`measurable_uncurry_eval`), `ω ↦ D_ρ(G ω)` is
measurable (`measurable_compactD_comp`), and `D_ρ(G)^p` is integrable with the same bound
(`integrable_compactD_rpow_of_subgaussian`). Finally, a pointwise domination
`|Y_n| ≤ K₀ D_ρ(ξ_n)` transfers the uniform `p`-th moment to `Y_n` (`moment_bound_of_dominated`) —
this is the hypothesis form used by `tendsto_integral_scaled_assembly`, and it is the hypothesis
that still has to be supplied for the actual finite-`n` core (the Taylor-tree asymptotics do not
provide a finite-`n` domination).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Grammar

/-! ### The Gamma weight -/

/-- The Gamma weight `t^{λ−1}e^{−αt} dt` on `(0,∞)`. -/
noncomputable def gammaWeight (lam α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (t ^ (lam - 1) * Real.exp (-α * t))

theorem measurable_gammaDensity (lam α : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (t ^ (lam - 1) * Real.exp (-α * t)) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem gammaWeight_univ {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    gammaWeight lam α univ = ENNReal.ofReal (Real.Gamma lam * α ^ (-lam)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (lam - 1) * Real.exp (-α * t)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := lam - 1) (b := α)
      (by linarith) one_pos hα
    simpa only [Real.rpow_one] using this
  have hval : ∫ t in Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-α * t) =
      Real.Gamma lam * α ^ (-lam) := by
    have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := lam - 1) (b := α) one_pos
      (by linarith) hα
    simp only [Real.rpow_one, div_one] at this
    rw [this, show lam - 1 + 1 = lam by ring]
    ring
  rw [gammaWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le), hval]

theorem gammaWeight_Iic (lam α : ℝ) : gammaWeight lam α (Iic 0) = 0 := by
  rw [gammaWeight, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

/-- `S_λ(a)` as a `gammaWeight`-integral: `S_λ(a) = ∫ e^{−(β−α)t + βa√t} γ_{λ,α}(dt)`. -/
theorem ofReal_fluctuation_eq_lintegral_gammaWeight {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (α a : ℝ) :
    ENNReal.ofReal (fluctuation β lam a) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(β - α) * t + β * a * Real.sqrt t)) ∂gammaWeight lam α := by
  have hg : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(β - α) * t + β * a * Real.sqrt t)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [ofReal_fluctuation_eq_lintegral β lam hβ hlam a, gammaWeight,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaDensity lam α) hg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [Pi.mul_apply, radialKernel]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)]
  congr 1
  rw [mul_assoc (t ^ (lam - 1)), ← Real.exp_add, mul_assoc (t ^ (lam - 1)), ← Real.exp_add]
  congr 2
  ring

/-! ### Joint measurability of random continuous functions -/

section Joint

variable {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [TopologicalSpace.MetrizableSpace K]
  [MeasurableSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]

/-- **Carathéodory**: a random continuous function with measurable evaluations is jointly
measurable. -/
theorem measurable_uncurry_eval (G : Ω → C(K, ℝ)) (hG : ∀ x, Measurable fun ω => G ω x) :
    Measurable fun p : Ω × K => G p.1 p.2 := by
  have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun x ω => G ω x) (fun ω => (G ω).continuous) (fun x => (hG x).stronglyMeasurable)
  exact h.measurable.comp measurable_swap

end Joint

/-! ### The uniform moment bound -/

section Main

variable {Ω K : Type*} [MeasurableSpace Ω] [MeasurableSpace K] (P : Measure Ω)
  [IsProbabilityMeasure P] (ρ : Measure K) [IsFiniteMeasure ρ]

/-- The sub-Gaussian moment bound `B = ρ(K) Γ(λ) (β(1 − pβc/2))^{−λ}`. -/
noncomputable def subgaussianBound (β lam c p M : ℝ) : ℝ :=
  M * (Real.Gamma lam * (β * (1 - p * β * c / 2)) ^ (-lam))

/-- **Uniform `p`-th moment of the leading coefficient from pointwise exponential moments**:
if `E e^{tX(x)} ≤ e^{ct²/2}` for `t ≥ 0` and every `x`, then for `p ≥ 1`, `pβc < 2`,
`E[(∫ S_λ(X(x)) dρ)^p] ≤ [ρ(K)Γ(λ)(β(1 − pβc/2))^{−λ}]^p`. -/
theorem lintegral_compactD_rpow_le_of_subgaussian {β lam c p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hp : 1 ≤ p) (h : p * β * c < 2) (hρ : ρ ≠ 0) (X : Ω → K → ℝ)
    (hX : Measurable (Function.uncurry X))
    (hmgf : ∀ x, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω x)) ∂P ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2))) :
    ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (fluctuation β lam (X ω x)) ∂ρ) ^ p ∂P ≤
      ENNReal.ofReal (subgaussianBound β lam c p (ρ.real univ)) ^ p := by
  set α : ℝ := β * (1 - p * β * c / 2) with hα
  have hα0 : 0 < α := mul_pos hβ (by linarith)
  set w : Measure ℝ := gammaWeight lam α with hw
  have hw_univ : w univ = ENNReal.ofReal (Real.Gamma lam * α ^ (-lam)) :=
    gammaWeight_univ hlam hα0
  have hwF : IsFiniteMeasure w := ⟨by rw [hw_univ]; exact ENNReal.ofReal_lt_top⟩
  set μ' : Measure (K × ℝ) := ρ.prod w with hμ'
  have hμ'_univ : μ' univ = ENNReal.ofReal (subgaussianBound β lam c p (ρ.real univ)) := by
    rw [hμ', ← Set.univ_prod_univ, Measure.prod_prod, hw_univ, subgaussianBound,
      ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hμ'_ne_top : μ' univ ≠ ⊤ := by rw [hμ'_univ]; exact ENNReal.ofReal_ne_top
  have hμ'_ne_zero : μ' univ ≠ 0 := by
    rw [hμ', ← Set.univ_prod_univ, Measure.prod_prod, hw_univ]
    refine mul_ne_zero (Measure.measure_univ_ne_zero.2 hρ) ?_
    exact (ENNReal.ofReal_pos.2 (mul_pos (Real.Gamma_pos_of_pos hlam)
      (Real.rpow_pos_of_pos hα0 _))).ne'
  -- the exponential integrand
  set e : Ω → K × ℝ → ℝ≥0∞ := fun ω z =>
    ENNReal.ofReal (Real.exp (-(β - α) * z.2 + β * X ω z.1 * Real.sqrt z.2)) with he
  have hXm : Measurable fun q : Ω × (K × ℝ) => X q.1 q.2.1 :=
    hX.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have he_meas : Measurable (Function.uncurry e) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_const.mul (measurable_snd.comp measurable_snd)).add
      ((measurable_const.mul hXm).mul
        (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_snd)))
  have he_meas_ω : ∀ ω, Measurable (e ω) := fun ω =>
    he_meas.comp (measurable_const.prodMk measurable_id)
  have hD : ∀ ω, ∫⁻ x, ENNReal.ofReal (fluctuation β lam (X ω x)) ∂ρ = ∫⁻ z, e ω z ∂μ' := by
    intro ω
    rw [hμ', lintegral_prod _ (he_meas_ω ω).aemeasurable]
    exact lintegral_congr fun x => ofReal_fluctuation_eq_lintegral_gammaWeight hβ hlam α (X ω x)
  simp_rw [hD]
  -- Hölder pointwise in `ω`
  have hHolder : ∀ ω, (∫⁻ z, e ω z ∂μ') ^ p ≤ (∫⁻ z, e ω z ^ p ∂μ') * (μ' univ) ^ (p - 1) := by
    intro ω
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1]
      simp
    · have hpq := Real.HolderConjugate.conjExponent hp1
      set q : ℝ := Real.conjExponent p with hq
      have hp0 : p ≠ 0 := by linarith
      have hqp : 1 / q * p = p - 1 := by
        have h1 := hpq.one_div_add_one_div
        rw [div_one] at h1
        have : 1 / q = 1 - 1 / p := by linarith
        rw [this, sub_mul, one_mul, one_div_mul_cancel hp0]
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ' hpq (he_meas_ω ω).aemeasurable
        (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hH
      calc (∫⁻ z, e ω z ∂μ') ^ p
          ≤ ((∫⁻ z, e ω z ^ p ∂μ') ^ (1 / p) * (μ' univ) ^ (1 / q)) ^ p :=
            ENNReal.rpow_le_rpow hH (by linarith)
        _ = (∫⁻ z, e ω z ^ p ∂μ') * (μ' univ) ^ (p - 1) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul,
              ← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one, hqp]
  -- the inner expectation is at most `1` on the support of the weight
  have hz : ∀ z : K × ℝ, 0 < z.2 → ∫⁻ ω, e ω z ^ p ∂P ≤ 1 := by
    rintro ⟨x, t⟩ ht
    simp only at ht
    have hsq := Real.sq_sqrt ht.le
    have hrew : ∀ ω, e ω (x, t) ^ p = ENNReal.ofReal (Real.exp (-(p * (β - α)) * t)) *
        ENNReal.ofReal (Real.exp ((p * β * Real.sqrt t) * X ω x)) := by
      intro ω
      simp only [he]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith : (0 : ℝ) ≤ p),
        ← Real.exp_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    simp_rw [hrew]
    have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (p * β * Real.sqrt t * X ω x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hX.comp (measurable_id.prodMk measurable_const))))
    rw [lintegral_const_mul _ hm]
    calc ENNReal.ofReal (Real.exp (-(p * (β - α)) * t)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((p * β * Real.sqrt t) * X ω x)) ∂P
        ≤ ENNReal.ofReal (Real.exp (-(p * (β - α)) * t)) *
          ENNReal.ofReal (Real.exp (c * (p * β * Real.sqrt t) ^ 2 / 2)) :=
          mul_le_mul' le_rfl (hmgf x _ (by positivity))
      _ = ENNReal.ofReal (Real.exp (-(p * (β - α)) * t + c * (p * β * Real.sqrt t) ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      _ = 1 := by
          rw [show -(p * (β - α)) * t + c * (p * β * Real.sqrt t) ^ 2 / 2 = 0 by
            rw [mul_pow, mul_pow, hsq, hα]; ring, Real.exp_zero, ENNReal.ofReal_one]
  have hae : ∀ᵐ z ∂μ', 0 < z.2 := by
    rw [ae_iff]
    have : {z : K × ℝ | ¬ 0 < z.2} = univ ×ˢ Iic 0 := by
      ext z
      simp [not_lt]
    rw [this, hμ', Measure.prod_prod, hw, gammaWeight_Iic, mul_zero]
  have hswap : ∫⁻ ω, ∫⁻ z, e ω z ^ p ∂μ' ∂P = ∫⁻ z, ∫⁻ ω, e ω z ^ p ∂P ∂μ' :=
    lintegral_lintegral_swap ((he_meas.pow_const p).aemeasurable)
  calc ∫⁻ ω, (∫⁻ z, e ω z ∂μ') ^ p ∂P
      ≤ ∫⁻ ω, (∫⁻ z, e ω z ^ p ∂μ') * (μ' univ) ^ (p - 1) ∂P := lintegral_mono hHolder
    _ = (∫⁻ ω, ∫⁻ z, e ω z ^ p ∂μ' ∂P) * (μ' univ) ^ (p - 1) :=
        lintegral_mul_const _ (he_meas.pow_const p).lintegral_prod_right'
    _ = (∫⁻ z, ∫⁻ ω, e ω z ^ p ∂P ∂μ') * (μ' univ) ^ (p - 1) := by rw [hswap]
    _ ≤ (∫⁻ _z, (1 : ℝ≥0∞) ∂μ') * (μ' univ) ^ (p - 1) :=
        mul_le_mul' (lintegral_mono_ae (hae.mono fun z hz' => hz z hz')) le_rfl
    _ = (μ' univ) ^ p := by
        rw [lintegral_const, one_mul]
        have : μ' univ * μ' univ ^ (p - 1) = μ' univ ^ (1 + (p - 1)) := by
          rw [ENNReal.rpow_add _ _ hμ'_ne_zero hμ'_ne_top, ENNReal.rpow_one]
        rw [this]
        congr 1
        ring
    _ = ENNReal.ofReal (subgaussianBound β lam c p (ρ.real univ)) ^ p := by rw [hμ'_univ]

/-! ### The empirical corollary (bounded independent observations) -/

/-- The normalised empirical sum `ξ_n(x) = n^{−1/2}∑_{i<n}(Z_i(x) − E Z_i(x))`. -/
noncomputable def empiricalField (Z : ℕ → Ω → K → ℝ) (n : ℕ) (ω : Ω) (x : K) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Z i ω x - ∫ ω', Z i ω' x ∂P)

theorem measurable_uncurry_empiricalField {Z : ℕ → Ω → K → ℝ}
    (hZ : ∀ i, Measurable (Function.uncurry (Z i))) (n : ℕ) :
    Measurable (Function.uncurry (empiricalField P Z n)) := by
  unfold empiricalField Function.uncurry
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine (hZ i).sub ?_
  have hm : StronglyMeasurable fun x : K => ∫ ω', Z i ω' x ∂P :=
    (hZ i).stronglyMeasurable.integral_prod_left'
  exact hm.measurable.comp measurable_snd

/-- **Uniform-in-`n` moment bound for the empirical leading coefficient**: bounded independent
observations with values in `[lo, hi]` give, with `c = (‖hi − lo‖/2)²`,
`E[(∫ S_λ(ξ_n(x)) dρ)^p] ≤ [ρ(K)Γ(λ)(β(1 − pβc/2))^{−λ}]^p` for every `n ≥ 1`. -/
theorem lintegral_compactD_rpow_empirical_le {β lam p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hp : 1 ≤ p) (hρ : ρ ≠ 0) {Z : ℕ → Ω → K → ℝ} (hZ : ∀ i, Measurable (Function.uncurry (Z i)))
    (hind : ∀ x, iIndepFun (fun i ω => Z i ω x) P) {lo hi : ℝ}
    (hbdd : ∀ i x, ∀ᵐ ω ∂P, Z i ω x ∈ Icc lo hi)
    (h : p * β * (‖hi - lo‖ / 2) ^ 2 < 2) {n : ℕ} (hn : 0 < n) :
    ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (fluctuation β lam (empiricalField P Z n ω x)) ∂ρ) ^ p ∂P ≤
      ENNReal.ofReal (subgaussianBound β lam ((‖hi - lo‖ / 2) ^ 2) p (ρ.real univ)) ^ p := by
  refine lintegral_compactD_rpow_le_of_subgaussian P ρ hβ hlam hp h hρ _
    (measurable_uncurry_empiricalField P hZ n) fun x t _ => ?_
  exact lintegral_ofReal_exp_normalisedSum_le
    (fun i => (hZ i).comp (measurable_id.prodMk measurable_const)) (hind x) (hbdd · x) hn t

/-! ### Real-valued corollaries for random continuous functions -/

variable {K' : Type*} [MetricSpace K'] [CompactSpace K'] [MeasurableSpace K'] [BorelSpace K']
  (ρ' : Measure K') [IsFiniteMeasure ρ']

theorem ofReal_compactD {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (g : C(K', ℝ)) :
    ENNReal.ofReal (compactD β lam ρ' g) = ∫⁻ x, ENNReal.ofReal (fluctuation β lam (g x)) ∂ρ' :=
  ofReal_integral_eq_lintegral_ofReal (integrable_fluctuation_comp ρ' hβ hlam g)
    (Filter.Eventually.of_forall fun _ => (fluctuation_pos β lam _ hβ hlam).le)

theorem measurable_compactD_comp {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (G : Ω → C(K', ℝ))
    (hG : Measurable fun q : Ω × K' => G q.1 q.2) :
    Measurable fun ω => compactD β lam ρ' (G ω) := by
  have h1 : Measurable fun ω => ∫⁻ x, ENNReal.ofReal (fluctuation β lam (G ω x)) ∂ρ' :=
    (ENNReal.measurable_ofReal.comp ((continuous_fluctuation β lam hβ hlam).measurable.comp
      hG)).lintegral_prod_right'
  have : (fun ω => compactD β lam ρ' (G ω)) = fun ω =>
      (∫⁻ x, ENNReal.ofReal (fluctuation β lam (G ω x)) ∂ρ').toReal := by
    funext ω
    rw [← ofReal_compactD ρ' hβ hlam, ENNReal.toReal_ofReal]
    exact integral_nonneg fun x => (fluctuation_pos β lam _ hβ hlam).le
  rw [this]
  exact h1.ennreal_toReal

/-- **Integrable `p`-th moment of `D_ρ(G)` with the explicit bound**, for a random continuous
function with the pointwise exponential-moment bound. -/
theorem integrable_compactD_rpow_of_subgaussian {β lam c p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (hp : 1 ≤ p) (h : p * β * c < 2) (hρ : ρ' ≠ 0) (G : Ω → C(K', ℝ))
    (hG : Measurable fun q : Ω × K' => G q.1 q.2)
    (hmgf : ∀ x, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * G ω x)) ∂P ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2))) :
    Integrable (fun ω => compactD β lam ρ' (G ω) ^ p) P ∧
      ∫ ω, compactD β lam ρ' (G ω) ^ p ∂P ≤ subgaussianBound β lam c p (ρ'.real univ) ^ p := by
  have hbound := lintegral_compactD_rpow_le_of_subgaussian P ρ' hβ hlam hp h hρ
    (fun ω x => G ω x) hG hmgf
  have hB0 : 0 ≤ subgaussianBound β lam c p (ρ'.real univ) := by
    unfold subgaussianBound
    have : 0 < 1 - p * β * c / 2 := by linarith
    positivity
  have hD0 : ∀ ω, 0 ≤ compactD β lam ρ' (G ω) := fun ω =>
    integral_nonneg fun x => (fluctuation_pos β lam _ hβ hlam).le
  have hrew : ∀ ω, (∫⁻ x, ENNReal.ofReal (fluctuation β lam (G ω x)) ∂ρ') ^ p =
      ENNReal.ofReal (compactD β lam ρ' (G ω) ^ p) := fun ω => by
    rw [← ofReal_compactD ρ' hβ hlam, ENNReal.ofReal_rpow_of_nonneg (hD0 ω) (by linarith)]
  simp_rw [hrew] at hbound
  rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by linarith)] at hbound
  have hmeas : Measurable fun ω => compactD β lam ρ' (G ω) ^ p :=
    (measurable_compactD_comp ρ' hβ hlam G hG).pow_const p
  have hint : Integrable (fun ω => compactD β lam ρ' (G ω) ^ p) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (hD0 ω) _)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hD0 ω) _)
  rw [← this] at hbound
  exact ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hB0 _) |>.1 hbound

/-! ### Transfer of the uniform moment through a pointwise domination -/

omit [IsProbabilityMeasure P] in
/-- **Domination wrapper**: if `|Y_n| ≤ K₀ D_n` pointwise and `E[D_n^p] ≤ B^p`, then
`E|Y_n|^p ≤ (K₀ B)^p` — the moment hypothesis of `tendsto_integral_scaled_assembly`. -/
theorem moment_bound_of_dominated {Y D : ℕ → Ω → ℝ} {K₀ B p : ℝ} (hK : 0 ≤ K₀) (hB : 0 ≤ B)
    (hp : 0 < p) (hYm : ∀ n, AEStronglyMeasurable (Y n) P) (hD0 : ∀ n ω, 0 ≤ D n ω)
    (hdom : ∀ n ω, |Y n ω| ≤ K₀ * D n ω) (hDint : ∀ n, Integrable (fun ω => D n ω ^ p) P)
    (hDb : ∀ n, ∫ ω, D n ω ^ p ∂P ≤ B ^ p) :
    (∀ n, Integrable (fun ω => |Y n ω| ^ p) P) ∧ ∀ n, ∫ ω, |Y n ω| ^ p ∂P ≤ (K₀ * B) ^ p := by
  have hpt : ∀ n ω, |Y n ω| ^ p ≤ K₀ ^ p * D n ω ^ p := fun n ω => by
    rw [← Real.mul_rpow hK (hD0 n ω)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hdom n ω) hp.le
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => |Y n ω| ^ p) P := fun n =>
    (((hYm n).aemeasurable.norm).pow_const p).aestronglyMeasurable
  have hint : ∀ n, Integrable (fun ω => |Y n ω| ^ p) P := fun n =>
    ((hDint n).const_mul (K₀ ^ p)).mono' (hmeas n) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hpt n ω)
  refine ⟨hint, fun n => ?_⟩
  calc ∫ ω, |Y n ω| ^ p ∂P ≤ ∫ ω, K₀ ^ p * D n ω ^ p ∂P :=
        integral_mono (hint n) ((hDint n).const_mul _) (hpt n)
    _ = K₀ ^ p * ∫ ω, D n ω ^ p ∂P := integral_const_mul _ _
    _ ≤ K₀ ^ p * B ^ p := mul_le_mul_of_nonneg_left (hDb n) (Real.rpow_nonneg hK _)
    _ = (K₀ * B) ^ p := (Real.mul_rpow hK hB).symm

end Main

end Grammar
