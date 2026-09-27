/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeAveragedPosterior

/-!
# The Leray density of `u₁² e^{−|u|²/2}` on the cone

The weighted Leray density of the cone under the Gaussian prior with the observable `u₁²` is
`π² e^{−|v|}(1 + v + |v|)` (examples_slop §3, cor. cone_gaussian): the pushforward of
`u₁² e^{−|u|²/2} du` along `q` is `π² e^{−|v|}(1 + v + |v|) dv` (★★★ `map_coneQ_gaussian_sq`), so

  `∫_{ℝ⁴} g(q(u)) u₁² e^{−|u|²/2} du = ∫_ℝ g(v) π² e^{−|v|}(1 + v + |v|) dv`

for every measurable `g` (★★ `integral_cone_gaussian_sq`), and the numerator `coneNumSq` of
`ConeAveragedPosterior` IS the four-dimensional frozen numerator `Z_N[u₁²; a]`
(★★ `coneNumSq_eq`).  The route is the bipolar reduction of `ConeGaussian` with the weight
`u₁² + u₂² = p`: the swap `u₁ ↔ u₂` preserves `q`, `e^{−|u|²/2}` and Lebesgue measure, so
`∫ u₁² (…) = ½ ∫ (u₁² + u₂²) (…)` (`lintegral_cone_sq_eq_half`), the radial factor `p` rides
along in the polar reduction (`lintegral_cone_gauss_weight`), and the weighted quadrant integral
`∫₀^∞∫₀^∞ p G((p − t)/2) e^{−(p+t)/2} = 2 ∫ G(v)(1 + v + |v|) e^{−|v|}` follows from
`∫_c^∞ p e^{−p} dp = (c + 1) e^{−c}` at `c = max(0, 2v)` (`lintegral_quadrant_weight`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology ENNReal

namespace Grammar

/-! ### The swap `u₁ ↔ u₂` -/

/-- The swap of the first pair. -/
def swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) := (u.1.swap, u.2)

theorem coneQ_swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : coneQ (swapFirst u) = coneQ u := by
  unfold coneQ swapFirst; simp only [Prod.swap]; ring

theorem gaussW_swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : gaussW (swapFirst u) = gaussW u := by
  unfold gaussW swapFirst; simp only [Prod.swap]; ring_nf

theorem measurePreserving_swapFirst : MeasurePreserving swapFirst volume volume := by
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]; exact ⟨measurable_swap, Measure.prod_swap⟩
  have h : MeasurePreserving
      (Prod.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) (id : ℝ × ℝ → ℝ × ℝ)) volume volume := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ)]; exact hswap.prod (MeasurePreserving.id _)
  exact h

/-- `∫ u₁² G(q) W = ∫ u₂² G(q) W` (lower integrals). -/
theorem lintegral_cone_sq_swap (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) := by
  have hf : Measurable fun u : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) :=
    (measurable_snd.comp measurable_fst |>.pow_const 2 |>.ennreal_ofReal).mul
      ((hG.comp measurable_coneQ).mul measurable_gaussW.ennreal_ofReal)
  rw [← measurePreserving_swapFirst.lintegral_comp hf]
  congr 1
  funext u
  rw [coneQ_swapFirst, gaussW_swapFirst]
  rfl

/-- `2 ∫ u₁² G(q) W = ∫ (u₁² + u₂²) G(q) W`. -/
theorem lintegral_cone_sq_eq_half (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    2 * ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2 + u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) := by
  have hf : Measurable fun u : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (u.1.1 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) :=
    (measurable_fst.comp measurable_fst |>.pow_const 2 |>.ennreal_ofReal).mul
      ((hG.comp measurable_coneQ).mul measurable_gaussW.ennreal_ofReal)
  rw [two_mul]
  nth_rewrite 2 [lintegral_cone_sq_swap G hG]
  rw [← lintegral_add_left hf]
  congr 1
  funext u
  rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-! ### The bipolar reduction with the radial weight -/

/-- The bipolar reduction with the weight `u₁² + u₂² = p`:
`∫ (u₁² + u₂²) G(q) e^{−|u|²/2} = π² ∫₀^∞ p ∫₀^∞ G((p − t)/2) e^{−(p+t)/2} dt dp`. -/
theorem lintegral_cone_gauss_weight (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2 + u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ENNReal.ofReal Real.pi * (ENNReal.ofReal Real.pi *
        ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2))) := by
  set F : ℝ → ℝ → ℝ≥0∞ := fun p t => G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2))
    with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    simp only [hFdef]
    fun_prop
  have hmeas : Measurable fun u : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (u.1.1 ^ 2 + u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) :=
    (((measurable_fst.comp measurable_fst).pow_const 2).add
      ((measurable_snd.comp measurable_fst).pow_const 2)).ennreal_ofReal.mul
      ((hG.comp measurable_coneQ).mul measurable_gaussW.ennreal_ofReal)
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ z₁ : ℝ × ℝ, ∫⁻ z₂ : ℝ × ℝ, ENNReal.ofReal (z₁.1 ^ 2 + z₁.2 ^ 2) *
      (G (coneQ (z₁, z₂)) * ENNReal.ofReal (gaussW (z₁, z₂))) =
      ENNReal.ofReal (z₁.1 ^ 2 + z₁.2 ^ 2) *
        (ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), F (z₁.1 ^ 2 + z₁.2 ^ 2) t) := by
    intro z₁
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have := lintegral_radial_sq (fun t => F (z₁.1 ^ 2 + z₁.2 ^ 2) t)
      (hFmeas.comp (measurable_const.prodMk measurable_id))
    rw [← this]
    rfl
  simp_rw [hinner]
  have hΨ : Measurable fun p : ℝ =>
      ENNReal.ofReal p * (ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), F p t) :=
    measurable_id.ennreal_ofReal.mul (measurable_const.mul
      (hFmeas.lintegral_prod_right' (ν := volume.restrict (Ioi 0))))
  refine (lintegral_radial_sq (fun p => ENNReal.ofReal p *
    (ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), F p t)) hΨ).trans ?_
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext p
  exact mul_left_comm _ _ _

/-! ### The half-line integral `∫_c^∞ p e^{−p} dp = (c + 1) e^{−c}` -/

theorem integral_mul_exp_neg_Ioi {c : ℝ} (hc : 0 ≤ c) :
    ∫ p in Ioi c, p * Real.exp (-p) = (c + 1) * Real.exp (-c) := by
  have hderiv : ∀ p ∈ Ioi c,
      HasDerivAt (fun p : ℝ => -((p + 1) * Real.exp (-p))) (p * Real.exp (-p)) p := by
    intro p _
    have h1 : HasDerivAt (fun p : ℝ => p + 1) 1 p := (hasDerivAt_id' p).add_const 1
    have h2 : HasDerivAt (fun p : ℝ => Real.exp (-p)) (Real.exp (-p) * -1) p :=
      (hasDerivAt_neg p).exp
    exact ((h1.mul h2).neg).congr_deriv (by ring)
  have hint : IntegrableOn (fun p : ℝ => p * Real.exp (-p)) (Ioi c) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) (by norm_num)
    simp only [Real.rpow_one] at this
    exact this.mono_set (Ioi_subset_Ioi hc)
  have htend : Tendsto (fun p : ℝ => -((p + 1) * Real.exp (-p))) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simp only [pow_one] at h1
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
    have := (h1.add h2).neg
    simp only [add_zero, neg_zero] at this
    refine this.congr fun p => ?_
    ring
  have hcont : ContinuousWithinAt (fun p : ℝ => -((p + 1) * Real.exp (-p))) (Ici c) c :=
    (by fun_prop : Continuous fun p : ℝ => -((p + 1) * Real.exp (-p))).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  ring

theorem lintegral_mul_exp_neg_Ioi {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ p in Ioi c, ENNReal.ofReal (p * Real.exp (-p)) =
      ENNReal.ofReal ((c + 1) * Real.exp (-c)) := by
  have hint : IntegrableOn (fun p : ℝ => p * Real.exp (-p)) (Ioi c) := by
    have := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) (by norm_num)
    simp only [Real.rpow_one] at this
    exact this.mono_set (Ioi_subset_Ioi hc)
  rw [← ofReal_integral_eq_lintegral_ofReal hint ?_, integral_mul_exp_neg_Ioi hc]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun p hp => ?_)
  have : 0 < p := lt_of_le_of_lt hc hp
  simp only [Pi.zero_apply]
  positivity

/-! ### The weighted quadrant integral -/

/-- ★★ **The weighted quadrant integral is the weighted Leray integral**:
`∫₀^∞∫₀^∞ p G((p − t)/2) e^{−(p+t)/2} dt dp = 2 ∫_ℝ G(v) e^{−|v|}(1 + v + |v|) dv`. -/
theorem lintegral_quadrant_weight (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)) =
      2 * ∫⁻ v, G v * ENNReal.ofReal (Real.exp (-|v|) * (1 + v + |v|)) := by
  simp_rw [lintegral_inner_subst]
  have e1 : ∀ p ∈ Ioi (0 : ℝ), ENNReal.ofReal p *
      (2 * ∫⁻ v in Iio (p / 2), G v * ENNReal.ofReal (Real.exp (v - p))) =
      2 * ∫⁻ v in Iio (p / 2), G v * ENNReal.ofReal (p * Real.exp (v - p)) := by
    intro p hp
    have hp' : 0 < p := hp
    rw [mul_left_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
    funext v
    rw [ENNReal.ofReal_mul hp'.le]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi e1, lintegral_const_mul' _ _ (by simp)]
  congr 1
  set H : ℝ → ℝ → ℝ≥0∞ := fun p v =>
    ({q : ℝ × ℝ | 0 < q.1 ∧ q.2 < q.1 / 2}).indicator (fun _ => (1 : ℝ≥0∞)) (p, v) *
      (G v * ENNReal.ofReal (p * Real.exp (v - p))) with hHdef
  have hS : MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.2 < q.1 / 2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hHmeas : Measurable (Function.uncurry H) := by
    simp only [hHdef]
    refine (measurable_const.indicator hS).mul ?_
    fun_prop
  have h1 : ∀ p ∈ Ioi (0 : ℝ), ∫⁻ v in Iio (p / 2), G v * ENNReal.ofReal (p * Real.exp (v - p)) =
      ∫⁻ v, H p v := by
    intro p hp
    have hp' : 0 < p := hp
    rw [← lintegral_indicator measurableSet_Iio]
    congr 1
    funext v
    simp only [hHdef, indicator, mem_ofPred_eq, mem_Iio]
    by_cases hv : v < p / 2 <;> simp [hv, hp']
  have h2 : ∫⁻ p in Ioi (0 : ℝ), ∫⁻ v, H p v = ∫⁻ p, ∫⁻ v, H p v := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext p
    by_cases hp : 0 < p
    · simp [hp]
    · simp only [indicator, mem_Ioi, hp, if_false]
      symm
      simp [hHdef, hp]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, h2, lintegral_lintegral_swap hHmeas.aemeasurable]
  congr 1
  funext v
  have h3 : ∫⁻ p, H p v = G v * ENNReal.ofReal (Real.exp v) *
      ∫⁻ p in Ioi (max 0 (2 * v)), ENNReal.ofReal (p * Real.exp (-p)) := by
    have hind : Measurable ((Ioi (max 0 (2 * v))).indicator fun p : ℝ =>
        ENNReal.ofReal (p * Real.exp (-p))) :=
      Measurable.indicator (by fun_prop) measurableSet_Ioi
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_const_mul _ hind]
    congr 1
    funext p
    simp only [hHdef, indicator, mem_ofPred_eq, mem_Ioi, max_lt_iff]
    by_cases h : 0 < p ∧ v < p / 2
    · have h' : 0 < p ∧ 2 * v < p := ⟨h.1, by linarith [h.2]⟩
      rw [if_pos h, if_pos h', one_mul, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      rw [Real.exp_sub, Real.exp_neg]
      field_simp
    · have h' : ¬ (0 < p ∧ 2 * v < p) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      rw [if_neg h, if_neg h', zero_mul, mul_zero]
  rw [h3, lintegral_mul_exp_neg_Ioi (le_max_left _ _), mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 2
  rcases le_or_gt 0 v with hv | hv
  · rw [max_eq_right (by linarith), abs_of_nonneg hv]
    have : Real.exp v * Real.exp (-(2 * v)) = Real.exp (-v) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (2 * v + 1) * this
  · rw [max_eq_left (by linarith), abs_of_neg hv]
    simp only [neg_zero, Real.exp_zero, zero_add, mul_one, neg_neg]
    ring

/-! ### The pushforward and the Bochner form -/

/-- ★★★ **The Leray density of `u₁² e^{−|u|²/2}` is `π² e^{−|v|}(1 + v + |v|)`**: the pushforward
of `u₁² e^{−|u|²/2} du` along `q`. -/
theorem map_coneQ_gaussian_sq :
    Measure.map coneQ (volume.withDensity fun u => ENNReal.ofReal (u.1.1 ^ 2 * gaussW u)) =
      volume.withDensity fun v =>
        ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|)) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_coneQ hs, withDensity_apply _ (measurable_coneQ hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_coneQ hs),
    ← lintegral_indicator hs]
  have h1 : ∀ u, (coneQ ⁻¹' s).indicator (fun u => ENNReal.ofReal (u.1.1 ^ 2 * gaussW u)) u =
      ENNReal.ofReal (u.1.1 ^ 2) *
        (s.indicator (fun _ => (1 : ℝ≥0∞)) (coneQ u) * ENNReal.ofReal (gaussW u)) := by
    intro u
    by_cases hu : coneQ u ∈ s
    · rw [indicator_of_mem (show u ∈ coneQ ⁻¹' s from hu), indicator_of_mem hu, one_mul,
        ENNReal.ofReal_mul (sq_nonneg _)]
    · rw [indicator_of_notMem (show u ∉ coneQ ⁻¹' s from hu), indicator_of_notMem hu, zero_mul,
        mul_zero]
  simp_rw [h1]
  have key := lintegral_cone_sq_eq_half (s.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hs)
  rw [lintegral_cone_gauss_weight (s.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hs),
    lintegral_quadrant_weight (s.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hs)] at key
  have h2 : ∀ v, s.indicator (fun v =>
      ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))) v =
      ENNReal.ofReal (Real.pi ^ 2) * (s.indicator (fun _ => (1 : ℝ≥0∞)) v *
        ENNReal.ofReal (Real.exp (-|v|) * (1 + v + |v|))) := by
    intro v
    by_cases hv : v ∈ s
    · rw [indicator_of_mem hv, indicator_of_mem hv, one_mul, mul_assoc,
        ENNReal.ofReal_mul (by positivity)]
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul, mul_zero]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  refine (ENNReal.mul_right_inj h2ne h2top).1 ?_
  rw [key, ENNReal.ofReal_pow Real.pi_pos.le]
  ring

/-- ★★ **The Bochner form**: for every measurable `g`,
`∫_{ℝ⁴} g(q(u)) u₁² e^{−|u|²/2} du = ∫_ℝ g(v) π² e^{−|v|}(1 + v + |v|) dv`. -/
theorem integral_cone_gaussian_sq (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ), g (coneQ u) * (u.1.1 ^ 2 * gaussW u) =
      ∫ v, g v * (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|)) := by
  have hdm : Measurable fun u : (ℝ × ℝ) × (ℝ × ℝ) => u.1.1 ^ 2 * gaussW u :=
    ((measurable_fst.comp measurable_fst).pow_const 2).mul measurable_gaussW
  have hL : ∫ u : (ℝ × ℝ) × (ℝ × ℝ), g (coneQ u) * (u.1.1 ^ 2 * gaussW u) =
      ∫ u, g (coneQ u) ∂(volume.withDensity fun u => ENNReal.ofReal (u.1.1 ^ 2 * gaussW u)) := by
    rw [show (fun u : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (u.1.1 ^ 2 * gaussW u)) =
      fun u => ((u.1.1 ^ 2 * gaussW u).toNNReal : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hdm.real_toNNReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have h0 : 0 ≤ u.1.1 ^ 2 * gaussW u := mul_nonneg (sq_nonneg _) (gaussW_pos u).le
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ h0]
    ring
  have hd : Measurable fun v : ℝ => Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|) := by fun_prop
  have hR : ∫ v, g v * (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|)) =
      ∫ v, g v ∂(volume.withDensity fun v =>
        ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))) := by
    rw [show (fun v : ℝ => ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))) =
      fun v => ((Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|)).toNNReal : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hd.real_toNNReal]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have h0 : 0 ≤ Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|) := by
      have := neg_abs_le v
      have : 0 ≤ 1 + v + |v| := by linarith
      positivity
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ h0]
    ring
  rw [hL, hR, ← map_coneQ_gaussian_sq,
    integral_map measurable_coneQ.aemeasurable hg.aestronglyMeasurable]

/-- ★★ **The numerator of the cone posterior is the four-dimensional frozen numerator**:
`coneNumSq N a = ∫_{ℝ⁴} u₁² e^{−N q²/2 + √N q a} e^{−|u|²/2} du`. -/
theorem coneNumSq_eq (N a : ℝ) :
    coneNumSq N a = ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * (u.1.1 ^ 2 * gaussW u) := by
  rw [integral_cone_gaussian_sq (fun v => Real.exp (-N * v ^ 2 / 2 + Real.sqrt N * v * a))
    (by fun_prop)]
  rfl

/-- ★★★ **The averaged first correction, four-dimensional on both sides**: with
`Z_N[f; a] = ∫_{ℝ⁴} f(u) e^{−N q²/2 + √N q a} e^{−|u|²/2} du` and the sample field `a ∼ N(0,1)`,
`√N (E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½) → 1/√π`. -/
theorem cone_averaged_correction_fourDim :
    Tendsto (fun N : ℝ => Real.sqrt N *
      ((∫ a, (∫ u : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * (u.1.1 ^ 2 * gaussW u)) /
        (∫ u : (ℝ × ℝ) × (ℝ × ℝ),
          Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * gaussW u) *
        gaussDensity a) - 1 / 2)) atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  simp_rw [← coneNumSq_eq, ← coneDen_eq]
  exact cone_averaged_correction

end Grammar
