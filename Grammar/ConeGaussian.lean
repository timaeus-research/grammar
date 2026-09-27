/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeExample

/-!
# The Leray density of the cone under the Gaussian prior

For the quadratic form `q(u) = ((u₁² + u₂²) − (u₃² + u₄²))/2` of signature `(2, 2)` on `ℝ⁴` and the
Gaussian weight `e^{−|u|²/2}`, the pushforward of the weighted Lebesgue measure along `q` has the
density `2π² e^{−|v|}` (★★★ `map_coneQ_gaussian`): the Leray density of the cone is `2π² e^{−|v|}`,
with the corner at `v = 0` of slope `∓2π²` that carries the vertex term of the expansion
(examples_slop §2).  The proof is bipolar coordinates on `ℝ² × ℝ²` (`lintegral_radial_sq`:
`∫ Ψ(|z|²) dz = π ∫_0^∞ Ψ`), reducing the four-dimensional integral to the quadrant integral
`π² ∫_0^∞∫_0^∞ G((p − t)/2) e^{−(p+t)/2}` (`lintegral_cone_gauss`), and the substitution
`t = p − 2v` with Tonelli over the triangle (`lintegral_quadrant`).  Everything is done with lower
integrals, so no integrability hypothesis is needed; the Bochner form follows for every observable
(★★ `integral_cone_gaussian`), in particular for the frozen partition function of the cone model
with a constant field (★★ `cone_evidence_eq`):

  `∫_{ℝ⁴} e^{−N q²/2 + √N q a} e^{−|u|²/2} du = 2π² ∫_ℝ e^{−N v²/2 + √N v a − |v|} dv`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- The quadratic form of signature `(2, 2)` on `(ℝ × ℝ) × (ℝ × ℝ)`. -/
noncomputable def coneQ (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ((u.1.1 ^ 2 + u.1.2 ^ 2) - (u.2.1 ^ 2 + u.2.2 ^ 2)) / 2

/-- The Gaussian weight `e^{−|u|²/2}`. -/
noncomputable def gaussW (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  Real.exp (-((u.1.1 ^ 2 + u.1.2 ^ 2) + (u.2.1 ^ 2 + u.2.2 ^ 2)) / 2)

theorem measurable_coneQ : Measurable coneQ := by
  unfold coneQ; fun_prop

theorem continuous_coneQ : Continuous coneQ := by
  unfold coneQ; fun_prop

theorem measurable_gaussW : Measurable gaussW := by
  unfold gaussW; fun_prop

theorem gaussW_pos (u : (ℝ × ℝ) × (ℝ × ℝ)) : 0 < gaussW u := Real.exp_pos _

/-! ### Polar coordinates on `ℝ²`: a radial integrand -/

theorem image_sq_Ioi : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact pow_pos (mem_Ioi.1 hy) 2
  · intro hx
    exact ⟨Real.sqrt x, Real.sqrt_pos.2 hx, Real.sq_sqrt (le_of_lt hx)⟩

/-- The substitution `p = r²` on `(0, ∞)`: `∫_0^∞ Ψ = 2 ∫_0^∞ r Ψ(r²) dr` (lower integrals). -/
theorem lintegral_Ioi_eq_two_mul_lintegral_sq (Ψ : ℝ → ℝ≥0∞) :
    ∫⁻ p in Ioi (0 : ℝ), Ψ p = 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * Ψ (r ^ 2) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := fun x => x ^ 2)
    (f' := fun x => 2 * x) measurableSet_Ioi
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt) (fun x hx y hy hxy => by
      have hx' : (0 : ℝ) < x := hx
      have hy' : (0 : ℝ) < y := hy
      simp only at hxy
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]) Ψ
  rw [image_sq_Ioi] at h
  rw [h, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  rw [abs_of_pos (by linarith), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]

/-- ★ **Bipolar reduction on `ℝ²`**: `∫_{ℝ²} Ψ(|z|²) dz = π ∫_0^∞ Ψ(p) dp`. -/
theorem lintegral_radial_sq (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z : ℝ × ℝ, Ψ (z.1 ^ 2 + z.2 ^ 2) = ENNReal.ofReal Real.pi * ∫⁻ p in Ioi (0 : ℝ), Ψ p := by
  rw [← lintegral_comp_polarCoord_symm (fun z : ℝ × ℝ => Ψ (z.1 ^ 2 + z.2 ^ 2))]
  have hpt : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • Ψ ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) =
        ENNReal.ofReal p.1 * Ψ (p.1 ^ 2) := by
    intro p _
    have : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2
      have := Real.cos_sq_add_sin_sq p.2
      nlinarith [this]
    rw [this, smul_eq_mul]
  have hm : Measurable fun x : ℝ × ℝ => ENNReal.ofReal x.1 * Ψ (x.1 ^ 2) :=
    measurable_fst.ennreal_ofReal.mul (hΨ.comp (measurable_fst.pow_const 2))
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  -- pull the angular factor out and substitute `p = r²`
  have h2π : ENNReal.ofReal (2 * Real.pi) = 2 * ENNReal.ofReal Real.pi := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2π, lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top),
    lintegral_Ioi_eq_two_mul_lintegral_sq Ψ]
  ring

/-! ### The four-dimensional integral as a quadrant integral -/

/-- ★ **The bipolar reduction of the cone integral**: for measurable `G`,
`∫_{ℝ⁴} G(q(u)) e^{−|u|²/2} du = π² ∫_0^∞∫_0^∞ G((p − t)/2) e^{−(p+t)/2} dt dp`. -/
theorem lintegral_cone_gauss (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ), G (coneQ u) * ENNReal.ofReal (gaussW u) =
      ENNReal.ofReal Real.pi * (ENNReal.ofReal Real.pi *
        ∫⁻ p in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
          G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2))) := by
  set F : ℝ → ℝ → ℝ≥0∞ := fun p t => G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2))
    with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    simp only [hFdef]
    fun_prop
  have hmeas : Measurable fun u : (ℝ × ℝ) × (ℝ × ℝ) => G (coneQ u) * ENNReal.ofReal (gaussW u) :=
    (hG.comp measurable_coneQ).mul measurable_gaussW.ennreal_ofReal
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  -- inner: a radial function of `z₂`
  have hinner : ∀ z₁ : ℝ × ℝ, ∫⁻ z₂ : ℝ × ℝ, G (coneQ (z₁, z₂)) * ENNReal.ofReal (gaussW (z₁, z₂)) =
      ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), F (z₁.1 ^ 2 + z₁.2 ^ 2) t := by
    intro z₁
    have := lintegral_radial_sq (fun t => F (z₁.1 ^ 2 + z₁.2 ^ 2) t)
      (hFmeas.comp (measurable_const.prodMk measurable_id))
    rw [← this]
    rfl
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ (by simp)]
  congr 1
  -- outer: a radial function of `z₁`
  have := lintegral_radial_sq (fun p => ∫⁻ t in Ioi (0 : ℝ), F p t)
    (hFmeas.lintegral_prod_right' (ν := volume.restrict (Ioi 0)))
  exact this

/-! ### The quadrant integral -/

theorem image_sub_two_mul (p : ℝ) : (fun v : ℝ => p - 2 * v) '' Iio (p / 2) = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    have : v < p / 2 := hv
    show (0 : ℝ) < p - 2 * v
    linarith
  · intro ht
    have ht' : (0 : ℝ) < t := ht
    exact ⟨(p - t) / 2, show (p - t) / 2 < p / 2 by linarith, by ring⟩

/-- The inner substitution `t = p − 2v`. -/
theorem lintegral_inner_subst (G : ℝ → ℝ≥0∞) (p : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)) =
      2 * ∫⁻ v in Iio (p / 2), G v * ENNReal.ofReal (Real.exp (v - p)) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Iio (p / 2))
    (f := fun v => p - 2 * v) (f' := fun _ => -2) measurableSet_Iio
    (fun v _ => by
      simpa using ((hasDerivAt_id v).const_mul 2 |>.const_sub p).hasDerivWithinAt)
    (fun x _ y _ hxy => by simp only at hxy; linarith)
    (fun t => G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)))
  rw [image_sub_two_mul] at h
  rw [h, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Iio fun v _ => ?_
  rw [show (p - (p - 2 * v)) / 2 = v by ring, show -(p + (p - 2 * v)) / 2 = v - p by ring,
    abs_neg, abs_two, ENNReal.ofReal_ofNat]

theorem setOf_lt_half_eq (v : ℝ) : {p : ℝ | 0 < p ∧ v < p / 2} = Ioi (max 0 (2 * v)) := by
  ext p
  simp only [mem_ofPred_eq, mem_Ioi, max_lt_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem lintegral_exp_neg_Ioi (c : ℝ) :
    ∫⁻ p in Ioi c, ENNReal.ofReal (Real.exp (-p)) = ENNReal.ofReal (Real.exp (-c)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_neg_Ioi]

/-- ★★ **The quadrant integral is the Leray integral**:
`∫_0^∞∫_0^∞ G((p − t)/2) e^{−(p+t)/2} dt dp = 2 ∫_ℝ G(v) e^{−|v|} dv`. -/
theorem lintegral_quadrant (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)) =
      2 * ∫⁻ v, G v * ENNReal.ofReal (Real.exp (-|v|)) := by
  simp_rw [lintegral_inner_subst]
  rw [lintegral_const_mul' _ _ (by simp)]
  congr 1
  -- indicators and Tonelli
  set H : ℝ → ℝ → ℝ≥0∞ := fun p v =>
    ({q : ℝ × ℝ | 0 < q.1 ∧ q.2 < q.1 / 2}).indicator (fun _ => (1 : ℝ≥0∞)) (p, v) *
      (G v * ENNReal.ofReal (Real.exp (v - p))) with hHdef
  have hS : MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.2 < q.1 / 2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hHmeas : Measurable (Function.uncurry H) := by
    simp only [hHdef]
    refine (measurable_const.indicator hS).mul ?_
    fun_prop
  have h1 : ∀ p ∈ Ioi (0 : ℝ), ∫⁻ v in Iio (p / 2), G v * ENNReal.ofReal (Real.exp (v - p)) =
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
  -- the `p`-integral for fixed `v`
  have h3 : ∫⁻ p, H p v = G v * ENNReal.ofReal (Real.exp v) *
      ∫⁻ p in Ioi (max 0 (2 * v)), ENNReal.ofReal (Real.exp (-p)) := by
    have hind : Measurable ((Ioi (max 0 (2 * v))).indicator fun p : ℝ =>
        ENNReal.ofReal (Real.exp (-p))) :=
      Measurable.indicator (by fun_prop) measurableSet_Ioi
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_const_mul _ hind]
    congr 1
    funext p
    simp only [hHdef, indicator, mem_ofPred_eq, mem_Ioi, max_lt_iff]
    by_cases h : 0 < p ∧ v < p / 2
    · have h' : 0 < p ∧ 2 * v < p := ⟨h.1, by linarith [h.2]⟩
      rw [if_pos h, if_pos h', one_mul, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, sub_eq_add_neg]
    · have h' : ¬ (0 < p ∧ 2 * v < p) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      rw [if_neg h, if_neg h', zero_mul, mul_zero]
  rw [h3, lintegral_exp_neg_Ioi, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 3
  rcases le_or_gt 0 v with hv | hv
  · rw [max_eq_right (by linarith), abs_of_nonneg hv]; ring
  · rw [max_eq_left (by linarith), abs_of_neg hv]; ring

/-! ### The pushforward measure -/

/-- ★★★ **The Leray density of the cone under the Gaussian prior is `2π² e^{−|v|}`**: the
pushforward of `e^{−|u|²/2} du` along `q` is `2π² e^{−|v|} dv`. -/
theorem map_coneQ_gaussian :
    Measure.map coneQ (volume.withDensity fun u => ENNReal.ofReal (gaussW u)) =
      volume.withDensity fun v => ENNReal.ofReal (2 * Real.pi ^ 2 * Real.exp (-|v|)) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_coneQ hs, withDensity_apply _ (measurable_coneQ hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_coneQ hs),
    ← lintegral_indicator hs]
  have h1 : ∀ u, (coneQ ⁻¹' s).indicator (fun u => ENNReal.ofReal (gaussW u)) u =
      s.indicator (fun _ => (1 : ℝ≥0∞)) (coneQ u) * ENNReal.ofReal (gaussW u) := by
    intro u
    by_cases hu : coneQ u ∈ s <;> simp [indicator, hu]
  simp_rw [h1]
  rw [lintegral_cone_gauss _ (measurable_const.indicator hs),
    lintegral_quadrant _ (measurable_const.indicator hs)]
  have h2 : ∀ v, s.indicator (fun v => ENNReal.ofReal (2 * Real.pi ^ 2 * Real.exp (-|v|))) v =
      ENNReal.ofReal (2 * Real.pi ^ 2) *
        (s.indicator (fun _ => (1 : ℝ≥0∞)) v * ENNReal.ofReal (Real.exp (-|v|))) := by
    intro v
    by_cases hv : v ∈ s
    · simp [indicator, hv, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2)]
    · simp [indicator, hv]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow Real.pi_pos.le]
  ring

/-- ★★ **The Bochner form**: for every measurable observable `g`,
`∫_{ℝ⁴} g(q(u)) e^{−|u|²/2} du = ∫_ℝ g(v) · 2π² e^{−|v|} dv`. -/
theorem integral_cone_gaussian (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ), g (coneQ u) * gaussW u =
      ∫ v, g v * (2 * Real.pi ^ 2 * Real.exp (-|v|)) := by
  have hL : ∫ u : (ℝ × ℝ) × (ℝ × ℝ), g (coneQ u) * gaussW u =
      ∫ u, g (coneQ u) ∂(volume.withDensity fun u => ENNReal.ofReal (gaussW u)) := by
    rw [show (fun u : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (gaussW u)) =
      fun u => ((gaussW u).toNNReal : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul measurable_gaussW.real_toNNReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [NNReal.smul_def, Real.coe_toNNReal _ (gaussW_pos u).le, mul_comm]
  have hd : Measurable fun v : ℝ => 2 * Real.pi ^ 2 * Real.exp (-|v|) := by fun_prop
  have hR : ∫ v, g v * (2 * Real.pi ^ 2 * Real.exp (-|v|)) =
      ∫ v, g v ∂(volume.withDensity fun v =>
        ENNReal.ofReal (2 * Real.pi ^ 2 * Real.exp (-|v|))) := by
    rw [show (fun v : ℝ => ENNReal.ofReal (2 * Real.pi ^ 2 * Real.exp (-|v|))) =
      fun v => ((2 * Real.pi ^ 2 * Real.exp (-|v|)).toNNReal : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hd.real_toNNReal]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * Real.exp (-|v|))]
    ring
  rw [hL, hR, ← map_coneQ_gaussian,
    integral_map measurable_coneQ.aemeasurable hg.aestronglyMeasurable]

/-- ★★ **The frozen partition function of the cone model with a constant field**, reduced to one
dimension: `∫_{ℝ⁴} e^{−N q²/2 + √N q a} e^{−|u|²/2} du = 2π² ∫_ℝ e^{−N v²/2 + √N v a − |v|} dv`. -/
theorem cone_evidence_eq (N a : ℝ) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * gaussW u =
      2 * Real.pi ^ 2 * ∫ v, Real.exp (-N * v ^ 2 / 2 + Real.sqrt N * v * a - |v|) := by
  rw [integral_cone_gaussian (fun v => Real.exp (-N * v ^ 2 / 2 + Real.sqrt N * v * a))
    (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [Real.exp_sub, Real.exp_neg]
  field_simp

end Grammar
