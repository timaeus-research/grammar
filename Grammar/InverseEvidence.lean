/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CompactBaseFirstMoment
import Grammar.GaussianFieldFernique

/-!
# The inverse evidence has all moments (§20, posterior expectations)

The Gaussian threshold `βv < 2` governs the **unnormalised** evidence `E D_ρ(G)` only
(`lintegral_compactD_eq_top`).  Normalised posterior expectations are unaffected: on
`0 < t < (1 + ‖g‖)^{−2}` the fluctuation integrand is at least `t^{λ−1} e^{−2β}`, so

★ `inv_compactD_le`: `D_ρ(g)^{−1} ≤ λ e^{2β} ρ(K)^{−1} (1 + ‖g‖)^{2λ}`,

a polynomial bound in the sup norm at every temperature and every variance.  Consequently

★★ `integrable_inv_compactD_rpow`: `E[D_ρ(G)^{−s}] < ∞` for every `s ≥ 0` as soon as
`(1 + ‖G‖)^{2λs}` is integrable, and ★★ `integrable_inv_compactD_rpow_of_isGaussian`: for a
Gaussian Borel law on `C(K,ℝ)` every inverse moment of the evidence is finite (Fernique via
`IsGaussian.memLp_id`).

The normalised radial moments are polynomially bounded as well: with `⟨t^p⟩_g =
∫ S_{λ+p}(g) dρ / D_ρ(g)` (`compactRadial`, `compactRadial_one = compactM2`),
★ `compactRadial_le`: `⟨t^p⟩_g ≤ Π_{i<p} (2(λ+i)/β + ‖g‖²/4)` (iterating `fluctuation_succ_le`,
`fluctuation_add_nat_le`).  These are the dominations Astra #162 §5 prescribes for the Stein
identity of posterior averages: never bound the numerator exponentially and the denominator
polynomially separately.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory Finset

namespace Grammar

section Pointwise

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ]

/-- ★ **The inverse evidence is polynomially bounded**:
`D_ρ(g)^{−1} ≤ λ e^{2β} ρ(K)^{−1} (1 + R)^{2λ}` for `‖g‖ ≤ R`. -/
theorem inv_compactD_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ‖g‖ ≤ R) :
    (compactD β lam ρ g)⁻¹ ≤ lam * Real.exp (2 * β) / ρ.real univ * (1 + R) ^ (2 * lam) := by
  have hM : 0 < ρ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hρ) (measure_ne_top _ _)
  have hlow := le_compactD ρ hβ hlam g hR
  have h1R : (0 : ℝ) < 1 + R := by linarith
  have hpos : 0 < ρ.real univ * (Real.exp (-2 * β) / lam * (1 + R) ^ (-(2 * lam))) := by
    have := Real.rpow_pos_of_pos h1R (-(2 * lam))
    positivity
  refine (inv_anti₀ hpos hlow).trans (le_of_eq ?_)
  rw [show -2 * β = -(2 * β) by ring, Real.exp_neg, Real.rpow_neg h1R.le]
  have hp : 0 < (1 + R) ^ (2 * lam) := Real.rpow_pos_of_pos h1R _
  field_simp

/-- The inverse evidence bound at `R = ‖g‖`. -/
theorem inv_compactD_le_norm (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) :
    (compactD β lam ρ g)⁻¹ ≤
      lam * Real.exp (2 * β) / ρ.real univ * (1 + ‖g‖) ^ (2 * lam) :=
  inv_compactD_le ρ hβ hlam hρ g (norm_nonneg g) le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- ★★ **All inverse moments of the evidence**: `D_ρ(G)^{−s}` is integrable whenever
`(1 + ‖G‖)^{2λs}` is. -/
theorem integrable_inv_compactD_rpow (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (G : Ω → C(K, ℝ)) (hG : Measurable fun q : Ω × K => G q.1 q.2) {s : ℝ} (hs : 0 ≤ s)
    (hint : Integrable (fun ω => (1 + ‖G ω‖) ^ (2 * lam * s)) P) :
    Integrable (fun ω => (compactD β lam ρ (G ω))⁻¹ ^ s) P := by
  have hmeas : Measurable fun ω => compactD β lam ρ (G ω) :=
    measurable_compactD_comp ρ hβ hlam G hG
  have hC0 : 0 ≤ lam * Real.exp (2 * β) / ρ.real univ := by
    have : 0 ≤ ρ.real univ := measureReal_nonneg
    positivity
  refine (hint.const_mul ((lam * Real.exp (2 * β) / ρ.real univ) ^ s)).mono'
    (hmeas.inv.pow_const s).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have hD := compactD_pos ρ hβ hlam hρ (G ω)
  have h1 : (0 : ℝ) ≤ 1 + ‖G ω‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.2 hD.le) _)]
  calc (compactD β lam ρ (G ω))⁻¹ ^ s ≤
        (lam * Real.exp (2 * β) / ρ.real univ * (1 + ‖G ω‖) ^ (2 * lam)) ^ s :=
        Real.rpow_le_rpow (inv_nonneg.2 hD.le) (inv_compactD_le_norm ρ hβ hlam hρ (G ω)) hs
    _ = (lam * Real.exp (2 * β) / ρ.real univ) ^ s * (1 + ‖G ω‖) ^ (2 * lam * s) := by
        rw [Real.mul_rpow hC0 (Real.rpow_nonneg h1 _), ← Real.rpow_mul h1]

end Pointwise

section Gaussian

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-- The Borel σ-algebra of the sup-norm topology on `C(K,ℝ)`. -/
local instance instMeasurableSpaceContinuousMapInv : MeasurableSpace C(K, ℝ) := borel _

local instance instBorelSpaceContinuousMapInv : BorelSpace C(K, ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(1 + x)^r ≤ 2^r (1 + x^r)` for `x, r ≥ 0`. -/
theorem one_add_rpow_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h2 : (1 + x) ≤ 2 * max 1 x := by
    rcases le_total x 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  have hm : 0 ≤ max 1 x := le_max_of_le_left zero_le_one
  calc (1 + x) ^ r ≤ (2 * max 1 x) ^ r := Real.rpow_le_rpow (by linarith) h2 hr
    _ = 2 ^ r * (max 1 x) ^ r := Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ r * (1 + x ^ r) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
        rcases le_total x 1 with h | h
        · rw [max_eq_left h, Real.one_rpow]
          linarith [Real.rpow_nonneg hx r]
        · rw [max_eq_right h]
          linarith

/-- **Fernique for all powers**: `(1 + ‖G‖)^r` is integrable for every `r ≥ 0` when `G` has a
Gaussian Borel law on `C(K,ℝ)`. -/
theorem integrable_one_add_norm_rpow_of_isGaussian {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => (1 + ‖G ω‖) ^ r) P := by
  have hprob : IsProbabilityMeasure (P.map G) := inferInstance
  have hfin : IsFiniteMeasure P := by
    constructor
    have h := measure_univ (μ := P.map G)
    rw [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h
    rw [h]
    exact ENNReal.one_lt_top
  rcases hr.eq_or_lt with h0 | hr'
  · subst h0
    simp only [Real.rpow_zero]
    exact integrable_const _
  have hnorm : Integrable (fun ω => ‖G ω‖ ^ r) P := by
    have hp0 : ENNReal.ofReal r ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hr'
    have h := (IsGaussian.memLp_id (P.map G) (ENNReal.ofReal r) ENNReal.ofReal_ne_top)
      |>.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hr] at h
    have hmeas : AEStronglyMeasurable (fun f : C(K, ℝ) => ‖id f‖ ^ r) (P.map G) :=
      (continuous_norm.rpow_const fun _ => Or.inr hr).aestronglyMeasurable
    exact (integrable_map_measure hmeas hG.aemeasurable).1 h
  have hmeas : Measurable fun ω => (1 + ‖G ω‖) ^ r :=
    (((continuous_const.add continuous_norm).rpow_const fun _ => Or.inr hr).measurable).comp hG
  refine (((integrable_const (1 : ℝ)).add hnorm).const_mul (2 ^ r)).mono'
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact one_add_rpow_le (norm_nonneg _) hr

variable [MeasurableSpace K] [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ]

/-- ★★ **Every inverse moment of the evidence of a Gaussian field is finite**: for a Gaussian
Borel law on `C(K,ℝ)`, `E[D_ρ(G)^{−s}] < ∞` for all `s ≥ 0`, at every temperature and every
variance — the threshold `βv < 2` concerns the unnormalised evidence only. -/
theorem integrable_inv_compactD_rpow_of_isGaussian (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    {G : Ω → C(K, ℝ)} (hG : Measurable G) [IsGaussian (P.map G)] {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun ω => (compactD β lam ρ (G ω))⁻¹ ^ s) P :=
  integrable_inv_compactD_rpow ρ hβ hlam hρ G
    (measurable_uncurry_eval G (measurable_eval_comp hG)) hs
    (integrable_one_add_norm_rpow_of_isGaussian hG (by positivity))

end Gaussian

section Radial

variable {β lam : ℝ}

/-- Iterating the second-moment ratio bound: `S_{λ+p}(a) ≤ Π_{i<p} (2(λ+i)/β + a₊²/4) S_λ(a)`. -/
theorem fluctuation_add_nat_le (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) (p : ℕ) :
    fluctuation β (lam + p) a ≤
      (∏ i ∈ range p, (2 * (lam + i) / β + max a 0 ^ 2 / 4)) * fluctuation β lam a := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hlp : 0 < lam + p := by positivity
    have h1 := fluctuation_succ_le hβ hlp a
    rw [prod_range_succ]
    have hc : 0 ≤ 2 * (lam + p) / β + max a 0 ^ 2 / 4 := by positivity
    calc fluctuation β (lam + ((p + 1 : ℕ) : ℝ)) a = fluctuation β (lam + p + 1) a := by
          push_cast; ring_nf
      _ ≤ (2 * (lam + p) / β + max a 0 ^ 2 / 4) * fluctuation β (lam + p) a := h1
      _ ≤ (2 * (lam + p) / β + max a 0 ^ 2 / 4) *
            ((∏ i ∈ range p, (2 * (lam + i) / β + max a 0 ^ 2 / 4)) * fluctuation β lam a) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (∏ i ∈ range p, (2 * (lam + i) / β + max a 0 ^ 2 / 4)) *
            (2 * (lam + p) / β + max a 0 ^ 2 / 4) * fluctuation β lam a := by ring

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ρ : Measure K) [IsFiniteMeasure ρ]

/-- The normalised radial moment `⟨t^p⟩_g = ∫ S_{λ+p}(g) dρ / D_ρ(g)` of the limit posterior. -/
noncomputable def compactRadial (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) (p : ℕ) : ℝ :=
  (∫ x, fluctuation β (lam + p) (g x) ∂ρ) / compactD β lam ρ g

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
theorem compactRadial_one (g : K → ℝ) : compactRadial β lam ρ g 1 = compactM2 β lam ρ g := by
  simp [compactRadial, compactM2]

/-- ★ **Normalised radial moments are polynomially bounded**:
`⟨t^p⟩_g ≤ Π_{i<p} (2(λ+i)/β + R²/4)` for `‖g‖ ≤ R`. -/
theorem compactRadial_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) {R : ℝ}
    (hR : ‖g‖ ≤ R) (p : ℕ) :
    compactRadial β lam ρ g p ≤ ∏ i ∈ range p, (2 * (lam + i) / β + R ^ 2 / 4) := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactRadial
  rw [div_le_iff₀ hD]
  unfold compactD
  rw [← integral_const_mul]
  refine integral_mono (integrable_fluctuation_comp ρ hβ (by positivity) g)
    ((integrable_fluctuation_comp ρ hβ hlam g).const_mul _) fun x => ?_
  refine (fluctuation_add_nat_le hβ hlam (g x) p).trans
    (mul_le_mul_of_nonneg_right ?_ (fluctuation_pos β lam _ hβ hlam).le)
  have hgx' : |g x| ≤ ‖g‖ := by
    have := g.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have hgx : max (g x) 0 ≤ R := max_le ((le_abs_self _).trans (hgx'.trans hR))
    ((norm_nonneg g).trans hR)
  have hsq : max (g x) 0 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (le_max_right _ _) hgx 2
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  linarith

end Radial

end Grammar
