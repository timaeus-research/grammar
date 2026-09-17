/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorWeightStein

/-!
# Two-site exchangeable weights: averaging the quotient balances the posterior (§20, sanity anchor)

On a base with two sites of masses `p, 1−p` and positive random posterior weights `U, V`, the
posterior mass of the first site is `Q_p = pU/(pU + (1−p)V)` (`twoSitePosteriorMass`).  If `(U,V)`
is **exchangeable**, then

★★ `integral_twoSitePosteriorMass_sub`:
`E Q_p − p = (p(1−p)(1−2p)/2) · E[(U−V)² / ((pU+(1−p)V)((1−p)U+pV))]`

(the symmetrised algebraic identity `twoSitePosteriorMass_symm_sub` integrated against the
exchangeable law; the ratio is bounded by `1/min(p,1−p)²`, so no moments of `U, V` enter).
Consequently ★ `integral_twoSitePosteriorMass_mem`: `E Q_p ∈ [min(p,1/2), max(p,1/2)]` — random
exchangeable weights move the averaged posterior mass **toward equal allocation**, a minority site
gains and a majority site loses; in particular positivity of an observable does not make the
covariance response nonnegative (Astra #164 §2).  The finite-atom posterior average of the
indicator of site `0` is exactly `Q_p` with `U = S_λ(g₀)`, `V = S_λ(g₁)` (`postAvg_two_eq`), so
this is a closed-form check on the averaged compact posterior.

Zero `sorry`/`axiom`.
-/

open MeasureTheory

namespace Grammar

/-- The posterior mass of the first of two sites with base masses `p, 1−p` and weights `u, v`. -/
noncomputable def twoSitePosteriorMass (p u v : ℝ) : ℝ := p * u / (p * u + (1 - p) * v)

/-- The exchangeability kernel `(u−v)² / ((pu+(1−p)v)((1−p)u+pv))`. -/
noncomputable def twoSiteKernel (p u v : ℝ) : ℝ :=
  (u - v) ^ 2 / ((p * u + (1 - p) * v) * ((1 - p) * u + p * v))

section Algebra

variable {p u v : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hu : 0 < u) (hv : 0 < v)
include hp hp₁ hu hv

theorem twoSite_denom_pos : 0 < p * u + (1 - p) * v := by nlinarith

theorem twoSite_denom_pos' : 0 < (1 - p) * u + p * v := by nlinarith

/-- ★ **The symmetrised identity**:
`(Q_p(u,v) + Q_p(v,u))/2 − p = (p(1−p)(1−2p)/2) · (u−v)²/((pu+(1−p)v)((1−p)u+pv))`. -/
theorem twoSitePosteriorMass_symm_sub :
    (twoSitePosteriorMass p u v + twoSitePosteriorMass p v u) / 2 - p =
      p * (1 - p) * (1 - 2 * p) / 2 * twoSiteKernel p u v := by
  have h1 := (twoSite_denom_pos hp hp₁ hu hv).ne'
  have h2 := (twoSite_denom_pos' hp hp₁ hu hv).ne'
  unfold twoSitePosteriorMass twoSiteKernel
  rw [show p * v + (1 - p) * u = (1 - p) * u + p * v by ring, div_add_div _ _ h1 h2, div_div,
    div_sub' (mul_ne_zero (mul_ne_zero h1 h2) two_ne_zero), mul_div_assoc',
    div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) two_ne_zero) (mul_ne_zero h1 h2)]
  ring

theorem twoSitePosteriorMass_nonneg : 0 ≤ twoSitePosteriorMass p u v :=
  div_nonneg (by positivity) (twoSite_denom_pos hp hp₁ hu hv).le

theorem twoSitePosteriorMass_le_one : twoSitePosteriorMass p u v ≤ 1 := by
  unfold twoSitePosteriorMass
  rw [div_le_one (twoSite_denom_pos hp hp₁ hu hv)]
  nlinarith

theorem twoSiteKernel_nonneg : 0 ≤ twoSiteKernel p u v :=
  div_nonneg (sq_nonneg _) (mul_pos (twoSite_denom_pos hp hp₁ hu hv)
    (twoSite_denom_pos' hp hp₁ hu hv)).le

/-- `(u−v)²/((pu+(1−p)v)((1−p)u+pv)) ≤ 1/min(p,1−p)²`. -/
theorem twoSiteKernel_le : twoSiteKernel p u v ≤ 1 / min p (1 - p) ^ 2 := by
  have hm : 0 < min p (1 - p) := lt_min hp (by linarith)
  have hmp : min p (1 - p) ≤ p := min_le_left _ _
  have hmq : min p (1 - p) ≤ 1 - p := min_le_right _ _
  have h1 : min p (1 - p) * (u + v) ≤ p * u + (1 - p) * v := by nlinarith
  have h2 : min p (1 - p) * (u + v) ≤ (1 - p) * u + p * v := by nlinarith
  have hsum : 0 < u + v := by linarith
  unfold twoSiteKernel
  rw [div_le_div_iff₀ (mul_pos (twoSite_denom_pos hp hp₁ hu hv) (twoSite_denom_pos' hp hp₁ hu hv))
    (by positivity)]
  have h3 : (u - v) ^ 2 ≤ (u + v) ^ 2 := by nlinarith
  calc (u - v) ^ 2 * min p (1 - p) ^ 2 ≤ (u + v) ^ 2 * min p (1 - p) ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (min p (1 - p) * (u + v)) * (min p (1 - p) * (u + v)) := by ring
    _ ≤ (p * u + (1 - p) * v) * ((1 - p) * u + p * v) :=
        mul_le_mul h1 h2 (by positivity) (twoSite_denom_pos hp hp₁ hu hv).le
    _ = 1 * ((p * u + (1 - p) * v) * ((1 - p) * u + p * v)) := by ring

/-- `p(1−p) · (u−v)²/((pu+(1−p)v)((1−p)u+pv)) ≤ 1` (the difference of the two sides is `uv`). -/
theorem twoSiteKernel_mul_le : p * (1 - p) * twoSiteKernel p u v ≤ 1 := by
  have h1 := twoSite_denom_pos hp hp₁ hu hv
  have h2 := twoSite_denom_pos' hp hp₁ hu hv
  unfold twoSiteKernel
  rw [mul_div_assoc', div_le_one (mul_pos h1 h2)]
  nlinarith [mul_pos hu hv]

end Algebra

section Exchangeable

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (U V : Ω → ℝ)
  (hU : Measurable U) (hV : Measurable V) (hpos : ∀ ω, 0 < U ω ∧ 0 < V ω)
  (hexch : μ.map (fun ω => (U ω, V ω)) = μ.map (fun ω => (V ω, U ω))) {p : ℝ} (hp : 0 < p)
  (hp₁ : p < 1)

omit [IsProbabilityMeasure μ] in
include hU hV hexch in
/-- Exchangeability transports integrals of functions of `(U,V)` to `(V,U)`. -/
theorem integral_swap_of_exchangeable (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    ∫ ω, F (U ω, V ω) ∂μ = ∫ ω, F (V ω, U ω) ∂μ := by
  have h1 : ∫ ω, F (U ω, V ω) ∂μ = ∫ z, F z ∂μ.map (fun ω => (U ω, V ω)) :=
    (integral_map (hU.prodMk hV).aemeasurable hF.aestronglyMeasurable).symm
  have h2 : ∫ ω, F (V ω, U ω) ∂μ = ∫ z, F z ∂μ.map (fun ω => (V ω, U ω)) :=
    (integral_map (hV.prodMk hU).aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, h2, hexch]

theorem measurable_twoSitePosteriorMass (p : ℝ) :
    Measurable fun z : ℝ × ℝ => twoSitePosteriorMass p z.1 z.2 := by
  unfold twoSitePosteriorMass
  exact (measurable_const.mul measurable_fst).div
    ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))

theorem measurable_twoSiteKernel (p : ℝ) :
    Measurable fun z : ℝ × ℝ => twoSiteKernel p z.1 z.2 := by
  unfold twoSiteKernel
  exact ((measurable_fst.sub measurable_snd).pow_const 2).div
    (((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)).mul
      ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))

include hU hV hpos hp hp₁

theorem integrable_twoSitePosteriorMass :
    Integrable (fun ω => twoSitePosteriorMass p (U ω) (V ω)) μ :=
  Integrable.of_bound ((measurable_twoSitePosteriorMass p).comp
    (hU.prodMk hV)).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (twoSitePosteriorMass_nonneg hp hp₁ (hpos ω).1 (hpos ω).2)]
      exact twoSitePosteriorMass_le_one hp hp₁ (hpos ω).1 (hpos ω).2)

theorem integrable_twoSitePosteriorMass_swap :
    Integrable (fun ω => twoSitePosteriorMass p (V ω) (U ω)) μ :=
  Integrable.of_bound ((measurable_twoSitePosteriorMass p).comp
    (hV.prodMk hU)).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (twoSitePosteriorMass_nonneg hp hp₁ (hpos ω).2 (hpos ω).1)]
      exact twoSitePosteriorMass_le_one hp hp₁ (hpos ω).2 (hpos ω).1)

theorem integrable_twoSiteKernel : Integrable (fun ω => twoSiteKernel p (U ω) (V ω)) μ :=
  Integrable.of_bound ((measurable_twoSiteKernel p).comp (hU.prodMk hV)).aestronglyMeasurable
    (1 / min p (1 - p) ^ 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (twoSiteKernel_nonneg hp hp₁ (hpos ω).1 (hpos ω).2)]
      exact twoSiteKernel_le hp hp₁ (hpos ω).1 (hpos ω).2)

include hexch

/-- ★★ **Averaging the quotient over exchangeable weights**:
`E Q_p(U,V) − p = (p(1−p)(1−2p)/2) · E[(U−V)²/((pU+(1−p)V)((1−p)U+pV))]`. -/
theorem integral_twoSitePosteriorMass_sub :
    (∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ) - p =
      p * (1 - p) * (1 - 2 * p) / 2 * ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ := by
  have hQint := integrable_twoSitePosteriorMass μ U V hU hV hpos hp hp₁
  have hQint' := integrable_twoSitePosteriorMass_swap μ U V hU hV hpos hp hp₁
  have hKint := integrable_twoSiteKernel μ U V hU hV hpos hp hp₁
  have hswap : ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ =
      ∫ ω, twoSitePosteriorMass p (V ω) (U ω) ∂μ :=
    integral_swap_of_exchangeable μ U V hU hV hexch _ (measurable_twoSitePosteriorMass p)
  have hsym : ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ =
      ∫ ω, (twoSitePosteriorMass p (U ω) (V ω) + twoSitePosteriorMass p (V ω) (U ω)) / 2 ∂μ := by
    rw [integral_div, integral_add hQint hQint', ← hswap]
    ring
  have hpt : ∀ ω, (twoSitePosteriorMass p (U ω) (V ω) + twoSitePosteriorMass p (V ω) (U ω)) / 2 =
      p + p * (1 - p) * (1 - 2 * p) / 2 * twoSiteKernel p (U ω) (V ω) := fun ω => by
    have := twoSitePosteriorMass_symm_sub hp hp₁ (hpos ω).1 (hpos ω).2
    linarith
  rw [hsym]
  simp_rw [hpt]
  rw [integral_add (integrable_const p) (hKint.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul]
  ring

/-- ★ **Balancing**: `E Q_p ∈ [min(p,1/2), max(p,1/2)]` — exchangeable random weights move the
averaged posterior mass toward equal allocation. -/
theorem integral_twoSitePosteriorMass_mem :
    min p (1 / 2) ≤ ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ∧
      ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ≤ max p (1 / 2) := by
  have h := integral_twoSitePosteriorMass_sub μ U V hU hV hpos hexch hp hp₁
  have hKint := integrable_twoSiteKernel μ U V hU hV hpos hp hp₁
  have hK0 : 0 ≤ ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ :=
    integral_nonneg fun ω => twoSiteKernel_nonneg hp hp₁ (hpos ω).1 (hpos ω).2
  have hpq : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hK1 : p * (1 - p) * ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ ≤ 1 := by
    rw [← integral_const_mul]
    calc ∫ ω, p * (1 - p) * twoSiteKernel p (U ω) (V ω) ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ :=
          integral_mono (hKint.const_mul _) (integrable_const _) fun ω =>
            twoSiteKernel_mul_le hp hp₁ (hpos ω).1 (hpos ω).2
      _ = 1 := by rw [integral_const, probReal_univ, one_smul]
  set Kb := ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ
  rcases le_or_gt p (1 / 2) with hp2 | hp2
  · rw [min_eq_left hp2, max_eq_right hp2]
    have hc : 0 ≤ 1 - 2 * p := by linarith
    constructor
    · nlinarith [mul_nonneg (mul_nonneg hpq.le hc) hK0]
    · nlinarith [mul_nonneg hc (sub_nonneg.2 hK1)]
  · rw [min_eq_right hp2.le, max_eq_left hp2.le]
    have hc : 0 ≤ 2 * p - 1 := by linarith
    constructor
    · nlinarith [mul_nonneg hc (sub_nonneg.2 hK1)]
    · nlinarith [mul_nonneg (mul_nonneg hpq.le hc) hK0]

end Exchangeable

section FiniteAtoms

variable {β lam : ℝ}

/-- The finite-atom posterior average of the indicator of site `0` on a two-site base with masses
`p, 1−p` is `Q_p(S_λ(g₀), S_λ(g₁))`. -/
theorem postAvg_two_eq (p : ℝ) (g : Fin 2 → ℝ) :
    postAvg β lam ![p, 1 - p] ![1, 0] g =
      twoSitePosteriorMass p (fluctuation β lam (g 0)) (fluctuation β lam (g 1)) := by
  unfold postAvg postWt quartetD twoSitePosteriorMass
  simp [Fin.sum_univ_two]

end FiniteAtoms

end Grammar
