/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MixedExponentExample

/-!
# The posterior expectation `E_N[y₀²] → 1/5` in the `x²y⁴` example

Consult #80 unit 2 (posterior check). For `K(y) = y₀² y₁⁴` on the square the leading residual-face
density is proportional to `|y₀|^{−1/2}`, so the posterior expectation of the observable `y₀²`
converges to `∫₀¹ t² t^{−1/2} dt / ∫₀¹ t^{−1/2} dt = (2/5)/2 = 1/5`. Formally: the residual face
integral of `y₀²` is `∫_{(0,1]²} u₀² u₀^{−1/2} du = 2/5` (`inner_sq`), so the coefficient of
`Z_N[y₀²]` at `(1/4, 0)` is `Γ(1/4) · 2/5` (`productCoeffD_sq`), and CCXLVII's transfer theorem
gives ★ `tendsto_posteriorExpectation_sq : E_N[y₀²] → 1/5`.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

namespace MixedExample

open SquareExample

/-- The observable `y₀²`. -/
def Fsq (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2

theorem continuous_Fsq : Continuous Fsq := (continuous_apply (0 : Fin 2)).pow 2

theorem hFc_sq : ∀ i, ContinuousOn (fun y => Fsq (((ResolutionCover.ofChart chart).chart i).φ y))
    (Ps i).W :=
  fun _ => continuous_Fsq.continuousOn

theorem hFm_sq : Measurable Fsq := continuous_Fsq.measurable

theorem hF_sq : Integrable (fun x => Fsq x * one.w x)
    (volume.restrict (⋃ i, (ResolutionCover.ofChart chart).image i)) := by
  rw [ResolutionCover.ofChart_iUnion_image]
  change Integrable _ (volume.restrict (id '' SquareExample.box))
  rw [Set.image_id]
  exact (continuous_Fsq.mul continuous_const).continuousOn.integrableOn_compact isCompact_box

/-- The normal index of the coordinate `y₀`. -/
theorem exists_inr_zero : ∃ a₀, (0 : Fin 2) =
    (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀) :=
  exists_inr_of_mem Finset.univ Finset.univ_nonempty (Finset.mem_univ 0)

theorem fin_two_eq (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> simp

theorem ratioExp_ne_of_zero {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀)) :
    ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a₀ = 1 / 4 := by
  rw [ratioExp_normal, ← ha₀, ratio_zero]
  norm_num

/-- The only non-minimal normal coordinate is that of `y₀`. -/
theorem eq_of_nonmin {a₀ a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    (h : ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4) : a = a₀ := by
  rw [ratioExp_normal] at h
  rcases fin_two_eq ((stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm
    (Sum.inr a)) with hj | hj
  · exact Sum.inr_injective ((stratumSplit (Finset.univ : Finset (Fin 2))
      Finset.univ_nonempty).symm.injective (hj.trans ha₀))
  · rw [hj, ratio_one] at h
    exact absurd rfl h

/-- The amplitude of the observable `y₀²` on the piece is `(w a₀)²`. -/
theorem pieceAmp_sq {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (w : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ) :
    (ResolutionCover.ofChart chart).pieceAmp () Finset.univ Finset.univ_nonempty (Ps ()).h (Ps ()).v
      (F := Fsq) (p := one) z w = w a₀ ^ 2 := by
  unfold ResolutionCover.pieceAmp
  rw [v_eq, tangentialMonomial_univ_h]
  change |(1 : ℝ)| * |(1 : ℝ)| * 1 * Fsq (planeSplit (stratumSplit Finset.univ
    Finset.univ_nonempty) (z, w)) = w a₀ ^ 2
  unfold Fsq
  rw [ha₀, planeSplit_stratum_inr]
  simp

/-- `∫_{(0,1]} t² · t^{−1/2} dt = 2/5`. -/
theorem integral_sq_rpow : ∫ t in Ioc (0 : ℝ) 1, t ^ 2 * t ^ (-(1 / 2 : ℝ)) = 2 / 5 := by
  have h : ∀ t ∈ Ioc (0 : ℝ) 1, t ^ 2 * t ^ (-(1 / 2 : ℝ)) = t ^ (3 / 2 : ℝ) := fun t ht => by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht.1]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioc h, integral_Ioc_rpow (by norm_num)]
  norm_num

/-- **The residual face integral of `y₀²` is `2/5`.** -/
theorem inner_sq (hk : ∀ a, 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a)
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (σ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool) :
    ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
      (ResolutionCover.ofChart chart).pieceAmp () Finset.univ Finset.univ_nonempty (Ps ()).h
        (Ps ()).v (F := Fsq) (p := one) z
        (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u)) *
        residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u = 2 / 5 := by
  obtain ⟨a₀, ha₀⟩ := exists_inr_zero
  have hna₀ := ratioExp_ne_of_zero ha₀
  -- the integrand as a product of one-variable functions
  have hpt : ∀ u : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ,
      (ResolutionCover.ofChart chart).pieceAmp () Finset.univ Finset.univ_nonempty (Ps ()).h
        (Ps ()).v (F := Fsq) (p := one) z
        (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u)) *
        residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u =
      ∏ a, ((if a = a₀ then u a ^ 2 else 1) *
        (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
            (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
          else u a ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
            2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4)))) :=
    fun u => by
    rw [pieceAmp_sq ha₀, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    unfold residualWeight
    congr 1
    rw [one_smul, reflect, faceProj]
    simp only [if_neg hna₀, mul_pow, sgn_sq, one_mul]
  rw [setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => hpt u,
    integral_unitBox_prod (fun a t => (if a = a₀ then t ^ 2 else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4))))]
  have hval : (∫ t in Ioc (0 : ℝ) 1, (fun a t => (if a = a₀ then t ^ 2 else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4))))
        a₀ t) = 2 / 5 := by
    have hexp : ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a₀ : ℝ) -
        2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a₀ : ℝ) * (1 / 4)) =
        -(1 / 2) := by
      rw [normalExp_h, normalHalfExp_of_nonmin (hk a₀) hna₀]
      norm_num
    simp only [if_true, if_neg hna₀, hexp]
    exact integral_sq_rpow
  have hother : ∀ a ∈ (Finset.univ : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1))),
      a ≠ a₀ → (∫ t in Ioc (0 : ℝ) 1, (fun a t => (if a = a₀ then t ^ 2 else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4))))
        a t) = 1 := fun a _ ha => by
    have hmin : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 := by
      by_contra hn
      exact ha (eq_of_nonmin ha₀ hn)
    simp only [if_neg ha, if_pos hmin, one_mul]
    simp
  rw [Finset.prod_eq_single a₀ hother (fun h => absurd (Finset.mem_univ _) h), hval]

/-- **The coefficient of `Z_N[y₀²]` at `(1/4, 0)` is `Γ(1/4) · 2/5`.** -/
theorem productCoeffD_sq :
    (ResolutionCover.ofChart chart).productCoeffD Ps K_nonneg one_pos hεb' hFc_sq hpc' hFm_sq hF_sq
      hK' ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) = Real.Gamma (1 / 4) * (2 / 5) :=
  productCoeffD_eq_of_inner hFc_sq hFm_sq hF_sq (2 / 5) inner_sq

/-- ★ **The posterior expectation of `y₀²` converges to `1/5`.** -/
theorem tendsto_posteriorExpectation_sq :
    Tendsto ((ResolutionCover.ofChart chart).posteriorExpectation K one Fsq) atTop (𝓝 (1 / 5)) := by
  have hc₁ : 0 < (ResolutionCover.ofChart chart).productCoeffD Ps K_nonneg one_pos hεb' hFc' hpc'
      hFm hF hK' ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) := by
    rw [productCoeffD_eq]
    exact mul_pos two_pos (Real.Gamma_pos_of_pos (by norm_num))
  have h := ((ResolutionCover.ofChart chart).tendsto_posteriorExpectation_of_hasLeadingTerm
    ((ResolutionCover.ofChart chart).hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps
      K_nonneg one_pos hεb' hpc' hK' hFc_sq hFm_sq hF_sq hact)
    ((ResolutionCover.ofChart chart).hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps
      K_nonneg one_pos hεb' hpc' hK' hFc' hFm hF hact) hc₁).2
  rw [productCoeffD_sq, productCoeffD_eq] at h
  have hΓ : Real.Gamma (1 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have : Real.Gamma (1 / 4) * (2 / 5) / (2 * Real.Gamma (1 / 4)) = 1 / 5 := by
    field_simp
  rwa [this] at h

end MixedExample

end Grammar
