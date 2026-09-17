/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianLimit
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Derivative processes of a smooth Gaussian random field are Gaussian

For a random field `ζ_o : ℝ^d → ℝ`, smooth for every `o`, whose value process on an open set `U`
is Gaussian (`IsGaussianProcess (fun (x : U) o => ζ o x) P`), every derivative-evaluation process
`(x, w) ↦ ∂^r ζ_o(x)(w₁,…,w_r)` on `U` is Gaussian (`isGaussianProcess_iteratedFDeriv`), and jointly in all orders
(`isGaussianProcess_jetEval_le`).  Route:
induction on `r`; the order-`r+1` evaluation at `(x, v, w)` is the a.s. (everywhere) limit of the
difference quotients `h_n⁻¹ (∂^r ζ(x + h_n v)(w) − ∂^r ζ(x)(w))`, each a continuous linear image
of two values of the order-`r` process (`IsGaussianProcess.of_isGaussianProcess`), and Gaussian
laws of finite-dimensional vectors are closed under a.s. limits (`hasGaussianLaw_pi_of_tendsto_ae`,
from `hasGaussianLaw_of_tendsto_ae`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ContDiff

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- ★ **Almost-sure limits of Gaussian random vectors are Gaussian** (finite index). -/
theorem hasGaussianLaw_pi_of_tendsto_ae {ι : Type*} [Finite ι] {V : ℕ → Ω → ι → ℝ}
    {W : Ω → ι → ℝ} (hV : ∀ n, HasGaussianLaw (V n) P)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => V n o) atTop (𝓝 (W o))) : HasGaussianLaw W P := by
  letI := Fintype.ofFinite ι
  have hVm : ∀ n, AEMeasurable (V n) P := fun n => (hV n).aemeasurable
  have hW : AEMeasurable W P := aemeasurable_of_tendsto_metrizable_ae atTop hVm hlim
  refine ⟨⟨fun L => ?_⟩⟩
  have hL : ∀ n, HasGaussianLaw (⇑L ∘ V n) P := fun n => (hV n).map L
  have hlimL : ∀ᵐ o ∂P, Tendsto (fun n => (⇑L ∘ V n) o) atTop (𝓝 ((⇑L ∘ W) o)) := by
    filter_upwards [hlim] with o ho
    exact (L.continuous.tendsto _).comp ho
  have hG := hasGaussianLaw_of_tendsto_ae hL hlimL
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hW,
    hG.map_eq_gaussianReal, integral_map hW L.continuous.aestronglyMeasurable,
    variance_map L.continuous.measurable.aemeasurable hW]
  rfl

variable {d : ℕ}

/-- The difference quotients of `x ↦ ∂^r f(x)(w)` along `v` converge to `∂^{r+1} f(x)(v, w)`. -/
theorem tendsto_diffQuot_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ)
    (x v : Fin d → ℝ) (w : Fin r → (Fin d → ℝ)) {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hh0 : ∀ n, h n ≠ 0) :
    Tendsto (fun n => (h n)⁻¹ * (iteratedFDeriv ℝ r f (x + h n • v) w - iteratedFDeriv ℝ r f x w))
      atTop (𝓝 (iteratedFDeriv ℝ (r + 1) f x (Fin.cons v w))) := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ r f) x :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top r)) x
  set A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Fin d → ℝ) ℝ w with hA
  have hg : HasFDerivAt (fun y => iteratedFDeriv ℝ r f y w)
      (A.comp (fderiv ℝ (iteratedFDeriv ℝ r f) x)) x :=
    A.hasFDerivAt.comp x hdiff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
    simpa using this
  have hcomp := hg.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hcomp
  have hseq : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hh, Eventually.of_forall fun n => hh0 n⟩
  have hval : (A.comp (fderiv ℝ (iteratedFDeriv ℝ r f) x)) v =
      iteratedFDeriv ℝ (r + 1) f x (Fin.cons v w) := by
    rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rfl
  rw [← hval]
  refine (hslope.comp hseq).congr fun n => ?_
  simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul]

/-- ★★ **Derivative processes of a smooth Gaussian field are Gaussian**: if the value process of
`ζ` on the open set `U` is Gaussian, so is every process `(x, w) ↦ ∂^r ζ_o(x)(w)` on `U`. -/
theorem isGaussianProcess_iteratedFDeriv {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o))
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) (r : ℕ) :
    IsGaussianProcess
      (fun (p : U × (Fin r → (Fin d → ℝ))) o => iteratedFDeriv ℝ r (ζ o) p.1 p.2) P := by
  induction r with
  | zero =>
    refine (hG.comp_right Prod.fst).congr fun p => Eventually.of_forall fun o => ?_
    simp [iteratedFDeriv_zero_apply]
  | succ r ih =>
    classical
    -- a ball around every point of `U`
    have hδ : ∀ p : U × (Fin (r + 1) → (Fin d → ℝ)), ∃ δ > 0, ball (p.1 : Fin d → ℝ) δ ⊆ U :=
      fun p => Metric.isOpen_iff.1 hU _ p.1.2
    choose δ hδpos hδball using hδ
    -- the step sizes and the shifted points
    let step : U × (Fin (r + 1) → (Fin d → ℝ)) → ℕ → ℝ := fun p n =>
      δ p / ((n + 1) * (‖p.2 0‖ + 1))
    have hstep_pos : ∀ p n, 0 < step p n := fun p n => by
      have := hδpos p
      positivity
    have hstep_ne : ∀ p n, step p n ≠ 0 := fun p n => (hstep_pos p n).ne'
    have hstep_tendsto : ∀ p, Tendsto (step p) atTop (𝓝 0) := fun p => by
      refine Filter.Tendsto.const_div_atTop ?_ (δ p)
      refine Tendsto.atTop_mul_const' (by positivity) ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hmem : ∀ p n, (p.1 : Fin d → ℝ) + step p n • p.2 0 ∈ U := fun p n => by
      refine hδball p ?_
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hstep_pos p n)]
      have hv : 0 ≤ ‖p.2 0‖ := norm_nonneg _
      have hn : (1 : ℝ) ≤ n + 1 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hδp := hδpos p
      have hlt : ‖p.2 0‖ < (n + 1) * (‖p.2 0‖ + 1) := by nlinarith
      calc step p n * ‖p.2 0‖ = δ p * (‖p.2 0‖ / ((n + 1) * (‖p.2 0‖ + 1))) := by
            simp only [step]
            ring
        _ < δ p * 1 := by
            refine mul_lt_mul_of_pos_left ?_ hδp
            rw [div_lt_one (by positivity)]
            exact hlt
        _ = δ p := mul_one _
    let pt : U × (Fin (r + 1) → (Fin d → ℝ)) → ℕ → U := fun p n => ⟨_, hmem p n⟩
    -- the difference quotients
    let V : ℕ → Ω → U × (Fin (r + 1) → (Fin d → ℝ)) → ℝ := fun n o p =>
      (step p n)⁻¹ * (iteratedFDeriv ℝ r (ζ o) (pt p n) (Fin.tail p.2) -
        iteratedFDeriv ℝ r (ζ o) p.1 (Fin.tail p.2))
    have hVG : ∀ n, IsGaussianProcess (fun p o => V n o p) P := fun n => by
      refine ih.of_isGaussianProcess fun p => ⟨{(pt p n, Fin.tail p.2), (p.1, Fin.tail p.2)},
        { toFun := fun y => (step p n)⁻¹ *
            (y ⟨(pt p n, Fin.tail p.2), by simp⟩ - y ⟨(p.1, Fin.tail p.2), by simp⟩)
          map_add' := fun y z => by
            simp only [Pi.add_apply]
            ring
          map_smul' := fun c y => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring }, fun o => ?_⟩
      simp [V, Finset.restrict]
    have hconv : ∀ p o, Tendsto (fun n => V n o p) atTop
        (𝓝 (iteratedFDeriv ℝ (r + 1) (ζ o) p.1 p.2)) := fun p o => by
      have h := tendsto_diffQuot_iteratedFDeriv (hζ o) r p.1 (p.2 0) (Fin.tail p.2)
        (hstep_tendsto p) (hstep_ne p)
      rw [Fin.cons_self_tail] at h
      exact h
    refine ⟨fun I => ?_⟩
    refine hasGaussianLaw_pi_of_tendsto_ae (V := fun n o => I.restrict fun p => V n o p)
      (fun n => (hVG n).hasGaussianLaw I) (Eventually.of_forall fun o => ?_)
    exact tendsto_pi_nhds.2 fun p => hconv p o

/-- ★★ **The joint derivative process of all orders `≤ R` is Gaussian**: indices are
`(r, x, w)` with `r ≤ R`, `x ∈ U` and a direction sequence `w : ℕ → ℝ^d` (the first `r` terms are
used).  Induction on `R`: the order-`R+1` evaluations are limits of difference quotients of
order-`R` evaluations, the lower orders are carried along unchanged. -/
theorem isGaussianProcess_jetEval_le {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o))
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) (R : ℕ) :
    IsGaussianProcess (fun (p : {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R}) o =>
      iteratedFDeriv ℝ p.1.1 (ζ o) p.1.2.1 (fun j : Fin p.1.1 => p.1.2.2 j)) P := by
  induction R with
  | zero =>
    refine (hG.comp_right fun p => p.1.2.1).congr fun p => Eventually.of_forall fun o => ?_
    obtain ⟨⟨r, x, w⟩, hr⟩ := p
    have hr0 : r = 0 := Nat.le_zero.1 hr
    subst hr0
    simp [iteratedFDeriv_zero_apply]
  | succ R ih =>
    classical
    have hδ : ∀ p : {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R + 1},
        ∃ δ > 0, ball (p.1.2.1 : Fin d → ℝ) δ ⊆ U :=
      fun p => Metric.isOpen_iff.1 hU _ p.1.2.1.2
    choose δ hδpos hδball using hδ
    let step : {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R + 1} → ℕ → ℝ := fun p n =>
      δ p / ((n + 1) * (‖p.1.2.2 0‖ + 1))
    have hstep_pos : ∀ p n, 0 < step p n := fun p n => by
      have := hδpos p
      positivity
    have hstep_ne : ∀ p n, step p n ≠ 0 := fun p n => (hstep_pos p n).ne'
    have hstep_tendsto : ∀ p, Tendsto (step p) atTop (𝓝 0) := fun p => by
      refine Filter.Tendsto.const_div_atTop ?_ (δ p)
      refine Tendsto.atTop_mul_const' (by positivity) ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hmem : ∀ p n, (p.1.2.1 : Fin d → ℝ) + step p n • p.1.2.2 0 ∈ U := fun p n => by
      refine hδball p ?_
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hstep_pos p n)]
      have hv : 0 ≤ ‖p.1.2.2 0‖ := norm_nonneg _
      have hn : (1 : ℝ) ≤ n + 1 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hδp := hδpos p
      have hlt : ‖p.1.2.2 0‖ < (n + 1) * (‖p.1.2.2 0‖ + 1) := by nlinarith
      calc step p n * ‖p.1.2.2 0‖ = δ p * (‖p.1.2.2 0‖ / ((n + 1) * (‖p.1.2.2 0‖ + 1))) := by
            simp only [step]
            ring
        _ < δ p * 1 := by
            refine mul_lt_mul_of_pos_left ?_ hδp
            rw [div_lt_one (by positivity)]
            exact hlt
        _ = δ p := mul_one _
    let pt : {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R + 1} → ℕ → U := fun p n => ⟨_, hmem p n⟩
    -- the approximants: difference quotients at the top order, the values below
    let V : ℕ → Ω → {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R + 1} → ℝ := fun n o p =>
      if p.1.1 = R + 1 then
        (step p n)⁻¹ * (iteratedFDeriv ℝ R (ζ o) (pt p n) (fun j : Fin R => p.1.2.2 (j + 1)) -
          iteratedFDeriv ℝ R (ζ o) p.1.2.1 (fun j : Fin R => p.1.2.2 (j + 1)))
      else iteratedFDeriv ℝ p.1.1 (ζ o) p.1.2.1 (fun j : Fin p.1.1 => p.1.2.2 j)
    have hVG : ∀ n, IsGaussianProcess (fun p o => V n o p) P := fun n => by
      refine ih.of_isGaussianProcess fun p => ?_
      by_cases hp : p.1.1 = R + 1
      · refine ⟨{⟨(R, pt p n, fun j => p.1.2.2 (j + 1)), le_rfl⟩,
          ⟨(R, p.1.2.1, fun j => p.1.2.2 (j + 1)), le_rfl⟩},
          { toFun := fun y => (step p n)⁻¹ *
              (y ⟨⟨(R, pt p n, fun j => p.1.2.2 (j + 1)), le_rfl⟩, by simp⟩ -
                y ⟨⟨(R, p.1.2.1, fun j => p.1.2.2 (j + 1)), le_rfl⟩, by simp⟩)
            map_add' := fun y z => by
              simp only [Pi.add_apply]
              ring
            map_smul' := fun c y => by
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }, fun o => ?_⟩
        simp [V, hp, Finset.restrict]
      · have hle : p.1.1 ≤ R := Nat.lt_succ_iff.1 (lt_of_le_of_ne p.2 hp)
        refine ⟨{⟨p.1, hle⟩},
          { toFun := fun y => y ⟨⟨p.1, hle⟩, by simp⟩
            map_add' := fun y z => by simp
            map_smul' := fun c y => by simp }, fun o => ?_⟩
        simp [V, hp, Finset.restrict]
    have hconv : ∀ p o, Tendsto (fun n => V n o p) atTop
        (𝓝 (iteratedFDeriv ℝ p.1.1 (ζ o) p.1.2.1 (fun j : Fin p.1.1 => p.1.2.2 j))) :=
      fun p o => by
      by_cases hp : p.1.1 = R + 1
      · have h := tendsto_diffQuot_iteratedFDeriv (hζ o) R p.1.2.1 (p.1.2.2 0)
          (fun j : Fin R => p.1.2.2 (j + 1)) (hstep_tendsto p) (hstep_ne p)
        simp only [V, hp, if_true]
        obtain ⟨⟨r, x, w⟩, hr⟩ := p
        simp only at hp
        subst hp
        have heq : (fun j : Fin (R + 1) => w j) =
            Fin.cons (w 0) (fun j : Fin R => w (j + 1)) := by
          funext j
          refine Fin.cases ?_ (fun i => ?_) j
          · simp
          · simp [Fin.cons_succ]
        dsimp only
        rw [heq]
        exact h
      · simp only [V, hp, if_false]
        exact tendsto_const_nhds
    refine ⟨fun I => ?_⟩
    exact hasGaussianLaw_pi_of_tendsto_ae (V := fun n o => I.restrict fun p => V n o p)
      (fun n => (hVG n).hasGaussianLaw I)
      (Eventually.of_forall fun o => tendsto_pi_nhds.2 fun p => hconv p o)

end Grammar
