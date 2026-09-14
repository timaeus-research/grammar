/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedRLCTIndex
import Grammar.SmoothResolvedModificationIndependence
import Grammar.MonomialBoxLowerBound

/-!
# Positivity of the leading coefficient at a realised extremal pair

Consult #128 follow-up (5), positivity half. If the extremal data `(λ*, m*)` of the zero fibre
(CDXXXIX) is REALISED at a point `P₀` of the zero fibre — exactly `m* ≥ 1` walls through `P₀`
resonate with `λ*` — and the prior is positive at `π(P₀)`, then the leading coefficient of the
partition function is positive:

  `0 < 𝒯^U_{λ*,m*−1}[1]`  (★★★ `coeff_one_pos_of_realised`),

so `(λ*, m*−1)` is the leading index of `Z^U_N[1]` in the sense of CDXXXIV
(`isLeadingIndexOne_of_realised`) and every consequence of that hypothesis (positivity of the
leading functional, its order-zero bound, the normalised limits) holds UNCONDITIONALLY for such
inputs. Together with CDXXXIX this is the RLCT identification on the resolved manifold: the
partition function satisfies `Z^U_N[1] = Z_N[1] ∼ c N^{−λ*}(log N)^{m*−1}` with `c > 0`, where
`(λ*, m*)` is the extremal pair of the intrinsic wall data on the zero fibre.

Proof. In the even chart box centred at `P₀` (CDXXX), the Euclidean partition function
`Z_N[1] = ∫ prior · e^{−NK}` dominates its restriction to the image of the open orthant box
`(0, ε]^d`, on which the chart representative `π ∘ φ⁻¹` is an injective differentiable map with
Jacobian `b(u) ∏ u^h` (`integral_image_orthant`, Mathlib's change of variables
`integral_image_eq_integral_abs_det_fderiv_smul`); by continuity `|b| · prior ∘ π ∘ φ⁻¹ ≥ c > 0`
on a small box (`exists_orthant_bound`), giving `Z_N[1] ≥ c ∫_{(0,ε]^d} ∏ u^h e^{−N ∏ u^{2k}}`
(`Z_one_ge_mul_monoBoxIntegral`); the monomial integral has leading asymptotics
`C N^{−λ*}(log N)^{m*−1}` with `C > 0` (`exists_tendsto_monoBoxIntegral`), since the wall data of
`P₀` is the chart data at the origin (`pairs_eq_pairData`); and the normalised partition function
converges to the coefficient (CDXXXIX), so the coefficient is at least `cC > 0`.

Non-claims: no formula for the leading coefficient; realisation and prior positivity are
hypotheses (the extremal pair of a compact zero fibre is always realised, but this is not
formalised here).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The orthant box `(0, ε]^d`. -/
def orthant (d : ℕ) (ε : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ : Fin d => Ioc 0 ε

theorem measurableSet_orthant (d : ℕ) (ε : ℝ) : MeasurableSet (orthant d ε) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem mem_orthant {ε : ℝ} {u : Fin d → ℝ} : u ∈ orthant d ε ↔ ∀ j, 0 < u j ∧ u j ≤ ε := by
  rw [orthant, Set.mem_univ_pi]
  rfl

theorem orthant_subset_centeredBox {ε a : ℝ} (hεa : ε ≤ a) : orthant d ε ⊆ centeredBox d a := by
  intro u hu j
  have := (mem_orthant.1 hu) j
  rw [abs_of_pos this.1]
  exact this.2.trans hεa

theorem prod_pow_pos_of_mem_orthant {ε : ℝ} {u : Fin d → ℝ} (hu : u ∈ orthant d ε)
    (g : Fin d → ℕ) : 0 < ∏ j, u j ^ g j :=
  Finset.prod_pos fun j _ => pow_pos ((mem_orthant.1 hu) j).1 _

theorem monoBoxIntegral_eq_setIntegral (k h : Fin d → ℕ) (ε N : ℝ) :
    monoBoxIntegral k h ε N =
      ∫ u in orthant d ε, (∏ j, u j ^ h j) * Real.exp (-N * ∏ j, u j ^ (2 * k j)) := rfl

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

section Chart

variable (E : EvenChartBox Ξ.R)

theorem orthant_subset_target {ε : ℝ} (hε : ε ≤ E.r) : orthant d ε ⊆ E.φ.target :=
  (orthant_subset_centeredBox hε).trans E.inner_box_subset

theorem centeredBox_subset_target {ε : ℝ} (hε : ε ≤ E.r) : centeredBox d ε ⊆ E.φ.target :=
  fun _ hu => E.inner_box_subset fun j => (hu j).trans hε

/-- **Change of variables on the orthant box**: the chart representative is injective and
differentiable on `(0, ε]^d` with Jacobian `b(u) ∏ u^h`. -/
theorem integral_image_orthant {ε : ℝ} (hε : ε ≤ E.r) (g : (Fin d → ℝ) → ℝ) :
    ∫ y in watanabeRep Ξ.R.g E.φ '' orthant d ε, g y =
      ∫ u in orthant d ε, |E.b u| * (∏ j, u j ^ E.h j) * g (watanabeRep Ξ.R.g E.φ u) := by
  have hsub := Ξ.orthant_subset_target E hε
  have hsub' : orthant d ε ⊆ {u | u ∈ E.φ.target ∧ Ξ.K (watanabeRep Ξ.R.g E.φ u) ≠ 0} := by
    intro u hu
    refine ⟨hsub hu, ?_⟩
    rw [E.phase_eq u (hsub hu)]
    exact (prod_pow_pos_of_mem_orthant hu _).ne'
  have hinj : InjOn (watanabeRep Ξ.R.g E.φ) (orthant d ε) := E.injOn_offZero.mono hsub'
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_orthant d ε)
    (f' := fun u => fderiv ℝ (watanabeRep Ξ.R.g E.φ) u)
    (fun u hu => ((E.analyticOnNhd_rep u (hsub hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt)
    hinj g]
  refine setIntegral_congr_fun (measurableSet_orthant d ε) fun u hu => ?_
  rw [E.jac_eq u (hsub hu), smul_eq_mul, abs_mul, abs_of_pos (prod_pow_pos_of_mem_orthant hu _)]

/-- **The lower bound on the partition function** by the monomial integral of the chart. -/
theorem Z_one_ge_mul_monoBoxIntegral {ε : ℝ} (hε : ε ≤ E.r) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u ∈ orthant d ε, c ≤ |E.b u| * Ξ.prior (watanabeRep Ξ.R.g E.φ u)) {N : ℝ}
    (hN : 0 ≤ N) :
    c * monoBoxIntegral E.k E.h ε N ≤ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N := by
  rw [Ξ.Z_one N]
  unfold partitionObs
  have hsub := Ξ.orthant_subset_target E hε
  have hcb := Ξ.centeredBox_subset_target E hε
  have hint : Integrable fun y => Ξ.prior y * 1 * Real.exp (-N * Ξ.K y) := by
    refine Ξ.integrable_prior.mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((Ξ.prior_smooth.continuous.mul continuous_const).aestronglyMeasurable).mul
        (Real.measurable_exp.comp (measurable_const.mul Ξ.K_m)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, mul_one, abs_mul, abs_of_nonneg (Ξ.prior_nonneg y),
        abs_of_pos (Real.exp_pos _)]
      by_cases hy : y ∈ tsupport Ξ.prior
      · have hK := Ξ.hK0 y (Ξ.prior_W hy)
        calc Ξ.prior y * Real.exp (-N * Ξ.K y) ≤ Ξ.prior y * 1 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith)) (Ξ.prior_nonneg y)
          _ = Ξ.prior y := mul_one _
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hnn : 0 ≤ᵐ[volume] fun y => Ξ.prior y * 1 * Real.exp (-N * Ξ.K y) :=
    Eventually.of_forall fun y =>
      mul_nonneg (mul_nonneg (Ξ.prior_nonneg y) zero_le_one) (Real.exp_pos _).le
  have hcont : ContinuousOn (fun u => |E.b u| * (∏ j, u j ^ E.h j) *
      (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * 1 * Real.exp (-N * ∏ j, u j ^ (2 * E.k j))))
      (centeredBox d ε) := by
    have hb : ContinuousOn E.b (centeredBox d ε) := E.b_analytic.continuousOn.mono hcb
    have hrep : ContinuousOn (watanabeRep Ξ.R.g E.φ) (centeredBox d ε) :=
      E.analyticOnNhd_rep.continuousOn.mono hcb
    have h1 : Continuous fun u : Fin d → ℝ => ∏ j, u j ^ E.h j := by fun_prop
    have h2 : Continuous fun u : Fin d → ℝ => Real.exp (-N * ∏ j, u j ^ (2 * E.k j)) := by
      fun_prop
    exact (hb.abs.mul h1.continuousOn).mul
      (((Ξ.prior_smooth.continuous.comp_continuousOn hrep).mul continuousOn_const).mul
        h2.continuousOn)
  calc c * monoBoxIntegral E.k E.h ε N
      = ∫ u in orthant d ε, c * ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j))) := by
        rw [monoBoxIntegral_eq_setIntegral, integral_const_mul]
    _ ≤ ∫ u in orthant d ε, |E.b u| * (∏ j, u j ^ E.h j) *
          (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * 1 *
            Real.exp (-N * Ξ.K (watanabeRep Ξ.R.g E.φ u))) := by
        refine integral_mono_of_nonneg
          (ae_restrict_of_forall_mem (measurableSet_orthant d ε) fun u hu => ?_) ?_
          (ae_restrict_of_forall_mem (measurableSet_orthant d ε) fun u hu => ?_)
        · exact mul_nonneg hc0
            (mul_nonneg (prod_pow_pos_of_mem_orthant hu _).le (Real.exp_pos _).le)
        · refine ((hcont.integrableOn_compact (isCompact_centeredBox d ε)).mono_set
            (orthant_subset_centeredBox le_rfl)).congr_fun ?_ (measurableSet_orthant d ε)
          intro u hu
          simp only
          rw [E.phase_eq u (hsub hu)]
        · beta_reduce
          have hP := prod_pow_pos_of_mem_orthant hu E.h
          have hE := Real.exp_pos (-N * Ξ.K (watanabeRep Ξ.R.g E.φ u))
          rw [E.phase_eq u (hsub hu)] at hE ⊢
          calc c * ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j)))
              ≤ (|E.b u| * Ξ.prior (watanabeRep Ξ.R.g E.φ u)) *
                  ((∏ j, u j ^ E.h j) * Real.exp (-N * ∏ j, u j ^ (2 * E.k j))) :=
                mul_le_mul_of_nonneg_right (hc u hu) (mul_pos hP hE).le
            _ = _ := by ring
    _ = ∫ y in watanabeRep Ξ.R.g E.φ '' orthant d ε, Ξ.prior y * 1 * Real.exp (-N * Ξ.K y) :=
        (Ξ.integral_image_orthant E hε fun y => Ξ.prior y * 1 * Real.exp (-N * Ξ.K y)).symm
    _ ≤ ∫ y, Ξ.prior y * 1 * Real.exp (-N * Ξ.K y) := setIntegral_le_integral hint hnn

/-- **The positive lower bound of the chart density** `|b| · prior ∘ π ∘ φ⁻¹` on a small orthant
box, from positivity of the prior at the centre. -/
theorem exists_orthant_bound {P₀ : Ξ.R.U} (hP : P₀ ∈ E.φ.source) (hP0 : E.φ P₀ = 0)
    (hprior : 0 < Ξ.prior (Ξ.R.gv P₀)) :
    ∃ ε c : ℝ, 0 < ε ∧ ε ≤ E.r ∧ 0 < c ∧
      ∀ u ∈ orthant d ε, c ≤ |E.b u| * Ξ.prior (watanabeRep Ξ.R.g E.φ u) := by
  set G : (Fin d → ℝ) → ℝ := fun u => |E.b u| * Ξ.prior (watanabeRep Ξ.R.g E.φ u) with hG
  have h0 : watanabeRep Ξ.R.g E.φ 0 = Ξ.R.gv P₀ := by
    change Ξ.R.gv (E.φ.symm 0) = _
    rw [← hP0, E.φ.left_inv hP]
  have hG0 : 0 < G 0 := by
    simp only [hG]
    rw [h0]
    exact mul_pos (abs_pos.2 (E.b_ne_zero 0 E.zero_mem.1)) hprior
  have hGc : ContinuousAt G 0 := by
    refine ((E.b_analytic 0 E.zero_mem.1).continuousAt.abs).mul ?_
    exact Ξ.prior_smooth.continuous.continuousAt.comp
      (E.analyticOnNhd_rep 0 E.zero_mem.1).continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hGc.eventually (lt_mem_nhds (half_lt_self hG0)))
  refine ⟨min (δ / 2) E.r, G 0 / 2, lt_min (half_pos hδ) E.r_pos, min_le_right _ _,
    half_pos hG0, fun u hu => ?_⟩
  have hu' : u ∈ Metric.closedBall (0 : Fin d → ℝ) (δ / 2) := by
    rw [closedBall_eq_centeredBox (half_pos hδ).le]
    exact orthant_subset_centeredBox (min_le_left _ _) hu
  exact (hball (Metric.closedBall_subset_ball (half_lt_self hδ) hu')).le

end Chart

/-- The resonance count at the centre of an even chart box, as a count of chart coordinates. -/
theorem resonanceCount_eq_card_of_centered (E : EvenChartBox Ξ.R) {P₀ : Ξ.R.U}
    (hP : P₀ ∈ E.φ.source) (hP0 : E.φ P₀ = 0) {lam : ℝ}
    (hlam : ∀ j, 0 < E.k j → 2 * (E.k j : ℝ) * lam ≤ E.h j + 1) :
    (Finset.univ.filter fun j => 0 < E.k j ∧ 2 * (E.k j : ℝ) * lam = E.h j + 1).card =
      resonanceCount Ξ.R Ξ.hK0 lam P₀ := by
  classical
  unfold resonanceCount
  rw [pairs_eq_pairData Ξ.R Ξ.hK0 E hP hP0]
  unfold pairData active
  rw [Multiset.filter_map, Multiset.card_map, Finset.card_def, Finset.filter_val,
    Finset.filter_val, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun j _ => ?_
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨hj, heq⟩
    exact ⟨⟨0, by rw [Nat.cast_zero, add_zero]; exact heq⟩, hj⟩
  · rintro ⟨⟨n, hn⟩, hj⟩
    dsimp only at hn
    have := hlam j hj
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact ⟨hj, by linarith⟩

/-- ★★★ **Positivity of the leading coefficient at a realised extremal pair**: if exactly
`m* ≥ 1` walls through a point `P₀` of the zero fibre resonate with `λ*` and the prior is
positive at `π(P₀)`, then `0 < 𝒯^U_{λ*,m*−1}[1]`. -/
theorem coeff_one_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) {P₀ : Ξ.R.U}
    (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) :
    0 < (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) := by
  obtain ⟨E, hEs, hE0⟩ := exists_centeredEvenChartBox Ξ.R Ξ.hK0 (show P₀ ∈ divisor Ξ.R from hP₀.2)
  have hpairs := pairs_eq_pairData Ξ.R Ξ.hK0 E hEs hE0
  have hmem : ∀ j, 0 < E.k j → (E.k j, E.h j) ∈ pairs Ξ.R Ξ.hK0 P₀ := fun j hj => by
    rw [hpairs]
    exact Multiset.mem_map.2 ⟨j, by rw [Finset.mem_val]; exact (mem_active E).2 hj, rfl⟩
  have hlam : ∀ j, 0 < E.k j → 2 * (E.k j : ℝ) * lam ≤ E.h j + 1 := fun j hj =>
    h.1 P₀ hP₀ _ (hmem j hj)
  have hm : (Finset.univ.filter fun j => 0 < E.k j ∧ 2 * (E.k j : ℝ) * lam = E.h j + 1).card = m :=
    (Ξ.resonanceCount_eq_card_of_centered E hEs hE0 hlam).trans hres
  obtain ⟨ε, c, hε, hεr, hc0, hc⟩ := Ξ.exists_orthant_bound E hEs hE0 hprior
  obtain ⟨C, hC, hlimI⟩ := exists_tendsto_monoBoxIntegral E.k E.h
    (fun _ hj => E.h_eq_zero_of_k_eq_zero hj) hε hlam hm hm1
  have hlimZ := Ξ.tendsto_normalised_Z_of_extremalData Y h (G := fun _ => (1 : ℝ)) contMDiff_const
  refine lt_of_lt_of_le (mul_pos hc0 hC) (le_of_tendsto_of_tendsto (hlimI.const_mul c) hlimZ ?_)
  filter_upwards [eventually_gt_atTop 1] with N hN
  unfold normalised
  have hpos : 0 ≤ N ^ lam / Real.log N ^ (m - 1) :=
    div_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN.le) _)
  calc c * (N ^ lam / Real.log N ^ (m - 1) * monoBoxIntegral E.k E.h ε N)
      = N ^ lam / Real.log N ^ (m - 1) * (c * monoBoxIntegral E.k E.h ε N) := by ring
    _ ≤ N ^ lam / Real.log N ^ (m - 1) * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).Z N :=
        mul_le_mul_of_nonneg_left
          (Ξ.Z_one_ge_mul_monoBoxIntegral E hεr hc0.le hc (by linarith)) hpos

/-- ★★★ **The realised extremal pair is the leading index of the partition function**: the
leading-index hypothesis of CDXXXIV holds unconditionally at a realised extremal pair with
positive prior. -/
theorem isLeadingIndexOne_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) :
    Ξ.IsLeadingIndexOne Y lam (m - 1) :=
  ⟨fun _ _ hp => (Ξ.withF _ contMDiff_const).coeff_eq_zero_of_precedes Y
      (Ξ.isExtremalData_withF h _ contMDiff_const) hp,
    (Ξ.coeff_one_pos_of_realised Y h hP₀ hprior hres hm1).ne'⟩

end ResolvedData

end SmoothEngine

end Grammar
