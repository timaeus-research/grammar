/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialChartProductBox

/-!
# The explicit leading coefficient of the box integral of a monomial chart (CCLXXI)

For a monomial chart `(φ, dom, e, h, W)` (hironaka's `IsMonomialChart`) at a divisor point `y₀`
(`monomialEval y₀ e = 0`), with a box radius `ρ` such that `closedBall y₀ ρ ⊆ restrictNhd` and the
observable–prior product positive on `φ(closedBall y₀ ρ)`, the box integral

`∫_{φ(productBox e y₀ ρ)} F p e^{−NK} ~ c · N^{−λ*} (log N)^{k*}`, `c > 0`,

where `(λ*, k*) = (min_{j∈J₀} (h_j+1)/e_j, #minimisers − 1)` is the divisor pair of the box package
and `c = productCoeffV (boxPackage)` — the explicit tied-face coefficient of CCLX/CCLXVII (the
residual face formula `tiedSum_residual_of_data` applies to it). The positivity input is
★ `dominantFace_pos`: the dominant face of the extremal stratum contains a nonempty open set of
the base (feet in the interior of the box with the residual coordinates in `(ε, ρ)` and the
tangential Jacobian coordinates nonzero), hence has positive measure.

This upgrades CCV's identified leading term (`IsMonomialChart.local_leading_term`, with an
opaque constant) to an explicit-coefficient statement for every monomial chart at every divisor
point (consult #84 unit 4); the coefficient is that of the region `φ(productBox)`, not of a
small ball.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

section Local

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W) {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W)
  {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W)

/-- The one-chart cover of the box. -/
noncomputable abbrev boxCover : ResolutionCover d Unit :=
  ResolutionCover.ofChart (IsMonomialChart.boxChart hc hρ hball)

/-- The box package as a family over the one-chart cover. -/
noncomputable abbrev boxPs : ∀ i : Unit, ProductMonomialChartVar (boxCover hc hρ hball) i K :=
  fun _ => IsMonomialChart.boxPackage hc hρ hball

include hc hρ hball in
theorem boxPs_e_support : (boxPs hc hρ hball ()).e.support = divisorSet e y₀ :=
  IsMonomialChart.boxPackage_e_support hc hρ hball

include hc hρ hball in
theorem boxPs_h : (boxPs hc hρ hball ()).h = h := rfl

include hc hρ hball in
theorem boxPs_pieceWeight (x : Fin d → ℝ) : (boxPs hc hρ hball ()).pieceWeight x = 1 := rfl

include hc hρ hball in
theorem boxPs_ratio {j : Fin d} (hj : j ∈ divisorSet e y₀) :
    (boxPs hc hρ hball ()).ratio j = ((h j : ℝ) + 1) / (e j : ℝ) := by
  unfold ProductMonomialChartVar.ratio
  rw [boxPs_h]
  change ((h j : ℝ) + 1) / ((restrictExp e (divisorSet e y₀) j : ℕ) : ℝ) = _
  rw [restrictExp, Finsupp.filter_apply_pos _ _ hj]

/-! ### The dominant face has positive measure -/

/-- A witness foot: the residual active coordinates at `3ρ/4`, the vanishing tangential Jacobian
coordinates at `ρ/2`, the minimal normal coordinates at `0`, all others at `y₀`. -/
noncomputable def witnessFoot (e h : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) (I₀ : Finset (Fin d)) :
    Fin d → ℝ := fun j =>
  if j ∈ I₀ then 0
  else if j ∈ divisorSet e y₀ then 3 * ρ / 4
  else if y₀ j = 0 ∧ j ∈ h.support then ρ / 2 else y₀ j

/-- The open target conditions of the dominant face. -/
def faceOpen (e h : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ ε : ℝ) (I₀ : Finset (Fin d)) :
    Set (Fin d → ℝ) :=
  (⋂ j ∈ divisorSet e y₀ \ I₀, {y : Fin d → ℝ | ε < |y j| ∧ |y j| < ρ}) ∩
    (⋂ j ∈ Finset.univ \ divisorSet e y₀, {y : Fin d → ℝ | |y j - y₀ j| < ρ}) ∩
    ⋂ j ∈ h.support \ I₀, {y : Fin d → ℝ | y j ≠ 0}

theorem isOpen_faceOpen (e h : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ ε : ℝ) (I₀ : Finset (Fin d)) :
    IsOpen (faceOpen e h y₀ ρ ε I₀) := by
  refine ((isOpen_biInter_finset fun j _ => ?_).inter (isOpen_biInter_finset fun j _ => ?_)).inter
    (isOpen_biInter_finset fun j _ => ?_)
  · exact (isOpen_lt continuous_const (continuous_abs.comp (continuous_apply j))).inter
      (isOpen_lt (continuous_abs.comp (continuous_apply j)) continuous_const)
  · exact isOpen_lt (continuous_abs.comp ((continuous_apply j).sub continuous_const))
      continuous_const
  · exact isOpen_ne_fun (continuous_apply j) continuous_const

theorem mem_faceOpen {ε : ℝ} {I₀ : Finset (Fin d)} {y : Fin d → ℝ} :
    y ∈ faceOpen e h y₀ ρ ε I₀ ↔
      (∀ j ∈ divisorSet e y₀, j ∉ I₀ → ε < |y j| ∧ |y j| < ρ) ∧
      (∀ j, j ∉ divisorSet e y₀ → |y j - y₀ j| < ρ) ∧
      ∀ j ∈ h.support, j ∉ I₀ → y j ≠ 0 := by
  unfold faceOpen
  simp only [mem_inter_iff, mem_iInter, Finset.mem_sdiff, Finset.mem_univ, true_and, and_imp,
    mem_ofPred_eq, and_assoc]

include hρ in
/-- The witness foot lies in the open face conditions (with `ε = ρ/2`). -/
theorem witnessFoot_mem_faceOpen {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ divisorSet e y₀) :
    witnessFoot e h y₀ ρ I₀ ∈ faceOpen e h y₀ ρ (ρ / 2) I₀ := by
  refine mem_faceOpen.2 ⟨fun j hj hjI => ?_, fun j hj => ?_, fun j hj hjI => ?_⟩
  · simp only [witnessFoot, if_neg hjI, if_pos hj, abs_of_pos (by positivity : (0 : ℝ) < 3 * ρ / 4)]
    constructor <;> linarith
  · have hjI : j ∉ I₀ := fun h' => hj (hI₀ h')
    simp only [witnessFoot, if_neg hjI, if_neg hj]
    split_ifs with h0
    · rw [h0.1, sub_zero, abs_of_pos (half_pos hρ)]
      linarith
    · rw [sub_self, abs_zero]
      exact hρ
  · simp only [witnessFoot, if_neg hjI]
    split_ifs with h1 h2
    · positivity
    · exact (by positivity : (0 : ℝ) < ρ / 2).ne'
    · intro h0
      exact h2 ⟨h0, hj⟩

/-- The witness foot vanishes on the stratum. -/
theorem witnessFoot_zero {I₀ : Finset (Fin d)} {j : Fin d} (hj : j ∈ I₀) :
    witnessFoot e h y₀ ρ I₀ j = 0 := by
  simp only [witnessFoot, if_pos hj]

include hc hρ hball in
/-- **The dominant face of an extremal stratum of the box has positive measure**, provided the
observable and the prior are positive on the box: it contains a nonempty open set of feet. -/
theorem dominantFace_pos {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFp : ∀ y ∈ Metric.closedBall y₀ ρ, 0 < F (φ y) ∧ 0 < p.w (φ y))
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (boxPs hc hρ hball ()).e.support) (hne₀ : I₀.Nonempty) :
    0 < volume ((boxPs hc hρ hball ()).dominantFace (fun i => (boxPs hc hρ hball i).e.support)
      (ρ / 2) I₀ hne₀ F p) := by
  rw [boxPs_e_support] at hI₀
  set τ := stratumSplit I₀ hne₀ with hτ
  -- the continuous foot map
  have hg : Continuous fun z : Fin (d - (I₀.card - 1 + 1)) → ℝ => planeSplit τ (z, 0) :=
    (planeSplit τ).continuous.comp (continuous_id.prodMk continuous_const)
  -- the open set of feet
  set U : Set (Fin (d - (I₀.card - 1 + 1)) → ℝ) :=
    (fun z => planeSplit τ (z, 0)) ⁻¹' faceOpen e h y₀ ρ (ρ / 2) I₀ with hU
  have hUopen : IsOpen U := (isOpen_faceOpen e h y₀ ρ (ρ / 2) I₀).preimage hg
  -- the witness foot is a foot
  have hfoot : planeSplit τ (((planeSplit τ).symm (witnessFoot e h y₀ ρ I₀)).1, 0) =
      witnessFoot e h y₀ ρ I₀ := by
    have h1 := planeFoot_planeSplit τ ((planeSplit τ).symm (witnessFoot e h y₀ ρ I₀)).1
      ((planeSplit τ).symm (witnessFoot e h y₀ ρ I₀)).2
    rw [ContinuousLinearEquiv.apply_symm_apply, hτ, planeFoot_eq_zeroOn] at h1
    rw [← h1, zeroOn_of_forall_eq_zero _ fun j hj => witnessFoot_zero hj]
  have hUne : U.Nonempty := ⟨_, by
    change planeSplit τ (_, 0) ∈ faceOpen e h y₀ ρ (ρ / 2) I₀
    rw [hfoot]
    exact witnessFoot_mem_faceOpen hρ hI₀⟩
  -- feet vanish on the stratum
  have hzero : ∀ (z : Fin (d - (I₀.card - 1 + 1)) → ℝ) {j : Fin d}, j ∈ I₀ →
      planeSplit τ (z, 0) j = 0 := fun z j hj => by
    obtain ⟨a, rfl⟩ := exists_inr_of_mem I₀ hne₀ hj
    rw [hτ, planeSplit_stratum_inr]
    rfl
  -- the open set lies in the dominant face
  have hsub : U ⊆ (boxPs hc hρ hball ()).dominantFace (fun i => (boxPs hc hρ hball i).e.support)
      (ρ / 2) I₀ hne₀ F p := by
    intro z hz
    have hy := mem_faceOpen.1 hz
    set y := planeSplit τ (z, 0) with hydef
    -- the foot lies in the box
    have hbox : y ∈ productBox e y₀ ρ := by
      refine And.intro ?_ fun j hj => ?_
      · rw [support_restrictExp_divisor]
        intro j _
        by_cases hjD : j ∈ divisorSet e y₀
        · simp only [zeroOn_apply_of_mem _ hjD, if_pos hjD, mem_singleton_iff]
        · simp only [zeroOn_apply_of_notMem _ hjD, if_neg hjD, mem_Icc]
          have := hy.2.1 j hjD
          rw [abs_lt] at this
          constructor <;> linarith [this.1, this.2]
      · rw [support_restrictExp_divisor] at hj
        by_cases hjI : j ∈ I₀
        · have hz0 := hzero z hjI
          rw [← hydef] at hz0
          rw [hz0, abs_zero]
          exact hρ.le
        · exact (hy.1 j hj hjI).2.le
    have hyW : y ∈ W :=
      restrictNhd_subset _ _ _ (productBox_subset_restrictNhd hρ hball hbox)
    have hyB : y ∈ Metric.closedBall y₀ ρ := productBox_subset_closedBall hρ hbox
    refine ⟨fun j hj hjI hlt => ?_, hbox, ?_, (hFp y hyB).2, (hFp y hyB).1, ?_, ?_⟩
    · beta_reduce at hj
      rw [boxPs_e_support] at hj
      exact absurd hlt (not_lt.2 (hy.1 j hj hjI).1.le)
    · rw [boxPs_pieceWeight]
      exact one_pos
    · exact hc.exists_jacUnit.choose_spec.2.1 y hyW
    · rw [boxPs_h]
      unfold tangentialMonomial
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact pow_ne_zero _ (hy.2.2 j hj.1 hj.2)
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hsub)

/-! ### The explicit leading coefficient -/

include hc hρ hball in
/-- **The box integral of a monomial chart at a divisor point has an explicit positive leading
coefficient**: with `(λ*, k*)` the divisor pair of the box package and `c` its total tied-face
coefficient, `∫_{φ(productBox)} F p e^{−NK} ~ c · N^{−λ*} (log N)^{k*}`. -/
theorem IsMonomialChart.boxIntegral_isEquivalent (hK0 : ∀ x, 0 ≤ K x) (hK : Measurable K)
    (hdiv : monomialEval y₀ e = 0) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFc : ContinuousOn (fun y => F (φ y)) W) (hpc : ContinuousOn (fun y => p.w (φ y)) W)
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFint : IntegrableOn (fun x => F x * p.w x) (φ '' productBox e y₀ ρ))
    (hFp : ∀ y ∈ Metric.closedBall y₀ ρ, 0 < F (φ y) ∧ 0 < p.w (φ y)) :
    ∃ (hact : ((boxCover hc hρ hball).activeCoordsV (boxPs hc hρ hball)).Nonempty)
      (hF : Integrable (fun x => F x * p.w x)
        (volume.restrict (⋃ i, (boxCover hc hρ hball).image i))),
      0 < (boxCover hc hρ hball).productCoeffV (boxPs hc hρ hball) hK0 (half_pos hρ)
          (fun _ => (half_le_self hρ.le : ρ / 2 ≤ ρ))
          (fun _ => hFc.mono (restrictNhd_subset _ _ _))
          (fun _ => hpc.mono (restrictNhd_subset _ _ _)) hFm hF hK
          ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) hact)
          ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) hact) ∧
      (fun N : ℝ => ∫ x in φ '' productBox e y₀ ρ, F x * p.w x * Real.exp (-N * K x)) ~[atTop]
        fun N => (boxCover hc hρ hball).productCoeffV (boxPs hc hρ hball) hK0 (half_pos hρ)
          (fun _ => (half_le_self hρ.le : ρ / 2 ≤ ρ))
          (fun _ => hFc.mono (restrictNhd_subset _ _ _))
          (fun _ => hpc.mono (restrictNhd_subset _ _ _)) hFm hF hK
          ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) hact)
          ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) hact) *
          powLogScale ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) hact)
            ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) hact) N := by
  have hact : ((boxCover hc hρ hball).activeCoordsV (boxPs hc hρ hball)).Nonempty :=
    ((boxCover hc hρ hball).activeCoordsV_ofChart_nonempty_iff (boxPs hc hρ hball) ()).2
      (IsMonomialChart.boxPackage_isActive hc hρ hball hdiv)
  have hF : Integrable (fun x => F x * p.w x)
      (volume.restrict (⋃ i, (boxCover hc hρ hball).image i)) := by
    rw [ResolutionCover.ofChart_iUnion_image]
    exact hFint
  obtain ⟨i₀, I₀, hI₀, hne₀, hall, hdeg⟩ :=
    (boxCover hc hρ hball).exists_extremal_stratumV (boxPs hc hρ hball) hact
  have hmain := (boxCover hc hρ hball).boltzmannIntegral_isEquivalent_of_productChartsV_extremal
    (boxPs hc hρ hball) hK0 (half_pos hρ) (fun _ => (half_le_self hρ.le : ρ / 2 ≤ ρ))
    (fun _ => hFc.mono (restrictNhd_subset _ _ _)) (fun _ => hpc.mono (restrictNhd_subset _ _ _))
    hFm hF hK hact hF0 p.nonneg (fun _ _ => zero_le_one) i₀ I₀ hI₀ hne₀ hall hdeg
    (dominantFace_pos hc hρ hball hFp I₀ hI₀ hne₀)
  refine ⟨hact, hF, hmain.1, ?_⟩
  have hZ : (boxCover hc hρ hball).boltzmannIntegral F K p =
      fun N : ℝ => ∫ x in φ '' productBox e y₀ ρ, F x * p.w x * Real.exp (-N * K x) := by
    funext N
    rw [ResolutionCover.ofChart_boltzmannIntegral]
    rfl
  rw [hZ] at hmain
  exact hmain.2

end Local

end Grammar
