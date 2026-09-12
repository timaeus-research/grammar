/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LocalExplicitCoefficient
import Grammar.CompactSourceLocalization

/-!
# The whole-box source certificate (CCLXXXI)

The first unit of the derived-certificate programme (consult #86, A1). For hironaka's monomial
chart `IsMonomialChart K φ dom e h W`, a divisor point `y₀` and a box radius `ρ` with
`closedBall y₀ ρ ⊆ restrictNhd` (the admissibility of CCLXX), the **whole-box source integral**
`boxSourceIntegral G p N = ∫_{productBox e y₀ ρ} G · |det Dφ| · (p∘φ) · e^{−N K∘φ}` of a source
amplitude `G` continuous on the closed box — no product package as input, no compactly supported
extension of `G`, no shrinking of the box, no cutoff — is the source chart integral of the box
package (`boxSourceIntegral_eq`), hence carries the one-chart certificate with remainder identically
zero (`boxSourceDecomposition`), and:

* ★ `hasLeadingTerm_boxSourceIntegral`: the zero-compatible expansion
  `boxSourceIntegral = c · N^{−λ*}(log N)^{k*} + o(·)` at the divisor pair of the box, with
  `c = (boxPackage).sourceCoeff G λ* k*` (nonnegative for `G, p ≥ 0`);
* `sourceDominantFace_pos`: for `G` and `p∘φ` positive on the closed box, the source dominant face
  of every extremal stratum contains the open set of feet of CCLXXI;
* ★★ `boxSourceIntegral_isEquivalent`: `c > 0` and `boxSourceIntegral ~ c · N^{−λ*}(log N)^{k*}`.

This is the direct application of the box-package construction to the integral over the box, not
an application of the localisation of CCLXXVII to `G · 1_{box}` (which is discontinuous at the
boundary).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

section WholeBox

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W) {y₀ : Fin d → ℝ}
  {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W)

/-- **The whole-box source integral** `∫_{box} G · |det Dφ| · (p∘φ) · e^{−N K∘φ}`. -/
noncomputable def boxSourceIntegral (G : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y in productBox e y₀ ρ, G y * |(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))

include hc hρ hball in
/-- The whole-box source integral is the source chart integral of the box chart. -/
theorem boxSourceIntegral_eq (G : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    (boxCover hc hρ hball).sourceChartIntegral () G K p N =
      boxSourceIntegral (φ := φ) (K := K) (e := e) (y₀ := y₀) (ρ := ρ) G p N := by
  rw [ResolutionCover.ofChart_sourceChartIntegral]
  unfold ResolutionChart.jac boxSourceIntegral
  rfl

include hc hρ hball in
/-- **The whole-box certificate**: the one-chart source decomposition with remainder zero. -/
noncomputable def boxSourceDecomposition (G : (Fin d → ℝ) → ℝ) (p : TubeWeight d) :
    (boxCover hc hρ hball).SourceDecomposition (fun _ => G) K p
      (boxSourceIntegral (φ := φ) (K := K) (e := e) (y₀ := y₀) (ρ := ρ) G p) where
  rem := fun _ => 0
  decomp := fun N _ => by
    rw [add_zero, Fintype.sum_unique]
    exact (boxSourceIntegral_eq hc hρ hball G p N).symm

variable (hK0 : ∀ x, 0 ≤ K x) (hK : Measurable K) (hdiv : monomialEval y₀ e = 0)
  {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hpc : ContinuousOn (fun y => p.w (φ y)) W)
  (hGm : Measurable G) (hGc : ContinuousOn G (productBox e y₀ ρ))

include hc hρ hball hdiv in
/-- The box package is active at a divisor point. -/
theorem boxPs_hact : ((boxCover hc hρ hball).activeCoordsV (boxPs hc hρ hball)).Nonempty :=
  ((boxCover hc hρ hball).activeCoordsV_ofChart_nonempty_iff (boxPs hc hρ hball) ()).2
    (IsMonomialChart.boxPackage_isActive hc hρ hball hdiv)

include hc hρ hball hK0 hK hdiv hpc hGm hGc in
/-- **The whole-box source coefficient** at the divisor pair of the box. -/
noncomputable def boxSourceCoeff : ℝ :=
  (IsMonomialChart.boxPackage hc hρ hball).sourceCoeff hK0 (half_pos hρ)
    (half_le_self hρ.le : ρ / 2 ≤ ρ) (hpc.mono (restrictNhd_subset _ _ _)) hGm hGc hK
    ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv))
    ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv))

include hc hρ hball hK0 hK hdiv hpc hGm hGc in
/-- ★ **The zero-compatible expansion of the whole-box source integral** at the divisor pair of
the box. -/
theorem hasLeadingTerm_boxSourceIntegral :
    HasLeadingTerm (boxSourceIntegral (φ := φ) (K := K) (e := e) (y₀ := y₀) (ρ := ρ) G p)
      (boxSourceCoeff hc hρ hball hK0 hK hdiv hpc hGm hGc)
      ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv))
      ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv)) := by
  have h := (IsMonomialChart.boxPackage hc hρ hball).hasLeadingTerm_sourceChartIntegral_extremal
    hK0 (half_pos hρ) (half_le_self hρ.le : ρ / 2 ≤ ρ) (hpc.mono (restrictNhd_subset _ _ _)) hGm
    hGc hK (boxPs_hact hc hρ hball hdiv)
  have hZ : (boxCover hc hρ hball).sourceChartIntegral () G K p =
      boxSourceIntegral (φ := φ) (K := K) (e := e) (y₀ := y₀) (ρ := ρ) G p :=
    funext fun N => boxSourceIntegral_eq hc hρ hball G p N
  rw [hZ] at h
  exact h

include hc hρ hball hK0 hK hdiv hpc hGm hGc in
/-- The whole-box source coefficient is nonnegative for `G, p ≥ 0`. -/
theorem boxSourceCoeff_nonneg (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x) :
    0 ≤ boxSourceCoeff hc hρ hball hK0 hK hdiv hpc hGm hGc :=
  (IsMonomialChart.boxPackage hc hρ hball).sourceCoeff_nonneg hK0 (half_pos hρ) _ _ hGm hGc hK hG0
    hp0 (fun _ => zero_le_one) _ _

include hc hρ hball in
/-- **The source dominant face of an extremal stratum of the box has positive measure** when the
source amplitude and the prior are positive on the box: it contains the open set of feet of
CCLXXI. -/
theorem sourceDominantFace_pos {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hGp : ∀ y ∈ Metric.closedBall y₀ ρ, 0 < G y ∧ 0 < p.w (φ y))
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (boxPs hc hρ hball ()).e.support) (hne₀ : I₀.Nonempty) :
    0 < volume ((boxPs hc hρ hball ()).sourceDominantFace
      (fun i => (boxPs hc hρ hball i).e.support) (ρ / 2) I₀ hne₀ G p) := by
  rw [boxPs_e_support] at hI₀
  set τ := stratumSplit I₀ hne₀ with hτ
  have hg : Continuous fun z : Fin (d - (I₀.card - 1 + 1)) → ℝ => planeSplit τ (z, 0) :=
    (planeSplit τ).continuous.comp (continuous_id.prodMk continuous_const)
  set U : Set (Fin (d - (I₀.card - 1 + 1)) → ℝ) :=
    (fun z => planeSplit τ (z, 0)) ⁻¹' faceOpen e h y₀ ρ (ρ / 2) I₀ with hU
  have hUopen : IsOpen U := (isOpen_faceOpen e h y₀ ρ (ρ / 2) I₀).preimage hg
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
  have hzero : ∀ (z : Fin (d - (I₀.card - 1 + 1)) → ℝ) {j : Fin d}, j ∈ I₀ →
      planeSplit τ (z, 0) j = 0 := fun z j hj => by
    obtain ⟨a, rfl⟩ := exists_inr_of_mem I₀ hne₀ hj
    rw [hτ, planeSplit_stratum_inr]
    rfl
  have hsub : U ⊆ (boxPs hc hρ hball ()).sourceDominantFace
      (fun i => (boxPs hc hρ hball i).e.support) (ρ / 2) I₀ hne₀ G p := by
    intro z hz
    have hy := mem_faceOpen.1 hz
    set y := planeSplit τ (z, 0) with hydef
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
    refine ⟨fun j hj hjI hlt => ?_, hbox, ?_, (hGp y hyB).2, (hGp y hyB).1, ?_, ?_⟩
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

include hc hρ hball hK0 hK hdiv hpc hGm hGc in
/-- ★★ **The whole-box source integral has an explicit positive leading coefficient** when the
source amplitude and the prior are positive on the closed box. -/
theorem boxSourceIntegral_isEquivalent (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hGp : ∀ y ∈ Metric.closedBall y₀ ρ, 0 < G y ∧ 0 < p.w (φ y)) :
    0 < boxSourceCoeff hc hρ hball hK0 hK hdiv hpc hGm hGc ∧
      boxSourceIntegral (φ := φ) (K := K) (e := e) (y₀ := y₀) (ρ := ρ) G p ~[atTop] fun N =>
        boxSourceCoeff hc hρ hball hK0 hK hdiv hpc hGm hGc *
          powLogScale
            ((boxCover hc hρ hball).coverLamV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv))
            ((boxCover hc hρ hball).coverDegV (boxPs hc hρ hball) (boxPs_hact hc hρ hball hdiv))
            N := by
  obtain ⟨i₀, I₀, hI₀, hne₀, hall, hdeg⟩ :=
    (boxCover hc hρ hball).exists_extremal_stratumV (boxPs hc hρ hball)
      (boxPs_hact hc hρ hball hdiv)
  have hc' : 0 < boxSourceCoeff hc hρ hball hK0 hK hdiv hpc hGm hGc :=
    (IsMonomialChart.boxPackage hc hρ hball).sourceCoeff_pos hK0 (half_pos hρ) _ _ hGm hGc hK hG0
      hp0 (fun _ => zero_le_one) I₀ hI₀ hne₀ hall hdeg
      (sourceDominantFace_pos hc hρ hball hGp I₀ hI₀ hne₀)
  exact ⟨hc', (hasLeadingTerm_boxSourceIntegral hc hρ hball hK0 hK hdiv hpc hGm hGc).isEquivalent
    hc'.ne'⟩

end WholeBox

end Grammar
