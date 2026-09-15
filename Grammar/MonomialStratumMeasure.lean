/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialResolvedData

/-!
# Regression: the leading stratum measure of `∏ x_i^{2κ}` is a point mass at the origin

For the equal-exponent monomial phase `K = ∏ x_i^{2κ}` (`κ > 0`; `x²y²` is `d = 2, κ = 1`) the
extremal data are `λ* = 1/(2κ)`, `m* = d`. The depth never exceeds `d`, so the deep zero fibre
`D_{d+1}` is empty and every observable is admissible; the exact stratum `S^{λ*}_d` is the origin.
The leading stratum measure `ν^{λ*}_d` is therefore carried by the origin and is the point mass
`c · δ₀` with `c = 𝒯^U_{λ*,d−1}[1] > 0` the RLCT constant (`extremalStratumMeasure_eq_smul_dirac`),
and for every smooth `f` on `ℝ^d`
`N^{λ*} (log N)^{−(d−1)} ∫ φ f e^{−NK} → c · f(0)` (`tendsto_normalised_partitionObs_equal`):
the leading coefficient of every insertion is its value at the crossing times the RLCT constant,
the residue reading of the `x²y²` example. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

section Equal

variable {d : ℕ} (κ : ℕ) (W : TopologicalSpace.Opens (Fin d → ℝ))
  {prior : (Fin d → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
  (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ)))

/-- The equal-exponent data `k_i = κ`. -/
abbrev equalExp (d κ : ℕ) : Fin d → ℕ := fun _ => κ

theorem kmax_equal [Nonempty (Fin d)] : kmax (equalExp d κ) = κ := by
  obtain ⟨i, hi⟩ := exists_eq_kmax (equalExp d κ)
  exact hi.symm

theorem mstar_equal [Nonempty (Fin d)] : mstar (equalExp d κ) = d := by
  unfold mstar
  rw [kmax_equal]
  simp

theorem exists_pos_equal (hκ : 0 < κ) [Nonempty (Fin d)] : ∃ i, 0 < equalExp d κ i :=
  ⟨Classical.arbitrary _, hκ⟩

/-- The deep zero fibre of depth `d + 1` is empty: the depth never exceeds the dimension. -/
theorem deepZeroFibre_equal_eq_empty :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).deepZeroFibre d = ∅ := by
  ext P
  simp only [ResolvedData.deepZeroFibre, mem_inter_iff, depthGE, mem_ofPred_eq, mem_empty_iff_false,
    iff_false, not_and, not_le]
  intro _
  exact Nat.lt_succ_of_le (depth_le_dim _ _ P)

/-- A point of the exact stratum `S^{λ*}_d` has all coordinates zero. -/
theorem exactStratum_equal_subset [Nonempty (Fin d)] :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).exactStratum (lamStar (equalExp d κ)) d ⊆
      {P | P.1 = 0} := by
  intro P hP
  obtain ⟨hZ, hdepth, -⟩ := hP
  have hd : depth (WatanabeModificationOn.ofMonomial (equalExp d κ) W) (monoK0 _ W) P = d := hdepth
  rw [depth_ofMonomial _ W P hZ.2] at hd
  have hall : zeroActive (equalExp d κ) P.1 = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hd, Fintype.card_fin])
  funext i
  have hi : i ∈ zeroActive (equalExp d κ) P.1 := by rw [hall]; exact Finset.mem_univ i
  exact ((mem_zeroActive _).1 hi).1

/-- The origin of `W`, as a point of the stratum open set (which is all of `U`). -/
def originX (h0W : (0 : Fin d → ℝ) ∈ W) :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).stratumOpen d :=
  ⟨originPt (equalExp d κ) W hps hp0 hpc hpW h0W, by
    rw [ResolvedData.stratumOpen, deepZeroFibre_equal_eq_empty]
    simp⟩

variable (hκ : 0 < κ) (h0W : (0 : Fin d → ℝ) ∈ W) (hp : 0 < prior 0)

include hκ in
/-- The extremal data of the equal-exponent phase. -/
theorem isExtremalData_equal [Nonempty (Fin d)] :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).IsExtremalData (lamStar (equalExp d κ)) d := by
  have h := isExtremalData_monomial (equalExp d κ) W hps hp0 hpc hpW (exists_pos_equal κ hκ)
  rwa [mstar_equal] at h

theorem one_le_dim [Nonempty (Fin d)] : 1 ≤ d := Fin.pos (Classical.arbitrary (Fin d))

include hκ in
/-- The leading stratum measure of the equal-exponent phase. -/
noncomputable def equalMeasure [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    Measure ((monomialData (equalExp d κ) W hps hp0 hpc hpW).stratumOpen d) :=
  (monomialData (equalExp d κ) W hps hp0 hpc hpW).extremalStratumMeasure Y
    (isExtremalData_equal κ W hps hp0 hpc hpW hκ) one_le_dim

/-- ★★★ **The leading stratum measure is carried by the origin.** -/
theorem equalMeasure_compl_origin [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure κ W hps hp0 hpc hpW hκ Y {originX κ W hps hp0 hpc hpW h0W}ᶜ = 0 := by
  refine measure_mono_null ?_
    ((monomialData (equalExp d κ) W hps hp0 hpc hpW).stratumMeasure_compl_exactStratum Y one_le_dim
      ((monomialData (equalExp d κ) W hps hp0 hpc hpW).zeroOrder_of_extremalData
        (isExtremalData_equal κ W hps hp0 hpc hpW hκ) d))
  intro x hx hxE
  apply hx
  have h0 : x.1.1 = 0 := exactStratum_equal_subset κ W hps hp0 hpc hpW hxE
  rw [mem_singleton_iff]
  apply Subtype.ext
  apply Subtype.ext
  exact h0

/-- ★★★ **The leading stratum measure of `∏ x_i^{2κ}` is the point mass `c · δ₀`** with
`c = 𝒯^U_{λ*,d−1}[1]` the RLCT constant. -/
theorem equalMeasure_eq_smul_dirac [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure κ W hps hp0 hpc hpW hκ Y =
      ENNReal.ofReal (((monomialData (equalExp d κ) W hps hp0 hpc hpW).withF (fun _ => (1 : ℝ))
        contMDiff_const).coeff Y (lamStar (equalExp d κ)) (d - 1)) •
        Measure.dirac (originX κ W hps hp0 hpc hpW h0W) := by
  set ν := equalMeasure κ W hps hp0 hpc hpW hκ Y with hν
  set x₀ := originX κ W hps hp0 hpc hpW h0W with hx₀
  have hnull : ν {x₀}ᶜ = 0 := equalMeasure_compl_origin κ W hps hp0 hpc hpW hκ h0W Y
  have hext := isExtremalData_equal κ W hps hp0 hpc hpW hκ
  have hmass : ν univ = ENNReal.ofReal (((monomialData (equalExp d κ) W hps hp0 hpc hpW).withF
      (fun _ => (1 : ℝ)) contMDiff_const).coeff Y (lamStar (equalExp d κ)) (d - 1)) := by
    change ((monomialData (equalExp d κ) W hps hp0 hpc hpW).extremalStratumMeasure Y hext
      one_le_dim) univ = _
    have h := (monomialData (equalExp d κ) W hps hp0 hpc hpW)
      |>.extremalStratumMeasure_univ_eq_of_deep_empty Y hext one_le_dim
        (deepZeroFibre_equal_eq_empty κ W hps hp0 hpc hpW)
    have hfin : ((monomialData (equalExp d κ) W hps hp0 hpc hpW).extremalStratumMeasure Y hext
        one_le_dim) univ ≠ ⊤ :=
      (((monomialData (equalExp d κ) W hps hp0 hpc hpW).extremalStratumMeasure_univ_le Y hext
        one_le_dim).trans_lt ENNReal.ofReal_lt_top).ne
    rw [← h, measureReal_def, ENNReal.ofReal_toReal hfin]
  ext s hs
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, ← hmass, smul_eq_mul]
  by_cases hx : x₀ ∈ s
  · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
    have h1 : ν s = ν (s ∩ {x₀}ᶜ) + ν (s ∩ {x₀}) := by
      rw [← measure_inter_add_sdiff s (measurableSet_singleton x₀).compl, Set.sdiff_eq, compl_compl]
    have h2 : ν univ = ν (univ ∩ {x₀}ᶜ) + ν (univ ∩ {x₀}) := by
      rw [← measure_inter_add_sdiff univ (measurableSet_singleton x₀).compl, Set.sdiff_eq,
        compl_compl]
    rw [h1, h2, measure_mono_null inter_subset_right hnull, measure_mono_null inter_subset_right
      hnull, zero_add, zero_add, univ_inter, inter_eq_right.2 (singleton_subset_iff.2 hx)]
  · rw [indicator_of_notMem hx, mul_zero]
    refine measure_mono_null (fun y hy => ?_) hnull
    intro hy'
    rw [mem_singleton_iff] at hy'
    exact hx (hy' ▸ hy)

include hps hp0 hpc hpW hκ h0W hp in
/-- ★★★ **The leading coefficient of every insertion is its value at the crossing**:
`N^{λ*} (log N)^{−(d−1)} ∫ φ f e^{−N ∏ x^{2κ}} → c · f(0)`. -/
theorem tendsto_normalised_partitionObs_equal [Nonempty (Fin d)] {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (normalised (lamStar (equalExp d κ)) (d - 1)
      (partitionObs (monoPhase (equalExp d κ)) prior f)) atTop (𝓝 (c * f 0)) := by
  set Ξ := monomialData (equalExp d κ) W hps hp0 hpc hpW with hΞ
  obtain ⟨Y⟩ := WatanabeModificationOn.exists_resolvedCoreTransport_of_modification Ξ.R Ξ.hK0
    Ξ.hKc Ξ.prior_smooth.continuous.measurable Ξ.prior_nonneg Ξ.prior_compact Ξ.prior_W
  have hext := isExtremalData_equal κ W hps hp0 hpc hpW hκ
  have hc := Ξ.coeff_one_pos_of_realised Y hext
    (originPt_mem_zeroFibre (equalExp d κ) W hps hp0 hpc hpW (exists_pos_equal κ hκ) h0W hp) hp
    (by rw [resonanceCount_monomial_zero (equalExp d κ) W hps hp0 hpc hpW (exists_pos_equal κ hκ)
      h0W, mstar_equal]) one_le_dim
  refine ⟨_, hc, ?_⟩
  have h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre d), f (Ξ.R.gv P) = 0 := by
    rw [deepZeroFibre_equal_eq_empty, nhdsSet_empty]
    exact Filter.eventually_bot
  have hlim := Ξ.tendsto_normalised_partitionObs_extremal Y hf hext one_le_dim h0
  have hint : ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y hext one_le_dim) =
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y (lamStar (equalExp d κ)) (d - 1) *
        f 0 := by
    change ∫ x, f (Ξ.R.gv x.1) ∂(equalMeasure κ W hps hp0 hpc hpW hκ Y) = _
    rw [equalMeasure_eq_smul_dirac κ W hps hp0 hpc hpW hκ h0W Y, integral_smul_measure,
      integral_dirac, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    rfl
  rwa [hint] at hlim

end Equal

end SmoothEngine

end Grammar
