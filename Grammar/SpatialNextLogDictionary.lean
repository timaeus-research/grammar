/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialIndependenceConverse

/-!
# The next-log observable dictionary with spatial phase (unit 376; Astra #46 unit 5)

One two-term quotient lemma (`quotient_second_order`) instantiated three times for
coefficient-family data with a spatial phase:

* **moments with observables** `E_{Q_N^ξ}[(NK)^r g(u)]`: the numerator is the chart integral with
  weight `h + 2rk`, exponent `λ + r`, amplitude `g η` (family `cg * cη`), so
  `L (E[(NK)^r g] − F_{r,g}/F) → (F B_{r,g} − F_{r,g} B)/F²` (`spatialMoment_twoTerm`), explicit
  for `m ≥ 2` (`spatialMoment_twoTerm_explicit`): the second coefficient is the finite-part
  face integral with `J_λ` replaced by `J_{λ+r}` and `η` by `g η`, the spatial weight unchanged;
* **energy Laplace transforms** `E[e^{-sNK}]`: temperature `β + s` and phase `ξ β/(β+s)`
  (family `(β/(β+s)) • cξ`), `L (E[e^{-sNK}] − F_s/F) → (F B_s − F_s B)/F²`
  (`spatialLaplace_twoTerm`);
* **evidence ratios** between two admissible phases,
  `L (𝒵_N[η;ξ']/𝒵_N[η;ξ] − F'/F) → (F B' − F' B)/F²` (`spatialEvidenceRatio_twoTerm`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-! ### Scalar multiples of coefficient families -/

theorem AbsSummable.const_smul {c : CoeffFamily d} (hc : AbsSummable c) (a : ℝ) :
    AbsSummable (a • c) := by
  unfold AbsSummable
  refine (hc.mul_left |a|).congr fun γ => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]

theorem evalF_const_smul (c : CoeffFamily d) (a : ℝ) (u : Fin d → ℝ) :
    evalF (a • c) u = a * evalF c u := by
  unfold evalF
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-! ### Moments with observables -/

/-- **Next-log correction of the posterior mixed moments** `E_{Q_N^ξ}[(NK)^r g(u)]`. -/
theorem spatialMoment_twoTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη cg : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (hg : AbsSummable cg) {ξ η g : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hgc : Continuous g) (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u)
    (hevg : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cg u = g u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : spatialFace h k l β ξ η ≠ 0) (r : ℕ) :
    Tendsto (fun N => Real.log N * (spatialMoment n h k β N ξ η g r -
        spatialFace (fun i => h i + 2 * r * k i) k (l + r) β ξ (fun u => g u * η u) /
          spatialFace h k l β ξ η)) atTop
      (𝓝 ((spatialFace h k l β ξ η *
          spatialSecondCoeff n (fun i => h i + 2 * r * k i) k β cξ (CoeffFamily.conv cg cη)
            (l + r) -
        spatialFace (fun i => h i + 2 * r * k i) k (l + r) β ξ (fun u => g u * η u) *
          spatialSecondCoeff n h k β cξ cη l) / spatialFace h k l β ξ η ^ 2)) := by
  have hZ := spatialPhase_twoTerm_chart n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
  have hgη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (CoeffFamily.conv cg cη) u = g u * η u :=
    fun u hu => by
      rw [evalF_conv hg hη (unitBox_subset_closedCube _ hu), hevg u hu, hevη u hu]
  have hgηc : Continuous fun u => g u * η u := hgc.mul hηc
  have hZ' := spatialPhase_twoTerm_chart n (fun i => h i + 2 * r * k i) k hk hβ hξ (hg.conv hη) hξc
    hgηc hevξ hgη (hmin_add_two_mul_k h k hk r hmin) (hatt_add_two_mul_k h k hk r hatt)
  rw [multCount_add_two_mul_k h k hk r l] at hZ'
  have hq := quotient_second_order hA hZ hZ'
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  unfold spatialMoment
  rw [origPhaseIntegral_energy_pow_mul n h k β N ξ (fun u => g u * η u) r, add_sub_cancel_left,
    Real.rpow_natCast, mul_div_assoc, div_self hlog, mul_one]
  ring

/-- The explicit version (`m ≥ 2`): the second coefficient of the numerator is the finite-part face
integral of weight `h + 2rk` and amplitude `g η`. -/
theorem spatialMoment_twoTerm_explicit (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη cg : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    (hg : AbsSummable cg) {ξ η g : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hgc : Continuous g) (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u)
    (hevg : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cg u = g u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) (hA : spatialFace h k l β ξ η ≠ 0) (r : ℕ) :
    Tendsto (fun N => Real.log N * (spatialMoment n h k β N ξ η g r -
        spatialFace (fun i => h i + 2 * r * k i) k (l + r) β ξ (fun u => g u * η u) /
          spatialFace h k l β ξ η)) atTop
      (𝓝 ((spatialFace h k l β ξ η *
          spatialSecondFace (fun i => h i + 2 * r * k i) k (l + r) β ξ (fun u => g u * η u) -
        spatialFace (fun i => h i + 2 * r * k i) k (l + r) β ξ (fun u => g u * η u) *
          spatialSecondFace h k l β ξ η) / spatialFace h k l β ξ η ^ 2)) := by
  have hgη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (CoeffFamily.conv cg cη) u = g u * η u :=
    fun u hu => by
      rw [evalF_conv hg hη (unitBox_subset_closedCube _ hu), hevg u hu, hevη u hu]
  have hgηc : Continuous fun u => g u * η u := hgc.mul hηc
  have hm' : 2 ≤ multCount (ratioExp (fun i => h i + 2 * r * k i) k) (l + r) := by
    rw [multCount_add_two_mul_k h k hk r l]
    exact hm
  have h1 := spatialSecondCoeff_eq n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm
  have h2 := spatialSecondCoeff_eq n (fun i => h i + 2 * r * k i) k hk hβ hξ (hg.conv hη) hξc hgηc
    hevξ hgη (hmin_add_two_mul_k h k hk r hmin) (hatt_add_two_mul_k h k hk r hatt) hm'
  have := spatialMoment_twoTerm n h k hk hβ hξ hη hg hξc hηc hgc hevξ hevη hevg hmin hatt hA r
  rw [h1, h2] at this
  exact this

/-! ### Energy Laplace transforms -/

set_option maxHeartbeats 1000000 in
-- the scalar-multiple family `(β/(β+s)) • cξ` makes the unification of the shifted data slow
/-- **Next-log correction of the posterior energy Laplace transform** `E_{Q_N^ξ}[e^{-sNK}]`,
`s ≥ 0`: the numerator is the chart integral at temperature `β + s` with phase `ξ β/(β+s)`. -/
theorem spatialLaplace_twoTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : spatialFace h k l β ξ η ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun N => Real.log N *
        (origPhaseIntegral n h k β N 1 ξ
            (fun u => Real.exp (-(s * N * ∏ i, u i ^ (2 * k i))) * η u) /
          origPhaseIntegral n h k β N 1 ξ η -
        spatialFace h k l (β + s) (fun u => ξ u * (β / (β + s))) η / spatialFace h k l β ξ η))
      atTop
      (𝓝 ((spatialFace h k l β ξ η *
          spatialSecondCoeff n h k (β + s) ((β / (β + s)) • cξ) cη l -
        spatialFace h k l (β + s) (fun u => ξ u * (β / (β + s))) η *
          spatialSecondCoeff n h k β cξ cη l) / spatialFace h k l β ξ η ^ 2)) := by
  have hβs : 0 < β + s := by linarith
  have hZ := spatialPhase_twoTerm_chart n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
  have hξc' : Continuous fun u => ξ u * (β / (β + s)) := hξc.mul continuous_const
  have hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF ((β / (β + s)) • cξ) u = ξ u * (β / (β + s)) :=
    fun u hu => by rw [evalF_const_smul, hevξ u hu, mul_comm]
  have hZ' := spatialPhase_twoTerm_chart n h k hk hβs (AbsSummable.const_smul hξ (β / (β + s))) hη
    hξc' hηc hevξ' hevη hmin hatt
  have hq := quotient_second_order hA hZ hZ'
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  rw [origPhaseIntegral_energy_tilt_spatial n h k hβ hs N 1 ξ η, sub_self, Real.rpow_zero, one_mul,
    div_self hlog, mul_one]

/-! ### Evidence ratios between phases -/

/-- **Next-log correction of the evidence ratio between two phases**:
`L (𝒵_N[η;ξ']/𝒵_N[η;ξ] − F'/F) → (F B' − F' B)/F²`. -/
theorem spatialEvidenceRatio_twoTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cξ' cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hξ' : AbsSummable cξ')
    (hη : AbsSummable cη) {ξ ξ' η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
    (hξc' : Continuous ξ') (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevξ' : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ' u = ξ' u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : spatialFace h k l β ξ η ≠ 0) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ' η /
        origPhaseIntegral n h k β N 1 ξ η - spatialFace h k l β ξ' η / spatialFace h k l β ξ η))
      atTop
      (𝓝 ((spatialFace h k l β ξ η * spatialSecondCoeff n h k β cξ' cη l -
        spatialFace h k l β ξ' η * spatialSecondCoeff n h k β cξ cη l) /
        spatialFace h k l β ξ η ^ 2)) := by
  have hZ := spatialPhase_twoTerm_chart n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
  have hZ' := spatialPhase_twoTerm_chart n h k hk hβ hξ' hη hξc' hηc hevξ' hevη hmin hatt
  have hq := quotient_second_order hA hZ hZ'
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  rw [sub_self, Real.rpow_zero, one_mul, div_self hlog, mul_one]

end Grammar
