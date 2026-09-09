/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialAssembly

/-!
# Two-dimensional regression and a strict transverse example (unit 373; Astra #46 unit 2)

The model `d = 2`, `h = (0,0)`, `k = (1,1)`, `η = 1`: `λ = 1/2`, `m = 2`, both coordinates on the
face, no residual weight, no logarithmic weight.  The explicit formulas of Headlines LXXII/LXXIX
reduce to
```
F(a,1) = J_{1/2}(a)/4,        B(a,1) = J̇_{1/2}(a)/4
```
(`spatialFace_twoDim`, `spatialSecondFace_twoDim_const`) — Astra's independent computation from
`Z_N(a) = N^{-1/2}/4 ∫₀^N y^{-1/2} e^{-βy+βa√y} (log N − log y) dy`.  For the linear phase
`ξ(x,z) = c + a x` with `a > 0` the leading coefficient is unchanged but
```
B(ξ,1) − B(c,1) = (1/2) ∫₀¹ (J_{1/2}(c+at) − J_{1/2}(c))/t dt > 0
```
(`spatialSecondFace_twoDim_linear`, `spatialSecondFace_twoDim_linear_pos`): identical leading
joint limit, strictly larger next-log evidence coefficient; consequently
`𝒵_N[1; c + a x] > 𝒵_N[1; c]` for all large `N` (`twoDim_transverse_evidence_pos`).  The
ingredients are the strict monotonicity of `J_ν` in the phase (`fluctMoment_strictMono_phase`,
from the Taylor expansion and `fluctMoment β a 1 ν 0 = J_{ν+1/2}(a) > 0`) and the bound
`(J(c+at) − J(c))/t ≤ J(c+a) − J(c)` on `(0,1]` (`fluctMoment_sub_div_le`), which makes the
finite-part integral absolutely convergent and strictly positive.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

/-! ### Monotonicity of `J_ν` in the phase -/

theorem fluctMoment_nonneg (β a : ℝ) (p : ℕ) (ν : ℝ) : 0 ≤ fluctMoment β a p ν 0 := by
  unfold fluctMoment
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  simp only [pow_zero, mul_one]
  exact mul_nonneg (Real.rpow_nonneg ht0.le _) (phaseKernel_nonneg _ _ _ _)

/-- `fluctMoment β a 1 ν 0 = J_{ν+1/2}(a)`. -/
theorem fluctMoment_one_eq (β a ν : ℝ) :
    fluctMoment β a 1 ν 0 = fluctMoment β a 0 (ν + 1 / 2) 0 := by
  unfold fluctMoment phaseKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  simp only [pow_zero, mul_one, pow_one]
  rw [Real.sqrt_eq_rpow, show ν + 1 / 2 - 1 = (ν - 1) + 1 / 2 by ring, Real.rpow_add ht0]
  ring

theorem fluctMoment_one_pos (β a : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) :
    0 < fluctMoment β a 1 ν 0 := by
  rw [fluctMoment_one_eq]
  exact fluctMoment_pos β a _ hβ (by linarith)

/-- **`J_ν` is strictly increasing in the phase.** -/
theorem fluctMoment_strictMono_phase (β : ℝ) (hβ : 0 < β) {a b : ℝ} (hab : a < b) {ν : ℝ}
    (hν : 0 < ν) : fluctMoment β a 0 ν 0 < fluctMoment β b 0 ν 0 := by
  have h := hasSum_fluctMoment_taylor β a b hβ hν 0
  have hnn : ∀ p, 0 ≤ (β * (b - a)) ^ p / (p.factorial : ℝ) * fluctMoment β a p ν 0 := fun p =>
    mul_nonneg (div_nonneg (pow_nonneg (mul_nonneg hβ.le (by linarith)) _) (by positivity))
      (fluctMoment_nonneg β a p ν)
  have hle := sum_le_hasSum ({0, 1} : Finset ℕ) (fun p _ => hnn p) h
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hle
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, pow_one,
    Nat.factorial_one] at hle
  have hpos : 0 < β * (b - a) * fluctMoment β a 1 ν 0 :=
    mul_pos (mul_pos hβ (by linarith)) (fluctMoment_one_pos β a hβ hν)
  linarith

/-- **The finite-part bound** `(J(c+at) − J(c))/t ≤ J(c+a) − J(c)` for `t ∈ (0,1]`, `a ≥ 0`. -/
theorem fluctMoment_sub_div_le (β : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) (c : ℝ) {a : ℝ}
    (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (fluctMoment β (c + a * t) 0 ν 0 - fluctMoment β c 0 ν 0) / t ≤
      fluctMoment β (c + a) 0 ν 0 - fluctMoment β c 0 ν 0 := by
  have ht0 : 0 < t := ht.1
  have h1 := hasSum_fluctMoment_taylor β c (c + a * t) hβ hν 0
  have h2 := hasSum_fluctMoment_taylor β c (c + a) hβ hν 0
  rw [add_sub_cancel_left] at h1 h2
  have hs1 : Summable fun p => (β * (a * t)) ^ (p + 1) / ((p + 1).factorial : ℝ) *
      fluctMoment β c (p + 1) ν 0 := (summable_nat_add_iff 1).2 h1.summable
  have hs2 : Summable fun p => (β * a) ^ (p + 1) / ((p + 1).factorial : ℝ) *
      fluctMoment β c (p + 1) ν 0 := (summable_nat_add_iff 1).2 h2.summable
  have e1 := h1.summable.tsum_eq_zero_add
  have e2 := h2.summable.tsum_eq_zero_add
  rw [h1.tsum_eq] at e1
  rw [h2.tsum_eq] at e2
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at e1 e2
  rw [e1, e2, add_sub_cancel_left, add_sub_cancel_left, div_eq_mul_inv, ← tsum_mul_right]
  refine (hs1.mul_right t⁻¹).tsum_le_tsum (fun p => ?_) hs2
  have hfm := fluctMoment_nonneg β c (p + 1) ν
  have hkey : (β * (a * t)) ^ (p + 1) * t⁻¹ ≤ (β * a) ^ (p + 1) := by
    rw [show β * (a * t) = (β * a) * t by ring, mul_pow, pow_succ t p, mul_assoc,
      mul_inv_cancel_right₀ ht0.ne']
    exact mul_le_of_le_one_right (pow_nonneg (mul_nonneg hβ.le ha) _) (pow_le_one₀ ht0.le ht.2)
  calc (β * (a * t)) ^ (p + 1) / ((p + 1).factorial : ℝ) * fluctMoment β c (p + 1) ν 0 * t⁻¹
      = ((β * (a * t)) ^ (p + 1) * t⁻¹) / ((p + 1).factorial : ℝ) *
          fluctMoment β c (p + 1) ν 0 := by ring
    _ ≤ (β * a) ^ (p + 1) / ((p + 1).factorial : ℝ) * fluctMoment β c (p + 1) ν 0 := by gcongr

theorem continuous_fluctMoment_phase (β : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) :
    Continuous fun a => fluctMoment β a 0 ν 0 := by
  have h : Continuous fun a => 2 * phaseMoment β (2 * ν) a :=
    continuous_const.mul (continuous_phaseMoment β (2 * ν) hβ (by positivity))
  exact h.congr fun a => by rw [fluctMoment_eq_two_mul_phaseMoment]

/-- The finite-part integrand of the linear transverse example is integrable on `(0,1]`. -/
theorem integrableOn_transverse_quot (β : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) (c : ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (fluctMoment β (c + a * t) 0 ν 0 - fluctMoment β c 0 ν 0) / t)
      (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded
    (M := fluctMoment β (c + a) 0 ν 0 - fluctMoment β c 0 ν 0)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) ?_ ?_
  · exact ((((continuous_fluctMoment_phase β hβ hν).comp
      (continuous_const.add (continuous_const.mul continuous_id))).sub
        continuous_const).measurable.div measurable_id).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have hle : c ≤ c + a * t := le_add_of_nonneg_right (mul_nonneg ha ht.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sub_nonneg.2
      (fluctMoment_mono_phase β hβ hle hν)) ht.1.le)]
    exact fluctMoment_sub_div_le β hβ hν c ha ht

/-- The finite-part integral of the linear transverse example is strictly positive. -/
theorem integral_transverse_quot_pos (β : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) (c : ℝ) {a : ℝ}
    (ha : 0 < a) :
    0 < ∫ t in Ioc (0 : ℝ) 1, (fluctMoment β (c + a * t) 0 ν 0 - fluctMoment β c 0 ν 0) / t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_transverse_quot β hβ hν c ha.le)]
  · have hsub : Ioc (0 : ℝ) 1 ⊆ Function.support (fun t : ℝ =>
        (fluctMoment β (c + a * t) 0 ν 0 - fluctMoment β c 0 ν 0) / t) ∩ Ioc 0 1 := by
      intro t ht
      refine ⟨?_, ht⟩
      rw [Function.mem_support]
      have hlt : c < c + a * t := lt_add_of_pos_right _ (mul_pos ha ht.1)
      exact (div_pos (sub_pos.2 (fluctMoment_strictMono_phase β hβ hlt hν)) ht.1).ne'
    calc (0 : ENNReal) < volume (Ioc (0 : ℝ) 1) := by
          rw [Real.volume_Ioc, sub_zero]
          exact ENNReal.ofReal_pos.2 one_pos
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have hle : c ≤ c + a * t := le_add_of_nonneg_right (mul_nonneg ha.le ht.1.le)
    exact div_nonneg (sub_nonneg.2 (fluctMoment_mono_phase β hβ hle hν)) ht.1.le

/-! ### The model `d = 2`, `h = (0,0)`, `k = (1,1)` -/

/-- The weight `h = (0,0)`. -/
def h₂ : Fin 2 → ℕ := fun _ => 0

/-- The exponent `k = (1,1)`. -/
def k₂ : Fin 2 → ℕ := fun _ => 1

theorem k₂_pos : ∀ i, 0 < k₂ i := fun _ => one_pos

theorem ratioExp_h₂k₂ (i : Fin 2) : ratioExp h₂ k₂ i = 1 / 2 := by
  unfold ratioExp h₂ k₂
  norm_num

theorem hmin_h₂k₂ : ∀ i, (1 / 2 : ℝ) ≤ ratioExp h₂ k₂ i := fun i => by rw [ratioExp_h₂k₂]

theorem hatt_h₂k₂ : ∃ i, ratioExp h₂ k₂ i = 1 / 2 := ⟨0, ratioExp_h₂k₂ 0⟩

theorem multCount_h₂k₂ : multCount (ratioExp h₂ k₂) (1 / 2) = 2 := by
  unfold multCount
  simp [ratioExp_h₂k₂]

theorem faceTwoK_h₂k₂ : faceTwoK h₂ k₂ (1 / 2) = 4 := by
  unfold faceTwoK
  simp [ratioExp_h₂k₂, k₂]
  norm_num

theorem residualWeight_h₂k₂ (u : Fin 2 → ℝ) : residualWeight h₂ k₂ (1 / 2) u = 1 := by
  unfold residualWeight
  simp [ratioExp_h₂k₂]

theorem logWeight_h₂k₂ (u : Fin 2 → ℝ) : logWeight h₂ k₂ (1 / 2) u = 0 := by
  unfold logWeight
  simp [ratioExp_h₂k₂]

theorem faceProj_h₂k₂ (u : Fin 2 → ℝ) : faceProj h₂ k₂ (1 / 2) u = 0 := by
  funext i
  simp [faceProj, ratioExp_h₂k₂]

theorem setIntegral_unitBox_const (d : ℕ) (c : ℝ) : ∫ _ in unitBox d, c = c := by
  rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul]

/-- **Regression, leading coefficient**: `F(a,1) = J_{1/2}(a)/4`. -/
theorem spatialFace_twoDim (β a : ℝ) :
    spatialFace h₂ k₂ (1 / 2) β (fun _ => a) (fun _ => 1) = fluctMoment β a 0 (1 / 2) 0 / 4 := by
  unfold spatialFace
  rw [multCount_h₂k₂, fluctMoment_eq_two_mul_phaseMoment]
  simp only [residualWeight_h₂k₂, ratioExp_h₂k₂, if_true, k₂, Nat.cast_one, Finset.prod_const_one,
    one_mul, mul_one]
  rw [setIntegral_unitBox_const]
  norm_num [Nat.factorial]
  ring

/-- **Regression, second coefficient**: `B(a,1) = J̇_{1/2}(a)/4`. -/
theorem spatialSecondFace_twoDim_const (β a : ℝ) :
    spatialSecondFace h₂ k₂ (1 / 2) β (fun _ => a) (fun _ => 1) =
      fluctMoment β a 0 (1 / 2) 1 / 4 := by
  unfold spatialSecondFace dressedAmplitude
  rw [multCount_h₂k₂, faceTwoK_h₂k₂]
  simp only [residualWeight_h₂k₂, logWeight_h₂k₂, mul_zero, mul_one, one_mul, integral_zero,
    sub_self, zero_div, ratioExp_h₂k₂, if_true, Finset.sum_const_zero, add_zero, zero_add,
    Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
  rw [setIntegral_unitBox_const]
  ring

/-- **The linear transverse phase** `ξ(x,z) = c + a x`:
`B(ξ,1) − B(c,1) = (1/2) ∫₀¹ (J_{1/2}(c+at) − J_{1/2}(c))/t dt`. -/
theorem spatialSecondFace_twoDim_linear (β c a : ℝ) :
    spatialSecondFace h₂ k₂ (1 / 2) β (fun u => c + a * u 0) (fun _ => 1) -
        spatialSecondFace h₂ k₂ (1 / 2) β (fun _ => c) (fun _ => 1) =
      (1 / 2) * ∫ t in Ioc (0 : ℝ) 1,
        (fluctMoment β (c + a * t) 0 (1 / 2) 0 - fluctMoment β c 0 (1 / 2) 0) / t := by
  rw [spatialSecondFace_twoDim_const]
  unfold spatialSecondFace dressedAmplitude
  rw [multCount_h₂k₂, faceTwoK_h₂k₂]
  simp only [residualWeight_h₂k₂, logWeight_h₂k₂, faceProj_h₂k₂, Pi.zero_apply, mul_zero, add_zero,
    mul_one, one_mul, integral_zero, zero_add, ratioExp_h₂k₂, if_true, k₂, Nat.cast_one,
    Nat.sub_self, Nat.factorial_zero]
  have e0 : ∀ t : ℝ, Function.update (0 : Fin (1 + 1) → ℝ) 0 t 0 = t := fun t => by simp
  have e1 : ∀ t : ℝ, Function.update (0 : Fin (1 + 1) → ℝ) (Fin.succ 0) t 0 = 0 := fun t => by
    rw [Function.update_of_ne (Fin.succ_ne_zero 0).symm]
    rfl
  rw [setIntegral_unitBox_const, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [e0, e1, mul_zero, add_zero, sub_self, zero_div, integral_zero]
  rw [setIntegral_unitBox_const]
  ring

/-- **Strict transverse sensitivity**: for `a > 0`, `B(c,1) < B(c + a x, 1)` although the leading
coefficients agree. -/
theorem spatialSecondFace_twoDim_linear_pos (β : ℝ) (hβ : 0 < β) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    spatialSecondFace h₂ k₂ (1 / 2) β (fun _ => c) (fun _ => 1) <
      spatialSecondFace h₂ k₂ (1 / 2) β (fun u => c + a * u 0) (fun _ => 1) := by
  rw [← sub_pos, spatialSecondFace_twoDim_linear]
  exact mul_pos (by norm_num) (integral_transverse_quot_pos β hβ (by norm_num) c ha)

/-! ### The coefficient family of the linear phase and the evidence at order `1/L` -/

/-- The coefficient family of `c + a x` on `Fin 2`. -/
noncomputable def linFamily (c a : ℝ) : CoeffFamily 2 :=
  fun γ => if γ = 0 then c else if γ = Pi.single 0 1 then a else 0

theorem linFamily_support (c a : ℝ) :
    ∀ γ, γ ∉ ({0, Pi.single 0 1} : Finset (Fin 2 → ℕ)) → linFamily c a γ = 0 := by
  intro γ hγ
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
  unfold linFamily
  rw [if_neg hγ.1, if_neg hγ.2]

theorem absSummable_linFamily (c a : ℝ) : AbsSummable (linFamily c a) :=
  summable_of_support_subset (linFamily_support c a)

theorem mono_single_fin2 (u : Fin 2 → ℝ) : mono (Pi.single 0 1 : Fin 2 → ℕ) u = u 0 := by
  unfold mono
  rw [Fin.prod_univ_two]
  simp

theorem zero_ne_single_fin2 : (0 : Fin 2 → ℕ) ≠ Pi.single 0 1 := by
  intro h
  have := congr_fun h 0
  simp at this

theorem evalF_linFamily (c a : ℝ) (u : Fin 2 → ℝ) : evalF (linFamily c a) u = c + a * u 0 := by
  unfold evalF
  rw [tsum_eq_sum_of_support_subset (linFamily_support c a), Finset.sum_pair zero_ne_single_fin2,
    mono_single_fin2]
  simp [linFamily, mono]

/-- **The evidence with the linear transverse phase exceeds the constant-phase evidence at order
`1/L`**: `L (𝒵_N[1; c + a x] − 𝒵_N[1; c])/(N^{-1/2} L) → (1/2) ∫₀¹ (J(c+at) − J(c))/t dt`. -/
theorem twoDim_transverse_evidence (β : ℝ) (hβ : 0 < β) (c a : ℝ) :
    Tendsto (fun N => Real.log N *
        ((origPhaseIntegral 1 h₂ k₂ β N 1 (fun u => c + a * u 0) (fun _ => 1) -
          origPhaseIntegral 1 h₂ k₂ β N 1 (fun _ => c) (fun _ => 1)) /
        (N ^ (-(1 / 2 : ℝ)) * Real.log N ^ (2 - 1)))) atTop
      (𝓝 ((1 / 2) * ∫ t in Ioc (0 : ℝ) 1,
        (fluctMoment β (c + a * t) 0 (1 / 2) 0 - fluctMoment β c 0 (1 / 2) 0) / t)) := by
  have hξc : Continuous fun u : Fin (1 + 1) → ℝ => c + a * u 0 := by fun_prop
  have hm : 2 ≤ multCount (ratioExp h₂ k₂) (1 / 2) := by rw [multCount_h₂k₂]
  have h := spatialPhase_transverse_correction 1 h₂ k₂ k₂_pos hβ (absSummable_linFamily c a)
    (absSummable_constFamily 1) hξc continuous_const (fun u _ => evalF_linFamily c a u)
    (fun u _ => evalF_constFamily 1 u) hmin_h₂k₂ hatt_h₂k₂ hm
  rw [← spatialSecondFace_sub_face 1 h₂ k₂ k₂_pos hβ (absSummable_linFamily c a)
    (absSummable_constFamily 1) hξc continuous_const (fun u _ => evalF_linFamily c a u)
    (fun u _ => evalF_constFamily 1 u) hmin_h₂k₂ hatt_h₂k₂ hm] at h
  have hcomp : ((fun u : Fin (1 + 1) → ℝ => c + a * u 0) ∘ faceProj h₂ k₂ (1 / 2)) =
      fun _ => c := by
    funext u
    rw [Function.comp_apply, faceProj_h₂k₂]
    simp
  rw [hcomp, spatialSecondFace_twoDim_linear, multCount_h₂k₂] at h
  exact h

/-- For `a > 0` the linear transverse phase gives strictly larger evidence for all large `N`. -/
theorem twoDim_transverse_evidence_pos (β : ℝ) (hβ : 0 < β) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N in atTop, origPhaseIntegral 1 h₂ k₂ β N 1 (fun _ => c) (fun _ => 1) <
      origPhaseIntegral 1 h₂ k₂ β N 1 (fun u => c + a * u 0) (fun _ => 1) := by
  have h := twoDim_transverse_evidence β hβ c a
  have hpos : 0 < (1 / 2 : ℝ) * ∫ t in Ioc (0 : ℝ) 1,
      (fluctMoment β (c + a * t) 0 (1 / 2) 0 - fluctMoment β c 0 (1 / 2) 0) / t :=
    mul_pos (by norm_num) (integral_transverse_quot_pos β hβ (by norm_num) c ha)
  filter_upwards [h.eventually (lt_mem_nhds hpos), eventually_gt_atTop (1 : ℝ)] with N hN hN1
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hden : 0 < N ^ (-(1 / 2 : ℝ)) * Real.log N ^ (2 - 1) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos hL _)
  have h1 := pos_of_mul_pos_right hN hL.le
  rw [div_pos_iff_of_pos_right hden] at h1
  linarith

end Grammar
