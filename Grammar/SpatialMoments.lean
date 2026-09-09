/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialLocationLaw
import Grammar.PhaseMomentHierarchy

/-!
# Spatial-phase energy moments and face selection (unit 358; Astra #44 unit 4)

Under a fixed continuous phase `ξ`, the posterior mixed moments converge:
`E_{Q_N^ξ}[(NK)^r g(u)] → ∫ η(P_J u) w(u) g(P_J u) J_{λ+r}(ξ(P_J u)) du / Z_ξ`
(`spatialMoment_tendsto`).  The energy insertion `(NK)^r` is the weight shift `h ↦ h + 2rk` at
exponent `λ + r`, which preserves the face, the residual weight and the multiplicity
(`faceProj_add_two_mul_k`, `residualWeight_add_two_mul_k`), so the shifted face functional is the
face integral against `M_β(2(λ+r); ξ(P_J u))`.  In particular the posterior mean of `NK` tends to
`∫ η w J_{λ+1}(ξ∘P_J) / ∫ η w J_λ(ξ∘P_J)`: the face locations are selected by the evidence weight
`J_λ(ξ(v))` and each contributes its tilted mean `μ(ξ(v))`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

/-! ### Weight shifts preserve the face data -/

theorem faceProj_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) (l : ℝ) :
    faceProj (fun i => h i + 2 * r * k i) k (l + r) = faceProj h k l := by
  funext u i
  unfold faceProj
  simp only [ratioExp_add_two_mul_k h k hk r i, add_left_inj]

theorem residualWeight_add_two_mul_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ)
    (l : ℝ) (u : Fin d → ℝ) :
    residualWeight (fun i => h i + 2 * r * k i) k (l + r) u = residualWeight h k l u := by
  unfold residualWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ratioExp_add_two_mul_k h k hk r i, add_left_inj]
  split_ifs
  · rfl
  · congr 1
    push_cast
    ring

/-- The shifted face functional is the face integral against `M_β(2(λ+r); ξ(P_J u))`. -/
theorem spatialFace_add_two_mul_k {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (r : ℕ) :
    spatialFace (fun i => h i + 2 * r * k i) k (l + r) β ξ η =
      1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
      (∫ u in unitBox (d + 1),
        faceWeight h k l η u * phaseMoment β (2 * (l + r)) (ξ (faceProj h k l u))) /
      2 ^ (multCount (ratioExp h k) l - 1) := by
  unfold spatialFace faceWeight
  rw [multCount_add_two_mul_k h k hk r l, faceProj_add_two_mul_k h k hk r l]
  have hprod : (∏ i, if ratioExp (fun i => h i + 2 * r * k i) k i = l + r then (k i : ℝ) else 1) =
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [ratioExp_add_two_mul_k h k hk r i, add_left_inj]
  rw [hprod]
  congr 2
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [residualWeight_add_two_mul_k h k hk r l u]
  ring

/-! ### Mixed moments -/

/-- The posterior mixed moment `E_{Q_N^ξ}[(NK)^r g(u)]`. -/
noncomputable def spatialMoment (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η g : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) : ℝ :=
  origPhaseIntegral n h k β N 1 ξ (fun u => (N * ∏ i, u i ^ (2 * k i)) ^ r * (g u * η u)) /
    origPhaseIntegral n h k β N 1 ξ η

theorem origPhaseIntegral_energy_pow_mul (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ ψ : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) :
    origPhaseIntegral n h k β N 1 ξ (fun u => (N * ∏ i, u i ^ (2 * k i)) ^ r * ψ u) =
      N ^ r * origPhaseIntegral n (fun i => h i + 2 * r * k i) k β N 1 ξ ψ := by
  rw [← origPhaseIntegral_energy_pow]
  unfold origPhaseIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  dsimp only
  rw [mul_pow]
  ring

/-- **Spatial-phase mixed moments**:
`E_{Q_N^ξ}[(NK)^r g(u)] → ∫ η(P_J u) w(u) g(P_J u) J_{λ+r}(ξ(P_J u)) du / Z_ξ`. -/
theorem spatialMoment_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η g : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hgc : Continuous g) (hF : 0 < spatialFace h k l β ξ η) (r : ℕ) :
    Tendsto (fun N => spatialMoment n h k β N ξ η g r) atTop
      (𝓝 ((∫ u in unitBox (n + 1), faceWeight h k l η u * g (faceProj h k l u) *
        fluctMoment β (ξ (faceProj h k l u)) 0 (l + r) 0) / spatialMass h k l β ξ η)) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hlr : 0 < l + r := by positivity
  have hminr := hmin_add_two_mul_k h k hk r hmin
  have hattr := hatt_add_two_mul_k h k hk r hatt
  have hmr : multCount (ratioExp (fun i => h i + 2 * r * k i) k) (l + r) =
      multCount (ratioExp h k) l := multCount_add_two_mul_k h k hk r l
  have hZ := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt ξ η hξc hηc
  have hZr := spatialPhase_tendsto n (fun i => h i + 2 * r * k i) k hk (l + r) β hlr hβ hminr
    hattr ξ (fun u => g u * η u) hξc (hgc.mul hηc)
  rw [hmr] at hZr
  have hdiv := hZr.div hZ hF.ne'
  refine (hdiv.congr' ?_).trans ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      pow_ne_zero _ (Real.log_pos hN).ne'
    have hpow : N ^ (-(l + r)) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hNr : N ^ r ≠ 0 := pow_ne_zero _ hN0.ne'
    simp only [Pi.div_apply]
    rw [spatialMoment, origPhaseIntegral_energy_pow_mul, show N ^ (-l) = N ^ (-(l + r)) * N ^ r by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
      congr 1
      ring]
    field_simp
  · apply le_of_eq
    congr 1
    rw [spatialFace_add_two_mul_k h k hk l β ξ (fun u => g u * η u) r, spatialFace_eq_faceWeight]
    have hc : (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1)) ≠ 0 := by
      refine one_div_ne_zero (mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
      split_ifs
      · exact_mod_cast (hk i).ne'
      · exact one_ne_zero
    have h2 : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hP : (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      split_ifs
      · exact_mod_cast (hk i).ne'
      · exact one_ne_zero
    have hZ' : spatialMass h k l β ξ η = 2 * ∫ u in unitBox (n + 1),
        faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
      unfold spatialMass
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
      rw [fluctMoment_eq_two_mul_phaseMoment]
      ring
    have hA : ∫ u in unitBox (n + 1), faceWeight h k l η u * g (faceProj h k l u) *
        fluctMoment β (ξ (faceProj h k l u)) 0 (l + r) 0 = 2 * ∫ u in unitBox (n + 1),
        faceWeight h k l (fun u => g u * η u) u *
          phaseMoment β (2 * (l + r)) (ξ (faceProj h k l u)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
      unfold faceWeight
      rw [fluctMoment_eq_two_mul_phaseMoment]
      ring
    have hI : 0 < ∫ u in unitBox (n + 1),
        faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
      have := spatialMass_pos_of_face h k hk l β ξ η hF
      rw [hZ'] at this
      linarith
    rw [hA, hZ']
    field_simp

/-- **Spatial-phase posterior mean of `NK`**:
`E_{Q_N^ξ}[NK] → ∫ η w J_{λ+1}(ξ∘P_J)/∫ η w J_λ(ξ∘P_J)`, the evidence-weighted face average of
the tilted means `μ(ξ(v))`. -/
theorem spatialMean_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hF : 0 < spatialFace h k l β ξ η) :
    Tendsto (fun N => origPhaseIntegral n h k β N 1 ξ
        (fun u => (N * ∏ i, u i ^ (2 * k i)) * η u) / origPhaseIntegral n h k β N 1 ξ η) atTop
      (𝓝 ((∫ u in unitBox (n + 1),
        faceWeight h k l η u * fluctMoment β (ξ (faceProj h k l u)) 0 (l + 1) 0) /
        spatialMass h k l β ξ η)) := by
  have := spatialMoment_tendsto n h k hk l β hβ hmin hatt ξ η (fun _ => 1) hξc hηc
    continuous_const hF 1
  simp only [spatialMoment, pow_one, one_mul, Nat.cast_one, mul_one] at this
  exact this

end Grammar
