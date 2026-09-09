/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseLaplaceLaw

/-!
# Leading asymptotics for an arbitrary continuous phase (unit 355; Astra #44 unit 1)

Headline XIX already covers a continuous spatially varying phase `ξ`: in the variable `N`,
`𝒵_N[η; ξ]/(N^{-λ}L^{m-1}) → F(ξ, η)` with
`F(ξ, η) = c ∫_box η(P_J u) M_β(2λ; ξ(P_J u)) w(u) du`, `w = ∏_{i∉J} u_i^{h_i−2k_iλ}`
(`spatialPhase_tendsto`): **only the restriction of the phase to the dominant face survives**
(`spatialFace_congr_face`).  The energy tilt is a temperature change with the pointwise rescaled
phase `ξ β/(β+t)` (`origPhaseIntegral_energy_tilt_spatial`), so the evidence ratio
`𝒵_N[η;ξ]/𝒵_N[η;a] → F(ξ,η)/F(a,η)` and the weighted Laplace transform
`E_{Q_N^ξ}[e^{-tNK} g(u)] →
r^{-λ} ∫ g η (P_J u) M_β(2λ; ξ(P_J u)/√r) w / ∫ η(P_J u) M_β(2λ; ξ(P_J u)) w`
(`spatialLaplace_tendsto`, `spatialFace_temperature`) — the Laplace transform in the energy,
weighted by `g`, of the joint law `Q^ξ ∝ y^{λ-1} e^{-βy+βξ(v)√y} dy ν_F(dv)`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

/-- The face functional of a continuous phase: `c ∫ η(P_J u) M_β(2λ; ξ(P_J u)) w(u) du`. -/
noncomputable def spatialFace {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
    (∫ u in unitBox (d + 1),
      (η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u))) *
        residualWeight h k l u) /
    2 ^ (multCount (ratioExp h k) l - 1)

theorem spatialFace_const {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β a : ℝ)
    (η : (Fin (d + 1) → ℝ) → ℝ) : spatialFace h k l β (fun _ => a) η = phaseFace h k l β a η := rfl

/-- **Only the face restriction of the phase matters.** -/
theorem spatialFace_congr_face {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    {ξ ξ' η : (Fin (d + 1) → ℝ) → ℝ}
    (hξ : ∀ u ∈ unitBox (d + 1), ξ (faceProj h k l u) = ξ' (faceProj h k l u)) :
    spatialFace h k l β ξ η = spatialFace h k l β ξ' η := by
  unfold spatialFace
  congr 2
  exact setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by rw [hξ u hu]

theorem origPhaseIntegral_eq_sqrt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ} (hN : 0 ≤ N)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 ξ η =
      ∫ u in unitBox (n + 1), η u * ((∏ i, u i ^ h i) *
        Real.exp (-(β * Real.sqrt N ^ 2 * ∏ i, u i ^ (2 * k i)) +
          β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u)) := by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset, Real.sq_sqrt hN]
  congr 1
  funext u
  ring

/-- **Leading term for a continuous phase, in the variable `N`.** -/
theorem spatialPhase_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    Tendsto (fun N => origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (spatialFace h k l β ξ η)) := by
  have hT := headline_phase_leading n h k hk l β hl hβ hmin hatt ξ η hξc hηc
  have hsq : Tendsto (fun N : ℝ => Real.sqrt N) atTop atTop := by
    have := tendsto_rpow_atTop (y := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr fun N => ?_
    rw [Real.sqrt_eq_rpow]
  have hc := (hT.comp hsq).div_const (2 ^ (multCount (ratioExp h k) l - 1))
  unfold spatialFace
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  have hpow : Real.sqrt N ^ (-(2 * l)) = N ^ (-l) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  change (∫ u in unitBox (n + 1), η u * ((∏ i, u i ^ h i) *
      Real.exp (-(β * Real.sqrt N ^ 2 * ∏ i, u i ^ (2 * k i)) +
        β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u))) /
      (Real.sqrt N ^ (-(2 * l)) * Real.log (Real.sqrt N) ^ (multCount (ratioExp h k) l - 1)) /
      2 ^ (multCount (ratioExp h k) l - 1) =
    origPhaseIntegral n h k β N 1 ξ η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))
  rw [← origPhaseIntegral_eq_sqrt n h k β hN0.le ξ η, hlog, hpow, div_pow]
  have hpowN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlogN : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  have h2 : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero hpowN (div_ne_zero hlogN h2)) h2)
    (mul_ne_zero hpowN hlogN)]
  rw [mul_assoc (N ^ (-l)), div_mul_cancel₀ _ h2]

/-- **Energy tilt with a spatial phase**: `𝒵_β[e^{-tNK} η; ξ] = 𝒵_{β+t}[η; ξ β/(β+t)]`. -/
theorem origPhaseIntegral_energy_tilt_spatial (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (N b : ℝ) (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N b ξ (fun u => Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * η u) =
      origPhaseIntegral n h k (β + t) N b (fun u => ξ u * (β / (β + t))) η := by
  unfold origPhaseIntegral
  congr 1
  funext u
  have hβt : β + t ≠ 0 := by linarith
  rw [show Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * η u * (∏ i, u i ^ h i) *
      Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u) =
      η u * (∏ i, u i ^ h i) * (Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u))
      by ring, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **Evidence ratio** between a continuous phase and a constant phase. -/
theorem spatialPhase_evidence_ratio (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) (a : ℝ)
    (hA : phaseFace h k l β a η ≠ 0) :
    Tendsto (fun N => origPhaseIntegral n h k β N 1 ξ η /
        origPhaseIntegral n h k β N 1 (fun _ => a) η) atTop
      (𝓝 (spatialFace h k l β ξ η / phaseFace h k l β a η)) := by
  have hZ := spatialPhase_tendsto n h k hk l β hl hβ hmin hatt ξ η hξc hηc
  have hZa := constPhase_tendsto n h k hk l β hl hβ hmin hatt a η hηc
  refine (hZ.div hZa hA).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hN0 _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hpow]

/-- The posterior expectation `E_{Q_N^ξ}[e^{-tNK} g(u)]` (weighted energy Laplace transform). -/
noncomputable def spatialLaplace (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η g : (Fin (n + 1) → ℝ) → ℝ) (t : ℝ) : ℝ :=
  origPhaseIntegral n h k β N 1 ξ
      (fun u => Real.exp (-(t * N * ∏ i, u i ^ (2 * k i))) * (g u * η u)) /
    origPhaseIntegral n h k β N 1 ξ η

/-- **Weighted energy Laplace limit for a continuous phase.** -/
theorem spatialLaplace_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η g : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η)
    (hgc : Continuous g) {t : ℝ} (ht : 0 ≤ t) (hF : spatialFace h k l β ξ η ≠ 0) :
    Tendsto (fun N => spatialLaplace n h k β N ξ η g t) atTop
      (𝓝 (spatialFace h k l (β + t) (fun u => ξ u * (β / (β + t))) (fun u => g u * η u) /
        spatialFace h k l β ξ η)) := by
  have hβt : 0 < β + t := by linarith
  have hZ := spatialPhase_tendsto n h k hk l β hl hβ hmin hatt ξ η hξc hηc
  have hZ' := spatialPhase_tendsto n h k hk l (β + t) hl hβt hmin hatt
    (fun u => ξ u * (β / (β + t))) (fun u => g u * η u) (hξc.mul continuous_const) (hgc.mul hηc)
  refine (hZ'.div hZ hF).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hN0 _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hpow, spatialLaplace,
    origPhaseIntegral_energy_tilt_spatial n h k hβ ht N 1 ξ (fun u => g u * η u)]

/-- **Temperature scaling of the spatial face functional**:
`F_{β+t}(ξβ/(β+t), η) = r^{-λ} F_β(ξ/√r, η)`, `r = (β+t)/β`. -/
theorem spatialFace_temperature {d : ℕ} (h k : Fin (d + 1) → ℕ) (l : ℝ) {β : ℝ} (hβ : 0 < β)
    {t : ℝ} (ht : 0 ≤ t) (ξ η : (Fin (d + 1) → ℝ) → ℝ) :
    spatialFace h k l (β + t) (fun u => ξ u * (β / (β + t))) η =
      ((β + t) / β) ^ (-l) * spatialFace h k l β (fun u => ξ u / Real.sqrt ((β + t) / β)) η := by
  unfold spatialFace
  have e : ∀ u, phaseMoment (β + t) (2 * l) (ξ (faceProj h k l u) * (β / (β + t))) =
      ((β + t) / β) ^ (-l) *
        phaseMoment β (2 * l) (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β)) :=
    fun u => by
      rw [phaseMoment_temperature β (2 * l) _ hβ ht, show -(2 * l / 2) = -l by ring]
  simp only [e]
  rw [show (∫ u in unitBox (d + 1), η (faceProj h k l u) * (((β + t) / β) ^ (-l) *
      phaseMoment β (2 * l) (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β))) *
        residualWeight h k l u) = ((β + t) / β) ^ (-l) * ∫ u in unitBox (d + 1),
      η (faceProj h k l u) * phaseMoment β (2 * l) (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β))
        * residualWeight h k l u by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring]
  ring

end Grammar
