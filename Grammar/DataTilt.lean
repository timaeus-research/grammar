/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomNextLogPosterior

/-!
# The data tilt and physical admissibility

`dataTilt c x` scales the phase coordinates of a datum by `c` and keeps the amplitude
(`xiCoord_dataTilt`, `etaCoord_dataTilt`); it is Lipschitz on the data space
(`lipschitzWith_dataTilt`) and represents the phase `c ξ_x` with the same amplitude
(`dataPhase_dataTilt`, `dataAmplitude_dataTilt`).  The exact identity
`Z^{β+s}_N(tilt_{β/(β+s)} x) = ∫ e^{−sNK} η_x e^{−βNK+β√N K^{1/2} ξ_x}` (`dataBoxIntegral_dataTilt`)
identifies the numerator of the posterior Laplace transform `E_{Q_N(x)}[e^{−sNK}]` with the chart
integral of the tilted datum at temperature `β + s`.

Physical admissibility: a datum with nonnegative represented amplitude and positive face weight has
positive leading coefficient, hence lies in the admissible domain
(`dataLead_pos_of_nonneg_of_faceWeight_pos`).  Membership in the admissible domain records only the
positivity of `F`; it is not a characterisation of physical data.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

theorem absSummable_const_smul {c : CoeffFamily d} (hc : AbsSummable c) (a : ℝ) :
    AbsSummable (a • c) := by
  unfold AbsSummable
  refine (hc.mul_left |a|).congr fun γ => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]

theorem evalF_const_smul' (c : CoeffFamily d) (a : ℝ) (u : Fin d → ℝ) :
    evalF (a • c) u = a * evalF c u := by
  unfold evalF
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem mass_const_smul (c : ℝ) (f : CoeffFamily d) : mass (c • f) = |c| * mass f := by
  unfold mass
  rw [← tsum_mul_left]
  congr 1
  funext γ
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]

/-- The data tilt: phase coordinates scaled by `c`, amplitude unchanged. -/
noncomputable def dataTilt (c : ℝ) (x : DataSpace d) : DataSpace d :=
  ofFamilies 1 one_pos (c • xiCoord x) (etaCoord x)
    ((absSummableAt_one_iff _).2 (absSummable_const_smul (absSummable_xiCoord x) c))
    ((absSummableAt_one_iff _).2 (absSummable_etaCoord x))

theorem xiCoord_dataTilt (c : ℝ) (x : DataSpace d) : xiCoord (dataTilt c x) = c • xiCoord x := by
  rw [← toXi_one, dataTilt, toXi_ofFamilies]

theorem etaCoord_dataTilt (c : ℝ) (x : DataSpace d) : etaCoord (dataTilt c x) = etaCoord x := by
  rw [← toEta_one, dataTilt, toEta_ofFamilies]

theorem dataTilt_apply_inl (c : ℝ) (x : DataSpace d) (γ : Fin d → ℕ) :
    (dataTilt c x : DataIdx d → ℝ) (Sum.inl γ) = c * x (Sum.inl γ) := by
  have := congrFun (xiCoord_dataTilt c x) γ
  simpa [xiCoord] using this

theorem dataTilt_apply_inr (c : ℝ) (x : DataSpace d) (γ : Fin d → ℕ) :
    (dataTilt c x : DataIdx d → ℝ) (Sum.inr γ) = x (Sum.inr γ) := by
  have := congrFun (etaCoord_dataTilt c x) γ
  simpa [etaCoord] using this

theorem dataTilt_sub (c : ℝ) (x y : DataSpace d) :
    dataTilt c x - dataTilt c y = dataTilt c (x - y) := by
  apply lp.ext
  funext i
  rcases i with γ | γ
  · simp [dataTilt_apply_inl, mul_sub]
  · simp [dataTilt_apply_inr]

theorem dataTilt_one (x : DataSpace d) : dataTilt 1 x = x := by
  apply lp.ext
  funext i
  rcases i with γ | γ
  · simp [dataTilt_apply_inl]
  · simp [dataTilt_apply_inr]

theorem norm_dataTilt_le (c : ℝ) (x : DataSpace d) : ‖dataTilt c x‖ ≤ max 1 |c| * ‖x‖ := by
  rw [norm_eq_mass_add_mass, norm_eq_mass_add_mass, xiCoord_dataTilt, etaCoord_dataTilt,
    mass_const_smul]
  have h1 := mass_nonneg (xiCoord x)
  have h2 := mass_nonneg (etaCoord x)
  have h3 := le_max_left 1 |c|
  have h4 := le_max_right 1 |c|
  nlinarith

theorem lipschitzWith_dataTilt (c : ℝ) :
    LipschitzWith (Real.toNNReal (max 1 |c|)) (dataTilt (d := d) c) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, dataTilt_sub, Real.coe_toNNReal _ (by positivity)]
    exact norm_dataTilt_le c (x - y)

theorem continuous_dataTilt (c : ℝ) : Continuous (dataTilt (d := d) c) :=
  (lipschitzWith_dataTilt c).continuous

theorem dataPhase_dataTilt (c : ℝ) (x : DataSpace d) (u : Fin d → ℝ) :
    dataPhase (dataTilt c x) u = c * dataPhase x u := by
  unfold dataPhase
  rw [xiCoord_dataTilt, evalF_const_smul']

theorem dataAmplitude_dataTilt (c : ℝ) (x : DataSpace d) :
    dataAmplitude (dataTilt c x) = dataAmplitude x := by
  funext u
  unfold dataAmplitude
  rw [etaCoord_dataTilt]

variable (n : ℕ) (h k : Fin (n + 1) → ℕ)

/-- **The Laplace numerator identity**: the chart integral of the tilted datum at temperature
`β + s` is the numerator `∫ e^{−sNK} η_x e^{−βNK + β√N K^{1/2} ξ_x}` of `E_{Q_N(x)}[e^{−sNK}]`. -/
theorem dataBoxIntegral_dataTilt {β s : ℝ} (hβ : 0 < β) (hs : 0 ≤ s) (N : ℝ)
    (x : DataSpace (n + 1)) :
    dataBoxIntegral n h k (β + s) N 1 (dataTilt (β / (β + s)) x) =
      origPhaseIntegral n h k β N 1 (dataPhase x)
        (fun u => Real.exp (-(s * N * ∏ i, u i ^ (2 * k i))) * dataAmplitude x u) := by
  rw [origPhaseIntegral_energy_tilt_spatial n h k hβ hs N 1, dataBoxIntegral_one,
    dataAmplitude_dataTilt]
  congr 1
  funext u
  rw [dataPhase_dataTilt]
  ring

/-- **Physical admissibility**: a datum whose represented amplitude is nonnegative on the cube with
positive face weight has positive leading coefficient. -/
theorem dataLead_pos_of_nonneg_of_faceWeight_pos (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (x : DataSpace (n + 1))
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ dataAmplitude x v)
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l (dataAmplitude x) u) :
    0 < dataLead n h k (β := β) l x := by
  unfold dataLead
  rw [(dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).2]
  exact spatialFace_pos_of_faceWeight h k hk (ratioExp_min_pos h k hk hatt) hβ hmin
    (continuous_dataPhase x) (continuous_dataAmplitude x) hηnn hW

end Grammar
