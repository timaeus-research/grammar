/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SingletonChartCertificate
import Grammar.BlowUpCubeChartModel
import Grammar.SignedBoxPackets
import Grammar.LocalAnalyticInputs

/-!
# The all-order expansion of the cube integral through the blow-up charts (CCCXLVII; phase E, E4)

Consult #102 §6–7. For the quadratic phase `K = |x|²` on the unit cube and a signed analytic
packet for the prior `p` and the observable `F` (holomorphic representatives on a complex
neighbourhood of the cube, `p ≥ 0` on the cube), the cube integral decomposes exactly into the
`d · 2^d` pieces `∫_{[0,1]^d} F(φ_β(R_σ z)) p(φ_β(R_σ z)) |z_β|^{d−1} e^{−N unit_β(z) z_β²} dz`
(CCCXLIV's chart adapter, CCCXXXVII's orthant decomposition, the reflection-invariant unit and
weight: `cube_integral_eq_sum_Lap`). Each piece is a singleton chart (CCCXLVI): the packet pulled
back along the complexified chart `φℂ_β` (`pullbackChart`) and the reflection (`pullback`), with
positive-part representatives, produces its certificate and coordinate-free expansion on the chart
geometry with active `{β}` and orders `(1, d−1)`, on the common spectrum `spectrumLe 2 0`
(`spec_piece`: one normal coordinate of exponent `1`, log degree `0`). Summing the `d · 2^d`
little-o statements gives ★★★ `cube_hasExpansion`: for every cutoff `A`,
`∫_{[−1,1]^d} F p e^{−N|x|²} − ∑_{q : α ∈ ℕ/2, α ≤ A} (∑_β ∑_σ C_{β,σ}(q)) N^{−α} = o(N^{−A})`, with
coefficients `C_{β,σ}(q)` the strata integrals of the chart certificates (the "assembled chart
expansions" of the original integral: all orders, coefficients as strata integrals in the blow-up
chart domains). Not included: the intrinsic gluing of the chart strata into the exceptional divisor;
the identification of the leading coefficient with CCXCV. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace Grammar

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox CoordModel

variable {d : ℕ} (β : Fin d)

/-! ### The complexified chart and the packet pullback -/

/-- The complexified blow-up chart. -/
def φℂ (z : Fin d → ℂ) : Fin d → ℂ := fun γ => if γ = β then z β else z β * z γ

theorem complexify_φ (y : Fin d → ℝ) : complexify (φ β y) = φℂ β (complexify y) := by
  funext γ
  simp only [complexify_apply, φℂ]
  split_ifs with h
  · subst h
    rw [φ_self]
  · rw [φ_other β y h]
    push_cast
    rfl

theorem differentiable_φℂ : Differentiable ℂ (φℂ β) :=
  differentiable_pi.2 fun γ => by
    unfold φℂ
    split_ifs
    · exact differentiable_apply β
    · exact (differentiable_apply β).mul (differentiable_apply γ)

variable {p F : (Fin d → ℝ) → ℝ}

/-- ★ **The packet pulled back along the chart**: representatives `H ∘ φℂ_β` on `φℂ_β⁻¹ Ω`. -/
def _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.pullbackChart
    (A : HolomorphicSignedBoxExtension 1 p F) :
    HolomorphicSignedBoxExtension 1 (p ∘ φ β) (F ∘ φ β) where
  Ω := φℂ β ⁻¹' A.Ω
  isOpen_Ω := A.isOpen_Ω.preimage (differentiable_φℂ β).continuous
  box_subset := fun y hy => by
    rw [mem_preimage, ← complexify_φ]
    exact A.box_subset _ (φ_mem_cube β hy)
  Hϕ := A.Hϕ ∘ φℂ β
  Hφ := A.Hφ ∘ φℂ β
  holϕ := A.holϕ.comp (differentiable_φℂ β).differentiableOn (mapsTo_preimage _ _)
  holφ := A.holφ.comp (differentiable_φℂ β).differentiableOn (mapsTo_preimage _ _)
  eqϕ := fun y hy => by
    have hy' : complexify (φ β y) ∈ A.Ω := by rwa [complexify_φ]
    simpa [Function.comp, complexify_φ] using A.eqϕ (φ β y) hy'
  eqφ := fun y hy => by
    have hy' : complexify (φ β y) ∈ A.Ω := by rwa [complexify_φ]
    simpa [Function.comp, complexify_φ] using A.eqφ (φ β y) hy'

/-! ### Reflection invariance of the unit, the weight and the phase -/

theorem unit_refl (σ : CoordSign d) (y : Fin d → ℝ) : unit β (refl σ y) = unit β y := by
  unfold unit
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [refl_apply, mul_pow, sq_sgn, one_mul]

theorem one_le_unit (y : Fin d → ℝ) : 1 ≤ unit β y := by
  unfold unit
  linarith [Finset.sum_nonneg fun γ (_ : γ ∈ Finset.univ.erase β) => sq_nonneg (y γ)]

theorem unit_tan (y y' : Fin d → ℝ) (h : ∀ j, j ≠ β → y j = y' j) : unit β y = unit β y' :=
  unit_indep β h

theorem Kc_unit_eq (y : Fin d → ℝ) : Kc β (unit β) y = K (φ β y) := (K_φ β y).symm

theorem K_φ_refl (σ : CoordSign d) (z : Fin d → ℝ) :
    K (φ β (refl σ z)) = Kc β (unit β) z := by
  rw [K_φ, unit_refl, refl_apply, mul_pow, sq_sgn, one_mul]
  rfl

theorem wgt_refl (h₀ : ℕ) (σ : CoordSign d) (z : Fin d → ℝ) :
    wgt (hS β h₀) (refl σ z) = wgt (hS β h₀) z := by
  rw [wgt_hS, wgt_hS, refl_apply, abs_mul, abs_sgn, one_mul]

/-! ### Weighted integrability of the representatives on the unit box -/

theorem wgt_le_one (h : Fin d → ℕ) {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 1)) : wgt h w ≤ 1 := by
  unfold wgt
  refine Finset.prod_le_one (fun i _ => pow_nonneg (abs_nonneg _) _)
    fun i _ => pow_le_one₀ (abs_nonneg _) ?_
  have := hw i (mem_univ _)
  rw [mem_Icc] at this
  exact abs_le.2 ⟨by linarith, this.2⟩

section Weighted

variable {ϕ φ : (Fin d → ℝ) → ℝ}

/-- The observable representative is integrable against the weighted positive-part prior. -/
theorem integrable_obsRep_weighted (A : HolomorphicBoxExtension 1 ϕ φ) (h : Fin d → ℕ) :
    Integrable A.obsRep ((volume.restrict (piBox d (Icc 0 1))).withDensity
      fun w => ENNReal.ofReal (wgt h w * WaterFilling.posPart A.priorRep w)) := by
  obtain ⟨Bϕ, hBϕ⟩ := A.exists_bound_priorRep
  obtain ⟨Bφ, hBφ⟩ := A.exists_bound_obsRep
  have hW : MeasurableSet (piBox d (Icc 0 (1 : ℝ))) := measurableSet_W 1
  have hle : ∫⁻ w in piBox d (Icc 0 (1 : ℝ)),
      ENNReal.ofReal (wgt h w * WaterFilling.posPart A.priorRep w) ≤
      ∫⁻ _ in piBox d (Icc 0 (1 : ℝ)), ENNReal.ofReal Bϕ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hW] with w hw
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : WaterFilling.posPart A.priorRep w ≤ |A.priorRep w| := by
      unfold WaterFilling.posPart
      exact max_le (le_abs_self _) (abs_nonneg _)
    have h2 : |A.priorRep w| ≤ Bϕ := by
      have := hBϕ w hw
      rwa [Real.norm_eq_abs] at this
    calc wgt h w * WaterFilling.posPart A.priorRep w ≤ 1 * WaterFilling.posPart A.priorRep w :=
          mul_le_mul_of_nonneg_right (wgt_le_one h hw) (WaterFilling.posPart_nonneg _ _)
      _ ≤ Bϕ := by rw [one_mul]; exact h1.trans h2
  have hfin : ∫⁻ w in piBox d (Icc 0 (1 : ℝ)),
      ENNReal.ofReal (wgt h w * WaterFilling.posPart A.priorRep w) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (HolomorphicBoxExtension.isCompact_box (a := (1 : ℝ))).measure_lt_top.ne
  have : IsFiniteMeasure ((volume.restrict (piBox d (Icc 0 (1 : ℝ)))).withDensity
      fun w => ENNReal.ofReal (wgt h w * WaterFilling.posPart A.priorRep w)) :=
    isFiniteMeasure_withDensity hfin
  refine Integrable.of_bound A.measurable_obsRep.aestronglyMeasurable Bφ ?_
  have hae : ∀ᵐ w ∂((volume.restrict (piBox d (Icc 0 (1 : ℝ)))).withDensity
      fun w => ENNReal.ofReal (wgt h w * WaterFilling.posPart A.priorRep w)),
      w ∈ piBox d (Icc 0 (1 : ℝ)) :=
    mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _) (mem_ae_iff.1 (ae_restrict_mem hW)))
  filter_upwards [hae] with w hw
  exact hBφ w hw

end Weighted

/-! ### Continuity of a signed packet on the signed box -/

theorem _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.continuousOn_prior {a : ℝ}
    (A : HolomorphicSignedBoxExtension a p F) : ContinuousOn p (piBox d (Icc (-a) a)) := by
  have h : ContinuousOn (fun w => (A.Hϕ (complexify w)).re) (piBox d (Icc (-a) a)) :=
    Complex.continuous_re.comp_continuousOn (A.holϕ.continuousOn.comp
      continuous_complexify.continuousOn fun w hw => A.box_subset w hw)
  exact h.congr fun w hw => A.eqϕ w (A.box_subset w hw)

theorem _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.continuousOn_obs {a : ℝ}
    (A : HolomorphicSignedBoxExtension a p F) : ContinuousOn F (piBox d (Icc (-a) a)) := by
  have h : ContinuousOn (fun w => (A.Hφ (complexify w)).re) (piBox d (Icc (-a) a)) :=
    Complex.continuous_re.comp_continuousOn (A.holφ.continuousOn.comp
      continuous_complexify.continuousOn fun w hw => A.box_subset w hw)
  exact h.congr fun w hw => A.eqφ w (A.box_subset w hw)

/-! ### The pieces `(β, σ)`: chart `β`, orthant `σ` -/

section Pieces

variable (A : HolomorphicSignedBoxExtension 1 p F) (σ : CoordSign d)

/-- The piece packet: the signed packet pulled back along the chart `φ_β` and the reflection
`R_σ`, a positive-box packet for `p ∘ φ_β ∘ R_σ`, `F ∘ φ_β ∘ R_σ`. -/
noncomputable def pieceExt : HolomorphicBoxExtension 1 ((p ∘ φ β) ∘ refl σ) ((F ∘ φ β) ∘ refl σ) :=
  (A.pullbackChart β).pullback σ

variable (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

include hp0 in
theorem priorRep_nonneg_piece : ∀ w ∈ piBox d (Icc 0 1), 0 ≤ (pieceExt β A σ).priorRep w :=
  (pieceExt β A σ).priorRep_nonneg_on
    (HolomorphicSignedBoxExtension.pullback_nonneg (fun _ hy => hp0 _ (φ_mem_cube β hy)) σ)

include hp0 in
theorem posPart_priorRep_eq :
    ∀ w ∈ piBox d (Icc 0 1),
      WaterFilling.posPart (pieceExt β A σ).priorRep w = (pieceExt β A σ).priorRep w :=
  fun _ hw => posPart_eq_of_mem 1 (priorRep_nonneg_piece β A σ hp0) hw

theorem obsRep_piece {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 1)) :
    (pieceExt β A σ).obsRep z = F (φ β (refl σ z)) :=
  (pieceExt β A σ).obsRep_eq_of_mem ((pieceExt β A σ).box_subset_realDomain hz)

include hp0 in
theorem posPart_priorRep_piece {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 1)) :
    WaterFilling.posPart (pieceExt β A σ).priorRep z = p (φ β (refl σ z)) := by
  rw [posPart_priorRep_eq β A σ hp0 z hz]
  exact (pieceExt β A σ).priorRep_eq_of_mem ((pieceExt β A σ).box_subset_realDomain hz)

/-- The common face-series radius of the piece. -/
noncomputable def pieceRadius : ℝ := (pieceExt β A σ).toRep.radius 1

theorem pieceRadius_pos : 0 < pieceRadius β A σ := (pieceExt β A σ).toRep.radius_pos 1

/-- The outer box side `b' = min(ρ, 1)`. -/
noncomputable def pieceB' : ℝ := min (pieceRadius β A σ) 1

/-- The core box side `b = b'/2`. -/
noncomputable def pieceB : ℝ := pieceB' β A σ / 2

theorem pieceB'_pos : 0 < pieceB' β A σ := lt_min (pieceRadius_pos β A σ) one_pos

theorem pieceB_pos : 0 < pieceB β A σ := half_pos (pieceB'_pos β A σ)

theorem pieceB_lt : pieceB β A σ < pieceB' β A σ := half_lt_self (pieceB'_pos β A σ)

theorem Lb_one : Lb 1 = 1 := by simp [Lb]

theorem pieceB'_le :
    Lb 1 * pieceB' β A σ ≤ ((pieceExt β A σ).toRep.faceSeries 1 (Iβ β)).ρ := by
  rw [Lb_one, one_mul]
  exact min_le_left _ _

theorem pieceB_le : Lb 1 * pieceB β A σ ≤ 1 := by
  rw [Lb_one, one_mul]
  have h1 : pieceB' β A σ ≤ 1 := min_le_right _ _
  unfold pieceB
  linarith [pieceB'_pos β A σ]

/-- ★★ **The piece certificate**: the singleton chart certificate of CCCXLVI for the unit
`unit_β`, the orders `(1, d−1)`, the positive-part prior representative and the observable
representative of the piece packet, on `[0,1]^d`. -/
noncomputable def pieceCert :
    ResolvedCertificate (SingletonChart.G β (d - 1)) (SingletonChart.N β (d - 1))
      (piBox d (Icc 0 1)) (Kc β (unit β))
      (fun w => wgt (hS β (d - 1)) w * WaterFilling.posPart (pieceExt β A σ).priorRep w)
      (pieceExt β A σ).obsRep :=
  cert β (unit β) (unit_tan β) 1 (d - 1) one_pos (continuous_unit β) 1 one_pos
    (fun y _ => one_le_unit β y) (pieceExt β A σ).priorRep (pieceExt β A σ).obsRep
    ((pieceExt β A σ).toRep.faceSeries 1 (Iβ β)) (pieceB β A σ) (pieceB' β A σ)
    (pieceB_pos β A σ) (pieceB_lt β A σ) (pieceB'_le β A σ) (pieceB_le β A σ)
    (WaterFilling.posPart (pieceExt β A σ).priorRep) (posPart_priorRep_eq β A σ hp0)
    (measurable_posPart (pieceExt β A σ).measurable_priorRep) (WaterFilling.posPart_nonneg _)
    (integrable_obsRep_weighted (pieceExt β A σ) (hS β (d - 1)))

/-- ★★ **The piece coefficient certificate**. -/
noncomputable def pieceCoeff : (pieceCert β A σ hp0).CoefficientCertificate :=
  coeffCert β (unit β) (unit_tan β) 1 (d - 1) one_pos (continuous_unit β) 1 one_pos
    (fun y _ => one_le_unit β y) (pieceExt β A σ).priorRep (pieceExt β A σ).obsRep
    ((pieceExt β A σ).toRep.faceSeries 1 (Iβ β)) (pieceB β A σ) (pieceB' β A σ)
    (pieceB_pos β A σ) (pieceB_lt β A σ) (pieceB'_le β A σ) (pieceB_le β A σ)
    (WaterFilling.posPart (pieceExt β A σ).priorRep) (posPart_priorRep_eq β A σ hp0)
    (measurable_posPart (pieceExt β A σ).measurable_priorRep) (WaterFilling.posPart_nonneg _)
    (integrable_obsRep_weighted (pieceExt β A σ) (hS β (d - 1)))

/-! ### Spectrum normalisation: one normal coordinate of exponent `1`, log degree `0` -/

theorem pieceCert_cores_k (J : Fin (pieceCert β A σ hp0).M)
    (i : Fin ((pieceCert β A σ hp0).n J + 1)) :
    (pieceCert β A σ hp0).cores.k J i = 1 := by
  change kS β (σI (Iβ β) i).1 = 1
  rw [Finset.mem_singleton.1 (σI (Iβ β) i).2]
  exact kS_self β

theorem latticeQ_piece (J : Fin (pieceCert β A σ hp0).M) :
    latticeQ ((pieceCert β A σ hp0).cores.k J) = 2 := by
  unfold latticeQ
  rw [Finset.prod_eq_one fun i _ => pieceCert_cores_k β A σ hp0 J i, mul_one]

theorem commonQ_piece : commonQ (pieceCert β A σ hp0).cores.k = 2 := by
  unfold commonQ
  rw [Finset.prod_congr rfl fun J _ => latticeQ_piece β A σ hp0 J, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  exact pow_one 2

theorem nI_Iβ : nI (Iβ β) = 0 := rfl

theorem commonD_piece : commonD (pieceCert β A σ hp0).n = 0 := by
  change Finset.univ.sup (fun _ : Fin 1 => nI (Iβ β)) = 0
  rw [Finset.sup_const Finset.univ_nonempty]
  rfl

/-- ★★ **The expansion of a piece** on the normalised spectrum `spectrumLe 2 0`: exponents in
`½ℕ`, no logarithms. -/
theorem piece_hasCoordFreeExpansion :
    (SingletonChart.N β (d - 1)).HasCoordFreeExpansion (pieceCert β A σ hp0).stratumMeasure
      (pieceCoeff β A σ hp0).field (spectrumLe 2 0) (piBox d (Icc 0 1)) (Kc β (unit β))
      (fun w => wgt (hS β (d - 1)) w * WaterFilling.posPart (pieceExt β A σ).priorRep w)
      (pieceExt β A σ).obsRep := by
  have h : (SingletonChart.N β (d - 1)).HasCoordFreeExpansion (pieceCert β A σ hp0).stratumMeasure
      (pieceCoeff β A σ hp0).field
      (spectrumLe (commonQ (pieceCert β A σ hp0).cores.k) (commonD (pieceCert β A σ hp0).n))
      (piBox d (Icc 0 1)) (Kc β (unit β))
      (fun w => wgt (hS β (d - 1)) w * WaterFilling.posPart (pieceExt β A σ).priorRep w)
      (pieceExt β A σ).obsRep :=
    hasCoordFreeExpansion_singleton β (unit β) (unit_tan β) 1 (d - 1) one_pos (continuous_unit β)
      1 one_pos (fun y _ => one_le_unit β y) (pieceExt β A σ).priorRep (pieceExt β A σ).obsRep
      ((pieceExt β A σ).toRep.faceSeries 1 (Iβ β)) (pieceB β A σ) (pieceB' β A σ)
      (pieceB_pos β A σ) (pieceB_lt β A σ) (pieceB'_le β A σ) (pieceB_le β A σ)
      (WaterFilling.posPart (pieceExt β A σ).priorRep) (posPart_priorRep_eq β A σ hp0)
      (measurable_posPart (pieceExt β A σ).measurable_priorRep) (WaterFilling.posPart_nonneg _)
      (pieceExt β A σ).measurable_obsRep
      (integrable_obsRep_weighted (pieceExt β A σ) (hS β (d - 1)))
  rwa [commonQ_piece, commonD_piece] at h

/-- The piece coefficient `C_{β,σ}(q)`: the strata integrals of the piece certificate. -/
noncomputable def pieceCoefficient (q : PowerLogIndex) : ℝ :=
  (SingletonChart.N β (d - 1)).expansionCoefficient (pieceCert β A σ hp0).stratumMeasure
    (pieceCoeff β A σ hp0).field (pieceExt β A σ).obsRep q

end Pieces

/-! ### The exact decomposition of the cube integral and the assembled expansion -/

section Assembly

variable [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

omit β in
include hp0 in
/-- ★ **The exact decomposition**: the cube Laplace integral is the sum over the `d · 2^d`
pieces of the piece Laplace integrals `∫_{[0,1]^d} F_{βσ} |z_β|^{d−1} p_{βσ}⁺ e^{−N unit_β z_β²}`
(chart adapter of CCCXLIV, orthant decomposition of CCCXXXVII, reflection invariance of the
unit and the weight). -/
theorem cube_integral_eq_sum_pieces (n : ℝ) :
    ∫ x in cube d, F x * p x * Real.exp (-n * K x) =
      ∑ β : Fin d, ∑ σ : CoordSign d, globalLaplace (piBox d (Icc 0 1)) (Kc β (unit β))
        (fun w => (pieceExt β A σ).obsRep w *
          (wgt (hS β (d - 1)) w * WaterFilling.posPart (pieceExt β A σ).priorRep w)) n := by
  have hcont : ContinuousOn (fun x => F x * p x * Real.exp (-n * K x)) (cube d) :=
    (A.continuousOn_obs.mul A.continuousOn_prior).mul
      ((continuous_const.mul continuous_K).rexp).continuousOn
  rw [cube_integral_eq_sum_chart _ (hcont.integrableOn_compact isCompact_cube)]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hβ : ContinuousOn (fun y => |y β| ^ (d - 1) *
      (F (φ β y) * p (φ β y) * Real.exp (-n * K (φ β y)))) (piBox d (Icc (-1) 1)) :=
    ((continuous_apply β).abs.pow _).continuousOn.mul
      (hcont.comp (continuous_φ β).continuousOn fun y hy => φ_mem_cube β hy)
  rw [show cube d = piBox d (Icc (-1) 1) from rfl, setIntegral_signedBox_eq_sum 1 _
    (hβ.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [setIntegral_orthantBox 1 σ]
  unfold globalLaplace
  refine setIntegral_congr_fun (measurableSet_W 1) fun z hz => ?_
  beta_reduce
  rw [K_φ_refl, refl_apply, abs_mul, abs_sgn, one_mul, ← wgt_hS β (d - 1) z,
    obsRep_piece β A σ hz, posPart_priorRep_piece β A σ hp0 hz]
  ring

omit β in
/-- The assembled coefficient `C(q) = ∑_β ∑_σ C_{β,σ}(q)`. -/
noncomputable def cubeCoefficient (q : PowerLogIndex) : ℝ :=
  ∑ β : Fin d, ∑ σ : CoordSign d, pieceCoefficient β A σ hp0 q

omit β in
theorem isLittleO_sum_fun {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (h : ∀ i ∈ s, f i =o[atTop] g) : (fun n => ∑ i ∈ s, f i n) =o[atTop] g :=
  (IsLittleO.sum h).congr_left fun n => Finset.sum_apply n s f

omit β in
include hp0 in
/-- ★★★ **The all-order expansion of the cube integral through the blow-up charts**: for a
signed analytic packet `(p, F)` on the unit cube with `p ≥ 0` there, and every cutoff `A`,
`∫_{[−1,1]^d} F p e^{−N|x|²} − ∑_{α ∈ ½ℕ, α ≤ A} C(α) N^{−α} = o(N^{−A})`, with
`C(α) = ∑_β ∑_σ C_{β,σ}(α)` the strata integrals of the `d · 2^d` singleton chart certificates
(no logarithms: the spectrum is `spectrumLe 2 0`). -/
theorem cube_hasExpansion (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ spectrumLe 2 0 A', cubeCoefficient A hp0 q * q.scale n) =o[atTop]
      fun n : ℝ => n ^ (-A') := by
  have hpt : ∀ n : ℝ, (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ spectrumLe 2 0 A', cubeCoefficient A hp0 q * q.scale n =
      ∑ β : Fin d, ∑ σ : CoordSign d, (globalLaplace (piBox d (Icc 0 1)) (Kc β (unit β))
        (fun w => (pieceExt β A σ).obsRep w *
          (wgt (hS β (d - 1)) w * WaterFilling.posPart (pieceExt β A σ).priorRep w)) n -
        ∑ q ∈ spectrumLe 2 0 A', pieceCoefficient β A σ hp0 q * q.scale n) := by
    intro n
    rw [cube_integral_eq_sum_pieces A hp0 n]
    simp only [Finset.sum_sub_distrib, cubeCoefficient, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm (s := spectrumLe 2 0 A')]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_comm
  exact (isLittleO_sum_fun Finset.univ fun β _ => isLittleO_sum_fun Finset.univ fun σ _ =>
    piece_hasCoordFreeExpansion β A σ hp0 A').congr_left fun n => (hpt n).symm

end Assembly

end BlowUpCube

end Grammar
