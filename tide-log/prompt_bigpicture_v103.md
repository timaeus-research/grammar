# Consult #103 — audit of phase E (the cube blow-up as a chart model, E0a–E4) and the next gate

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 648 modules, zero sorry/axiom, all headline theorems axiom-clean
`[propext, Classical.choice, Quot.sound]`). Your consult #102 designed phase E: generalise the producer from
the coordinate monomial model (all coordinates active) to a CHART MODEL with an active set, orders `h`, a
positive tangential unit, and assemble the ORIGINAL cube integral `∫_{[−1,1]^d} F p e^{−N|x|²}` through the
`d` blow-up charts. You said: stop after E4 for the paper. All five units are landed and merged (main
`d8853e3`). This consult is the AUDIT: does what landed meet the specification, what are the fidelity risks,
which of the E4 gate items are worth proving, and what is the next gated phase. As in #99/#101, please be
concrete and, where you find a defect, say exactly which statement to change.

## 1. What landed (2026-09-13)

| Unit | Headline | Content |
|---|---|---|
| E1 | CCCXLIII `ChartModelGeometry` | `ChartModel.geometry d A k h hk : ResolvedGeometry d (Fin d → ℝ)` — components `↥A`, `π = id`, strata `S_I = {u_i = 0, i ∈ I; u_i ≠ 0, i ∈ A∖I}`, `E = ⋃_{i∈A}{u_i=0}`; `normalData` with `N I s = span{e_i : i ∈ I}`, `Φ s v = s + v`; `mem_stratumSet_univ_iff : u ∈ S_A ↔ ∀ i ∈ A, u i = 0`; phase `u₀(y)·∏_{i∈A} y_i^{2k_i}` |
| E0a | CCCXLIV `BlowUpCubeChartModel` | the cube's singleton data (`unit_indep`: unit depends only on `y_γ, γ≠β`; `phase_singleton`), `abs_det_φ : |det| = |y_β|^{d−1}`, `abs_det_φ_refl` (even for every d), wedges a.e. disjoint (`ae_wedge_unique`), ★ `wedge_integral_eq`, ★ `cube_integral_eq_sum_chart : ∫_{cube} g = ∑_β ∫_{cube} |y_β|^{d−1} g(φ_β y)` (integrability only) |
| E2 | CCCXLV `WeightedNormalisedBoxCore` | `wcore`: the normalised core with orders `h` (weight `wgt h w = ∏|w_i|^{h_i}` in the measure, amplitude `J·Hw·Lw·fϕ` with `Hw = ∏_{tangential}|t_j|^{h_j}`, `Lw = ∏_{normal} λ_j^{h_j}`), tangential unit through `WData.unit` with `hnorm : unit t · tanUnit · ∏ λ_j^{2k_j} = β`; `wgt_Φ`, `densityW_ae`; `h = 0` recovers the old core |
| E3 | CCCXLVI `SingletonChartCertificate` | ONE active coordinate `β`, phase `Kc β u = u(y)·y_β²` with `u ≥ c > 0` continuous, depending only on coordinates `≠ β`; orders `(k,h) = (δ_β, h₀δ_β)`; base = closed face `{y_β=0} ∩ [0,a]^d` (compact), `λ(s) = u(s)^{−1/2}`, face series in the ORIGINAL normal variable rescaled by `λ` (`Lb·b' ≤ ρ`, `Lb·b ≤ a`, `Lb = c^{−1/2}`), one core + tail with gap `b²`; ★★ `cert`, ★★ `coeffCert`, ★★★ `hasCoordFreeExpansion_singleton`; prior argument `ϕ'` agreeing with the series prior on the box (for positive-part representatives) |
| E4 | CCCXLVII `BlowUpCubeExpansion` | full source below: `φℂ` + ★ `pullbackChart`, reflection invariance, `d·2^d` pieces, `commonQ = 2`, `commonD = 0` ⇒ spectrum `spectrumLe 2 0`, ★ `cube_integral_eq_sum_pieces` (exact), ★★★ `cube_hasExpansion` |

The headline statement (E4):
```
theorem cube_hasExpansion [NeZero d] (A : HolomorphicSignedBoxExtension 1 p F)
    (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x) (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ spectrumLe 2 0 A', cubeCoefficient A hp0 q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-A')
```
with `cubeCoefficient A hp0 q = ∑_β ∑_σ (N β (d−1)).expansionCoefficient (pieceCert …).stratumMeasure
(pieceCoeff …).field (pieceExt β A σ).obsRep q` (the strata integrals of the piece certificates), and
`spectrumLe 2 0 A' = {(α, 0) : α ∈ ½ℕ, α ≤ A'}` (lattice `Q = 2`, log degree `0`).

## 2. What we want audited

1. **Specification.** #102 §6–7 asked for "signed blow-up charts + exact finite-sum assembly of the ORIGINAL
   cube integral (all orders)". Is `cube_hasExpansion` that theorem? Note what it is NOT: the coefficients are
   sums over charts and orthants of strata integrals on the CHART geometries (each `G β (d−1)` has components
   `{β}`, strata `{y_β = 0}` and its complement in `[0,1]^d`); there is no intrinsic gluing of the `d·2^d`
   chart faces into the exceptional divisor `E ≅ S^{d−1}` (or `ℝP^{d−1}`), and no identification of
   `C(d/2+j)` with `Γ(d/2+j)/(2j)! ∑_β ∫ u_β^{−d/2−j} D^{2j}a(0)[v_β,…]`. Is that the right stopping point for
   the paper's "assembled chart expansions", or is the gluing needed before the paper can cite it?
2. **The spectrum is a superset.** `spectrumLe 2 0 A'` contains every `α = m/2 ≤ A'`, including `α < d/2`
   where the oracle says the coefficient is `0` (the true expansion is `∑_j C_j N^{−d/2−j}`). The theorem
   holds as stated (those `cubeCoefficient`s ARE zero by uniqueness CCCVIII/CutoffExpansion.coeff_unique +
   the leading term CCLXXXIII `cubeIntegral_isEquivalent ~ c N^{−d/2}`), but vanishing is not proved. Also
   odd `m` (half-integer shifts) should vanish by the odd-order cancellation you predicted. Should we prove
   (a) `cubeCoefficient q = 0` for `q.exponent < d/2`, (b) `cubeCoefficient (d/2, 0) = π^{d/2}·F(0)p(0)`
   (CCXCV), (c) vanishing at `α ∉ d/2 + ℕ`? Which is the cheapest route — via uniqueness against a
   known expansion, or termwise on the certificate (odd normal orders vanish pointwise on each piece and the
   two orthant sides cancel, as in G7's `synthetic_cancellation`)?
3. **Fidelity of the pieces.** Each piece uses the positive-part representative `posPart priorRep` of the
   pulled-back prior (nonnegative everywhere, agreeing with the prior on `[0,1]^d`) and the indicator
   representatives `priorRep/obsRep` (zero off the real domain) — the certificate's measure and observable are
   these representatives, and the identification with the original `F, p` is only on the box
   (`obsRep_piece`, `posPart_priorRep_piece`). Is anything lost — in particular, are the jets
   `normalDifferential obsRep` at face points the jets of `F∘φ_β∘R_σ`? (They agree on the open real domain
   ⊇ box, so the germs at every base point agree; we did not restate the coefficients in terms of `F`.)
4. **The unit's role.** The singleton producer takes `λ(s) = u(s)^{−1/2}` and the exact identity `u λ² = 1`
   (`hnorm`); the face series are rescaled by `λ` in the normal variable at each base point
   (`Fϕ`, `Fφ` — `OriginalFaceSeries` in the original normal variable, then `Φ_eq_orig`). Is the
   normalisation what your #102 §5 intended (the normal coordinate `y_β ↦ √u·y_β`), and is the resulting
   moment field the one the paper would call the chart coefficient tensor (density `|y_β|^{d−1}·p·√u^{−1}`
   per unit normal length)?
5. **Next gate.** Options we see: (i) E4 gate items above (vanishing below `d/2`, leading coefficient =
   CCXCV, half-integer cancellation); (ii) E5 general partial-active collar (recovers G and E3); (iii) the
   intrinsic gluing of the chart strata (projector space / exceptional divisor as a resolved geometry with
   `π ≠ id`, the a.e.-disjoint wedge cover as a `ResolvedGeometry` on the whole cube); (iv) programme J
   (observable-independent functional); (v) an SNC atlas. Rank them for the paper, with the stopping point.
6. Any statement you would change now (names, hypotheses, non-claims), as in #99 §A4.

## 3. Material — E4 full source (Grammar/BlowUpCubeExpansion.lean)

```lean
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
```

## 4. Material — E3 key declarations (Grammar/SingletonChartCertificate.lean, extracts)

```lean
variable {d : ℕ} (β : Fin d)

/-! ### The singleton index data -/

/-- The singleton index. -/
def Iβ : NonemptyIdx d := ⟨{β}, Finset.singleton_nonempty β⟩

/-- The phase exponents: `1` at `β`, `0` elsewhere. -/
def kS : Fin d → ℕ := Pi.single β 1

...
noncomputable abbrev G (h₀ : ℕ) : ResolvedGeometry d (Fin d → ℝ) :=
  ChartModel.geometry d {β} (kS β) (hS β h₀) (hkS β)

/-- Its normal data. -/
noncomputable abbrev N (h₀ : ℕ) : ResolvedNormalData (G β h₀) (Amb d) :=
  ChartModel.normalData d {β} (kS β) (hS β h₀) (hkS β)

/-! ### The tangential unit and the widths -/

variable (u : (Fin d → ℝ) → ℝ)

/-- The unit as a function of the tangential coordinates (the point with `y_β = 0`). -/
noncomputable def unitT (t : Tan (Iβ β).1 → ℝ) : ℝ := u (liftPoint (Iβ β).1 t)

/-- The normal width `λ(t) = (√u(t))⁻¹`. -/
noncomputable def lam (t : Tan (Iβ β).1 → ℝ) : Nrm (Iβ β).1 → ℝ := fun _ => (Real.sqrt (unitT β
u t))⁻¹

/-- The width bound `(√c)⁻¹`. -/
noncomputable def Lb (c : ℝ) : ℝ := (Real.sqrt c)⁻¹

omit β u in
theorem continuous_liftPoint (I : Finset (Fin d)) : Continuous (liftPoint I) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j ∈ I
  · simp only [liftPoint_apply, dif_pos hj]
    exact continuous_const
  · simp only [liftPoint_apply, dif_neg hj]
    exact continuous_apply _

theorem liftPoint_tan_apply (y : Fin d → ℝ) {j : Fin d} (hj : j ≠ β) :
    liftPoint (Iβ β).1 (tan (Iβ β).1 y) j = y j := by
  have hj' : j ∉ (Iβ β).1 := fun h => hj (Finset.mem_singleton.1 h)
  rw [liftPoint_apply, dif_neg hj']
  rfl

variable (hu_tan : ∀ y y' : Fin d → ℝ, (∀ j, j ≠ β → y j = y' j) → u y = u y')

include hu_tan in
theorem unitT_tan (y : Fin d → ℝ) : unitT β u (tan (Iβ β).1 y) = u y :=
  hu_tan _ _ fun _ hj => liftPoint_tan_apply β y hj

/-! ### The base: the closed face -/

variable (a : ℝ) (h₀ : ℕ)

...
variable (ϕ φ : (Fin d → ℝ) → ℝ) (O : OriginalFaceSeries a ϕ φ (Iβ β)) (b b' : ℝ) (hb : 0 < b)
  (hbb' : b < b') (hb'ρ : Lb c * b' ≤ O.ρ) (hba : Lb c * b ≤ a)
  (ϕ' : (Fin d → ℝ) → ℝ) (hϕ'eq : ∀ w ∈ piBox d (Icc 0 a), ϕ' w = ϕ w)

...
noncomputable def data :
    WData (kS β) (Iβ β).1 (nI (Iβ β)) (K β a h₀) (piBox d (Icc 0 a)) ϕ' φ where
  σ := σI (Iβ β)
  e := e β a h₀
  he := continuous_e β a h₀
  he_inj := e_injective β a h₀
  lamT := lam β u
  hlamT := measurable_lam β u hu_cont
  hlam_cont := continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb
  hpos := fun _ ht j => lam_pos β u a h₀ ha c hc hu_lb ht j
  unit := unitT β u
  β := 1
  hnorm := fun _ ht => hnorm β u a h₀ ha c hc hu_lb ht
  b := b
  b' := b'
  hb := hb
  hbb' := hbb'
  hW := image_subset_box β u a h₀ ha c hc hu_lb b hb hba
  Fϕ := Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ
  Fφ := Fφ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ
  hϕ_eq := fun s _ hv =>
    (hϕ'eq _ (image_subset_box β u a h₀ ha c hc hu_lb b hb hba
      (mem_image_Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u)
        (fun _ ht j => lam_pos β u a h₀ ha c hc hu_lb ht j) s hv))).trans
      (hϕ_eq β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ s hv)
  hφ_eq := fun s _ hv => hφ_eq β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ s hv

/-! ### The localisation datum, the core and the core decomposition -/

variable (hϕm : Measurable ϕ') (hϕ0 : ∀ w, 0 ≤ ϕ' w) (hφm : Measurable φ)
...
include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- The one-core decomposition: the collar and the phase-gap tail. -/
noncomputable def cores :
    AnalyticCoreDecomposition (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint) 1
      (fun _ => K β a h₀) (fun _ => nI (Iβ β)) 1 where
  core := fun _ => (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ.restrict
    (image (Iβ β).1 (e β a h₀) (lam β u) b)
  tail := (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ.restrict
    (image (Iβ β).1 (e β a h₀) (lam β u) b)ᶜ
  measure_eq := by
    rw [Fin.sum_univ_one, Measure.restrict_add_restrict_compl (measurableSet_image (Iβ β).1 b
      (measurableEmbedding_e (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (e_injective β a h₀))
      (measurable_lam β u hu_cont))]
  δ₀ := b ^ 2
  δ₀_pos := pow_pos hb 2
  gap := gap_aux β u hu_tan a h₀ ha hu_cont c hc hu_lb φ b hb ϕ' hφint
  chart := fun _ => core β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ'
     hϕ'eq hϕm hϕ0
    hφint

/-! ### The frame -/

theorem mem_amb_singleton_univ (j : Fin d) :
    j ∈ ChartModel.amb d {β} Finset.univ ↔ j ∈ (Iβ β).1 := by
  rw [ChartModel.mem_amb]
  constructor
  · rintro ⟨hj, _⟩
    exact hj
  · intro hj
    exact ⟨hj, Finset.mem_univ _⟩

/-- The box coordinates as the ambient index set of the deepest stratum. -/
noncomputable def σ' : Fin (nI (Iβ β) + 1) ≃ ↥(ChartModel.amb d {β} Finset.univ) :=
  (σI (Iβ β)).trans (Equiv.subtypeEquivRight fun j => (mem_amb_singleton_univ β j).symm)

...
noncomputable def cert :
    ResolvedCertificate (G β h₀) (N β h₀) (piBox d (Icc 0 a)) (Kc β u)
      (fun w => wgt (hS β h₀) w * ϕ' w) φ where
  L := locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint
  obs_eq := rfl
  phase_eq := rfl
  transport := Measure.map_id
  M := 1
  n := fun _ => nI (Iβ β)
  strat := fun _ => Finset.univ
  base := fun _ => base β a h₀
  isCompact_base := fun _ => isCompact_base β a h₀
  β := 1
  β_pos := one_pos
  cores := cores β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm
     hϕ0 hφint
  T := fun _ => NormalisedBox.wpresentation (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
    (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
    (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl
  frame := fun _ s => frame β u a h₀ ha c hc hu_lb s
  Φ_eq := fun _ s v => Φ_eq_frame β u a h₀ ha c hc hu_lb s v

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- ★★ **The coefficient certificate**: density family `J H L · fϕ`, observable jets `fφ`. -/
noncomputable def coeffCert :
    (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
      hφint).CoefficientCertificate where
  cc := fun _ s γ => JW (hS β h₀) (Iβ β).1 (e β a h₀) (lam β u) s *
    (Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).f s γ
  cc_abs := fun _ s =>
    ((Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).smul
      (JW (hS β h₀) (Iβ β).1 (e β a h₀) (lam β u))
      (continuous_JW (hS β h₀) (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (lam β u)
        (continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb)) _
      (abs_JW_le (hS β h₀) (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (lam β u)
        (continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb))).absSummableAt_of_le hb.le hbb'.le s
  jet_abs := fun _ s => by
    have h := NormalisedBox.jetFamily_obsFibre_w (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    exact (congrArg (fun f => AbsSummableAt f b) h).mpr
      ((Fφ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).absSummableAt_of_le hb.le
        hbb'.le s)
  datum_eq := fun _ s => by
    have h := NormalisedBox.jetFamily_obsFibre_w (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    have h1 := NormalisedBox.toEta_wcore_x (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    exact h1.trans (congrArg (CoeffFamily.conv _) h.symm)

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφm hφint in
/-- ★★★ **The coordinate-free expansion of the singleton chart**: the weighted integral
`∫_{[0,a]^d} φ · |y_β|^{h₀} ϕ · e^{−n u(y) y_β²}` has the coordinate-free expansion on the chart
strata, with produced certificates and the spectrum of one normal coordinate. -/
theorem hasCoordFreeExpansion_singleton :
    (N β h₀).HasCoordFreeExpansion
      (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
        hφint).stratumMeasure
      (coeffCert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
        hφint).field
      (spectrumLe (commonQ (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba
        ϕ' hϕ'eq hϕm hϕ0 hφint).cores.k) (commonD (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ
     φ O b b'
        hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0 hφint).n))
      (piBox d (Icc 0 a)) (Kc β u) (fun w => wgt (hS β h₀) w * ϕ' w) φ :=
  (coeffCert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
    hφint).hasCoordFreeExpansion_le (hu_cont.measurable.mul ((measurable_pi_apply β).pow_const 2))
    ((measurable_wgt _).mul hϕm) (fun w => mul_nonneg (wgt_nonneg _ _) (hϕ0 w)) hφm

end SingletonChart

end Grammar
```

## 5. Material — E2 core signature and E1 geometry (extracts)

```lean
287-  exact abs_le.2 ⟨by linarith, this.2⟩
288-
289-include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
290-/-- ★★ **The weighted normalised box core**: orders `h` recorded (`h = hι h I σ`), density
291-`c_h = J H_I L_I · ϕ`, exact transport of the weighted measure, normalised phase with the unit,
292-scaled product amplitude. -/
293:noncomputable def wcore : CorePresentation L (L.μ.restrict (image I D.e D.lamT D.b)) K n D.β where
294-  ν := baseMeasure I D.e
295-  isFiniteMeasure_ν := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
296-  h := hι h I D.σ
297-  k := kι k I D.σ
298-  k_pos := fun i => hkI (D.σ i)
299-  b := D.b
300-  b_pos := D.hb
301-  Φ := Φ I D.σ D.e D.lamT
302-  measurable_Φ := measurable_Φ I D.σ (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT
303-  c := cw h I D.e D.lamT D.b D.b' D.hb D.Fϕ
304-  measurable_c :=
305-    (((continuous_JW h I D.e D.he D.lamT D.hlam_cont).comp continuous_fst).mul
...
240:structure WData (k : Fin d → ℕ) (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
241-    (W : Set (Fin d → ℝ)) (ϕ φ : (Fin d → ℝ) → ℝ) where
242-  /-- the identification of box coordinates with the normal coordinates -/
243-  σ : Fin (n + 1) ≃ Nrm I
244-  /-- the tangential coordinates of the base -/
245-  e : K → (Tan I → ℝ)
246-  he : Continuous e
247-  he_inj : Function.Injective e
248-  /-- the normal widths -/
249-  lamT : (Tan I → ℝ) → (Nrm I → ℝ)
250-  hlamT : Measurable lamT
251-  hlam_cont : ContinuousOn lamT (range e)
252-  hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j
253-  /-- the tangential phase unit and the normalised constant -/
254-  unit : (Tan I → ℝ) → ℝ
...
63:noncomputable def geometry : ResolvedGeometry d (Fin d → ℝ) where
64-  π := id
65-  continuous_π := continuous_id
66-  proper_π := isProperMap_id
67-  Component := ↥A
68-  E := fun i => {u : Fin d → ℝ | u i.1 = 0}
69-  isClosed_E := fun i => isClosed_eq (continuous_apply i.1) continuous_const
70-  k := fun i => k i.1
71-  h := fun i => h i.1
72-  k_pos := fun i => hk i.1 i.2
73-
159:noncomputable def normalData : ResolvedNormalData (geometry d A k h hk) (CoordModel.Amb d) where
160-  N := fun I _ => CoordModel.normalSpace d (amb d A I)
161-  finrank_N := fun I _ => (CoordModel.finrank_normalSpace d _).trans (card_amb d A I)
162-  finiteDimensional_N := fun _ _ => inferInstance
163-  du := fun I _ => du d A I
164-  du_linearIndependent := fun I _ => linearIndependent_du d A I
165-  Φ := fun _ s v => fun i => s.1 i + (v : CoordModel.Amb d) i
166-  Φ_zero := fun _ s => by
167-    funext i
```

## 6. Material — the leading-order results already available for the gate items

* CCLXXXIII `BlowUpCube.cubeIntegral_isEquivalent : (fun N => ∫_{cube} F p e^{−N K}) ~[atTop] fun N => c · N^{−d/2}`
  (analytic `F, p`, `d ≥ 2`); CCLXXXIV `coeff_eq_pi_rpow : c = π^{d/2}` for `F = p = 1`; CCXCV
  `BlowUpCube.leadingMeasure_eq : leadingMeasure = π^{d/2} δ₀`.
* CCCVIII `expansionCoefficient_eq_of_certificates` (canonicity), `CutoffExpansion.coeff_unique`,
  `CutoffExpansion.coeff_eq_of_lattices` (uniqueness of finite-cutoff expansions on a declared lattice).
* G7 (CCCXLII): `reflTensor_evalV_basis_pair`, `synthetic_cancellation` (odd observable → 0),
  `synthetic_order_zero`, `sum_sgn_zero` — the reflection cancellation mechanics on the coordinate model.
