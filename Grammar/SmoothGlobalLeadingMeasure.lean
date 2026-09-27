/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolvedExtremalLocalisation

/-!
# The global leading measure and the extremal stratum measure (polar-distribution plan, unit 21)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The extremal stratum measure `ν^{λ*}_{m*}` of the
library lives on the open stratum `X = U ∖ D_{m*+1}` and is characterised by its integrals of the
smooth TEST functions (compactly supported in `X`); the raw leading measure `ρ^{λ*}_{m*}` of unit 19
lives on all of `U` and represents the coefficient functional on EVERY smooth observable (unit 20).
On the tests the two representations agree, so by the uniqueness theorem
`eq_stratumMeasure_of_tests` (regularity of the restriction of a finite measure to an open subset
of the σ-compact metrisable manifold `U`):

  `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`  (★★★ `extremalStratumMeasure_eq_leadingResidue`)

Pushing forward along `X ↪ U` gives the GLOBAL extremal stratum measure
`globalExtremalStratumMeasure = Γ(λ*)/(m*−1)! · ρ|_X` on `U`
(★★★ `globalExtremalStratumMeasure_eq_restrict`), and it is the full multiple
`Γ(λ*)/(m*−1)! · ρ` exactly when the raw measure gives the deep fibre `D_{m*+1} ∩ Z₀` measure zero
(★★ `globalExtremalStratumMeasure_eq_iff`).  In particular the extremal stratum measure is FINITE
with total mass `Γ(λ*)/(m*−1)! · ρ(X)` (`extremalStratumMeasure_univ`,
`isFiniteMeasure_extremalStratumMeasure`) — the deep-fibre nullity itself (the statement that the
raw measure charges no point of depth `> m*`) is left to the intrinsic-depth/coordinate-wall bridge.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The raw leading measure on the open stratum -/

theorem measurableSet_stratumOpen (m : ℕ) : MeasurableSet (Ξ.stratumOpen m) :=
  (Ξ.isOpen_stratumOpen m).measurableSet

theorem measurableSet_deepZeroFibre (m : ℕ) : MeasurableSet (Ξ.deepZeroFibre m) :=
  (Ξ.isCompact_deepZeroFibre m).isClosed.measurableSet

/-- The raw leading measure restricted to the open stratum `X = U ∖ D_{m+1}`. -/
noncomputable def leadingResidueMeasureX (lam : ℝ) (m : ℕ) : Measure (Ξ.stratumOpen m) :=
  (Ξ.leadingResidueMeasureU Y lam m).comap Subtype.val

theorem integral_leadingResidueMeasureX (lam : ℝ) (m : ℕ) (G : Ξ.R.U → ℝ) :
    ∫ x, G x.1 ∂(Ξ.leadingResidueMeasureX Y lam m) =
      ∫ x in Ξ.stratumOpen m, G x ∂(Ξ.leadingResidueMeasureU Y lam m) :=
  integral_subtype_comap (Ξ.measurableSet_stratumOpen m) G

theorem leadingResidueMeasureX_apply (lam : ℝ) (m : ℕ) (s : Set (Ξ.stratumOpen m)) :
    Ξ.leadingResidueMeasureX Y lam m s = Ξ.leadingResidueMeasureU Y lam m (Subtype.val '' s) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).comap_apply _ _

/-- The raw leading measure is regular at a chart-leading pair (finite on the σ-compact
metrisable manifold `U`). -/
theorem regular_leadingResidueMeasureU {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureU Y lam m).Regular :=
  haveI := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem regular_leadingResidueMeasureX {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureX Y lam m).Regular :=
  haveI := Ξ.regular_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.comap' _ (Ξ.isOpen_stratumOpen m).isOpenEmbedding_subtypeVal

/-! ### The extremal stratum measure is the raw leading measure on the stratum -/

/-- ★★★ **The extremal stratum measure is the raw leading measure on the open stratum**:
`ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`. -/
theorem extremalStratumMeasure_eq_leadingResidue {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m := by
  symm
  have := Ξ.regular_leadingResidueMeasureX Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  have : (ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m).Regular :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  unfold extremalStratumMeasure
  refine Ξ.eq_stratumMeasure_of_tests Y hm _ _ fun G hG hGt => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    Ξ.integral_leadingResidueMeasureX, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => image_eq_zero_of_notMem_tsupport fun hx' => hx (hGt.2 hx')]
  exact (Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm hG).symm

/-- The total mass of the extremal stratum measure is `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(X)`. -/
theorem extremalStratumMeasure_univ {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ =
      ENNReal.ofReal (residueConst lam m) * Ξ.leadingResidueMeasureU Y lam m (Ξ.stratumOpen m) := by
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.smul_apply, smul_eq_mul,
    Ξ.leadingResidueMeasureX_apply, image_univ, Subtype.range_coe]

/-- ★ The extremal stratum measure is finite under the certificate. -/
theorem isFiniteMeasure_extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.extremalStratumMeasure Y h hm) := by
  have := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  refine ⟨?_⟩
  rw [Ξ.extremalStratumMeasure_univ Y h hc hμ hm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-! ### The global extremal stratum measure on `U` -/

/-- ★★★ **The global extremal stratum measure** on `U`: the pushforward of `ν^{λ*}_{m*}` along
`X ↪ U`. -/
noncomputable def globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure Ξ.R.U :=
  (Ξ.extremalStratumMeasure Y h hm).map Subtype.val

/-- ★★★ **The global extremal stratum measure is the raw leading measure restricted to the open
stratum**: `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_{U ∖ D_{m*+1}}`. -/
theorem globalExtremalStratumMeasure_eq_restrict {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm = ENNReal.ofReal (residueConst lam m) •
      (Ξ.leadingResidueMeasureU Y lam m).restrict (Ξ.stratumOpen m) := by
  unfold globalExtremalStratumMeasure
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.map_smul,
    leadingResidueMeasureX, map_comap_subtype_coe (Ξ.measurableSet_stratumOpen m)]

/-- ★★ **The raw leading measure is the global extremal stratum measure exactly when the deep
fibre is null**: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on `U` iff
`ρ^{λ*}_{m*}(D_{m*+1} ∩ Z₀) = 0`. -/
theorem globalExtremalStratumMeasure_eq_iff {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
        ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m ↔
      Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0 := by
  rw [Ξ.globalExtremalStratumMeasure_eq_restrict Y h hc hμ hm]
  constructor
  · intro heq
    have hc0 : ENNReal.ofReal (residueConst lam m) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (residueConst_pos hμ m)).ne'
    have := congrArg (fun ν : Measure Ξ.R.U => ν (Ξ.deepZeroFibre m)) heq
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (Ξ.measurableSet_deepZeroFibre m)] at this
    rw [stratumOpen, inter_compl_self, measure_empty, mul_zero, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hc0
  · intro hnull
    rw [Measure.restrict_eq_self_of_ae_mem]
    exact compl_mem_ae_iff.2 hnull

/-- The global extremal stratum measure integrates every smooth observable vanishing off the open
stratum to the coefficient functional. -/
theorem integral_globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (G : Ξ.R.U → ℝ) :
    ∫ x, G x ∂(Ξ.globalExtremalStratumMeasure Y h hm) =
      ∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).integral_map _

end ResolvedData

end SmoothEngine

end Grammar
