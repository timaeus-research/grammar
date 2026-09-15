/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumMeasureExtremal

/-!
# The extremal stratum measure is finite

At extremal data `(λ*, m*)` the leading functional is nonnegative on every nonnegative observable
(`coeff_nonneg_of_extremalData`), so a cutoff `0 ≤ χ ≤ 1` has `T[χ] ≤ 𝒯^U_{λ*,m*−1}[1]`. Inner
regularity then bounds the total mass of the extremal stratum measure `ν^{λ*}_{m*}` by the
unit-observable coefficient (`extremalStratumMeasure_univ_le`): the leading stratum measure is a
FINITE measure (`IsFiniteMeasure` instance). When the deeper zero fibre `D_{m*+1}` is empty the
unit observable is admissible and the mass equals the coefficient
(`extremalStratumMeasure_univ_eq_of_deep_empty`): the total mass of the leading residue measure is
then the RLCT constant. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The leading functional is monotone: a test `χ ≤ 1` has coefficient at most that of `1`. -/
theorem coeff_le_coeff_one_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {χ : Ξ.R.U → ℝ} (hχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ) (hχ1 : ∀ P, χ P ≤ 1) :
    (Ξ.withF χ hχ).coeff Y lam (m - 1) ≤
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) := by
  have hχ' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * χ P) :=
    contMDiff_const.mul hχ
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (1 : ℝ) + (-1 : ℝ) * χ P) :=
    contMDiff_const.add hχ'
  have hnn := Ξ.coeff_nonneg_of_extremalData Y h hsum (Eventually.of_forall fun P => by
    have := hχ1 P
    change 0 ≤ (1 : ℝ) + (-1 : ℝ) * χ P
    linarith)
  rw [Ξ.coeff_add Y contMDiff_const hχ' lam (m - 1), Ξ.coeff_smul Y hχ (-1) lam (m - 1)] at hnn
  linarith

instance {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    (Ξ.extremalStratumMeasure Y h hm).Regular := by
  unfold extremalStratumMeasure
  infer_instance

/-- ★★★ **The extremal stratum measure is finite, with total mass at most the RLCT constant**
`𝒯^U_{λ*,m*−1}[1]`. -/
theorem extremalStratumMeasure_univ_le {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ ≤
      ENNReal.ofReal ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)) := by
  rw [Measure.Regular.innerRegular.measure_eq_iSup isOpen_univ]
  refine iSup₂_le fun K _ => iSup_le fun hK => ?_
  have hKc : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hKX : Subtype.val '' K ⊆ Ξ.stratumOpen m := by
    rintro P ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨χ, hχ, hχt, hχ1, hχ01⟩ := Ξ.exists_cutoff m hKc hKX
  have hle : (Ξ.extremalStratumMeasure Y h hm).real K ≤
      ∫ x, χ x.1 ∂(Ξ.extremalStratumMeasure Y h hm) := by
    rw [← integral_indicator_one hK.measurableSet]
    refine integral_mono ?_ ?_ fun x => ?_
    · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    · exact (Ξ.toCc m hχ hχt).continuous.integrable_of_hasCompactSupport
        (Ξ.toCc m hχ hχt).hasCompactSupport
    · by_cases hx : x ∈ K
      · simp [hx, hχ1 x.1 ⟨x, hx, rfl⟩]
      · simp [hx, (hχ01 x.1).1]
  have hT : ∫ x, χ x.1 ∂(Ξ.extremalStratumMeasure Y h hm) = Ξ.T Y lam m χ hχ :=
    Ξ.integral_stratumMeasure_test Y hm (Ξ.zeroOrder_of_extremalData h m) hχ hχt
  have hTle : Ξ.T Y lam m χ hχ ≤
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) :=
    Ξ.coeff_le_coeff_one_of_extremalData Y h hχ fun P => (hχ01 P).2
  calc Ξ.extremalStratumMeasure Y h hm K
      = ENNReal.ofReal ((Ξ.extremalStratumMeasure Y h hm).real K) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hK.measure_lt_top.ne]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans (hT ▸ hTle))

instance {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.extremalStratumMeasure Y h hm) :=
  ⟨(Ξ.extremalStratumMeasure_univ_le Y h hm).trans_lt ENNReal.ofReal_lt_top⟩

/-- ★★★ **Total mass when the deeper zero fibre is empty**: if `D_{m*+1} = ∅`, the unit observable
is admissible and the total mass of `ν^{λ*}_{m*}` is exactly the RLCT constant
`𝒯^U_{λ*,m*−1}[1]`. -/
theorem extremalStratumMeasure_univ_eq_of_deep_empty {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (hD : Ξ.deepZeroFibre m = ∅) :
    (Ξ.extremalStratumMeasure Y h hm).real univ =
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) := by
  have h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), (fun _ : Ξ.R.U => (1 : ℝ)) P = 0 := by
    rw [hD, nhdsSet_empty]
    exact Filter.eventually_bot
  have hrep := Ξ.coeff_withF_eq_integral_stratumMeasure Y hm (Ξ.zeroOrder_of_extremalData h m)
    contMDiff_const h0
  change _ = (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)
  rw [hrep]
  change (Ξ.extremalStratumMeasure Y h hm).real univ =
    ∫ _, (1 : ℝ) ∂(Ξ.extremalStratumMeasure Y h hm)
  rw [integral_const, measureReal_def, smul_eq_mul, mul_one]

end ResolvedData

end SmoothEngine

end Grammar
