/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DigammaSeriesComplex
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The Gaussian deep linear network through depth five, in ζ-values

The reader-facing closure of §2: with `ζ₃ = Re ζ(3)`, `ζ₅ = Re ζ(5)` (real, `riemannZeta_three_im`),
`ζ(2) = π²/6`, `ζ(4) = π⁴/90` (Mathlib), and `c₁ = 4 log 2 − 2γ`, `b = 5 log 2 − 3γ`,
`a = 6 log 2 − 4γ`:

  `Q₃ = [c₁³/6 + c₁π²/2 + (4/3)ζ₃]/(4π)`,  `D₄ = (2b³ + 7π²b + 12ζ₃)/(24π√(2π))`,
  `D₅ = [a³/6 + 2π²a/3 + (2/3)ζ₃]/(4π²)`,  `E₅ = [a⁴/24 + π²a²/3 + (2/3)aζ₃ + 5π⁴/18]/(4π²)`,
  `Q₅ = [a⁵/120 + π²a³/9 + a²ζ₃/3 + 5π⁴a/18 + 4π²ζ₃/9 + (26/5)ζ₅]/(8π²)`,

by rewriting the symbolic forms of DCLXXII, DCLXXIII, DCLXXIX with the ζ-bridge (DCLXXXIII).  Also
the regression `psiOneCoeff 1 = ζ(2)`.  Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

/-- `ζ(3)` is real. -/
theorem riemannZeta_three_im : (riemannZeta 3).im = 0 := by
  have h := psiOneCoeff_im 2
  rw [psiOneCoeff_two_eq_zeta, Complex.neg_im] at h
  linarith

theorem riemannZeta_five_im : (riemannZeta 5).im = 0 := by
  have h := psiOneCoeff_im 4
  rw [psiOneCoeff_four_eq_zeta, Complex.neg_im] at h
  linarith

theorem riemannZeta_four_re : (riemannZeta 4).re = Real.pi ^ 4 / 90 := by
  rw [riemannZeta_four, ← Complex.ofReal_pow, Complex.div_ofNat_re, Complex.ofReal_re]

/-- Regression: `ψ₁ = ζ(2) = π²/6` (DCLXXVII's value against Mathlib's `riemannZeta_two`). -/
theorem psiOneCoeff_one_eq_zeta : psiOneCoeff 1 = riemannZeta 2 := by
  rw [psiOneCoeff_one, riemannZeta_two]
  push_cast
  ring

theorem gammaLogThirdOne_eq : gammaLogThirdOne = -2 * (riemannZeta 3).re :=
  gammaLogThirdOne_eq_zeta

theorem gammaLogFourthOne_eq_pi : gammaLogFourthOne = Real.pi ^ 4 / 15 := by
  rw [gammaLogFourthOne_eq_zeta, riemannZeta_four_re]
  ring

theorem gammaLogFifthOne_eq : gammaLogFifthOne = -24 * (riemannZeta 5).re :=
  gammaLogFifthOne_eq_zeta

/-- ★★★ `c₃ = c₁³/6 + c₁π²/2 + (4/3)ζ(3)`. -/
theorem depthThreeJetCubic_eq_zeta :
    depthThreeJetCubic = depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 +
      4 / 3 * (riemannZeta 3).re := by
  rw [depthThreeJetCubic_eq_logThird, gammaLogThirdOne_eq]
  ring

/-- ★★★ `Q₃ = [c₁³/6 + c₁π²/2 + (4/3)ζ(3)]/(4π)`. -/
theorem residualMass_three_eq_zeta :
    residualMass 3 (enginePoly 3) = (depthThreeJetLinear ^ 3 / 6 +
      depthThreeJetLinear * Real.pi ^ 2 / 2 + 4 / 3 * (riemannZeta 3).re) / (4 * Real.pi) := by
  rw [residualMass_three_eq_jet, depthThreeJetCubic_eq_zeta]

/-- ★★★ `D₄ = (2b³ + 7π²b + 12ζ(3))/(24π√(2π))`, `b = 5 log 2 − 3γ`. -/
theorem depthFourConst_eq_zeta :
    depthFourConst =
      (2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) ^ 3 +
        7 * Real.pi ^ 2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) +
        12 * (riemannZeta 3).re) / (24 * Real.pi * Real.sqrt (2 * Real.pi)) := by
  rw [depthFourConst_eq_logThird, gammaLogThirdOne_eq]
  ring

/-- ★★★ `D₅ = [a³/6 + 2π²a/3 + (2/3)ζ(3)]/(4π²)`, `a = 6 log 2 − 4γ`. -/
theorem depthFiveLinCoeff_eq_zeta :
    depthFiveLinCoeff = (depthFiveCentring ^ 3 / 6 + 2 * Real.pi ^ 2 * depthFiveCentring / 3 +
      2 / 3 * (riemannZeta 3).re) / (4 * Real.pi ^ 2) := by
  rw [depthFiveLinCoeff_eq, gammaLogThirdOne_eq]
  ring

/-- ★★★ `E₅ = [a⁴/24 + π²a²/3 + (2/3)aζ(3) + 5π⁴/18]/(4π²)`. -/
theorem depthFiveConst_eq_zeta :
    depthFiveConst = (depthFiveCentring ^ 4 / 24 + Real.pi ^ 2 * depthFiveCentring ^ 2 / 3 +
      2 / 3 * depthFiveCentring * (riemannZeta 3).re + 5 * Real.pi ^ 4 / 18) /
      (4 * Real.pi ^ 2) := by
  rw [depthFiveConst_eq, gammaLogThirdOne_eq, gammaLogFourthOne_eq_pi]
  ring

/-- ★★★ `Q₅ = [a⁵/120 + π²a³/9 + a²ζ(3)/3 + 5π⁴a/18 + 4π²ζ(3)/9 + (26/5)ζ(5)]/(8π²)`. -/
theorem residualMass_five_eq_zeta :
    residualMass 5 (enginePoly 5) = (depthFiveCentring ^ 5 / 120 +
      Real.pi ^ 2 * depthFiveCentring ^ 3 / 9 + depthFiveCentring ^ 2 * (riemannZeta 3).re / 3 +
      5 * Real.pi ^ 4 * depthFiveCentring / 18 + 4 * Real.pi ^ 2 * (riemannZeta 3).re / 9 +
      26 / 5 * (riemannZeta 5).re) / (8 * Real.pi ^ 2) := by
  rw [residualMass_five_eq, gammaLogThirdOne_eq, gammaLogFourthOne_eq_pi, gammaLogFifthOne_eq]
  ring

end Grammar
