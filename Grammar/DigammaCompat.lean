/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthFiveJetClosed

/-!
# Compatibility with Mathlib's digamma, and reality of the digamma jets

`gammaLogDeriv = Complex.digamma` (Mathlib's `logDeriv Gamma`; `gammaLogDeriv_eq_digamma`), so
Mathlib's `digamma_one_half` is a regression for `ψ½_0 = −2 log 2 − γ` (`psiHalfCoeff_zero`); and
the one-point recurrence with DCLXXIII's real Gamma jets gives that every `ψ_j` is real
(`psiOneCoeff_im`), so the symbols `λ₄ = (6ψ₃).re`, `λ₅ = (24ψ₄).re` are the complex coefficients
themselves (`psiOneCoeff_three_eq`, `psiOneCoeff_four_eq`).  Astra round 27 bookkeeping.
Zero `sorry`/`axiom`.
-/

open Finset

namespace Grammar

theorem gammaLogDeriv_eq_digamma : gammaLogDeriv = Complex.digamma := by
  funext z
  rw [Complex.digamma_def, logDeriv_apply]
  rfl

/-- `ψ½_0 = −2 log 2 − γ` (Mathlib's `digamma_one_half`). -/
theorem psiHalfCoeff_zero :
    psiHalfCoeff 0 = -2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) := by
  rw [psiHalfCoeff, taylorCoeff_zero', gammaLogDeriv_eq_digamma, Complex.digamma_one_half]

/-- The Gamma jets at `1` are real: `g_r = G_r/r!`. -/
theorem gammaOneCoeff_eq_ofReal (r : ℕ) :
    gammaOneCoeff r = ((gammaOneLogMoment r / r.factorial : ℝ) : ℂ) := by
  rw [gammaOneCoeff, taylorCoeff, iteratedDeriv_eq_iterate, ← gammaOneLogMoment_eq_iterate]
  push_cast
  ring

theorem gammaOneCoeff_im (r : ℕ) : (gammaOneCoeff r).im = 0 := by
  rw [gammaOneCoeff_eq_ofReal, Complex.ofReal_im]

/-- `ψ_n = (n+1)g_{n+1} − Σ_{j<n} ψ_j g_{n−j}` (the recurrence solved for `ψ_n`). -/
theorem psiOneCoeff_eq_of_recurrence (n : ℕ) :
    psiOneCoeff n = ((n : ℂ) + 1) * gammaOneCoeff (n + 1) -
      ∑ j ∈ range n, psiOneCoeff j * gammaOneCoeff (n - j) := by
  have h := gammaOneCoeff_succ_mul n
  rw [Finset.sum_range_succ, Nat.sub_self, gammaOneCoeff_zero, mul_one] at h
  rw [h]
  ring

/-- Every `ψ_j` is real. -/
theorem psiOneCoeff_im (n : ℕ) : (psiOneCoeff n).im = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [psiOneCoeff_eq_of_recurrence, Complex.sub_im, Complex.mul_im, gammaOneCoeff_im,
      Complex.im_sum]
    have hsum : ∑ j ∈ range n, (psiOneCoeff j * gammaOneCoeff (n - j)).im = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Complex.mul_im, ih j (Finset.mem_range.1 hj), gammaOneCoeff_im]
      ring
    rw [hsum]
    simp

theorem psiOneCoeff_three_eq : psiOneCoeff 3 = ((gammaLogFourthOne / 6 : ℝ) : ℂ) := by
  unfold gammaLogFourthOne
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [psiOneCoeff_im]

theorem psiOneCoeff_four_eq : psiOneCoeff 4 = ((gammaLogFifthOne / 24 : ℝ) : ℂ) := by
  unfold gammaLogFifthOne
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [psiOneCoeff_im]

end Grammar
