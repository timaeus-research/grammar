/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensityLeadCoeff
import Grammar.SpectralCoefficients

/-!
# Shifting the state density by one exponent (Programme Q, N2, unit 315a)

Inserting the energy `u^{2k}` multiplies the state density of `u^{h+γ}` (with respect to
`K = u^{2k}`) by `t`: in the power–log representation every exponent moves up by one and the
coefficients are unchanged. Formally the convolution calculus commutes with the shift
(`PowLogRep.conv_shift`), so `stateDensityRep n (w + 1) = shift 1 (stateDensityRep n w)`
(`stateDensityRep_shift`), coefficient extraction transports (`PowLogRep.coeffAt_shift`), and the
monomial weights of `h + 2k` are those of `h` plus one (`monoWeights_add_two_k`). Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Grammar

namespace PowLogRep

theorem shift_smul (a r : ℝ) (c : PowLogRep) : shift a (smul r c) = smul r (shift a c) := by
  unfold shift smul
  simp [List.map_map, Function.comp_def]

theorem shift_shift (a b : ℝ) (c : PowLogRep) : shift a (shift b c) = shift (b + a) c := by
  unfold shift
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext t
  simp only [Prod.mk.injEq, and_true]
  ring

theorem shift_cons (a : ℝ) (t : ℝ × ℕ × ℝ) (c : PowLogRep) :
    shift a (t :: c) = (t.1 + a, t.2.1, t.2.2) :: shift a c := rfl

theorem shift_flatMap (a : ℝ) (c : PowLogRep) (f : ℝ × ℕ × ℝ → PowLogRep) :
    shift a (c.flatMap f) = c.flatMap fun t => shift a (f t) := by
  unfold shift
  rw [List.map_flatMap]

/-- The basis convolution commutes with the unit shift. -/
theorem basisConv_shift (w : ℝ) (t : ℝ × ℕ × ℝ) :
    basisConv (w + 1) (t.1 + 1, t.2.1, t.2.2) = shift 1 (basisConv w t) := by
  unfold basisConv
  by_cases h : t.1 = w + 1
  · rw [if_pos (by simp [h]), if_pos h]
    rfl
  · rw [if_neg (by simpa using h), if_neg h, shift_smul, shift_shift]
    simp only
    congr 2
    · ring
    · congr 1
      ring

/-- The convolution commutes with the unit shift. -/
theorem conv_shift (w : ℝ) (c : PowLogRep) : conv (w + 1) (shift 1 c) = shift 1 (conv w c) := by
  unfold conv
  rw [shift_flatMap]
  conv_lhs => unfold shift
  rw [List.flatMap_map]
  congr 1
  funext t
  exact basisConv_shift w t

/-- Coefficient extraction transports along the unit shift. -/
theorem coeffAt_shift (c : PowLogRep) (μ : ℝ) (q : ℕ) :
    coeffAt (shift 1 c) (μ + 1) q = coeffAt c μ q := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    rw [shift_cons, coeffAt_cons, coeffAt_cons, ih]
    congr 1
    simp only [add_left_inj]

end PowLogRep

/-- **The state density of the shifted weights is the shifted state density.** -/
theorem stateDensityRep_shift : ∀ (n : ℕ) (w : Fin (n + 1) → ℝ),
    stateDensityRep n (fun i => w i + 1) = PowLogRep.shift 1 (stateDensityRep n w)
  | 0, w => rfl
  | n + 1, w => by
    rw [stateDensityRep_succ, stateDensityRep_succ]
    have htail : (Fin.tail fun i => w i + 1) = fun i => Fin.tail w i + 1 := rfl
    rw [htail, stateDensityRep_shift n (Fin.tail w)]
    exact PowLogRep.conv_shift (w 0) _

/-- The monomial weights of `h + 2k` are those of `h` plus one. -/
theorem monoWeights_add_two_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    monoWeights (fun i => h i + 2 * k i) k = fun i => monoWeights h k i + 1 := by
  funext i
  unfold monoWeights
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  field_simp
  push_cast
  ring

end Grammar
