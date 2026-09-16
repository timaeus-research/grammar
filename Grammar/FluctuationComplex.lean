/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.Fluctuation
import Mathlib.Analysis.MellinTransform

/-!
# The fluctuation function at a complex index and the Mellin transform of the tilted phase

`fluctuationCplx s a = ∫_0^∞ t^{s−1} e^{−t + a√t} dt` for `s : ℂ`, agreeing with `fluctuation 1 λ a`
at real `s = λ`, and the scaling identity

★ `mellin_exp_tilt : mellin (N ↦ e^{−NK + √N H}) s = K^{−s} · fluctuationCplx s (H/√K)`  (`K > 0`),

the pointwise input of the fluctuation zeta function `ζ_φ(s;H) = ∫ φ K^{−s} S_s(H/√K) dν_χ`
(consult #158, item 1).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Real

namespace Grammar

/-- The fluctuation function at a complex index. -/
noncomputable def fluctuationCplx (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Real.exp (-t + a * Real.sqrt t) : ℂ)

/-- At a real index the complex fluctuation function is the real one. -/
theorem fluctuationCplx_ofReal (lam a : ℝ) :
    fluctuationCplx (lam : ℂ) a = (fluctuation 1 lam a : ℂ) := by
  unfold fluctuationCplx fluctuation
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [show (lam : ℂ) - 1 = ((lam - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht0]
  push_cast
  congr 2
  ring

/-- ★ **The Mellin transform of the tilted phase**: for `K > 0`,
`∫_0^∞ N^{s−1} e^{−NK + √N H} dN = K^{−s} S_s(H/√K)`. -/
theorem mellin_exp_tilt {K : ℝ} (hK : 0 < K) (H : ℝ) (s : ℂ) :
    mellin (fun N : ℝ => (Real.exp (-N * K + Real.sqrt N * H) : ℂ)) s =
      (K : ℂ) ^ (-s) * fluctuationCplx s (H / Real.sqrt K) := by
  have hsq : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hfun : (fun N : ℝ => (Real.exp (-N * K + Real.sqrt N * H) : ℂ)) =
      fun N : ℝ => (Real.exp (-(K * N) + H / Real.sqrt K * Real.sqrt (K * N)) : ℂ) := by
    funext N
    congr 2
    rw [Real.sqrt_mul hK.le]
    have hne := hsq.ne'
    field_simp
  have h := mellin_comp_mul_left (fun t : ℝ => (Real.exp (-t + H / Real.sqrt K * Real.sqrt t) : ℂ))
    s hK
  rw [hfun]
  simp only [smul_eq_mul] at h
  rw [h]
  rfl

end Grammar
