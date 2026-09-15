/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedStratumPositive
import Grammar.SmoothResolvedRLCTIndex

/-!
# The Euclidean coefficients through the resolution: supports and the graded stratum formula

Consult #130, Unit E4. For a smooth observable `f` on `W`, the Euclidean coefficient
`C_{μ,q}(f)` of `∫ prior · f · e^{−NK}` is the resolved coefficient of the pull-back `f ∘ π`
(CDXXVIII). Hence:

* `C_{μ,q}` is supported on the IMAGE `π(Z₀ ∩ {r_μ ≥ q+1})` of the resonant zero fibre
  (`observableCoeff_eq_zero_of_eventually_zero_image`: `f` vanishing near the image pulls back to
  `f ∘ π` vanishing near the fibre), a refinement of Theorem C's support in the zero set;
* when `f ∘ π` vanishes near the deep zero fibre `Z₀ ∩ {depth ≥ c+1}`, `C_{μ,c−1}(f)` is the
  stratum sum of the pull-back (`observableCoeff_eq_stratumSum`), nonnegative for `f ≥ 0` under
  the zero-order condition (`observableCoeff_nonneg_of_deep`), and determined by the values of
  `f` on `π(S^μ_c)` (`observableCoeff_eq_of_eqOn_image`).

Non-claims (Astra #130 §9): different resolved strata may project to the same subset of `W`, and
the neighbourhood-vanishing hypothesis on `f ∘ π` is a genuine restriction; without it the
Euclidean coefficients retain their Taylor-subtracted chart-face formulas, and no canonical
regularised contribution of an individual stratum is asserted. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- A function vanishing near the image `π(S)` pulls back to one vanishing near `S`. -/
theorem eventually_comp_gv {S : Set Ξ.R.U} {f : (Fin d → ℝ) → ℝ}
    (hf : ∀ᶠ y in 𝓝ˢ (Ξ.R.gv '' S), f y = 0) : ∀ᶠ P in 𝓝ˢ S, f (Ξ.R.gv P) = 0 := by
  rw [eventually_nhdsSet_iff_forall] at hf ⊢
  intro P hP
  exact (Ξ.R.contMDiff_gv.continuous.continuousAt (x := P)).eventually (hf _ ⟨P, hP, rfl⟩)

/-- ★★ **Support of the Euclidean coefficients in the image of the resonant zero fibre**: an
observable on `W` vanishing near `π(Z₀ ∩ {r_μ ≥ q+1})` has vanishing `C_{μ,q}`. -/
theorem observableCoeff_eq_zero_of_eventually_zero_image {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) {μ : ℝ} {q : ℕ}
    (h0 : ∀ᶠ y in 𝓝ˢ (Ξ.R.gv '' Ξ.resonantZeroFibre μ q), f y = 0) :
    (Ξ.X Y).observableCoeff μ q f hf = 0 := by
  rw [← Ξ.coeff_comp_gv Y hf μ q]
  exact (Ξ.withF (fun P => f (Ξ.R.gv P))
    (Ξ.contMDiff_comp_gv hf)).coeff_eq_zero_of_eventually_zero_resonant Y (Ξ.eventually_comp_gv h0)

/-- ★★★ **The graded stratum formula for the Euclidean coefficients**: if `f ∘ π` vanishes near the
deep zero fibre, `C_{μ,c−1}(f)` is the stratum sum of the pull-back. -/
theorem observableCoeff_eq_stratumSum {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {c : ℕ}
    (hc : 1 ≤ c) (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0) (μ : ℝ) :
    (Ξ.X Y).observableCoeff μ (c - 1) f hf =
      (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).stratumSum Y μ c := by
  rw [← Ξ.coeff_comp_gv Y hf μ (c - 1)]
  exact (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff_eq_stratumSum Y hc h0 μ

/-- ★★ **Positivity of the Euclidean coefficient** under the zero-order condition. -/
theorem observableCoeff_nonneg_of_deep {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {μ : ℝ}
    {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0) (hf0 : ∀ y, 0 ≤ f y) :
    0 ≤ (Ξ.X Y).observableCoeff μ (c - 1) f hf := by
  rw [← Ξ.coeff_comp_gv Y hf μ (c - 1)]
  exact (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff_nonneg_of_deep Y hc hzero
    h0 fun P => hf0 _

/-- ★★ **Values-only dependence of the Euclidean coefficient** on the image `π(S^μ_c)` of the exact
stratum. -/
theorem observableCoeff_eq_of_eqOn_image {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hf0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0)
    (hg0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), g (Ξ.R.gv P) = 0)
    (heq : EqOn f g (Ξ.R.gv '' Ξ.exactStratum μ c)) :
    (Ξ.X Y).observableCoeff μ (c - 1) f hf = (Ξ.X Y).observableCoeff μ (c - 1) g hg := by
  rw [← Ξ.coeff_comp_gv Y hf μ (c - 1), ← Ξ.coeff_comp_gv Y hg μ (c - 1)]
  exact Ξ.coeff_eq_of_eqOn_exactStratum Y hc hzero (Ξ.contMDiff_comp_gv hf)
    (Ξ.contMDiff_comp_gv hg) hf0 hg0 fun P hP => heq ⟨P, hP, rfl⟩

end ResolvedData

end SmoothEngine

end Grammar
