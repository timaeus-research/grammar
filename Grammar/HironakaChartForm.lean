/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeCharts
import Monomialize.Transport.AnalyticResolutionExports
import Monomialize.Transport.ProductSectorAtlasBlowUp

/-!
# Hironaka's exact analytic chart form and product-sector atlases (consult #110, units G0/H3)

`hironaka` (local working copy, branch `sector-atlas`) exports two exact analytic outputs, both
axiom-clean: Watanabe's Theorem 2.3 (`WatanabeModification`: an analytic manifold `U`, a proper
surjective analytic `g : U → W`, an analytic isomorphism off the zero set, and at every point over
the zero set a chart with `K ∘ g ∘ φ⁻¹ = S ∏ u_i^{k_i}` EXACTLY and Jacobian `b ∏ u_i^{h_i}`, `b`
analytic nonvanishing; for `K ≥ 0` the even form `∏ u_i^{2 k_i}`), and the class of
`ProductSectorAtlas`es (box domains, analytic charts, analytic positive phase unit times an even
monomial, analytic Jacobian unit, pairwise a.e.-disjoint sector images) with EXACT weight-one
transport. This module re-exports them in the vocabulary of this library and identifies the cube
blow-up atlas of `hironaka` with the cube charts of CCCXLIII (`φ β`, `unit β`, `cube d`).

**Non-claim.** `HasProductSectorAtlas K Ω` is the hypothesis under which the certificate
programme can proceed; it is PROVED here only for the cube blow-up. Neither Watanabe's theorem
nor the chart form `Q'` supplies a product-sector atlas for a general analytic phase: making the
chart images almost disjoint while keeping product domains and analytic normal amplitudes is the
open theorem of the programme (consult #110 §4).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open Monomialize.Transport Monomialize.VolumeScaling

variable {d : ℕ}

/-! ### Watanabe's Theorem 2.3, re-exported -/

/-- ★★ **Watanabe's Theorem 2.3** (hironaka, axiom-clean): a real-analytic `K` near `0` with
`K 0 = 0`, not identically zero near `0`, has a resolution triple `(W, U, g)` with exact monomial
charts over the zero set. -/
theorem exists_watanabeModification_of_analytic {U₀ : Set (Fin d → ℝ)} (hU₀ : IsOpen U₀)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U₀) (h0 : K 0 = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K x = 0) (h0U : (0 : Fin d → ℝ) ∈ U₀) :
    Nonempty (WatanabeModification K U₀) :=
  exists_watanabeModification hU₀ hK h0 hne h0U

/-- For a phase nonnegative on `U₀` every chart of the triple is even (`S = 1`, exponents
`2 k_i`). -/
theorem WatanabeModification.evenChartAt {U₀ : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ}
    (M : WatanabeModification K U₀) (hK0 : ∀ x ∈ U₀, 0 ≤ K x) (P : M.toOn.U)
    (hP : K ((Monomialize.Manifold.AnalyticManifold.model ℝ (Fin d → ℝ)).inclusion M.W
      (M.toOn.g P)) = 0) :
    WatanabeEvenChartAt K M.toOn.g P :=
  Monomialize.Transport.WatanabeChartAt.even_of_nonneg (M.toOn.chartAt P hP)
    fun x hx => hK0 x (M.W_subset hx)

/-! ### Product-sector atlases -/

/-- **The product-sector hypothesis** for a phase `K` on a domain `Ω`: a `ProductSectorAtlas`
exists. Proved below for the cube blow-up; NOT claimed for general analytic phases. -/
def HasProductSectorAtlas (K : (Fin d → ℝ) → ℝ) (Ω : Set (Fin d → ℝ)) : Prop :=
  Nonempty (ProductSectorAtlas d K Ω)

namespace BlowUpCube

theorem sumSq_eq_K : (sumSq : (Fin d → ℝ) → ℝ) = K := rfl

theorem fullBlock_eq_B : fullBlock d = B d := rfl

theorem centeredBox_one_eq_cube : centeredBox d 1 = cube d := by
  rw [centeredBox_eq_pi]
  rfl

/-- ★★ **The cube blow-up atlas** of `hironaka`, for the phase `K = ∑ x_j²` on the cube
`centeredBox d 1 = [−1, 1]^d`: its charts are the cube charts `φ β` of CCCXLIII. -/
noncomputable def cubeAtlas [NeZero d] : ProductSectorAtlas d K (centeredBox d 1) :=
  cubeBlowUpAtlas 1 one_pos

theorem cubeAtlas_φ [NeZero d] (β : Fin d) : (cubeAtlas (d := d)).φ β = φ β := rfl

theorem cubeAtlas_dom [NeZero d] (β : Fin d) :
    (cubeAtlas (d := d)).dom β = blowUpChartBox (B d) β 1 := rfl

theorem cubeAtlas_phaseUnit [NeZero d] (β : Fin d) :
    (cubeAtlas (d := d)).phaseUnit β = unit β := rfl

theorem hasProductSectorAtlas_cube [NeZero d] : HasProductSectorAtlas K (centeredBox d 1) :=
  ⟨cubeAtlas⟩

/-- ★ **Exact transport on the cube**: the sum over the pivots of the push-forwards of the chart
measures with density `a ∘ φ_β · |y_β|^{d−1}` is the density `a` on the cube. -/
theorem cube_exactTransport [NeZero d] {a : (Fin d → ℝ) → ℝ≥0∞} (ha : Measurable a) :
    ∑ β : Fin d, ((volume.restrict ((cubeAtlas (d := d)).dom β)).withDensity fun x =>
      a (φ β x) * (cubeAtlas (d := d)).toPartialResolution.jacDensity β x).map (φ β) =
      (volume.restrict (cube d)).withDensity a := by
  rw [← centeredBox_one_eq_cube]
  exact (cubeAtlas (d := d)).exactTransport ha

end BlowUpCube

end Grammar
