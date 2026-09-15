/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalResolvedExpansion
import Grammar.EmpiricalRectReplacement
import Grammar.SmoothResolvedStratumFormula

/-!
# The resolved graded empirical formula (§20, consult #143 priority 2b)

For a smooth root field `ξ` and an observable `F` vanishing near the deep zero fibre
`D_{c+1} = Z₀ ∩ {depth ≥ c+1}`, the coefficient of the resolved empirical expansion at the top
logarithmic power `(μ, c − 1)` is the **branchwise weighted stratum sum** (★★★
`resolvedCoeff_eq_empStratumSum`): over the pieces `p` and the base points `s`, the population
stratum term of the piece with the amplitude replaced by
`amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)` — the replacement rule `∂^α A ↦ ∂^α[A S_μ(ζ)]/Γ(μ)`
applied branch by branch (`pieceCoeff_top_eq_smoothCoeff`), where `ζ = Lψ_p ∘ Tm_{p,s}` is the
smooth branch representative of the field on the piece. The inputs are the cube replacement rule
(`empCoeffRect_top_eq_smoothCoeff`) and the deep vanishing of the chart amplitudes within the
piece boxes (`deepVanishing_amp`, from `Gloc_eventually_zero_deep`). Above the depth the
coefficients vanish (`resolvedCoeff_eq_zero_of_deep`); with `c − 1` in place of `c` the same theorem
shows that for `c ≥ 2` the coefficient annihilates `𝓘_c`, so it defines a functional on
`𝓘_{c+1}/𝓘_c`, presented branchwise. Non-claim: the sum is NOT asserted to be the population coefficient of
a globally defined amplitude on the resolved manifold — the branch representatives need not
descend across the walls (consult #143). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Deep vanishing of the chart amplitudes -/

/-- ★ **The piece amplitude vanishes near the deep set of the piece box, within the box**, when
`F` vanishes near the deep zero fibre. -/
theorem deepVanishing_amp {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    DeepVanishing ((Ξ.amp Y p).amp s) (Y.T.a p.1) c := by
  intro v hv
  obtain ⟨hvbox, hcard⟩ := hv
  have hvJ : ∀ i ∈ (univ : Finset (Fin ((Ξ.X Y).da p))).filter (fun i => v i = 0), v i = 0 :=
    fun i hi => (mem_filter.1 hi).2
  have h1 := ((Ξ.continuous_facePt Y p s).tendsto v).eventually
    (Ξ.Gloc_eventually_zero_deep Y hF p s _ hcard hvbox hvJ)
  refine h1.mono fun w hw hwbox => ?_
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hwbox)]
  exact hw

namespace SmoothRootField

variable {Ξ Y} (ξ : Ξ.SmoothRootField Y)

/-- The smooth branch representative of the field on a piece, at a base point. -/
theorem contDiff_branch (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ContDiff ℝ ∞ fun v => ξ.Lψ p ((Ξ.X Y).Tm p s v) :=
  (ξ.Lψ_smooth p).comp (contDiff_affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s))

/-- The replaced amplitude of a piece: `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)`. -/
noncomputable def replacedAmp (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) : (Fin ((Ξ.X Y).da p) → ℝ) → ℝ :=
  fun v => (Ξ.amp Y p).amp s v * fluctuation 1 μ (ξ.Lψ p ((Ξ.X Y).Tm p s v)) / Real.Gamma μ

theorem contDiff_replacedAmp (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {μ : ℝ} (hμ : 0 < μ) : ContDiff ℝ ∞ (ξ.replacedAmp p s μ) :=
  (contDiff_mul_fluctuation ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s) hμ).div_const _

theorem jetsZeroOn_replacedAmp {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {μ : ℝ} (hμ : 0 < μ) :
    JetsZeroOn (ξ.replacedAmp p s μ) (deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) :=
  jetsZeroOn_of_deepVanishing (ξ.contDiff_replacedAmp p s hμ) (Y.T.a_pos p.1)
    ((Ξ.deepVanishing_amp Y hF p s).mono_fun fun v hv => by
      simp only [replacedAmp, hv, zero_mul, zero_div])

/-! ### The branchwise replacement rule -/

/-- ★★ **The branchwise replacement rule**: the piece coefficient at the top power is the base
integral of the population cube coefficient of the replaced amplitude. -/
theorem pieceCoeff_top_eq_smoothCoeff {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) (p : (Ξ.X Y).PIdx) :
    ξ.pieceCoeff p μ (c - 1) =
      ∫ s, smoothCoeff (ξ.replacedAmp p s μ) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) 1 (Y.T.a p.1) μ (c - 1)
        ∂(Ξ.piecePresentation Y p).ν := by
  unfold pieceCoeff
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact empCoeffRect_top_eq_smoothCoeff ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s)
    ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hμ hc (Ξ.deepVanishing_amp Y hF p s)

/-- ★ **Vanishing above the depth**: the resolved empirical coefficients of log degree `≥ c`
vanish for observables vanishing near `D_{c+1}`. -/
theorem resolvedCoeff_eq_zero_of_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (μ : ℝ) {q : ℕ} (hq : c ≤ q) : ξ.resolvedCoeff μ q = 0 := by
  unfold resolvedCoeff pieceCoeff
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)]
  exact empCoeffRect_eq_zero_of_deep ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s)
    (Y.T.a_pos p.1) (Ξ.deepVanishing_amp Y hF p s) μ hq

/-! ### The branchwise weighted stratum sum -/

/-- The empirical stratum term of a piece at a base point: the population stratum term
(`pieceStratumSum`) with the amplitude replaced by `amp · S_μ(ζ)/Γ(μ)`. -/
noncomputable def empPieceStratumSum (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter (fun J => J.card = c),
    faceW J (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) *
      (faceCoef ((Ξ.X Y).kA p) 1 (Y.T.a p.1) J
          (fun i => resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i + (Ξ.X Y).hA p i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) (lJ J)
            (ξ.replacedAmp p s μ) (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => 2 * (Ξ.X Y).kA p i)
          (Y.T.a p.1) μ 0)

/-- The branchwise weighted stratum sum: the empirical stratum terms integrated over the bases
and summed over the pieces. -/
noncomputable def empStratumSum (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ p, ∫ s, ξ.empPieceStratumSum p s μ c ∂(Ξ.piecePresentation Y p).ν

/-- ★★★ **The resolved graded empirical formula**: for an observable vanishing near the deep zero
fibre `D_{c+1}`, the resolved empirical coefficient at `(μ, c − 1)` is the branchwise weighted
stratum sum with the amplitudes `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s})/Γ(μ)`. -/
theorem resolvedCoeff_eq_empStratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    ξ.resolvedCoeff μ (c - 1) = ξ.empStratumSum μ c := by
  unfold resolvedCoeff empStratumSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ξ.pieceCoeff_top_eq_smoothCoeff hc hF hμ p]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact smoothCoeff_eq_faceSum_top (ξ.contDiff_replacedAmp p s hμ) _ _ ((Ξ.X Y).kA_pos p) one_pos
    (Y.T.a_pos p.1) μ hc (ξ.jetsZeroOn_replacedAmp hF p s hμ)

end SmoothRootField

end ResolvedData

end SmoothEngine

end Grammar
