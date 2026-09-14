/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedCoefficient
import Grammar.SmoothCoeffJetBound

/-!
# The chart-wise jet bound on the resolved coefficient functionals

Consult #127, Unit D3b (consult #128 follow-up (2)). The resolved coefficient functional
`𝒯^U_{μ,q}[F]` is bounded by a constant times the chart-wise `C^R` seminorm of the observable:

  `|𝒯^U_{μ,q}[F]| ≤ jetConstU μ q · M`  whenever  `‖D^r (F ∘ φ_i⁻¹)(u)‖ ≤ M` for all resolution
  charts `i`, all `u` in the closed chart box and all `r ≤ engineOrder μ`

(`abs_coeff_le_of_chartJetBound`, hypothesis `ChartJetBound`). This is the continuity of
`𝒯^U_{μ,q}` for the smooth topology on `U` read in the finitely many resolution charts of the
transport, with the same finite order `engineOrder μ` (the sum of the engine's Taylor depths over
a piece) as Theorem C's Euclidean bound (CDXVI). The proof is Theorem C's: the chart amplitude
factors on the box as the transport density times the smooth extension of the chart
representative `F ∘ φ_i⁻¹` (`amp_eq_mul`), the density family has a uniform rectangular bound,
the observable family inherits the rectangular bound from the jet bound through the affine chart
coordinate (`rectBound_obsfamU`; no chain rule through an analytic chart map is needed since the
hypothesis is already stated in the resolution charts), and the engine's quantitative bound
(`abs_smoothCoeff_le`) gives each piece.

Non-claims: the constant depends on the transport `Y` (the coefficient does not); no
test-function space on the manifold `U` is constructed; the order is an upper bound.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The smooth extension of the chart representative of the observable -/

theorem exists_obsExtU (i : Y.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (fun u => Ξ.F (Y.chartInv i u)) (centeredBox d (Y.T.a i)) := by
  obtain ⟨g, hg, heq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (Y.T.V_open i)
    (isCompact_centeredBox d (Y.T.a i)).isClosed (Y.T.box_subset_V i)
    ((Y.V_eq i) ▸ Y.contDiffOn_comp_chartInv Ξ.F_smooth i)
  exact ⟨g, hg, heq⟩

/-- The globally smooth extension of the chart representative `F ∘ φ_i⁻¹` off the box. -/
noncomputable def obsExtU (i : Y.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (Ξ.exists_obsExtU Y i)

theorem contDiff_obsExtU (i : Y.T.ι) : ContDiff ℝ ∞ (Ξ.obsExtU Y i) :=
  (Classical.choose_spec (Ξ.exists_obsExtU Y i)).1

theorem obsExtU_eq (i : Y.T.ι) {u : Fin d → ℝ} (hu : u ∈ centeredBox d (Y.T.a i)) :
    Ξ.obsExtU Y i u = Ξ.F (Y.chartInv i u) := (Classical.choose_spec (Ξ.exists_obsExtU Y i)).2 hu

/-- The observable family of a piece: `s ↦ (F ∘ φ⁻¹)^{ext} ∘ T_s`. -/
noncomputable def obsfamU (p : (Ξ.X Y).PIdx) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine ((Ξ.X Y).continuous_sc p) ((Ξ.X Y).eqv p) p.2
    (Ξ.contDiff_obsExtU Y p.1) (Y.T.a p.1)

/-- On the box the piece amplitude factors as density times observable. -/
theorem amp_eq_mul (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : ∀ j, v j ∈ Icc 0 (Y.T.a p.1)) :
    (Ξ.amp Y p).amp s v = (Ξ.X Y).ρfam p s v * (Ξ.obsfamU Y p).amp s v := by
  change Ξ.G Y p.1 ((Ξ.X Y).Tm p s v) =
    (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p s v) * Ξ.obsExtU Y p.1 ((Ξ.X Y).Tm p s v)
  rw [Ξ.G_eq Y p.1 ((Ξ.X Y).Tm_mem_box p s hv), (Ξ.X Y).ρf_eq p.1 ((Ξ.X Y).Tm_mem_box p s hv),
    Ξ.obsExtU_eq Y p.1 ((Ξ.X Y).Tm_mem_box p s hv)]
  rfl

/-! ### The piece bounds -/

theorem abs_smoothCoeff_amp_le (p : (Ξ.X Y).PIdx) (μ : ℝ) (q : ℕ) {Mρ Mf : ℝ}
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (hρ : RectBound ((Ξ.X Y).ρfam p s) ((Ξ.X Y).pieceDepth p μ) (Y.T.a p.1) Mρ)
    (hf : RectBound ((Ξ.obsfamU Y p).amp s) ((Ξ.X Y).pieceDepth p μ) (Y.T.a p.1) Mf) :
    |smoothCoeff ((Ξ.amp Y p).amp s) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (Y.T.phaseConst p.1)
        (Y.T.a p.1) μ q| ≤
      (Ξ.X Y).pieceConst p μ q * (Mρ * Mf) := by
  have hcongr : smoothCoeff ((Ξ.amp Y p).amp s) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
      (Y.T.phaseConst p.1) (Y.T.a p.1) μ q =
      smoothCoeff ((((Ξ.X Y).ρfam p).mul (Ξ.obsfamU Y p)) s) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
        (Y.T.phaseConst p.1) (Y.T.a p.1) μ q := by
    refine smoothCoeff_congr_box ((Ξ.amp Y p).smooth s)
      ((((Ξ.X Y).ρfam p).mul (Ξ.obsfamU Y p)).smooth s) ((Ξ.X Y).kA_pos p)
      (Y.T.phaseConst_pos p.1) (Y.T.a_pos p.1) (fun v hv => ?_) μ q
    rw [SmoothAmplitudeFamily.mul_apply]
    exact Ξ.amp_eq_mul Y p s fun j => Ioc_subset_Icc_self (hv j (Set.mem_univ j))
  rw [hcongr, SmoothAmplitudeFamily.mul_apply]
  have hmul := RectBound.mul (((Ξ.X Y).ρfam p).smooth s) ((Ξ.obsfamU Y p).smooth s)
    (Y.T.a_pos p.1).le hρ hf
  have := abs_smoothCoeff_le (β := Y.T.phaseConst p.1)
    ((((Ξ.X Y).ρfam p).mul (Ξ.obsfamU Y p)).smooth s) ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hmul q
  rw [SmoothAmplitudeFamily.mul_apply] at this
  refine this.trans (le_of_eq ?_)
  unfold BridgeInputs.pieceConst BridgeInputs.pieceDepth
  ring

theorem abs_familyCoeff_amp_le (p : (Ξ.X Y).PIdx) (μ : ℝ) (q : ℕ) {Mρ Mf : ℝ}
    (hρ : ∀ s, RectBound ((Ξ.X Y).ρfam p s) ((Ξ.X Y).pieceDepth p μ) (Y.T.a p.1) Mρ)
    (hf : ∀ s, RectBound ((Ξ.obsfamU Y p).amp s) ((Ξ.X Y).pieceDepth p μ) (Y.T.a p.1) Mf) :
    |familyCoeff (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1)) (Ξ.amp Y p)
        ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.phaseConst p.1) (Y.T.a p.1) μ q| ≤
      (Ξ.X Y).pieceConst p μ q * (Mρ * Mf) *
        (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1)).real univ := by
  unfold familyCoeff
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs]
  exact Ξ.abs_smoothCoeff_amp_le Y p μ q s (hρ s) (hf s)

/-! ### The chart-wise jet bound -/

/-- **The chart-wise jet bound** of order `R` and size `M`: all Fréchet derivatives of order
`≤ R` of every chart representative `F ∘ φ_i⁻¹` are bounded by `M` on the closed chart box. -/
def ChartJetBound (R : ℕ) (M : ℝ) : Prop :=
  ∀ i : Y.T.ι, JetBound R (centeredBox d (Y.T.a i)) (fun u => Ξ.F (Y.chartInv i u)) M

/-- The rectangular bound of the observable family of a piece from the chart-wise jet bound. -/
theorem rectBound_obsfamU (p : (Ξ.X Y).PIdx) (μ : ℝ) {M : ℝ}
    (hJ : Ξ.ChartJetBound Y ((Ξ.X Y).engineOrder μ) M) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    RectBound ((Ξ.obsfamU Y p).amp s) ((Ξ.X Y).pieceDepth p μ) (Y.T.a p.1) M := by
  intro m hm v hv
  have hu : (Ξ.X Y).Tm p s v ∈ centeredBox d (Y.T.a p.1) := (Ξ.X Y).Tm_mem_box p s hv
  have huV : (Ξ.X Y).Tm p s v ∈ Y.T.V p.1 := Y.T.box_subset_V p.1 hu
  change |pdMulti m (List.finRange ((Ξ.X Y).da p))
    (fun v => Ξ.obsExtU Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v)) v| ≤ _
  rw [abs_pdMulti_comp_affineMap_finRange ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s)
    (Ξ.contDiff_obsExtU Y p.1) m v]
  change |pdMulti (extendIdx ((Ξ.X Y).eqv p) m) (List.finRange d) (Ξ.obsExtU Y p.1)
    ((Ξ.X Y).Tm p s v)| ≤ _
  have hF : ContDiffOn ℝ ∞ (fun u => Ξ.F (Y.chartInv p.1 u)) (Y.T.V p.1) :=
    (Y.V_eq p.1) ▸ Y.contDiffOn_comp_chartInv Ξ.F_smooth p.1
  rw [pdMulti_eqOn_centeredBox (Y.T.V_open p.1) (Y.T.a_pos p.1) (Y.T.box_subset_V p.1)
    (Ξ.contDiff_obsExtU Y p.1).contDiffOn hF (fun u hu => Ξ.obsExtU_eq Y p.1 hu) _ _ hu]
  refine (abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem (Y.T.V_open p.1) hF _ huV).trans ?_
  refine hJ p.1 _ ?_ _ hu
  rw [sum_extendIdx]
  exact (Finset.sum_le_sum fun j _ => hm j).trans ((Ξ.X Y).sum_pieceDepth_le_engineOrder p μ)

/-- ★ **The jet-bound constant** of the resolved expansion at `(μ, q)`. -/
noncomputable def jetConstU (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ I : Fin (Fintype.card (Ξ.X Y).PIdx), (Ξ.X Y).pieceConst ((Ξ.X Y).en I) μ q *
    (Ξ.X Y).densityBound ((Ξ.X Y).en I) μ *
      (baseMeasure ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)
        (Y.T.h ((Ξ.X Y).en I).1)).real univ

theorem jetConstU_nonneg (μ : ℝ) (q : ℕ) : 0 ≤ Ξ.jetConstU Y μ q :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg ((Ξ.X Y).pieceConst_nonneg _ μ q)
    ((Ξ.X Y).densityBound_nonneg _ μ)) measureReal_nonneg

/-- ★★★ **The chart-wise jet bound on the resolved coefficient functional**:
`|𝒯^U_{μ,q}[F]| ≤ jetConstU μ q · M` whenever the chart representatives `F ∘ φ_i⁻¹` have all
derivatives of order `≤ engineOrder μ` bounded by `M` on the closed chart boxes. -/
theorem abs_coeff_le_of_chartJetBound (μ : ℝ) (q : ℕ) {M : ℝ}
    (hJ : Ξ.ChartJetBound Y ((Ξ.X Y).engineOrder μ) M) :
    |Ξ.coeff Y μ q| ≤ Ξ.jetConstU Y μ q * M := by
  unfold coeff SmoothCoreDecomposition.coeff jetConstU
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  refine (Ξ.abs_familyCoeff_amp_le Y ((Ξ.X Y).en I) μ q ((Ξ.X Y).rectBound_ρfam ((Ξ.X Y).en I) μ)
    (Ξ.rectBound_obsfamU Y ((Ξ.X Y).en I) μ hJ)).trans (le_of_eq ?_)
  ring

end ResolvedData

end SmoothEngine

end Grammar
