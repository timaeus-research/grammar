/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartVarPosterior

/-!
# The residual face formula in chart data for variable-unit product charts (CCLXVII)

For a stratum `I` of a variable-unit product chart, the tied sum of a certified piece atlas at the
stratum's own pair is expressed **without the chosen atlas**, directly in the chart data
(`tiedSum_residual_of_data`): with `h_a`, `k_a` the normal exponents, `λ = min_a (h_a+1)/(2k_a)`,
`J` the minimal normal coordinates and `s = ∑_{a∉J}(h_a − 2k_a λ + 1)`,

`∑_{tied} coeff = 2^{|J|} ∑_{τ : residual signs} ∫_base β(z) · ε^{s} · Γ(λ)/(|J|−1)!
  ∏_{a∈J} 1/(2k_a) · ∫_{(0,1]^{r}} pieceAmp(z, τ·(ε faceProj w)) · q_var(z, τ·(ε faceProj w))^{−λ}
  · ∏_{a∉J} w_a^{h_a−2k_aλ} dw dz`,

where `q_var(z,n) = u(Ψ(z,n)) · tangentialMonomial(z)` is the variable phase **restricted to the
minimal face** (the minimal coordinates of `n` are zero, the residual ones are kept) — not frozen at
the normal origin. When the inner face integral is a function `R(z)` of the base point alone
(`tiedSum_residual_of_inner`), the tied sum is `2^{|J|} · 2^{r−|J|} · ε^{s} · faceLeadConst ·
∫_base β R`. This is the variable-unit analogue of the residual formula used in the `x²y⁴` example
(CCLI), so that examples only have to identify the face and evaluate its integral.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

/-- Reflected dilated face points lie in the closed ball of the dilation radius. -/
theorem reflect_smul_faceProj_mem_closedBall {r : ℕ} (h k : Fin r → ℕ) (l : ℝ) (σ : Fin r → Bool)
    {b : ℝ} (hb : 0 ≤ b) {u : Fin r → ℝ} (hu : u ∈ unitBox r) :
    reflect σ (b • faceProj h k l u) ∈ Metric.closedBall (0 : Fin r → ℝ) b := by
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hb).2 fun a => ?_
  simp only [Real.norm_eq_abs, reflect, Pi.smul_apply, smul_eq_mul, abs_mul, abs_sgn', one_mul,
    abs_of_nonneg hb]
  unfold faceProj
  split_ifs
  · simp [hb]
  · have hua := hu a (mem_univ a)
    rw [abs_of_pos hua.1]
    exact mul_le_of_le_one_right hb hua.2

namespace ProductMonomialChartVar

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar R i K) (I : Finset (Fin d)) (hne : I.Nonempty)

/-- The minimal normal coordinates of the stratum at its exponent. -/
noncomputable def minimalNormal : Finset (Fin (I.card - 1 + 1)) :=
  minimalCoords (normalExp I hne P.h) (normalHalfExp I hne P.e)
    (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e))

theorem card_minimalNormal (hK0 : ∀ x, 0 ≤ K x) (hI : I ⊆ P.e.support) :
    (P.minimalNormal I hne).card = P.pieceMult I hne := by
  unfold minimalNormal
  rw [← multCount_eq_card_minimalCoords, P.pieceMult_eq hK0 I hI hne]

section Atlas

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hI : I ⊆ P.e.support)

/-- **The residual face formula in chart data**: the tied sum of a certified piece atlas at the
stratum's own pair, in reduced orthant form, with the amplitude `pieceAmp` and the variable phase
restricted to the minimal face. -/
theorem tiedSum_residual_of_data {lam₀ : ℝ} {k₀ : ℕ} (hlam : P.pieceLam I hne = lam₀)
    (hk₀ : P.pieceMult I hne - 1 = k₀)
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff =
      2 ^ (P.minimalNormal I hne).card *
        ∑ τ : {a : Fin (I.card - 1 + 1) // a ∉ P.minimalNormal I hne} → Bool,
          ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
            (P.pieceDensity hε hεb hD I hI hne p).beta z *
              (ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
                    (normalHalfExp I hne P.e) a =
                      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)),
                  (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e)
                    (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) a + 1)) *
                (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e)
                    (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) 1 *
                  ∫ w in unitBox (I.card - 1 + 1),
                    R.pieceAmp i I hne P.h P.v (F := F) (p := p) z
                        (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                          (normalHalfExp I hne P.e)
                          (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) *
                      varPhase I hne P.u P.e z
                          (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                            (normalHalfExp I hne P.e)
                            (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) ^
                        (-(minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e))) *
                      residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e)
                        (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', rfl⟩ := hAt
  have hmin : minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) = lam₀ :=
    (P.pieceLam_eq hK0 I hI hne).trans hlam
  have hmult : multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
      (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) - 1 = k₀ := by
    rw [P.pieceMult_eq hK0 I hI hne]
    exact hk₀
  rw [R.varPieceAtlas_sum_tied_residual i D hε I hne _ hbase hβ rfl _ _ hk qv hqv hqv_pos A' hA'c
    hamp' hphase' hFm hF hK hK0 hmin hmult]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine (VarUnitCell.reflected_coeff_eq (R.varPieceCell i D hε I hne
    (P.pieceDensity hε hεb hD I hI hne p) hbase hβ (normalExp I hne P.h) (normalHalfExp I hne P.e)
    hk qv hqv hqv_pos A' hA'c) (extendFalse _ τ)).trans ?_
  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
  change (P.pieceDensity hε hεb hD I hI hne p).beta z *
    (ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
          (normalHalfExp I hne P.e) a =
            minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)),
        (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e)
          (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) a + 1)) *
      (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e)
          (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) 1 *
        ∫ w in unitBox (I.card - 1 + 1),
          A' z (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
              (normalHalfExp I hne P.e)
              (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) *
            qv z (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                (normalHalfExp I hne P.e)
                (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) ^
              (-(minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e))) *
            residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e)
              (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) = _
  congr 1
  congr 1
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun w hw => ?_
  have hmem := reflect_smul_faceProj_mem_closedBall (normalExp I hne P.h) (normalHalfExp I hne P.e)
    (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) (extendFalse _ τ) hε.le hw
  rw [hA' z hz _ hmem, hq' z hz _ hmem]
  rfl

/-- **The inner-stratum corollary**: when the face integral is a function `Rz` of the base point
alone (independent of the residual signs), the tied sum is
`2^{|J|} · #(residual sign classes) · ε^{s} · faceLeadConst · ∫_base β Rz`. -/
theorem tiedSum_residual_of_inner {lam₀ : ℝ} {k₀ : ℕ} (hlam : P.pieceLam I hne = lam₀)
    (hk₀ : P.pieceMult I hne - 1 = k₀)
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At)
    (Rz : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ)
    (hinner : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ τ : {a : Fin (I.card - 1 + 1) // a ∉ P.minimalNormal I hne} → Bool,
        ∫ w in unitBox (I.card - 1 + 1),
          R.pieceAmp i I hne P.h P.v (F := F) (p := p) z
              (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                (normalHalfExp I hne P.e)
                (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) *
            varPhase I hne P.u P.e z
                (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                  (normalHalfExp I hne P.e)
                  (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) ^
              (-(minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e))) *
            residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e)
              (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w = Rz z) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff =
      2 ^ (P.minimalNormal I hne).card *
        (Fintype.card ({a : Fin (I.card - 1 + 1) // a ∉ P.minimalNormal I hne} → Bool) : ℝ) *
        ((ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
              (normalHalfExp I hne P.e) a =
                minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)),
            (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e)
              (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) a + 1)) *
          faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e)
            (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) 1) *
          ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
            (P.pieceDensity hε hεb hD I hI hne p).beta z * Rz z) := by
  rw [P.tiedSum_residual_of_data I hne hK0 hε hεb hD hFm hF hK hI hlam hk₀ hAt]
  have hbaseM : MeasurableSet (P.pieceDensity hε hεb hD I hI hne p).base := by
    obtain ⟨-, -, -, -, -, -, hbase, -⟩ := hAt
    exact hbase.isClosed.measurableSet
  have hterm : ∀ τ : {a : Fin (I.card - 1 + 1) // a ∉ P.minimalNormal I hne} → Bool,
      ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
        (P.pieceDensity hε hεb hD I hI hne p).beta z *
          (ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
                (normalHalfExp I hne P.e) a =
                  minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)),
              (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e)
                (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) a + 1)) *
            (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e)
                (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) 1 *
              ∫ w in unitBox (I.card - 1 + 1),
                R.pieceAmp i I hne P.h P.v (F := F) (p := p) z
                    (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                      (normalHalfExp I hne P.e)
                      (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) *
                  varPhase I hne P.u P.e z
                      (reflect (extendFalse _ τ) (ε • faceProj (normalExp I hne P.h)
                        (normalHalfExp I hne P.e)
                        (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) ^
                    (-(minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e))) *
                  residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e)
                    (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) w)) =
      (ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
            (normalHalfExp I hne P.e) a =
              minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)),
          (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e)
            (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) a + 1)) *
        faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e)
          (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) 1) *
        ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
          (P.pieceDensity hε hεb hD I hI hne p).beta z * Rz z := fun τ => by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hbaseM fun z hz => ?_
    rw [hinner z hz τ]
    ring
  rw [Finset.sum_congr rfl fun τ _ => hterm τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Atlas

end ProductMonomialChartVar

end Grammar
