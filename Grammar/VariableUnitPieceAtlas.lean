/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LeadingAtlas
import Grammar.SingleChartScalarAtlas

/-!
# Variable-unit piece atlases (CCLIX)

The chart–stratum piece bridge **without the normal-independence hypothesis** on the phase unit.

* **The variable normal form of the phase**: where `K = u · y^e` on a monomial chart,
  `K(Ψ(z,n)) = q_var(z,n) ∏_a n_a^{2k_a}` with `q_var(z,n) = u(Ψ(z,n)) · tangentialMonomial(z)`
  (`varPhase`, `phase_varNormalForm`) — no `hind`. The variable phase is nonzero where the unit and
  the active tangential coordinates are (`varPhase_ne_zero`), positive at a normal point with all
  coordinates nonzero by `K ≥ 0` (`varPhase_pos_of_ne`), and positive on the whole closed normal
  ball by the intermediate value theorem along the connected ball (`varPhase_pos_closedBall`):
  the unit does not vanish along the ball, so it keeps the sign it has at `(ε/2, …, ε/2)`.
* **The variable-unit cell of a piece** `varPieceCell` (an adapted density in variable normal
  form), the identity `pieceIntegral_eq_varSymIntegral`, the orthant atlas `varPieceAtlas :
  FiniteVarUnitAtlas`, and the compatibility `varPieceCell_const_eq_toVar` (a constant unit gives
  the scalar piece cell, as a variable-unit cell).
* **From chart data** (`exists_varPieceAtlas_of_chart_data`): the atlas of a chart–stratum piece
  from monomial-chart data with the unit only continuous and nonvanishing — the variable phase and
  the amplitude are Tietze-extended from the compact base × closed ball; the atlas is the orthant
  atlas of the piece cell with exposed data (`qv = varPhase` and `A' = pieceAmp` on base × closed
  ball), all cells at `(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)`.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

/-! ### The variable normal form of the phase -/

section VarPhase

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty) (u : (Fin d → ℝ) → ℝ) (e : Fin d →₀ ℕ)

/-- **The variable phase** `q_var(z,n) = u(Ψ(z,n)) · tangentialMonomial(z)`. -/
noncomputable def varPhase (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ) :
    ℝ :=
  u (planeSplit (stratumSplit I hne) (z, n)) * tangentialMonomial I hne e z

/-- The scalar phase is the variable phase at the normal origin. -/
theorem varPhase_zero (z : Fin (d - (I.card - 1 + 1)) → ℝ) :
    varPhase I hne u e z 0 = scalarPhase I hne u e z := rfl

variable {K : (Fin d → ℝ) → ℝ} {z : Fin (d - (I.card - 1 + 1)) → ℝ}

/-- **The variable normal form of the phase**: where `K = u · y^e`,
`K(Ψ(z,n)) = q_var(z,n) ∏_a n_a^{2k_a}` — no independence hypothesis on the unit. -/
theorem phase_varNormalForm {n : Fin (I.card - 1 + 1) → ℝ}
    (hK : K (planeSplit (stratumSplit I hne) (z, n)) =
      u (planeSplit (stratumSplit I hne) (z, n)) *
        monomialEval (planeSplit (stratumSplit I hne) (z, n)) e)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a) :
    K (planeSplit (stratumSplit I hne) (z, n)) =
      varPhase I hne u e z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := by
  rw [hK, monomialEval_planeSplit]
  unfold varPhase
  simp only [hpar]
  ring

/-- The variable phase is nonzero where the unit and the active tangential coordinates are. -/
theorem varPhase_ne_zero {n : Fin (I.card - 1 + 1) → ℝ}
    (hu0 : u (planeSplit (stratumSplit I hne) (z, n)) ≠ 0)
    (hz : ∀ j ∈ e.support, j ∉ I → planeSplit (stratumSplit I hne) (z, 0) j ≠ 0) :
    varPhase I hne u e z n ≠ 0 := by
  unfold varPhase
  refine mul_ne_zero hu0 ?_
  unfold tangentialMonomial
  exact Finset.prod_ne_zero_iff.2 fun j hj =>
    pow_ne_zero _ (hz j (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2)

/-- **Positivity at a normal point with all coordinates nonzero**, from `K ≥ 0`. -/
theorem varPhase_pos_of_ne {n : Fin (I.card - 1 + 1) → ℝ}
    (hK : K (planeSplit (stratumSplit I hne) (z, n)) =
      u (planeSplit (stratumSplit I hne) (z, n)) *
        monomialEval (planeSplit (stratumSplit I hne) (z, n)) e)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a)
    (hK0 : 0 ≤ K (planeSplit (stratumSplit I hne) (z, n))) (hn : ∀ a, n a ≠ 0)
    (hu0 : u (planeSplit (stratumSplit I hne) (z, n)) ≠ 0)
    (hz : ∀ j ∈ e.support, j ∉ I → planeSplit (stratumSplit I hne) (z, 0) j ≠ 0) :
    0 < varPhase I hne u e z n := by
  have hq0 := varPhase_ne_zero I hne u e hu0 hz
  have hP : 0 < ∏ a, n a ^ (2 * normalHalfExp I hne e a) :=
    Finset.prod_pos fun a _ => (even_two_mul _).pow_pos (hn a)
  rw [phase_varNormalForm I hne u e hK hpar] at hK0
  rcases lt_or_gt_of_ne hq0 with hlt | hgt
  · exfalso
    have := mul_neg_of_neg_of_pos hlt hP
    linarith
  · exact hgt

/-- **Positivity on the closed normal ball** by the intermediate value theorem: the unit does not
vanish along the connected closed ball, so it has the sign it has at the interior point
`(ε/2, …, ε/2)`, where `K ≥ 0` forces the variable phase to be positive. -/
theorem varPhase_pos_closedBall {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K (planeSplit (stratumSplit I hne) (z, n)) =
        u (planeSplit (stratumSplit I hne) (z, n)) *
          monomialEval (planeSplit (stratumSplit I hne) (z, n)) e)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a)
    (hK0 : ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      0 ≤ K (planeSplit (stratumSplit I hne) (z, n)))
    (hu0 : ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      u (planeSplit (stratumSplit I hne) (z, n)) ≠ 0)
    (hucont : ContinuousOn (fun n : Fin (I.card - 1 + 1) → ℝ => u (planeSplit (stratumSplit I hne)
      (z, n))) (Metric.closedBall 0 ε))
    (hz : ∀ j ∈ e.support, j ∉ I → planeSplit (stratumSplit I hne) (z, 0) j ≠ 0)
    {n : Fin (I.card - 1 + 1) → ℝ} (hn : n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    0 < varPhase I hne u e z n := by
  have hstar_ball : (fun _ : Fin (I.card - 1 + 1) => ε / 2) ∈
      Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hstar_cb := Metric.ball_subset_closedBall hstar_ball
  have hstar_pos : 0 < varPhase I hne u e z (fun _ => ε / 2) :=
    varPhase_pos_of_ne I hne u e (hK _ hstar_ball) hpar (hK0 _ hstar_ball)
      (fun _ => (half_pos hε).ne') (hu0 _ hstar_cb) hz
  have hconn : IsPreconnected (Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε) :=
    (convex_closedBall _ _).isPreconnected
  have hsame : 0 < u (planeSplit (stratumSplit I hne) (z, n)) *
      u (planeSplit (stratumSplit I hne) (z, fun _ => ε / 2)) := by
    rcases lt_or_gt_of_ne (hu0 n hn) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hu0 _ hstar_cb) with h2 | h2
    · exact mul_pos_of_neg_of_neg h1 h2
    · exfalso
      obtain ⟨n'', hn'', h0⟩ := hconn.intermediate_value hn hstar_cb hucont ⟨h1.le, h2.le⟩
      exact hu0 n'' hn'' h0
    · exfalso
      obtain ⟨n'', hn'', h0⟩ := hconn.intermediate_value hstar_cb hn hucont ⟨h2.le, h1.le⟩
      exact hu0 n'' hn'' h0
    · exact mul_pos h1 h2
  have htm : tangentialMonomial I hne e z ≠ 0 := by
    unfold tangentialMonomial
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      pow_ne_zero _ (hz j (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2)
  have hprod : 0 < varPhase I hne u e z n * varPhase I hne u e z (fun _ => ε / 2) := by
    unfold varPhase
    have hsq : 0 < tangentialMonomial I hne e z ^ 2 := by positivity
    calc (0 : ℝ) < (u (planeSplit (stratumSplit I hne) (z, n)) *
          u (planeSplit (stratumSplit I hne) (z, fun _ => ε / 2))) *
          tangentialMonomial I hne e z ^ 2 := mul_pos hsame hsq
      _ = _ := by ring
  rcases mul_pos_iff.1 hprod with h | h
  · exact h.1
  · exact absurd hstar_pos (not_lt.2 h.2.le)

end VarPhase

/-! ### The variable-unit cell of a piece -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hqv : Continuous (Function.uncurry qv))
  (hqv_pos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))

/-- **The variable-unit cell of an adapted piece in variable normal form.** -/
noncomputable def varPieceCell : VarUnitCell (d - (I.card - 1 + 1)) where
  n := I.card - 1
  h := h
  k := k
  k_pos := hk
  b := ε
  b_pos := hε
  A := A
  A_cont := hA
  base := Ad.base
  base_compact := hbase
  βw := Ad.beta
  βw_int := hβ
  u := qv
  u_cont := hqv
  u_pos := hqv_pos

omit hqv hqv_pos in
/-- A constant unit gives the scalar piece cell, viewed as a variable-unit cell. -/
theorem varPieceCell_const_eq_toVar (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q)
    (hq_pos : ∀ z ∈ Ad.base, 0 < q z) :
    R.varPieceCell i D hε I hne Ad hbase hβ h k hk (fun z _ => q z) (hq.comp continuous_fst)
        (fun z hz _ _ => hq_pos z hz) A hA =
      (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).toVar := rfl

variable (hamp : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
      A z n * ∏ j, |n j| ^ h j)
  (hphase : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) = qv z n * ∏ j, n j ^ (2 * k j))
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The piece integral is the symmetric integral of its variable-unit cell** for every `N ≥ 0`. -/
theorem pieceIntegral_eq_varSymIntegral {N : ℝ} (hN : 0 ≤ N) :
    R.pieceIntegral D ε i I F K p N =
      (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).symIntegral N := by
  rw [R.pieceIntegral_eq_adapted i D I hne Ad hFm hF hK hK0 hN]
  unfold VarUnitCell.symIntegral
  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
  congr 1
  change _ = symVarKernel (I.card - 1) h k ε qv A z N
  unfold symVarKernel
  rw [hbox]
  have hinner : ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * (Real.exp (-N * K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))) *
        F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) =
      ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A z n * (∏ j, |n j| ^ h j) * Real.exp (-(qv z n * N * ∏ j, n j ^ (2 * k j))) := by
    refine setIntegral_congr_fun measurableSet_ball fun n hn => ?_
    rw [hphase z hz n hn, ← hamp z hz n hn]
    ring_nf
  rw [hinner, ball_eq_piBox_Ioo hε]
  exact setIntegral_congr_set (piBox_Ioo_ae_eq_Ioc ε)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The orthant atlas of an adapted piece in variable normal form.** -/
noncomputable def varPieceAtlas :
    FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) where
  ι := Fin (I.card - 1 + 1) → Bool
  cell := (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).reflected
  eq := fun N hN => by
    rw [R.pieceIntegral_eq_varSymIntegral i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos A hA
      hamp hphase hFm hF hK hK0 hN]
    exact (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).symIntegral_eq_sum hN

include hbox hamp hphase hFm hF hK hK0 in
/-- Every cell of the variable piece atlas sits at `(min_j (h_j+1)/(2k_j), #minimisers − 1)`. -/
theorem varPieceAtlas_cell_lam (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.varPieceAtlas i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos A hA hamp hphase hFm hF
      hK hK0).cell σ).lam = minRatio h k := rfl

include hbox hamp hphase hFm hF hK hK0 in
theorem varPieceAtlas_cell_mult (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.varPieceAtlas i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos A hA hamp hphase hFm hF
      hK hK0).cell σ).mult = multCount (ratioExp h k) (minRatio h k) := rfl

end ResolutionCover

/-! ### The variable-unit atlas from chart data -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  (e h : Fin d →₀ ℕ) (hD : D i = e.support) (hI : I ⊆ e.support)
  {K : (Fin d → ℝ) → ℝ} (hK0 : ∀ x, 0 ≤ K x) {W : Set (Fin d → ℝ)} (hW : IsOpen W)
  (hsub : (R.chart i).dom ⊆ W) (u v : (Fin d → ℝ) → ℝ) (hu : ContinuousOn u W)
  (hu0 : ∀ y ∈ W, u y ≠ 0) (hKu : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e)
  (hv : ContinuousOn v W)
  (hdet : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h)
  (T' : Set (Fin d → ℝ)) (hT' : IsClosed T') (ρT : (Fin d → ℝ) → ℝ) (hρm : Measurable ρT)
  {Cρ : ℝ} (hρb : ∀ x, |ρT x| ≤ Cρ)
  (hdom : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
  (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y))
  {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) W)
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) W)
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hy₀ : ∃ y₀ ∈ W, ∀ j ∈ I, y₀ j = 0)

include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hT' hρm hρb hdom hρ hFc hpc hFm hF hK hy₀ in
/-- **The variable-unit atlas of a chart–stratum piece from monomial-chart data, with its cells
exposed** — no independence hypothesis on the unit: the atlas is the orthant atlas of the
variable-unit cell built on the compact-base piece density `chartPieceDensity`, with a continuous
positive unit `qv` equal to the variable phase `u(Ψ(z,n)) · tangentialMonomial(z)` on base × closed
ball and a continuous amplitude `A'` equal to `pieceAmp` there; all cells at the pair
`(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`. -/
theorem exists_varPieceAtlas_of_chart_data :
    ∃ At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
      (∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
        (minRatio (normalExp I hne h) (normalHalfExp I hne e))) ∧
      ∃ (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
        (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
        (hqv : Continuous (Function.uncurry qv))
        (hqv_pos : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
        (hA'c : Continuous (Function.uncurry A'))
        (hk : ∀ a, 0 < normalHalfExp I hne e a)
        (hbase : IsCompact (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hβ : IntegrableOn (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).beta
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hamp' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).amp z n *
              F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
              A' z n * ∏ a, |n a| ^ normalExp I hne h a)
        (hphase' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
              qv z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a)),
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            qv z n = varPhase I hne u e z n) ∧
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            A' z n = R.pieceAmp i I hne h v (F := F) (p := p) z n) ∧
        At = R.varPieceAtlas i D hε I hne
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ) hbase hβ rfl
          (normalExp I hne h) (normalHalfExp I hne e) hk qv hqv hqv_pos A' hA'c hamp' hphase' hFm
          hF hK hK0 := by
  -- the adapted density with compact base
  set Ad := R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ with hAd
  have hbase : IsCompact Ad.base :=
    R.chartPieceDensity_base_compact i D hε I hne e hD hI K p T' hT' ρT hdom hρ
  have hmemdom : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := fun z hz n hn =>
    R.mem_dom_of_mem_base i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn
  have hmemdomc : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := fun z hz n hn =>
    R.mem_dom_of_mem_base_closedBall i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn
  -- the base weight is integrable
  have hβ : IntegrableOn Ad.beta Ad.base := by
    have hβeq : Ad.beta = fun z => T'.indicator ρT (planeSplit (stratumSplit I hne) (z, 0)) := rfl
    rw [hβeq]
    refine Measure.integrableOn_of_bounded hbase.measure_lt_top.ne ?_ (M := Cρ) ?_
    · exact ((hρm.indicator hT'.measurableSet).comp
        ((planeSplit (stratumSplit I hne)).continuous.comp
          (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs]
      by_cases hx : planeSplit (stratumSplit I hne) (z, 0) ∈ T'
      · rw [indicator_of_mem hx]
        exact hρb _
      · rw [indicator_of_notMem hx, abs_zero]
        exact (abs_nonneg _).trans (hρb 0)
  -- parity of the normal exponents
  obtain ⟨y₀, hy₀W, hy₀I⟩ := hy₀
  have hK0' : ∀ y ∈ W, 0 ≤ K ((R.chart i).φ y) := fun y _ => hK0 _
  have hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a := fun a =>
    normalExp_eq_two_mul_halfExp I hne e hW (K := fun y => K ((R.chart i).φ y)) hKu hK0' hy₀W
      (hu.continuousAt (hW.mem_nhds hy₀W)) (hu0 y₀ hy₀W) hy₀I a
  have he : ∀ j ∈ I, 0 < e j := fun j hj =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (hI hj))
  have hk : ∀ a, 0 < normalHalfExp I hne e a := normalHalfExp_pos I hne e he hpar
  -- the variable phase on the base × ball
  have hphase0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        varPhase I hne u e z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [(R.chart i).Φ_eqOn (hmemdom z hz n hn)]
    exact phase_varNormalForm I hne u e (K := fun y => K ((R.chart i).φ y))
      (hKu _ (hsub (hmemdom z hz n hn))) hpar
  have hfootOf : ∀ z ∈ Ad.base,
      planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I := fun z hz => by
    rw [hAd, chartPieceDensity_base] at hz
    exact hz.1.1
  have hΨz : ∀ z : Fin (d - (I.card - 1 + 1)) → ℝ, Continuous fun n : Fin (I.card - 1 + 1) → ℝ =>
      planeSplit (stratumSplit I hne) (z, n) := fun z =>
    (planeSplit (stratumSplit I hne)).continuous.comp (continuous_const.prodMk continuous_id)
  have hqpos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      0 < varPhase I hne u e z n := fun z hz n hn => by
    refine varPhase_pos_closedBall I hne u e (K := fun y => K ((R.chart i).φ y)) hε
      (fun n hn => hKu _ (hsub (hmemdom z hz n hn))) hpar (fun n _ => hK0 _)
      (fun n hn => hu0 _ (hsub (hmemdomc z hz n hn)))
      (hu.comp (hΨz z).continuousOn fun n hn => hsub (hmemdomc z hz n hn)) ?_ hn
    intro j hj hjI h0
    have := hfootOf z hz j (by rw [hD]; exact hj) hjI
    apply this
    rw [h0, abs_zero]
    exact hε
  -- continuous representatives on the compact base × closed ball
  have hΨ : Continuous fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q := (planeSplit (stratumSplit I hne)).continuous
  have hmaps : MapsTo (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q) (Ad.base ×ˢ Metric.closedBall 0 ε) W :=
    fun q hq => hsub (hmemdomc q.1 hq.1 q.2 hq.2)
  have hqcont : ContinuousOn (Function.uncurry (varPhase I hne u e))
      (Ad.base ×ˢ Metric.closedBall 0 ε) :=
    (hu.comp hΨ.continuousOn hmaps).mul
      ((continuous_tangentialMonomial I hne e).comp continuous_fst).continuousOn
  obtain ⟨qv'', hqv''c, hqv''eq⟩ := exists_continuous_extension_of_isClosed
    (hbase.isClosed.prod Metric.isClosed_closedBall) hqcont
  have hqv : Continuous (Function.uncurry (Function.curry qv'')) := by
    rwa [Function.uncurry_curry]
  have hqv_pos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      0 < Function.curry qv'' z n := fun z hz n hn => by
    change 0 < qv'' (z, n)
    rw [hqv''eq (z, n) ⟨hz, hn⟩]
    exact hqpos z hz n hn
  have hphase' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        Function.curry qv'' z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [hphase0 z hz n hn]
    congr 1
    exact (hqv''eq (z, n) ⟨hz, Metric.ball_subset_closedBall hn⟩).symm
  -- the amplitude identity on the base and the open ball
  have hamp0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
        R.pieceAmp i I hne h v (F := F) (p := p) z n * ∏ a, |n a| ^ normalExp I hne h a :=
    fun z hz n hn => by
      have hdomzn := hmemdom z hz n hn
      have hampeq : Ad.amp z n = (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
          p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) := rfl
      rw [hampeq, (R.chart i).Φ_eqOn hdomzn]
      unfold ResolutionChart.jac pieceAmp
      rw [hdet _ (hsub hdomzn), abs_mul, abs_monomialEval_planeSplit]
      ring
  have hAcont : ContinuousOn (Function.uncurry (R.pieceAmp i I hne h v (F := F) (p := p)))
      (Ad.base ×ˢ Metric.closedBall 0 ε) := by
    have h1 := (hv.comp hΨ.continuousOn hmaps).abs
    have h2 : ContinuousOn (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)
        => |tangentialMonomial I hne h q.1|) (Ad.base ×ˢ Metric.closedBall 0 ε) :=
      ((continuous_tangentialMonomial I hne h).comp continuous_fst).continuousOn.abs
    have h3 := hpc.comp hΨ.continuousOn hmaps
    have h4 := hFc.comp hΨ.continuousOn hmaps
    exact ((h1.mul h2).mul h3).mul h4
  obtain ⟨A'', hA''c, hA''eq⟩ := exists_continuous_extension_of_isClosed
    (hbase.isClosed.prod Metric.isClosed_closedBall) hAcont
  have hA'c : Continuous (Function.uncurry (Function.curry A'')) := by
    rwa [Function.uncurry_curry]
  have hamp' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
        Function.curry A'' z n * ∏ a, |n a| ^ normalExp I hne h a := fun z hz n hn => by
    rw [hamp0 z hz n hn]
    congr 1
    exact (hA''eq (z, n) ⟨hz, Metric.ball_subset_closedBall hn⟩).symm
  exact ⟨R.varPieceAtlas i D hε I hne Ad hbase hβ rfl (normalExp I hne h) (normalHalfExp I hne e)
    hk (Function.curry qv'') hqv hqv_pos (Function.curry A'') hA'c hamp' hphase' hFm hF hK hK0,
    fun _ => rfl, fun _ => rfl, Function.curry qv'', Function.curry A'', hqv, hqv_pos, hA'c, hk,
    hbase, hβ, hamp', hphase', fun z hz n hn => hqv''eq (z, n) ⟨hz, hn⟩,
    fun z hz n hn => hA''eq (z, n) ⟨hz, hn⟩, rfl⟩

include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hT' hρm hρb hdom hρ hFc hpc hFm hF hK hy₀ in
/-- **The variable-unit atlas of a chart–stratum piece from monomial-chart data** (no independence
hypothesis on the unit): all cells at `(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)`. -/
theorem exists_varPieceAtlas_of_chart :
    ∃ At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
      ∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
        (minRatio (normalExp I hne h) (normalHalfExp I hne e)) := by
  obtain ⟨At, h1, h2, -⟩ := R.exists_varPieceAtlas_of_chart_data i D hε I hne e h hD hI hK0 hW hsub
    u v hu hu0 hKu hv hdet T' hT' ρT hρm hρb hdom hρ hFc hpc hFm hF hK hy₀
  exact ⟨At, h1, h2⟩

end ResolutionCover

end Grammar
