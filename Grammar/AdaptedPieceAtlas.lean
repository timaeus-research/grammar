/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SymmetricScalarUnitCells

/-!
# The bridge from an adapted piece in normal form to a scalar-unit atlas

Unit 3 of consult #76 (`tide-log/gpt6_bigpicture_v76.md`): the first CONCRETE constructor of the
hypotheses of the conditional global theorems. A chart–stratum piece whose static density is an
adapted product density (CCXXVIII) with a compact base, an integrable tangential weight and the
`ε`-ball as normal box, and whose pulled-back amplitude and phase are in **scalar normal form** on
the base and the ball —
`amp(z,n) · F(φ_i(z,n)) = A(z,n) ∏_j |n_j|^{h_j}` and `K(φ_i(z,n)) = q(z) ∏_j n_j^{2k_j}` with `A`
jointly continuous, `q` continuous and positive on the base, `k_j > 0` —
has its piece integral equal, for every `N ≥ 0`, to the symmetric integral of the scalar-unit cell
`(n = |I| − 1, h, k, b = ε, A, base, β, q)` (`pieceIntegral_eq_symIntegral`: the adapted iterated
form of CCXXVIII, the pointwise normal-form identities on the open ball, and the null boundary
between the open ball and the half-open box, `ball_eq_piBox_Ioo`, `piBox_Ioo_ae_eq_Ioc`), hence
admits the orthant atlas of that cell (`pieceAtlas`), with all cells at the pair
`(min_j (h_j+1)/(2k_j), #minimisers − 1)` (`pieceAtlas_cell_lam`). The base dimension of the atlas
is the piece's `d − |I|`; the conditional global theorem is restated with a per-piece base dimension
(`hasLeadingTerm_boltzmannIntegral_of_scalarAtlases'`).

Non-claims: the normal-form identities are HYPOTHESES on the piece (a constant chart unit times the
tangential monomial gives `q(z)`; an `n`-dependent unit is not covered); the fibre-constant
allocation, the compactness of the base and the integrability of the weight are inputs.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### The open ball and the half-open box -/

section Boxes

variable {r : ℕ} {ε : ℝ}

theorem ball_eq_piBox_Ioo (hε : 0 < ε) :
    Metric.ball (0 : Fin r → ℝ) ε = piBox r (Ioo (-ε) ε) := by
  ext n
  rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
  unfold piBox
  simp only [Set.mem_pi, mem_univ, true_implies, mem_Ioo, Real.norm_eq_abs, abs_lt]

/-- The open and the half-open boxes differ by a null set. -/
theorem piBox_Ioo_ae_eq_Ioc (ε : ℝ) :
    (piBox r (Ioo (-ε) ε) : Set (Fin r → ℝ)) =ᵐ[volume] piBox r (Ioc (-ε) ε) := by
  unfold piBox
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · rw [sdiff_eq_empty.2 (pi_mono fun _ _ => Ioo_subset_Ioc_self), measure_empty]
  · have hfin : (volume : Measure (Fin r → ℝ)) (Set.pi univ fun _ => Ioo (-ε) ε) ≠ ⊤ := by
      rw [Real.volume_pi_Ioo]
      exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne
    rw [measure_sdiff (pi_mono fun _ _ => Ioo_subset_Ioc_self)
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet hfin, Real.volume_pi_Ioc,
      Real.volume_pi_Ioo, tsub_self]

end Boxes

/-! ### The bridge -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q) (hq_pos : ∀ z ∈ Ad.base, 0 < q z)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))

/-- **The scalar-unit cell of an adapted piece in normal form.** -/
noncomputable def pieceCell : ScalarUnitCell (d - (I.card - 1 + 1)) where
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
  q := q
  q_cont := hq
  q_pos := hq_pos

variable (hamp : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
      A z n * ∏ j, |n j| ^ h j)
  (hphase : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) = q z * ∏ j, n j ^ (2 * k j))
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The piece integral is the symmetric integral of its cell** for every `N ≥ 0`. -/
theorem pieceIntegral_eq_symIntegral {N : ℝ} (hN : 0 ≤ N) :
    R.pieceIntegral D ε i I F K p N =
      (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).symIntegral N := by
  rw [R.pieceIntegral_eq_adapted i D I hne Ad hFm hF hK hK0 hN]
  unfold ScalarUnitCell.symIntegral
  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
  congr 1
  change _ = symScalarKernel (I.card - 1) h k ε q A z N
  unfold symScalarKernel
  rw [hbox]
  have hinner : ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * (Real.exp (-N * K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))) *
        F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) =
      ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A z n * (∏ j, |n j| ^ h j) * Real.exp (-(q z * N * ∏ j, n j ^ (2 * k j))) := by
    refine setIntegral_congr_fun measurableSet_ball fun n hn => ?_
    rw [hphase z hz n hn, ← hamp z hz n hn]
    ring_nf
  rw [hinner, ball_eq_piBox_Ioo hε]
  exact setIntegral_congr_set (piBox_Ioo_ae_eq_Ioc ε)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The orthant atlas of an adapted piece in scalar normal form.** -/
noncomputable def pieceAtlas :
    FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) where
  ι := Fin (I.card - 1 + 1) → Bool
  cell := (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).reflected
  eq := fun N hN => by
    rw [R.pieceIntegral_eq_symIntegral i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp
      hphase hFm hF hK hK0 hN]
    exact (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).symIntegral_eq_sum hN

include hbox hamp hphase hFm hF hK hK0 in
/-- Every cell of the piece atlas sits at the pair `(min_j (h_j+1)/(2k_j), #minimisers − 1)`. -/
theorem pieceAtlas_cell_lam (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF hK
      hK0).cell σ).lam = minRatio h k := rfl

include hbox hamp hphase hFm hF hK hK0 in
theorem pieceAtlas_cell_mult (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF hK
      hK0).cell σ).mult = multCount (ratioExp h k) (minRatio h k) := rfl

end ResolutionCover

/-! ### The conditional global theorem with per-piece base dimensions -/

namespace ResolutionCover

open Monomialize.Analytic Monomialize.VolumeScaling

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The coefficient of the chart–stratum pair `(i, I)` from its atlas (per-piece base dimension). -/
noncomputable def scalarAtlasPieceCoeff' {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    {tdim : ι → Finset (Fin d) → ℕ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ (e i).support ∧ I.Nonempty then
    ∑ j ∈ (At i I hI.1 hI.2).tied lam₀ k₀, ((At i I hI.1 hI.2).cell j).coeff
  else 0

/-- **The conditional global leading coefficient with scalar-unit atlases of per-piece base
dimension.** -/
theorem hasLeadingTerm_boltzmannIntegral_of_scalarAtlases' (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (tdim : ι → Finset (Fin d) → ℕ)
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι),
      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' At lam₀ k₀ i I) lam₀ k₀ := by
  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
    (scalarAtlasPieceCoeff' At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
    (fun i I hI => by
      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
      unfold scalarAtlasPieceCoeff'
      rw [dif_pos ⟨hsub, hne⟩]
      exact (At i I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam i I hsub hne)
        (hk i I hsub hne))
    (fun _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
  have hcoef : ∀ i : ι, (∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
      (fun _ => lam₀ = lam₀ ∧ k₀ = k₀), scalarAtlasPieceCoeff' At lam₀ k₀ i I) =
      ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' At lam₀ k₀ i I :=
    fun i => by rw [Finset.filter_true_of_mem fun _ _ => ⟨rfl, rfl⟩]
  beta_reduce at hmain
  rw [Finset.sum_congr rfl fun i _ => hcoef i] at hmain
  exact hmain

end ResolutionCover

end Grammar
