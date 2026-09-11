/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GlobalExponentBound
import Monomialize.VolumeScaling.PartialResolution
import Monomialize.Analytic.BM89.QInduction
import Monomialize.Analytic.BM89.Readout

/-!
# The exponent of a monomial resolution: the finite local cover from the chart domains

The conditional theorem of `GlobalExponentBound` is discharged for a hironaka **partial
resolution** whose charts are monomial: the finite local cover exists. The point is that the region
of the divisor-point theorem contains
the chart image of an **open source neighbourhood** of the divisor point
(`exists_isOpen_subset_localRegion`), the chart domains are compact, and the charts cover the
resolved compact set up to a null set (`PartialResolution.cover`). Covering each compact
`dom_i ∩ φ_i⁻¹(B̄(w,r))` by finitely many such neighbourhoods (divisor points) and by neighbourhoods
on which the phase stays positive (other points) gives finitely many local regions and a phase gap
`δ₀` off their union, almost everywhere on the region.

**Theorem** (`exponent_of_monomialResolution`): for `K ≥ 0` analytic on an open `U ∋ w`, `K w = 0`,
`F > 0` analytic on `U`, and a partial resolution `R` of `K` on a compact neighbourhood `N` of `w`
whose charts are monomial, there is a compact neighbourhood `Ω ⊆ U` of `w`
and finitely many divisor-point chart pairs `(λ_p, m_p) = (C_p.lam, C_p.mult)` such that
`∫_Ω F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})` with `λ_* = min_p λ_p`, `m_* = max{m_p : λ_p = λ_*}`:
**the exponent pair is the minimum over the divisor points of the charts of the minimal Mellin
ratio of the normal exponents**, `(h_{n_j}+1)/(2k_j)`.

With hironaka's `Q_all` this is unconditional (`exponent_of_analytic`): no support condition on the
Jacobian exponents is needed, the tangential Jacobian weights being carried by the centred chart
data. Non-claims: leading order only; the coefficient is not identified; the finite family of pairs
depends on the chosen finite subcover (its minimum does not, by the theorem itself, but this is not
stated); the exponent is that of a compact neighbourhood, not identified with a germ invariant.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

variable {d : ℕ}

/-- **The exponent of a monomial resolution.** -/
theorem exponent_of_monomialResolution {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    {w : Fin d → ℝ} (hw : w ∈ U) (hKw : K w = 0) {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x) {N : Set (Fin d → ℝ)} (hN : N ∈ 𝓝 w)
    (R : PartialResolution d K N) (hR : R.IsMonomial) :
    ∃ Rg : Set (Fin d → ℝ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ U ∧
      ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
        (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
        (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
        regionIntegral volume Rg F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  classical
  have hR' : ∀ i, ∃ (e h : Fin d →₀ ℕ) (W : Set (Fin d → ℝ)),
      IsMonomialChart K (R.φ i) (R.dom i) e h W := hR
  choose e h W hc using hR'
  -- a closed ball around `w` inside `U`
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hw)
  set r' := r / 2 with hr'
  have hr'pos : 0 < r' := half_pos hr
  have hcball : Metric.closedBall w r' ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  -- the compact chart pieces over the ball
  set D : R.ι → Set (Fin d → ℝ) := fun i => R.dom i ∩ (R.φ i) ⁻¹' Metric.closedBall w r' with hD
  have hDc : ∀ i, IsCompact (D i) := fun i => by
    refine (R.dom_compact i).of_isClosed_subset ?_ inter_subset_left
    exact ((hc i).analyticOnNhd.continuousOn.mono (hc i).subset).preimage_isClosed_of_isClosed
      (R.dom_compact i).isClosed Metric.isClosed_closedBall
  have hDW : ∀ i, D i ⊆ W i := fun i => inter_subset_left.trans (hc i).subset
  have hDU : ∀ i, ∀ y ∈ D i, R.φ i y ∈ U := fun i y hy => hcball hy.2
  -- neighbourhoods at divisor points (data from the divisor-point theorem)
  have hdiv : ∀ (i : R.ι) (y₀ : Fin d → ℝ), ∃ (V Ω : Set (Fin d → ℝ)) (lam : ℝ) (m : ℕ) (c : ℝ),
      y₀ ∈ D i → K (R.φ i y₀) = 0 →
        IsOpen V ∧ y₀ ∈ V ∧ IsCompact Ω ∧ Ω ⊆ U ∧ (∀ y ∈ V, R.φ i y ∈ Ω) ∧
          (∃ C : CentredChartData K (R.φ i) (h i) y₀, lam = C.lam ∧ m = C.mult) ∧ 0 < c ∧
          (fun N : ℝ => ∫ x in Ω, F x * Real.exp (-N * K x)) ~[atTop]
            fun N => c * powLogScale lam (m - 1) N := by
    intro i y₀
    by_cases hy : y₀ ∈ D i ∧ K (R.φ i y₀) = 0
    · obtain ⟨C, Ω, hΩc, -, -, hΩU, ⟨V, hVo, hy₀V, hVΩ⟩, c, hc0, hequiv⟩ :=
        IsMonomialChart.local_leading_term (hc i) hU hK hK0 hKm (hDW i hy.1)
          (hDU i y₀ hy.1) hy.2 hF (hFpos _ (hDU i y₀ hy.1))
      exact ⟨V, Ω, C.lam, C.mult, c, fun _ _ => ⟨hVo, hy₀V, hΩc, hΩU, hVΩ, ⟨C, rfl, rfl⟩, hc0,
        hequiv⟩⟩
    · exact ⟨∅, ∅, 0, 0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hy⟩
  choose Vd Ωd lamd md cd hd using hdiv
  -- neighbourhoods at the other points (the phase stays positive)
  have hpos : ∀ (i : R.ι) (y₀ : Fin d → ℝ), ∃ V : Set (Fin d → ℝ),
      y₀ ∈ D i → K (R.φ i y₀) ≠ 0 →
        IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, K (R.φ i y₀) / 2 ≤ K (R.φ i y) := by
    intro i y₀
    by_cases hy : y₀ ∈ D i ∧ K (R.φ i y₀) ≠ 0
    · have hKpos : 0 < K (R.φ i y₀) := lt_of_le_of_ne (hK0 _ (hDU i y₀ hy.1)) (Ne.symm hy.2)
      have hcont : ContinuousAt (fun y => K (R.φ i y)) y₀ := by
        have h1 : ContinuousAt (R.φ i) y₀ :=
          ((hc i).analyticOnNhd _ (hDW i hy.1)).continuousAt
        have h2 : ContinuousAt K (R.φ i y₀) := (hK _ (hDU i y₀ hy.1)).continuousAt
        exact h2.comp h1
      have hev : ∀ᶠ y in 𝓝 y₀, K (R.φ i y₀) / 2 < K (R.φ i y) :=
        hcont.eventually (lt_mem_nhds (by linarith))
      obtain ⟨V, hV, hVo, hy₀V⟩ := eventually_nhds_iff.1 hev
      exact ⟨V, fun _ _ => ⟨hVo, hy₀V, fun y hy => (hV y hy).le⟩⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hy⟩
  choose Vp hp using hpos
  -- the neighbourhood assignment and the finite subcovers
  set Un : R.ι → (Fin d → ℝ) → Set (Fin d → ℝ) := fun i y₀ =>
    if K (R.φ i y₀) = 0 then Vd i y₀ else Vp i y₀ with hUn
  have hUn_nhds : ∀ i, ∀ y₀ ∈ D i, Un i y₀ ∈ 𝓝 y₀ := by
    intro i y₀ hy₀
    simp only [hUn]
    split_ifs with hK0'
    · exact (hd i y₀ hy₀ hK0').1.mem_nhds (hd i y₀ hy₀ hK0').2.1
    · exact (hp i y₀ hy₀ hK0').1.mem_nhds (hp i y₀ hy₀ hK0').2.1
  have hsub : ∀ i, ∃ t : Finset (Fin d → ℝ), (∀ y ∈ t, y ∈ D i) ∧ D i ⊆ ⋃ y ∈ t, Un i y :=
    fun i => (hDc i).elim_nhds_subcover (Un i) (hUn_nhds i)
  choose t htD htcover using hsub
  -- the divisor-type and positive-type centres
  set Zc : R.ι → Finset (Fin d → ℝ) := fun i => (t i).filter fun z => K (R.φ i z) = 0 with hZc
  set Pc : R.ι → Finset (Fin d → ℝ) := fun i => (t i).filter fun z => K (R.φ i z) ≠ 0 with hPc
  -- the index type of the local regions
  let ι : Type := Σ i : R.ι, ↥(Zc i)
  let Ω : ι → Set (Fin d → ℝ) := fun p => Ωd p.1 p.2.1
  let lam : ι → ℝ := fun p => lamd p.1 p.2.1
  let m : ι → ℕ := fun p => md p.1 p.2.1
  let c : ι → ℝ := fun p => cd p.1 p.2.1
  have hpZ : ∀ p : ι, p.2.1 ∈ D p.1 ∧ K (R.φ p.1 p.2.1) = 0 := fun p => by
    have := Finset.mem_filter.1 p.2.2
    exact ⟨htD p.1 _ this.1, this.2⟩
  have hdp : ∀ p : ι, IsOpen (Vd p.1 p.2.1) ∧ p.2.1 ∈ Vd p.1 p.2.1 ∧ IsCompact (Ω p) ∧ Ω p ⊆ U ∧
      (∀ y ∈ Vd p.1 p.2.1, R.φ p.1 y ∈ Ω p) ∧
      (∃ C : CentredChartData K (R.φ p.1) (h p.1) p.2.1, lam p = C.lam ∧ m p = C.mult) ∧
      0 < c p ∧ (fun N : ℝ => ∫ x in Ω p, F x * Real.exp (-N * K x)) ~[atTop]
        fun N => c p * powLogScale (lam p) (m p - 1) N :=
    fun p => hd p.1 p.2.1 (hpZ p).1 (hpZ p).2
  -- the phase gap off the divisor-type neighbourhoods
  set Spos : Finset (Σ i : R.ι, Fin d → ℝ) := Finset.univ.sigma Pc with hSpos
  set g : (Σ i : R.ι, Fin d → ℝ) → ℝ := fun q => K (R.φ q.1 q.2) / 2 with hg
  have hgpos : ∀ q ∈ Spos, 0 < g q := by
    intro q hq
    have hq' := Finset.mem_filter.1 (Finset.mem_sigma.1 hq).2
    have hqD : q.2 ∈ D q.1 := htD q.1 _ hq'.1
    exact half_pos (lt_of_le_of_ne (hK0 _ (hDU q.1 q.2 hqD)) (Ne.symm hq'.2))
  set δ₀ : ℝ := if hne : Spos.Nonempty then (Spos.image g).min' (hne.image g) else 1 with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    simp only [hδ₀]
    split_ifs with hne
    · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 (Finset.min'_mem (Spos.image g) (hne.image g))
      rw [← hqe]
      exact hgpos q hq
    · exact one_pos
  have hδ₀le : ∀ q ∈ Spos, δ₀ ≤ g q := by
    intro q hq
    have hne : Spos.Nonempty := ⟨q, hq⟩
    simp only [hδ₀, dif_pos hne]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem g hq)
  -- the region
  set N' : Set (Fin d → ℝ) := N ∩ Metric.closedBall w r' with hN'
  set Rg : Set (Fin d → ℝ) := N' ∪ ⋃ p : ι, Ω p with hRg
  have hΩU : ∀ p, Ω p ⊆ U := fun p => (hdp p).2.2.2.1
  have hRgU : Rg ⊆ U := by
    refine union_subset (inter_subset_right.trans hcball) (iUnion_subset fun p => hΩU p)
  have hRgc : IsCompact Rg := by
    refine IsCompact.union ?_ (isCompact_iUnion fun p => (hdp p).2.2.1)
    exact R.K_compact.inter_right Metric.isClosed_closedBall
  have hRgn : Rg ∈ 𝓝 w := by
    refine Filter.mem_of_superset (Filter.inter_mem hN (Metric.closedBall_mem_nhds w hr'pos)) ?_
    exact subset_union_left
  have hRgm : MeasurableSet Rg := hRgc.isClosed.measurableSet
  -- a.e. cover: off the null set of the resolution, small phase forces membership in a piece
  have hcover : ∀ x ∈ N', x ∉ N \ ⋃ i, R.φ i '' R.dom i → x ∉ ⋃ p : ι, Ω p → δ₀ ≤ K x := by
    intro x hxN' hxE hxΩ
    have hxim : x ∈ ⋃ i, R.φ i '' R.dom i := by
      by_contra hcon
      exact hxE ⟨hxN'.1, hcon⟩
    obtain ⟨i, y, hyD, rfl⟩ := mem_iUnion.1 hxim
    have hyDi : y ∈ D i := ⟨hyD, hxN'.2⟩
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (htcover i hyDi)
    by_cases hKz : K (R.φ i z) = 0
    · -- divisor-type centre: `y` lies in a piece
      have hzZ : z ∈ Zc i := Finset.mem_filter.2 ⟨hzt, hKz⟩
      have hyV : y ∈ Vd i z := by
        simp only [hUn, if_pos hKz] at hyz
        exact hyz
      exfalso
      apply hxΩ
      refine mem_iUnion.2 ⟨⟨i, ⟨z, hzZ⟩⟩, ?_⟩
      exact (hdp ⟨i, ⟨z, hzZ⟩⟩).2.2.2.2.1 y hyV
    · -- positive-type centre: the phase is at least the gap
      have hyV : y ∈ Vp i z := by
        simp only [hUn, if_neg hKz] at hyz
        exact hyz
      have hzP : (⟨i, z⟩ : Σ i : R.ι, Fin d → ℝ) ∈ Spos :=
        Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨hzt, hKz⟩⟩
      exact (hδ₀le _ hzP).trans ((hp i z (htD i z hzt) hKz).2.2 y hyV)
  have hgap : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∈ Rg → x ∉ ⋃ p : ι, Ω p → δ₀ ≤ K x := by
    have hnull : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∉ N \ ⋃ i, R.φ i '' R.dom i := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => not_not.1 hx) R.cover
    filter_upwards [hnull] with x hxE hxRg hxΩ
    rcases hxRg with hxN' | hxΩ'
    · exact hcover x hxN' hxE hxΩ
    · exact absurd hxΩ' hxΩ
  -- at least one divisor-type piece: the phase is small on a neighbourhood of `w`
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hgap' : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∈ Rg → δ₀ ≤ K x := by
      filter_upwards [hgap] with x hx hxRg
      exact hx hxRg (by simp)
    -- the ball on which `K < δ₀`
    have hKc : ContinuousAt K w := (hK w hw).continuousAt
    have hev : ∀ᶠ x in 𝓝 w, K x < δ₀ := hKc.eventually (gt_mem_nhds (by rw [hKw]; exact hδ₀pos))
    obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hev hRgn)
    have hpos : 0 < volume (Metric.ball w ρ) := Metric.measure_ball_pos volume w hρ
    have hzero : volume (Metric.ball w ρ) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hgap')
      intro x hx
      have := hρball hx
      simp only [mem_ofPred_eq]
      push Not
      exact ⟨this.2, this.1⟩
    exact hpos.ne' hzero
  -- the conditional theorem
  have hF0 : ∀ x ∈ Rg, 0 ≤ F x := fun x hx => (hFpos x (hRgU hx)).le
  have hFint : IntegrableOn F Rg volume :=
    (hF.continuousOn.mono hRgU).integrableOn_compact hRgc
  have hK0' : ∀ x ∈ Rg, 0 ≤ K x := fun x hx => hK0 x (hRgU hx)
  have hΩm : ∀ p, MeasurableSet (Ω p) := fun p => (hdp p).2.2.1.isClosed.measurableSet
  have hΩR : ∀ p, Ω p ⊆ Rg := fun p => (subset_iUnion Ω p).trans subset_union_right
  have hcpos : ∀ p, 0 < c p := fun p => (hdp p).2.2.2.2.2.2.1
  have hI : ∀ p, (fun N : ℝ => ∫ x in Ω p, F x * Real.exp (-N * K x)) ~[atTop]
      fun N => c p * powLogScale (lam p) (m p - 1) N := fun p => (hdp p).2.2.2.2.2.2.2
  obtain ⟨i₀, hmin, hmax, hΘ⟩ := isTheta_of_local_leading_terms hRgm hF0 hFint hK0' hKm Ω hΩm hΩR
    hδ₀pos hgap c lam m hcpos hI
  refine ⟨Rg, hRgc, hRgn, hRgU, ι, inferInstance, lam, m, i₀, fun p => ?_, hmin, hmax, hΘ⟩
  obtain ⟨C, hl, hm⟩ := (hdp p).2.2.2.2.2.1
  exact ⟨p.1, p.2.1, h p.1, C, (hpZ p).1.1, (hpZ p).2, hl, hm⟩

/-- **The resolution formula for the exponent of a Laplace integral, unconditionally.** For
`K ≥ 0` analytic on an open `U ∋ w` with `K w = 0` and `K` not identically zero near `w`, and
`F > 0` analytic on `U`, hironaka's chart form (`Q_all`) provides a monomial partial resolution `R`
of `K` on a compact neighbourhood of `w`, and some compact neighbourhood `Ω ⊆ U` of `w` has
`∫_Ω F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})` with `(λ_*, m_*)` the min/max over finitely many
divisor-point chart pairs `(min_j (h_{n_j}+1)/(2k_j), #minimisers)` of `R`. -/
theorem exponent_of_analytic {U : Set (Fin d → ℝ)} (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ}
    (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K) {w : Fin d → ℝ}
    (hw : w ∈ U) (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x) :
    ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
      ∃ Rg : Set (Fin d → ℝ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ U ∧
        ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
          (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
            (C : CentredChartData K (R.φ i) h y₀),
            y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
          (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
          regionIntegral volume Rg F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  obtain ⟨N, -, hNn, R, hR⟩ := Monomialize.Analytic.exists_monomialResolution_at
    (Monomialize.Analytic.Q_all d) hU hK hw hKw hne
  exact ⟨N, R, hR, exponent_of_monomialResolution hU hK hK0 hKm hw hKw hF hFpos hNn R hR⟩

end Grammar
