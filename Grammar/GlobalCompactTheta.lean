/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GlobalExponentHironaka
import Grammar.GlobalLaplaceMeasureBasic

/-!
# The exponent of the original integral over a compact region, unconditionally (CCXCIV)

Unit 8 of the global programme (consult #89): the finite-cover globalisation of the local
resolution formula `exponent_of_analytic`. For a compact region `W` inside an open set `U` on which
`K ≥ 0` and `F > 0` are analytic, with the zero set `W₀ = W ∩ {K = 0}` nonempty, contained in the
interior of `W`, and `K` not identically zero near any of its points, the ORIGINAL integral
`∫_W F e^{−tK}` is `Θ(t^{−λ*} (log t)^{m*−1})` where `(λ*, m*)` is the extremal pair (minimal
exponent, then maximal multiplicity) over a finite family of local pairs, each the pair
`(min_j (h_{n_j}+1)/(2k_j), #minimisers)` of a centred chart of a hironaka monomial resolution at a
divisor point (`exponent_of_compact`). No a.e.-disjointness, no assembly certificate and no
partition of unity: the upper bound sums finitely many local neighbourhoods and an exponentially
small remainder on the compact set where `K` has a positive minimum, the lower bound is the one
extremal neighbourhood (`isTheta_of_local_theta`, the `Θ`-input variant of
`isTheta_of_local_leading_terms`).

The interior hypothesis is essential: a zero of `K` on the boundary of `W` can change or destroy
the power–log asymptotics. The coefficient is not identified here (that is the certified leading
measure of CCXC–CCXCIII).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.VolumeScaling

namespace Grammar

/-! ### The global exponent from local `Θ`-inputs -/

section Global

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {R : Set X} (hR : MeasurableSet R)
  {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x) (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x)
  (hKm : Measurable K) {ι : Type*} (Ω : ι → Set X)
  (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩR : ∀ i, Ω i ⊆ R) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
  (hgap : ∀ᵐ x ∂μ, x ∈ R → x ∉ ⋃ i, Ω i → δ₀ ≤ K x) (lam : ι → ℝ) (m : ι → ℕ)
  (hI : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) =Θ[atTop]
    powLogScale (lam i) (m i - 1))

include hR hF0 hFint hK0 hKm hΩm hΩR hI in
/-- **Lower bound from the leading piece** (`Θ`-input). -/
theorem powLogScale_isBigO_regionIntegral_of_theta (i₀ : ι) :
    powLogScale (lam i₀) (m i₀ - 1) =O[atTop] regionIntegral μ R F K := by
  refine (hI i₀).symm.isBigO.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have hpos : 0 ≤ ∫ x in Ω i₀, F x * Real.exp (-N * K x) ∂μ :=
    setIntegral_nonneg (hΩm i₀) fun x hx => regionIntegrand_nonneg hF0 (hΩR i₀ hx)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (hpos.trans (setIntegral_le_regionIntegral hR hF0 hFint hK0 hKm (hΩR i₀) hN))]
  exact setIntegral_le_regionIntegral hR hF0 hFint hK0 hKm (hΩR i₀) hN

include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hI in
/-- **Upper bound from the cover and the gap** (`Θ`-input). -/
theorem regionIntegral_isBigO_powLogScale_of_theta [Finite ι] {i₀ : ι}
    (hmin : ∀ i, lam i₀ ≤ lam i) (hmax : ∀ i, lam i = lam i₀ → m i ≤ m i₀) :
    regionIntegral μ R F K =O[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  classical
  cases nonempty_fintype ι
  set g := powLogScale (lam i₀) (m i₀ - 1) with hg
  have hpiece : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) =O[atTop] g := by
    intro i
    refine (hI i).isBigO.trans ?_
    rcases lt_or_eq_of_le (hmin i) with hlt | heq
    · exact (powLogScale_isLittleO_of_lt hlt _ _).isBigO
    · rw [← heq]
      exact powLogScale_isBigO_of_le _ (Nat.sub_le_sub_right (hmax i heq.symm) 1)
  have htail : (fun N : ℝ => Real.exp (-N * δ₀) * ∫ x in R, F x ∂μ) =O[atTop] g :=
    (((exp_neg_isLittleO_powLogScale hδ₀ _ _).isBigO).const_mul_left (∫ x in R, F x ∂μ)).congr_left
      fun N => mul_comm _ _
  have hsum : (fun N : ℝ => (∑ i, ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) +
      Real.exp (-N * δ₀) * ∫ x in R, F x ∂μ) =O[atTop] g := by
    refine IsBigO.add ?_ htail
    have := IsBigO.sum (l := atTop) (g := g) (s := Finset.univ)
      (A := fun i (N : ℝ) => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) fun i _ => hpiece i
    refine this.congr_left fun N => ?_
    simp only [Finset.sum_apply]
  refine (IsBigO.of_bound 1 ?_).trans hsum
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have hZ0 : 0 ≤ regionIntegral μ R F K N :=
    setIntegral_nonneg hR fun x hx => regionIntegrand_nonneg hF0 hx
  have hle := regionIntegral_le_sum_add_tail hR hF0 hFint hK0 hKm Ω hΩm hΩR hgap hN
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hZ0, abs_of_nonneg (hZ0.trans hle)]
  exact hle

include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hI in
/-- **The global exponent from local `Θ`-inputs**: the region integral is
`Θ(N^{−λ*}(log N)^{m*−1})` at the extremal pair of the local pairs. -/
theorem isTheta_of_local_theta [Finite ι] [Nonempty ι] :
    ∃ i₀ : ι, (∀ i, lam i₀ ≤ lam i) ∧ (∀ i, lam i = lam i₀ → m i ≤ m i₀) ∧
      regionIntegral μ R F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  obtain ⟨i₀, hmin, hmax⟩ := exists_leading_piece lam m
  exact ⟨i₀, hmin, hmax,
    ⟨regionIntegral_isBigO_powLogScale_of_theta hR hF0 hFint hK0 hKm Ω hΩm hΩR hδ₀ hgap lam m hI
      hmin hmax,
    powLogScale_isBigO_regionIntegral_of_theta hR hF0 hFint hK0 hKm Ω hΩm hΩR lam m hI i₀⟩⟩

end Global

/-! ### The compact-region theorem -/

variable {d : ℕ}

/-- **The local input at a zero**: a compact neighbourhood inside `W` on which the integral is
`Θ` of a local resolution pair. -/
theorem exists_local_theta {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x)
    {w : Fin d → ℝ} (hw : w ∈ W) (hKw : K w = 0) (hint : w ∈ interior W) (hnt : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ (Rg : Set (Fin d → ℝ)) (l : ℝ) (q : ℕ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ W ∧
      (∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
        ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ l = C.lam ∧ q = C.mult) ∧
      regionIntegral volume Rg F K =Θ[atTop] powLogScale l (q - 1) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨N, R, hR, Rg, hRgc, hRgn, hRgb, -, ι, _, lam, m, i₀, hdesc, hmin, hmax, hΘ⟩ :=
    exponent_of_analytic hU hK hK0 hKm (hWU hw) hKw hnt hF hFpos (half_pos hρ)
  refine ⟨Rg, lam i₀, m i₀, hRgc, hRgn, ?_, ?_, hΘ⟩
  · exact hRgb.trans ((Metric.closedBall_subset_ball (half_lt_self hρ)).trans hball)
  · obtain ⟨i, y₀, h, C, hy₀, hKy₀, hl, hm⟩ := hdesc i₀
    exact ⟨N, R, hR, i, y₀, h, C, hy₀, hKy₀, hl, hm⟩

/-- ★★★ **The exponent of the original integral over a compact region, unconditionally.** For `W`
compact inside an open `U` with `K ≥ 0`, `F > 0` analytic on `U`, the zero set `W ∩ {K = 0}`
nonempty and contained in the interior of `W`, and `K` not identically zero near any zero,
`∫_W F e^{−tK} = Θ(t^{−λ*} (log t)^{m*−1})` where `(λ*, m*)` is the extremal pair (minimal exponent,
then maximal multiplicity) of a finite family of local resolution pairs, each the pair of a centred
chart of a hironaka monomial resolution at a divisor point over a zero of `K` in `W`. -/
theorem exponent_of_compact {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hW : IsCompact W)
    (hWU : W ⊆ U) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x)
    (hKm : Measurable K) {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U)
    (hFpos : ∀ x ∈ U, 0 < F x) (hint : ∀ w ∈ W, K w = 0 → w ∈ interior W)
    (hnt : ∀ w ∈ W, K w = 0 → ¬ K =ᶠ[𝓝 w] 0) (hW0 : ∃ w ∈ W, K w = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
      (∀ p, ∃ w ∈ W, K w = 0 ∧ ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N),
        R.IsMonomial ∧ ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
          (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
      (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
      globalLaplace W K F =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  classical
  -- the zero set is compact
  have hKc : ContinuousOn K W := (hK.continuousOn).mono hWU
  set W₀ : Set (Fin d → ℝ) := W ∩ K ⁻¹' {0} with hW₀def
  have hW₀c : IsCompact W₀ :=
    hW.of_isClosed_subset (hKc.preimage_isClosed_of_isClosed hW.isClosed isClosed_singleton)
      inter_subset_left
  -- local data at every zero
  have hloc : ∀ w : W₀, ∃ (Rg : Set (Fin d → ℝ)) (l : ℝ) (q : ℕ), IsCompact Rg ∧
      Rg ∈ 𝓝 (w : Fin d → ℝ) ∧ Rg ⊆ W ∧
      (∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
        ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ l = C.lam ∧ q = C.mult) ∧
      regionIntegral volume Rg F K =Θ[atTop] powLogScale l (q - 1) := fun w =>
    exists_local_theta hU hWU hK hK0 hKm hF hFpos w.2.1 w.2.2 (hint w w.2.1 w.2.2)
      (hnt w w.2.1 w.2.2)
  choose Rg l q hRgc hRgn hRgW hdesc hΘ using hloc
  -- a finite subcover of the zero set by the interiors
  have hcov : W₀ ⊆ ⋃ w : W₀, interior (Rg w) := fun x hx =>
    mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hRgn ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hW₀c.elim_finite_subcover (fun w : W₀ => interior (Rg w))
    (fun _ => isOpen_interior) hcov
  obtain ⟨w₀, hw₀W, hw₀K⟩ := hW0
  have hw₀ : w₀ ∈ ⋃ w ∈ t, interior (Rg w) := ht ⟨hw₀W, hw₀K⟩
  obtain ⟨j₀, hj₀t, -⟩ := mem_iUnion₂.1 hw₀
  -- the index type
  let ι := {w : W₀ // w ∈ t}
  have : Nonempty ι := ⟨⟨j₀, hj₀t⟩⟩
  -- the gap on the complement of the interiors
  set S : Set (Fin d → ℝ) := W \ ⋃ j : ι, interior (Rg j.1) with hSdef
  have hSc : IsCompact S := hW.diff (isOpen_iUnion fun _ => isOpen_interior)
  have hSpos : ∀ x ∈ S, 0 < K x := fun x hx => by
    rcases (hK0 x (hWU hx.1)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hx₀ : x ∈ W₀ := ⟨hx.1, h.symm⟩
      obtain ⟨j, hjt, hj⟩ := mem_iUnion₂.1 (ht hx₀)
      exact hx.2 (mem_iUnion.2 ⟨⟨j, hjt⟩, hj⟩)
  obtain ⟨δ₀, hδ₀, hδ⟩ := exists_pos_le_of_isCompact hSc (hKc.mono sdiff_subset) hSpos
  have hgap : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∈ W → x ∉ ⋃ j : ι, Rg j.1 → δ₀ ≤ K x :=
    Eventually.of_forall fun x hxW hx => hδ x ⟨hxW, fun hxi => hx (mem_iUnion.2
      (by obtain ⟨j, hj⟩ := mem_iUnion.1 hxi; exact ⟨j, interior_subset hj⟩))⟩
  -- assemble
  obtain ⟨i₀, hmin, hmax, hΘW⟩ := isTheta_of_local_theta (μ := volume) hW.measurableSet
    (fun x hx => (hFpos x (hWU hx)).le)
    ((hF.continuousOn.mono hWU).integrableOn_compact hW) (fun x hx => hK0 x (hWU hx)) hKm
    (fun j : ι => Rg j.1) (fun j => (hRgc j.1).isClosed.measurableSet) (fun j => hRgW j.1) hδ₀
    hgap (fun j : ι => l j.1) (fun j : ι => q j.1) (fun j => hΘ j.1)
  refine ⟨ι, inferInstance, inferInstance, fun j => l j.1, fun j => q j.1, i₀, fun j => ?_,
    hmin, hmax, hΘW⟩
  exact ⟨j.1, j.1.2.1, j.1.2.2, hdesc j.1⟩

end Grammar
