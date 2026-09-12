/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.WholeBoxSourceCertificate
import Grammar.AEDisjointSourceAssembly

/-!
# Boundary-compatible box assemblies (CCLXXXII)

The second unit of the derived-certificate programme (consult #86, A2): finitely many centred
product boxes at divisor points of ONE monomial chart (`BoxFamily`) whose pairwise intersections are
null give, through the whole-box certificates of CCLXXXI and the a.e.-disjoint assembly of
CCLXXVIII, the explicit positive leading coefficient of any target region a.e.-equal to the union
of the box images — the certificate is DERIVED from the monomial-chart data:

* the **a.e.-disjointness criterion** `IsMonomialChart.volume_image_inter_eq_zero`: the images of
  two subsets of the monomial neighbourhood with null intersection have null intersection (points
  of a common image come from the null intersection or from the null Jacobian zero set, by the
  off-exceptional injectivity; differentiable maps preserve null sets);
* `ProductMonomialChartVar.sourceCoeff_eq_of_cutoff`: the source coefficient does not depend on
  the cutoff (uniqueness of certificates), so the positivity of CCLXXXI at cutoff `ρ/2` transfers
  to the uniform cutoff of an assembly;
* `exists_mem_tiedCharts'`: the extremal pair over the active charts is attained;
* ★★ `BoxFamily.targetIntegral_isEquivalent`: for `F∘φ`, `p∘φ` continuous on the neighbourhood and
  positive on the closed boxes, `∫_{Rg} F p e^{−nK} ~ c n^{−λ*}(log n)^{k*}` with `c > 0` the sum of
  the tied whole-box source coefficients, `(λ*, k*)` the extremal divisor pair over the boxes.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

/-! ### Cutoff independence and the attained extremal pair -/

namespace ProductMonomialChartVar

open ResolutionCover (ofChart)

variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) {ε ε' : ℝ} (hε : 0 < ε)
  (hε' : 0 < ε') (hεb : ε ≤ P.b) (hεb' : ε' ≤ P.b) {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W) (hGm : Measurable G)
  (hGc : ContinuousOn G C.dom) (hK : Measurable K)

include hK0 hε hε' hεb hεb' hpc hGm hGc hK in
/-- **The source coefficient does not depend on the cutoff** (uniqueness of certificates). -/
theorem sourceCoeff_eq_of_cutoff (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty, lam₀ ≤ P.pieceLam I hne)
    (hk : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty,
      P.pieceLam I hne = lam₀ → P.pieceMult I hne - 1 ≤ k₀) :
    P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ =
      P.sourceCoeff hK0 hε' hεb' hpc hGm hGc hK lam₀ k₀ :=
  (P.hasLeadingTerm_sourceChartIntegral hK0 hε hεb hpc hGm hGc hK lam₀ k₀ hlam hk).coeff_unique
    (P.hasLeadingTerm_sourceChartIntegral hK0 hε' hεb' hpc hGm hGc hK lam₀ k₀ hlam hk)

end ProductMonomialChartVar

/-- The extremal pair of a finite family is attained. -/
theorem exists_extremalDegree_eq {α : Type*} (s : Finset α) (lam : α → ℝ) (k : α → ℕ)
    (hs : s.Nonempty) :
    ∃ j ∈ s, lam j = extremalExponent s lam hs ∧ k j = extremalDegree s lam k hs := by
  obtain ⟨j, hj, hk⟩ := Finset.exists_mem_eq_sup' (nonempty_filter_extremal s lam hs) k
  rw [Finset.mem_filter] at hj
  exact ⟨j, hj.1, hj.2, hk.symm⟩

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)

/-- **Some active chart is tied** at the extremal pair. -/
theorem exists_mem_tiedCharts' (hne : (R.activeCharts Ps).Nonempty) :
    ∃ i, i ∈ R.tiedCharts' Ps hne := by
  classical
  obtain ⟨i, hi, h1, h2⟩ :=
    exists_extremalDegree_eq (R.activeCharts Ps) (R.chartLam' Ps) (R.chartDeg' Ps) hne
  exact ⟨i, Finset.mem_filter.2 ⟨hi, h1, h2⟩⟩

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) {F : (Fin d → ℝ) → ℝ}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty)

include hK0 hε hεb hpc hFc hFm hK in
/-- The assembled coefficient is positive when one tied chart's term is positive. -/
theorem aeDisjointCoeff_pos_of_tied (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hi₀ : i₀ ∈ R.tiedCharts' Ps hne)
    (hpos : 0 < R.sourceChartCoeff' Ps (fun i y => F ((R.chart i).Φ y)) hK0 hε hεb hpc
      (fun i => hFm.comp (R.chart i).measurable_Φ)
      (fun i => continuousOn_pullback_Φ (R.chart i) (hFc i) (Ps i).dom_subset) hK i₀) :
    0 < R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne := by
  unfold aeDisjointCoeff sourceDecompCoeff
  exact Finset.sum_pos' (fun i _ => R.sourceChartCoeff'_nonneg Ps _ hK0 hε hεb hpc _ _ hK
    (fun _ _ => hF0 _) hp0 hr0 i) ⟨i₀, hi₀, hpos⟩

include hK0 hε hεb hpc hFc hFm hK in
/-- **Asymptotic equivalence from a positive assembled coefficient** (a.e.-disjoint images). -/
theorem targetIntegral_isEquivalent_of_aeDisjoint_of_pos (hdisj : R.AEDisjointImages)
    {Rg : Set (Fin d → ℝ)} (h₁ : volume (Rg \ ⋃ i, R.image i) = 0)
    (h₂ : volume ((⋃ i, R.image i) \ Rg) = 0)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hcpos : 0 < R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne) :
    targetIntegral Rg F K p ~[atTop] fun N =>
      R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne *
        powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) N := by
  have h := (R.hasLeadingTerm_boltzmannIntegral_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK hne
    hdisj hF).isEquivalent hcpos.ne'
  have heq : targetIntegral Rg F K p = R.boltzmannIntegral F K p :=
    funext fun N => R.targetIntegral_eq_boltzmannIntegral_of_ae_eq h₁ h₂ F K p N
  rw [heq]
  exact h

end ResolutionCover

/-! ### The a.e.-disjointness criterion within one monomial chart -/

section Criterion

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W)

include hc in
/-- **Images of null-intersecting subsets of the monomial neighbourhood have null intersection**:
a common image point comes from the null intersection or from the null Jacobian zero set. -/
theorem IsMonomialChart.volume_image_inter_eq_zero {A B : Set (Fin d → ℝ)} (hA : A ⊆ W)
    (hB : B ⊆ W) (hAB : volume (A ∩ B) = 0) : volume (φ '' A ∩ φ '' B) = 0 := by
  have hdiff : DifferentiableOn ℝ φ W := hc.analyticOnNhd.differentiableOn
  have hsub : φ '' A ∩ φ '' B ⊆
      φ '' (A ∩ B) ∪ φ '' ((A ∪ B) ∩ {y | monomialEval y h = 0}) := by
    rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    by_cases ha0 : monomialEval a h = 0
    · exact Or.inr ⟨a, ⟨Or.inl ha, ha0⟩, rfl⟩
    by_cases hb0 : monomialEval b h = 0
    · exact Or.inr ⟨b, ⟨Or.inr hb, hb0⟩, hab⟩
    · have hba : b = a := hc.injOn ⟨hB hb, hb0⟩ ⟨hA ha, ha0⟩ hab
      exact Or.inl ⟨a, ⟨ha, hba ▸ hb⟩, rfl⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hdiff.mono fun y (hy : y ∈ A ∩ B) => hA hy.1) hAB
  · exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hdiff.mono fun y (hy : y ∈ (A ∪ B) ∩ {y | monomialEval y h = 0}) =>
        hy.1.elim (fun h' => hA h') fun h' => hB h')
      (measure_mono_null inter_subset_right (volume_monomialEval_zero_set h))

end Criterion

/-! ### Box families -/

/-- **A finite family of admissible centred boxes at divisor points** of a monomial chart. -/
structure BoxFamily {d : ℕ} (e : Fin d →₀ ℕ) (W : Set (Fin d → ℝ)) (ι : Type*) where
  /-- The divisor points. -/
  pt : ι → (Fin d → ℝ)
  /-- The box radii. -/
  ρ : ι → ℝ
  ρ_pos : ∀ k, 0 < ρ k
  ball_subset : ∀ k, Metric.closedBall (pt k) (ρ k) ⊆ restrictNhd e (divisorSet e (pt k)) W
  divisor : ∀ k, monomialEval (pt k) e = 0

namespace BoxFamily

open ResolutionCover (ofChart)

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} {ι : Type*} [Fintype ι] (Bf : BoxFamily e W ι)
  (hc : IsMonomialChart K φ dom e h W)

/-- The box of `k`. -/
abbrev box (k : ι) : Set (Fin d → ℝ) := productBox e (Bf.pt k) (Bf.ρ k)

omit [Fintype ι] in
theorem box_subset_W (k : ι) : Bf.box k ⊆ W :=
  (productBox_subset_restrictNhd (Bf.ρ_pos k) (Bf.ball_subset k)).trans (restrictNhd_subset _ _ _)

include hc in
/-- **The cover of box charts.** -/
noncomputable def cover : ResolutionCover d ι :=
  ⟨fun k => IsMonomialChart.boxChart hc (Bf.ρ_pos k) (Bf.ball_subset k)⟩

include hc in
/-- **The box packages.** -/
noncomputable def packages : ∀ k, ProductMonomialChartVar (ofChart ((Bf.cover hc).chart k)) () K :=
  fun k => IsMonomialChart.boxPackage hc (Bf.ρ_pos k) (Bf.ball_subset k)

theorem image_eq (k : ι) : (Bf.cover hc).image k = φ '' Bf.box k := rfl

theorem packages_b (k : ι) : (Bf.packages hc k).b = Bf.ρ k := rfl

theorem packages_r (k : ι) (x : Fin d → ℝ) : (Bf.packages hc k).r x = 1 := rfl

theorem packages_isActive (k : ι) : (Bf.packages hc k).IsActive :=
  IsMonomialChart.boxPackage_isActive hc (Bf.ρ_pos k) (Bf.ball_subset k) (Bf.divisor k)

theorem activeCharts_nonempty [Nonempty ι] :
    ((Bf.cover hc).activeCharts (Bf.packages hc)).Nonempty :=
  ⟨Classical.arbitrary ι, ((Bf.cover hc).mem_activeCharts (Bf.packages hc)).2
    (Bf.packages_isActive hc _)⟩

/-- **The a.e.-disjointness criterion**: null pairwise box intersections give a.e.-disjoint images.
-/
theorem aeDisjointImages (hnull : ∀ k l, k ≠ l → volume (Bf.box k ∩ Bf.box l) = 0) :
    (Bf.cover hc).AEDisjointImages := fun k l hkl =>
  IsMonomialChart.volume_image_inter_eq_zero hc (Bf.box_subset_W k) (Bf.box_subset_W l)
    (hnull k l hkl)

variable (hK0 : ∀ x, 0 ≤ K x) (hK : Measurable K) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F (φ y)) W) (hpc : ContinuousOn (fun y => p.w (φ y)) W)
  (hFm : Measurable F) {ε : ℝ} (hε : 0 < ε) (hερ : ∀ k, ε ≤ Bf.ρ k)

include hc hK0 hK hFc hpc hFm hε hερ in
/-- **The assembled box coefficient**: the sum over the tied boxes of the whole-box source
coefficients (at the uniform cutoff). -/
noncomputable def coeff [Nonempty ι] : ℝ :=
  (Bf.cover hc).aeDisjointCoeff (Bf.packages hc) hK0 hε hερ
    (fun _ => hpc.mono (restrictNhd_subset _ _ _)) (fun _ => hFc.mono (restrictNhd_subset _ _ _))
    hFm hK (Bf.activeCharts_nonempty hc)

include hc hK0 hK hFc hpc hFm hε hερ in
/-- **Positivity of the assembled box coefficient** when `F∘φ`, `p∘φ` are positive on the closed
boxes: the tied box's whole-box coefficient is positive (CCLXXXI) at its own cutoff, hence at the
uniform cutoff. -/
theorem coeff_pos [Nonempty ι] (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hpos : ∀ k, ∀ y ∈ Metric.closedBall (Bf.pt k) (Bf.ρ k), 0 < F (φ y) ∧ 0 < p.w (φ y)) :
    0 < Bf.coeff hc hK0 hK hFc hpc hFm hε hερ := by
  obtain ⟨i₀, hi₀⟩ := (Bf.cover hc).exists_mem_tiedCharts' (Bf.packages hc)
    (Bf.activeCharts_nonempty hc)
  refine (Bf.cover hc).aeDisjointCoeff_pos_of_tied (Bf.packages hc) hK0 hε hερ _ _ hFm hK _ hF0 hp0
    (fun k x => by rw [Bf.packages_r]; exact zero_le_one) i₀ hi₀ ?_
  unfold ResolutionCover.sourceChartCoeff'
  rw [dif_pos (Bf.packages_isActive hc i₀), ResolutionCover.chartLam'_of_active _ _
    (Bf.packages_isActive hc i₀), ResolutionCover.chartDeg'_of_active _ _
    (Bf.packages_isActive hc i₀)]
  have hact := ((ofChart ((Bf.cover hc).chart i₀)).activeCoordsV_ofChart_nonempty_iff
    (fun _ => Bf.packages hc i₀) ()).2 (Bf.packages_isActive hc i₀)
  have hcut := (Bf.packages hc i₀).sourceCoeff_eq_of_cutoff hK0 hε (half_pos (Bf.ρ_pos i₀))
    (show ε ≤ (Bf.packages hc i₀).b from hερ i₀)
    (show Bf.ρ i₀ / 2 ≤ (Bf.packages hc i₀).b from half_le_self (Bf.ρ_pos i₀).le)
    (hpc.mono (restrictNhd_subset _ _ _)) (hFm.comp ((Bf.cover hc).chart i₀).measurable_Φ)
    (ResolutionCover.continuousOn_pullback_Φ ((Bf.cover hc).chart i₀) hFc (Bf.box_subset_W i₀)) hK
    ((ofChart ((Bf.cover hc).chart i₀)).coverLamV (fun _ => Bf.packages hc i₀) hact)
    ((ofChart ((Bf.cover hc).chart i₀)).coverDegV (fun _ => Bf.packages hc i₀) hact)
    (fun I hI hne =>
      (ofChart _).coverLamV_le_pieceLam (fun _ => Bf.packages hc i₀) hact () I hI hne)
    (fun I hI hne hl =>
      (ofChart _).pieceMult_le_coverDegV (fun _ => Bf.packages hc i₀) hact () I hI hne hl)
  rw [hcut]
  have hGp : ∀ y ∈ Metric.closedBall (Bf.pt i₀) (Bf.ρ i₀),
      0 < F (((Bf.cover hc).chart i₀).Φ y) ∧ 0 < p.w (φ y) := fun y hy => by
    rw [((Bf.cover hc).chart i₀).Φ_eqOn (closedBall_subset_productBox (Bf.ρ_pos i₀) hy)]
    exact hpos i₀ y hy
  exact (boxSourceIntegral_isEquivalent hc (Bf.ρ_pos i₀) (Bf.ball_subset i₀) hK0 hK (Bf.divisor i₀)
    hpc (hFm.comp ((Bf.cover hc).chart i₀).measurable_Φ)
    (ResolutionCover.continuousOn_pullback_Φ ((Bf.cover hc).chart i₀) hFc
      (Bf.box_subset_W i₀)) (fun _ => hF0 _) hp0 hGp).1

include hc hK0 hK hFc hpc hFm hε hερ in
/-- ★★ **The explicit leading coefficient of a region covered a.e. by the images of a box family
with null pairwise intersections**: `∫_{Rg} F p e^{−nK} ~ c n^{−λ*}(log n)^{k*}`, `c > 0` the sum of
the tied whole-box source coefficients. -/
theorem targetIntegral_isEquivalent [Nonempty ι]
    (hnull : ∀ k l, k ≠ l → volume (Bf.box k ∩ Bf.box l) = 0) {Rg : Set (Fin d → ℝ)}
    (h₁ : volume (Rg \ ⋃ k, φ '' Bf.box k) = 0) (h₂ : volume ((⋃ k, φ '' Bf.box k) \ Rg) = 0)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ k, φ '' Bf.box k)))
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hpos : ∀ k, ∀ y ∈ Metric.closedBall (Bf.pt k) (Bf.ρ k), 0 < F (φ y) ∧ 0 < p.w (φ y)) :
    0 < Bf.coeff hc hK0 hK hFc hpc hFm hε hερ ∧
      targetIntegral Rg F K p ~[atTop] fun N => Bf.coeff hc hK0 hK hFc hpc hFm hε hερ *
        powLogScale ((Bf.cover hc).partitionLam' (Bf.packages hc) (Bf.activeCharts_nonempty hc))
          ((Bf.cover hc).partitionDeg' (Bf.packages hc) (Bf.activeCharts_nonempty hc)) N :=
  ⟨Bf.coeff_pos hc hK0 hK hFc hpc hFm hε hερ hF0 hp0 hpos,
    (Bf.cover hc).targetIntegral_isEquivalent_of_aeDisjoint_of_pos (Bf.packages hc) hK0 hε hερ _ _
      hFm hK _ (Bf.aeDisjointImages hc hnull) h₁ h₂ hF
      (Bf.coeff_pos hc hK0 hK hFc hpc hFm hε hερ hF0 hp0 hpos)⟩

end BoxFamily

end Grammar
