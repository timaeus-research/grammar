/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BoxFamilyAssembly
import Monomialize.Analytic.BlowUpChart

/-!
# The blow-up charts of the unit cube in every dimension (CCLXXXIII)

The third unit of the derived-certificate programme (consult #86, A3): hironaka's standard blow-up
of the origin of `ℝ^d` (`blowUpChart` with the full block), `φ_β(y)_β = y_β`,
`φ_β(y)_γ = y_β y_γ`, on the unit cube `[−1, 1]^d`, for the quadratic phase `K = ∑ x_i²`:

* `K ∘ φ_β = y_β² (1 + ∑_{γ ≠ β} y_γ²)` and `det Dφ_β = y_β^{d−1}` (hironaka's axiom-clean
  `det_fderiv_blowUpChart`), so each chart is a monomial chart by hand (`isMonomialChart`) with
  `e = 2δ_β`, `h = (d−1)δ_β`, unit `1 + ∑_{γ≠β} y_γ²`, and the cube is its box at the origin
  (`cube_eq_productBox`), admissible with `W = univ`;
* the images are the wedges `{|x_β| ≤ 1, |x_γ| ≤ |x_β| ∀ γ}` (`image_eq`), they cover the cube
  exactly (hironaka's `blowUpChartBox_cover`) and meet only on the null diagonals
  (`volume_wedge_inter`);
* the cover of the `d` box charts with their box packages (CCLXXI's `boxPackage`) has
  a.e.-disjoint images (`aeDisjointImages`), all charts active with pair `(d/2, 0)`
  (`chartLam'_eq`, `chartDeg'_eq`, `partitionLam'_eq`, `partitionDeg'_eq`);
* ★★ `cubeIntegral_isEquivalent`: for `F`, `p` continuous and positive on the cube,
  `∫_{[−1,1]^d} F p e^{−N ∑ x_i²} ~ c N^{−d/2}` with `c > 0` the sum of the `d` whole-box source
  coefficients — "one blow-up suffices", the certificate DERIVED from the chart data (the
  identification `c = π^{d/2}` for `F = p = 1` is CCLXXXIV).

The dimension is at least `2` (`hd : 1 < d`): in dimension `1` the chart is the identity.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace BlowUpCube

variable {d : ℕ}

/-! ### The charts and the phase -/

/-- The full block. -/
def B (d : ℕ) : Fin d ↪ Fin d := Function.Embedding.refl (Fin d)

/-- The blow-up chart of pivot `β`. -/
noncomputable def φ (β : Fin d) : (Fin d → ℝ) → (Fin d → ℝ) := blowUpChart (B d) β

theorem φ_self (β : Fin d) (y : Fin d → ℝ) : φ β y β = y β := blowUpChart_apply_scaling (B d) y

theorem φ_other (β : Fin d) (y : Fin d → ℝ) {γ : Fin d} (hγ : γ ≠ β) : φ β y γ = y β * y γ :=
  blowUpChart_apply_ratio (B d) y hγ

theorem det_φ (β : Fin d) (y : Fin d → ℝ) : (fderiv ℝ (φ β) y).det = y β ^ (d - 1) := by
  unfold φ
  rw [det_fderiv_blowUpChart, Fintype.card_fin]
  rfl

theorem analyticOnNhd_φ (β : Fin d) : AnalyticOnNhd ℝ (φ β) univ := by
  classical
  have hproj : ∀ j : Fin d, AnalyticOnNhd ℝ (fun x : Fin d → ℝ => x j) univ := fun j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).analyticOnNhd univ
  unfold φ blowUpChart
  refine AnalyticOnNhd.pi fun j => ?_
  by_cases hj : ∃ γ, γ ≠ β ∧ B d γ = j
  · simp only [if_pos hj]
    exact (hproj (B d β)).mul (hproj j)
  · simp only [if_neg hj]
    exact hproj j

theorem continuous_φ (β : Fin d) : Continuous (φ β) := continuous_blowUpChart (B d) β

/-- The unit cube `[−1, 1]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc (-1) 1

theorem mem_cube {x : Fin d → ℝ} : x ∈ cube d ↔ ∀ j, |x j| ≤ 1 := by
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem isCompact_cube : IsCompact (cube d) := isCompact_univ_pi fun _ => isCompact_Icc

theorem zero_mem_cube : (0 : Fin d → ℝ) ∈ cube d := mem_cube.2 fun _ => by simp

theorem cube_eq_closedBall : cube d = Metric.closedBall 0 1 := by
  ext x
  rw [mem_cube, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs]

theorem cube_eq_centeredBox : cube d = centeredBox d 1 := by
  ext x
  rw [mem_cube]
  rfl

/-- The quadratic phase `K(x) = ∑ x_i²`. -/
noncomputable def K (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem K_nonneg (x : Fin d → ℝ) : 0 ≤ K x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_K : Continuous (K (d := d)) := by
  unfold K
  fun_prop

/-- The unit `1 + ∑_{γ ≠ β} y_γ²`. -/
noncomputable def unit (β : Fin d) (y : Fin d → ℝ) : ℝ := 1 + ∑ γ ∈ Finset.univ.erase β, y γ ^ 2

theorem unit_pos (β : Fin d) (y : Fin d → ℝ) : 0 < unit β y :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem continuous_unit (β : Fin d) : Continuous (unit β) := by
  unfold unit
  fun_prop

theorem K_φ (β : Fin d) (y : Fin d → ℝ) : K (φ β y) = unit β y * y β ^ 2 := by
  classical
  unfold K unit
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ β), φ_self]
  have h : ∀ γ ∈ Finset.univ.erase β, φ β y γ ^ 2 = y β ^ 2 * y γ ^ 2 := fun γ hγ => by
    rw [φ_other β y (Finset.ne_of_mem_erase hγ)]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

/-! ### The monomial data -/

/-- The phase exponents `2δ_β`. -/
noncomputable def expo (β : Fin d) : Fin d →₀ ℕ := Finsupp.single β 2

/-- The Jacobian exponents `(d−1)δ_β`. -/
noncomputable def jexp (β : Fin d) : Fin d →₀ ℕ := Finsupp.single β (d - 1)

theorem monomialEval_single (y : Fin d → ℝ) (β : Fin d) (k : ℕ) :
    monomialEval y (Finsupp.single β k) = y β ^ k := by
  unfold monomialEval
  exact Finsupp.prod_single_index (pow_zero _)

theorem expo_support (β : Fin d) : (expo β).support = {β} :=
  Finsupp.support_single_ne_zero β two_ne_zero

theorem monomialEval_expo (β : Fin d) (y : Fin d → ℝ) : monomialEval y (expo β) = y β ^ 2 :=
  monomialEval_single y β 2

theorem monomialEval_jexp (β : Fin d) (y : Fin d → ℝ) :
    monomialEval y (jexp β) = y β ^ (d - 1) :=
  monomialEval_single y β (d - 1)

variable (hd : 1 < d)

include hd in
/-- **The blow-up chart is a monomial chart for the quadratic phase on the cube.** -/
theorem isMonomialChart (β : Fin d) :
    IsMonomialChart K (φ β) (cube d) (expo β) (jexp β) univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_φ β
  injOn := fun a ha b hb hab => by
    have ha' : monomialEval a (jexp β) ≠ 0 := ha.2
    have hb' : monomialEval b (jexp β) ≠ 0 := hb.2
    rw [monomialEval_jexp] at ha' hb'
    exact blowUpChart_injOn_compl_pivotHyperplane (B d) β
      (fun h0 => ha' (by
        rw [show a (B d β) = a β from rfl] at h0
        rw [h0]
        exact zero_pow (by omega)))
      (fun h0 => hb' (by
        rw [show b (B d β) = b β from rfl] at h0
        rw [h0]
        exact zero_pow (by omega)))
      hab
  exists_unit := ⟨unit β, (continuous_unit β).continuousOn, fun y _ => (unit_pos β y).ne',
    fun y _ => by rw [K_φ, monomialEval_expo]⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero,
    fun y _ => by rw [det_φ, monomialEval_jexp, one_mul]⟩

/-- The divisor set of the origin is the support. -/
theorem divisorSet_zero (β : Fin d) : divisorSet (expo β) 0 = {β} :=
  (Finset.filter_true_of_mem fun _ _ => rfl).trans (expo_support β)

/-- The admissibility of the unit box at the origin (everything is the whole space). -/
theorem ball_subset (β : Fin d) :
    Metric.closedBall (0 : Fin d → ℝ) 1 ⊆ restrictNhd (expo β) (divisorSet (expo β) 0) univ :=
  fun y _ => mem_restrictNhd.2 ⟨mem_univ y, fun j hj hjD => by
    rw [divisorSet_zero] at hjD
    rw [expo_support] at hj
    exact absurd hj hjD⟩

theorem cube_eq_productBox (β : Fin d) : cube d = productBox (expo β) 0 1 := by
  rw [productBox_eq_closedBall one_pos, cube_eq_closedBall]

/-! ### The wedges -/

/-- The wedge `{|x_β| ≤ 1, |x_γ| ≤ |x_β| ∀ γ}`. -/
def wedge (β : Fin d) : Set (Fin d → ℝ) := {x | |x β| ≤ 1 ∧ ∀ γ, |x γ| ≤ |x β|}

theorem wedge_subset_cube (β : Fin d) : wedge β ⊆ cube d := fun _ ⟨h1, h2⟩ =>
  mem_cube.2 fun γ => (h2 γ).trans h1

theorem image_eq (β : Fin d) : φ β '' cube d = wedge β := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_cube] at hy
    refine ⟨by rw [φ_self]; exact hy β, fun γ => ?_⟩
    by_cases hγ : γ = β
    · rw [hγ]
    · rw [φ_other β y hγ, φ_self, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hy γ)
  · rintro ⟨h1, h2⟩
    by_cases h0 : x β = 0
    · have hz : x = 0 := funext fun γ => by
        have := h2 γ
        rw [h0, abs_zero] at this
        exact abs_nonpos_iff.1 this
      refine ⟨0, zero_mem_cube, ?_⟩
      rw [hz]
      exact blowUpChart_zero (B d) β
    · refine ⟨fun γ => if γ = β then x β else x γ / x β, mem_cube.2 fun γ => ?_, funext fun γ => ?_⟩
      · split_ifs with hγ
        · exact h1
        · rw [abs_div, div_le_one (abs_pos.2 h0)]
          exact h2 γ
      · by_cases hγ : γ = β
        · rw [hγ, φ_self, if_pos rfl]
        · rw [φ_other β _ hγ, if_pos rfl, if_neg hγ, mul_div_cancel₀ _ h0]

theorem blowUpChartBox_one (β : Fin d) : blowUpChartBox (B d) β 1 = cube d := by
  ext x
  rw [mem_blowUpChartBox_iff, mem_cube]
  constructor
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = β
    · exact h2 j fun γ hγ hγj => hγ (hγj.trans hj)
    · exact h1 j hj
  · intro h
    exact ⟨fun γ _ => h γ, fun j _ => h j⟩

/-- **The wedges cover the cube** (hironaka's argmax cover). -/
theorem iUnion_wedge [NeZero d] : ⋃ β, wedge β = cube d := by
  refine subset_antisymm (iUnion_subset wedge_subset_cube) ?_
  intro x hx
  have h := blowUpChartBox_cover (B d) (1 : ℝ) (cube_eq_centeredBox ▸ hx)
  obtain ⟨β, hβ⟩ := mem_iUnion.1 h
  rw [blowUpChartBox_one] at hβ
  exact mem_iUnion.2 ⟨β, (image_eq β) ▸ hβ⟩

/-- The diagonal `{x_β = c · x_γ}` as a subspace. -/
noncomputable def diagonal (β γ : Fin d) (c : ℝ) : Submodule ℝ (Fin d → ℝ) :=
  LinearMap.ker (LinearMap.proj β - c • LinearMap.proj γ : (Fin d → ℝ) →ₗ[ℝ] ℝ)

theorem mem_diagonal {β γ : Fin d} {c : ℝ} {x : Fin d → ℝ} :
    x ∈ diagonal β γ c ↔ x β = c * x γ := by
  simp only [diagonal, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, sub_eq_zero]

theorem diagonal_ne_top {β γ : Fin d} (hβγ : β ≠ γ) (c : ℝ) : diagonal β γ c ≠ ⊤ := by
  classical
  intro h
  have : (fun j : Fin d => if j = β then (1 : ℝ) else 0) ∈ diagonal β γ c := h ▸ Submodule.mem_top
  rw [mem_diagonal] at this
  simp [hβγ.symm] at this

theorem volume_diagonal {β γ : Fin d} (hβγ : β ≠ γ) (c : ℝ) :
    volume {x : Fin d → ℝ | x β = c * x γ} = 0 := by
  have h := Measure.addHaar_submodule (volume : Measure (Fin d → ℝ)) (diagonal β γ c)
    (diagonal_ne_top hβγ c)
  exact measure_mono_null (fun x hx => mem_diagonal.2 hx) h

/-- **Two wedges meet on the null diagonals.** -/
theorem volume_wedge_inter {β γ : Fin d} (hβγ : β ≠ γ) : volume (wedge β ∩ wedge γ) = 0 := by
  refine measure_mono_null (fun x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ?_)
    (measure_union_null (volume_diagonal hβγ 1) (volume_diagonal hβγ (-1)))
  have habs : |x β| = |x γ| := le_antisymm (h2 β) (h1 γ)
  rcases abs_eq_abs.1 habs with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-! ### The cover of box charts and its assembly -/

include hd in
/-- The box chart of pivot `β` on the cube. -/
noncomputable def chart (β : Fin d) : ResolutionChart d :=
  IsMonomialChart.boxChart (isMonomialChart hd β) one_pos (ball_subset β)

include hd in
/-- The cover of the `d` box charts. -/
noncomputable def R : ResolutionCover d (Fin d) := ⟨chart hd⟩

include hd in
/-- The box packages. -/
noncomputable def Ps :
    ∀ β, ProductMonomialChartVar (ResolutionCover.ofChart ((R hd).chart β)) () K :=
  fun β => IsMonomialChart.boxPackage (isMonomialChart hd β) one_pos (ball_subset β)

theorem R_image (β : Fin d) : (R hd).image β = wedge β := by
  change φ β '' productBox (expo β) 0 1 = wedge β
  rw [← cube_eq_productBox, image_eq]

theorem iUnion_image_eq [NeZero d] : ⋃ β, (R hd).image β = cube d := by
  rw [show (fun β => (R hd).image β) = wedge from funext (R_image hd)]
  exact iUnion_wedge

theorem aeDisjointImages : (R hd).AEDisjointImages := fun β γ hβγ => by
  rw [R_image, R_image]
  exact volume_wedge_inter hβγ

theorem Ps_isActive (β : Fin d) : (Ps hd β).IsActive :=
  IsMonomialChart.boxPackage_isActive _ _ _ (by rw [monomialEval_expo]; simp)

theorem Ps_b (β : Fin d) : (Ps hd β).b = 1 := rfl

theorem Ps_W (β : Fin d) : (Ps hd β).W = restrictNhd (expo β) (divisorSet (expo β) 0) univ := rfl

theorem Ps_r (β : Fin d) (x : Fin d → ℝ) : (Ps hd β).r x = 1 := rfl

theorem hne [NeZero d] : ((R hd).activeCharts (Ps hd)).Nonempty :=
  ⟨0, ((R hd).mem_activeCharts (Ps hd)).2 (Ps_isActive hd 0)⟩

theorem ratio_eq (β : Fin d) : (Ps hd β).ratio β = d / 2 := by
  have h := boxPs_ratio (isMonomialChart hd β) one_pos (ball_subset β)
    (j := β) (by rw [divisorSet_zero]; exact Finset.mem_singleton_self β)
  change (Ps hd β).ratio β = _ at h
  rw [h]
  simp only [jexp, expo, Finsupp.single_eq_same]
  rw [Nat.cast_sub hd.le, Nat.cast_one, sub_add_cancel]
  norm_num

theorem Ps_e_support (β : Fin d) : (Ps hd β).e.support = {β} := by
  rw [show (Ps hd β).e.support = divisorSet (expo β) 0 from
    IsMonomialChart.boxPackage_e_support _ _ _, divisorSet_zero]

theorem coverLamV_eq (β : Fin d) (hact) :
    (ResolutionCover.ofChart ((R hd).chart β)).coverLamV (fun _ => Ps hd β) hact = d / 2 := by
  unfold ResolutionCover.coverLamV
  have hmem : β ∈ (Ps hd β).e.support := by
    rw [Ps_e_support]
    exact Finset.mem_singleton_self β
  refine le_antisymm ((Finset.inf'_le _
    ((ResolutionCover.ofChart _).mem_activeCoordsV (fun _ => Ps hd β) hmem)).trans_eq
      (ratio_eq hd β)) (Finset.le_inf' _ _ fun x hx => ?_)
  obtain ⟨i, j⟩ := x
  have hj : j = β := by
    have := (Finset.mem_sigma.1 hx).2
    rwa [Ps_e_support, Finset.mem_singleton] at this
  subst hj
  exact (ratio_eq hd j).ge

theorem coverDegV_eq (β : Fin d) (hact) :
    (ResolutionCover.ofChart ((R hd).chart β)).coverDegV (fun _ => Ps hd β) hact = 0 := by
  unfold ResolutionCover.coverDegV
  rw [coverLamV_eq]
  have hmem : β ∈ (Ps hd β).e.support := by
    rw [Ps_e_support]
    exact Finset.mem_singleton_self β
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Ps hd β).e.support,
      (Ps hd β).ratio j = d / 2) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => ⟨β, hmem, ratio_eq hd β⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hall : ((Ps hd β).e.support.filter fun j => (Ps hd β).ratio j = d / 2) = {β} := by
    rw [Ps_e_support]
    exact Finset.filter_true_of_mem fun j hj => by
      rw [Finset.mem_singleton] at hj
      rw [hj]
      exact ratio_eq hd β
  rw [hall, Finset.card_singleton]

theorem chartLam'_eq (β : Fin d) : (R hd).chartLam' (Ps hd) β = d / 2 := by
  rw [(R hd).chartLam'_of_active (Ps hd) (Ps_isActive hd β)]
  exact coverLamV_eq hd β _

theorem chartDeg'_eq (β : Fin d) : (R hd).chartDeg' (Ps hd) β = 0 := by
  rw [(R hd).chartDeg'_of_active (Ps hd) (Ps_isActive hd β)]
  exact coverDegV_eq hd β _

theorem partitionLam'_eq [NeZero d] : (R hd).partitionLam' (Ps hd) (hne hd) = d / 2 := by
  unfold ResolutionCover.partitionLam' extremalExponent
  refine le_antisymm ((Finset.inf'_le _ (((R hd).mem_activeCharts (Ps hd)).2
    (Ps_isActive hd 0))).trans_eq (chartLam'_eq hd 0)) (Finset.le_inf' _ _ fun i _ =>
      (chartLam'_eq hd i).ge)

theorem partitionDeg'_eq [NeZero d] : (R hd).partitionDeg' (Ps hd) (hne hd) = 0 := by
  unfold ResolutionCover.partitionDeg' extremalDegree
  exact le_antisymm (Finset.sup'_le _ _ fun i _ => (chartDeg'_eq hd i).le) (Nat.zero_le _)

theorem hεb : ∀ β, (1 : ℝ) ≤ (Ps hd β).b := fun _ => le_rfl

/-! ### The assembled leading term of the cube integral -/

variable [NeZero d] {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFc : Continuous F)
  (hpc : Continuous p.w)

omit [NeZero d] in
include hd hFc in
theorem hFcR : ∀ β, ContinuousOn (fun y => F (((R hd).chart β).φ y)) (Ps hd β).W := fun β =>
  (hFc.comp (continuous_φ β)).continuousOn

omit [NeZero d] in
include hd hpc in
theorem hpcR : ∀ β, ContinuousOn (fun y => p.w (((R hd).chart β).φ y)) (Ps hd β).W := fun β =>
  (hpc.comp (continuous_φ β)).continuousOn

include hd hFc hpc in
/-- **The assembled coefficient** of the cube integral: the sum of the `d` tied whole-box source
coefficients. -/
noncomputable def coeff : ℝ :=
  (R hd).aeDisjointCoeff (Ps hd) K_nonneg one_pos (hεb hd) (hpcR hd hpc) (hFcR hd hFc)
    hFc.measurable continuous_K.measurable (hne hd)

include hd hFc hpc in
theorem hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ β, (R hd).image β)) := by
  rw [iUnion_image_eq]
  exact (hFc.mul hpc).continuousOn.integrableOn_compact isCompact_cube

omit [NeZero d] in
theorem φ_mem_cube (β : Fin d) {y : Fin d → ℝ} (hy : y ∈ cube d) : φ β y ∈ cube d :=
  wedge_subset_cube β (image_eq β ▸ mem_image_of_mem (φ β) hy)

include hd hFc hpc in
/-- **Positivity of the assembled coefficient** for `F`, `p` positive on the cube: the tied chart's
whole-box coefficient (CCLXXXI) is positive, at any cutoff (CCLXXXII). -/
theorem coeff_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hpos : ∀ x ∈ cube d, 0 < F x ∧ 0 < p.w x) : 0 < coeff hd hFc hpc := by
  obtain ⟨i₀, hi₀⟩ := (R hd).exists_mem_tiedCharts' (Ps hd) (hne hd)
  refine (R hd).aeDisjointCoeff_pos_of_tied (Ps hd) K_nonneg one_pos (hεb hd) _ _ hFc.measurable
    continuous_K.measurable _ hF0 hp0 (fun k x => by rw [Ps_r]; exact zero_le_one) i₀ hi₀ ?_
  unfold ResolutionCover.sourceChartCoeff'
  rw [dif_pos (Ps_isActive hd i₀), (R hd).chartLam'_of_active _ (Ps_isActive hd i₀),
    (R hd).chartDeg'_of_active _ (Ps_isActive hd i₀)]
  have hact := ((ResolutionCover.ofChart ((R hd).chart i₀)).activeCoordsV_ofChart_nonempty_iff
    (fun _ => Ps hd i₀) ()).2 (Ps_isActive hd i₀)
  have hcut := (Ps hd i₀).sourceCoeff_eq_of_cutoff K_nonneg one_pos (half_pos one_pos)
    (show (1 : ℝ) ≤ (Ps hd i₀).b from le_rfl)
    (show (1 : ℝ) / 2 ≤ (Ps hd i₀).b from by rw [Ps_b]; norm_num) (hpcR hd hpc i₀)
    (hFc.measurable.comp ((R hd).chart i₀).measurable_Φ)
    (ResolutionCover.continuousOn_pullback_Φ ((R hd).chart i₀) (hFcR hd hFc i₀)
      (Ps hd i₀).dom_subset) continuous_K.measurable
    ((ResolutionCover.ofChart ((R hd).chart i₀)).coverLamV (fun _ => Ps hd i₀) hact)
    ((ResolutionCover.ofChart ((R hd).chart i₀)).coverDegV (fun _ => Ps hd i₀) hact)
    (fun I hI hne =>
      (ResolutionCover.ofChart _).coverLamV_le_pieceLam (fun _ => Ps hd i₀) hact () I hI hne)
    (fun I hI hne hl =>
      (ResolutionCover.ofChart _).pieceMult_le_coverDegV (fun _ => Ps hd i₀) hact () I hI hne hl)
  rw [hcut]
  have hGp : ∀ y ∈ Metric.closedBall (0 : Fin d → ℝ) 1,
      0 < F (((R hd).chart i₀).Φ y) ∧ 0 < p.w (φ i₀ y) := fun y hy => by
    have hyc : y ∈ cube d := cube_eq_closedBall ▸ hy
    have hyd : y ∈ ((R hd).chart i₀).dom := by
      show y ∈ productBox (expo i₀) 0 1
      rw [← cube_eq_productBox]
      exact hyc
    rw [((R hd).chart i₀).Φ_eqOn hyd]
    exact hpos _ (φ_mem_cube i₀ hyc)
  exact (boxSourceIntegral_isEquivalent (isMonomialChart hd i₀) one_pos (ball_subset i₀) K_nonneg
    continuous_K.measurable (by rw [monomialEval_expo]; simp)
    (hpc.comp (continuous_φ i₀)).continuousOn
    (hFc.measurable.comp ((R hd).chart i₀).measurable_Φ)
    (ResolutionCover.continuousOn_pullback_Φ ((R hd).chart i₀) (hFcR hd hFc i₀)
      (Ps hd i₀).dom_subset) (fun _ => hF0 _) hp0 hGp).1

include hd hFc hpc in
/-- ★★ **One blow-up suffices**: for `F`, `p` continuous, nonnegative and positive on the unit cube,
`∫_{[−1,1]^d} F p e^{−N ∑ x_i²} ~ c N^{−d/2}` with `c > 0` the sum of the `d` whole-box source
coefficients of the blow-up charts — the certificate derived from the chart data. -/
theorem cubeIntegral_isEquivalent (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hpos : ∀ x ∈ cube d, 0 < F x ∧ 0 < p.w x) :
    0 < coeff hd hFc hpc ∧
      targetIntegral (cube d) F K p ~[atTop] fun N => coeff hd hFc hpc * N ^ (-(d / 2 : ℝ)) := by
  refine ⟨coeff_pos hd hFc hpc hF0 hp0 hpos, ?_⟩
  have h := (R hd).targetIntegral_isEquivalent_of_aeDisjoint_of_pos (Ps hd) K_nonneg one_pos
    (hεb hd) (hpcR hd hpc) (hFcR hd hFc) hFc.measurable continuous_K.measurable (hne hd)
    (aeDisjointImages hd) (Rg := cube d)
    (by simp only [iUnion_image_eq, sdiff_self, measure_empty])
    (by simp only [iUnion_image_eq, sdiff_self, measure_empty]) (hF hd hFc hpc)
    (coeff_pos hd hFc hpc hF0 hp0 hpos)
  rw [partitionLam'_eq, partitionDeg'_eq] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  unfold coeff
  simp [powLogScale]

end BlowUpCube

end Grammar
