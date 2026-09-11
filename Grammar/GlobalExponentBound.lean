/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartLeadingTerm
import Grammar.ExpGapLocalisation

/-!
# The global exponent from local leading terms, conditional on a local cover (Astra #70, route D)

For a nonnegative observable the exponent pair of a region integral is determined by finitely many
local regions with identified leading terms, with **no ownership and no intersection expansions**:
if the regions `Ω_i ⊆ R` cover `R` up to a set on which the phase is a.e. at least `δ₀ > 0`, and
each local integral satisfies `∫_{Ω_i} F e^{−NK} ~ c_i N^{−λ_i}(log N)^{m_i−1}` with `c_i > 0`, then
`∫_R F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})` with `λ_* = min_i λ_i` and `m_* = max{m_i : λ_i = λ_*}`
(`isTheta_of_local_leading_terms`): the lower bound is one piece, the upper bound is the sum of
the pieces plus the exponentially small tail. In logarithmic form the free energy is
`−log ∫_R F e^{−NK} = λ_* log N − (m_*−1) log log N + O(1)` (`freeEnergy_asymptotic`).

The hypotheses are exactly what `IsMonomialChart.local_leading_term` supplies for one region at a
divisor point of a hironaka chart (`c_i = localLeadingCoeff`, `λ_i = C.lam`, `m_i = C.mult`); the
**finite local cover of `R ∩ {K < δ₀}` by such regions is a hypothesis here, not a theorem**: the
local regions of CCIV are the charts' own strip boxes, not ambient neighbourhoods, and the
resolution readout provides an a.e. cover by charts but no cover by boxes. Non-claims: no
expansion beyond the leading order, no identification of the coefficient of the region integral.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

theorem regionIntegrand_nonneg {X : Type*} {R : Set X} {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x)
    {N : ℝ} {x : X} (hx : x ∈ R) : 0 ≤ F x * Real.exp (-N * K x) :=
  mul_nonneg (hF0 x hx) (Real.exp_pos _).le

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The region integral `∫_R F e^{−NK}`. -/
noncomputable def regionIntegral (μ : Measure X) (R : Set X) (F K : X → ℝ) (N : ℝ) : ℝ :=
  ∫ x in R, F x * Real.exp (-N * K x) ∂μ

variable {R : Set X} (hR : MeasurableSet R) {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x)
  (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x) (hKm : Measurable K)

include hFint hKm hK0 hR in
theorem integrableOn_regionIntegrand {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun x => F x * Real.exp (-N * K x)) R μ := by
  have h : Integrable (fun x => Real.exp (-N * K x) * F x) (μ.restrict R) := by
    refine Integrable.bdd_mul (c := 1) hFint
      (Real.measurable_exp.comp (hKm.const_mul (-N))).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem hR fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [hK0 x hx]
  exact h.congr (Eventually.of_forall fun x => mul_comm _ _)

include hR hF0 hFint hK0 hKm in
/-- The region integral dominates the integral over any measurable subregion. -/
theorem setIntegral_le_regionIntegral {Ω : Set X} (hΩR : Ω ⊆ R) {N : ℝ} (hN : 0 ≤ N) :
    ∫ x in Ω, F x * Real.exp (-N * K x) ∂μ ≤ regionIntegral μ R F K N :=
  setIntegral_mono_set (integrableOn_regionIntegrand hR hFint hK0 hKm hN)
    (ae_restrict_of_forall_mem hR fun _ hx => regionIntegrand_nonneg hF0 hx)
    (Eventually.of_forall hΩR)

include hR hF0 hFint hK0 hKm in
/-- **The cover bound**: the region integral is at most the sum over the pieces plus the
exponentially small tail `e^{−Nδ₀} ∫_R F`. -/
theorem regionIntegral_le_sum_add_tail {ι : Type*} [Fintype ι] (Ω : ι → Set X)
    (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩR : ∀ i, Ω i ⊆ R) {δ₀ : ℝ}
    (hgap : ∀ᵐ x ∂μ, x ∈ R → x ∉ ⋃ i, Ω i → δ₀ ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    regionIntegral μ R F K N ≤
      (∑ i, ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) +
        Real.exp (-N * δ₀) * ∫ x in R, F x ∂μ := by
  classical
  set f : X → ℝ := fun x => F x * Real.exp (-N * K x) with hf
  set U := ⋃ i, Ω i with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion hΩm
  have hUR : U ⊆ R := iUnion_subset hΩR
  have hfR : IntegrableOn f R μ := integrableOn_regionIntegrand hR hFint hK0 hKm hN
  have hsplit : regionIntegral μ R F K N = (∫ x in R ∩ U, f x ∂μ) + ∫ x in R \ U, f x ∂μ :=
    (integral_inter_add_sdiff hUm hfR).symm
  rw [hsplit, inter_eq_right.2 hUR]
  refine add_le_add ?_ ?_
  · -- the union is bounded by the sum of the pieces
    have hfU : IntegrableOn f U μ := hfR.mono_set hUR
    have hind : ∀ x, U.indicator f x ≤ ∑ i, (Ω i).indicator f x := by
      intro x
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        have hnn : ∀ j, 0 ≤ (Ω j).indicator f x := fun j =>
          indicator_nonneg (fun y hy => regionIntegrand_nonneg hF0 (hΩR j hy)) x
        calc f x = (Ω i).indicator f x := (indicator_of_mem hi f).symm
          _ ≤ ∑ j, (Ω j).indicator f x :=
              Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
      · rw [indicator_of_notMem hx]
        exact Finset.sum_nonneg fun j _ =>
          indicator_nonneg (fun y hy => regionIntegrand_nonneg hF0 (hΩR j hy)) x
    rw [← integral_indicator hUm]
    calc ∫ x, U.indicator f x ∂μ ≤ ∫ x, ∑ i, (Ω i).indicator f x ∂μ := by
          refine integral_mono (hfU.integrable_indicator hUm) ?_ hind
          exact integrable_finsetSum _ fun i _ =>
            (hfR.mono_set (hΩR i)).integrable_indicator (hΩm i)
      _ = ∑ i, ∫ x in Ω i, f x ∂μ := by
          rw [integral_finsetSum _ fun i _ => (hfR.mono_set (hΩR i)).integrable_indicator (hΩm i)]
          exact Finset.sum_congr rfl fun i _ => integral_indicator (hΩm i)
  · -- the tail is exponentially small
    have hRU : MeasurableSet (R \ U) := hR.diff hUm
    have hsub : R \ U ⊆ R := sdiff_subset
    calc ∫ x in R \ U, f x ∂μ ≤ ∫ x in R \ U, F x * Real.exp (-N * δ₀) ∂μ := by
          refine setIntegral_mono_ae_restrict (hfR.mono_set hsub)
            ((hFint.mono_set hsub).mul_const _) ?_
          filter_upwards [ae_restrict_mem hRU, ae_restrict_of_ae hgap] with x hx hgx
          refine mul_le_mul_of_nonneg_left ?_ (hF0 x hx.1)
          rw [Real.exp_le_exp]
          have := hgx hx.1 hx.2
          nlinarith
      _ = Real.exp (-N * δ₀) * ∫ x in R \ U, F x ∂μ := by
          rw [integral_mul_const, mul_comm]
      _ ≤ Real.exp (-N * δ₀) * ∫ x in R, F x ∂μ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact setIntegral_mono_set hFint (ae_restrict_of_forall_mem hR hF0)
            (Eventually.of_forall hsub)

end Abstract

/-! ### Power–log comparisons -/

/-- The power–log scale `N^{−λ}(log N)^{r}`. -/
noncomputable def powLogScale (l : ℝ) (r : ℕ) (N : ℝ) : ℝ := N ^ (-l) * Real.log N ^ r

theorem powLogScale_pos (l : ℝ) (r : ℕ) {N : ℝ} (hN : 1 < N) : 0 < powLogScale l r N :=
  mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN) _)

/-- `N^{−λ}` is dominated by every scale `N^{−λ}(log N)^r`. -/
theorem rpow_neg_isBigO_powLogScale (l : ℝ) (r : ℕ) :
    (fun N : ℝ => N ^ (-l)) =O[atTop] powLogScale l r := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hN
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN0 _),
    powLogScale, abs_of_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos (by linarith) _))]
  exact le_mul_of_one_le_right (Real.rpow_pos_of_pos hN0 _).le (one_le_pow₀ hlog)

/-- A scale with a strictly larger exponent is negligible. -/
theorem powLogScale_isLittleO_of_lt {l l' : ℝ} (h : l < l') (r r' : ℕ) :
    powLogScale l' r' =o[atTop] powLogScale l r := by
  have h1 : (fun N : ℝ => Real.log N ^ (r' : ℝ)) =o[atTop] fun N : ℝ => N ^ (l' - l) :=
    isLittleO_log_rpow_rpow_atTop (r' : ℝ) (by linarith)
  have h2 : (fun N : ℝ => N ^ (-l') * Real.log N ^ (r' : ℝ)) =o[atTop]
      fun N : ℝ => N ^ (-l') * N ^ (l' - l) :=
    (isBigO_refl (fun N : ℝ => N ^ (-l')) atTop).mul_isLittleO h1
  have h3 : (fun N : ℝ => N ^ (-l') * N ^ (l' - l)) =ᶠ[atTop] fun N : ℝ => N ^ (-l) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have h4 : powLogScale l' r' =ᶠ[atTop] fun N : ℝ => N ^ (-l') * Real.log N ^ (r' : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    rw [powLogScale, Real.rpow_natCast]
  exact (((h2.congr' h4.symm h3)).trans_isBigO (rpow_neg_isBigO_powLogScale l r))

/-- A scale with the same exponent and a lower log degree is dominated. -/
theorem powLogScale_isBigO_of_le (l : ℝ) {r r' : ℕ} (h : r' ≤ r) :
    powLogScale l r' =O[atTop] powLogScale l r := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hN
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.exp_one_gt_d9; linarith) hN
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (powLogScale_pos _ _ hN1),
    abs_of_pos (powLogScale_pos _ _ hN1)]
  unfold powLogScale
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog h) (Real.rpow_pos_of_pos hN0 _).le

/-- `e^{−δ₀N}` is negligible against every scale. -/
theorem exp_neg_isLittleO_powLogScale {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (l : ℝ) (r : ℕ) :
    (fun N : ℝ => Real.exp (-N * δ₀)) =o[atTop] powLogScale l r := by
  have h1 : (fun N : ℝ => Real.exp (-δ₀ * N)) =o[atTop] fun N : ℝ => N ^ (-l) :=
    isLittleO_exp_neg_mul_rpow_atTop hδ₀ (-l)
  have h2 : (fun N : ℝ => Real.exp (-N * δ₀)) = fun N : ℝ => Real.exp (-δ₀ * N) := by
    funext N
    ring_nf
  rw [h2]
  exact h1.trans_isBigO (rpow_neg_isBigO_powLogScale l r)

/-! ### The global exponent -/

section Global

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {R : Set X} (hR : MeasurableSet R)
  {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x) (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x)
  (hKm : Measurable K) {ι : Type*} (Ω : ι → Set X)
  (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩR : ∀ i, Ω i ⊆ R) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
  (hgap : ∀ᵐ x ∂μ, x ∈ R → x ∉ ⋃ i, Ω i → δ₀ ≤ K x) (c lam : ι → ℝ) (m : ι → ℕ)
  (hc : ∀ i, 0 < c i)
  (hI : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) ~[atTop]
    fun N => c i * powLogScale (lam i) (m i - 1) N)

/-- The leading piece: minimal exponent, then maximal log degree among the minimisers. -/
theorem exists_leading_piece [Finite ι] [Nonempty ι] : ∃ i₀ : ι, (∀ i, lam i₀ ≤ lam i) ∧
    ∀ i, lam i = lam i₀ → m i ≤ m i₀ := by
  classical
  cases nonempty_fintype ι
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  obtain ⟨i₀, hi₀S, hi₀⟩ := Finset.exists_max_image (Finset.univ.filter fun i => lam i = lam i₁) m
    ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hl₀ : lam i₀ = lam i₁ := (Finset.mem_filter.1 hi₀S).2
  refine ⟨i₀, fun i => hl₀ ▸ hi₁ i (Finset.mem_univ i), fun i hi => ?_⟩
  exact hi₀ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi.trans hl₀⟩)

include hR hF0 hFint hK0 hKm hΩm hΩR hc hI in
/-- **Lower bound**: the leading scale is dominated by the region integral. -/
theorem powLogScale_isBigO_regionIntegral (i₀ : ι) :
    powLogScale (lam i₀) (m i₀ - 1) =O[atTop] regionIntegral μ R F K := by
  have h1 : (fun N => c i₀ * powLogScale (lam i₀) (m i₀ - 1) N) =O[atTop]
      fun N : ℝ => ∫ x in Ω i₀, F x * Real.exp (-N * K x) ∂μ := (hI i₀).isBigO_symm
  have h2 : powLogScale (lam i₀) (m i₀ - 1) =O[atTop]
      fun N : ℝ => ∫ x in Ω i₀, F x * Real.exp (-N * K x) ∂μ :=
    (isBigO_const_mul_left_iff (hc i₀).ne').1 h1
  refine h2.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have hpos : 0 ≤ ∫ x in Ω i₀, F x * Real.exp (-N * K x) ∂μ :=
    setIntegral_nonneg (hΩm i₀) fun x hx => regionIntegrand_nonneg hF0 (hΩR i₀ hx)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (hpos.trans (setIntegral_le_regionIntegral hR hF0 hFint hK0 hKm (hΩR i₀) hN))]
  exact setIntegral_le_regionIntegral hR hF0 hFint hK0 hKm (hΩR i₀) hN

include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hI in
/-- **Upper bound**: the region integral is dominated by the leading scale. -/
theorem regionIntegral_isBigO_powLogScale [Finite ι] {i₀ : ι} (hmin : ∀ i, lam i₀ ≤ lam i)
    (hmax : ∀ i, lam i = lam i₀ → m i ≤ m i₀) :
    regionIntegral μ R F K =O[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  classical
  cases nonempty_fintype ι
  set g := powLogScale (lam i₀) (m i₀ - 1) with hg
  -- every piece is `O(g)`
  have hpiece : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) =O[atTop] g := by
    intro i
    refine (hI i).isBigO.trans ((IsBigO.const_mul_left ?_ _))
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

include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hc hI in
/-- **The global exponent from local leading terms** (conditional on the local cover): the region
integral is `Θ(N^{−λ_*}(log N)^{m_*−1})` with `λ_* = min_i λ_i` and `m_* = max{m_i : λ_i = λ_*}`. -/
theorem isTheta_of_local_leading_terms [Finite ι] [Nonempty ι] :
    ∃ i₀ : ι, (∀ i, lam i₀ ≤ lam i) ∧ (∀ i, lam i = lam i₀ → m i ≤ m i₀) ∧
      regionIntegral μ R F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  obtain ⟨i₀, hmin, hmax⟩ := exists_leading_piece lam m
  exact ⟨i₀, hmin, hmax,
    ⟨regionIntegral_isBigO_powLogScale hR hF0 hFint hK0 hKm Ω hΩm hΩR hδ₀ hgap c lam m hI
      hmin hmax,
    powLogScale_isBigO_regionIntegral hR hF0 hFint hK0 hKm Ω hΩm hΩR c lam m hc hI i₀⟩⟩

end Global

/-! ### The free energy form -/

/-- A `Θ`-comparison of eventually positive functions bounds the difference of logarithms. -/
theorem log_sub_log_isBigO_one {Z g : ℝ → ℝ} (hZ : ∀ᶠ N in atTop, 0 < Z N)
    (hg : ∀ᶠ N in atTop, 0 < g N) (h : Z =Θ[atTop] g) :
    (fun N => Real.log (Z N) - Real.log (g N)) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  obtain ⟨c₂, hc₂⟩ := isBigO_iff.1 h.1
  obtain ⟨c₁, hc₁⟩ := isBigO_iff.1 h.2
  refine IsBigO.of_bound (|Real.log c₂| + |Real.log c₁|) ?_
  filter_upwards [hZ, hg, hc₂, hc₁] with N hZN hgN h2 h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hZN] at h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgN] at h1
  rw [abs_of_pos hgN] at h2
  rw [abs_of_pos hZN] at h1
  have hc₂pos : 0 < c₂ := by
    by_contra hcon
    have : c₂ * g N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hgN.le
    linarith
  have hc₁pos : 0 < c₁ := by
    by_contra hcon
    have : c₁ * Z N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hZN.le
    linarith
  rw [Real.norm_eq_abs, norm_one, mul_one, Real.log_div hZN.ne' hgN.ne' |>.symm]
  have hup : Real.log (Z N / g N) ≤ Real.log c₂ := by
    rw [Real.log_le_log_iff (div_pos hZN hgN) hc₂pos, div_le_iff₀ hgN]
    exact h2
  have hlow : -Real.log c₁ ≤ Real.log (Z N / g N) := by
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.2 hc₁pos) (div_pos hZN hgN),
      inv_le_iff_one_le_mul₀ hc₁pos, div_mul_eq_mul_div, le_div_iff₀ hgN, one_mul, mul_comm]
    exact h1
  rw [abs_le]
  constructor
  · have := le_abs_self (Real.log c₁)
    linarith [abs_nonneg (Real.log c₂)]
  · have := le_abs_self (Real.log c₂)
    linarith [abs_nonneg (Real.log c₁)]

/-- The logarithm of the power–log scale. -/
theorem log_powLogScale (l : ℝ) (r : ℕ) {N : ℝ} (hN : 1 < N) :
    Real.log (powLogScale l r N) = -l * Real.log N + r * Real.log (Real.log N) := by
  have hN0 : 0 < N := by linarith
  unfold powLogScale
  rw [Real.log_mul (Real.rpow_pos_of_pos hN0 _).ne' (pow_pos (Real.log_pos hN) _).ne',
    Real.log_rpow hN0, Real.log_pow]

/-- **The free energy asymptotic** `−log Z(N) = λ log N − (m−1) log log N + O(1)` from the
`Θ`-comparison with the power–log scale. -/
theorem freeEnergy_asymptotic {Z : ℝ → ℝ} (hZ : ∀ᶠ N in atTop, 0 < Z N) {l : ℝ} {r : ℕ}
    (h : Z =Θ[atTop] powLogScale l r) :
    (fun N => -Real.log (Z N) - (l * Real.log N - r * Real.log (Real.log N))) =O[atTop]
      fun _ : ℝ => (1 : ℝ) := by
  have hg : ∀ᶠ N in atTop, 0 < powLogScale l r N := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    exact powLogScale_pos l r hN
  have h1 := log_sub_log_isBigO_one hZ hg h
  refine (h1.neg_left).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  rw [log_powLogScale l r hN]
  ring

end Grammar
