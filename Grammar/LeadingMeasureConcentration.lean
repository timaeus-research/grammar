/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GlobalCompactTheta

/-!
# Concentration of leading measures on the zero set; bounded open regions (CCXCVI)

Consult #90's two recommended additions to the global programme.

* **Concentration.** A finite leading measure of a finite-volume region `W` (CCXC) is concentrated
  on the zero set `closure W ∩ {K = 0}` whenever `K ≥ 0` is continuous on `closure W`
  (`HasLeadingMeasure.compl_zeroSet_eq_zero`): a bounded continuous test vanishing near the zero
  set has an exponentially small Laplace integral, hence zero coefficient
  (`HasLeadingMeasure.integral_eq_zero_of_gap`), and Urysohn functions on a compact exhaustion of
  the complement of the zero set force the measure of that complement to vanish. This replaces the
  case-by-case geometric support arguments (the cube of CCXCV) by a structural fact.
* **Bounded open regions.** The unconditional exponent theorem of CCXCIV transfers to a bounded
  OPEN region whose zeros avoid the boundary: `∫_W F e^{−tK} = Θ(t^{−λ*} (log t)^{m*−1})`
  (`exponent_of_bounded_open`), the boundary contribution being exponentially small by the
  positive gap of `K` on the compact set `closure W \ W`; no volume condition on the boundary.
-/

open MeasureTheory Set Filter Topology Asymptotics BoundedContinuousFunction

namespace Grammar

variable {d : ℕ} {W : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ} {lam : ℝ} {q : ℕ}
  {σ : Measure (Fin d → ℝ)}

/-- An amplitude vanishing off `{K ≥ κ}` has an exponentially small Laplace integral. -/
theorem hasExponentialBound_globalLaplace_of_gap (hW : volume W ≠ ⊤) {a : (Fin d → ℝ) → ℝ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |a x| ≤ M) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ x ∈ W, a x ≠ 0 → κ ≤ K x) : HasExponentialBound (globalLaplace W K a) := by
  refine ⟨M * volume.real W, mul_nonneg hM0 measureReal_nonneg, κ, hκ, fun t ht => ?_⟩
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := W)
    (f := fun x => a x * Real.exp (-t * K x)) hW.lt_top (C := M * Real.exp (-κ * t))
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      by_cases ha : a x = 0
      · rw [ha, abs_zero, zero_mul]
        positivity
      · exact mul_le_mul (hM x) (Real.exp_le_exp.2 (by nlinarith [hgap x hx ha]))
          (Real.exp_pos _).le hM0)
  rw [Real.norm_eq_abs] at h
  unfold globalLaplace
  calc |∫ x in W, a x * Real.exp (-t * K x)| ≤ M * Real.exp (-κ * t) * volume.real W := h
    _ = M * volume.real W * Real.exp (-κ * t) := by ring

/-- **Tests supported in a phase gap have zero coefficient.** -/
theorem HasLeadingMeasure.integral_eq_zero_of_gap (hW : volume W ≠ ⊤)
    (h : HasLeadingMeasure W K lam q σ) (a : (Fin d → ℝ) →ᵇ ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ x ∈ W, a x ≠ 0 → κ ≤ K x) : ∫ w, a w ∂σ = 0 := by
  have hexp := hasExponentialBound_globalLaplace_of_gap (K := K) hW (a := a) (norm_nonneg a)
    (fun x => by rw [← Real.norm_eq_abs]; exact a.norm_coe_le_norm x) hκ hgap
  have h0 : HasLeadingTerm (globalLaplace W K a) 0 lam q :=
    (hexp.isLittleO_powLogScale lam q).tendsto_div_nhds_zero
  exact (h a).coeff_unique h0

/-- ★★ **Concentration**: a finite leading measure of a finite-volume region is concentrated on the
zero set `closure W ∩ {K = 0}` (`K ≥ 0` continuous on the closure). -/
theorem HasLeadingMeasure.compl_zeroSet_eq_zero [IsFiniteMeasure σ] (hW : volume W ≠ ⊤)
    (hK0 : ∀ x, 0 ≤ K x) (hKc : ContinuousOn K (closure W)) (h : HasLeadingMeasure W K lam q σ) :
    σ (closure W ∩ K ⁻¹' {0})ᶜ = 0 := by
  set Z : Set (Fin d → ℝ) := closure W ∩ K ⁻¹' {0} with hZdef
  have hZc : IsClosed Z := hKc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  -- the compact exhaustion of the complement
  have hF : ∀ n : ℕ, σ (Metric.closedBall (0 : Fin d → ℝ) n \
      Metric.thickening (1 / ((n : ℝ) + 1)) Z) = 0 := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set F : Set (Fin d → ℝ) := Metric.closedBall 0 n \ Metric.thickening δ Z with hFdef
    have hFc : IsCompact F := (isCompact_closedBall _ _).diff Metric.isOpen_thickening
    set T : Set (Fin d → ℝ) := Metric.cthickening (δ / 2) Z with hTdef
    have hdisj : Disjoint F T := by
      rw [Set.disjoint_left]
      intro x hx hxT
      exact hx.2 (Metric.cthickening_subset_thickening' hδpos (half_lt_self hδpos) Z hxT)
    obtain ⟨f, hf1, hf0, hfsupp, hf01⟩ :=
      exists_continuous_one_zero_of_isCompact hFc Metric.isClosed_cthickening hdisj
    let a : (Fin d → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f f.continuous 1
      fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]; exact (hf01 x).2
    have ha : ∀ x, a x = f x := fun _ => rfl
    -- the gap on the support of `f` inside the closure
    have hC : IsCompact (tsupport f ∩ closure W) := hfsupp.inter_right isClosed_closure
    have hCpos : ∀ x ∈ tsupport f ∩ closure W, 0 < K x := by
      intro x hx
      rcases (hK0 x).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hxZ : x ∈ Z := ⟨hx.2, heq.symm⟩
        have hnhds : Metric.thickening (δ / 2) Z ∈ 𝓝 x :=
          Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening (half_pos hδpos) Z hxZ)
        have hnot : x ∉ tsupport f := by
          intro hcl
          obtain ⟨y, hyT, hyf⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
          exact hyf (hf0 (Metric.thickening_subset_cthickening _ _ hyT))
        exact hnot hx.1
    obtain ⟨κ, hκ, hκle⟩ := exists_pos_le_of_isCompact hC (hKc.mono inter_subset_right) hCpos
    have hint : ∫ w, a w ∂σ = 0 :=
      h.integral_eq_zero_of_gap hW a hκ fun x hxW hax =>
        hκle x ⟨subset_tsupport _ hax, subset_closure hxW⟩
    -- `1_F ≤ a`
    have hle : (σ F).toReal ≤ ∫ w, a w ∂σ := by
      have hmono : ∫ w, F.indicator (fun _ => (1 : ℝ)) w ∂σ ≤ ∫ w, a w ∂σ := by
        refine integral_mono ((integrable_const (1 : ℝ)).indicator hFc.measurableSet)
          (a.integrable σ) fun x => ?_
        by_cases hx : x ∈ F
        · simp only [indicator_of_mem hx, ha, hf1 hx, Pi.one_apply, le_refl]
        · simp only [indicator_of_notMem hx, ha]
          exact (hf01 x).1
      rwa [integral_indicator_const _ hFc.measurableSet, smul_eq_mul, mul_one,
        measureReal_def] at hmono
    rw [hint] at hle
    have h0 : (σ F).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff _).1 h0 |>.resolve_right (measure_ne_top _ _)
  -- the exhaustion covers the complement
  have hunion : Zᶜ ⊆ ⋃ n : ℕ, Metric.closedBall (0 : Fin d → ℝ) n \
      Metric.thickening (1 / ((n : ℝ) + 1)) Z := by
    intro x hx
    have hxcl : x ∉ closure Z := by rwa [hZc.closure_eq]
    obtain ⟨ε, hε, hxε⟩ : ∃ ε > 0, x ∉ Metric.thickening ε Z := by
      by_contra hcon
      refine hxcl ((Metric.closure_eq_iInter_thickening Z).symm ▸ mem_iInter₂.2 fun ε hε => ?_)
      by_contra hx'
      exact hcon ⟨ε, hε, hx'⟩
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hε
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max n₁ n₂, ⟨?_, fun hthick => hxε ?_⟩⟩
    · rw [mem_closedBall_zero_iff]
      exact hn₂.trans (by exact_mod_cast le_max_right n₁ n₂)
    · refine Metric.thickening_mono ?_ Z hthick
      have h1 : (1 : ℝ) / ((max n₁ n₂ : ℕ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
        gcongr
        exact_mod_cast le_max_left n₁ n₂
      exact h1.trans hn₁.le
  exact measure_mono_null hunion (measure_iUnion_null hF)

/-! ### Bounded open regions -/

open Monomialize.VolumeScaling in
/-- ★★ **The exponent of the original integral over a bounded open region**: with the zeros of `K`
in `closure W` all inside `W`, `∫_W F e^{−tK} = Θ(t^{−λ*} (log t)^{m*−1})` at the extremal pair of
finitely many hironaka centred-chart pairs, the boundary contribution being exponentially small. -/
theorem exponent_of_bounded_open {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) (hWU : closure W ⊆ U) (hK : AnalyticOnNhd ℝ K U)
    (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K) {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x)
    (hbd : ∀ w ∈ closure W, K w = 0 → w ∈ W) (hnt : ∀ w ∈ W, K w = 0 → ¬ K =ᶠ[𝓝 w] 0)
    (hW0 : ∃ w ∈ W, K w = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
      (∀ p, ∃ w ∈ W, K w = 0 ∧ ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N),
        R.IsMonomial ∧ ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
          (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
      (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
      globalLaplace W K F =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
  have hWc : IsCompact (closure W) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hWb.closure
  obtain ⟨ι, hfin, hnonempty, lam, m, i₀, hdesc, hmin, hmax, hΘ⟩ :=
    exponent_of_compact hU hWc hWU hK hK0 hKm hF hFpos
      (fun w hw hKw => interior_mono subset_closure (by rw [hWo.interior_eq]; exact hbd w hw hKw))
      (fun w hw hKw => hnt w (hbd w hw hKw) hKw)
      (hW0.imp fun w hw => ⟨subset_closure hw.1, hw.2⟩)
  refine ⟨ι, hfin, hnonempty, lam, m, i₀, fun p => ?_, hmin, hmax, ?_⟩
  · obtain ⟨w, hw, hKw, rest⟩ := hdesc p
    exact ⟨w, hbd w hw hKw, hKw, rest⟩
  -- the boundary contribution is exponentially small
  have hKc : ContinuousOn K (closure W) := hK.continuousOn.mono hWU
  have hFc : ContinuousOn F (closure W) := hF.continuousOn.mono hWU
  have hbdry : IsCompact (closure W \ W) := hWc.diff hWo
  have hbpos : ∀ x ∈ closure W \ W, 0 < K x := fun x hx => by
    rcases (hK0 x (hWU hx.1)).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hbd x hx.1 heq.symm) hx.2
  have htail : HasExponentialBound fun t : ℝ =>
      ∫ x in closure W \ W, F x * Real.exp (-t * K x) :=
    hasExponentialBound_setIntegral_of_isCompact hbdry
      ((hFc.mono sdiff_subset).integrableOn_compact hbdry) (hKc.mono sdiff_subset) hbpos
  have hlittle := htail.isLittleO_powLogScale (lam i₀) (m i₀ - 1)
  have hsplit : ∀ t : ℝ, globalLaplace (closure W) K F t =
      globalLaplace W K F t + ∫ x in closure W \ W, F x * Real.exp (-t * K x) := by
    intro t
    have hint : IntegrableOn (fun x => F x * Real.exp (-t * K x)) (closure W) :=
      (hFc.mul (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul hKc))).integrableOn_compact hWc
    unfold globalLaplace
    rw [← setIntegral_union disjoint_sdiff_self_right (hWc.diff hWo).isClosed.measurableSet
      (hint.mono_set subset_closure) (hint.mono_set sdiff_subset),
      union_sdiff_cancel subset_closure]
  have hO1 : globalLaplace W K F =O[atTop] powLogScale (lam i₀) (m i₀ - 1) := by
    have heq : globalLaplace W K F = fun t => globalLaplace (closure W) K F t +
        -(∫ x in closure W \ W, F x * Real.exp (-t * K x)) := funext fun t => by
      rw [hsplit t]; ring
    rw [heq]
    exact hΘ.isBigO.add_isLittleO hlittle.neg_left
  have hO2 : powLogScale (lam i₀) (m i₀ - 1) =O[atTop] globalLaplace W K F := by
    refine hΘ.symm.isBigO.trans ?_
    have hlittle' : (fun t : ℝ => -(∫ x in closure W \ W, F x * Real.exp (-t * K x))) =o[atTop]
        globalLaplace (closure W) K F := hlittle.neg_left.trans_isBigO hΘ.symm.isBigO
    refine hlittle'.right_isBigO_add.congr_right fun t => ?_
    rw [hsplit t]; ring
  exact ⟨hO1, hO2⟩

end Grammar
