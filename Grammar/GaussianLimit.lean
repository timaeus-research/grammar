/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Almost-sure limits of real Gaussian variables are Gaussian

`hasGaussianLaw_of_tendsto_ae`: if `X n` has a Gaussian law for every `n` and `X n → Y` almost
surely, then `Y` has a Gaussian law.  Route: the characteristic functions converge pointwise
(dominated convergence); the variances are eventually bounded because `|φ_Y|` is close to `1` near
`0`; the means are eventually bounded by tightness (convergence in probability) and Chebyshev;
a convergent subsequence of the parameters identifies `φ_Y = φ_{N(m,v)}`, and characteristic
functions determine the law.  This is the closure step of the Gaussian-jet programme (§20, item 6):
derivative evaluations of a Gaussian field are limits of finite differences of its values.

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Set
open scoped ENNReal NNReal

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem norm_cexp_ofReal_mul_ofReal_mul_I (t y : ℝ) : ‖cexp ((t : ℂ) * (y : ℂ) * I)‖ = 1 := by
  rw [show (t : ℂ) * (y : ℂ) * I = ((t * y : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

omit [IsProbabilityMeasure P] in
/-- The characteristic function of the law of a real random variable, as an integral over `Ω`. -/
theorem charFun_map_real_eq_integral {Y : Ω → ℝ} (hY : AEMeasurable Y P) (t : ℝ) :
    charFun (P.map Y) t = ∫ o, cexp ((t : ℂ) * (Y o : ℂ) * I) ∂P := by
  rw [charFun_apply_real, integral_map hY]
  exact (Continuous.aestronglyMeasurable (by fun_prop))

/-- Pointwise convergence of the characteristic functions under a.s. convergence. -/
theorem tendsto_charFun_map_of_tendsto_ae {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => X n o) atTop (𝓝 (Y o))) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (X n)) t) atTop (𝓝 (charFun (P.map Y) t)) := by
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hX hlim
  have hc : Continuous fun x : ℝ => cexp ((t : ℂ) * (x : ℂ) * I) := by fun_prop
  rw [charFun_map_real_eq_integral hY t]
  rw [show (fun n => charFun (P.map (X n)) t) =
      fun n => ∫ o, cexp ((t : ℂ) * (X n o : ℂ) * I) ∂P from
    funext fun n => charFun_map_real_eq_integral (hX n) t]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1)
    ?_ ?_
  · intro n
    exact (hc.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  · intro n
    exact Eventually.of_forall fun o => le_of_eq (norm_cexp_ofReal_mul_ofReal_mul_I t (X n o))
  · filter_upwards [hlim] with o ho
    exact (hc.tendsto (Y o)).comp ho

omit [IsProbabilityMeasure P] in
/-- The characteristic function of a real Gaussian variable in terms of its mean and variance. -/
theorem charFun_map_of_hasGaussianLaw {X : Ω → ℝ} (hX : HasGaussianLaw X P) (t : ℝ) :
    charFun (P.map X) t =
      cexp ((t : ℂ) * ((P[X] : ℝ) : ℂ) * I - ((Var[X; P] : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
  rw [hX.map_eq_gaussianReal, charFun_gaussianReal]
  congr 2
  simp [Real.coe_toNNReal _ (variance_nonneg X P)]

omit [IsProbabilityMeasure P] in
/-- The modulus of the characteristic function of a real Gaussian variable. -/
theorem norm_charFun_map_of_hasGaussianLaw {X : Ω → ℝ} (hX : HasGaussianLaw X P) (t : ℝ) :
    ‖charFun (P.map X) t‖ = Real.exp (-(Var[X; P] * t ^ 2 / 2)) := by
  rw [charFun_map_of_hasGaussianLaw hX t]
  have : (t : ℂ) * ((P[X] : ℝ) : ℂ) * I - ((Var[X; P] : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2 =
      ((-(Var[X; P] * t ^ 2 / 2) : ℝ) : ℂ) + ((t * P[X] : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_exp_ofReal]

omit [IsProbabilityMeasure P] in
/-- A real Gaussian variable has a second moment. -/
theorem memLp_two_of_hasGaussianLaw {X : Ω → ℝ} (hX : HasGaussianLaw X P) : MemLp X 2 P := by
  have h1 : MemLp id 2 (P.map X) := by
    rw [hX.map_eq_gaussianReal]
    exact memLp_id_gaussianReal 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).1 h1

/-- Under a.s. convergence of Gaussian variables the variances are eventually bounded: the limit's
characteristic function is close to `1` near `0`. -/
theorem exists_eventually_variance_le_of_tendsto_ae {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => X n o) atTop (𝓝 (Y o))) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ n in atTop, Var[X n; P] ≤ V := by
  have hXm : ∀ n, AEMeasurable (X n) P := fun n => (hX n).aemeasurable
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  have hcont : Continuous (charFun (P.map Y)) := continuous_charFun
  have h0 : charFun (P.map Y) 0 = 1 := by
    rw [charFun_zero]
    simp [Measure.real]
  -- a point `t₀ ≠ 0` where `‖φ_Y t₀‖ > 1/2`
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := (0 : ℝ))) (1 / 2)
    (by norm_num)
  set t₀ : ℝ := δ / 2 with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have hnear : dist (charFun (P.map Y) t₀) (charFun (P.map Y) 0) < 1 / 2 := by
    refine hδ' ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]
    linarith
  have hhalf : 1 / 2 < ‖charFun (P.map Y) t₀‖ := by
    rw [h0, dist_eq_norm] at hnear
    have := norm_sub_norm_le (1 : ℂ) (charFun (P.map Y) t₀)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hconv := (tendsto_charFun_map_of_tendsto_ae hXm hlim t₀).norm
  refine ⟨2 * Real.log 2 / t₀ ^ 2, by positivity, ?_⟩
  filter_upwards [hconv.eventually (eventually_gt_nhds hhalf)] with n hn
  rw [norm_charFun_map_of_hasGaussianLaw (hX n)] at hn
  have hlog : Real.log (1 / 2) < -(Var[X n; P] * t₀ ^ 2 / 2) :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hn
  rw [one_div, Real.log_inv] at hlog
  have ht2 : 0 < t₀ ^ 2 := by positivity
  rw [le_div_iff₀ ht2]
  linarith

/-- A real random variable is eventually inside a ball with high probability. -/
theorem exists_measure_abs_ge_lt {Y : Ω → ℝ} (hY : AEMeasurable Y P) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ P {o | M ≤ |Y o|} < ε := by
  have hmeas : ∀ k : ℕ, NullMeasurableSet {o | (k : ℝ) ≤ |Y o|} P := fun k =>
    nullMeasurableSet_le aemeasurable_const hY.norm
  have hanti : Antitone fun k : ℕ => {o | (k : ℝ) ≤ |Y o|} := by
    intro i j hij o ho
    change (j : ℝ) ≤ |Y o| at ho
    change (i : ℝ) ≤ |Y o|
    exact le_trans (by exact_mod_cast hij) ho
  have hinter : (⋂ k : ℕ, {o | (k : ℝ) ≤ |Y o|}) = ∅ := by
    ext o
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact exists_nat_gt _
  have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨k, Nat.cast_nonneg k, hk⟩

/-- Under a.s. convergence of Gaussian variables with eventually bounded variances, the means are
eventually bounded (tightness and Chebyshev). -/
theorem exists_eventually_abs_integral_le_of_tendsto_ae {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => X n o) atTop (𝓝 (Y o))) {V : ℝ}
    (hV : ∀ᶠ n in atTop, Var[X n; P] ≤ V) :
    ∃ B : ℝ, ∀ᶠ n in atTop, |P[X n]| ≤ B := by
  have hXm : ∀ n, AEMeasurable (X n) P := fun n => (hX n).aemeasurable
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim
  obtain ⟨M, hM0, hM⟩ := exists_measure_abs_ge_lt hY (ε := ENNReal.ofReal (1 / 8))
    (ENNReal.ofReal_pos.2 (by norm_num))
  have hprob := tendstoInMeasure_of_tendsto_ae (fun n => (hXm n).aestronglyMeasurable) hlim 1
    one_pos
  have hV' : 0 ≤ V := by
    obtain ⟨n, hn⟩ := hV.exists
    exact (variance_nonneg _ _).trans hn
  set c : ℝ := 2 * Real.sqrt (V + 1) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨M + 1 + c, ?_⟩
  filter_upwards [hV, hprob.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by norm_num) :
    (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 8)))] with n hVn hn
  set m : ℝ := P[X n] with hm
  -- the three bad events
  have hA : P {o | M + 1 ≤ |X n o|} ≤ ENNReal.ofReal (1 / 4) := by
    have hsub : {o | M + 1 ≤ |X n o|} ⊆
        {o | (1 : ℝ≥0∞) ≤ edist (X n o) (Y o)} ∪ {o | M ≤ |Y o|} := by
      intro o ho
      change M + 1 ≤ |X n o| at ho
      by_cases hd : (1 : ℝ) ≤ |X n o - Y o|
      · left
        change (1 : ℝ≥0∞) ≤ edist (X n o) (Y o)
        rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hd
      · right
        change M ≤ |Y o|
        have hd' := not_le.1 hd
        have := abs_sub_abs_le_abs_sub (X n o) (Y o)
        linarith
    calc P {o | M + 1 ≤ |X n o|}
        ≤ P ({o | (1 : ℝ≥0∞) ≤ edist (X n o) (Y o)} ∪ {o | M ≤ |Y o|}) := measure_mono hsub
      _ ≤ P {o | (1 : ℝ≥0∞) ≤ edist (X n o) (Y o)} + P {o | M ≤ |Y o|} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := add_le_add hn.le hM.le
      _ = ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  have hB : P {o | c ≤ |X n o - m|} ≤ ENNReal.ofReal (1 / 4) := by
    have hcheb := meas_ge_le_variance_div_sq (memLp_two_of_hasGaussianLaw (hX n)) hcpos
    refine hcheb.trans ?_
    have hc2 : c ^ 2 = 4 * (V + 1) := by
      rw [hc, mul_pow, Real.sq_sqrt (by linarith)]
      norm_num
    have hle : Var[X n; P] / c ^ 2 ≤ 1 / 4 := by
      rw [hc2, div_le_iff₀ (by positivity)]
      linarith
    exact ENNReal.ofReal_le_ofReal hle
  -- the good event is nonempty
  have hgood : ({o | M + 1 ≤ |X n o|} ∪ {o | c ≤ |X n o - m|})ᶜ.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    have huniv : {o | M + 1 ≤ |X n o|} ∪ {o | c ≤ |X n o - m|} = univ :=
      compl_empty_iff.1 hempty
    have h1 : P univ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
      rw [← huniv]
      exact (measure_union_le _ _).trans (add_le_add hA hB)
    rw [measure_univ, ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at h1
    have h3 : ENNReal.ofReal (1 / 4 + 1 / 4) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
    exact absurd h1 (not_le.2 h3)
  obtain ⟨o, ho⟩ := hgood
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le] at ho
  have := abs_sub_abs_le_abs_sub m (X n o)
  rw [abs_sub_comm m (X n o)] at this
  linarith

/-- ★★ **Almost-sure limits of real Gaussian variables are Gaussian.** -/
theorem hasGaussianLaw_of_tendsto_ae {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => X n o) atTop (𝓝 (Y o))) : HasGaussianLaw Y P := by
  have hXm : ∀ n, AEMeasurable (X n) P := fun n => (hX n).aemeasurable
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim
  obtain ⟨V, hV0, hV⟩ := exists_eventually_variance_le_of_tendsto_ae hX hlim
  obtain ⟨B, hB⟩ := exists_eventually_abs_integral_le_of_tendsto_ae hX hlim hV
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hV.and hB)
  -- the parameters along the shifted sequence are bounded
  set z : ℕ → ℝ × ℝ := fun n => (P[X (n + N₀)], Var[X (n + N₀); P]) with hz
  have hzmem : ∀ n, z n ∈ Icc (-B) B ×ˢ Icc 0 V := fun n => by
    obtain ⟨h1, h2⟩ := hN₀ (n + N₀) (Nat.le_add_left _ _)
    exact ⟨abs_le.1 h2, variance_nonneg _ _, h1⟩
  obtain ⟨⟨m, v⟩, -, ψ, hψ, hlimz⟩ :=
    tendsto_subseq_of_bounded ((isCompact_Icc.prod isCompact_Icc).isBounded) hzmem
  have hmean : Tendsto (fun n => P[X (ψ n + N₀)]) atTop (𝓝 m) :=
    (continuous_fst.tendsto (m, v)).comp hlimz
  have hvar : Tendsto (fun n => Var[X (ψ n + N₀); P]) atTop (𝓝 v) :=
    (continuous_snd.tendsto (m, v)).comp hlimz
  have hv0 : 0 ≤ v := ge_of_tendsto' hvar fun n => variance_nonneg _ _
  -- identification of the characteristic function
  have hchar : ∀ t : ℝ, charFun (P.map Y) t = charFun (gaussianReal m v.toNNReal) t := by
    intro t
    have h1 : Tendsto (fun n => charFun (P.map (X (ψ n + N₀))) t) atTop
        (𝓝 (charFun (P.map Y) t)) :=
      (tendsto_charFun_map_of_tendsto_ae hXm hlim t).comp
        ((tendsto_add_atTop_nat N₀).comp hψ.tendsto_atTop)
    have h2 : Tendsto (fun n => charFun (P.map (X (ψ n + N₀))) t) atTop
        (𝓝 (cexp ((t : ℂ) * (m : ℂ) * I - (v : ℂ) * (t : ℂ) ^ 2 / 2))) := by
      rw [show (fun n => charFun (P.map (X (ψ n + N₀))) t) = fun n =>
          cexp ((t : ℂ) * ((P[X (ψ n + N₀)] : ℝ) : ℂ) * I -
            ((Var[X (ψ n + N₀); P] : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) from
        funext fun n => charFun_map_of_hasGaussianLaw (hX _) t]
      refine Tendsto.cexp ?_
      refine Tendsto.sub ?_ ?_
      · exact ((tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto m |>.comp hmean)).mul
          tendsto_const_nhds)
      · exact ((Complex.continuous_ofReal.tendsto v |>.comp hvar).mul tendsto_const_nhds).div_const
          _
    rw [tendsto_nhds_unique h1 h2, charFun_gaussianReal]
    congr 2
    simp [Real.coe_toNNReal v hv0]
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  have hmap : P.map Y = gaussianReal m v.toNNReal := Measure.ext_of_charFun (funext hchar)
  exact ⟨by rw [hmap]; infer_instance⟩

end Grammar
