/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalPieceLeading
import Grammar.SmoothLogIntegrable
import Grammar.SmoothAmplitudeFamily
import Grammar.FluctuationLipschitz
import Grammar.EmpiricalLeadingConsistency

/-!
# The closed-face leading measure (polar-distribution programme, unit 18)

Consult #167 (A4, `tide-log/plan_polar_distribution.md`). On the box `(0,b]^d` with data `(h,k)`
and leading exponent `l` (`BoxLeading h k l m`: `l ≤ (h_i+1)/2k_i` for every `i`, at most `m`
attaining it), let `J = resSet h k l` be the resonant coordinates. For a nonnegative amplitude `a`
the **leading face measure** is the pushforward under the face inclusion `w ↦ glue J 0 w` of the
density
  `(∏_{i∈J} (2k_i)⁻¹) · a(0_J, w) · ∏_{i∉J} w_i^{h_i − 2k_i l}`
on the complementary box `(0,b]^{Jᶜ}` (`leadingFaceDensity`, `leadingFaceMeasure`). Since every
complementary wall has exponent `> l`, the weight has exponents `> −1` and the measure is FINITE
(`leadingFaceMeasure_univ_lt_top`); it is carried by the closed face `{u_J = 0}` and gives the
deeper corners `{∃ i ∉ J, u_i = 0}` measure zero (`leadingFaceMeasure_face`,
`leadingFaceMeasure_deep`). Integrals against it are the box integrals of the face construction
(`integral_leadingFaceMeasure`), so the empirical face functional of `EmpiricalFaceFunctional`
is `(1/(m−1)!) ∫ S_l(ξ) dρ^η` (`faceFunctional_eq_integral_leadingFaceMeasure`), and the leading
limit of the tilted box integral with amplitude `a·F` is, for every continuous `F` and field `ξ`,
  `N^l (log N)^{−(m−1)} ∫ a F u^h e^{−N u^{2k} + √N u^k ξ} → (1/(m−1)!) ∫ F S_l(ξ) dρ^a`
(★★ `tendsto_empBoxIntegral_leadingFaceMeasure`), with no admissibility hypothesis on `F`: the
measure representation on the CLOSED face is the new content, the limit itself is
`tendsto_empBoxIntegral_div_boxFaceLimit`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-- The residue weight on positive coordinates as a product of real powers. -/
theorem residueWeight_eq_prod {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    residueWeight h k μ w = ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * μ) := by
  unfold residueWeight mono
  rw [← Real.finsetProd_rpow _ _ (fun j _ => pow_nonneg (hw j).le _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hw j).le,
    ← Real.rpow_add (hw j)]
  congr 1
  push_cast
  ring

/-- The residue weight is integrable on the box when every exponent exceeds `−1`. -/
theorem integrableOn_residueWeight_box {ι : Type*} [Fintype ι] (h k : ι → ℕ) {μ : ℝ}
    (hμ : ∀ i, 2 * (k i : ℝ) * μ < h i + 1) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (residueWeight h k μ) (SmoothEngine.box ι b) := by
  have hc : ∀ i, -1 < (h i : ℝ) - 2 * (k i : ℝ) * μ := fun i => by linarith [hμ i]
  have := integrableOn_prod_rpow_mul_log_pow hc (fun _ => 0) 0 hb
  simp only [pow_zero, mul_one] at this
  exact this.congr_fun (fun w hw => (residueWeight_eq_prod h k μ fun j =>
    SmoothEngine.pos_of_mem_box hw j).symm) (SmoothEngine.measurableSet_box b)

theorem measurable_residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) :
    Measurable (residueWeight h k μ) := by
  unfold residueWeight
  exact (measurable_mono _).mul ((measurable_mono _).pow_const _)

section

variable (h k : Fin d → ℕ) (l : ℝ)

/-- The leading face density with amplitude `a`:
`(∏_{i∈J} (2k_i)⁻¹) · a(0_J,w) · residueWeight(w)` on the complementary box. -/
noncomputable def leadingFaceDensity (a : (Fin d → ℝ) → ℝ)
    (w : {i // ¬ inJ (resSet h k l) i} → ℝ) : ℝ :=
  (∏ i ∈ resSet h k l, (2 * (k i : ℝ))⁻¹) * a (glue (resSet h k l) 0 w) *
    residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w

/-- The leading face measure on `ℝ^d`: the density pushed forward under the face inclusion. -/
noncomputable def leadingFaceMeasure (b : ℝ) (a : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  ((volume.restrict (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b)).withDensity
    fun w => ENNReal.ofReal (leadingFaceDensity h k l a w)).map (glue (resSet h k l) 0)

theorem measurable_glue_zero (J : Finset (Fin d)) :
    Measurable fun w : {i // ¬ inJ J i} → ℝ => glue J 0 w :=
  (continuous_glue_zero J).measurable

theorem leadingFaceDensity_nonneg {a : (Fin d → ℝ) → ℝ} (ha : ∀ u, 0 ≤ a u) {b : ℝ}
    {w : {i // ¬ inJ (resSet h k l) i} → ℝ} (hw : w ∈ SmoothEngine.box _ b) :
    0 ≤ leadingFaceDensity h k l a w :=
  mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (ha _))
    (residueWeight_nonneg _ _ _ hw)

theorem measurable_leadingFaceDensity {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    Measurable (leadingFaceDensity h k l a) := by
  unfold leadingFaceDensity
  exact (measurable_const.mul (ha.comp (continuous_glue_zero _)).measurable).mul
    (measurable_residueWeight _ _ _)

/-- Integrals against the leading face measure are box integrals of the face construction. -/
theorem integral_leadingFaceMeasure {b : ℝ} {a : (Fin d → ℝ) → ℝ} (ha : Continuous a)
    (ha0 : ∀ u, 0 ≤ a u) {F : (Fin d → ℝ) → ℝ} (hF : Measurable F) :
    ∫ u, F u ∂(leadingFaceMeasure h k l b a) =
      ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
        F (glue (resSet h k l) 0 w) * leadingFaceDensity h k l a w := by
  unfold leadingFaceMeasure
  rw [integral_map (measurable_glue_zero _).aemeasurable hF.aestronglyMeasurable]
  have hmeas : Measurable fun w => (leadingFaceDensity h k l a w).toNNReal :=
    (measurable_leadingFaceDensity h k l ha).real_toNNReal
  have hd : (fun w => ENNReal.ofReal (leadingFaceDensity h k l a w)) =
      fun w => ((leadingFaceDensity h k l a w).toNNReal : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hmeas]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box b) fun w hw => ?_
  simp only [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (leadingFaceDensity_nonneg h k l ha0 hw)]
  ring

/-- The complementary weight is integrable under `BoxLeading`, since every complementary wall has
exponent strictly greater than `l`. -/
theorem integrableOn_residueWeight_compl (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l)
      (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b) := by
  refine integrableOn_residueWeight_box _ _ (fun i => ?_) hb
  have hne : ratioExp h k i ≠ l := fun h' => i.2 (inJ_iff.2 (mem_resSet.2 h'))
  have hlt : l < ratioExp h k i := lt_of_le_of_ne (hmin i) (Ne.symm hne)
  have hk' : (0 : ℝ) < 2 * k i := by
    have := Nat.cast_pos (α := ℝ) |>.2 (hk i)
    positivity
  unfold ratioExp at hlt
  rw [lt_div_iff₀ hk'] at hlt
  linarith

/-- The leading face density is integrable on the complementary box for continuous `a`. -/
theorem integrableOn_leadingFaceDensity (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    IntegrableOn (leadingFaceDensity h k l a)
      (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBox b).exists_bound_of_continuousOn ha.continuousOn
  have hcont : Continuous fun w : {i // ¬ inJ (resSet h k l) i} → ℝ =>
      (∏ i ∈ resSet h k l, (2 * (k i : ℝ))⁻¹) * a (glue (resSet h k l) 0 w) :=
    continuous_const.mul (ha.comp (continuous_glue_zero _))
  refine ((integrableOn_residueWeight_compl h k l hk hmin hb.le).bdd_mul
    (c := |∏ i ∈ resSet h k l, (2 * (k i : ℝ))⁻¹| * C) hcont.aestronglyMeasurable ?_)
  rw [ae_restrict_iff' (SmoothEngine.measurableSet_box b)]
  refine Eventually.of_forall fun w hw => ?_
  rw [norm_mul, Real.norm_eq_abs (∏ i ∈ resSet h k l, (2 * (k i : ℝ))⁻¹)]
  exact mul_le_mul_of_nonneg_left (hC _ (mem_closedBox.2 (glue_zero_mem_Icc _ hb hw)))
    (abs_nonneg _)

/-- The leading face measure is finite. -/
theorem leadingFaceMeasure_univ_lt_top (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    leadingFaceMeasure h k l b a univ < ⊤ := by
  unfold leadingFaceMeasure
  rw [Measure.map_apply (measurable_glue_zero _) MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_)
    (integrableOn_leadingFaceDensity h k l hk hmin hb ha).lintegral_lt_top
  exact le_rfl

theorem isFiniteMeasure_leadingFaceMeasure (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    IsFiniteMeasure (leadingFaceMeasure h k l b a) :=
  ⟨leadingFaceMeasure_univ_lt_top h k l hk hmin hb ha⟩

theorem measurableSet_coordZero (i : Fin d) : MeasurableSet {u : Fin d → ℝ | u i = 0} :=
  measurableSet_eq_fun (measurable_pi_apply i) measurable_const

/-- The measure is carried by the closed face `{u_J = 0}`. -/
theorem leadingFaceMeasure_face (b : ℝ) (a : (Fin d → ℝ) → ℝ) :
    leadingFaceMeasure h k l b a {u | ∃ i ∈ resSet h k l, u i ≠ 0} = 0 := by
  unfold leadingFaceMeasure
  have hmeas : MeasurableSet {u : Fin d → ℝ | ∃ i ∈ resSet h k l, u i ≠ 0} := by
    have : {u : Fin d → ℝ | ∃ i ∈ resSet h k l, u i ≠ 0} =
        ⋃ i ∈ resSet h k l, {u : Fin d → ℝ | u i = 0}ᶜ := by
      ext u; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ => (measurableSet_coordZero i).compl
  rw [Measure.map_apply (measurable_glue_zero _) hmeas]
  have : (glue (resSet h k l) 0 ⁻¹' {u : Fin d → ℝ | ∃ i ∈ resSet h k l, u i ≠ 0}) = ∅ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and, not_not]
    intro i hi
    exact glue_apply_of_mem _ _ _ hi
  rw [this, measure_empty]

/-- The deeper corners `{∃ i ∉ J, u_i = 0}` carry no mass. -/
theorem leadingFaceMeasure_deep (b : ℝ) (a : (Fin d → ℝ) → ℝ) :
    leadingFaceMeasure h k l b a {u | ∃ i, i ∉ resSet h k l ∧ u i = 0} = 0 := by
  unfold leadingFaceMeasure
  have hmeas : MeasurableSet {u : Fin d → ℝ | ∃ i, i ∉ resSet h k l ∧ u i = 0} := by
    have : {u : Fin d → ℝ | ∃ i, i ∉ resSet h k l ∧ u i = 0} =
        ⋃ i ∈ (Finset.univ.filter fun i => i ∉ resSet h k l), {u : Fin d → ℝ | u i = 0} := by
      ext u; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ => measurableSet_coordZero i
  rw [Measure.map_apply (measurable_glue_zero _) hmeas, withDensity_apply _
    ((measurable_glue_zero _) hmeas), Measure.restrict_restrict ((measurable_glue_zero _) hmeas)]
  have : (glue (resSet h k l) 0 ⁻¹' {u : Fin d → ℝ | ∃ i, i ∉ resSet h k l ∧ u i = 0}) ∩
      SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b = ∅ := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro ⟨i, hi, hw⟩ hbox
    rw [glue_apply_of_not_mem _ _ _ hi] at hw
    exact (SmoothEngine.pos_of_mem_box hbox ⟨i, fun h' => hi (inJ_iff.1 h')⟩).ne' hw

  rw [this, Measure.restrict_empty, lintegral_zero_measure]

end

section

variable (h k : Fin d → ℕ) {l : ℝ} {m : ℕ}

/-- The empirical face functional is `(1/(m−1)!) ∫ S_l(ξ) dρ^η` for a nonnegative continuous
amplitude `η`. -/
theorem faceFunctional_eq_integral_leadingFaceMeasure (hl : 0 < l) {b : ℝ}
    {ξ η : (Fin d → ℝ) → ℝ} (hξ : Continuous ξ) (hη : Continuous η) (hη0 : ∀ u, 0 ≤ η u) :
    faceFunctional h k l b ξ η =
      (1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ)) *
        ∫ u, fluctuation 1 l (ξ u) ∂(leadingFaceMeasure h k l b η) := by
  have hS : Continuous fun u => fluctuation 1 l (ξ u) :=
    (differentiable_fluctuation 1 l one_pos hl).continuous.comp hξ
  rw [integral_leadingFaceMeasure h k l hη hη0 hS.measurable]
  unfold faceFunctional leadingFaceDensity
  rw [← integral_const_mul, ← integral_const_mul, one_div, mul_inv, Finset.prod_inv_distrib]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box b) fun w _ => ?_
  try dsimp only
  ring

/-- **The leading limit of the tilted box integral on the closed face.** Under `BoxLeading` with
the multiplicity attained, for every continuous field `ξ`, nonnegative continuous amplitude `a`
and continuous observable `F`,
`N^l (log N)^{−(m−1)} ∫_{(0,b]^d} a F u^h e^{−N u^{2k} + √N u^k ξ} → (1/(m−1)!) ∫ F S_l(ξ) dρ^a`.
No admissibility of `F` is needed. -/
theorem tendsto_empBoxIntegral_leadingFaceMeasure (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (hm : 1 ≤ m)
    (hlead : BoxLeading h k l m) (hatt : multCount (ratioExp h k) l = m)
    {ξ a F : (Fin d → ℝ) → ℝ} (hξ : Continuous ξ) (ha : Continuous a) (ha0 : ∀ u, 0 ≤ a u)
    (hF : Continuous F) :
    Tendsto (fun N => empBoxIntegral h k N b ξ (fun u => a u * F u) /
        (N ^ (-l) * Real.log N ^ (m - 1))) atTop
      (𝓝 ((1 / ((m - 1).factorial : ℝ)) *
        ∫ u, F u * fluctuation 1 l (ξ u) ∂(leadingFaceMeasure h k l b a))) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := exists_eq_of_multCount_pos (ℓ := ratioExp h k) (l := l) (by omega)
    rw [← hi]; exact ratioExp_pos h k hk i
  have hlim := tendsto_empBoxIntegral_div_boxFaceLimit h k hk hb hm hlead ξ (fun u => a u * F u)
    hξ (ha.mul hF)
  convert hlim using 2
  unfold boxFaceLimit
  rw [if_pos hatt]
  have hS : Continuous fun u => F u * fluctuation 1 l (ξ u) :=
    hF.mul ((differentiable_fluctuation 1 l one_pos hl).continuous.comp hξ)
  rw [integral_leadingFaceMeasure h k l ha ha0 hS.measurable]
  unfold faceFunctional leadingFaceDensity
  rw [hatt, ← integral_const_mul, ← integral_const_mul, one_div, one_div, mul_inv,
    Finset.prod_inv_distrib]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box b) fun w _ => ?_
  try dsimp only
  ring

end

end Grammar
