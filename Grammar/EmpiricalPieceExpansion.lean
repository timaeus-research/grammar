/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalAffineJets
import Grammar.EmpiricalPieceIntegral
import Grammar.SmoothFamilyIntegral

/-!
# The empirical expansion of a chart piece (§20 Stage 7, part 2)

A **smooth root field** is a root field whose branch representative on every piece is the pull-back
`Lψ_p ∘ Tm_p` of a smooth function on the chart coordinate space along the affine chart map of the
piece (smooth up to the walls; the sector sign is absorbed piece by piece). For such a field the
empirical piece integral
`empPieceInt Y p ξ N = ∫_{Base} empBoxIntegral h k N b (loc_p(s,·)) (amp s) dν`
is the base integral of rectangle integrals of the piece field family, and the box-form theorems
apply UNIFORMLY over the compact base: the rectangle kernel and the rectangle coefficients are
measurable and bounded in the base point (`measurable_empCoeffAtDepth_comp`,
`exists_abs_empCoeffRect_le_pieceFam`), and the remainder constant is uniform
(`emp_cutoffExpansion_rect_uniform`). Integrating over the base with
`cutoffExpansion_integral_of_uniform` gives ★★★ `empPieceInt_cutoffExpansion`: the empirical piece
integral is a cutoff expansion on the chart lattice `(2∏ kᵢ)⁻¹ℕ` with logarithmic degree `≤ da − 1`
and coefficients the base integrals of the rectangle coefficients `empPieceCoeff`. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Measurability of the coefficients in a parameter -/

section CoeffMeasurable

variable {α : Type*} [MeasurableSpace α] {d : ℕ}

/-- A face coefficient integral of a jointly measurable family is measurable in the parameter. -/
theorem measurable_faceCoeffInt_comp {ι : Type*} [Fintype ι] {G : α → (ι → ℝ) → ℝ}
    (hG : Measurable (Function.uncurry G)) (h a : ι → ℕ) (b μ : ℝ) (e : ℕ) :
    Measurable fun x => faceCoeffInt (G x) h a b μ e := by
  have hm : Measurable (Function.uncurry fun (x : α) (w : ι → ℝ) =>
      G x w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) := by
    change Measurable fun p : α × (ι → ℝ) =>
      G p.1 p.2 * mono h p.2 * mono a p.2 ^ (-μ) * logSum a p.2 ^ e
    exact ((hG.mul ((measurable_mono h).comp measurable_snd)).mul
      (((measurable_mono a).comp measurable_snd).pow_const _)).mul
      (((measurable_logSum a).comp measurable_snd).pow_const _)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (box ι b))).measurable

/-- ★ **The depth-`p` coefficients are measurable in a parameter** as soon as the face amplitudes
of the family are jointly measurable in (parameter, complementary coordinates, coupling). -/
theorem measurable_empCoeffAtDepth_comp {η ζ : α → (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)
    (hface : ∀ (J : Finset (Fin d)) (m : Fin d → ℕ),
      Measurable (Function.uncurry fun (z : α × ({i // ¬ inJ J i} → ℝ)) (τ : ℝ) =>
        faceAmp p J (fieldFam (η z.1) (ζ z.1) τ) m z.2)) (μ : ℝ) (q : ℕ) :
    Measurable fun x => empCoeffAtDepth (η x) (ζ x) h k p μ q := by
  unfold empCoeffAtDepth
  refine Finset.measurable_sum _ fun x _ => measurable_const.mul
    (Finset.measurable_sum _ fun j _ => measurable_const.mul ?_)
  have hG : Measurable (Function.uncurry fun (a : α) (w : {i // ¬ inJ x.1 i} → ℝ) =>
      empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (fieldFam (η a) (ζ a) τ) x.2 w) μ j) :=
    measurable_empFaceCoef_comp (α := α × ({i // ¬ inJ x.1 i} → ℝ)) k x.1 (fun i => x.2 i + h i)
      (G := fun z τ => faceAmp p x.1 (fieldFam (η z.1) (ζ z.1) τ) x.2 z.2) (hface x.1 x.2) μ j
  exact measurable_faceCoeffInt_comp hG (fun i : {i // ¬ inJ x.1 i} => h i)
    (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)

/-- The canonical coefficients are measurable in the parameter. -/
theorem measurable_empCoeff_comp {η ζ : α → (Fin d → ℝ) → ℝ} (h k : Fin d → ℕ)
    (hface : ∀ (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ),
      Measurable (Function.uncurry fun (z : α × ({i // ¬ inJ J i} → ℝ)) (τ : ℝ) =>
        faceAmp p J (fieldFam (η z.1) (ζ z.1) τ) m z.2)) (μ : ℝ) (q : ℕ) :
    Measurable fun x => empCoeff (η x) (ζ x) h k μ q :=
  measurable_empCoeffAtDepth_comp h k _ (hface _) μ q

end CoeffMeasurable

/-! ### Vanishing off the ambient lattice -/

section Lattice

variable {d : ℕ}

theorem exists_nat_div_of_mem_innerSpectrum {n : ℕ} (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : μ ∈ innerSpectrum k e) : ∃ m : ℕ, μ = (m : ℝ) / ((2 * ∏ i, k i : ℕ) : ℝ) := by
  unfold innerSpectrum at hμ
  rw [List.mem_toFinset, List.mem_map] at hμ
  obtain ⟨en, hen, rfl⟩ := hμ
  obtain ⟨j, hj⟩ := stateDensityRep_exponent_mem _ (sdWeights k e) en hen
  rw [hj]
  have hsd : sdWeights k e j + 1 = ((e j : ℝ) + 1) / (2 * (k j : ℝ)) := by
    unfold sdWeights; ring
  have hprod : ∏ i, k i = k j * ∏ i ∈ Finset.univ.erase j, k i := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hkj : (0 : ℝ) < k j := by exact_mod_cast hk _
  have hP : (0 : ℝ) < ∏ i ∈ Finset.univ.erase j, (k i : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast hk _
  refine ⟨(e j + 1) * ∏ i ∈ Finset.univ.erase j, k i, ?_⟩
  rw [hsd, hprod]
  push_cast
  field_simp

theorem empFaceCoef_eq_zero_of_not_lattice (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (J : Finset (Fin d)) (e : Fin d → ℕ) (G : ℝ → ℝ) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) (j : ℕ) : empFaceCoef k J e G μ j = 0 := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    unfold faceInnerCoeff empInnerCoeff
    rw [Finset.sum_eq_zero fun j' _ => ?_, mul_zero]
    have hnot : μ ∉ innerSpectrum ((fun i : {i // inJ J i} => k i) ∘ (faceEquiv _).symm)
        ((fun i : {i // inJ J i} => e i) ∘ (faceEquiv _).symm) := by
      intro hmem
      obtain ⟨m, hm⟩ := exists_nat_div_of_mem_innerSpectrum _ _ (fun i => hk _) hmem
      -- transport to the ambient lattice through `QJ ∣ Qamb`
      have hQJ : (2 * ∏ i, k ((faceEquiv {i // inJ J i}).symm i).1 : ℕ) = QJ k J := by
        unfold QJ
        congr 1
        exact Equiv.prod_comp (faceEquiv {i // inJ J i}).symm fun i : {i // inJ J i} => k i
      obtain ⟨c, hc⟩ := QJ_dvd_Qamb k J
      have hQJpos : 0 < QJ k J := QJ_pos k J hk
      apply hμ (m * c)
      rw [hm, hQJ, hc]
      push_cast
      have hc0 : (c : ℝ) ≠ 0 := by
        intro hc0
        have hcz : c = 0 := by exact_mod_cast hc0
        rw [hcz, mul_zero] at hc
        exact (Qamb_pos k hk).ne' hc
      have hQ0 : (QJ k J : ℝ) ≠ 0 := by exact_mod_cast hQJpos.ne'
      field_simp
    rw [coeffAt_eq_zero_of_not_mem _ hnot j', zero_mul, zero_mul]
  · rfl

theorem empCoeffAtDepth_eq_zero_of_not_lattice {η ζ : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) (q : ℕ) :
    empCoeffAtDepth η ζ h k p μ q = 0 := by
  unfold empCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ =>
    empFaceCoef_eq_zero_of_not_lattice k hk x.1 _ _ hμ j, mul_zero]

theorem empCoeff_eq_zero_of_not_lattice {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) (q : ℕ) :
    empCoeff η ζ h k μ q = 0 :=
  empCoeffAtDepth_eq_zero_of_not_lattice h k _ hk hμ q

end Lattice

/-! ### The piece field family: bounds and measurability of the rectangle data -/

section Piece

variable {d da : ℕ} {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
  (σ : WaterFilling.CoordSign d) (G Lψ : (Fin d → ℝ) → ℝ) {b : ℝ}
  {S : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
  {sc : S → {i // ¬ inJ J i} → ℝ}

/-- The dilated amplitude of a piece is the composition with the diagonal scaling. -/
theorem pieceAmp_eq_comp_diag (c : {i // ¬ inJ J i} → ℝ) :
    pieceAmp e σ G b c = (fun v => G (affineMap e σ c v)) ∘ diag (fun _ => b) := rfl

omit [CompactSpace S] in
/-- ★ The rectangle coefficients of the piece family are measurable in the base point. -/
theorem measurable_empCoeffRect_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (h k : Fin da → ℕ) (μ : ℝ) (q : ℕ) :
    Measurable fun s => empCoeffRect (fun v => G (affineMap e σ (sc s) v))
      (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) μ q := by
  unfold empCoeffRect
  refine measurable_const.mul ?_
  unfold scaleCoeff
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  refine (Measurable.mul ?_ measurable_const).mul measurable_const
  have := measurable_empCoeff_comp (η := fun s => pieceAmp e σ G b (sc s))
    (ζ := fun s => pieceAmp e σ Lψ b (sc s)) h k
    (fun p F m => measurable_faceAmp_pieceFam e σ G Lψ b hG hLψ hsc p F m) μ j
  exact this

omit [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- ★ The rectangle coefficients of the piece family are bounded uniformly in the base point. -/
theorem exists_abs_empCoeffRect_le_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (hb : 0 < b) (h k : Fin da → ℕ) (hk : ∀ i, 0 < k i) (μ : ℝ) (q : ℕ) :
    ∃ B : ℝ, ∀ s, |empCoeffRect (fun v => G (affineMap e σ (sc s) v))
      (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) μ q| ≤ B := by
  have hQ := Qamb_pos k hk
  have hL₀ : L₀ h ≤ cutoffOf h μ := L₀_le_cutoffOf h μ
  obtain ⟨C, M', hC0, hC⟩ := exists_fieldJetBound_pieceFam e σ G Lψ b hG hLψ hsc
    (depthOf h k (cutoffOf h μ))
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepth_le h k (depthOf h k (cutoffOf h μ)) hk
    (depthOf_add hk hL₀) (depthOf_pos hk hL₀) M'
  have hX0 : 0 < mono (fun i => 2 * k i) (fun _ : Fin da => b) := mono_pos _ fun _ => hb
  refine ⟨|∏ _i : Fin da, b| * |mono h (fun _ : Fin da => b)| *
    ((mono (fun i => 2 * k i) (fun _ : Fin da => b)) ^ (-μ) *
      ∑ j ∈ Finset.Ico q (da - 1 + 1), C * K₁ * (j.choose q : ℝ) *
        |log (mono (fun i => 2 * k i) (fun _ : Fin da => b))| ^ (j - q)), fun s => ?_⟩
  unfold empCoeffRect scaleCoeff
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (rpow_pos_of_pos hX0 _)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j hj => ?_)) (rpow_pos_of_pos hX0 _).le) (by positivity)
  rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    (pow_nonneg (abs_nonneg _) _)
  have hjD : j ≤ da - 1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
  rw [← pieceAmp_eq_comp_diag, ← pieceAmp_eq_comp_diag]
  by_cases hμl : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · have hμL : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
      (mem_latticeBelow_iff hQ).2 ⟨hμl, lt_cutoffOf h μ⟩
    rw [empCoeff_eq (contDiff_pieceAmp e σ G b hG _) (contDiff_pieceAmp e σ Lψ b hLψ _) hk hL₀
      hμL hjD]
    have hsum := hK₁ _ _ (contDiff_pieceAmp e σ G b hG _) (contDiff_pieceAmp e σ Lψ b hLψ _) C
      (hC s)
    have h1 : |empCoeffAtDepth (pieceAmp e σ G b (sc s)) (pieceAmp e σ Lψ b (sc s)) h k
        (depthOf h k (cutoffOf h μ)) μ j| ≤
        ∑ j' ∈ range (da - 1 + 1), |empCoeffAtDepth (pieceAmp e σ G b (sc s))
          (pieceAmp e σ Lψ b (sc s)) h k (depthOf h k (cutoffOf h μ)) μ j'| :=
      Finset.single_le_sum (f := fun j' => |empCoeffAtDepth (pieceAmp e σ G b (sc s))
        (pieceAmp e σ Lψ b (sc s)) h k (depthOf h k (cutoffOf h μ)) μ j'|)
        (fun j' _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjD))
    have h2 : ∑ j' ∈ range (da - 1 + 1), |empCoeffAtDepth (pieceAmp e σ G b (sc s))
        (pieceAmp e σ Lψ b (sc s)) h k (depthOf h k (cutoffOf h μ)) μ j'| ≤
        ∑ ν ∈ latticeBelow (Qamb k) (cutoffOf h μ), ∑ j' ∈ range (da - 1 + 1),
          |empCoeffAtDepth (pieceAmp e σ G b (sc s)) (pieceAmp e σ Lψ b (sc s)) h k
            (depthOf h k (cutoffOf h μ)) ν j'| :=
      Finset.single_le_sum (f := fun ν => ∑ j' ∈ range (da - 1 + 1),
        |empCoeffAtDepth (pieceAmp e σ G b (sc s)) (pieceAmp e σ Lψ b (sc s)) h k
          (depthOf h k (cutoffOf h μ)) ν j'|) (fun ν _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        hμL
    exact h1.trans (h2.trans hsum)
  · have hμl' : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k := fun m hm => hμl ⟨m, hm⟩
    rw [empCoeff_eq_zero_of_not_lattice hk hμl' j, abs_zero]
    exact mul_nonneg hC0 hK₁0

omit [CompactSpace S] in
/-- The rectangle kernel of the piece family, as a function of the base point. -/
theorem measurable_empIntegralRect_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (h k : Fin da → ℕ) (N : ℝ) :
    Measurable fun s => empIntegralRect (fun v => G (affineMap e σ (sc s) v))
      (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) N := by
  have hc : Continuous fun z : S × (Fin da → ℝ) => G (affineMap e σ (sc z.1) z.2) *
      mono h z.2 * exp (-N * mono (fun i => 2 * k i) z.2 +
        Real.sqrt N * mono k z.2 * Lψ (affineMap e σ (sc z.1) z.2)) := by
    have hA : Continuous fun z : S × (Fin da → ℝ) => affineMap e σ (sc z.1) z.2 :=
      (continuous_affineMap_pair e σ).comp ((hsc.comp continuous_fst).prodMk continuous_snd)
    exact ((hG.continuous.comp hA).mul ((continuous_mono h).comp continuous_snd)).mul
      (continuous_exp.comp ((continuous_const.mul ((continuous_mono _).comp continuous_snd)).add
        ((continuous_const.mul ((continuous_mono k).comp continuous_snd)).mul
          (hLψ.continuous.comp hA))))
  unfold empIntegralRect
  exact (hc.measurable.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (rect fun _ : Fin da => b))).measurable

omit [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- The rectangle kernel is bounded uniformly in the base point (for `N ≥ 0`). -/
theorem exists_abs_empIntegralRect_le_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (hb : 0 < b) (h k : Fin da → ℕ) :
    ∃ Bd : ℝ, ∀ s, ∀ N : ℝ, 0 ≤ N → |empIntegralRect (fun v => G (affineMap e σ (sc s) v))
      (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) N| ≤ Bd := by
  have hA : Continuous fun z : S × (Fin da → ℝ) => affineMap e σ (sc z.1) z.2 :=
    (continuous_affineMap_pair e σ).comp ((hsc.comp continuous_fst).prodMk continuous_snd)
  have hK : IsCompact ((Set.univ : Set S) ×ˢ closedBox da b) :=
    isCompact_univ.prod (isCompact_closedBox b)
  obtain ⟨AG, hAG⟩ := hK.exists_bound_of_continuousOn (hG.continuous.comp hA).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hLψ.continuous.comp hA).continuousOn
  refine ⟨exp (M ^ 2 / 2) * AG * empBoxIntegral h k (0 / 2) b (fun _ => 0) (fun _ => 1) +
    exp (M ^ 2 / 2) * AG * 1, fun s N hN => ?_⟩
  have hid : empIntegralRect (fun v => G (affineMap e σ (sc s) v))
      (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) N =
      empBoxIntegral h k N b (fun v => Lψ (affineMap e σ (sc s) v))
        (fun v => G (affineMap e σ (sc s) v)) := by
    unfold empIntegralRect empBoxIntegral
    rw [rect_const]
  rw [hid]
  have hbox : ∀ u ∈ box (Fin da) b, u ∈ closedBox da b := fun u hu =>
    mem_closedBox.2 fun i => Ioc_subset_Icc_self (hu i (Set.mem_univ i))
  have h1 := abs_empBoxIntegral_le h k hN (ξ := fun v => Lψ (affineMap e σ (sc s) v))
    (η := fun v => G (affineMap e σ (sc s) v)) (M := M) (A := AG)
    (fun u hu => by simpa [Real.norm_eq_abs] using hM (s, u) ⟨Set.mem_univ _, hbox u hu⟩)
    (fun u hu => by simpa [Real.norm_eq_abs] using hAG (s, u) ⟨Set.mem_univ _, hbox u hu⟩)
  refine h1.trans ?_
  -- the zero-field half-temperature integral is at most its value at `N = 0` plus one
  have hAG0 : 0 ≤ AG := (abs_nonneg _).trans (by
    simpa [Real.norm_eq_abs] using hAG (s, fun _ => b) ⟨Set.mem_univ _, mem_closedBox.2 fun _ =>
      ⟨hb.le, le_rfl⟩⟩)
  have hmono : empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) ≤
      empBoxIntegral h k (0 / 2) b (fun _ => 0) (fun _ => 1) := by
    unfold empBoxIntegral
    refine setIntegral_mono_on ?_ ?_ (measurableSet_box b) fun u hu => ?_
    · exact integrableOn_box_of_continuous ((continuous_const.mul (continuous_mono h)).mul
        (continuous_exp.comp ((continuous_const.mul (continuous_mono _)).add
          ((continuous_const.mul (continuous_mono k)).mul continuous_const)))) b
    · exact integrableOn_box_of_continuous ((continuous_const.mul (continuous_mono h)).mul
        (continuous_exp.comp ((continuous_const.mul (continuous_mono _)).add
          ((continuous_const.mul (continuous_mono k)).mul continuous_const)))) b
    · have hu0 : 0 ≤ mono (fun i => 2 * k i) u := (mono_pos _ (pos_of_mem_box hu)).le
      have hm : 0 ≤ mono h u := (mono_pos _ (pos_of_mem_box hu)).le
      simp only [mul_zero, add_zero, one_mul]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hm
  have hpos : 0 ≤ exp (M ^ 2 / 2) * AG := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hpos]

omit [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- ★★ **The uniform rectangle expansion of the piece family**: one constant for all base points,
for `N` beyond a threshold depending only on the piece data. -/
theorem emp_cutoffExpansion_rect_uniform (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (hb : 0 < b) (h k : Fin da → ℕ) (hk : ∀ i, 0 < k i) (L' : ℝ) :
    ∃ K₀ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ s, ∀ N : ℝ, N₀ ≤ N →
      |empIntegralRect (fun v => G (affineMap e σ (sc s) v))
          (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) N -
        absSpectralSum (Qamb k) (da - 1) (empCoeffRect (fun v => G (affineMap e σ (sc s) v))
          (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b)) L' N| ≤
        K₀ * (N ^ (-L') * (1 + log N) ^ (da - 1)) := by
  set A : ℝ := (∏ _i : Fin da, b) * mono h (fun _ : Fin da => b) with hA
  set Bb : ℝ := mono (fun i => 2 * k i) (fun _ : Fin da => b) with hBb
  have hBb0 : 0 < Bb := mono_pos _ fun _ => hb
  set p : Fin da → ℕ := depthOf h k (max ⌈L'⌉₊ (L₀ h)) with hp
  obtain ⟨C, M', hC0, hC⟩ := exists_fieldJetBound_pieceFam e σ G Lψ b hG hLψ hsc p
  obtain ⟨K₀, hK₀0, hK₀⟩ := emp_cutoffExpansion_uniform (h := h) (k := k) hk L' M'
  refine ⟨|A| * (C * K₀) * (Bb ^ (-L') * (1 + |log Bb|) ^ (da - 1)), max 1 Bb⁻¹,
    le_max_left _ _, fun s N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by linarith
  have hBN : 1 ≤ Bb * N := by
    have := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hN) hBb0.le
    rwa [mul_inv_cancel₀ hBb0.ne'] at this
  rw [empIntegralRect_eq _ _ h k (fun _ => hb) N]
  unfold empCoeffRect
  rw [absSpectralSum_const_mul, ← absSpectralSum_mul_pos _ _ hBb0 hNpos, ← mul_sub, abs_mul]
  rw [← pieceAmp_eq_comp_diag, ← pieceAmp_eq_comp_diag]
  have hkey := hK₀ _ _ (contDiff_pieceAmp e σ G b hG _) (contDiff_pieceAmp e σ Lψ b hLψ _) C (hC s)
    (Bb * N) hBN
  have hlog := one_add_log_mul_le' hBb0 hN1
  have hlogN : 0 ≤ log N := log_nonneg hN1
  have hpow : (1 + log (Bb * N)) ^ (da - 1) ≤ ((1 + |log Bb|) * (1 + log N)) ^ (da - 1) :=
    pow_le_pow_left₀ (by linarith [log_nonneg hBN]) hlog _
  have hrp : (Bb * N) ^ (-L') = Bb ^ (-L') * N ^ (-L') := Real.mul_rpow hBb0.le hNpos.le
  calc |A| * |empIntegral (pieceAmp e σ G b (sc s)) (pieceAmp e σ Lψ b (sc s)) h k (Bb * N) -
        absSpectralSum (Qamb k) (da - 1) (empCoeff (pieceAmp e σ G b (sc s))
          (pieceAmp e σ Lψ b (sc s)) h k) L' (Bb * N)|
      ≤ |A| * (C * K₀ * ((Bb * N) ^ (-L') * (1 + log (Bb * N)) ^ (da - 1))) :=
        mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    _ ≤ |A| * (C * K₀ * ((Bb ^ (-L') * N ^ (-L')) *
          ((1 + |log Bb|) * (1 + log N)) ^ (da - 1))) := by
        rw [hrp]
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- ★★★ **The empirical expansion of a chart piece**: the base integral of the rectangle kernels of
the piece family is a cutoff expansion on the chart lattice with logarithmic degree `≤ da − 1`,
with coefficients the base integrals of the rectangle coefficients. -/
theorem empRect_cutoffExpansion_integral (ν : Measure S) [IsFiniteMeasure ν] (hG : ContDiff ℝ ∞ G)
    (hLψ : ContDiff ℝ ∞ Lψ) (hsc : Continuous sc) (hb : 0 < b) (h k : Fin da → ℕ)
    (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (da - 1)
      (fun N => ∫ s, empIntegralRect (fun v => G (affineMap e σ (sc s) v))
        (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) N ∂ν)
      (fun μ q => ∫ s, empCoeffRect (fun v => G (affineMap e σ (sc s) v))
        (fun v => Lψ (affineMap e σ (sc s) v)) h k (fun _ => b) μ q ∂ν) := by
  refine cutoffExpansion_integral_of_uniform ν (fun N hN => ?_) (fun μ q => ?_) fun L' _ => ?_
  · obtain ⟨Bd, hBd⟩ := exists_abs_empIntegralRect_le_pieceFam e σ G Lψ hG hLψ hsc hb h k
    exact Integrable.of_bound
      (measurable_empIntegralRect_pieceFam e σ G Lψ hG hLψ hsc h k N).aestronglyMeasurable Bd
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hBd s N (by linarith))
  · obtain ⟨B, hB⟩ := exists_abs_empCoeffRect_le_pieceFam e σ G Lψ hG hLψ hsc hb h k hk μ q
    exact Integrable.of_bound
      (measurable_empCoeffRect_pieceFam e σ G Lψ hG hLψ hsc h k μ q).aestronglyMeasurable B
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hB s)
  · obtain ⟨K₀, N₀, hN₀, hK₀⟩ := emp_cutoffExpansion_rect_uniform e σ G Lψ hG hLψ hsc hb h k hk L'
    exact ⟨K₀, N₀, hN₀, hK₀⟩

end Piece

end SmoothEngine

end Grammar
