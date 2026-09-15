/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedStratumPositive

/-!
# Absolute convergence of the stratum face integrals

Consult #130, Unit E1c. The face integrand of the graded stratum formula,
`∂_J^α A (0_J, w) · ∏_{i∉J} w_i^{h_i} (∏_{i∉J} w_i^{2k_i})^{−μ}`, has a power singularity along the
walls `w_i = 0` of the face box, where the face meets the deeper strata. When the amplitude `A`
vanishes on a neighbourhood of the deep set (relative to the closed box), the derivative
`∂_J^α A` vanishes in a COLLAR `{w : ∃ i, w_i < δ}` of the walls (compactness of the wall set and
`IsCompact.exists_thickening_subset_open`), and off the collar the power weight is bounded, so the
integrand is dominated by `M · w^p` for a large `p` and the engine's weighted integrability
(`integrable_faceCoeff`) applies: the face integral is absolutely convergent
(★ `integrableOn_stratum_integrand`). On the resolved manifold the neighbourhood vanishing of the
piece amplitude follows from `F` vanishing near the deep zero fibre (`exists_open_amp_zero`), so
every face integral of the stratum sum is absolutely convergent
(★★ `integrableOn_pieceStratum_integrand`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

theorem glue_zero_mem_closedBox_of_mem_Icc {J : Finset (Fin d)} {b : ℝ} (hb : 0 ≤ b)
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ Set.pi univ fun _ => Icc (0 : ℝ) b) :
    glue J 0 w ∈ closedBox d b := by
  rw [mem_closedBox]
  intro i
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi, Pi.zero_apply]
    exact ⟨le_rfl, hb⟩
  · rw [glue_apply_of_not_mem J _ _ hi]
    exact hw ⟨i, fun h => hi (inJ_iff.1 h)⟩ (Set.mem_univ _)

/-- ★ **Absolute convergence of the stratum face integrand**: if the amplitude vanishes on a
neighbourhood of the deep set relative to the closed box, the face integrand is integrable on the
face box. -/
theorem integrableOn_stratum_integrand {A : (Fin d → ℝ) → ℝ} (hA : ContDiff ℝ ∞ A)
    (h k : Fin d → ℕ) {b : ℝ} (hb : 0 < b) {c : ℕ} {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    (hAO : ∀ v ∈ O ∩ closedBox d b, A v = 0) (hdeep : deepSet d b c ⊆ O) (J : Finset (Fin d))
    (hJc : J.card = c) (α : Fin d → ℕ) (hα : ∀ i ∉ J, α i = 0) (μ : ℝ) :
    IntegrableOn (fun w : {i // ¬ inJ J i} → ℝ =>
      pdMulti α (lJ J) A (glue J 0 w) * mono (fun i : {i // ¬ inJ J i} => h i) w *
        mono (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (-μ) *
        logSum (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ 0) (box {i // ¬ inJ J i} b) := by
  classical
  -- the wall set of the face box and its image in the closed box
  set B : Set ({i // ¬ inJ J i} → ℝ) :=
    (Set.pi univ fun _ => Icc (0 : ℝ) b) ∩ ⋃ i : {i // ¬ inJ J i}, {w | w i = 0} with hB
  have hBc : IsCompact B :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_apply i) continuous_const)
  have hK₀ : IsCompact (glue J 0 '' B) := hBc.image (continuous_glue_zero J)
  have hK₀O : glue J 0 '' B ⊆ O := by
    rintro v ⟨w, ⟨hwbox, hwz⟩, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hwz
    have hiJ : i.1 ∉ J := fun h => i.2 (inJ_iff.2 h)
    refine hdeep (mem_deepSet_of_zeros (glue_zero_mem_closedBox_of_mem_Icc hb.le hwbox)
      (J := insert i.1 J) ?_ ?_)
    · rw [Finset.card_insert_of_notMem hiJ, hJc]
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rw [glue_apply_of_not_mem J _ _ hiJ]
        exact hi
      · rw [glue_apply_of_mem J _ _ hj]
        rfl
  obtain ⟨δ, hδ, hthick⟩ := hK₀.exists_thickening_subset_open hO hK₀O
  obtain ⟨M₀, hM₀⟩ := exists_rect_bound hA α b
  have hM₀0 : 0 ≤ M₀ :=
    (abs_nonneg _).trans (hM₀ α (fun _ => le_rfl) 0 fun _ => ⟨le_rfl, hb.le⟩)
  set p : {i // ¬ inJ J i} → ℕ := fun i => ⌈2 * (k i : ℝ) * μ⌉₊ + 1 with hp
  have hμ : ∀ i : {i // ¬ inJ J i}, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1 := by
    intro i
    have h1 := Nat.le_ceil (2 * (k i : ℝ) * μ)
    have h2 : (0 : ℝ) ≤ h i := Nat.cast_nonneg _
    simp only [hp]
    push_cast
    linarith
  have hδp : 0 < δ ^ (∑ i, p i) := pow_pos hδ _
  have hderiv : ∀ w : {i // ¬ inJ J i} → ℝ,
      pdMulti α (lJ J) A (glue J 0 w) = pdMulti α (List.finRange d) A (glue J 0 w) := fun w => by
    rw [pdMulti_lJ_eq_finRange_of_zero_off hA J α hα]
  refine integrable_faceCoeff hb (M := M₀ / δ ^ (∑ i, p i)) (p := p) ?_ ?_ hμ le_rfl
  · exact ((contDiff_pdMulti hA α (lJ J)).continuous.comp
      (continuous_glue_zero J)).aestronglyMeasurable
  · intro w hw
    have hwIcc : ∀ j, glue J 0 w j ∈ Icc 0 b := fun j => glue_zero_mem_Icc J hb hw j
    by_cases hcol : ∃ i : {i // ¬ inJ J i}, w i < δ
    · -- the collar: the derivative vanishes
      obtain ⟨i, hi⟩ := hcol
      have hiJ : i.1 ∉ J := fun h => i.2 (inJ_iff.2 h)
      have hvO : glue J 0 w ∈ O := by
        refine hthick (Metric.mem_thickening_iff.2
          ⟨glue J 0 (Function.update w i 0), ⟨Function.update w i 0, ⟨?_, ?_⟩, rfl⟩, ?_⟩)
        · intro j _
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
            exact ⟨le_rfl, hb.le⟩
          · rw [Function.update_of_ne hji]
            exact Ioc_subset_Icc_self (hw j (Set.mem_univ j))
        · exact Set.mem_iUnion.2 ⟨i, Function.update_self ..⟩
        · rw [dist_pi_lt_iff hδ]
          intro j
          by_cases hjJ : j ∈ J
          · rw [glue_apply_of_mem J _ _ hjJ, glue_apply_of_mem J _ _ hjJ, dist_self]
            exact hδ
          · rw [glue_apply_of_not_mem J _ _ hjJ, glue_apply_of_not_mem J _ _ hjJ]
            by_cases hji : (⟨j, fun h => hjJ (inJ_iff.1 h)⟩ : {i // ¬ inJ J i}) = i
            · rw [hji, Function.update_self, Real.dist_eq, sub_zero,
                abs_of_pos (hw i (Set.mem_univ i)).1]
              exact hi
            · rw [Function.update_of_ne hji, dist_self]
              exact hδ
      have hv0 : pdMulti α (lJ J) A (glue J 0 w) = 0 := by
        rw [hderiv]
        exact pdMulti_eq_zero_of_eqOn_inter_closedBox hA hb hO hAO
          ⟨hvO, mem_closedBox.2 hwIcc⟩ α
      rw [hv0, abs_zero]
      exact mul_nonneg (div_nonneg hM₀0 hδp.le) (mono_nonneg_of_mem_box hw p)
    · -- off the collar: the derivative is bounded and the weight is bounded below
      have hcol' : ∀ i : {i // ¬ inJ J i}, δ ≤ w i := fun i =>
        le_of_not_gt fun hlt => hcol ⟨i, hlt⟩
      have hbound : |pdMulti α (lJ J) A (glue J 0 w)| ≤ M₀ := by
        rw [hderiv]
        exact hM₀ α (fun _ => le_rfl) _ hwIcc
      have hmono : δ ^ (∑ i, p i) ≤ mono p w := by
        unfold mono
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod (fun i _ => pow_nonneg hδ.le _)
          fun i _ => pow_le_pow_left₀ hδ.le (hcol' i) _
      calc |pdMulti α (lJ J) A (glue J 0 w)| ≤ M₀ := hbound
        _ = M₀ / δ ^ (∑ i, p i) * δ ^ (∑ i, p i) := (div_mul_cancel₀ _ hδp.ne').symm
        _ ≤ M₀ / δ ^ (∑ i, p i) * mono p w :=
          mul_le_mul_of_nonneg_left hmono (div_nonneg hM₀0 hδp.le)

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The piece amplitude vanishes on a neighbourhood of the deep set (relative to the closed box)
when `F` vanishes near the deep zero fibre. -/
theorem exists_open_amp_zero {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ∃ O : Set (Fin ((Ξ.X Y).da p) → ℝ), IsOpen O ∧ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c ⊆ O ∧
      ∀ v ∈ O ∩ closedBox _ (Y.T.a p.1), (Ξ.amp Y p).amp s v = 0 := by
  refine ⟨{u | ∀ᶠ u' in 𝓝 u, u' ∈ closedBox _ (Y.T.a p.1) → (Ξ.amp Y p).amp s u' = 0},
    isOpen_setOfPred_eventually_nhds, fun v hv => ?_, fun v hv => hv.1.self_of_nhds hv.2⟩
  obtain ⟨hvbox, hcard⟩ := hv
  have hvJ : ∀ i ∈ (univ : Finset (Fin ((Ξ.X Y).da p))).filter (fun i => v i = 0), v i = 0 :=
    fun i hi => (mem_filter.1 hi).2
  have h1 := Ξ.Gloc_eventually_zero_deep Y hF p s _ hcard hvbox hvJ
  have h2 : ∀ᶠ u' in 𝓝 v, Ξ.Gloc Y p.1 (Ξ.facePt Y p s u') = 0 :=
    (Ξ.continuous_facePt Y p s).continuousAt.eventually h1
  filter_upwards [h2] with u' hu' hbox
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hbox)]
  exact hu'

/-- ★★ **Every face integral of the stratum sum is absolutely convergent.** -/
theorem integrableOn_pieceStratum_integrand {c : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (J : Finset (Fin ((Ξ.X Y).da p)))
    (hJc : J.card = c) (μ : ℝ) :
    IntegrableOn (fun w : {i // ¬ inJ J i} → ℝ =>
      pdMulti (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) (lJ J) ((Ξ.amp Y p).amp s)
          (glue J 0 w) *
        mono (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) w *
        mono (fun i : {i // ¬ inJ J i} => 2 * (Ξ.X Y).kA p i) w ^ (-μ) *
        logSum (fun i : {i // ¬ inJ J i} => 2 * (Ξ.X Y).kA p i) w ^ 0)
      (box {i // ¬ inJ J i} (Y.T.a p.1)) := by
  obtain ⟨O, hO, hdeep, hAO⟩ := Ξ.exists_open_amp_zero Y hF p s
  exact integrableOn_stratum_integrand ((Ξ.amp Y p).smooth s) _ _ (Y.T.a_pos p.1) hO hAO hdeep J
    hJc _ (fun i hi => resOrder_of_not_mem hi) μ

end ResolvedData

end SmoothEngine

end Grammar
