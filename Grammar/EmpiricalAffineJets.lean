/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalUniform
import Grammar.EmpiricalMellinJet
import Grammar.EmpiricalBoxScaling
import Grammar.SmoothAffineFamily
import Grammar.ParametricFaceAmplitude

/-!
# The empirical field family of a chart piece: jets, uniform jet bounds, joint smoothness
(§20 Stage 7, part 1)

A chart piece presents its amplitude as `G ∘ A_s` with `G` smooth on the chart coordinate space
and `A_s = affineMap e σ (sc s)` the affine chart map of the piece (face coordinates reflected by
`σ`, complementary coordinates at the base point `s`). A SMOOTH root field is one whose branch
representative is likewise `Lψ ∘ A_s` with `Lψ` smooth on the chart coordinate space. After the
dilation of the box `(0,b]^{da}` to the unit box the empirical field family of the piece is
`fieldFam (G ∘ A_s ∘ b) (Lψ ∘ A_s ∘ b) τ = (fieldFam G Lψ τ) ∘ A_s ∘ b`.

This file provides the three inputs of the resolved assembly: the coordinate jets of the piece
family are the reflected, dilated ambient jets (`pdMulti_comp_smul`, ★ `pdMulti_pieceFam`); the
rectangular jet bound holds UNIFORMLY over a compact base (★★ `exists_fieldJetBound_pieceFam`,
from the jet bound of the ambient family on the compact image of base × box); and the face
amplitudes of the piece family are jointly continuous in (base point, coupling, complementary
coordinates) (★ `continuous_faceAmp_pieceFam`), by the joint smoothness of the parametrised face
amplitude with the parameter `(τ, sc s)`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Coordinate jets under a dilation -/

section Smul

variable {n : ℕ}

theorem smul_update (b : ℝ) (v : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    b • Function.update v i t = Function.update (b • v) i (b * t) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem pd_comp_smul (F : (Fin n → ℝ) → ℝ) (b : ℝ) (i : Fin n) :
    pd i (fun v => F (b • v)) = fun v => b * pd i F (b • v) := by
  funext v
  have hl : line (fun v => F (b • v)) i v = fun t => line F i (b • v) (b * t) := by
    funext t
    simp only [line, smul_update]
  change deriv (line (fun v => F (b • v)) i v) (v i) = _
  rw [hl, deriv_comp_mul_left, smul_eq_mul]
  simp only [pd, Pi.smul_apply, smul_eq_mul]

theorem pdPow_comp_smul (F : (Fin n → ℝ) → ℝ) (b : ℝ) (i : Fin n) (q : ℕ) :
    pdPow i q (fun v => F (b • v)) = fun v => b ^ q * pdPow i q F (b • v) := by
  induction q with
  | zero => funext v; simp [pdPow_zero]
  | succ q ih =>
    rw [pdPow_succ', ih, pd_const_mul, pd_comp_smul, pdPow_succ']
    funext v
    ring

theorem pdMulti_comp_smul (F : (Fin n → ℝ) → ℝ) (b : ℝ) (m : Fin n → ℕ) (l : List (Fin n)) :
    pdMulti m l (fun v => F (b • v)) = fun v => b ^ wordLen m l * pdMulti m l F (b • v) := by
  induction l with
  | nil => funext v; simp [pdMulti_nil, wordLen]
  | cons i l ih =>
    rw [pdMulti_cons, ih, pdPow_const_mul, pdPow_comp_smul, pdMulti_cons, wordLen_cons]
    funext v
    rw [pow_add]
    ring

end Smul

/-! ### The piece field family -/

variable {d da : ℕ} {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
  (σ : WaterFilling.CoordSign d)

variable (G Lψ : (Fin d → ℝ) → ℝ) (b : ℝ)

/-- The dilated affine chart map `v ↦ A_c (b v)`. -/
def pieceMap (c : {i // ¬ inJ J i} → ℝ) (v : Fin da → ℝ) : Fin d → ℝ := affineMap e σ c (b • v)

/-- The piece amplitude on the unit box: `G ∘ A_c ∘ b`. -/
def pieceAmp (c : {i // ¬ inJ J i} → ℝ) : (Fin da → ℝ) → ℝ := fun v => G (pieceMap e σ b c v)

theorem fieldFam_pieceAmp (c : {i // ¬ inJ J i} → ℝ) (τ : ℝ) :
    fieldFam (pieceAmp e σ G b c) (pieceAmp e σ Lψ b c) τ =
      fun v => fieldFam G Lψ τ (pieceMap e σ b c v) := rfl

theorem contDiff_pieceAmp (hG : ContDiff ℝ ∞ G) (c : {i // ¬ inJ J i} → ℝ) :
    ContDiff ℝ ∞ (pieceAmp e σ G b c) :=
  hG.comp ((contDiff_affineMap e σ c).comp (contDiff_id.const_smul b))

/-- The word length of the extended multi-index over the face list is the word length of `m`. -/
theorem wordLen_extendIdx (m : Fin da → ℕ) :
    wordLen (extendIdx e m) ((List.finRange da).map fun j => (e j).1) =
      wordLen m (List.finRange da) := by
  rw [wordLen_eq_sum_map, wordLen_eq_sum_map, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [Function.comp, extendIdx_face]

/-- ★ **The jets of the piece family** are the reflected, dilated ambient jets:
`∂^m (F ∘ A_c ∘ b) = b^{|m|} (∏ σ^m) (∂^{ext m} F) ∘ A_c ∘ b`. -/
theorem pdMulti_pieceMap (F : (Fin d → ℝ) → ℝ) (c : {i // ¬ inJ J i} → ℝ) (m : Fin da → ℕ) :
    pdMulti m (List.finRange da) (fun v => F (pieceMap e σ b c v)) =
      fun v => b ^ wordLen m (List.finRange da) * (∏ j, WaterFilling.sgn σ (e j).1 ^ m j) *
        pdMulti (extendIdx e m) ((List.finRange da).map fun j => (e j).1) F
          (pieceMap e σ b c v) := by
  funext v
  have h2 := congrFun (pdMulti_comp_smul (fun u => F (affineMap e σ c u)) b m (List.finRange da)) v
  have h3 := congrFun (pdMulti_finRange_comp_affineMap e σ c F m) (b • v)
  change pdMulti m (List.finRange da) (fun v => (fun u => F (affineMap e σ c u)) (b • v)) v = _
  rw [h2, h3]
  simp only [pieceMap]
  ring

/-! ### The uniform jet bound over a compact base -/

variable {S : Type*} [TopologicalSpace S] [CompactSpace S] {sc : S → {i // ¬ inJ J i} → ℝ}

/-- The compact image of base × closed unit box under the dilated chart maps. -/
theorem isCompact_pieceMap_image (hsc : Continuous sc) :
    IsCompact ((fun z : S × (Fin da → ℝ) => pieceMap e σ b (sc z.1) z.2) ''
      (Set.univ ×ˢ closedBox da 1)) := by
  refine (isCompact_univ.prod (isCompact_closedBox 1)).image ?_
  exact (continuous_affineMap_pair e σ).comp
    ((hsc.comp continuous_fst).prodMk (continuous_snd.const_smul b))

/-- ★★ **The uniform rectangular jet bound of the piece family**: one constant `C` and one field
bound `M'` for all base points. -/
theorem exists_fieldJetBound_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (p : Fin da → ℕ) :
    ∃ C M' : ℝ, 0 ≤ C ∧ ∀ s,
      FieldJetBound (pieceAmp e σ G b (sc s)) (pieceAmp e σ Lψ b (sc s)) p 1 C M' := by
  set K := (fun z : S × (Fin da → ℝ) => pieceMap e σ b (sc z.1) z.2) '' (Set.univ ×ˢ closedBox da 1)
    with hK
  have hKc : IsCompact K := isCompact_pieceMap_image e σ b hsc
  obtain ⟨M', hM'⟩ := hKc.exists_bound_of_continuousOn hLψ.continuous.continuousOn
  have hζM : ∀ z ∈ K, |Lψ z| ≤ M' := fun z hz => by simpa [Real.norm_eq_abs] using hM' z hz
  -- the jets of the ambient family, bounded on `K`
  have hjet : ∀ m : Fin da → ℕ, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ K,
      |pdMulti (extendIdx e m) ((List.finRange da).map fun j => (e j).1) (fieldFam G Lψ τ) z| ≤
        Cm * (1 + τ) ^ (0 + wordLen (extendIdx e m) ((List.finRange da).map fun j => (e j).1)) *
          exp (M' * τ) :=
    fun m => ((isJet_fieldFam hG).pdMulti hLψ (extendIdx e m) _).bound_of_isCompact hKc hζM
  choose Cm hCm0 hCm using hjet
  have hS0 : 0 ≤ ∑ m ∈ Fintype.piFinset (fun i => range (p i + 1)), Cm m :=
    Finset.sum_nonneg fun m' _ => hCm0 m'
  refine ⟨(∑ m ∈ Fintype.piFinset (fun i => range (p i + 1)), Cm m) * |b| ^ (∑ i, p i) +
    ∑ m ∈ Fintype.piFinset (fun i => range (p i + 1)), Cm m, M',
    add_nonneg (mul_nonneg hS0 (by positivity)) hS0, fun s => ?_⟩
  intro m hm τ hτ v hv
  have hmem : m ∈ Fintype.piFinset (fun i => range (p i + 1)) :=
    Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hm i))
  have hzK : pieceMap e σ b (sc s) v ∈ K := ⟨(s, v), ⟨Set.mem_univ _, hv⟩, rfl⟩
  have hwl : wordLen m (List.finRange da) ≤ ∑ i, p i := by
    rw [wordLen_eq_sum_toFinset m (List.nodup_finRange da), List.toFinset_finRange]
    exact Finset.sum_le_sum fun i _ => hm i
  have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith
  have hCsum : Cm m ≤ ∑ m' ∈ Fintype.piFinset (fun i => range (p i + 1)), Cm m' :=
    Finset.single_le_sum (fun m' _ => hCm0 m') hmem
  rw [fieldFam_pieceAmp, pdMulti_pieceMap, abs_mul, abs_mul, abs_pow]
  have hsgn : |∏ j, WaterFilling.sgn σ (e j).1 ^ m j| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun j _ => abs_nonneg _) fun j _ => ?_
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by unfold WaterFilling.sgn; split_ifs <;> simp)
  have hjb := hCm m τ hτ _ hzK
  rw [zero_add, wordLen_extendIdx] at hjb
  -- `|b|^{|m|} ≤ |b|^{Σp} + 1` (whether `|b| ≤ 1` or not)
  have hbpow : |b| ^ wordLen m (List.finRange da) ≤ |b| ^ (∑ i, p i) + 1 := by
    rcases le_or_gt |b| 1 with hb1 | hb1
    · have : |b| ^ wordLen m (List.finRange da) ≤ 1 := pow_le_one₀ (abs_nonneg _) hb1
      linarith [pow_nonneg (abs_nonneg b) (∑ i, p i)]
    · have := pow_le_pow_right₀ hb1.le hwl
      linarith
  have hpow : (1 + τ) ^ wordLen m (List.finRange da) ≤ (1 + τ) ^ (∑ i, p i) :=
    pow_le_pow_right₀ h1τ hwl
  calc |b| ^ wordLen m (List.finRange da) * |∏ j, WaterFilling.sgn σ (e j).1 ^ m j| *
        |pdMulti (extendIdx e m) ((List.finRange da).map fun j => (e j).1) (fieldFam G Lψ τ)
          (pieceMap e σ b (sc s) v)|
      ≤ (|b| ^ (∑ i, p i) + 1) * 1 *
          (Cm m * (1 + τ) ^ wordLen m (List.finRange da) * exp (M' * τ)) := by
        gcongr
    _ ≤ (|b| ^ (∑ i, p i) + 1) * 1 *
          ((∑ m' ∈ Fintype.piFinset (fun i => range (p i + 1)), Cm m') * (1 + τ) ^ (∑ i, p i) *
            exp (M' * τ)) := by
        gcongr
    _ = _ := by ring

/-! ### Joint continuity of the face amplitudes of the piece family -/

/-- The ambient family of the piece, jointly smooth in the parameter `(τ, c)` and the face
coordinates. -/
theorem contDiff_pieceJoint (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ) :
    ContDiff ℝ ∞ fun z : (ℝ × ({i // ¬ inJ J i} → ℝ)) × (Fin da → ℝ) =>
      fieldFam G Lψ z.1.1 (pieceMap e σ b z.1.2 z.2) := by
  have h1 : ContDiff ℝ ∞ fun z : (ℝ × ({i // ¬ inJ J i} → ℝ)) × (Fin da → ℝ) =>
      (z.1.1, pieceMap e σ b z.1.2 z.2) := by
    refine (contDiff_fst.comp contDiff_fst).prodMk ?_
    have h2 : ContDiff ℝ ∞ fun z : (ℝ × ({i // ¬ inJ J i} → ℝ)) × (Fin da → ℝ) =>
        (z.1.2, b • z.2) :=
      (contDiff_snd.comp contDiff_fst).prodMk (contDiff_snd.const_smul b)
    exact (contDiff_affineMap_pair e σ).comp h2
  exact (contDiff_fieldFam_joint hG hLψ).comp h1

omit [CompactSpace S] in
/-- ★ **Joint continuity of the piece face amplitudes** in (base point, coupling, complementary
coordinates), for every engine face `F ⊆ Fin da` and multi-index `m`. -/
theorem continuous_faceAmp_pieceFam (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ)
    (hsc : Continuous sc) (p : Fin da → ℕ) (F : Finset (Fin da)) (m : Fin da → ℕ) :
    Continuous fun z : S × ℝ × ({i // ¬ inJ F i} → ℝ) =>
      faceAmp p F (fieldFam (pieceAmp e σ G b (sc z.1)) (pieceAmp e σ Lψ b (sc z.1)) z.2.1) m
        z.2.2 := by
  have hjoint := contDiff_faceAmp_slice (B := ℝ × ({i // ¬ inJ J i} → ℝ))
    (G := fun z : (ℝ × ({i // ¬ inJ J i} → ℝ)) × (Fin da → ℝ) =>
      fieldFam G Lψ z.1.1 (pieceMap e σ b z.1.2 z.2)) (contDiff_pieceJoint e σ G Lψ b hG hLψ) p F m
  have hf : Continuous fun z : S × ℝ × ({i // ¬ inJ F i} → ℝ) => ((z.2.1, sc z.1), z.2.2) :=
    (continuous_snd.fst.prodMk (hsc.comp continuous_fst)).prodMk continuous_snd.snd
  exact hjoint.continuous.comp hf

omit [CompactSpace S] in
/-- The piece face amplitudes are jointly measurable in `(base point, complementary coordinates,
coupling)` — the shape required by the coefficient measurability lemmas. -/
theorem measurable_faceAmp_pieceFam [MeasurableSpace S] [OpensMeasurableSpace S]
    (hG : ContDiff ℝ ∞ G) (hLψ : ContDiff ℝ ∞ Lψ) (hsc : Continuous sc) (p : Fin da → ℕ)
    (F : Finset (Fin da)) (m : Fin da → ℕ) :
    Measurable (Function.uncurry fun (z : S × ({i // ¬ inJ F i} → ℝ)) (τ : ℝ) =>
      faceAmp p F (fieldFam (pieceAmp e σ G b (sc z.1)) (pieceAmp e σ Lψ b (sc z.1)) τ) m z.2) := by
  have hf : Continuous fun q : (S × ({i // ¬ inJ F i} → ℝ)) × ℝ => (q.1.1, q.2, q.1.2) :=
    continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)
  exact ((continuous_faceAmp_pieceFam e σ G Lψ b hG hLψ hsc p F m).comp hf).measurable

end SmoothEngine

end Grammar
