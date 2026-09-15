/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothExactResonance
import Grammar.SmoothRemainderIdentity

/-!
# The face-sum collapse at the top logarithmic power

Consult #130, Unit E1d. For an amplitude `A` whose jets vanish on the DEEP SET of the closed box
(the points with at least `c + 1` vanishing coordinates, `deepSet`), the engine coefficient at
`(μ, c − 1)` collapses to a sum over the faces `J` of size exactly `c`, each contributing ONE term:
the resonant Taylor order `α_J` (`resOrder`, `α_j = 2k_jμ − h_j − 1` on `J`), the top face
coefficient `faceCoef k β b J (α_J + h) μ (c−1)` (zero unless every coordinate of `J` resonates
exactly, CDXLIV), and the honest face integral of the normal derivative `∂_J^{α_J} A` on the face
`{u_J = 0}` against the power weight `∏_{i∉J} w_i^{h_i} (∏_{i∉J} w_i^{2k_i})^{−μ}` — no logarithmic
factor and no Taylor subtraction (★★★ `smoothCoeff_eq_faceSum_top`). Faces of size `< c` have an
empty top-log range or a pole of order below `c`; faces of size `> c` have vanishing face amplitude;
at size `c` only the log index `c − 1` and only the Taylor order `α_J` survive
(`faceCoef_top_eq_zero_of_not_exact`), and the Taylor remainder in the complementary coordinates is
the identity (`remList_eq_self_of_jetsZeroOn`). The depth certificate `α_j < p_j` holds because the
engine's depth at the cutoff `L > μ` is `2k_jL − h_j`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

open MonoRep CoeffFamily

variable {d : ℕ}

/-- The deep set: points of the closed box with at least `c + 1` vanishing coordinates. -/
def deepSet (d : ℕ) (b : ℝ) (c : ℕ) : Set (Fin d → ℝ) :=
  {v ∈ closedBox d b | c + 1 ≤ (univ.filter fun i => v i = 0).card}

theorem deepSet_update {b : ℝ} (hb : 0 ≤ b) {c : ℕ} :
    ∀ v ∈ deepSet d b c, ∀ i, Function.update v i 0 ∈ deepSet d b c := by
  intro v hv i
  refine ⟨?_, ?_⟩
  · rw [mem_closedBox]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact ⟨le_rfl, hb⟩
    · rw [Function.update_of_ne hj]
      exact (mem_closedBox.1 hv.1) j
  · refine hv.2.trans (Finset.card_le_card fun j hj => ?_)
    rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, ?_⟩
    by_cases hji : j = i
    · subst hji
      exact Function.update_self ..
    · rw [Function.update_of_ne hji]
      exact hj.2

theorem mem_deepSet_of_zeros {b : ℝ} {c : ℕ} {v : Fin d → ℝ} (hv : v ∈ closedBox d b)
    {J : Finset (Fin d)} (hJc : c + 1 ≤ J.card) (hJ : ∀ i ∈ J, v i = 0) : v ∈ deepSet d b c :=
  ⟨hv, hJc.trans (Finset.card_le_card fun i hi => mem_filter.2 ⟨mem_univ _, hJ i hi⟩)⟩

/-- The resonant Taylor order of a face: `α_j = 2k_jμ − h_j − 1` on `J`, `0` off `J`. -/
noncomputable def resOrder (h k : Fin d → ℕ) (μ : ℝ) (J : Finset (Fin d)) : Fin d → ℕ :=
  fun j => if j ∈ J then ⌊2 * (k j : ℝ) * μ⌋₊ - h j - 1 else 0

theorem resOrder_eq_of_exact {h k : Fin d → ℕ} {μ : ℝ} {J : Finset (Fin d)} {m : Fin d → ℕ}
    {j : Fin d} (hj : j ∈ J) (hres : 2 * (k j : ℝ) * μ = m j + h j + 1) :
    resOrder h k μ J j = m j := by
  unfold resOrder
  rw [if_pos hj]
  have : (2 * (k j : ℝ) * μ) = ((m j + h j + 1 : ℕ) : ℝ) := by
    push_cast
    exact hres
  rw [this, Nat.floor_natCast]
  omega

theorem resOrder_of_not_mem {h k : Fin d → ℕ} {μ : ℝ} {J : Finset (Fin d)} {j : Fin d}
    (hj : j ∉ J) : resOrder h k μ J j = 0 := by
  unfold resOrder
  rw [if_neg hj]

theorem card_subtype_inJ (J : Finset (Fin d)) : Fintype.card {i // inJ J i} = J.card := by
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp [inJ_iff]

theorem DJ_eq (J : Finset (Fin d)) : DJ J = J.card - 1 := by
  unfold DJ
  rw [card_subtype_inJ]

theorem faceCoeffInt_congr_box {ι : Type*} [Fintype ι] {G G' : (ι → ℝ) → ℝ} (h a : ι → ℕ)
    (b μ : ℝ) (e : ℕ) (hG : ∀ w ∈ box ι b, G w = G' w) :
    faceCoeffInt G h a b μ e = faceCoeffInt G' h a b μ e := by
  unfold faceCoeffInt
  exact setIntegral_congr_fun (measurableSet_box b) fun w hw => by rw [hG w hw]

/-- The face coefficient vanishes at log degrees `≥ |J|` (the pole order is at most `|J|`). -/
theorem faceCoef_eq_zero_of_card_le (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β)
    (hb : 0 < b) (J : Finset (Fin d)) (e : Fin d → ℕ) (μ : ℝ) {j : ℕ} (hj : J.card ≤ j) :
    faceCoef k β b J e μ j = 0 := by
  unfold faceCoef
  by_cases hJ : J.Nonempty
  · rw [dif_pos hJ]
    have := nonempty_subtype_inJ hJ
    have hcard : exactCount (fun i : {i // inJ J i} => k i) (fun i => e i) μ ≤ j := by
      refine le_trans ?_ hj
      unfold exactCount
      exact (Finset.card_le_univ _).trans (card_subtype_inJ J).le
    exact faceMonoCoeff_eq_zero_of_exactCount_le (fun i : {i // inJ J i} => k i) (fun i => e i)
      (fun i => hk i.1) hβ hb hcard
  · rw [dif_neg hJ]

theorem mem_idxL_iff {p : Fin d → ℕ} {l : List (Fin d)} {m : Fin d → ℕ} :
    m ∈ idxL p l ↔ ∀ i, m i ∈ (if i ∈ l then Finset.range (p i) else {0}) := by
  unfold idxL
  exact Fintype.mem_piFinset

/-- ★★★ **The face-sum collapse at the top logarithmic power**: for an amplitude whose jets vanish
on the deep set `{≥ c+1 vanishing coordinates}`, the `(μ, c−1)` coefficient is the sum over the
faces of size `c` of `faceW · faceCoef · ∫_{face} ∂_J^{α_J} A · (power weight)`. -/
theorem smoothCoeff_eq_faceSum_top {A : (Fin d → ℝ) → ℝ} (hA : ContDiff ℝ ∞ A)
    (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) {c : ℕ}
    (hc : 1 ≤ c) (hdeep : JetsZeroOn A (deepSet d b c)) :
    smoothCoeff A h k β b μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (faceCoef k β b J (fun i => resOrder h k μ J i + h i) μ (c - 1) *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) b μ 0) := by
  classical
  have hμL : μ < cutoffOf h μ := lt_cutoffOf h μ
  unfold smoothCoeff smoothCoeffAtDepth faceIndex
  rw [Finset.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  rcases lt_trichotomy J.card c with hlt | heq | hgt
  · -- faces of size `< c`: the pole order is below the log degree
    rw [if_neg hlt.ne]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro j hj
    have hj' : c - 1 ≤ j := (Finset.mem_Ico.1 hj).1
    rw [faceCoef_eq_zero_of_card_le k hk hβ hb J _ μ (by omega), zero_mul, zero_mul]
  · -- faces of size `c`
    rw [if_pos heq]
    have hDJ : DJ J = c - 1 := by rw [DJ_eq, heq]
    have hIco : Finset.Ico (c - 1) (DJ J + 1) = {c - 1} := by
      rw [hDJ, Nat.sub_add_cancel hc, Nat.Ico_pred_singleton hc]
    simp_rw [hIco, Finset.sum_singleton, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self]
    -- exact resonance of a Taylor order forces it to be the resonant order
    have hexact : ∀ m : Fin d → ℕ, m ∈ idxL (depthOf h k (cutoffOf h μ)) (lJ J) →
        (∀ j ∈ J, 2 * (k j : ℝ) * μ = m j + h j + 1) → m = resOrder h k μ J := by
      intro m hm hres
      funext j
      by_cases hj : j ∈ J
      · exact (resOrder_eq_of_exact hj (hres j hj)).symm
      · rw [resOrder_of_not_mem hj]
        have := (mem_idxL_iff.1 hm) j
        rw [if_neg (by rwa [mem_lJ])] at this
        exact Finset.mem_singleton.1 this
    -- a face coefficient at the top log power vanishes unless the order is exactly resonant
    have hzero : ∀ m : Fin d → ℕ, (∃ j ∈ J, 2 * (k j : ℝ) * μ ≠ m j + h j + 1) →
        faceCoef k β b J (fun i => m i + h i) μ (c - 1) = 0 := by
      rintro m ⟨j, hj, hne⟩
      rw [← hDJ]
      exact faceCoef_top_eq_zero_of_not_exact k hk hβ hb J (fun i => m i + h i) hj
        (by push_cast; exact hne)
    rw [Finset.sum_eq_single (resOrder h k μ J)]
    · -- the surviving term: the remainder is the identity on the face
      congr 1
      congr 1
      refine faceCoeffInt_congr_box _ _ _ _ _ fun w hw => ?_
      unfold faceAmp
      refine remList_eq_self_of_jetsZeroOn _ (deepSet_update hb.le) (lK J) (nodup_lK J) _
        (contDiff_pdMulti hA _ (lJ J)) (hdeep.pdMulti hA _ (lJ J)) _ fun i hi => ?_
      have hiJ : i ∉ J := (mem_lK J).1 hi
      refine mem_deepSet_of_zeros ?_ (J := insert i J) ?_ ?_
      · rw [mem_closedBox]
        intro j
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          exact ⟨le_rfl, hb.le⟩
        · rw [Function.update_of_ne hji]
          exact glue_zero_mem_Icc J hb hw j
      · rw [Finset.card_insert_of_notMem hiJ, heq]
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact Function.update_self ..
        · have hji : j ≠ i := fun h' => hiJ (h' ▸ hj)
          rw [Function.update_of_ne hji, glue_apply_of_mem J _ _ hj]
          rfl
    · -- other Taylor orders: some coordinate fails exact resonance
      intro m hm hne
      rw [hzero m, zero_mul, mul_zero]
      by_contra hall
      exact hne (hexact m hm fun j hj => by_contra fun hne' => hall ⟨j, hj, hne'⟩)
    · -- the resonant order lies in the index set whenever it resonates exactly
      intro hnot
      rw [hzero _, zero_mul, mul_zero]
      by_contra hall
      have hall' : ∀ i ∈ J, 2 * (k i : ℝ) * μ = resOrder h k μ J i + h i + 1 :=
        fun i hi => by_contra fun hne' => hall ⟨i, hi, hne'⟩
      refine hnot (mem_idxL_iff.2 fun i => ?_)
      by_cases hi : i ∈ J
      · rw [if_pos ((mem_lJ J).2 hi), Finset.mem_range]
        have hres := hall' i hi
        have hkL : ((resOrder h k μ J i + h i + 1 : ℕ) : ℝ) < 2 * k i * (cutoffOf h μ : ℕ) := by
          push_cast
          rw [← hres]
          have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
            have := Nat.cast_pos (α := ℝ) |>.2 (hk i)
            positivity
          exact mul_lt_mul_of_pos_left hμL hk'
        have hkL' : resOrder h k μ J i + h i + 1 < 2 * k i * cutoffOf h μ := by
          exact_mod_cast hkL
        unfold depthOf
        omega
      · rw [if_neg (by rwa [mem_lJ]), Finset.mem_singleton]
        exact resOrder_of_not_mem hi
  · -- faces of size `> c`: the face amplitude vanishes
    rw [if_neg hgt.ne']
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ (faceAmp_eq_zero_of_jets_zero _ J hA m hb
      fun v hv hvJ α => hdeep α v (mem_deepSet_of_zeros hv (by omega) hvJ)), mul_zero]

end SmoothEngine

end Grammar
