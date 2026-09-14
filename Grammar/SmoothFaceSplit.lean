/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceOperators
import Grammar.SmoothTwoDim

/-!
# The face split of the smooth engine (consult #116 §1.2, §3.3)

For a Taylor set `J ⊆ Fin d` with complement `K`, the box `(0,b]^d` splits as
`(0,b]^J × (0,b]^K` (`glue`, `integral_box_split`, Fubini with the `K`-variables outside), and
the face-`J` term of the subset formula integrates to a finite sum of ONE-FLAT-COMPLEMENT face
integrals ★ `faceTerm_integral`:
`∫ (T_J R_K F)(v) v^h e^{−Nβ v^{2k}} dv = ∑_{m ∈ idxL J} (∏_{i∈J} 1/m_i!) ·`
`  ∫_{(0,b]^K} G_{J,m}(w) w^{h_K} · Z^J_{m+h}(N w^{2k_K}) dw`,
with the flat face amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)` (`faceAmp`) and the inner face
monomial integral `Z^J_e(t) = ∫_{(0,b]^J} u^e e^{−βt u^{2k}} du`. The amplitude is flat of
order `p` in the `K`-variables (`faceAmp_bound`, from `remList_bound` and the rectangular
mixed-derivative bound, via permutation invariance of iterated coordinate derivatives
`pdMulti_perm`) — exactly the outer amplitude of the generic face theorem. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Iterated coordinate derivatives: congruence, append, permutation -/

variable (p : Fin d → ℕ)

theorem pdList_eq_pdMulti (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    pdList p l G = pdMulti p l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih => rw [pdList_cons, pdMulti_cons, ih]

theorem pdMulti_congr {m m' : Fin d → ℕ} {l : List (Fin d)} (h : ∀ i ∈ l, m i = m' i)
    (G : (Fin d → ℝ) → ℝ) : pdMulti m l G = pdMulti m' l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdMulti_cons, h i (List.mem_cons_self ..),
      ih (fun j hj => h j (List.mem_cons_of_mem i hj))]

theorem pdMulti_append (m : Fin d → ℕ) (l l' : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    pdMulti m (l ++ l') G = pdMulti m l (pdMulti m l' G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih => rw [List.cons_append, pdMulti_cons, pdMulti_cons, ih]

/-- Iterated coordinate derivatives of a smooth function do not depend on the order. -/
theorem pdMulti_perm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ)
    {l l' : List (Fin d)} (hl : l.Perm l') : pdMulti m l G = pdMulti m l' G := by
  induction hl generalizing G with
  | nil => rfl
  | cons i _ ih => rw [pdMulti_cons, pdMulti_cons, ih hG]
  | swap i j l =>
    rw [pdMulti_cons, pdMulti_cons, pdMulti_cons, pdMulti_cons,
      pdPow_comm (contDiff_pdMulti (m := m) hG l)]
  | trans _ _ ih₁ ih₂ => rw [ih₁ hG, ih₂ hG]

theorem pdMulti_remList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ)
    {l l' : List (Fin d)} (hdisj : ∀ i ∈ l, i ∉ l') :
    pdMulti m l (remList p l' G) = remList p l' (pdMulti m l G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdMulti_cons, ih hG (fun j hj => hdisj j (List.mem_cons_of_mem i hj)),
      pdPow_remList p (contDiff_pdMulti (m := m) hG l) (hdisj i (List.mem_cons_self ..))]

/-! ### The Taylor and flat coordinate lists of a face -/

variable (J : Finset (Fin d))

/-- The Taylor coordinates of the face, in the standard enumeration. -/
def lJ : List (Fin d) := (List.finRange d).filter (· ∈ J)

/-- The flat coordinates of the face, in the standard enumeration. -/
def lK : List (Fin d) := (List.finRange d).filter (· ∉ J)

theorem mem_lJ {i : Fin d} : i ∈ lJ J ↔ i ∈ J := by simp [lJ]

theorem mem_lK {i : Fin d} : i ∈ lK J ↔ i ∉ J := by simp [lK]

theorem nodup_lJ : (lJ J).Nodup := (List.nodup_finRange d).filter _

theorem nodup_lK : (lK J).Nodup := (List.nodup_finRange d).filter _

theorem lJ_append_lK_perm : (lJ J ++ lK J).Perm (List.finRange d) := by
  have h := List.filter_append_perm (fun x : Fin d => decide (x ∈ J)) (List.finRange d)
  have hK : (List.finRange d).filter (fun x => !decide (x ∈ J)) = lK J := by
    unfold lK
    exact List.filter_congr fun x _ => by simp
  rw [hK] at h
  exact h

theorem faceOp_finRange_eq {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    faceOp p J (List.finRange d) F = tayList p (lJ J) (remList p (lK J) F) :=
  faceOp_eq p hF J (List.nodup_finRange d)

/-! ### Gluing the face and complementary coordinates -/

/-- Membership in the Taylor set as a plain predicate, so that the subtypes `{i // inJ J i}` and
`{i // ¬ inJ J i}` carry the generic `Subtype.fintype` instance (no `Finset`-specific instance). -/
def inJ (J : Finset (Fin d)) (i : Fin d) : Prop := i ∈ J

instance (J : Finset (Fin d)) : DecidablePred (inJ J) :=
  fun i => inferInstanceAs (Decidable (i ∈ J))

theorem inJ_iff {J : Finset (Fin d)} {i : Fin d} : inJ J i ↔ i ∈ J := Iff.rfl

/-- The point of `ℝ^d` with `J`-coordinates `u` and complementary coordinates `w`. -/
def glue (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) : Fin d → ℝ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm (u, w)

theorem glue_apply_of_mem (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) {i : Fin d}
    (hi : i ∈ J) : glue J u w i = u ⟨i, hi⟩ := by
  have hi' : inJ J i := hi
  simp [glue, MeasurableEquiv.piEquivPiSubtypeProd, hi']

theorem glue_apply_of_not_mem (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) {i : Fin d}
    (hi : i ∉ J) : glue J u w i = w ⟨i, hi⟩ := by
  have hi' : ¬ inJ J i := hi
  simp [glue, MeasurableEquiv.piEquivPiSubtypeProd, hi']

theorem glue_apply_subtype (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ)
    (i : {i // inJ J i}) : glue J u w i = u i := glue_apply_of_mem J u w i.2

theorem glue_apply_subtype' (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ)
    (i : {i // ¬ inJ J i}) : glue J u w i = w i := glue_apply_of_not_mem J u w i.2

theorem continuous_glue :
    Continuous fun uw : ({i // inJ J i} → ℝ) × ({i // ¬ inJ J i} → ℝ) => glue J uw.1 uw.2 := by
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ J
  · simp only [glue_apply_of_mem J _ _ hi]
    exact (continuous_apply _).comp continuous_fst
  · simp only [glue_apply_of_not_mem J _ _ hi]
    exact (continuous_apply _).comp continuous_snd

theorem continuous_glue_zero : Continuous fun w : {i // ¬ inJ J i} → ℝ => glue J 0 w :=
  (continuous_glue J).comp (Continuous.prodMk continuous_const continuous_id)

theorem glue_zero_mem_Icc {b : ℝ} (hb : 0 < b) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) (i : Fin d) : glue J 0 w i ∈ Icc 0 b := by
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi]; exact ⟨le_rfl, hb.le⟩
  · rw [glue_apply_of_not_mem J _ _ hi]
    exact Ioc_subset_Icc_self (hw ⟨i, hi⟩ (Set.mem_univ _))

theorem box_split_preimage (b : ℝ) :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm ⁻¹'
      box (Fin d) b = box {i // inJ J i} b ×ˢ box {i // ¬ inJ J i} b := by
  ext ⟨u, w⟩
  simp only [Set.mem_preimage, Set.mem_prod, box, Set.mem_univ_pi]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h i; rwa [← glue, glue_apply_subtype] at this
    · have := h i; rwa [← glue, glue_apply_subtype'] at this
  · rintro ⟨hu, hw⟩ i
    change glue J u w i ∈ Ioc 0 b
    by_cases hi : i ∈ J
    · rw [glue_apply_of_mem J u w hi]; exact hu ⟨i, hi⟩
    · rw [glue_apply_of_not_mem J u w hi]; exact hw ⟨i, hi⟩

/-- Fubini on the box with the complementary coordinates outside. -/
theorem integral_box_split (b : ℝ) (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f (box (Fin d) b)) :
    ∫ v in box (Fin d) b, f v =
      ∫ w in box {i // ¬ inJ J i} b, ∫ u in box {i // inJ J i} b, f (glue J u w) := by
  have hmp := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm
  have hemb := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
    (inJ J)).symm.measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb f (box (Fin d) b)
  rw [box_split_preimage] at h
  rw [← h]
  have hint' : IntegrableOn (f ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
      (inJ J)).symm) (box {i // inJ J i} b ×ˢ box {i // ¬ inJ J i} b) := by
    rw [← box_split_preimage]
    exact (hmp.integrableOn_comp_preimage hemb).2 hf
  have hint : Integrable (f ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
      (inJ J)).symm) ((volume.restrict (box {i // inJ J i} b)).prod
        (volume.restrict (box {i // ¬ inJ J i} b))) := by
    rw [Measure.prod_restrict]
    exact hint'
  have h2 := integral_prod_symm _ hint
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h2
  simp only [Function.comp_def] at h2
  exact h2

/-! ### Monomials, zeroing and Taylor monomials on glued points -/

theorem mono_glue (e : Fin d → ℕ) (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    mono e (glue J u w) =
      mono (fun i : {i // inJ J i} => e i) u * mono (fun i : {i // ¬ inJ J i} => e i) w := by
  unfold mono
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ J)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [glue_apply_subtype]
  · exact Finset.prod_congr rfl fun i _ => by rw [glue_apply_subtype']

theorem zeroL_lJ_glue (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    zeroL (lJ J) (glue J u w) = glue J 0 w := by
  funext i
  by_cases hi : i ∈ J
  · simp [zeroL, mem_lJ, hi, glue_apply_of_mem J _ _ hi]
  · simp [zeroL, mem_lJ, hi, glue_apply_of_not_mem J _ _ hi]

theorem tayMono_glue {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) (u : {i // inJ J i} → ℝ)
    (w : {i // ¬ inJ J i} → ℝ) :
    tayMono m (glue J u w) =
      (∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹) *
        mono (fun i : {i // inJ J i} => m i) u := by
  unfold tayMono
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ J)]
  have h2 : ∏ i : {x // ¬ inJ J x}, glue J u w i ^ m i / ((m i).factorial : ℝ) = 1 :=
    Finset.prod_eq_one fun i _ => by
      rw [mem_idxL_zero p hm (fun h => i.2 ((mem_lJ J).1 h))]; simp
  rw [h2, mul_one, mono, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [glue_apply_subtype]
  ring

/-! ### The face amplitude and the face-term integral -/

variable (F : (Fin d → ℝ) → ℝ)

/-- The flat face amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)`. -/
noncomputable def faceAmp (m : Fin d → ℕ) (w : {i // ¬ inJ J i} → ℝ) : ℝ :=
  remList p (lK J) (pdMulti m (lJ J) F) (glue J 0 w)

variable {F}

theorem continuous_faceAmp (hF : ContDiff ℝ ∞ F) (m : Fin d → ℕ) :
    Continuous (faceAmp p J F m) :=
  (contDiff_remList p (contDiff_pdMulti hF m _) _).continuous.comp (continuous_glue_zero J)

theorem continuous_zeroL (l : List (Fin d)) : Continuous (zeroL l) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ l
  · simp only [zeroL, hi, if_true]; exact continuous_const
  · simp only [zeroL, hi, if_false]; exact continuous_apply i

theorem continuous_tayMono (m : Fin d → ℕ) : Continuous (tayMono m) :=
  continuous_finsetProd _ fun i _ => ((continuous_apply i).pow _).div_const _

/-- ★ **The face-term integral**: the face-`J` term of the subset formula is a finite sum of
one-flat-complement face integrals with the inner face monomial integral at `t = N w^{2k_K}`. -/
theorem faceTerm_integral (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {β b N : ℝ} :
    ∫ v in box (Fin d) b, faceOp p J (List.finRange d) F v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
    ∑ m ∈ idxL p (lJ J), (∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹) *
      ∫ w in box {i // ¬ inJ J i} b,
        faceAmp p J F m w * mono (fun i : {i // ¬ inJ J i} => h i) w *
        ∫ u in box {i // inJ J i} b, mono (fun i : {i // inJ J i} => m i + h i) u *
          exp (-(β * (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)) *
            mono (fun i : {i // inJ J i} => 2 * k i) u) := by
  have hdisj : ∀ i ∈ lJ J, i ∉ lK J := fun i hi h' => (mem_lK J).1 h' ((mem_lJ J).1 hi)
  set E : (Fin d → ℝ) → ℝ := fun v => exp (-(N * β) * mono (fun i => 2 * k i) v) with hE
  have hEc : Continuous E := continuous_exp.comp (continuous_const.mul (continuous_mono _))
  set S : (Fin d → ℕ) → (Fin d → ℝ) → ℝ := fun m v =>
    tayMono m v * remList p (lK J) (pdMulti m (lJ J) F) (zeroL (lJ J) v) * mono h v * E v
    with hS
  have hSc : ∀ m, Continuous (S m) := fun m => by
    simp only [hS]
    exact (((continuous_tayMono m).mul
      ((contDiff_remList p (contDiff_pdMulti hF m _) _).continuous.comp
        (continuous_zeroL _))).mul (continuous_mono h)).mul hEc
  have hpt : ∀ v, faceOp p J (List.finRange d) F v * mono h v * E v =
      ∑ m ∈ idxL p (lJ J), S m v := by
    intro v
    rw [faceOp_finRange_eq p J hF, tayList_eq_sum p (contDiff_remList p hF _) (nodup_lJ J),
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hS]
    rw [pdMulti_remList p hF m hdisj]
  rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v,
    integral_finsetSum _ fun m _ => integrableOn_box_of_continuous (hSc m) b]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_box_split J b (S m) (integrableOn_box_of_continuous (hSc m) b)]
  have hinner : ∀ w : {i // ¬ inJ J i} → ℝ,
      ∫ u in box {i // inJ J i} b, S m (glue J u w) =
      (∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹) *
        (faceAmp p J F m w * mono (fun i : {i // ¬ inJ J i} => h i) w *
        ∫ u in box {i // inJ J i} b, mono (fun i : {i // inJ J i} => m i + h i) u *
          exp (-(β * (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)) *
            mono (fun i : {i // inJ J i} => 2 * k i) u)) := by
    intro w
    rw [← mul_assoc, ← MeasureTheory.integral_const_mul
      ((∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹) *
        (faceAmp p J F m w * mono (fun i : {i // ¬ inJ J i} => h i) w))]
    refine setIntegral_congr_fun (measurableSet_box (ι := {i // inJ J i}) b) fun u _ => ?_
    simp only [hS, hE]
    rw [tayMono_glue p J hm, zeroL_lJ_glue, mono_glue, mono_glue, faceAmp, ← mono_mul_mono]
    have harg : -(N * β) * (mono (fun i : {i // inJ J i} => 2 * k i) u *
        mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) =
        -(β * (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)) *
          mono (fun i : {i // inJ J i} => 2 * k i) u := by ring
    rw [harg]
    ring
  rw [setIntegral_congr_fun (measurableSet_box (ι := {i // ¬ inJ J i}) b) fun w _ => hinner w,
    MeasureTheory.integral_const_mul]

/-! ### Flatness of the face amplitude -/

/-- The multi-index `m` on `J`, `p` on the complement. -/
def faceIdx (m : Fin d → ℕ) : Fin d → ℕ := fun i => if i ∈ J then m i else p i

theorem faceIdx_le {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) (i : Fin d) :
    faceIdx p J m i ≤ p i := by
  unfold faceIdx
  split_ifs with hi
  · have := (Fintype.mem_piFinset.1 hm) i
    simp only [mem_lJ, hi, if_true, Finset.mem_range] at this
    exact this.le
  · exact le_rfl

/-- `R_K^p ∂^m F` differentiated `p` times in the `K`-coordinates is `∂^{faceIdx m} F`. -/
theorem pdList_lK_pdMulti_lJ (hF : ContDiff ℝ ∞ F) (m : Fin d → ℕ) :
    pdList p (lK J) (pdMulti m (lJ J) F) = pdMulti (faceIdx p J m) (List.finRange d) F := by
  rw [pdList_eq_pdMulti,
    ← pdMulti_perm hF _ (List.perm_append_comm.trans (lJ_append_lK_perm J)), pdMulti_append,
    pdMulti_congr (m := faceIdx p J m) (m' := m) (l := lJ J)
      (fun i hi => by simp [faceIdx, (mem_lJ J).1 hi]) F,
    pdMulti_congr (m := faceIdx p J m) (m' := p) (l := lK J)
      (fun i hi => by simp [faceIdx, (mem_lK J).1 hi]) (pdMulti m (lJ J) F)]

/-- ★ **Flatness of the face amplitude**: under the rectangular mixed-derivative bound
`|∂^m F| ≤ M` for `m ≤ p`, `|G_{J,m}(w)| ≤ (∏_{i∈K} 1/(p_i−1)!) · M · w^{p_K}` on the box. -/
theorem faceAmp_bound (hF : ContDiff ℝ ∞ F) {b : ℝ} (hb : 0 < b) (hp0 : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M)
    {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) :
    |faceAmp p J F m w| ≤
      (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M *
        mono (fun i : {i // ¬ inJ J i} => p i) w := by
  have hbound := remList_bound p (contDiff_pdMulti hF m (lJ J)) hb hp0 (lK J) (nodup_lK J)
    (M := M) (fun v hv => by rw [pdList_lK_pdMulti_lJ p J hF]; exact hM _ (faceIdx_le p J hm) v hv)
    (glue J 0 w) (glue_zero_mem_Icc J hb hw)
  refine hbound.trans (le_of_eq ?_)
  have hlist : ((lK J).map fun i => glue J 0 w i ^ p i / ((p i - 1).factorial : ℝ)).prod =
      ∏ i : {i // ¬ inJ J i}, glue J 0 w i ^ p i / ((p i - 1).factorial : ℝ) := by
    rw [← List.prod_toFinset _ (nodup_lK J)]
    exact Finset.prod_subtype ((lK J).toFinset) (fun i => by rw [List.mem_toFinset, mem_lK]; rfl) _
  have hprod : ∏ i : {i // ¬ inJ J i}, glue J 0 w i ^ p i / ((p i - 1).factorial : ℝ) =
      (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) *
        mono (fun i : {i // ¬ inJ J i} => p i) w := by
    unfold mono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [glue_apply_subtype']
    ring
  rw [hlist, hprod]
  ring

end SmoothEngine

end Grammar
