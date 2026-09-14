/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral

/-!
# Smooth amplitude families: uniform bounds and parameter continuity (consult #117 §2, U4b–U4c)

A `SmoothAmplitudeFamily S d b` is a family `s ↦ amp s` of smooth amplitudes on `ℝ^d` whose
mixed coordinate derivatives of every order are jointly continuous on `S × [0,b]^d`. On a compact
base this gives (i) a rectangular mixed-derivative bound uniform in `s` at every depth
(`exists_uniform_rect_bound`), hence (ii) the depth expansion with a constant uniform in `s`
(`uniform_depth`, from `smooth_expansion_at_depth_uniform`); (iii) joint continuity of the flat
face amplitudes `G_{J,m}(s, w) = (R_K^p ∂^m amp s)(0_J, w)` (`continuousOn_faceAmp_family`, by
list induction through the Taylor remainders, using only the derivative algebra `pdMulti_add`),
hence by dominated convergence (iv) continuity in `s` of every face coefficient integral and of
the canonical coefficients ★ `continuous_smoothCoeff`, and of the integral itself
(`continuous_smoothIntegral`); finally (v) ★★ `uniform_cutoff`: the canonical expansion through an
ARBITRARY real cutoff with a constant uniform in `s`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Derivative algebra -/

theorem pdPow_add (i : Fin d) (a c : ℕ) (G : (Fin d → ℝ) → ℝ) :
    pdPow i (a + c) G = pdPow i a (pdPow i c G) :=
  Function.iterate_add_apply _ _ _ _

theorem pdMulti_zero (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) : pdMulti 0 l G = G := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [pdMulti_cons, ih]; rfl

/-- Iterated coordinate derivatives compose additively. -/
theorem pdMulti_add {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (m m' : Fin d → ℕ)
    (l : List (Fin d)) : pdMulti m l (pdMulti m' l G) = pdMulti (m + m') l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdMulti_cons, ← pdPow_pdMulti (contDiff_pdMulti (m := m') hG l) m i (m' i) l,
      ih hG, pdMulti_cons, Pi.add_apply, pdPow_add]

/-- `∂^{n e_i}` over all coordinates is `∂_i^n`. -/
theorem pdMulti_single_finRange {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (n : ℕ) :
    pdMulti (Pi.single i n) (List.finRange d) G = pdPow i n G := by
  have hperm : (List.finRange d).Perm (i :: (List.finRange d).erase i) :=
    List.perm_cons_erase (List.mem_finRange i)
  rw [pdMulti_perm hG _ hperm, pdMulti_cons, Pi.single_eq_same,
    pdMulti_congr (m := Pi.single i n) (m' := 0) (l := (List.finRange d).erase i)
      (fun j hj => by
        have hji : j ≠ i := ((List.nodup_finRange d).mem_erase_iff.1 hj).1
        simp [Pi.single_eq_of_ne hji]) G, pdMulti_zero]

/-- `∂^m` over the Taylor list of a face equals `∂^m` over all coordinates when `m` is supported
on the face. -/
theorem pdMulti_lJ_eq_finRange {p : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ}
    (hm : m ∈ idxL p (lJ J)) {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    pdMulti m (lJ J) G = pdMulti m (List.finRange d) G := by
  rw [← pdMulti_perm hG _ (lJ_append_lK_perm J), pdMulti_append,
    pdMulti_congr (m := m) (m' := 0) (l := lK J)
      (fun i hi => mem_idxL_zero p hm fun h => (mem_lK J).1 hi ((mem_lJ J).1 h)) G,
    pdMulti_zero]

/-! ### The family structure and uniform bounds -/

/-- The closed box `[0,b]^d`. -/
def closedBox (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc 0 b

theorem isCompact_closedBox (b : ℝ) : IsCompact (closedBox d b) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem mem_closedBox {b : ℝ} {v : Fin d → ℝ} : v ∈ closedBox d b ↔ ∀ i, v i ∈ Icc 0 b := by
  unfold closedBox
  exact Set.mem_univ_pi

theorem box_subset_closedBox (b : ℝ) : box (Fin d) b ⊆ closedBox d b := fun _ hv =>
  mem_closedBox.2 fun i => Ioc_subset_Icc_self (hv i (Set.mem_univ i))

/-- The rectangular mixed-derivative bound `|∂^m F| ≤ M` on `[0,b]^d` for all `m ≤ p`. -/
def RectBound (F : (Fin d → ℝ) → ℝ) (p : Fin d → ℕ) (b M : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
    |pdMulti m (List.finRange d) F v| ≤ M

/-- A family of smooth amplitudes with jointly continuous mixed derivatives on `S × [0,b]^d`. -/
structure SmoothAmplitudeFamily (S : Type*) [TopologicalSpace S] (d : ℕ) (b : ℝ) where
  /-- the amplitudes -/
  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  /-- joint continuity of every mixed coordinate derivative on `S × [0,b]^d` -/
  deriv_cont : ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (amp z.1) z.2)
    (Set.univ ×ˢ closedBox d b)

namespace SmoothAmplitudeFamily

variable {S : Type*} [TopologicalSpace S] {b : ℝ} (F : SmoothAmplitudeFamily S d b)

instance : CoeFun (SmoothAmplitudeFamily S d b) fun _ => S → (Fin d → ℝ) → ℝ := ⟨amp⟩

/-- The amplitudes themselves are jointly continuous. -/
theorem continuousOn_amp : ContinuousOn (fun z : S × (Fin d → ℝ) => F z.1 z.2)
    (Set.univ ×ˢ closedBox d b) := by
  have := F.deriv_cont 0
  simpa only [pdMulti_zero] using this

/-- ★ **The uniform rectangular bound** on a compact base. -/
theorem exists_uniform_rect_bound [CompactSpace S] (p : Fin d → ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, RectBound (F s) p b M := by
  classical
  set T : Finset (Fin d → ℕ) := Fintype.piFinset fun i => Finset.range (p i + 1) with hT
  have hK : IsCompact (Set.univ ×ˢ closedBox d b) :=
    (isCompact_univ (X := S)).prod (isCompact_closedBox b)
  have hbd : ∀ m : Fin d → ℕ, ∃ C : ℝ, ∀ z ∈ Set.univ ×ˢ closedBox d b,
      ‖pdMulti m (List.finRange d) (F z.1) z.2‖ ≤ C := fun m =>
    hK.exists_bound_of_continuousOn (F.deriv_cont m)
  choose C hC using hbd
  refine ⟨∑ m ∈ T, |C m|, Finset.sum_nonneg fun m _ => abs_nonneg _, fun s m hm v hv => ?_⟩
  have hmT : m ∈ T := by
    rw [hT, Fintype.mem_piFinset]
    exact fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hm i))
  have hz : ((s, v) : S × (Fin d → ℝ)) ∈ Set.univ ×ˢ closedBox d b :=
    ⟨Set.mem_univ _, mem_closedBox.2 hv⟩
  calc |pdMulti m (List.finRange d) (F s) v| ≤ C m := by
        have := hC m (s, v) hz; rwa [Real.norm_eq_abs] at this
    _ ≤ |C m| := le_abs_self _
    _ ≤ ∑ m ∈ T, |C m| := Finset.single_le_sum (fun m _ => abs_nonneg (C m)) hmT

variable {h k p : Fin d → ℕ} {β : ℝ} {L : ℕ}

/-- ★ **The depth expansion, uniformly over the family.** -/
theorem uniform_depth [CompactSpace S] (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) :
    ∃ K : ℝ, ∀ s, ∀ N : ℝ, 1 ≤ N →
      |smoothIntegral (F s) h k β b N -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth (F s) h k p β b) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  obtain ⟨M, -, hM⟩ := F.exists_uniform_rect_bound p
  obtain ⟨K, hK⟩ := smooth_expansion_at_depth_uniform (h := h) hk hβ hb hL hp hp0 M
  exact ⟨K, fun s N hN => hK (F s) (F.smooth s) (hM s) N hN⟩

/-! ### Joint continuity of the flat face amplitudes -/

/-- Joint continuity of all mixed derivatives of a family on `S × [0,b]^d`. -/
def DerivsCont (H : S → (Fin d → ℝ) → ℝ) (b : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (H z.1) z.2)
    (Set.univ ×ˢ closedBox d b)

theorem derivsCont_pdMulti {H : S → (Fin d → ℝ) → ℝ} (hsm : ∀ s, ContDiff ℝ ∞ (H s))
    (hH : DerivsCont H b) (m' : Fin d → ℕ) :
    DerivsCont (fun s => pdMulti m' (List.finRange d) (H s)) b := fun m => by
  have := hH (m + m')
  refine this.congr fun z _ => ?_
  simp only
  rw [pdMulti_add (hsm z.1)]

theorem update_mem_closedBox {b : ℝ} (hb : 0 ≤ b) {v : Fin d → ℝ} (hv : v ∈ closedBox d b)
    (i : Fin d) : Function.update v i 0 ∈ closedBox d b := by
  rw [mem_closedBox] at hv ⊢
  intro j
  by_cases hji : j = i
  · subst hji; simp [hb]
  · rw [Function.update_of_ne hji]; exact hv j

/-- ★ **Joint continuity of iterated remainders**: if all mixed derivatives of a family are jointly
continuous on `S × [0,b]^d`, so is `(s, v) ↦ (R_l^p (H s))(v)`. -/
theorem continuousOn_remList_family (p : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b)
    {H : S → (Fin d → ℝ) → ℝ} (hsm : ∀ s, ContDiff ℝ ∞ (H s)) (hH : DerivsCont H b)
    {l : List (Fin d)} (hl : l.Nodup) :
    ContinuousOn (fun z : S × (Fin d → ℝ) => remList p l (H z.1) z.2)
      (Set.univ ×ˢ closedBox d b) := by
  induction l generalizing H with
  | nil =>
    have := hH 0
    simpa only [pdMulti_zero, remList_nil] using this
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    have hpt : ∀ z : S × (Fin d → ℝ), remList p (i :: l) (H z.1) z.2 =
        remList p l (H z.1) z.2 - ∑ n ∈ Finset.range (p i),
          ((n.factorial : ℝ)⁻¹ * z.2 i ^ n) *
            remList p l (pdPow i n (H z.1)) (Function.update z.2 i 0) := by
      intro z
      rw [remList_cons]
      change remList p l (H z.1) z.2 - coordTaylor i (p i) (remList p l (H z.1)) z.2 = _
      rw [coordTaylor_apply]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pdPow_remList p (hsm z.1) hi]
    refine ContinuousOn.congr ?_ fun z _ => hpt z
    refine (ih hsm hH hl').sub (continuousOn_finsetSum _ fun n _ => ?_)
    · have hcomp : ContinuousOn (fun z : S × (Fin d → ℝ) =>
          remList p l (pdPow i n (H z.1)) (Function.update z.2 i 0))
          (Set.univ ×ˢ closedBox d b) := by
        have hin := ih (H := fun s => pdPow i n (H s)) (fun s => contDiff_pdPow (hsm s) i n)
          (by
            have := derivsCont_pdMulti hsm hH (Pi.single i n)
            refine fun m => (this m).congr fun z _ => ?_
            simp only
            rw [pdMulti_single_finRange (hsm z.1)]) hl'
        refine hin.comp (f := fun z : S × (Fin d → ℝ) => (z.1, Function.update z.2 i 0))
          (Continuous.continuousOn (by fun_prop)) ?_
        intro z hz
        exact ⟨Set.mem_univ _, update_mem_closedBox hb hz.2 i⟩
      exact (continuousOn_const.mul
        (((continuous_apply i).comp continuous_snd).continuousOn.pow n)).mul hcomp

/-- The flat face amplitudes of a family are jointly continuous on `S × [0,b]^K`. -/
theorem continuousOn_faceAmp_family (hb : 0 ≤ b) (p : Fin d → ℕ) (J : Finset (Fin d))
    {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) :
    ContinuousOn (fun z : S × ({i // ¬ inJ J i} → ℝ) => faceAmp p J (F z.1) m z.2)
      (Set.univ ×ˢ Set.pi univ fun _ : {i // ¬ inJ J i} => Icc 0 b) := by
  have hH : DerivsCont (fun s => pdMulti m (lJ J) (F s)) b := fun m' => by
    have := derivsCont_pdMulti F.smooth F.deriv_cont m m'
    refine this.congr fun z _ => ?_
    simp only
    rw [pdMulti_lJ_eq_finRange hm (F.smooth z.1)]
  have hrem := continuousOn_remList_family p hb (H := fun s => pdMulti m (lJ J) (F s))
    (fun s => contDiff_pdMulti (F.smooth s) m _) hH (nodup_lK J)
  refine hrem.comp (f := fun z : S × ({i // ¬ inJ J i} → ℝ) => (z.1, glue J 0 z.2))
    (Continuous.continuousOn (continuous_fst.prodMk ((continuous_glue_zero J).comp continuous_snd)))
    ?_
  rintro ⟨s, w⟩ ⟨-, hw⟩
  refine ⟨Set.mem_univ _, mem_closedBox.2 fun i => ?_⟩
  change glue J 0 w i ∈ Icc 0 b
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi]; exact ⟨le_rfl, hb⟩
  · rw [glue_apply_of_not_mem J _ _ hi]; exact hw ⟨i, hi⟩ (Set.mem_univ _)

/-- Continuity in the parameter of `s ↦ G_s(w)` for a fixed `w` in the box. -/
theorem continuous_faceAmp_family_apply (hb : 0 ≤ b) (p : Fin d → ℕ) (J : Finset (Fin d))
    {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) : Continuous fun s => faceAmp p J (F s) m w :=
  (continuousOn_faceAmp_family F hb p J hm).comp_continuous
    (f := fun s => (s, w)) (continuous_id.prodMk continuous_const) fun s =>
    ⟨Set.mem_univ s, fun i _ => Ioc_subset_Icc_self (hw i (Set.mem_univ i))⟩

/-- The pointwise majorant of the face coefficient integrand. -/
theorem abs_faceCoeff_integrand_le {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℝ} {p h a : ι → ℕ}
    {b M : ℝ} (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) (μ : ℝ) (e : ℕ) {w : ι → ℝ}
    (hw : w ∈ box ι b) :
    |G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e| ≤
      M * ((∏ i, w i ^ ((p i + h i : ℝ) - a i * μ)) * |logSum a w| ^ e) := by
  have hpos := pos_of_mem_box hw
  have hGw := hGM w hw
  have h1 : 0 ≤ mono h w * mono a w ^ (-μ) * |logSum a w| ^ e := by
    have := mono_pos h hpos
    have := rpow_pos_of_pos (mono_pos a hpos) (-μ)
    positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (mono_pos h hpos),
    abs_of_pos (rpow_pos_of_pos (mono_pos a hpos) _), abs_pow,
    ← mono_mul_mono_mul_rpow p h a μ hpos]
  calc |G w| * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e
      = |G w| * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring
    _ ≤ M * mono p w * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) :=
        mul_le_mul_of_nonneg_right hGw h1
    _ = M * (mono p w * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring

/-- ★ **Parameter continuity of the face coefficient integrals** (dominated convergence). -/
theorem continuous_faceCoeffInt_family [CompactSpace S] [FirstCountableTopology S] (hb : 0 < b)
    (hp0 : ∀ i, 0 < p i)
    (J : Finset (Fin d)) {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {μ : ℝ}
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (e : ℕ) :
    Continuous fun s => faceCoeffInt (faceAmp p J (F s) m) (fun i : {i // ¬ inJ J i} => h i)
      (fun i : {i // ¬ inJ J i} => 2 * k i) b μ e := by
  obtain ⟨M, -, hM⟩ := F.exists_uniform_rect_bound p
  set M' : ℝ := (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M with hM'
  have hGM : ∀ s, ∀ w ∈ box {i // ¬ inJ J i} b, |faceAmp p J (F s) m w| ≤
      M' * mono (fun i : {i // ¬ inJ J i} => p i) w := fun s w hw =>
    faceAmp_bound p J (F.smooth s) hb hp0 (hM s) hm hw
  unfold faceCoeffInt
  refine continuous_of_dominated (μ := volume.restrict (box {i // ¬ inJ J i} b))
    (bound := fun w => M' * ((∏ i : {i // ¬ inJ J i},
      w i ^ ((p i + h i : ℝ) - (2 * k i : ℕ) * μ)) *
        |logSum (fun i : {i // ¬ inJ J i} => 2 * k i) w| ^ e))
    (fun s => ?_) (fun s => ?_) ?_ ?_
  · exact (((continuous_faceAmp p J (F.smooth s) m).aestronglyMeasurable.mul
      (measurable_mono _).aestronglyMeasurable).mul
      ((measurable_mono _).pow_const _).aestronglyMeasurable).mul
      ((measurable_logSum _).pow_const e).aestronglyMeasurable
  · refine (ae_restrict_mem (measurableSet_box b)).mono fun w hw => ?_
    rw [Real.norm_eq_abs]
    exact abs_faceCoeff_integrand_le (hGM s) μ e hw
  · exact (integrableOn_prod_rpow_mul_abs_log_pow
      (c := fun i : {i // ¬ inJ J i} => (p i + h i : ℝ) - (2 * k i : ℕ) * μ)
      (fun i => by have := hμ i; linarith) (fun i => ((2 * k i : ℕ) : ℝ)) le_rfl
      hb.le).const_mul M'
  · refine (ae_restrict_mem (measurableSet_box b)).mono fun w hw => ?_
    exact ((continuous_faceAmp_family_apply F hb.le p J hm hw).mul continuous_const).mul
      continuous_const |>.mul continuous_const

/-- ★ **Parameter continuity of the depth coefficients** below the cutoff. -/
theorem continuous_smoothCoeffAtDepth [CompactSpace S] [FirstCountableTopology S] (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ : μ ≤ L) (q : ℕ) :
    Continuous fun s => smoothCoeffAtDepth (F s) h k p β b μ q := by
  have hμ' : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1 := fun i => by
    have h1 : ((2 * k i : ℕ) : ℝ) * L = (p i : ℝ) + h i := by exact_mod_cast (hp i).symm
    have h2 : ((2 * k i : ℕ) : ℝ) * μ ≤ ((2 * k i : ℕ) : ℝ) * L :=
      mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg _)
    linarith
  unfold smoothCoeffAtDepth
  refine continuous_finsetSum _ fun x hx => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_const.mul continuous_const).mul ?_)
  exact continuous_faceCoeffInt_family F hb hp0 x.1 (Finset.mem_sigma.1 hx).2 hμ' (j - q)

/-- ★★ **Parameter continuity of the canonical smooth coefficients.** -/
theorem continuous_smoothCoeff [CompactSpace S] [FirstCountableTopology S] (hk : ∀ i, 0 < k i)
    (hb : 0 < b) (μ : ℝ)
    (q : ℕ) : Continuous fun s => smoothCoeff (F s) h k β b μ q := by
  unfold smoothCoeff
  exact continuous_smoothCoeffAtDepth F hb (depthOf_add hk (L₀_le_cutoffOf h μ))
    (depthOf_pos hk (L₀_le_cutoffOf h μ)) (lt_cutoffOf h μ).le q

/-- Parameter continuity of the integral itself, with a continuous nonnegative phase scale. -/
theorem continuous_smoothIntegral_beta [CompactSpace S] [FirstCountableTopology S] {βf : S → ℝ}
    (hβ : Continuous βf) (hβ0 : ∀ s, 0 ≤ βf s) {N : ℝ} (hN : 0 ≤ N) :
    Continuous fun s => smoothIntegral (F s) h k (βf s) b N := by
  obtain ⟨M, hM0, hM⟩ := F.exists_uniform_rect_bound 0
  have hF0 : ∀ s, ∀ v ∈ box (Fin d) b, |F s v| ≤ M := fun s v hv => by
    have := hM s 0 (fun i => le_rfl) v fun i => Ioc_subset_Icc_self (hv i (Set.mem_univ i))
    rwa [pdMulti_zero] at this
  unfold smoothIntegral
  refine continuous_of_dominated (μ := volume.restrict (box (Fin d) b))
    (bound := fun v => M * mono h v) (fun s => ?_) (fun s => ?_) ?_ ?_
  · exact (((F.smooth s).continuous.mul (continuous_mono h)).mul
      (continuous_exp.comp (continuous_const.mul (continuous_mono _)))).aestronglyMeasurable
  · refine (ae_restrict_mem (measurableSet_box b)).mono fun v hv => ?_
    have hpos := pos_of_mem_box hv
    have hmh : 0 ≤ mono h v := (mono_pos h hpos).le
    have hexp : exp (-(N * βf s) * mono (fun i => 2 * k i) v) ≤ 1 := by
      rw [exp_le_one_iff]
      have := (mono_pos (fun i => 2 * k i) hpos).le
      nlinarith [mul_nonneg hN (hβ0 s)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hmh, abs_of_pos (exp_pos _)]
    calc |F s v| * mono h v * exp (-(N * βf s) * mono (fun i => 2 * k i) v)
        ≤ M * mono h v * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hF0 s v hv) hmh) hexp (exp_pos _).le
            (mul_nonneg hM0 hmh)
      _ = M * mono h v := by ring
  · exact (integrableOn_box_of_continuous (continuous_mono h) b).const_mul M
  · refine (ae_restrict_mem (measurableSet_box b)).mono fun v hv => ?_
    have hc : Continuous fun s => F s v :=
      F.continuousOn_amp.comp_continuous (f := fun s => (s, v))
        (continuous_id.prodMk continuous_const) fun s =>
        ⟨Set.mem_univ s, box_subset_closedBox b hv⟩
    exact (hc.mul continuous_const).mul
      (continuous_exp.comp ((continuous_const.mul hβ).neg.mul continuous_const))

/-- Parameter continuity of the integral itself. -/
theorem continuous_smoothIntegral [CompactSpace S] [FirstCountableTopology S] (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) : Continuous fun s => smoothIntegral (F s) h k β b N :=
  F.continuous_smoothIntegral_beta continuous_const (fun _ => hβ) hN

/-! ### The canonical expansion through an arbitrary cutoff, uniformly in the parameter -/

/-- ★★ **Uniform canonical expansion**: for every real cutoff `L' > 0` there is one constant for
the whole family. -/
theorem uniform_cutoff [CompactSpace S] [FirstCountableTopology S] (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) (L' : ℝ) :
    ∃ C : ℝ, ∀ s, ∀ N : ℝ, 1 ≤ N →
      |smoothIntegral (F s) h k β b N -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeff (F s) h k β b) L' N| ≤
        C * (N ^ (-L') * (1 + log N) ^ (d - 1)) := by
  have hQ := Qamb_pos k hk
  set L : ℕ := max ⌈L'⌉₊ (L₀ h) with hLdef
  have hL : L₀ h ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le (by unfold L₀; omega) hL
  have hLL : L' ≤ (L : ℝ) := by
    have h1 := Nat.le_ceil L'
    have h2 : ((⌈L'⌉₊ : ℕ) : ℝ) ≤ ((max ⌈L'⌉₊ (L₀ h) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    linarith
  obtain ⟨K, hK⟩ := F.uniform_depth hk hβ hb hL0 (depthOf_add hk hL) (depthOf_pos hk hL)
  -- the dropped coefficients are bounded uniformly in `s`
  have hcont : Continuous fun s => ∑ ν ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
      |smoothCoeffAtDepth (F s) h k (depthOf h k L) β b ν j| := by
    refine continuous_finsetSum _ fun ν hν => continuous_finsetSum _ fun j _ => ?_
    have hνL : ν ≤ L := ((mem_latticeBelow_iff hQ).1 hν).2.le
    exact (continuous_smoothCoeffAtDepth F hb (depthOf_add hk hL) (depthOf_pos hk hL) hνL j).abs
  obtain ⟨B, hB⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨K + B, fun s N hN => ?_⟩
  have hlow := bound_lower_cutoff hQ hLL hN (hK s N hN)
  have hcoef : absSpectralSum (Qamb k) (d - 1) (smoothCoeff (F s) h k β b) L' N =
      absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth (F s) h k (depthOf h k L) β b) L' N := by
    unfold absSpectralSum
    refine Finset.sum_congr rfl fun μ hμ => ?_
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hμL : μ ∈ latticeBelow (Qamb k) L := latticeBelow_mono hQ hLL hμ
    rw [smoothCoeff_eq (F.smooth s) hk hβ hb hL hμL (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
  rw [hcoef]
  refine hlow.trans (mul_le_mul_of_nonneg_right ?_ (by have := log_nonneg hN; positivity))
  have := hB s (Set.mem_univ s)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _)] at this
  linarith

end SmoothAmplitudeFamily

end SmoothEngine

end Grammar
