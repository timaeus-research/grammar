/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneral
import Grammar.EmpiricalMellinJet
import Grammar.SmoothFaceSumCollapse
import Grammar.SmoothResolvedResonant
import Grammar.StateDensitySecondCoeff
import Grammar.SmoothFaceMonoTop

/-!
# The empirical face-sum collapse at the top logarithmic power: the graded empirical Theorem E
in a box (§20 units 3–4 of consult #142)

**Top spectral coefficient.** On a face all of whose coordinates resonate exactly with `μ`
(`2kᵢμ = eᵢ + 1`), the empirical face coefficient at the top logarithmic power `|J| − 1` is
`(∏_{i∈J} 1/(2kᵢ)) / (|J|−1)! · mellinMom G μ 0` (`empInnerCoeff_top_of_exact`, from the top
coefficient `1/(m−1)!` of the state density), and it vanishes if some coordinate fails exact
resonance (`empInnerCoeff_top_eq_zero_of_not_exact`); at log degrees `≥ |J|` every face coefficient
vanishes (`empFaceCoef_eq_zero_of_card_le`). Packaged as `resonantTop`:
★ `empFaceCoef_top : empFaceCoef k J e G μ (DJ J) = resonantTop k J e μ * mellinMom G μ 0`.

**Depth flatness.** If `η` vanishes near the deep set `{≥ c+1 vanishing coordinates}` then so does
`η e^{τζ}` for every `τ`, its jets vanish there (`jetsZeroOn_of_eventually_zero`), the face
amplitudes of faces of size `> c` vanish, and on faces of size `c` the complementary Taylor
remainder is the identity — so the face amplitude is the plain normal derivative
`∂_J^α (η e^{τζ})(0_J, w)`, whose Mellin moment is `∂_J^α[η · S_μ(ζ)](0_J, w)`
(`EmpiricalMellinJet`).

★★★ `empCoeff_eq_faceSum_top`: for `η` vanishing near the deep set, `1 ≤ c`, `μ > 0`,
`empCoeff η ζ h k μ (c−1) = ∑_{|J|=c} faceW J α_J · resonantTop k J (α_J+h) μ ·`
`  ∫_{(0,1]^K} ∂_J^{α_J}[η · S_μ(ζ)](0_J, w) w^{h_K} (w^{2k_K})^{−μ} dw`, `α_J = resOrder h k μ J`;
`empCoeff_eq_zero_of_deep`: the coefficients of log degree `≥ c` vanish; and
★★★ `empCoeff_top_eq_smoothCoeff`: the empirical top coefficient is the POPULATION top coefficient
of the amplitude `η · S_μ(ζ)/Γ(μ)`:
`empCoeff η ζ h k μ (c−1) = smoothCoeff (η S_μ(ζ)/Γ(μ)) h k 1 1 μ (c−1)`
— the paper's replacement rule `∂^α A ↦ ∂^α[A S_μ(ζ)]/Γ(μ)`, exponent by exponent. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### The top spectral coefficient of the inner kernel -/

section Inner

variable {n : ℕ} (k e : Fin (n + 1) → ℕ)

theorem sdWeights_add_one_eq_iff (hk : ∀ i, 0 < k i) (μ : ℝ) (i : Fin (n + 1)) :
    sdWeights k e i + 1 = μ ↔ 2 * (k i : ℝ) * μ = e i + 1 := by
  unfold sdWeights
  have hk' : (2 * (k i : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < k i := by exact_mod_cast hk i
    positivity
  constructor
  · intro h
    have h' : ((e i : ℝ) + 1) / (2 * (k i : ℝ)) = μ := by linarith
    rw [div_eq_iff hk'] at h'
    linarith
  · intro h
    have h' : ((e i : ℝ) + 1) / (2 * (k i : ℝ)) = μ := by
      rw [div_eq_iff hk']
      linarith
    linarith

theorem expMult_sdWeights_of_exact (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hex : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) : expMult (sdWeights k e) μ = n + 1 := by
  unfold expMult
  rw [Finset.filter_eq_self.2 fun i _ => (sdWeights_add_one_eq_iff k e hk μ i).2 (hex i),
    Finset.card_univ, Fintype.card_fin]

theorem expMult_sdWeights_lt_of_not_exact (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hne : ∃ i, 2 * (k i : ℝ) * μ ≠ e i + 1) : expMult (sdWeights k e) μ < n + 1 := by
  obtain ⟨i, hi⟩ := hne
  unfold expMult
  have hss : (Finset.univ.filter fun j => sdWeights k e j + 1 = μ) ⊂ Finset.univ :=
    Finset.filter_ssubset.2 ⟨i, Finset.mem_univ _,
      fun h => hi ((sdWeights_add_one_eq_iff k e hk μ i).1 h)⟩
  have := Finset.card_lt_card hss
  rwa [Finset.card_univ, Fintype.card_fin] at this

/-- ★ **The top inner coefficient of an exactly resonant face**:
`empInnerCoeff k e G μ n = (∏ 1/(2kᵢ)) · (1/n!) · mellinMom G μ 0`. -/
theorem empInnerCoeff_top_of_exact (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hex : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) (G : ℝ → ℝ) :
    empInnerCoeff k e G μ n =
      (∏ i, 1 / (2 * (k i : ℝ))) * (1 / (n.factorial : ℝ)) * mellinMom G μ 0 := by
  have hw : ∀ i, sdWeights k e i + 1 = μ := fun i => (sdWeights_add_one_eq_iff k e hk μ i).2 (hex i)
  have hE := expMult_sdWeights_of_exact k e hk hex
  have hlead := stateDensityRep_leadCoeff n (sdWeights k e) μ (fun i => (hw i).symm.le) ⟨0, hw 0⟩
  rw [hE, Nat.add_sub_cancel, Finset.prod_eq_one (fun i _ => if_pos (hw i)), mul_one] at hlead
  unfold empInnerCoeff
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => ?_, zero_add, Nat.choose_self,
    Nat.cast_one, mul_one, Nat.sub_self, hlead]
  · ring
  · rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj), Nat.cast_zero, mul_zero, zero_mul]

/-- The top inner coefficient vanishes unless every coordinate resonates exactly. -/
theorem empInnerCoeff_top_eq_zero_of_not_exact (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hne : ∃ i, 2 * (k i : ℝ) * μ ≠ e i + 1) (G : ℝ → ℝ) : empInnerCoeff k e G μ n = 0 := by
  have hE := expMult_sdWeights_lt_of_not_exact k e hk hne
  unfold empInnerCoeff
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => ?_, zero_add,
    stateDensityRep_coeffAt_eq_zero_of_le n _ μ (Nat.lt_succ_iff.1 hE), zero_mul, zero_mul,
    mul_zero]
  rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj), Nat.cast_zero, mul_zero, zero_mul]

/-- The inner coefficients vanish at log degrees `≥ n + 1`. -/
theorem empInnerCoeff_eq_zero_of_le (G : ℝ → ℝ) (μ : ℝ) {j : ℕ} (hj : n + 1 ≤ j) :
    empInnerCoeff k e G μ j = 0 := by
  unfold empInnerCoeff
  rw [Finset.sum_eq_zero fun j' hj' => ?_, mul_zero]
  have : j' < j := lt_of_lt_of_le (Finset.mem_range.1 hj') hj
  rw [Nat.choose_eq_zero_of_lt this, Nat.cast_zero, mul_zero, zero_mul]

theorem mellinMom_zero_fun (μ : ℝ) (ℓ : ℕ) : mellinMom (fun _ => (0 : ℝ)) μ ℓ = 0 := by
  unfold mellinMom momKernel
  simp

theorem empInnerCoeff_zero_fun (μ : ℝ) (q : ℕ) : empInnerCoeff k e (fun _ => (0 : ℝ)) μ q = 0 := by
  unfold empInnerCoeff
  simp [mellinMom_zero_fun]

end Inner

/-! ### The top face coefficient -/

variable {d : ℕ}

/-- The resonant top constant of a face `J`: `(∏_{i∈J} 1/(2kᵢ)) / (|J|−1)!` if every coordinate of
`J` resonates exactly with `μ` (`2kᵢμ = eᵢ + 1`), `0` otherwise. -/
noncomputable def resonantTop (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) (μ : ℝ) : ℝ :=
  if ∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1 then
    (∏ i : {i // inJ J i}, 1 / (2 * (k i : ℝ))) / ((J.card - 1).factorial : ℝ)
  else 0

theorem resonantTop_of_not_exact (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) {μ : ℝ}
    (hne : ∃ j ∈ J, 2 * (k j : ℝ) * μ ≠ e j + 1) : resonantTop k J e μ = 0 := by
  unfold resonantTop
  rw [if_neg]
  rintro hall
  obtain ⟨j, hj, hne⟩ := hne
  exact hne (hall j hj)

/-- Exact resonance on the face, transported along `faceEquiv`. -/
theorem exact_iff_reindex (k : Fin d → ℕ) (J : Finset (Fin d)) (hJ : J.Nonempty) (e : Fin d → ℕ)
    (μ : ℝ) :
    haveI := nonempty_subtype_inJ hJ
    (∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1) ↔
      ∀ i : Fin (Fintype.card {i // inJ J i} - 1 + 1),
        2 * ((((fun i : {i // inJ J i} => k i) ∘ (faceEquiv {i // inJ J i}).symm) i : ℕ) : ℝ) * μ =
          (((fun i : {i // inJ J i} => e i) ∘ (faceEquiv {i // inJ J i}).symm) i : ℕ) + 1 := by
  have := nonempty_subtype_inJ hJ
  constructor
  · intro h i
    exact h ((faceEquiv {i // inJ J i}).symm i).1 ((faceEquiv {i // inJ J i}).symm i).2
  · intro h j hj
    have := h ((faceEquiv {i // inJ J i}) ⟨j, hj⟩)
    rwa [Function.comp_apply, Function.comp_apply, Equiv.symm_apply_apply] at this

/-- ★ **The top face coefficient**: `empFaceCoef k J e G μ (DJ J) = resonantTop · mellinMom G μ 0`
for every nonempty face. -/
theorem empFaceCoef_top (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (J : Finset (Fin d)) (hJ : J.Nonempty)
    (e : Fin d → ℕ) (G : ℝ → ℝ) (μ : ℝ) :
    empFaceCoef k J e G μ (DJ J) = resonantTop k J e μ * mellinMom G μ 0 := by
  have := nonempty_subtype_inJ hJ
  unfold empFaceCoef resonantTop
  rw [dif_pos hJ]
  unfold faceInnerCoeff DJ
  have hcard : J.card - 1 = Fintype.card {i // inJ J i} - 1 := by rw [card_subtype_inJ]
  have hprod : ∏ i : Fin (Fintype.card {i // inJ J i} - 1 + 1),
      1 / (2 * ((((fun i : {i // inJ J i} => k i) ∘ (faceEquiv {i // inJ J i}).symm) i : ℕ) : ℝ)) =
      ∏ i : {i // inJ J i}, 1 / (2 * (k i : ℝ)) :=
    Equiv.prod_comp (faceEquiv {i // inJ J i}).symm fun i => 1 / (2 * (k i : ℝ))
  by_cases hex : ∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1
  · rw [if_pos hex, hcard]
    rw [empInnerCoeff_top_of_exact
      ((fun i : {i // inJ J i} => k i) ∘ (faceEquiv {i // inJ J i}).symm)
      ((fun i : {i // inJ J i} => e i) ∘ (faceEquiv {i // inJ J i}).symm) (fun i => hk _)
      ((exact_iff_reindex k J hJ e μ).1 hex) G, hprod]
    ring
  · rw [if_neg hex, zero_mul]
    have hne : ∃ i, 2 * ((((fun i : {i // inJ J i} => k i) ∘ (faceEquiv {i // inJ J i}).symm) i :
        ℕ) : ℝ) * μ ≠ (((fun i : {i // inJ J i} => e i) ∘ (faceEquiv {i // inJ J i}).symm) i : ℕ) +
        1 := by
      by_contra hall
      push Not at hall
      exact hex ((exact_iff_reindex k J hJ e μ).2 hall)
    exact empInnerCoeff_top_eq_zero_of_not_exact
      ((fun i : {i // inJ J i} => k i) ∘ (faceEquiv {i // inJ J i}).symm)
      ((fun i : {i // inJ J i} => e i) ∘ (faceEquiv {i // inJ J i}).symm) (fun i => hk _) hne G

/-- The face coefficients vanish at log degrees `≥ |J|`. -/
theorem empFaceCoef_eq_zero_of_card_le (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ)
    (G : ℝ → ℝ) (μ : ℝ) {j : ℕ} (hj : J.card ≤ j) : empFaceCoef k J e G μ j = 0 := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    unfold faceInnerCoeff
    refine empInnerCoeff_eq_zero_of_le _ _ G μ ?_
    rw [Nat.sub_add_cancel Fintype.card_pos, card_subtype_inJ]
    exact hj
  · rfl

theorem empFaceCoef_zero_fun (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) (μ : ℝ)
    (j : ℕ) : empFaceCoef k J e (fun _ => (0 : ℝ)) μ j = 0 := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    exact empInnerCoeff_zero_fun _ _ μ j
  · rfl

/-! ### Linearity helpers -/

theorem faceCoeffInt_const_mul {ι : Type*} [Fintype ι] (c : ℝ) (G : (ι → ℝ) → ℝ) (h a : ι → ℕ)
    (b μ : ℝ) (e : ℕ) :
    faceCoeffInt (fun w => c * G w) h a b μ e = c * faceCoeffInt G h a b μ e := by
  unfold faceCoeffInt
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box b) fun w _ => ?_
  ring

theorem pdMulti_const_mul (c : ℝ) (H : (Fin d → ℝ) → ℝ) (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => c * H v) = fun v => c * pdMulti m l H v := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [pdMulti_cons, ih, pdPow_const_mul, pdMulti_cons]

/-! ### Depth flatness -/

theorem deepSet_subset_closedBox (b : ℝ) (c : ℕ) : deepSet d b c ⊆ closedBox d b := fun _ hv => hv.1

/-- A smooth function vanishing on a neighbourhood of a subset of the closed box has vanishing
jets on that subset. -/
theorem jetsZeroOn_of_eventually_zero {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {b : ℝ}
    (hb : 0 < b) {S : Set (Fin d → ℝ)} (hS : S ⊆ closedBox d b) (h : ∀ᶠ v in 𝓝ˢ S, G v = 0) :
    JetsZeroOn G S := by
  obtain ⟨O, hO, hSO, hOsub⟩ := mem_nhdsSet_iff_exists.1 h
  intro α v hv
  exact pdMulti_eq_zero_of_eqOn_inter_closedBox hG hb hO (fun w hw => hOsub hw.1) ⟨hSO hv, hS hv⟩ α

/-- **Deep vanishing within the box**: `η` vanishes near every point of the deep set
`{≥ c+1 vanishing coordinates}` of `[0,b]^d`, on the closed box. This is the form in which the
chart amplitudes vanish (they are arbitrary smooth extensions off the chart box). -/
def DeepVanishing (η : (Fin d → ℝ) → ℝ) (b : ℝ) (c : ℕ) : Prop :=
  ∀ v ∈ deepSet d b c, ∀ᶠ w in 𝓝 v, w ∈ closedBox d b → η w = 0

theorem DeepVanishing.of_eventually {η : (Fin d → ℝ) → ℝ} {b : ℝ} {c : ℕ}
    (h : ∀ᶠ v in 𝓝ˢ (deepSet d b c), η v = 0) : DeepVanishing η b c :=
  fun v hv => (eventually_nhdsSet_iff_forall.1 h v hv).mono fun _ hw _ => hw

theorem DeepVanishing.mono_fun {η η' : (Fin d → ℝ) → ℝ} {b : ℝ} {c : ℕ} (h : DeepVanishing η b c)
    (h' : ∀ v, η v = 0 → η' v = 0) : DeepVanishing η' b c :=
  fun v hv => (h v hv).mono fun w hw hwb => h' w (hw hwb)

/-- A smooth function vanishing near the deep set within the closed box has vanishing jets on
the deep set. -/
theorem jetsZeroOn_of_deepVanishing {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {b : ℝ}
    (hb : 0 < b) {c : ℕ} (h : DeepVanishing G b c) : JetsZeroOn G (deepSet d b c) := by
  intro α v hv
  obtain ⟨O, hOsub, hO, hvO⟩ := mem_nhds_iff.1 (h v hv)
  exact pdMulti_eq_zero_of_eqOn_inter_closedBox hG hb hO (fun w hw => hOsub hw.1 hw.2)
    ⟨hvO, hv.1⟩ α

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The field family inherits the deep vanishing of the amplitude, for every coupling. -/
theorem jetsZeroOn_fieldFam_deep (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {c : ℕ}
    (hdeep : DeepVanishing η 1 c) (τ : ℝ) : JetsZeroOn (fieldFam η ζ τ) (deepSet d 1 c) :=
  jetsZeroOn_of_deepVanishing (contDiff_fieldFam hη hζ τ) one_pos
    (hdeep.mono_fun fun v hv => by simp [fieldFam, hv])

/-- On a face of size `c` the face amplitude of the field family is the plain normal derivative. -/
theorem faceAmp_fieldFam_eq_pdMulti (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {c : ℕ}
    (hdeep : DeepVanishing η 1 c) (p : Fin d → ℕ) {J : Finset (Fin d)}
    (hJ : J.card = c) (m : Fin d → ℕ) (τ : ℝ) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} 1) :
    faceAmp p J (fieldFam η ζ τ) m w = pdMulti m (lJ J) (fieldFam η ζ τ) (glue J 0 w) := by
  unfold faceAmp
  refine remList_eq_self_of_jetsZeroOn _ (deepSet_update zero_le_one) (lK J) (nodup_lK J) _
    (contDiff_pdMulti (contDiff_fieldFam hη hζ τ) _ (lJ J))
    ((jetsZeroOn_fieldFam_deep hη hζ hdeep τ).pdMulti (contDiff_fieldFam hη hζ τ) _ (lJ J)) _
    fun i hi => ?_
  have hiJ : i ∉ J := (mem_lK J).1 hi
  refine mem_deepSet_of_zeros ?_ (J := insert i J) ?_ ?_
  · rw [mem_closedBox]
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self]
      exact ⟨le_rfl, zero_le_one⟩
    · rw [Function.update_of_ne hji]
      exact glue_zero_mem_Icc J one_pos hw j
  · rw [Finset.card_insert_of_notMem hiJ, hJ]
  · intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact Function.update_self ..
    · have hji : j ≠ i := fun h' => hiJ (h' ▸ hj)
      rw [Function.update_of_ne hji, glue_apply_of_mem J _ _ hj]
      rfl

/-- On a face of size `> c` the face amplitude of the field family vanishes. -/
theorem faceAmp_fieldFam_eq_zero (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {c : ℕ}
    (hdeep : DeepVanishing η 1 c) (p : Fin d → ℕ) {J : Finset (Fin d)}
    (hJ : c < J.card) (m : Fin d → ℕ) (τ : ℝ) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} 1) : faceAmp p J (fieldFam η ζ τ) m w = 0 :=
  faceAmp_eq_zero_of_jets_zero p J (contDiff_fieldFam hη hζ τ) m one_pos
    (fun v hv hvJ α => jetsZeroOn_fieldFam_deep hη hζ hdeep τ α v
      (mem_deepSet_of_zeros hv (by omega) hvJ)) w hw

/-! ### The collapse -/

/-- ★★★ **The empirical face-sum collapse at the top logarithmic power**: for `η` vanishing near
the deep set `{≥ c+1 vanishing coordinates}` and `μ > 0`, the empirical coefficient at `(μ, c−1)`
is the sum over the faces of size `c` of
`faceW · resonantTop · ∫_{face} ∂_J^{α_J}[η · S_μ(ζ)](0_J, w) · (power weight)`. -/
theorem empCoeff_eq_faceSum_top (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (resonantTop k J (fun i => resOrder h k μ J i + h i) μ *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J)
                (fun v => η v * fluctuation 1 μ (ζ v)) (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) 1 μ 0) := by
  classical
  have hμL : μ < cutoffOf h μ := lt_cutoffOf h μ
  set p : Fin d → ℕ := depthOf h k (cutoffOf h μ) with hp
  unfold empCoeff empCoeffAtDepth faceIndex
  rw [Finset.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  rcases lt_trichotomy J.card c with hlt | heq | hgt
  · -- faces of size `< c`: log degree `≥ |J|`
    rw [if_neg hlt.ne]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro j hj
    have hj' : c - 1 ≤ j := (Finset.mem_Ico.1 hj).1
    rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ =>
      empFaceCoef_eq_zero_of_card_le k J _ _ μ (by omega), mul_zero]
  · -- faces of size `c`
    rw [if_pos heq]
    have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
    have hDJ : DJ J = c - 1 := by rw [DJ_eq, heq]
    have hIco : Finset.Ico (c - 1) (DJ J + 1) = {c - 1} := by
      rw [hDJ, Nat.sub_add_cancel hc, Nat.Ico_pred_singleton hc]
    simp_rw [hIco, Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
    have htop : ∀ (e : Fin d → ℕ) (G : ℝ → ℝ),
        empFaceCoef k J e G μ (c - 1) = resonantTop k J e μ * mellinMom G μ 0 := by
      intro e G
      rw [← hDJ]
      exact empFaceCoef_top k hk J hJne e G μ
    -- exact resonance of a Taylor order forces it to be the resonant order
    have hexact : ∀ m : Fin d → ℕ, m ∈ idxL p (lJ J) →
        (∀ j ∈ J, 2 * (k j : ℝ) * μ = m j + h j + 1) → m = resOrder h k μ J := by
      intro m hm hres
      funext j
      by_cases hj : j ∈ J
      · exact (resOrder_eq_of_exact hj (hres j hj)).symm
      · rw [resOrder_of_not_mem hj]
        have := (mem_idxL_iff.1 hm) j
        rw [if_neg (by rwa [mem_lJ])] at this
        exact Finset.mem_singleton.1 this
    have hzero : ∀ m : Fin d → ℕ, (∃ j ∈ J, 2 * (k j : ℝ) * μ ≠ m j + h j + 1) →
        resonantTop k J (fun i => m i + h i) μ = 0 := by
      rintro m ⟨j, hj, hne⟩
      exact resonantTop_of_not_exact k J _ ⟨j, hj, by push_cast; exact hne⟩
    rw [Finset.sum_eq_single (resOrder h k μ J)]
    · -- the surviving term
      congr 1
      rw [← faceCoeffInt_const_mul]
      refine faceCoeffInt_congr_box _ _ _ _ _ fun w hw => ?_
      rw [htop]
      congr 1
      have hfa : (fun τ => faceAmp p J (fieldFam η ζ τ) (resOrder h k μ J) w) =
          fun τ => pdMulti (resOrder h k μ J) (lJ J) (fieldFam η ζ τ) (glue J 0 w) :=
        funext fun τ => faceAmp_fieldFam_eq_pdMulti hη hζ hdeep p heq _ τ hw
      rw [hfa]
      exact mellinMom_pdMulti_fieldFam_zero hη hζ hμ _ (lJ J) (glue J 0 w)
    · -- other Taylor orders
      intro m hm hne
      rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ => ?_, mul_zero]
      rw [htop, hzero m, zero_mul]
      by_contra hall
      exact hne (hexact m hm fun j hj => by_contra fun hne' => hall ⟨j, hj, hne'⟩)
    · -- the resonant order lies in the index set whenever it resonates exactly
      intro hnot
      have hz : resonantTop k J (fun i => resOrder h k μ J i + h i) μ = 0 := by
        refine hzero _ ?_
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
          simp only [depthOf]
          omega
        · rw [if_neg (by rwa [mem_lJ]), Finset.mem_singleton]
          exact resOrder_of_not_mem hi
      rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ => ?_, mul_zero]
      rw [htop, hz, zero_mul]
  · -- faces of size `> c`: the face amplitude vanishes
    rw [if_neg hgt.ne']
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w hw => ?_, mul_zero]
    have hfa : (fun τ => faceAmp p J (fieldFam η ζ τ) m w) = fun _ => (0 : ℝ) :=
      funext fun τ => faceAmp_fieldFam_eq_zero hη hζ hdeep p hgt m τ hw
    rw [hfa, empFaceCoef_zero_fun]

/-- ★★ **Vanishing above the depth**: for `η` vanishing near the deep set, the empirical
coefficients of log degree `≥ c` vanish. -/
theorem empCoeff_eq_zero_of_deep (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ} {c : ℕ}
    (hdeep : DeepVanishing η 1 c) {q : ℕ} (hq : c ≤ q) :
    empCoeff η ζ h k μ q = 0 := by
  unfold empCoeff empCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro j hj
  have hj' : q ≤ j := (Finset.mem_Ico.1 hj).1
  rcases le_or_gt x.1.card j with hle | hgt
  · rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w _ =>
      empFaceCoef_eq_zero_of_card_le k x.1 _ _ μ hle, mul_zero]
  · have hcard : c < x.1.card := by omega
    rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w hw => ?_, mul_zero]
    have hfa : (fun τ => faceAmp (depthOf h k (cutoffOf h μ)) x.1 (fieldFam η ζ τ) x.2 w) =
        fun _ => (0 : ℝ) :=
      funext fun τ => faceAmp_fieldFam_eq_zero hη hζ hdeep _ hcard x.2 τ hw
    rw [hfa, empFaceCoef_zero_fun]

/-- ★★★ **The replacement rule**: the empirical top coefficient is the population top coefficient
of the amplitude `η · S_μ(ζ)/Γ(μ)` — exponent by exponent, the field enters through the
fluctuation function evaluated on the field. -/
theorem empCoeff_top_eq_smoothCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) h k 1 1 μ (c - 1) := by
  have hΓ : 0 < Real.Gamma μ := Real.Gamma_pos_of_pos hμ
  set S : (Fin d → ℝ) → ℝ := fun v => η v * fluctuation 1 μ (ζ v) with hS
  have hSc : ContDiff ℝ ∞ S := contDiff_mul_fluctuation hη hζ hμ
  have hA : (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) =
      fun v => (Real.Gamma μ)⁻¹ * S v := by
    funext v
    simp only [hS]
    ring
  have hAc : ContDiff ℝ ∞ fun v => (Real.Gamma μ)⁻¹ * S v := contDiff_const.mul hSc
  have hAdeep : JetsZeroOn (fun v => (Real.Gamma μ)⁻¹ * S v) (deepSet d 1 c) :=
    jetsZeroOn_of_deepVanishing hAc one_pos (hdeep.mono_fun fun v hv => by simp [hS, hv])
  rw [hA, smoothCoeff_eq_faceSum_top hAc h k hk one_pos one_pos μ hc hAdeep,
    empCoeff_eq_faceSum_top hη hζ hk hμ hc hdeep]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJc : J.card = c := (Finset.mem_filter.1 hJ).2
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
  congr 1
  rw [pdMulti_const_mul, faceCoeffInt_const_mul]
  by_cases hex : ∀ j ∈ J, 2 * (k j : ℝ) * μ = ((fun i => resOrder h k μ J i + h i) j : ℕ) + 1
  · rw [← hDJ, faceCoef_top_eq k hk one_pos one_pos J hJne _ hex]
    unfold resonantTop
    rw [if_pos hex, Real.one_rpow, hDJ, hJc]
    have hprod : ∏ i : {i // inJ J i}, 1 / (2 * (k i : ℝ)) =
        (∏ i : {i // inJ J i}, 2 * (k i : ℝ))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => one_div _
    rw [hprod]
    field_simp
    ring
  · push Not at hex
    obtain ⟨j, hj, hne⟩ := hex
    rw [← hDJ, faceCoef_top_eq_zero_of_not_exact k hk one_pos one_pos J _ hj hne,
      resonantTop_of_not_exact k J _ ⟨j, hj, hne⟩]
    ring

end SmoothEngine

end Grammar
