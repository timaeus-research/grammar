/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral
import Grammar.SmoothAmplitudeFamily
import Grammar.SmoothObservableCoeff

/-!
# Resonant support of the smooth expansion coefficients

Consult #127, Unit D6a. The smooth engine expands `∫_{(0,b]^d} F(v) v^h e^{−Nβ v^{2k}} dv` for a
smooth amplitude `F` as `∑_{μ,q} c_{μ,q} N^{−μ} (log N)^q`, with the coefficient system
`smoothCoeff F h k β b μ q` (`SmoothGeneral`, `SmoothGeneralDepth`). Each coefficient is a finite
sum over FACES `J ⊆ {1,…,d}` and Taylor multi-indices `m` supported on `J` of products

  `faceCoef k β b J (m + h) μ j · C(j, q) · ∫_{(0,b]^{Jᶜ}} G_{J,m}(w) w^h (w^{2k})^{−μ} S(w)^{j−q}`

where `faceCoef` collects the power–log coefficients of the monomial face integral
`∫_{(0,b]^J} ∏_{i∈J} u_i^{m_i+h_i} e^{−Nβ ∏_{i∈J} u_i^{2k_i}}` and `G_{J,m} = faceAmp p J F m` is
the `m`-th normal derivative of `F` along the face `{v_i = 0 : i ∈ J}`, with the complementary
Taylor remainders, evaluated at the face point with complementary coordinates `w`.

## Resonance

A coordinate `i` with data `(k_i, e_i)` is **resonant** at the exponent `μ` when
`2 k_i μ ∈ e_i + 1 + ℕ`. The one-dimensional integral `∫_0^b u^{e} e^{−N β u^{2k}} du` has a pole
of its Mellin transform at `μ` exactly when `i` is resonant there, and the power–log coefficient of
a product of such integrals at `(μ, j)` can only be nonzero when the log degree `j` is strictly
below the number of resonant coordinates — the multiplicity of the pole. The engine already knows
this for the abstract state density (`stateDensityRep_coeffAt_eq_zero_of_le`: the coefficient of
`(log N)^j` vanishes at log degree `j ≥ expMult w μ`, the number of coordinates with `w_i + 1 = μ`).
Here we thread that fact through the whole coefficient system.

* `resonantCount k e μ` is the number of resonant coordinates; it is ANTITONE in the exponent
  vector `e` (`resonantCount_le_of_le`: `2kμ ∈ e'+1+ℕ ⊆ e+1+ℕ` for `e ≤ e'`) and invariant under
  reindexing (`resonantCount_comp_equiv`).
* For the monomial `u^s` the Stage-1 weights are `monoWeights s k i + 1 = (s_i + 1)/(2k_i)`, so a
  coordinate contributing to `expMult` is resonant for `(k_i, e_i)` whenever `e ≤ s`, with
  `m = s_i − e_i` (`expMult_monoWeights_le_resonantCount`).
* The monomial lists feeding the spectral coefficients have support `≥ e` when the coefficient
  family is the monomial `u^e` (`monoFam_support_ge`, `scale_support_ge`, `truncList_support_ge`,
  `mul_support_ge`: products of monomial lists add multi-indices), whence
  `coeffTerm_eq_zero_of_resonantCount_le` → `spectralCoeff_eq_zero_of_resonantCount_le` →
  `familySpectralCoeff_eq_zero_of_resonantCount_le` (limit of the truncations) →
  `boxCoeff_eq_zero_of_resonantCount_le` → `faceMonoCoeff_eq_zero_of_resonantCount_le` → ★★
  `faceCoef_eq_zero_of_resonantCount_le`: the face coefficients vanish at log degree
  `j ≥ resonantCount (k|J) (e|J) μ`.

## Flat amplitudes

If all coordinate jets of `F` vanish on the closed face-in-box `{v ∈ [0,b]^d : v_i = 0, i ∈ J}`
(`JetsZeroOn`), then so do the jets of every coordinate derivative of `F`
(`JetsZeroOn.pdPow`, `JetsZeroOn.pdMulti`, by the commutation of coordinate derivatives), and the
iterated coordinate Taylor remainder over any list of DISTINCT coordinates vanishes on the face
(`remList_eq_zero_of_jetsZeroOn`): the remainder
`R_i^q G(v) = G(v) − ∑_{n<q} v_i^n/n! ∂_i^n G(v[i:=0])` only evaluates derivatives of `G` at
points of the face, which is closed under `v ↦ v[i := 0]`.
Hence the face amplitude `faceAmp p J F m` vanishes on the open box
(`faceAmp_eq_zero_of_jets_zero`) and the face coefficient integral is zero
(`faceCoeffInt_eq_zero_of_forall`).

## The support theorem

★★★ `smoothCoeffAtDepth_eq_zero_of_resonant`, `smoothCoeff_eq_zero_of_resonant`: if for every face
`J` with `q + 1 ≤ resonantCount (k|J) (h|J) μ` the jets of `F` vanish on the closed face-in-box,
then `smoothCoeff F h k β b μ q = 0`. Every face term `(J, m)` dies for one of two reasons: either
`resonantCount (k|J) (h|J) μ ≤ q ≤ j`, and then (by antitonicity, `m ≥ 0`) the face coefficient
`faceCoef k β b J (m+h) μ j` vanishes; or the resonance count exceeds `q`, and then the face
amplitude vanishes on the box. The corollary `smoothCoeff_eq_zero_of_eqOn_zero_resonant` takes the
hypothesis in the form "`F` vanishes on an open set containing each such closed face-in-box", using
`pdMulti_eqOn_of_isOpen`.

Non-claims: no sharpness (nonvanishing of the coefficients is a non-claim of the programme), no
statement about the coefficient at `(μ, q)` when only SOME of the resonant faces carry vanishing
jets, and the vanishing of `F` in the corollary is required on an OPEN neighbourhood of the closed
face-in-box (jets on the closed set suffice for the main theorem). No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

open MonoRep CoeffFamily

/-! ### The resonance count -/

open Classical in
/-- The number of coordinates `i` resonant at `μ` for the data `(k_i, e_i)`:
`2 k_i μ ∈ e_i + 1 + ℕ`. -/
noncomputable def resonantCount {ι : Type*} [Fintype ι] (k e : ι → ℕ) (μ : ℝ) : ℕ :=
  (univ.filter fun i => ∃ m : ℕ, 2 * (k i : ℝ) * μ = (e i : ℝ) + 1 + m).card

/-- A larger exponent vector resonates less often: `2kμ ∈ e' + 1 + ℕ ⊆ e + 1 + ℕ` for `e ≤ e'`. -/
theorem resonantCount_le_of_le {ι : Type*} [Fintype ι] (k : ι → ℕ) {e e' : ι → ℕ}
    (h : ∀ i, e i ≤ e' i) (μ : ℝ) : resonantCount k e' μ ≤ resonantCount k e μ := by
  classical
  unfold resonantCount
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨-, m, hm⟩ := hi
  refine ⟨Finset.mem_univ _, e' i - e i + m, ?_⟩
  rw [hm]
  push_cast [Nat.cast_sub (h i)]
  ring

/-- The resonance count is invariant under reindexing. -/
theorem resonantCount_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (k e : κ → ℕ) (μ : ℝ) : resonantCount (k ∘ σ) (e ∘ σ) μ = resonantCount k e μ := by
  classical
  unfold resonantCount
  exact Finset.card_equiv σ fun i => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-- A coordinate of the monomial `u^s` contributing to the multiplicity of `μ`
(`(s_i+1)/(2k_i) = μ`) is resonant for `(k_i, e_i)` whenever `e ≤ s`, with `m = s_i − e_i`. -/
theorem expMult_monoWeights_le_resonantCount {n : ℕ} (k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {e s : Fin (n + 1) → ℕ} (he : ∀ i, e i ≤ s i) (μ : ℝ) :
    expMult (monoWeights s k) μ ≤ resonantCount k e μ := by
  classical
  unfold expMult resonantCount
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, s i - e i, ?_⟩
  have hi' : ((s i : ℝ) + 1) / (2 * (k i : ℝ)) = μ := by
    have := hi.2
    simp only [monoWeights] at this
    linarith
  have hk' : (k i : ℝ) ≠ 0 := by have := hk i; positivity
  rw [Nat.cast_sub (he i), ← hi']
  field_simp
  ring

/-! ### Support of the monomial lists -/

theorem mem_mul {d : ℕ} {P Q : MonoRep d} {x : (Fin d → ℕ) × ℝ} (hx : x ∈ mul P Q) :
    ∃ s ∈ P, ∃ t ∈ Q, x = (s.1 + t.1, s.2 * t.2) := by
  unfold mul at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨s, hs, hx⟩ := hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨s, hs, t, ht, rfl⟩

/-- Products of monomial lists add multi-indices: a support lower bound on the left factor passes
to the product. -/
theorem mul_support_ge {d : ℕ} {e : Fin d → ℕ} {P : MonoRep d}
    (hP : ∀ s ∈ P, s.2 ≠ 0 → ∀ i, e i ≤ s.1 i) (Q : MonoRep d) :
    ∀ x ∈ mul P Q, x.2 ≠ 0 → ∀ i, e i ≤ x.1 i := by
  intro x hx hx2 i
  obtain ⟨s, hs, t, ht, rfl⟩ := mem_mul hx
  exact (hP s hs (left_ne_zero_of_mul hx2) i).trans (Nat.le_add_right _ _)

theorem truncList_support_ge {d : ℕ} {e : Fin d → ℕ} {c : CoeffFamily d}
    (hc : ∀ γ, c γ ≠ 0 → ∀ i, e i ≤ γ i) (m : ℕ) :
    ∀ s ∈ truncList c m, s.2 ≠ 0 → ∀ i, e i ≤ s.1 i := by
  intro s hs
  unfold truncList at hs
  rw [List.mem_map] at hs
  obtain ⟨γ, -, rfl⟩ := hs
  exact hc γ

theorem scale_support_ge {d : ℕ} {e : Fin d → ℕ} {c : CoeffFamily d}
    (hc : ∀ γ, c γ ≠ 0 → ∀ i, e i ≤ γ i) (b : ℝ) :
    ∀ γ, scale c b γ ≠ 0 → ∀ i, e i ≤ γ i := by
  intro γ hγ
  unfold scale at hγ
  exact hc γ (left_ne_zero_of_mul hγ)

/-- The monomial family `u^e` is supported at `e`. -/
theorem monoFam_support_ge {d : ℕ} (e : Fin d → ℕ) :
    ∀ γ, monoFam e γ ≠ 0 → ∀ i, e i ≤ γ i := by
  intro γ hγ i
  unfold monoFam at hγ
  split_ifs at hγ with h
  · rw [h]
  · exact absurd rfl hγ

/-! ### Vanishing of the spectral coefficients above the resonance count -/

/-- The per-phase-order coefficient `coeffTerm` vanishes at log degree `j ≥ resonantCount k (h+e) μ`
when every term of `P` with nonzero coefficient has multi-index `≥ e`. -/
theorem coeffTerm_eq_zero_of_resonantCount_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β a : ℝ) (p : ℕ) (μ : ℝ) {j : ℕ} (P : MonoRep (n + 1)) (e : Fin (n + 1) → ℕ)
    (hP : ∀ s ∈ P, s.2 ≠ 0 → ∀ i, e i ≤ s.1 i) (hj : resonantCount k (h + e) μ ≤ j) :
    coeffTerm n h k β a p μ j P = 0 := by
  unfold coeffTerm
  rw [List.sum_eq_zero, mul_zero]
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  by_cases hs2 : s.2 = 0
  · rw [hs2, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro q hq
    rw [stateDensityRep_coeffAt_eq_zero_of_le, zero_mul, zero_mul]
    calc expMult (monoWeights (h + s.1) k) μ
        ≤ resonantCount k (h + e) μ :=
          expMult_monoWeights_le_resonantCount k hk
            (fun i => Nat.add_le_add_left (hP s hs hs2 i) (h i)) μ
      _ ≤ j := hj
      _ ≤ q := (Finset.mem_Ico.1 hq).1

theorem spectralCoeff_eq_zero_of_resonantCount_le (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (ξ η : MonoRep (n + 1)) {e : Fin (n + 1) → ℕ}
    (hη : ∀ s ∈ η, s.2 ≠ 0 → ∀ i, e i ≤ s.1 i) {μ : ℝ} {j : ℕ}
    (hj : resonantCount k (h + e) μ ≤ j) : spectralCoeff n h k β ξ η μ j = 0 := by
  unfold spectralCoeff
  have hz : ∀ p : ℕ, β ^ p / (p.factorial : ℝ) *
      coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p)) = 0 := fun p => by
    rw [coeffTerm_eq_zero_of_resonantCount_le n h k hk β _ p μ _ e (mul_support_ge hη _) hj,
      mul_zero]
  simp_rw [hz]
  exact tsum_zero

/-- The family spectral coefficients vanish at log degree `j ≥ resonantCount k (h+e) μ` when the
coefficient family `cη` is supported on multi-indices `≥ e`. -/
theorem familySpectralCoeff_eq_zero_of_resonantCount_le (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {e : Fin (n + 1) → ℕ}
    (hsupp : ∀ γ, cη γ ≠ 0 → ∀ i, e i ≤ γ i) {μ : ℝ} {j : ℕ}
    (hj : resonantCount k (h + e) μ ≤ j) : familySpectralCoeff n h k β cξ cη μ j = 0 := by
  have h1 := tendsto_truncCoeff n h k hk β hβ hξ hη μ j
  have h2 : Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 0) := by
    have : truncCoeff n h k β cξ cη μ j = fun _ => 0 := funext fun m =>
      spectralCoeff_eq_zero_of_resonantCount_le n h k hk β _ _ (truncList_support_ge hsupp m) hj
    rw [this]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

theorem boxCoeff_eq_zero_of_resonantCount_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummableAt cξ b) (hη : AbsSummableAt cη b) {e : Fin (n + 1) → ℕ}
    (hsupp : ∀ γ, cη γ ≠ 0 → ∀ i, e i ≤ γ i) {μ : ℝ} {j : ℕ}
    (hj : resonantCount k (h + e) μ ≤ j) : boxCoeff n h k β b cξ cη μ j = 0 := by
  unfold boxCoeff
  rw [Finset.sum_eq_zero (s := Finset.Ico j (n + 1)), mul_zero]
  intro q hq
  rw [familySpectralCoeff_eq_zero_of_resonantCount_le n h k hk β hβ
    (AbsSummable.of_scale hb.le hξ) (AbsSummable.of_scale hb.le hη) (scale_support_ge hsupp b)
    (hj.trans (Finset.mem_Ico.1 hq).1), zero_mul, zero_mul]

/-- The face monomial coefficients vanish at log degree `j ≥ resonantCount k e μ`. -/
theorem faceMonoCoeff_eq_zero_of_resonantCount_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} {j : ℕ}
    (hj : resonantCount k e μ ≤ j) : faceMonoCoeff k e β b μ j = 0 := by
  unfold faceMonoCoeff
  refine boxCoeff_eq_zero_of_resonantCount_le _ 0 (k ∘ (faceEquiv ι).symm) (fun i => hk _) β hβ hb
    (absSummableAt_zero b) (absSummableAt_monoFam _ b) (monoFam_support_ge _) ?_
  rw [zero_add, resonantCount_comp_equiv]
  exact hj

/-- ★★ **Resonant support of the face coefficients**: `faceCoef k β b J e μ j = 0` for
`j ≥ resonantCount (k|J) (e|J) μ` (the empty face has zero coefficients). -/
theorem faceCoef_eq_zero_of_resonantCount_le {d : ℕ} (k : Fin d → ℕ) (β b : ℝ)
    (J : Finset (Fin d)) (e : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {μ : ℝ}
    {j : ℕ} (hj : resonantCount (fun i : {i // inJ J i} => k i) (fun i => e i) μ ≤ j) :
    faceCoef k β b J e μ j = 0 := by
  unfold faceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    exact faceMonoCoeff_eq_zero_of_resonantCount_le (fun i : {i // inJ J i} => k i)
      (fun i => e i) (fun i => hk i) hβ hb hj
  · rfl

/-! ### Flat amplitudes: vanishing jets on a face kill the remainders -/

variable {d : ℕ}

/-- All coordinate jets of `G` vanish on `S`. -/
def JetsZeroOn (G : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) : Prop :=
  ∀ α : Fin d → ℕ, ∀ v ∈ S, pdMulti α (List.finRange d) G v = 0

theorem JetsZeroOn.apply {G : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} (h : JetsZeroOn G S)
    {v : Fin d → ℝ} (hv : v ∈ S) : G v = 0 := by
  have := h 0 v hv
  rwa [pdMulti_zero] at this

theorem JetsZeroOn.pdPow {G : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} (hG : ContDiff ℝ ∞ G)
    (h : JetsZeroOn G S) (i : Fin d) (n : ℕ) : JetsZeroOn (pdPow i n G) S := by
  intro α v hv
  rw [← pdMulti_single_finRange hG i n, pdMulti_add hG]
  exact h _ v hv

theorem JetsZeroOn.pdMulti {G : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} (hG : ContDiff ℝ ∞ G)
    (h : JetsZeroOn G S) (m : Fin d → ℕ) (l : List (Fin d)) :
    JetsZeroOn (pdMulti m l G) S := by
  induction l generalizing G with
  | nil => exact h
  | cons i l ih =>
    rw [pdMulti_cons]
    exact (ih hG h).pdPow (contDiff_pdMulti hG m l) i (m i)

/-- The iterated coordinate Taylor remainder over distinct coordinates vanishes at every point of a
set closed under `v ↦ v[i := 0]` on which all jets of the function vanish. -/
theorem remList_eq_zero_of_jetsZeroOn (p : Fin d → ℕ) {S : Set (Fin d → ℝ)}
    (hS : ∀ v ∈ S, ∀ i, Function.update v i 0 ∈ S) :
    ∀ l : List (Fin d), l.Nodup → ∀ G : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G → JetsZeroOn G S →
      ∀ v ∈ S, remList p l G v = 0 := by
  intro l
  induction l with
  | nil =>
    intro _ G _ hGS v hv
    rw [remList_nil]
    exact hGS.apply hv
  | cons i l ih =>
    intro hl G hG hGS v hv
    have hil : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    rw [remList_cons]
    simp only [coordRem, coordTaylor]
    rw [ih hl' G hG hGS v hv, Finset.sum_eq_zero, sub_zero]
    intro m _
    rw [pdPow_remList p hG hil,
      ih hl' _ (contDiff_pdPow hG i m) (hGS.pdPow hG i m) _ (hS v hv i), mul_zero]

/-- The closed face-in-box `{v ∈ [0,b]^d : v_i = 0, i ∈ J}`. -/
def closedFaceBox (d : ℕ) (b : ℝ) (J : Finset (Fin d)) : Set (Fin d → ℝ) :=
  {v ∈ closedBox d b | ∀ i ∈ J, v i = 0}

theorem closedFaceBox_update {b : ℝ} (hb : 0 ≤ b) (J : Finset (Fin d)) :
    ∀ v ∈ closedFaceBox d b J, ∀ i, Function.update v i 0 ∈ closedFaceBox d b J := by
  intro v hv i
  refine ⟨fun j _ => ?_, fun j hj => ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [Function.update_self]
      exact ⟨le_rfl, hb⟩
    · rw [Function.update_of_ne hji]
      exact hv.1 j (Set.mem_univ _)
  · by_cases hji : j = i
    · subst hji
      exact Function.update_self ..
    · rw [Function.update_of_ne hji]
      exact hv.2 j hj

theorem glue_zero_mem_closedFaceBox (J : Finset (Fin d)) {b : ℝ} (hb : 0 < b)
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} b) :
    glue J 0 w ∈ closedFaceBox d b J := by
  refine ⟨fun i _ => glue_zero_mem_Icc J hb hw i, fun i hi => ?_⟩
  rw [glue_apply_of_mem J _ _ hi]
  rfl

/-- ★ **Flat amplitudes**: if all jets of `F` vanish on the closed face-in-box of `J`, the face
amplitude `faceAmp p J F m` vanishes on the open box. -/
theorem faceAmp_eq_zero_of_jets_zero (p : Fin d → ℕ) (J : Finset (Fin d)) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (m : Fin d → ℕ) {b : ℝ} (hb : 0 < b)
    (hJ : ∀ v ∈ closedBox d b, (∀ i ∈ J, v i = 0) →
      ∀ α : Fin d → ℕ, pdMulti α (List.finRange d) F v = 0) :
    ∀ w ∈ box {i // ¬ inJ J i} b, faceAmp p J F m w = 0 := by
  intro w hw
  have hFS : JetsZeroOn F (closedFaceBox d b J) := fun α v hv => hJ v hv.1 hv.2 α
  unfold faceAmp
  exact remList_eq_zero_of_jetsZeroOn p (closedFaceBox_update hb.le J) (lK J) (nodup_lK J) _
    (contDiff_pdMulti hF m _) (hFS.pdMulti hF m _) _ (glue_zero_mem_closedFaceBox J hb hw)

theorem faceCoeffInt_eq_zero_of_forall {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℝ} (h a : ι → ℕ)
    (b μ : ℝ) (e : ℕ) (hG : ∀ w ∈ box ι b, G w = 0) : faceCoeffInt G h a b μ e = 0 := by
  unfold faceCoeffInt
  exact setIntegral_eq_zero_of_forall_eq_zero fun w hw => by simp [hG w hw]

/-! ### The support theorem -/

/-- ★★★ **Resonant support of the depth-`p` coefficients**: if, for every face `J` whose
resonance count at `μ` exceeds `q`, all jets of `F` vanish on the closed face-in-box of `J`, then
the coefficient of `N^{−μ}(log N)^q` vanishes. -/
theorem smoothCoeffAtDepth_eq_zero_of_resonant {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k p : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ)
    (hres : ∀ J : Finset (Fin d),
      q + 1 ≤ resonantCount (fun i : {i // inJ J i} => k i) (fun i => h i) μ →
      ∀ v ∈ closedBox d b, (∀ i ∈ J, v i = 0) →
        ∀ α : Fin d → ℕ, pdMulti α (List.finRange d) F v = 0) :
    smoothCoeffAtDepth F h k p β b μ q = 0 := by
  unfold smoothCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro j hj
  by_cases hJ : q + 1 ≤ resonantCount (fun i : {i // inJ x.1 i} => k i) (fun i => h i) μ
  · rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _
      (faceAmp_eq_zero_of_jets_zero p x.1 hF x.2 hb (hres x.1 hJ)), mul_zero]
  · have hle : resonantCount (fun i : {i // inJ x.1 i} => k i) (fun i => h i) μ ≤ j := by
      have := (Finset.mem_Ico.1 hj).1
      omega
    have hmono := resonantCount_le_of_le (fun i : {i // inJ x.1 i} => k i)
      (e := fun i : {i // inJ x.1 i} => h i) (e' := fun i : {i // inJ x.1 i} => x.2 i + h i)
      (fun i => Nat.le_add_left _ _) μ
    rw [faceCoef_eq_zero_of_resonantCount_le k β b x.1 (fun i => x.2 i + h i) hk hβ hb
      (hmono.trans hle), zero_mul, zero_mul]

/-- ★★★ **Resonant support of the canonical smooth coefficients**. -/
theorem smoothCoeff_eq_zero_of_resonant {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ)
    (hres : ∀ J : Finset (Fin d),
      q + 1 ≤ resonantCount (fun i : {i // inJ J i} => k i) (fun i => h i) μ →
      ∀ v ∈ closedBox d b, (∀ i ∈ J, v i = 0) →
        ∀ α : Fin d → ℕ, pdMulti α (List.finRange d) F v = 0) :
    smoothCoeff F h k β b μ q = 0 := by
  unfold smoothCoeff
  exact smoothCoeffAtDepth_eq_zero_of_resonant hF h k _ hk hβ hb μ q hres

/-- The support theorem with the hypothesis "`F` vanishes on an open set containing the closed
face-in-box" for every face whose resonance count at `μ` exceeds `q`. -/
theorem smoothCoeff_eq_zero_of_eqOn_zero_resonant {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ)
    (hres : ∀ J : Finset (Fin d),
      q + 1 ≤ resonantCount (fun i : {i // inJ J i} => k i) (fun i => h i) μ →
      ∃ O : Set (Fin d → ℝ), IsOpen O ∧ {v ∈ closedBox d b | ∀ i ∈ J, v i = 0} ⊆ O ∧
        EqOn F 0 O) :
    smoothCoeff F h k β b μ q = 0 := by
  refine smoothCoeff_eq_zero_of_resonant hF h k hk hβ hb μ q fun J hJ v hv hvJ α => ?_
  obtain ⟨O, hO, hSO, hFO⟩ := hres J hJ
  have hvO : v ∈ O := hSO ⟨hv, hvJ⟩
  rw [pdMulti_eqOn_of_isOpen hO hFO α (List.finRange d) hvO]
  exact congrFun (pdMulti_zeroFun α (List.finRange d)) v

end SmoothEngine

end Grammar
