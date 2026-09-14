/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral
import Grammar.SmoothFamilyIntegral
import Grammar.SmoothCoreDecomposition
import Grammar.SmoothBridgeConsumer

/-!
# Finite-jet determination of the smooth coefficients (consult #122 U1–U2)

The canonical coefficients of the smooth-amplitude engine depend on the amplitude only through
finitely many coordinate derivatives on the chart-local divisor — the coordinate walls
`walls d = ⋃ᵢ {vᵢ = 0}` of the box. Two amplitudes with equal coordinate jets of orders `α ≤ p`
(`EqJetsOn`) on `walls ∩ [0,b]^d` have the same flat face amplitudes (★ `faceAmp_congr`: the
iterated Taylor remainder `R_K^p ∂^m F (0_J, w)` is a combination of derivatives at points with
`v_J = 0`, `J ≠ ∅`, by `remList_congr`), hence the same depth-`p` coefficient system
(★★ `smoothCoeffAtDepth_congr`; the empty face carries zero coefficients) and the same canonical
coefficients (★★ `smoothCoeff_congr`, with the explicit componentwise order
`depthOf h k (cutoffOf h μ)` and the total order `jetOrder h k μ`). Integrated over a chart base
and summed over the charts this is the finite-jet determination of the intrinsic coefficient of a
`SmoothCoreDecomposition` (★★ `familyCoeff_congr`, `SmoothCoreDecomposition.coeff_congr`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The chart-local divisor and finite jets -/

/-- The chart-local divisor: the union of the coordinate walls `{v_i = 0}`. -/
def walls (d : ℕ) : Set (Fin d → ℝ) := {v | ∃ i, v i = 0}

theorem mem_walls {v : Fin d → ℝ} : v ∈ walls d ↔ ∃ i, v i = 0 := Iff.rfl

theorem update_zero_mem_walls (v : Fin d → ℝ) (i : Fin d) : Function.update v i 0 ∈ walls d :=
  ⟨i, Function.update_self ..⟩

/-- `walls ∩ [0,b]^d` is closed under the coordinate projections `v ↦ v[i := 0]`. -/
theorem update_zero_mem_walls_inter_closedBox {b : ℝ} (hb : 0 ≤ b) {v : Fin d → ℝ}
    (hv : v ∈ walls d ∩ closedBox d b) (i : Fin d) :
    Function.update v i 0 ∈ walls d ∩ closedBox d b := by
  refine ⟨update_zero_mem_walls v i, mem_closedBox.2 fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact ⟨le_rfl, hb⟩
  · rw [Function.update_of_ne hj]
    exact mem_closedBox.1 hv.2 j

/-- **Equal finite jets**: equal coordinate partial derivatives `∂^α` of all orders `α ≤ p`
(componentwise) at every point of `s`. -/
def EqJetsOn (p : Fin d → ℕ) (F G : (Fin d → ℝ) → ℝ) (s : Set (Fin d → ℝ)) : Prop :=
  ∀ α : Fin d → ℕ, (∀ i, α i ≤ p i) → ∀ v ∈ s,
    pdMulti α (List.finRange d) F v = pdMulti α (List.finRange d) G v

theorem EqJetsOn.mono {p : Fin d → ℕ} {F G : (Fin d → ℝ) → ℝ} {s t : Set (Fin d → ℝ)}
    (h : EqJetsOn p F G s) (hts : t ⊆ s) : EqJetsOn p F G t :=
  fun α hα v hv => h α hα v (hts hv)

theorem EqJetsOn.of_le {p p' : Fin d → ℕ} {F G : (Fin d → ℝ) → ℝ} {s : Set (Fin d → ℝ)}
    (h : EqJetsOn p' F G s) (hp : ∀ i, p i ≤ p' i) : EqJetsOn p F G s :=
  fun α hα v hv => h α (fun i => (hα i).trans (hp i)) v hv

/-- Equal jets of all TOTAL orders `∑ α ≤ ∑ p` give equal jets of componentwise orders `≤ p`. -/
theorem EqJetsOn.of_total {p : Fin d → ℕ} {F G : (Fin d → ℝ) → ℝ} {s : Set (Fin d → ℝ)}
    (h : ∀ α : Fin d → ℕ, ∑ i, α i ≤ ∑ i, p i → ∀ v ∈ s,
      pdMulti α (List.finRange d) F v = pdMulti α (List.finRange d) G v) :
    EqJetsOn p F G s :=
  fun α hα v hv => h α (Finset.sum_le_sum fun i _ => hα i) v hv

/-! ### The iterated remainder depends only on the jets on the walls -/

variable (p : Fin d → ℕ)

/-- ★ **Jet determination of the iterated remainder**: on a set closed under the coordinate
projections, `R_l^p H` depends on `H` only through the derivatives `∂^α H`, `α ≤ p` on `l`, at the
points of the set. -/
theorem remList_congr {s : Set (Fin d → ℝ)} (hs : ∀ v ∈ s, ∀ i, Function.update v i 0 ∈ s)
    {l : List (Fin d)} (hl : l.Nodup) :
    ∀ {H₁ H₂ : (Fin d → ℝ) → ℝ}, ContDiff ℝ ∞ H₁ → ContDiff ℝ ∞ H₂ →
      (∀ α : Fin d → ℕ, (∀ i ∈ l, α i ≤ p i) → ∀ v ∈ s, pdMulti α l H₁ v = pdMulti α l H₂ v) →
      ∀ v ∈ s, remList p l H₁ v = remList p l H₂ v := by
  induction l with
  | nil =>
    intro H₁ H₂ _ _ hyp v hv
    exact hyp 0 (fun i hi => (List.not_mem_nil hi).elim) v hv
  | cons i l ih =>
    intro H₁ H₂ h₁ h₂ hyp v hv
    have hil : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    have hyp' : ∀ m : ℕ, m ≤ p i → ∀ α : Fin d → ℕ, (∀ j ∈ l, α j ≤ p j) → ∀ v ∈ s,
        pdMulti α l (pdPow i m H₁) v = pdMulti α l (pdPow i m H₂) v := by
      intro m hm α hα v hv
      have key : ∀ H : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ H →
          pdMulti α l (pdPow i m H) v = pdMulti (Function.update α i m) (i :: l) H v := by
        intro H hH
        rw [← pdPow_pdMulti hH α i m l, pdMulti_cons, Function.update_self,
          pdMulti_update_of_not_mem hil]
      rw [key H₁ h₁, key H₂ h₂]
      refine hyp _ (fun j hj => ?_) v hv
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [Function.update_self]
        exact hm
      · have hji : j ≠ i := fun h => hil (h ▸ hj)
        rw [Function.update_of_ne hji]
        exact hα j hj
    have h0 := ih hl' h₁ h₂ (hyp' 0 (Nat.zero_le _)) v hv
    have hsum : ∀ m ∈ Finset.range (p i), pdPow i m (remList p l H₁) (Function.update v i 0) =
        pdPow i m (remList p l H₂) (Function.update v i 0) := by
      intro m hm
      rw [pdPow_remList p h₁ hil m, pdPow_remList p h₂ hil m]
      exact ih hl' (contDiff_pdPow h₁ i m) (contDiff_pdPow h₂ i m)
        (hyp' m (Finset.mem_range.1 hm).le) _ (hs v hv i)
    simp only [remList_cons, coordRem, coordTaylor_apply]
    rw [h0, Finset.sum_congr rfl fun m hm => by rw [hsum m hm]]

/-- The mixed derivative `∂^m` on `J` and `∂^α` on the complement, over all coordinates. -/
theorem pdMulti_lK_pdMulti_lJ_eq {H : (Fin d → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (J : Finset (Fin d))
    (m α : Fin d → ℕ) :
    pdMulti α (lK J) (pdMulti m (lJ J) H) =
      pdMulti (fun i => if i ∈ J then m i else α i) (List.finRange d) H := by
  rw [← pdMulti_perm hH _ (List.perm_append_comm.trans (lJ_append_lK_perm J)), pdMulti_append,
    pdMulti_congr (m := fun i => if i ∈ J then m i else α i) (m' := m) (l := lJ J)
      (fun i hi => if_pos ((mem_lJ J).1 hi)) H,
    pdMulti_congr (m := fun i => if i ∈ J then m i else α i) (m' := α) (l := lK J)
      (fun i hi => if_neg ((mem_lK J).1 hi)) (pdMulti m (lJ J) H)]

theorem lt_of_mem_idxL {J : Finset (Fin d)} {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {i : Fin d}
    (hi : i ∈ J) : m i < p i := by
  have := (Fintype.mem_piFinset.1 hm) i
  simpa [mem_lJ, hi] using this

/-- ★ **Jet determination of the flat face amplitude**: for a nonempty face `J`, the flat face
amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)` on the box depends on `F` only through the jets of
orders `≤ p` on `walls ∩ [0,b]^d`. -/
theorem faceAmp_congr {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {b : ℝ} (hb : 0 < b) {J : Finset (Fin d)} (hJ : J.Nonempty)
    (hjet : EqJetsOn p F G (walls d ∩ closedBox d b)) {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J))
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} b) :
    faceAmp p J F m w = faceAmp p J G m w := by
  unfold faceAmp
  refine remList_congr p (fun v hv i => update_zero_mem_walls_inter_closedBox hb.le hv i)
    (nodup_lK J) (contDiff_pdMulti hF m _) (contDiff_pdMulti hG m _) ?_ _ ?_
  · intro α hα v hv
    rw [pdMulti_lK_pdMulti_lJ_eq hF, pdMulti_lK_pdMulti_lJ_eq hG]
    refine hjet _ (fun i => ?_) v hv
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      exact (lt_of_mem_idxL p hm hi).le
    · rw [if_neg hi]
      exact hα i ((mem_lK J).2 hi)
  · obtain ⟨i, hi⟩ := hJ
    refine ⟨⟨i, ?_⟩, mem_closedBox.2 (glue_zero_mem_Icc J hb hw)⟩
    rw [glue_apply_of_mem J _ _ hi]
    rfl

/-! ### Jet determination of the coefficient systems -/

/-- ★★ **Jet determination at depth `p`**: the depth-`p` coefficient system depends on the
amplitude only through its jets of orders `≤ p` on the walls of the box. -/
theorem smoothCoeffAtDepth_congr {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ) (β : ℝ) {b : ℝ} (hb : 0 < b)
    (hjet : EqJetsOn p F G (walls d ∩ closedBox d b)) (μ : ℝ) (q : ℕ) :
    smoothCoeffAtDepth F h k p β b μ q = smoothCoeffAtDepth G h k p β b μ q := by
  unfold smoothCoeffAtDepth
  refine Finset.sum_congr rfl fun x hx => ?_
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  by_cases hJ : x.1.Nonempty
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold faceCoeffInt
    exact setIntegral_congr_fun (measurableSet_box b) fun w hw => by
      rw [faceAmp_congr p hF hG hb hJ hjet hm hw]
  · have h0 : faceCoef k β b x.1 (fun i => x.2 i + h i) = fun _ _ => 0 := by
      unfold faceCoef
      rw [dif_neg hJ]
    simp only [h0, zero_mul, Finset.sum_const_zero]

/-- The total jet order of the canonical coefficient at `μ`:
`∑ᵢ (2kᵢ · max(⌊μ⌋₊ + 1, ∑ h + 1) − hᵢ)`. -/
noncomputable def jetOrder (h k : Fin d → ℕ) (μ : ℝ) : ℕ := ∑ i, depthOf h k (cutoffOf h μ) i

theorem jetOrder_eq (h k : Fin d → ℕ) (μ : ℝ) :
    jetOrder h k μ = ∑ i, (2 * k i * max (⌊μ⌋₊ + 1) (∑ j, h j + 1) - h i) := rfl

/-- ★★ **Finite-jet determination of the canonical coefficients**: `smoothCoeff F μ q` depends
on `F` only through its coordinate jets of componentwise orders `≤ depthOf h k (cutoffOf h μ)`
on `walls ∩ [0,b]^d`. -/
theorem smoothCoeff_congr {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (h k : Fin d → ℕ) (β : ℝ) {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hjet : EqJetsOn (depthOf h k (cutoffOf h μ)) F G (walls d ∩ closedBox d b)) (q : ℕ) :
    smoothCoeff F h k β b μ q = smoothCoeff G h k β b μ q :=
  smoothCoeffAtDepth_congr _ hF hG h k β hb hjet μ q

/-- ★★ The canonical coefficient at `μ` depends only on the jets of total order `≤ jetOrder h k μ`
on the walls. -/
theorem smoothCoeff_congr_of_total {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ) (β : ℝ) {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hjet : ∀ α : Fin d → ℕ, ∑ i, α i ≤ jetOrder h k μ → ∀ v ∈ walls d ∩ closedBox d b,
      pdMulti α (List.finRange d) F v = pdMulti α (List.finRange d) G v) (q : ℕ) :
    smoothCoeff F h k β b μ q = smoothCoeff G h k β b μ q :=
  smoothCoeff_congr hF hG h k β hb (EqJetsOn.of_total hjet) q

/-- **Regression, `d = 1`**: the coefficients depend only on `F⁽ⁿ⁾(0)`, `n ≤ 2k·L − h`. -/
theorem smoothCoeff_congr_dim_one {F G : (Fin 1 → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (h k : Fin 1 → ℕ) (β : ℝ) {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hjet : ∀ n ≤ depthOf h k (cutoffOf h μ) 0, pdPow 0 n F 0 = pdPow 0 n G 0) (q : ℕ) :
    smoothCoeff F h k β b μ q = smoothCoeff G h k β b μ q := by
  refine smoothCoeff_congr hF hG h k β hb (fun α hα v hv => ?_) q
  obtain ⟨⟨i, hi⟩, -⟩ := hv
  have hv0 : v = 0 := funext fun j => by rw [Subsingleton.elim j i]; exact hi
  have hl : List.finRange 1 = [0] := rfl
  rw [hv0, hl]
  simp only [pdMulti_cons, pdMulti_nil]
  exact hjet _ (hα 0)

/-! ### Families and core decompositions -/

/-- ★★ **Jet determination of the integrated coefficients**: the family coefficient at `μ` depends
on the amplitude family only through the fibrewise jets of orders `≤ depthOf h k (cutoffOf h μ)`
on the walls. -/
theorem familyCoeff_congr {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (ν : Measure S)
    {b : ℝ} (hb : 0 < b) (F G : SmoothAmplitudeFamily S d b) (h k : Fin d → ℕ) (βf : S → ℝ)
    {μ : ℝ} (hjet : ∀ s, EqJetsOn (depthOf h k (cutoffOf h μ)) (F s) (G s)
      (walls d ∩ closedBox d b)) (q : ℕ) :
    familyCoeff ν F h k βf b μ q = familyCoeff ν G h k βf b μ q := by
  unfold familyCoeff
  exact integral_congr_ae (Eventually.of_forall fun s =>
    smoothCoeff_congr (F.smooth s) (G.smooth s) h k (βf s) hb (hjet s) q)

/-- ★★ Two smooth core presentations with the same chart data (base measure, exponents, box, phase
unit) and amplitude families with equal wall jets have the same integrated coefficients. -/
theorem SmoothCorePresentation.familyCoeff_congr {U : Type*} [MeasurableSpace U]
    {D D' : LocalisationData U} {target target' : Measure U} {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] (C : SmoothCorePresentation D target S d)
    (C' : SmoothCorePresentation D' target' S d) (hν : C.ν = C'.ν) (hh : C.h = C'.h)
    (hk : C.k = C'.k) (hβ : C.βf = C'.βf) (hb : C.b = C'.b) {μ : ℝ}
    (hjet : ∀ s, EqJetsOn (depthOf C.h C.k (cutoffOf C.h μ)) (C.amp s) (C'.amp s)
      (walls d ∩ closedBox d C.b)) (q : ℕ) :
    familyCoeff C.ν C.amp C.h C.k C.βf C.b μ q =
      familyCoeff C'.ν C'.amp C'.h C'.k C'.βf C'.b μ q := by
  obtain ⟨ν, h, k, _, b, b_pos, βf, _, _, Φ, _, ρ, _, _, amp, _, _, _⟩ := C
  obtain ⟨ν', h', k', _, b', _, βf', _, _, Φ', _, ρ', _, _, amp', _, _, _⟩ := C'
  dsimp only at hν hh hk hβ hb hjet ⊢
  subst hν hh hk hβ hb
  exact SmoothEngine.familyCoeff_congr ν b_pos amp amp' h k βf hjet q

/-- ★★ **Finite-jet determination of the intrinsic coefficients**: two smooth core decompositions
with the same chart data whose amplitude families have equal wall jets of orders
`≤ depthOf h k (cutoffOf h μ)` (chartwise) have the same global coefficient at `(μ, q)`. -/
theorem SmoothCoreDecomposition.coeff_congr {U : Type*} [MeasurableSpace U]
    {D D' : LocalisationData U} {M : ℕ} {S : Fin M → Type*} [∀ I, TopologicalSpace (S I)]
    [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ} (A : SmoothCoreDecomposition D M S dim)
    (A' : SmoothCoreDecomposition D' M S dim) (hν : ∀ I, (A.chart I).ν = (A'.chart I).ν)
    (hh : ∀ I, (A.chart I).h = (A'.chart I).h) (hk : ∀ I, (A.chart I).k = (A'.chart I).k)
    (hβ : ∀ I, (A.chart I).βf = (A'.chart I).βf) (hb : ∀ I, (A.chart I).b = (A'.chart I).b)
    {μ : ℝ} (hjet : ∀ I s, EqJetsOn (depthOf (A.chart I).h (A.chart I).k (cutoffOf (A.chart I).h μ))
      ((A.chart I).amp s) ((A'.chart I).amp s) (walls (dim I) ∩ closedBox (dim I) (A.chart I).b))
    (q : ℕ) : A.coeff μ q = A'.coeff μ q := by
  unfold SmoothCoreDecomposition.coeff
  exact Finset.sum_congr rfl fun I _ => (A.chart I).familyCoeff_congr (A'.chart I) (hν I) (hh I)
    (hk I) (hβ I) (hb I) (hjet I) q

/-! ### Derivatives on a closed box of functions smooth on an open neighbourhood -/

theorem pd_eq_fderiv_of_differentiableAt {G : (Fin d → ℝ) → ℝ} {v : Fin d → ℝ}
    (hG : DifferentiableAt ℝ G v) (i : Fin d) : pd i G v = fderiv ℝ G v (Pi.single i 1) := by
  unfold pd line
  have hG' : DifferentiableAt ℝ G (Function.update v i (v i)) := by
    rwa [Function.update_eq_self]
  have h := hG'.hasFDerivAt.comp_hasDerivAt (v i) (hasDerivAt_update v i (v i))
  rw [Function.update_eq_self] at h
  exact h.deriv

variable {V : Set (Fin d → ℝ)}

theorem contDiffOn_pd (hV : IsOpen V) {G : (Fin d → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G V)
    (i : Fin d) : ContDiffOn ℝ ∞ (pd i G) V :=
  ((hG.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const).congr fun v hv =>
    pd_eq_fderiv_of_differentiableAt
      ((hG.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hv)) i

theorem contDiffOn_pdPow (hV : IsOpen V) {G : (Fin d → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G V)
    (i : Fin d) (q : ℕ) : ContDiffOn ℝ ∞ (pdPow i q G) V := by
  induction q generalizing G with
  | zero => exact hG
  | succ q ih => rw [pdPow_succ]; exact ih (contDiffOn_pd hV hG i)

theorem contDiffOn_pdMulti (hV : IsOpen V) {G : (Fin d → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G V)
    (m : Fin d → ℕ) (l : List (Fin d)) : ContDiffOn ℝ ∞ (pdMulti m l G) V := by
  induction l generalizing G with
  | nil => exact hG
  | cons i l ih => exact contDiffOn_pdPow hV (ih hG) i (m i)

/-- Coordinate derivatives on the closed box `[−a,a]^d` of functions smooth on an open
neighbourhood are determined by the values on the box (one-sided derivatives at the boundary). -/
theorem pd_eqOn_centeredBox (hV : IsOpen V) {a : ℝ} (ha : 0 < a) (hBV : centeredBox d a ⊆ V)
    {G₁ G₂ : (Fin d → ℝ) → ℝ} (h₁ : ContDiffOn ℝ ∞ G₁ V) (h₂ : ContDiffOn ℝ ∞ G₂ V)
    (heq : EqOn G₁ G₂ (centeredBox d a)) (i : Fin d) :
    EqOn (pd i G₁) (pd i G₂) (centeredBox d a) := by
  intro u hu
  have hui : u i ∈ Icc (-a) a := abs_le.1 (hu i)
  have hline : EqOn (line G₁ i u) (line G₂ i u) (Icc (-a) a) := by
    intro t ht
    refine heq fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact abs_le.2 ht
    · rw [Function.update_of_ne hj]
      exact hu j
  have hdiff : ∀ G : (Fin d → ℝ) → ℝ, ContDiffOn ℝ ∞ G V →
      DifferentiableAt ℝ (line G i u) (u i) := by
    intro G hG
    have hGu : DifferentiableAt ℝ G (Function.update u i (u i)) := by
      rw [Function.update_eq_self]
      exact (hG.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hBV hu))
    exact (hGu.hasFDerivAt.comp_hasDerivAt (u i) (hasDerivAt_update u i (u i))).differentiableAt
  have huniq : UniqueDiffWithinAt ℝ (Icc (-a) a) (u i) := uniqueDiffOn_Icc (by linarith) _ hui
  change deriv (line G₁ i u) (u i) = deriv (line G₂ i u) (u i)
  rw [← (hdiff G₁ h₁).hasDerivAt.hasDerivWithinAt.derivWithin huniq,
    ← (hdiff G₂ h₂).hasDerivAt.hasDerivWithinAt.derivWithin huniq]
  exact derivWithin_congr hline (hline hui)

theorem pdPow_eqOn_centeredBox (hV : IsOpen V) {a : ℝ} (ha : 0 < a) (hBV : centeredBox d a ⊆ V)
    {G₁ G₂ : (Fin d → ℝ) → ℝ} (h₁ : ContDiffOn ℝ ∞ G₁ V) (h₂ : ContDiffOn ℝ ∞ G₂ V)
    (heq : EqOn G₁ G₂ (centeredBox d a)) (i : Fin d) (q : ℕ) :
    EqOn (pdPow i q G₁) (pdPow i q G₂) (centeredBox d a) := by
  induction q generalizing G₁ G₂ with
  | zero => exact heq
  | succ q ih =>
    rw [pdPow_succ, pdPow_succ]
    exact ih (contDiffOn_pd hV h₁ i) (contDiffOn_pd hV h₂ i)
      (pd_eqOn_centeredBox hV ha hBV h₁ h₂ heq i)

/-- ★ **Jets on a closed box from an open neighbourhood**: all mixed coordinate derivatives of two
functions smooth on an open `V ⊇ [−a,a]^d` and equal on the box agree on the box. -/
theorem pdMulti_eqOn_centeredBox (hV : IsOpen V) {a : ℝ} (ha : 0 < a) (hBV : centeredBox d a ⊆ V)
    {G₁ G₂ : (Fin d → ℝ) → ℝ} (h₁ : ContDiffOn ℝ ∞ G₁ V) (h₂ : ContDiffOn ℝ ∞ G₂ V)
    (heq : EqOn G₁ G₂ (centeredBox d a)) (m : Fin d → ℕ) (l : List (Fin d)) :
    EqOn (pdMulti m l G₁) (pdMulti m l G₂) (centeredBox d a) := by
  induction l generalizing G₁ G₂ with
  | nil => exact heq
  | cons i l ih =>
    exact pdPow_eqOn_centeredBox hV ha hBV (contDiffOn_pdMulti hV h₁ m l)
      (contDiffOn_pdMulti hV h₂ m l) (ih h₁ h₂ heq) i (m i)

/-! ### The Leibniz rule for the coordinate derivatives -/

theorem pd_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin d → ℝ) → ℝ}
    (hF : ∀ j ∈ s, ContDiff ℝ ∞ (F j)) (i : Fin d) :
    pd i (fun v => ∑ j ∈ s, F j v) = fun v => ∑ j ∈ s, pd i (F j) v := by
  funext v
  have hline : line (fun v => ∑ j ∈ s, F j v) i v = ∑ j ∈ s, line (F j) i v := by
    funext t
    simp only [line, Finset.sum_apply]
  change deriv (line (fun v => ∑ j ∈ s, F j v) i v) (v i) = _
  rw [hline, deriv_sum fun j hj =>
    ((contDiff_line (hF j hj) i v).differentiable (by simp)).differentiableAt]
  rfl

theorem pdPow_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin d → ℝ) → ℝ}
    (hF : ∀ j ∈ s, ContDiff ℝ ∞ (F j)) (i : Fin d) (q : ℕ) :
    pdPow i q (fun v => ∑ j ∈ s, F j v) = fun v => ∑ j ∈ s, pdPow i q (F j) v := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [pdPow_succ', ih, pd_sum s (fun j hj => contDiff_pdPow (hF j hj) i q) i]
    funext v
    simp only [pdPow_succ']

/-- The one-coordinate Leibniz rule. -/
theorem pdPow_mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f)
    (i : Fin d) (q : ℕ) :
    pdPow i q (fun v => D v * f v) = fun v => ∑ r ∈ Finset.range (q + 1),
      ((q.choose r : ℕ) : ℝ) * pdPow i r D v * pdPow i (q - r) f v := by
  funext v
  have hl : line (fun v => D v * f v) i v = line D i v * line f i v := by
    funext t
    rfl
  have hcast : ∀ G : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G → ContDiffAt ℝ q (line G i v) (v i) :=
    fun G hG => (contDiff_line hG i v).contDiffAt.of_le (by exact_mod_cast le_top)
  have h := iteratedDeriv_mul (hcast D hD) (hcast f hf)
  rw [← hl, iteratedDeriv_line, line_apply_self] at h
  rw [h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_line, iteratedDeriv_line, line_apply_self, line_apply_self]

/-- The Leibniz coefficients `∏_{i∈l} C(α_i, β_i)`. -/
def leibC (α : Fin d → ℕ) : List (Fin d) → (Fin d → ℕ) → ℝ
  | [], _ => 1
  | i :: l, β => ((α i).choose (β i) : ℝ) * leibC α l β

theorem leibC_update_of_not_mem (α : Fin d → ℕ) {i : Fin d} {l : List (Fin d)} (hi : i ∉ l)
    (β : Fin d → ℕ) (n : ℕ) : leibC α l (Function.update β i n) = leibC α l β := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hji : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem j h)
    simp only [leibC, Function.update_of_ne hji, ih hil]

/-- ★ **The Leibniz rule** for iterated coordinate derivatives over distinct coordinates:
`∂^α (D f) = ∑_{β ≤ α} (∏ᵢ C(αᵢ, βᵢ)) ∂^β D · ∂^{α−β} f`. -/
theorem pdMulti_mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f)
    (α : Fin d → ℕ) {l : List (Fin d)} (hl : l.Nodup) :
    pdMulti α l (fun v => D v * f v) = fun v => ∑ β ∈ idxL (fun i => α i + 1) l,
      leibC α l β * (pdMulti β l D v * pdMulti (α - β) l f v) := by
  induction l with
  | nil =>
    funext v
    rw [idxL_nil, Finset.sum_singleton]
    simp [pdMulti_nil, leibC]
  | cons i l ih =>
    have hil : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    rw [pdMulti_cons, ih hl', pdPow_sum _ (F := fun β v =>
      leibC α l β * (pdMulti β l D v * pdMulti (α - β) l f v)) fun β _ =>
        contDiff_const.mul ((contDiff_pdMulti hD β l).mul (contDiff_pdMulti hf (α - β) l))]
    funext v
    rw [sum_idxL_cons (fun i => α i + 1) hil, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [pdPow_const_mul, pdPow_mul (contDiff_pdMulti hD β l) (contDiff_pdMulti hf (α - β) l)]
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hD' : pdPow i r (pdMulti β l D) v = pdMulti (Function.update β i r) (i :: l) D v := by
      rw [pdMulti_cons, Function.update_self, pdMulti_update_of_not_mem hil]
    have hf' : pdPow i (α i - r) (pdMulti (α - β) l f) v =
        pdMulti (α - Function.update β i r) (i :: l) f v := by
      rw [pdMulti_cons, Pi.sub_apply, Function.update_self,
        pdMulti_congr (m := α - Function.update β i r) (m' := α - β) (l := l) (fun j hj => by
          have hji : j ≠ i := fun h => hil (h ▸ hj)
          simp only [Pi.sub_apply, Function.update_of_ne hji]) f]
    rw [hD', hf']
    simp only [leibC, Function.update_self, leibC_update_of_not_mem α hil]
    ring

/-- Multiplication by a fixed smooth function preserves equality of finite jets. -/
theorem EqJetsOn.mul_left {P : Fin d → ℕ} {D f g : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {W : Set (Fin d → ℝ)} (h : EqJetsOn P f g W) :
    EqJetsOn P (fun v => D v * f v) (fun v => D v * g v) W := by
  intro α hα v hv
  simp only [pdMulti_mul hD hf α (List.nodup_finRange d),
    pdMulti_mul hD hg α (List.nodup_finRange d)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [h (α - β) (fun i => (Nat.sub_le _ _).trans (hα i)) v hv]

/-- ★ **The extension step**: jets on a closed box of `G = ρ · f` (`ρ` smooth, `f` smooth on an
open neighbourhood `V` of the box) are determined by the jets of `f`. -/
theorem EqJetsOn.of_mul_eqOn_centeredBox (hV : IsOpen V) {a : ℝ} (ha : 0 < a)
    (hBV : centeredBox d a ⊆ V) {G₁ G₂ ρ f₁ f₂ : (Fin d → ℝ) → ℝ} (hG₁ : ContDiff ℝ ∞ G₁)
    (hG₂ : ContDiff ℝ ∞ G₂) (hρ : ContDiff ℝ ∞ ρ) (hf₁ : ContDiffOn ℝ ∞ f₁ V)
    (hf₂ : ContDiffOn ℝ ∞ f₂ V) (heq₁ : ∀ u ∈ centeredBox d a, G₁ u = ρ u * f₁ u)
    (heq₂ : ∀ u ∈ centeredBox d a, G₂ u = ρ u * f₂ u) {W : Set (Fin d → ℝ)}
    (hW : W ⊆ centeredBox d a) {P : Fin d → ℕ} (h : EqJetsOn P f₁ f₂ W) :
    EqJetsOn P G₁ G₂ W := by
  have hC : IsClosed (centeredBox d a) := (isCompact_centeredBox d a).isClosed
  obtain ⟨O₁, hO₁, hO₁eq, -⟩ := exists_contDiff_eqOn_of_contDiffOn hV hC hBV hf₁
  obtain ⟨O₂, hO₂, hO₂eq, -⟩ := exists_contDiff_eqOn_of_contDiffOn hV hC hBV hf₂
  have hO : EqJetsOn P O₁ O₂ W := by
    intro α hα u hu
    rw [pdMulti_eqOn_centeredBox hV ha hBV hO₁.contDiffOn hf₁ hO₁eq α _ (hW hu),
      pdMulti_eqOn_centeredBox hV ha hBV hO₂.contDiffOn hf₂ hO₂eq α _ (hW hu)]
    exact h α hα u hu
  have hmul := hO.mul_left hρ hO₁ hO₂
  have e₁ : EqOn G₁ (fun u => ρ u * O₁ u) (centeredBox d a) := fun u hu => by
    change G₁ u = ρ u * O₁ u
    rw [heq₁ u hu, hO₁eq hu]
  have e₂ : EqOn G₂ (fun u => ρ u * O₂ u) (centeredBox d a) := fun u hu => by
    change G₂ u = ρ u * O₂ u
    rw [heq₂ u hu, hO₂eq hu]
  intro α hα u hu
  rw [pdMulti_eqOn_centeredBox hV ha hBV hG₁.contDiffOn (hρ.mul hO₁).contDiffOn e₁ α _ (hW hu),
    pdMulti_eqOn_centeredBox hV ha hBV hG₂.contDiffOn (hρ.mul hO₂).contDiffOn e₂ α _ (hW hu)]
  exact hmul α hα u hu

/-! ### Jets through the affine chart-coordinate map -/

/-- `∂^m` over a nodup list containing the support of `m` is `∂^m` over all coordinates. -/
theorem pdMulti_eq_finRange_of_nodup {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {m : Fin d → ℕ}
    {l : List (Fin d)} (hl : l.Nodup) (hm : ∀ i, i ∉ l → m i = 0) :
    pdMulti m l G = pdMulti m (List.finRange d) G := by
  have hperm : l.Perm (lJ l.toFinset) := (List.perm_ext_iff_of_nodup hl (nodup_lJ _)).2 fun i => by
    rw [mem_lJ, List.mem_toFinset]
  rw [pdMulti_perm hG m hperm, ← pdMulti_perm hG _ (lJ_append_lK_perm l.toFinset), pdMulti_append,
    pdMulti_congr (m := m) (m' := 0) (l := lK l.toFinset)
      (fun i hi => hm i fun h => (mem_lK _).1 hi (List.mem_toFinset.2 h)) G, pdMulti_zero]

/-- ★ **Jets through the affine chart map**: equal jets of the pulled-back amplitudes on the walls
of the active box follow from equal jets of orders `≤ extendIdx e P` on the part of the closed
chart box with some `J`-coordinate zero. -/
theorem EqJetsOn.comp_affineMap {da : ℕ} {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) (sc : {i // ¬ inJ J i} → ℝ) {a : ℝ} (hsc : ∀ j, |sc j| ≤ a)
    {G₁ G₂ : (Fin d → ℝ) → ℝ} (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) {P : Fin da → ℕ}
    (h : EqJetsOn (extendIdx e P) G₁ G₂ (centeredBox d a ∩ {u | ∃ j ∈ J, u j = 0})) :
    EqJetsOn P (fun v => G₁ (affineMap e σ sc v)) (fun v => G₂ (affineMap e σ sc v))
      (walls da ∩ closedBox da a) := by
  intro α hα v hv
  simp only [pdMulti_finRange_comp_affineMap]
  congr 1
  have hnd : ((List.finRange da).map fun j => (e j).1).Nodup :=
    (List.nodup_finRange da).map fun j j' hjj' => e.injective (Subtype.val_injective hjj')
  have hsupp : ∀ i, i ∉ (List.finRange da).map (fun j => (e j).1) → extendIdx e α i = 0 := by
    intro i hi
    refine extendIdx_of_not_mem e α fun hiJ => hi ?_
    exact List.mem_map.2 ⟨e.symm ⟨i, hiJ⟩, List.mem_finRange _, by simp⟩
  rw [pdMulti_eq_finRange_of_nodup hG₁ hnd hsupp, pdMulti_eq_finRange_of_nodup hG₂ hnd hsupp]
  refine h _ (fun i => ?_) _ ⟨fun i => ?_, ?_⟩
  · unfold extendIdx
    split_ifs with hi
    · exact hα _
    · exact le_rfl
  · by_cases hi : i ∈ J
    · rw [affineMap_apply_of_mem e σ sc v hi, abs_mul, WaterFilling.abs_sgn, one_mul]
      have hvi := mem_closedBox.1 hv.2 (e.symm ⟨i, hi⟩)
      rw [abs_of_nonneg hvi.1]
      exact hvi.2
    · rw [affineMap_apply_of_not_mem e σ sc v hi]
      exact hsc _
  · obtain ⟨j, hj⟩ := hv.1
    exact ⟨(e j).1, (e j).2, by rw [affineMap_apply_face, hj, mul_zero]⟩

/-! ### The producer: jets of the observable on the active walls -/

namespace BridgeInputs

variable (X : BridgeInputs d)

/-- The active walls of chart `i`: the points of the closed chart box with some active coordinate
zero. -/
def activeWalls (i : X.T.ι) : Set (Fin d → ℝ) :=
  centeredBox d (X.T.a i) ∩ {u | ∃ j, 0 < X.T.k i j ∧ u j = 0}

/-- The componentwise jet order of chart `i` at the exponent `μ`:
`2 k_{ij} L_i(μ) − h_{ij}`, `L_i(μ) = max(⌊μ⌋₊ + 1, ∑_{j active} h_{ij} + 1)`. -/
noncomputable def chartJetOrder (i : X.T.ι) (μ : ℝ) : Fin d → ℕ :=
  fun j => 2 * X.T.k i j * max (⌊μ⌋₊ + 1) (∑ j' ∈ X.act i, X.T.h i j' + 1) - X.T.h i j

/-- The total jet order of chart `i` at the exponent `μ`. -/
noncomputable def chartJetTotal (i : X.T.ι) (μ : ℝ) : ℕ := ∑ j, X.chartJetOrder i μ j

theorem extendIdx_depthOf_le (p : X.PIdx) (μ : ℝ) (j : Fin d) :
    extendIdx (X.eqv p) (depthOf (X.hA p) (X.kA p) (cutoffOf (X.hA p) μ)) j ≤
      X.chartJetOrder p.1 μ j := by
  have hsum : ∑ j', X.hA p j' = ∑ j ∈ X.act p.1, X.T.h p.1 j := by
    rw [Finset.sum_subtype (X.act p.1) (p := inJ (X.act p.1)) (fun _ => Iff.rfl) (X.T.h p.1)]
    exact Fintype.sum_equiv (X.eqv p) _ _ fun _ => rfl
  unfold extendIdx
  split_ifs with hj
  · unfold depthOf cutoffOf L₀ chartJetOrder
    rw [hsum]
    have hk : X.kA p ((X.eqv p).symm ⟨j, hj⟩) = X.T.k p.1 j := by
      unfold kA
      rw [Equiv.apply_symm_apply]
    have hh : X.hA p ((X.eqv p).symm ⟨j, hj⟩) = X.T.h p.1 j := by
      unfold hA
      rw [Equiv.apply_symm_apply]
    rw [hk, hh]
  · exact Nat.zero_le _

/-- The bridge inputs with the observable replaced (same phase, prior and transport). -/
def withObs (obs' : (Fin d → ℝ) → ℝ) (hobs' : ContDiff ℝ ∞ obs') : BridgeInputs d :=
  { X with obs := obs', obs_smooth := hobs' }

/-- ★★★ **Finite-jet determination of the intrinsic coefficients**: two observables whose chart
pull-backs `obs ∘ ψᵢ` have equal coordinate jets of componentwise orders `≤ chartJetOrder i μ` on
the active walls of every chart box give the same coefficient at `(μ, q)`. -/
theorem coeff_congr_of_jets {obs' : (Fin d → ℝ) → ℝ} (hobs' : ContDiff ℝ ∞ obs') {μ : ℝ}
    (hjet : ∀ i : X.T.ι, EqJetsOn (X.chartJetOrder i μ) (X.obs ∘ X.T.ψ i) (obs' ∘ X.T.ψ i)
      (X.activeWalls i)) (q : ℕ) :
    X.decomp.coeff μ q = (X.withObs obs' hobs').decomp.coeff μ q := by
  refine SmoothCoreDecomposition.coeff_congr X.decomp (X.withObs obs' hobs').decomp (fun I => rfl)
    (fun I => rfl) (fun I => rfl) (fun I => rfl) (fun I => rfl) (fun I s => ?_) q
  change EqJetsOn (depthOf (X.hA (X.en I)) (X.kA (X.en I)) (cutoffOf (X.hA (X.en I)) μ))
    (fun v => X.G (X.en I).1 (affineMap (X.eqv (X.en I)) (X.en I).2 (X.sc (X.en I) s) v))
    (fun v => (X.withObs obs' hobs').G (X.en I).1
      (affineMap (X.eqv (X.en I)) (X.en I).2 (X.sc (X.en I) s) v))
    (walls (X.da (X.en I)) ∩ closedBox (X.da (X.en I)) (X.T.a (X.en I).1))
  refine EqJetsOn.comp_affineMap (X.eqv (X.en I)) (X.en I).2 (X.sc (X.en I) s) (fun j => ?_)
    (X.contDiff_G _) ((X.withObs obs' hobs').contDiff_G _) ?_
  · change |WaterFilling.sgn (X.en I).2 j.1 * s.1 j| ≤ _
    rw [abs_mul, WaterFilling.abs_sgn, one_mul, abs_of_nonneg (Base_val_nonneg _ _ s j)]
    exact Base_val_le _ _ s j
  · refine EqJetsOn.of_mul_eqOn_centeredBox (X.T.V_open _) (X.T.a_pos _) (X.T.box_subset_V _)
      (X.contDiff_G _) ((X.withObs obs' hobs').contDiff_G _) (X.contDiff_ρf (X.en I).1)
      (X.obs_smooth.comp_contDiffOn (X.contDiffOn_ψ _)) (hobs'.comp_contDiffOn (X.contDiffOn_ψ _))
      (fun u hu => ?_) (fun u hu => ?_) (fun u hu => hu.1)
      (((hjet _).mono fun u hu => ⟨hu.1, ?_⟩).of_le (X.extendIdx_depthOf_le (X.en I) μ))
    · rw [X.G_eq _ hu, X.ρf_eq _ hu]
      rfl
    · rw [(X.withObs obs' hobs').G_eq _ hu, X.ρf_eq _ hu]
      rfl
    · obtain ⟨j, hj, hj0⟩ := hu.2
      exact ⟨j, X.mem_act.1 hj, hj0⟩

/-- ★★ The coefficient at `μ` depends on the observable only through the chart jets of TOTAL order
`≤ chartJetTotal i μ` on the active walls. -/
theorem coeff_congr_of_jets_total {obs' : (Fin d → ℝ) → ℝ} (hobs' : ContDiff ℝ ∞ obs') {μ : ℝ}
    (hjet : ∀ i : X.T.ι, ∀ γ : Fin d → ℕ, ∑ j, γ j ≤ X.chartJetTotal i μ →
      ∀ u ∈ X.activeWalls i, pdMulti γ (List.finRange d) (X.obs ∘ X.T.ψ i) u =
        pdMulti γ (List.finRange d) (obs' ∘ X.T.ψ i) u) (q : ℕ) :
    X.decomp.coeff μ q = (X.withObs obs' hobs').decomp.coeff μ q :=
  X.coeff_congr_of_jets hobs' (fun i => EqJetsOn.of_total (hjet i)) q

end BridgeInputs

end SmoothEngine

end Grammar
