/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaPolar
import Grammar.SmoothResonantSupport
import Grammar.SmoothJetDetermination
import Grammar.SmoothStratumJetDependence

/-!
# Reality, support and jet dependence of the chart polar coefficients (unit 6)

Three structural facts about the polar coefficients `chartPolarCoeff p F h k μ q` of unit 5.

* **Reality.**  The chart zeta functional and the regular factors commute with complex
  conjugation (`ConjSymm`), hence so do the holomorphic face factors and all their derivatives;
  at a real point the iterated derivatives are real, so every polar coefficient is a real number
  (`chartPolarReal`, `ofReal_chartPolarReal`).
* **Support.**  A coordinate is *resonant at `μ`* (depth `p`) when `mᵢ + hᵢ + 1 = 2kᵢ μ` for some
  `mᵢ < pᵢ`; the `r`-th resonant stratum `resStratum p h k μ r` is the part of the closed box
  where at least `r` resonant coordinates vanish.  If all jets of `F` vanish on
  `resStratum p h k μ (q + 1)` (in particular if `F` vanishes on a neighbourhood of it) then the
  `q`-th polar coefficient vanishes: `A_{μ,q+1}` is supported on the codimension-`(q+1)` resonant
  stratum.
* **Jet congruence.**  Two amplitudes with the same rectangular `p`-jets on
  `resStratum p h k μ (q + 1)` have the same `q`-th polar coefficient; in particular the polar
  coefficient depends on `F` only through its `p`-jet along the resonant stratum.

The face-level input is the face-local jet congruence `faceAmp_congr_closedFaceBox` (the
analogue of `faceAmp_congr` on one closed face box) and the flat-amplitude vanishing
`faceAmp_eq_zero_of_jets_zero`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics ComplexConjugate
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Functions commuting with complex conjugation -/

section Conj

/-- A function `ℂ → ℂ` commuting with complex conjugation. -/
def ConjSymm (f : ℂ → ℂ) : Prop := ∀ z, f (conj z) = conj (f z)

theorem ConjSymm.comp_eq {f : ℂ → ℂ} (hf : ConjSymm f) : conj ∘ f ∘ conj = f := by
  funext w; simp only [Function.comp, hf w, Complex.conj_conj]

theorem ConjSymm.deriv {f : ℂ → ℂ} (hf : ConjSymm f) : ConjSymm (deriv f) := by
  intro z
  have := congrFun (deriv_conj_conj (f := f)) (conj z)
  rw [hf.comp_eq] at this
  simpa [Function.comp] using this

theorem ConjSymm.iteratedDeriv_conjSymm {f : ℂ → ℂ} (hf : ConjSymm f) (n : ℕ) :
    ConjSymm (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- At a real point the iterated derivatives of a conjugation-symmetric function are real. -/
theorem ConjSymm.iteratedDeriv_ofReal {f : ℂ → ℂ} (hf : ConjSymm f) (n : ℕ) (x : ℝ) :
    ((iteratedDeriv n f x).re : ℂ) = iteratedDeriv n f x := by
  rw [← Complex.conj_eq_iff_re]
  have := hf.iteratedDeriv_conjSymm n (x : ℂ)
  rw [Complex.conj_ofReal] at this
  exact this.symm

theorem ConjSymm.mul {f g : ℂ → ℂ} (hf : ConjSymm f) (hg : ConjSymm g) :
    ConjSymm fun z => f z * g z := fun z => by simp [hf z, hg z]

theorem ConjSymm.prod {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ t, ConjSymm (f i)) : ConjSymm fun z => ∏ i ∈ t, f i z := fun z => by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi => hf i hi z

end Conj

/-! ### Reality of the polar coefficients -/

section Reality

variable {ι : Type*} [Fintype ι]

theorem cpowWeight_conj (h k : ι → ℕ) (s : ℂ) (u : ι → ℝ) :
    cpowWeight h k (conj s) u = conj (cpowWeight h k s u) := by
  unfold cpowWeight
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofNat]

/-- The chart zeta functional commutes with conjugation. -/
theorem chartZeta_conj (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (s : ℂ) :
    chartZeta G h k (conj s) = conj (chartZeta G h k s) := by
  unfold chartZeta
  have : ∀ u, (G u : ℂ) * cpowWeight h k (conj s) u = conj ((G u : ℂ) * cpowWeight h k s u) := by
    intro u
    rw [cpowWeight_conj, map_mul, Complex.conj_ofReal]
  simp_rw [this]
  exact integral_conj

theorem conjSymm_chartZeta (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) : ConjSymm (chartZeta G h k) :=
  fun s => chartZeta_conj G h k s

variable {d : ℕ}

theorem conjSymm_regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ConjSymm (regularFactor h k J m μ) := by
  unfold regularFactor
  refine ConjSymm.prod _ fun i _ z => ?_
  simp only [map_div₀, map_one, map_add, map_sub, map_mul, Complex.conj_natCast,
    Complex.conj_ofNat]

theorem conjSymm_faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) : ConjSymm (faceHolo p F h k J m μ) :=
  (conjSymm_regularFactor h k J m μ).mul (conjSymm_chartZeta _ _ _)

/-- The polar coefficients as real numbers. -/
noncomputable def chartPolarReal (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  (chartPolarCoeff p F h k μ q).re

/-- ★ **Reality**: every chart polar coefficient at a real point is real. -/
theorem ofReal_chartPolarReal (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ)
    (q : ℕ) : ((chartPolarReal p F h k μ q : ℝ) : ℂ) = chartPolarCoeff p F h k μ q := by
  unfold chartPolarReal chartPolarCoeff
  rw [← Complex.conj_eq_iff_re, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hres : conj (resConst h k x.1 x.2 μ) = resConst h k x.1 x.2 μ := by
    unfold resConst
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_inv₀, map_mul, Complex.conj_natCast, Complex.conj_ofNat]
  have hder := (conjSymm_faceHolo p F h k x.1 x.2 μ).iteratedDeriv_conjSymm
    (poleOrder h k x.1 x.2 μ - 1 - q) (μ : ℂ)
  rw [Complex.conj_ofReal] at hder
  simp only [map_mul, map_div₀, map_pow, map_neg, map_one, Complex.conj_ofReal,
    Complex.conj_natCast, hres, ← hder]

theorem chartPolarCoeff_im (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ)
    (q : ℕ) : (chartPolarCoeff p F h k μ q).im = 0 := by
  rw [← ofReal_chartPolarReal, Complex.ofReal_im]

end Reality

/-! ### Resonant coordinates and the resonant strata -/

section Support

variable {d : ℕ}

/-- The coordinates resonant at `μ` at depth `p`: `mᵢ + hᵢ + 1 = 2kᵢ μ` for some `mᵢ < pᵢ`. -/
noncomputable def resCoord (p h k : Fin d → ℕ) (μ : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i =>
    ∃ m ∈ Finset.range (p i), ((m + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

theorem faceResSet_subset_resCoord (p h k : Fin d → ℕ) {J : Finset (Fin d)} {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) :
    faceResSet h k J m μ ⊆ resCoord p h k μ := by
  intro i hi
  obtain ⟨hiJ, hres⟩ := mem_faceResSet.1 hi
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    m i, Finset.mem_range.2 (lt_of_mem_idxL p hm hiJ), hres⟩

/-- The `r`-th resonant stratum of the closed unit box: at least `r` resonant coordinates
vanish. -/
def resStratum (p h k : Fin d → ℕ) (μ : ℝ) (r : ℕ) : Set (Fin d → ℝ) :=
  {v ∈ closedBox d 1 | r ≤ ((resCoord p h k μ).filter fun i => v i = 0).card}

theorem resStratum_antitone (p h k : Fin d → ℕ) (μ : ℝ) {r r' : ℕ} (hr : r ≤ r') :
    resStratum p h k μ r' ⊆ resStratum p h k μ r := fun _ hv => ⟨hv.1, hr.trans hv.2⟩

/-- A closed face box of pole order `≥ r` lies in the `r`-th resonant stratum. -/
theorem closedFaceBox_subset_resStratum (p h k : Fin d → ℕ) {J : Finset (Fin d)}
    {m : Fin d → ℕ} (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) {r : ℕ}
    (hr : r ≤ poleOrder h k J m μ) :
    closedFaceBox d 1 J ⊆ resStratum p h k μ r := by
  intro v hv
  refine ⟨hv.1, hr.trans (Finset.card_le_card fun i hi => ?_)⟩
  exact Finset.mem_filter.2 ⟨faceResSet_subset_resCoord p h k hm μ hi,
    hv.2 i (faceResSet_subset h k J m μ hi)⟩

/-- The chart zeta functional of an amplitude vanishing on the open box is zero. -/
theorem chartZeta_eq_zero_of_forall {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℝ}
    (hG : ∀ w ∈ SmoothEngine.box ι 1, G w = 0) (h k : ι → ℕ) (s : ℂ) :
    chartZeta G h k s = 0 := by
  unfold chartZeta
  exact setIntegral_eq_zero_of_forall_eq_zero fun w hw => by rw [hG w hw]; simp

/-- Two amplitudes agreeing on the open box have the same chart zeta functional. -/
theorem chartZeta_congr {ι : Type*} [Fintype ι] {G G' : (ι → ℝ) → ℝ}
    (hG : ∀ w ∈ SmoothEngine.box ι 1, G w = G' w) (h k : ι → ℕ) (s : ℂ) :
    chartZeta G h k s = chartZeta G' h k s := by
  unfold chartZeta
  exact setIntegral_congr_fun (SmoothEngine.measurableSet_box (ι := ι) 1) fun w hw => by
    rw [hG w hw]

/-- ★ **Support of the polar coefficients**: if all jets of `F` vanish on the `(q+1)`-st resonant
stratum then the `q`-th polar coefficient vanishes. -/
theorem chartPolarCoeff_eq_zero_of_jetsZeroOn (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ)
    (hF0 : JetsZeroOn F (resStratum p h k μ (q + 1))) :
    chartPolarCoeff p F h k μ q = 0 := by
  unfold chartPolarCoeff
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hx, hq⟩ := Finset.mem_filter.1 hx
  have hm : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hamp : ∀ w ∈ SmoothEngine.box {i // ¬ inJ x.1 i} 1, SmoothEngine.faceAmp p x.1 F x.2 w = 0 :=
    faceAmp_eq_zero_of_jets_zero p x.1 hF x.2 one_pos fun v hv hJ α =>
      hF0 α v (closedFaceBox_subset_resStratum p h k hm μ hq ⟨hv, hJ⟩)
  have hzero : faceHolo p F h k x.1 x.2 μ = fun _ => 0 := by
    funext s
    unfold faceHolo
    rw [chartZeta_eq_zero_of_forall hamp, mul_zero]
  rw [hzero, iteratedDeriv_const]
  simp

/-- Support under vanishing on a neighbourhood: if `F = 0` on an open set containing the
`(q+1)`-st resonant stratum (intersected with the closed box) then the `q`-th coefficient is
zero. -/
theorem chartPolarCoeff_eq_zero_of_eqOn_zero (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ) {O : Set (Fin d → ℝ)}
    (hO : IsOpen O) (hsub : resStratum p h k μ (q + 1) ⊆ O)
    (h0 : ∀ v ∈ O ∩ closedBox d 1, F v = 0) :
    chartPolarCoeff p F h k μ q = 0 :=
  chartPolarCoeff_eq_zero_of_jetsZeroOn p hF h k μ q fun α _ hv =>
    pdMulti_eq_zero_of_eqOn_inter_closedBox hF one_pos hO h0 ⟨hsub hv, hv.1⟩ α

/-! ### Jet congruence -/

/-- Face-local jet congruence: equal rectangular `p`-jets on the closed face box of `J` give equal
face amplitudes on the open complementary box. -/
theorem faceAmp_congr_closedFaceBox (p : Fin d → ℕ) {F G : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (J : Finset (Fin d))
    (hjet : EqJetsOn p F G (closedFaceBox d 1 J)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ SmoothEngine.box {i // ¬ inJ J i} 1) :
    SmoothEngine.faceAmp p J F m w = SmoothEngine.faceAmp p J G m w := by
  unfold SmoothEngine.faceAmp
  refine remList_congr p (closedFaceBox_update one_pos.le J) (nodup_lK J)
    (contDiff_pdMulti hF m _) (contDiff_pdMulti hG m _) ?_ _
    (glue_zero_mem_closedFaceBox J one_pos hw)
  intro α hα v hv
  rw [pdMulti_lK_pdMulti_lJ_eq hF, pdMulti_lK_pdMulti_lJ_eq hG]
  refine hjet _ (fun i => ?_) v hv
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    exact (lt_of_mem_idxL p hm hi).le
  · rw [if_neg hi]
    exact hα i ((mem_lK J).2 hi)

/-- ★ **Jet congruence**: amplitudes with equal rectangular `p`-jets on the `(q+1)`-st resonant
stratum have equal `q`-th polar coefficients. -/
theorem chartPolarCoeff_congr (p : Fin d → ℕ) {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ)
    (hjet : EqJetsOn p F G (resStratum p h k μ (q + 1))) :
    chartPolarCoeff p F h k μ q = chartPolarCoeff p G h k μ q := by
  unfold chartPolarCoeff
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hx, hq⟩ := Finset.mem_filter.1 hx
  have hm : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hjet' : EqJetsOn p F G (closedFaceBox d 1 x.1) := fun α hα v hv =>
    hjet α hα v (closedFaceBox_subset_resStratum p h k hm μ hq hv)
  have hholo : faceHolo p F h k x.1 x.2 μ = faceHolo p G h k x.1 x.2 μ := by
    funext s
    unfold faceHolo
    rw [chartZeta_congr fun w hw => faceAmp_congr_closedFaceBox p hF hG x.1 hjet' hm hw]
  rw [hholo]

/-- Jet congruence under agreement on a neighbourhood of the resonant stratum. -/
theorem chartPolarCoeff_congr_of_eqOn (p : Fin d → ℕ) {F G : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ)
    {O : Set (Fin d → ℝ)} (hO : IsOpen O) (hsub : resStratum p h k μ (q + 1) ⊆ O)
    (heq : ∀ v ∈ O ∩ closedBox d 1, F v = G v) :
    chartPolarCoeff p F h k μ q = chartPolarCoeff p G h k μ q :=
  chartPolarCoeff_congr p hF hG h k μ q fun α _ _ hv =>
    pdMulti_eq_of_eqOn_inter_closedBox hF hG one_pos hO heq ⟨hsub hv, hv.1⟩ α

end Support

end Grammar
