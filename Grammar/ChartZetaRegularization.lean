/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaFace
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The meromorphic continuation of the chart zeta functional (polar-distribution programme, unit 4)

Consult #167 (A1; `tide-log/plan_polar_distribution.md`). The face sum of unit 3,
  `chartZetaAtDepth p F h k s = Σ_{(J,m)∈faceIndex p} faceW J m · innerFactor h k J m s ·
     chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s`,
with `innerFactor = ∏_{i∈J} 1/(mᵢ+hᵢ+1−2kᵢs)`, is defined for every `s`. It equals
`chartZeta F h k` on the strip (`chartZetaAtDepth_eq_chartZeta`), and for positive depths it is
holomorphic on the flat strip `2kᵢ Re s < pᵢ+hᵢ+1` away from the finitely many candidate poles
`(mᵢ+hᵢ+1)/2kᵢ` (`PoleAt`, `finite_poleSet`; ★ `differentiableOn_chartZetaAtDepth`, by the
flat bound `faceAmp_bound` and the flat-strip holomorphy of unit 2). Two admissible depths give
the same function on their common domain (★★ `chartZetaAtDepth_eq_of_depths`): the identity
theorem on the open strip `−1 < Re s < L` minus the poles, whose preconnectedness is transported
from the plane minus a countable set (`Set.Countable.isPathConnected_compl_of_one_lt_rank`)
through an `arctan` homeomorphism (`isPreconnected_strip_diff_finite`). This is the meromorphic
continuation of `chartZeta F h k` to `Re s < min (pᵢ+hᵢ+1)/2kᵢ`, with poles only at the
candidate exponents. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ContDiff

namespace Grammar

open SmoothEngine

/-! ### A strip minus finitely many points is preconnected -/

section Strip

/-- The `arctan` homeomorphism of the plane onto the strip `c₁ < Re < c₂`. -/
noncomputable def stripMap (c₁ c₂ : ℝ) (z : ℂ) : ℂ :=
  (((c₁ + c₂) / 2 + (c₂ - c₁) / Real.pi * Real.arctan z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I

theorem stripMap_re (c₁ c₂ : ℝ) (z : ℂ) :
    (stripMap c₁ c₂ z).re = (c₁ + c₂) / 2 + (c₂ - c₁) / Real.pi * Real.arctan z.re := by
  unfold stripMap
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem stripMap_im (c₁ c₂ : ℝ) (z : ℂ) : (stripMap c₁ c₂ z).im = z.im := by
  unfold stripMap
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

theorem continuous_stripMap (c₁ c₂ : ℝ) : Continuous (stripMap c₁ c₂) := by
  unfold stripMap
  exact (Complex.continuous_ofReal.comp (continuous_const.add
    (continuous_const.mul (Real.continuous_arctan.comp Complex.continuous_re)))).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

theorem stripMap_injective {c₁ c₂ : ℝ} (hc : c₁ < c₂) : Function.Injective (stripMap c₁ c₂) := by
  intro z w hzw
  have hre := congrArg Complex.re hzw
  have him := congrArg Complex.im hzw
  rw [stripMap_re, stripMap_re] at hre
  rw [stripMap_im, stripMap_im] at him
  have hb : (c₂ - c₁) / Real.pi ≠ 0 := by
    have := Real.pi_pos
    exact div_ne_zero (by linarith) this.ne'
  have : Real.arctan z.re = Real.arctan w.re := by
    have h1 : (c₂ - c₁) / Real.pi * Real.arctan z.re = (c₂ - c₁) / Real.pi * Real.arctan w.re := by
      linarith
    exact mul_left_cancel₀ hb h1
  exact Complex.ext (Real.arctan_injective this) him

theorem stripMap_mem {c₁ c₂ : ℝ} (hc : c₁ < c₂) (z : ℂ) :
    c₁ < (stripMap c₁ c₂ z).re ∧ (stripMap c₁ c₂ z).re < c₂ := by
  rw [stripMap_re]
  have hpi := Real.pi_pos
  have h1 := Real.neg_pi_div_two_lt_arctan z.re
  have h2 := Real.arctan_lt_pi_div_two z.re
  have hb : 0 < (c₂ - c₁) / Real.pi := div_pos (by linarith) hpi
  constructor
  · have : -(c₂ - c₁) / 2 < (c₂ - c₁) / Real.pi * Real.arctan z.re := by
      have := mul_lt_mul_of_pos_left h1 hb
      rw [show (c₂ - c₁) / Real.pi * (-(Real.pi / 2)) = -(c₂ - c₁) / 2 by
        field_simp] at this
      exact this
    linarith
  · have : (c₂ - c₁) / Real.pi * Real.arctan z.re < (c₂ - c₁) / 2 := by
      have := mul_lt_mul_of_pos_left h2 hb
      rw [show (c₂ - c₁) / Real.pi * (Real.pi / 2) = (c₂ - c₁) / 2 by
        field_simp] at this
      exact this
    linarith

theorem stripMap_surj {c₁ c₂ : ℝ} (_hc : c₁ < c₂) {s : ℂ} (hs : c₁ < s.re ∧ s.re < c₂) :
    ∃ z, stripMap c₁ c₂ z = s := by
  have hpi := Real.pi_pos
  have hb : 0 < (c₂ - c₁) / Real.pi := div_pos (by linarith) hpi
  set t := (s.re - (c₁ + c₂) / 2) / ((c₂ - c₁) / Real.pi) with ht
  have ht1 : -(Real.pi / 2) < t := by
    rw [ht, lt_div_iff₀ hb]
    rw [show -(Real.pi / 2) * ((c₂ - c₁) / Real.pi) = -(c₂ - c₁) / 2 by field_simp]
    linarith [hs.1]
  have ht2 : t < Real.pi / 2 := by
    rw [ht, div_lt_iff₀ hb]
    rw [show Real.pi / 2 * ((c₂ - c₁) / Real.pi) = (c₂ - c₁) / 2 by field_simp]
    linarith [hs.2]
  have hne : c₂ - c₁ ≠ 0 := by linarith
  refine ⟨⟨Real.tan t, s.im⟩, ?_⟩
  apply Complex.ext
  · rw [stripMap_re]
    simp only
    rw [Real.arctan_tan ht1 ht2, ht]
    field_simp
    ring
  · rw [stripMap_im]

/-- The image of the complement of a set under the strip map is the strip minus the image. -/
theorem stripMap_image_compl {c₁ c₂ : ℝ} (hc : c₁ < c₂) (P : Set ℂ) :
    stripMap c₁ c₂ '' (stripMap c₁ c₂ ⁻¹' P)ᶜ = {s : ℂ | c₁ < s.re ∧ s.re < c₂} \ P := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨stripMap_mem hc z, hz⟩
  · rintro ⟨hs, hsP⟩
    obtain ⟨z, rfl⟩ := stripMap_surj hc hs
    exact ⟨z, hsP, rfl⟩

/-- ★ **A strip minus a finite set is preconnected.** -/
theorem isPreconnected_strip_diff_finite {c₁ c₂ : ℝ} (hc : c₁ < c₂) {P : Set ℂ}
    (hP : P.Finite) : IsPreconnected ({s : ℂ | c₁ < s.re ∧ s.re < c₂} \ P) := by
  rw [← stripMap_image_compl hc P]
  have hfin : (stripMap c₁ c₂ ⁻¹' P).Finite :=
    hP.preimage (stripMap_injective hc).injOn
  have hpc : IsPathConnected (stripMap c₁ c₂ ⁻¹' P)ᶜ :=
    hfin.countable.isPathConnected_compl_of_one_lt_rank (by
      simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
  exact (hpc.image (continuous_stripMap c₁ c₂)).isConnected.isPreconnected

end Strip

/-! ### The face sum for all `s`, its poles and its holomorphy -/

section Continuation

variable {d : ℕ}

/-- The inner rational factor `∏_{i∈J} 1/(mᵢ + hᵢ + 1 − 2kᵢ s)`. -/
noncomputable def innerFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (s : ℂ) :
    ℂ :=
  ∏ i : {i // inJ J i}, 1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)

/-- The face sum at depth `p`, defined for every `s`. -/
noncomputable def chartZetaAtDepth (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (s : ℂ) : ℂ :=
  ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
    innerFactor h k x.1 x.2 s *
    chartZeta (SmoothEngine.faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
      (fun i => k i) s

/-- On the strip the face sum is the chart zeta functional (unit 3). -/
theorem chartZetaAtDepth_eq_chartZeta (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ} (hs : ZetaStrip h k s) :
    chartZetaAtDepth p F h k s = chartZeta F h k s := by
  rw [chartZeta_eq_sum_faces p hF h k hs]
  rfl

/-- `s` is a candidate pole at depth `p`: some inner denominator vanishes. -/
def PoleAt (p h k : Fin d → ℕ) (s : ℂ) : Prop :=
  ∃ x ∈ SmoothEngine.faceIndex p, ∃ i ∈ x.1,
    ((x.2 i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 = 0

/-- The candidate poles are the finitely many points `(mᵢ + hᵢ + 1)/(2kᵢ)`. -/
theorem finite_poleSet (p h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    {s : ℂ | PoleAt p h k s}.Finite := by
  refine Set.Finite.subset (((SmoothEngine.faceIndex p).sigma fun x => x.1).finite_toSet.image
    (fun y : (Σ _ : (Σ _ : Finset (Fin d), Fin d → ℕ), Fin d) =>
      (((y.1.2 y.2 + h y.2 : ℕ) : ℂ) + 1) / (2 * ((k y.2 : ℕ) : ℂ)))) ?_
  rintro s ⟨x, hx, i, hi, hden⟩
  refine ⟨⟨x, i⟩, Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨hx, hi⟩), ?_⟩
  have hk' : (2 * ((k i : ℕ) : ℂ)) ≠ 0 := by
    have := hk i
    exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  simp only
  rw [div_eq_iff hk']
  linear_combination hden

/-- Every candidate pole has positive real part. -/
theorem pos_re_of_poleAt {p h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {s : ℂ} (hs : PoleAt p h k s) :
    0 < s.re := by
  obtain ⟨x, _, i, _, hden⟩ := hs
  have hre : (((x.2 i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1).re =
      ((x.2 i + h i : ℕ) : ℝ) - 2 * (k i : ℝ) * s.re + 1 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.add_re]
  have := congrArg Complex.re hden
  rw [hre, Complex.zero_re] at this
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  have hm : (0 : ℝ) ≤ ((x.2 i + h i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A finite product of functions differentiable on `U` is differentiable on `U`. -/
theorem differentiableOn_finset_prod' {ι : Type*} (t : Finset ι) {U : Set ℂ} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ t, f i s) U := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const _
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite sum of functions differentiable on `U` is differentiable on `U`. -/
theorem differentiableOn_finset_sum' {ι : Type*} (t : Finset ι) {U : Set ℂ} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun s => ∑ i ∈ t, f i s) U := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact differentiableOn_const _
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_innerFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    {U : Set ℂ}
    (hU : ∀ s ∈ U, ∀ i ∈ J, ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0) :
    DifferentiableOn ℂ (innerFactor h k J m) U := by
  unfold innerFactor
  refine differentiableOn_finset_prod' _ fun i _ => ?_
  refine (differentiableOn_const _).div ?_ fun s hs => hU s hs i.1 i.2
  exact ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).add
    (differentiableOn_const _)

theorem flatStrip_subtype {p h k : Fin d → ℕ} (J : Finset (Fin d)) {s : ℂ}
    (hs : FlatStrip p h k s) :
    FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) s := fun i => hs i

/-- The flat face amplitude is `p`-flat on the complementary box. -/
theorem flatOn_faceAmp (p : Fin d → ℕ) (J : Finset (Fin d)) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hp0 : ∀ i, 0 < p i) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Grammar.FlatOn (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => p i) C := by
  obtain ⟨M, hM⟩ := exists_rect_bound hF p 1
  have hM' : ∀ m' : Fin d → ℕ, (∀ i, m' i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      |SmoothEngine.pdMulti m' (List.finRange d) F v| ≤ max M 0 :=
    fun m' hm' v hv => (hM m' hm' v hv).trans (le_max_left _ _)
  refine ⟨(∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * max M 0,
    mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (le_max_right _ _), fun w hw => ?_⟩
  exact faceAmp_bound p J hF one_pos hp0 hM' hm hw

/-- ★ **Holomorphy of the face sum** on the flat strip away from the candidate poles. -/
theorem differentiableOn_chartZetaAtDepth (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) :
    DifferentiableOn ℂ (chartZetaAtDepth p F h k)
      {s | FlatStrip p h k s ∧ ¬ PoleAt p h k s} := by
  unfold chartZetaAtDepth
  refine differentiableOn_finset_sum' _ fun x hx => ?_
  have hx' : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := by
    have := Finset.mem_sigma.1 hx
    exact this.2
  obtain ⟨C, hC, hflat⟩ := flatOn_faceAmp p x.1 hF hp0 hx'
  refine DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _) ?_) ?_
  · exact differentiableOn_innerFactor h k x.1 x.2 fun s hs i hi hden =>
      hs.2 ⟨x, hx, i, hi, hden⟩
  · exact (differentiableOn_chartZeta_flat (continuous_faceAmp p x.1 hF x.2).continuousOn hC
      hflat _ _).mono fun s hs => flatStrip_subtype x.1 hs.1

end Continuation

/-! ### Depth compatibility -/

section Compatibility

variable {d : ℕ} [Nonempty (Fin d)]

/-- The right edge of the flat strip: `min_i (pᵢ + hᵢ + 1)/(2kᵢ)`. -/
noncomputable def flatEdge (p h k : Fin d → ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => ((p i : ℝ) + h i + 1) / (2 * k i)

theorem flatStrip_iff_re_lt (p h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (s : ℂ) :
    FlatStrip p h k s ↔ s.re < flatEdge p h k := by
  unfold FlatStrip flatEdge
  rw [Finset.lt_inf'_iff]
  refine ⟨fun H i _ => ?_, fun H i => ?_⟩
  · have hk' : (0 : ℝ) < 2 * k i := by have := Nat.cast_pos (α := ℝ) |>.2 (hk i); positivity
    rw [lt_div_iff₀ hk']
    linarith [H i]
  · have hk' : (0 : ℝ) < 2 * k i := by have := Nat.cast_pos (α := ℝ) |>.2 (hk i); positivity
    have := H i (Finset.mem_univ i)
    rw [lt_div_iff₀ hk'] at this
    linarith

theorem flatEdge_pos (p h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) : 0 < flatEdge p h k := by
  unfold flatEdge
  rw [Finset.lt_inf'_iff]
  intro i _
  have hk' : (0 : ℝ) < 2 * k i := by have := Nat.cast_pos (α := ℝ) |>.2 (hk i); positivity
  positivity

omit [Nonempty (Fin d)] in
theorem zetaStrip_neg_half (h k : Fin d → ℕ) : ZetaStrip h k ((-1 / 2 : ℝ) : ℂ) := fun i => by
  simp only [Complex.ofReal_re]
  have : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ h i := Nat.cast_nonneg _
  nlinarith

/-- ★★ **Depth compatibility**: two positive depths give the same continuation on the common
flat strip away from either set of candidate poles. -/
theorem chartZetaAtDepth_eq_of_depths {p p' : Fin d → ℕ} {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hp0 : ∀ i, 0 < p i)
    (hp0' : ∀ i, 0 < p' i) {s : ℂ} (hs : FlatStrip p h k s) (hs' : FlatStrip p' h k s)
    (hpole : ¬ PoleAt p h k s) (hpole' : ¬ PoleAt p' h k s) (hre : -1 < s.re) :
    chartZetaAtDepth p F h k s = chartZetaAtDepth p' F h k s := by
  set L := min (flatEdge p h k) (flatEdge p' h k) with hL
  set P := {t : ℂ | PoleAt p h k t} ∪ {t : ℂ | PoleAt p' h k t} with hP
  set U := {t : ℂ | -1 < t.re ∧ t.re < L} \ P with hU
  have hPfin : P.Finite := (finite_poleSet p h k hk).union (finite_poleSet p' h k hk)
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re |>.inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin.isClosed
  have hUsub : ∀ t ∈ U, FlatStrip p h k t ∧ ¬ PoleAt p h k t := fun t ht =>
    ⟨(flatStrip_iff_re_lt p h k hk t).2 (lt_of_lt_of_le ht.1.2 (min_le_left _ _)),
      fun hp => ht.2 (Or.inl hp)⟩
  have hUsub' : ∀ t ∈ U, FlatStrip p' h k t ∧ ¬ PoleAt p' h k t := fun t ht =>
    ⟨(flatStrip_iff_re_lt p' h k hk t).2 (lt_of_lt_of_le ht.1.2 (min_le_right _ _)),
      fun hp => ht.2 (Or.inr hp)⟩
  have hf : AnalyticOnNhd ℂ (chartZetaAtDepth p F h k) U :=
    ((differentiableOn_chartZetaAtDepth p hF h k hp0).mono hUsub).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ (chartZetaAtDepth p' F h k) U :=
    ((differentiableOn_chartZetaAtDepth p' hF h k hp0').mono hUsub').analyticOnNhd hUopen
  have hLpos : 0 < L := lt_min (flatEdge_pos p h k hk) (flatEdge_pos p' h k hk)
  have hconn : IsPreconnected U := isPreconnected_strip_diff_finite (by linarith) hPfin
  have hz₀ : ((-1 / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨⟨by simp; norm_num, by simp; linarith⟩, ?_⟩
    rintro (hp | hp)
    · have := pos_re_of_poleAt hk hp; simp at this; linarith
    · have := pos_re_of_poleAt hk hp; simp at this; linarith
  have hfg : chartZetaAtDepth p F h k =ᶠ[𝓝 ((-1 / 2 : ℝ) : ℂ)] chartZetaAtDepth p' F h k := by
    filter_upwards [(ZetaStrip.isOpen h k).mem_nhds (zetaStrip_neg_half h k)] with t ht
    rw [chartZetaAtDepth_eq_chartZeta p hF h k ht, chartZetaAtDepth_eq_chartZeta p' hF h k ht]
  have hsU : s ∈ U := by
    refine ⟨⟨hre, lt_min ((flatStrip_iff_re_lt p h k hk s).1 hs)
      ((flatStrip_iff_re_lt p' h k hk s).1 hs')⟩, ?_⟩
    rintro (hp | hp)
    · exact hpole hp
    · exact hpole' hp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hz₀ hfg hsU

end Compatibility

end Grammar
