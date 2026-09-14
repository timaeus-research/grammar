/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral
import Grammar.SmoothFamilyIntegral
import Grammar.SmoothLogIntegrable
import Grammar.SmoothAmplitudeFamily

/-!
# A quantitative bound on the smooth coefficients (consult #123 unit C1a)

The canonical coefficients `smoothCoeff F h k β b μ q` of the smooth-amplitude integral
`∫_{(0,b]^d} F(v) v^h e^{−Nβ v^{2k}} dv` are finite sums, over the faces `(J, m)`, of fixed real
numbers (the face power–log coefficients `faceCoef`, binomial weights) times the face coefficient
integrals `∫_{(0,b]^K} G(w) w^h (w^{2k})^{−μ} S(w)^e dw`, whose outer amplitude
`G = faceAmp p J F m` is a coordinate Taylor remainder of `F`. The engine's convergence proof
(`integrable_faceCoeff`) already dominates every such integrand by
`M ∏ᵢ wᵢ^{pᵢ+hᵢ−2kᵢμ} |S(w)|^e` with `M` the rectangular mixed-derivative bound of `F`. Here we
make that domination QUANTITATIVE:

* `faceMajorant p h a b μ e = ∫_{(0,b]^ι} w^p w^h (w^a)^{−μ} |S(w)|^e dw` is the absolute majorant
  integral (finite under `aᵢ μ < pᵢ + hᵢ + 1`, nonnegative), and
  `|faceCoeffInt G h a b μ e| ≤ M · faceMajorant p h a b μ e` whenever `|G| ≤ M w^p` on the box
  (★ `abs_faceCoeffInt_le`);
* `coeffBoundConstant h k p β b μ q` is the explicit constant obtained by replacing, in the
  definition of `smoothCoeffAtDepth`, every face coefficient by its absolute value and every face
  coefficient integral by `(∏_{i∉J} 1/(pᵢ−1)!) · faceMajorant`; it depends only on
  `(h, k, p, β, b, μ, q)` and NOT on the amplitude, and
  ★★★ `abs_smoothCoeffAtDepth_le : |smoothCoeffAtDepth F h k p β b μ q| ≤ coeffBoundConstant … * M`
  for every smooth `F` with `RectBound F p b M`, under the convergence condition
  `2kᵢ μ < pᵢ + hᵢ + 1`;
* at the canonical depth `p = depthOf h k (cutoffOf h μ)` the convergence condition is automatic
  (`μ < cutoffOf h μ` and `pᵢ + hᵢ = 2kᵢ L`), giving ★★★ `abs_smoothCoeff_le`;
* for a `SmoothAmplitudeFamily` with a uniform rectangular bound and a constant phase unit,
  ★ `abs_familyCoeff_le_const_beta : |familyCoeff ν F h k (fun _ => β) b μ q| ≤ C · M · ν(S)`.

So the canonical coefficients are bounded LINEARLY in the derivative bound of the amplitude, with a
constant that is an explicit finite sum of absolutely convergent power–log integrals. This is the
quantitative input for continuity/stability statements about the coefficients in the amplitude
(e.g. a `C^p`-perturbation of the amplitude moves each coefficient by at most `C` times the size
of the perturbation, by linearity of `smoothCoeff` in `F`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### The absolute majorant of a face coefficient integral -/

section Majorant

variable {ι : Type*} [Fintype ι]

/-- The absolute majorant integral `∫_{(0,b]^ι} w^p w^h (w^a)^{−μ} |S(w)|^e dw`. -/
noncomputable def faceMajorant (p h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : ℝ :=
  ∫ w in box ι b, mono p w * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e

theorem faceMajorant_nonneg (p h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : 0 ≤ faceMajorant p h a b μ e :=
  setIntegral_nonneg (measurableSet_box b) fun w hw => by
    have hpos := pos_of_mem_box hw
    have := mono_pos p hpos
    have := mono_pos h hpos
    have := rpow_pos_of_pos (mono_pos a hpos) (-μ)
    positivity

/-- The majorant integrand converges under `aᵢ μ < pᵢ + hᵢ + 1`. -/
theorem integrableOn_faceMajorant {p h a : ι → ℕ} {b : ℝ} (hb : 0 < b) {μ : ℝ}
    (hμ : ∀ i, (a i : ℝ) * μ < p i + h i + 1) (e : ℕ) :
    IntegrableOn (fun w => mono p w * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) (box ι b) := by
  have hint := integrableOn_prod_rpow_mul_abs_log_pow (D := e)
    (c := fun i => (p i + h i : ℝ) - a i * μ) (fun i => by have := hμ i; linarith)
    (fun i => (a i : ℝ)) le_rfl hb.le
  refine hint.congr_fun (fun w hw => ?_) (measurableSet_box b)
  simp only [logSum]
  rw [mono_mul_mono_mul_rpow p h a μ (pos_of_mem_box hw)]

/-- ★ **The face coefficient integral is bounded by the majorant**: if `|G(w)| ≤ M w^p` on the
box, then `|∫ G w^h (w^a)^{−μ} S^e| ≤ M · faceMajorant p h a b μ e`. -/
theorem abs_faceCoeffInt_le {G : (ι → ℝ) → ℝ} {p h a : ι → ℕ} {b M : ℝ} (hb : 0 < b)
    (hG : AEStronglyMeasurable G (volume.restrict (box ι b)))
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) {μ : ℝ}
    (hμ : ∀ i, (a i : ℝ) * μ < p i + h i + 1) (e : ℕ) :
    |faceCoeffInt G h a b μ e| ≤ M * faceMajorant p h a b μ e := by
  have hGint : IntegrableOn (fun w => G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e)
      (box ι b) := integrable_faceCoeff hb hG hGM hμ le_rfl
  unfold faceCoeffInt faceMajorant
  rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrableOn_faceMajorant hb hμ e).const_mul M) ?_
  refine (ae_restrict_mem (measurableSet_box b)).mono fun w hw => ?_
  have hpos := pos_of_mem_box hw
  have h1 : 0 ≤ mono h w * mono a w ^ (-μ) * |logSum a w| ^ e := by
    have := mono_pos h hpos
    have := rpow_pos_of_pos (mono_pos a hpos) (-μ)
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (mono_pos h hpos),
    abs_of_pos (rpow_pos_of_pos (mono_pos a hpos) _), abs_pow]
  calc |G w| * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e
      = |G w| * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring
    _ ≤ M * mono p w * (mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) :=
        mul_le_mul_of_nonneg_right (hGM w hw) h1
    _ = M * (mono p w * mono h w * mono a w ^ (-μ) * |logSum a w| ^ e) := by ring

end Majorant

/-! ### The explicit constant -/

variable {d : ℕ}

/-- ★★ **The coefficient bound constant**: `smoothCoeffAtDepth` with every face coefficient
replaced by its absolute value and every face coefficient integral by
`(∏_{i∉J} 1/(pᵢ−1)!) · faceMajorant`. It depends only on `(h, k, p, β, b, μ, q)`. -/
noncomputable def coeffBoundConstant (h k p : Fin d → ℕ) (β b μ : ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1),
    |faceCoef k β b x.1 (fun i => x.2 i + h i) μ j| * (j.choose q) *
      ((∏ i : {i // ¬ inJ x.1 i}, ((p i - 1).factorial : ℝ)⁻¹) *
        faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
          (fun i : {i // ¬ inJ x.1 i} => 2 * k i) b μ (j - q))

theorem coeffBoundConstant_nonneg (h k p : Fin d → ℕ) (β b μ : ℝ) (q : ℕ) :
    0 ≤ coeffBoundConstant h k p β b μ q :=
  Finset.sum_nonneg fun x _ => mul_nonneg (faceW_nonneg _ _) <| Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (faceMajorant_nonneg _ _ _ _ _ _))

variable {F : (Fin d → ℝ) → ℝ} {h k p : Fin d → ℕ} {β b μ M : ℝ}

/-- The convergence condition restricted to the flat coordinates of a face. -/
theorem face_convergence (hμ : ∀ i, 2 * (k i : ℝ) * μ < p i + h i + 1) (J : Finset (Fin d))
    (i : {i // ¬ inJ J i}) :
    ((2 * k i.1 : ℕ) : ℝ) * μ < (p i.1 : ℝ) + h i.1 + 1 := by
  have := hμ i.1
  push_cast
  linarith

/-- The `(J, m)` face sum of `smoothCoeffAtDepth` is bounded by the corresponding face sum of the
constant, times `M`. -/
theorem abs_faceSum_le (hF : ContDiff ℝ ∞ F) (hb : 0 < b) (hp0 : ∀ i, 0 < p i)
    (hμ : ∀ i, 2 * (k i : ℝ) * μ < p i + h i + 1) (hFM : RectBound F p b M)
    {J : Finset (Fin d)} {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) (q : ℕ) :
    |∑ j ∈ Finset.Ico q (DJ J + 1), faceCoef k β b J (fun i => m i + h i) μ j * (j.choose q) *
        faceCoeffInt (faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i)
          (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)| ≤
      (∑ j ∈ Finset.Ico q (DJ J + 1), |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q) *
        ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) *
          faceMajorant (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
            (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q))) * M := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hint := abs_faceCoeffInt_le (ι := {i // ¬ inJ J i}) hb
    (continuous_faceAmp p J hF m).aestronglyMeasurable
    (fun w hw => faceAmp_bound p J hF hb hp0 hFM hm hw) (face_convergence hμ J) (j - q)
  rw [abs_mul, abs_mul, Nat.abs_cast]
  calc |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q) *
        |faceCoeffInt (faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i)
          (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)|
      ≤ |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q) *
        ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M *
          faceMajorant (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
            (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

/-- ★★★ **The quantitative coefficient bound at depth `p`**: for smooth `F` with the rectangular
mixed-derivative bound `|∂^m F| ≤ M` on `[0,b]^d` (`m ≤ p`), under the convergence condition
`2kᵢ μ < pᵢ + hᵢ + 1`,
`|smoothCoeffAtDepth F h k p β b μ q| ≤ coeffBoundConstant h k p β b μ q · M`,
with a constant independent of the amplitude. -/
theorem abs_smoothCoeffAtDepth_le (hF : ContDiff ℝ ∞ F) (hb : 0 < b) (hp0 : ∀ i, 0 < p i)
    (hμ : ∀ i, 2 * (k i : ℝ) * μ < p i + h i + 1) (hFM : RectBound F p b M) (q : ℕ) :
    |smoothCoeffAtDepth F h k p β b μ q| ≤ coeffBoundConstant h k p β b μ q * M := by
  unfold smoothCoeffAtDepth coeffBoundConstant
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hW := faceW_nonneg x.1 x.2
  rw [abs_mul, abs_of_nonneg hW]
  exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (abs_faceSum_le hF hb hp0 hμ hFM hm q) hW)
    (by ring)

/-- The convergence condition holds automatically at the canonical depth. -/
theorem canonical_convergence (hk : ∀ i, 0 < k i) (h : Fin d → ℕ) (μ : ℝ) (i : Fin d) :
    2 * (k i : ℝ) * μ < depthOf h k (cutoffOf h μ) i + h i + 1 := by
  have h1 : ((depthOf h k (cutoffOf h μ) i : ℕ) : ℝ) + h i = 2 * k i * cutoffOf h μ := by
    exact_mod_cast depthOf_add hk (L₀_le_cutoffOf h μ) i
  have h2 := lt_cutoffOf h μ
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  have h3 : (0 : ℝ) < 2 * k i := by linarith
  have := mul_lt_mul_of_pos_left h2 h3
  linarith

/-- ★★★ **The quantitative bound on the canonical smooth coefficients**: for smooth `F` with the
rectangular bound `|∂^m F| ≤ M` on `[0,b]^d` at the canonical depth `p = 2k·cutoffOf h μ − h`,
`|smoothCoeff F h k β b μ q| ≤ coeffBoundConstant h k p β b μ q · M`. -/
theorem abs_smoothCoeff_le (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hb : 0 < b)
    (hFM : RectBound F (depthOf h k (cutoffOf h μ)) b M) (q : ℕ) :
    |smoothCoeff F h k β b μ q| ≤
      coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q * M := by
  unfold smoothCoeff
  exact abs_smoothCoeffAtDepth_le hF hb (depthOf_pos hk (L₀_le_cutoffOf h μ))
    (canonical_convergence hk h μ) hFM q

/-! ### Families over a base -/

/-- ★ **The integrated coefficients with a constant phase unit**: for a smooth amplitude family
with the uniform rectangular bound `M` at the canonical depth and a finite base measure,
`|familyCoeff ν F h k (fun _ => β) b μ q| ≤ coeffBoundConstant … · M · ν(S)`. -/
theorem abs_familyCoeff_le_const_beta {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] (F : SmoothAmplitudeFamily S d b) (hk : ∀ i, 0 < k i)
    (hb : 0 < b) (hFM : ∀ s, RectBound (F s) (depthOf h k (cutoffOf h μ)) b M) (q : ℕ) :
    |familyCoeff ν F h k (fun _ => β) b μ q| ≤
      coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q * M * ν.real univ := by
  unfold familyCoeff
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs]
  exact abs_smoothCoeff_le (F.smooth s) hk hb (hFM s) q

end SmoothEngine

end Grammar
