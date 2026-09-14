/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceTheorem
import Grammar.SmoothOneDim

/-!
# The inner monomial integral and the one-variable face theorem (consult #116, milestone 3 prep)

The one-dimensional monomial integral `Z_e(t) = ∫_0^b v^e e^{−t v^{2k}} dv` satisfies the GLOBAL
two-regime estimate `|Z_e(t) − Γ(λ_e)/(2k) · t^{−λ_e}| ≤ C t^{−L}` for every `t > 0` and every
natural `L ≥ λ_e = (e+1)/(2k)` (★ `innerMono_two_regime`: for `t ≥ 1` the tail beyond `b` is
exponentially small, for `t < 1` the remainder is the tail itself, at most the leading term).
This is exactly the input `hZ2` of the generic face theorem (`face_expansion`) with the
spectrum `{λ_e}` and logarithmic degree `0`. We also record the measure-theoretic bridges from
the abstract box `(0,b]^ι` to iterated one-dimensional integrals for `ι = Fin 1` and `ι = Fin 2`
(`integral_box_one`, `integral_box_two`, `integral_box_two'`) and the resulting one-variable face
theorem `face_expansion_one`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset intervalIntegral

namespace Grammar

namespace SmoothEngine

/-! ### The inner monomial integral -/

/-- `Z_e(t) = ∫_0^b v^e e^{−t v^{2k}} dv`. -/
noncomputable def innerMono (k e : ℕ) (b t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..b, v ^ e * exp (-t * v ^ (2 * k))

theorem continuous_innerMono (k e : ℕ) (b : ℝ) : Continuous (innerMono k e b) := by
  unfold innerMono
  exact continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t v : ℝ => v ^ e * exp (-t * v ^ (2 * k))) (by fun_prop) 0 b

theorem innerMono_nonneg (k e : ℕ) {b : ℝ} (hb : 0 ≤ b) (t : ℝ) : 0 ≤ innerMono k e b t :=
  intervalIntegral.integral_nonneg hb fun _ hv => mul_nonneg (pow_nonneg hv.1 _) (exp_pos _).le

/-- The leading coefficient `Γ(λ_e)/(2k)`. -/
noncomputable def innerCoeff (k e : ℕ) : ℝ := Gamma (lam k e) / (2 * k)

theorem innerCoeff_nonneg {k : ℕ} (hk : 0 < k) (e : ℕ) : 0 ≤ innerCoeff k e :=
  div_nonneg (Gamma_pos_of_pos (lam_pos hk e)).le (by positivity)

/-- The exact identity `Z_e(t) = Γ(λ_e)/(2k) t^{−λ_e} − ∫_b^∞ v^e e^{−t v^{2k}} dv`. -/
theorem innerMono_eq {k : ℕ} (hk : 0 < k) (e : ℕ) {b : ℝ} (hb : 0 ≤ b) {t : ℝ} (ht : 0 < t) :
    innerMono k e b t = innerCoeff k e * t ^ (-lam k e) - monoTail 1 k e b t := by
  have h := integral_pow_mul_exp_eq (β := 1) one_pos hk e hb ht
  simp only [mul_one, Real.one_rpow] at h
  unfold innerMono innerCoeff
  exact h

theorem tailConst_one_nonneg (k e : ℕ) : 0 ≤ tailConst 1 k e :=
  setIntegral_nonneg measurableSet_Ioi fun _ hv =>
    mul_nonneg (pow_nonneg (le_of_lt hv) _) (exp_pos _).le

/-- The two-regime constant. -/
noncomputable def innerConst (k e : ℕ) (b : ℝ) (L : ℕ) : ℝ :=
  max (tailConst 1 k e * L.factorial / (b ^ (2 * k) / 2) ^ L) (innerCoeff k e)

theorem innerConst_nonneg {k : ℕ} (hk : 0 < k) (e : ℕ) (b : ℝ) (L : ℕ) :
    0 ≤ innerConst k e b L :=
  le_max_of_le_right (innerCoeff_nonneg hk e)

/-- ★ **The global two-regime estimate for the inner monomial integral**:
`|Z_e(t) − Γ(λ_e)/(2k) t^{−λ_e}| ≤ C t^{−L}` for all `t > 0`, `L ≥ λ_e`. -/
theorem innerMono_two_regime {k : ℕ} (hk : 0 < k) (e : ℕ) {b : ℝ} (hb : 0 < b) (L : ℕ)
    (hL : lam k e ≤ L) {t : ℝ} (ht : 0 < t) :
    |innerMono k e b t - innerCoeff k e * t ^ (-lam k e)| ≤
      innerConst k e b L * t ^ (-(L : ℝ)) := by
  have hid := innerMono_eq hk e hb.le ht
  have htail : 0 ≤ monoTail 1 k e b t := monoTail_nonneg e hb.le t
  have hrem : |innerMono k e b t - innerCoeff k e * t ^ (-lam k e)| = monoTail 1 k e b t := by
    rw [hid, sub_sub_cancel_left, abs_neg, abs_of_nonneg htail]
  rw [hrem]
  have hrp : t ^ (-(L : ℝ)) = (t ^ L)⁻¹ := by rw [rpow_neg ht.le, rpow_natCast]
  rcases le_or_gt 1 t with h1 | h1
  · have hmt := monoTail_le (β := 1) one_pos hk e hb.le h1
    have hc : 0 < b ^ (2 * k) / 2 := by positivity
    have hexp := exp_neg_mul_le L hc ht
    have hT := tailConst_one_nonneg k e
    have hform : t * 1 * b ^ (2 * k) / 2 = b ^ (2 * k) / 2 * t := by ring
    rw [hform] at hmt
    have hL' : 0 ≤ (L.factorial : ℝ) / (b ^ (2 * k) / 2) ^ L / t ^ L := by positivity
    calc monoTail 1 k e b t ≤ exp (-(b ^ (2 * k) / 2 * t)) * tailConst 1 k e := hmt
      _ ≤ (L.factorial : ℝ) / (b ^ (2 * k) / 2) ^ L / t ^ L * tailConst 1 k e :=
          mul_le_mul_of_nonneg_right hexp hT
      _ = tailConst 1 k e * L.factorial / (b ^ (2 * k) / 2) ^ L * (t ^ L)⁻¹ := by ring
      _ ≤ innerConst k e b L * (t ^ L)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = innerConst k e b L * t ^ (-(L : ℝ)) := by rw [hrp]
  · have hZ := innerMono_nonneg k e hb.le t
    have hpow : t ^ (-lam k e) ≤ t ^ (-(L : ℝ)) :=
      rpow_le_rpow_of_exponent_ge ht h1.le (by linarith)
    have hcoef := innerCoeff_nonneg hk e
    calc monoTail 1 k e b t = innerCoeff k e * t ^ (-lam k e) - innerMono k e b t := by
          linarith
      _ ≤ innerCoeff k e * t ^ (-lam k e) := by linarith
      _ ≤ innerCoeff k e * t ^ (-(L : ℝ)) := mul_le_mul_of_nonneg_left hpow hcoef
      _ ≤ innerConst k e b L * t ^ (-(L : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg ht.le _)

/-- The face-theorem input for the inner integral at the effective parameter `β t`:
spectrum `{λ_e}`, coefficient `Γ(λ_e)/(2k) β^{−λ_e}`, logarithmic degree `0`. -/
theorem innerMono_two_regime_beta {k : ℕ} (hk : 0 < k) (e : ℕ) {b : ℝ} (hb : 0 < b) {β : ℝ}
    (hβ : 0 < β) (L : ℕ) (hL : lam k e ≤ L) {t : ℝ} (ht : 0 < t) :
    |innerMono k e b (β * t) - powLog {lam k e} 0 (fun μ _ => innerCoeff k e * β ^ (-μ)) t| ≤
      innerConst k e b L * β ^ (-(L : ℝ)) * t ^ (-(L : ℝ)) * (1 + |log t|) ^ 0 := by
  have h := innerMono_two_regime hk e hb L hL (mul_pos hβ ht)
  rw [Real.mul_rpow hβ.le ht.le, Real.mul_rpow hβ.le ht.le] at h
  have hp : powLog {lam k e} 0 (fun μ _ => innerCoeff k e * β ^ (-μ)) t =
      innerCoeff k e * (β ^ (-lam k e) * t ^ (-lam k e)) := by
    simp only [powLog, Finset.sum_singleton, zero_add, Finset.sum_range_one, pow_zero, mul_one]
    ring
  rw [hp, pow_zero, mul_one]
  calc |innerMono k e b (β * t) - innerCoeff k e * (β ^ (-lam k e) * t ^ (-lam k e))|
      ≤ innerConst k e b L * (β ^ (-(L : ℝ)) * t ^ (-(L : ℝ))) := h
    _ = _ := by ring

/-! ### Bridges from the abstract box to iterated integrals -/

theorem box_one_preimage (b : ℝ) :
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹' box (Fin 1) b = Ioc 0 b := by
  ext y
  simp [box, Set.mem_pi]

/-- The box integral over `(0,b]^{Fin 1}` is the one-dimensional integral. -/
theorem integral_box_one (b : ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    ∫ w in box (Fin 1) b, f w = ∫ y in Ioc 0 b, f (fun _ => y) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).symm.setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding f (box (Fin 1) b)
  rw [box_one_preimage] at h
  refine h.symm.trans (setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_)
  exact congrArg f (funext fun _ => rfl)

theorem finTwoArrow_symm_apply' (x y : ℝ) :
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (x, y) = ![x, y] := by
  funext i
  fin_cases i <;> rfl

theorem box_two_preimage (b : ℝ) :
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm ⁻¹' box (Fin 2) b = Ioc 0 b ×ˢ Ioc 0 b := by
  ext ⟨x, y⟩
  rw [Set.mem_preimage, finTwoArrow_symm_apply', Set.mem_prod, box, Set.mem_univ_pi,
    Fin.forall_fin_two]
  simp

/-- The composite `f ∘ finTwoArrow.symm` is integrable on the product of intervals. -/
theorem integrableOn_comp_finTwoArrow_symm (b : ℝ) (f : (Fin 2 → ℝ) → ℝ)
    (hf : IntegrableOn f (box (Fin 2) b)) :
    IntegrableOn (f ∘ (MeasurableEquiv.finTwoArrow (α := ℝ)).symm) (Ioc 0 b ×ˢ Ioc 0 b) := by
  rw [← box_two_preimage]
  exact ((volume_preserving_finTwoArrow ℝ).symm.integrableOn_comp_preimage
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.measurableEmbedding).2 hf

theorem integral_box_eq_prod (b : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    ∫ v in box (Fin 2) b, f v =
      ∫ z in Ioc 0 b ×ˢ Ioc 0 b, f ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm z) := by
  have h := (volume_preserving_finTwoArrow ℝ).symm.setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.measurableEmbedding f (box (Fin 2) b)
  rw [box_two_preimage] at h
  exact h.symm

/-- Fubini on the square `(0,b]^{Fin 2}`, outer variable the first coordinate. -/
theorem integral_box_two (b : ℝ) (f : (Fin 2 → ℝ) → ℝ) (hf : IntegrableOn f (box (Fin 2) b)) :
    ∫ v in box (Fin 2) b, f v = ∫ x in Ioc 0 b, ∫ y in Ioc 0 b, f ![x, y] := by
  rw [integral_box_eq_prod]
  have h2 := setIntegral_prod (μ := volume) (ν := volume) _
    (integrableOn_comp_finTwoArrow_symm b f hf)
  simp only [Function.comp_def, finTwoArrow_symm_apply'] at h2
  exact h2

/-- Fubini on the square `(0,b]^{Fin 2}`, outer variable the second coordinate. -/
theorem integral_box_two' (b : ℝ) (f : (Fin 2 → ℝ) → ℝ) (hf : IntegrableOn f (box (Fin 2) b)) :
    ∫ v in box (Fin 2) b, f v = ∫ y in Ioc 0 b, ∫ x in Ioc 0 b, f ![x, y] := by
  rw [integral_box_eq_prod]
  have hint : Integrable (f ∘ (MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
      ((volume.restrict (Ioc 0 b)).prod (volume.restrict (Ioc 0 b))) := by
    rw [Measure.prod_restrict]
    exact integrableOn_comp_finTwoArrow_symm b f hf
  have h2 := integral_prod_symm _ hint
  rw [Measure.prod_restrict] at h2
  simp only [Function.comp_def, finTwoArrow_symm_apply'] at h2
  exact h2

/-- Continuous functions are integrable on the box. -/
theorem integrableOn_box_of_continuous {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) (b : ℝ) : IntegrableOn f (box ι b) := by
  refine (hf.continuousOn.integrableOn_compact (K := Set.pi univ fun _ => Icc 0 b)
    (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set fun w hw i _ => ?_
  exact Ioc_subset_Icc_self (hw i (Set.mem_univ i))

/-! ### The one-variable face theorem -/

/-- ★ **The face theorem with one outer variable**: `∫_0^b G(y) y^h Z'(N y^a) dy` expands with
coefficients `∫_0^b G(y) y^h (y^a)^{−μ} (a log y)^{j−q} dy` and remainder
`≤ C M (1 + log N)^D N^{−L} ∫_0^b y^{p+h−aL} (1 + |a log y|)^D dy`. -/
theorem face_expansion_one {G Z' : ℝ → ℝ} {p h a : ℕ} {b M C L N : ℝ} {Λ : Finset ℝ} {D : ℕ}
    {c : ℝ → ℕ → ℝ} (hb : 0 < b) (hG : Continuous G)
    (hGM : ∀ y ∈ Ioc 0 b, |G y| ≤ M * y ^ p) (hZm : Measurable Z')
    (hZ2 : ∀ t : ℝ, 0 < t → |Z' t - powLog Λ D c t| ≤ C * t ^ (-L) * (1 + |log t|) ^ D)
    (hΛ : ∀ μ ∈ Λ, μ ≤ L) (hA : (a : ℝ) * L < p + h + 1) (hN : 1 ≤ N) :
    |(∫ y in Ioc 0 b, G y * y ^ h * Z' (N * y ^ a)) -
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        c μ j * (j.choose q) * log N ^ q *
          ∫ y in Ioc 0 b, G y * y ^ h * (y ^ a) ^ (-μ) * ((a : ℝ) * log y) ^ (j - q)| ≤
      C * M * (1 + log N) ^ D * N ^ (-L) *
        ∫ y in Ioc 0 b, y ^ ((p + h : ℝ) - a * L) * (1 + |(a : ℝ) * log y|) ^ D := by
  have hG' : AEStronglyMeasurable (fun w : Fin 1 → ℝ => G (w 0))
      (volume.restrict (box (Fin 1) b)) :=
    (hG.comp (continuous_apply 0)).aestronglyMeasurable
  have hGM' : ∀ w ∈ box (Fin 1) b, |G (w 0)| ≤ M * mono (fun _ => p) w := fun w hw => by
    rw [mono, Fin.prod_univ_one]
    exact hGM (w 0) (hw 0 (mem_univ 0))
  have key := face_expansion (ι := Fin 1) (G := fun w => G (w 0)) (p := fun _ => p)
    (h := fun _ => h) (a := fun _ => a) hb hG' hGM' hZm hZ2 hΛ (fun _ => hA) hN
  simp only [mono, logSum, Fin.prod_univ_one, Fin.sum_univ_one, faceRemWeight, faceCoeffInt,
    integral_box_one] at key
  exact key

end SmoothEngine

end Grammar
