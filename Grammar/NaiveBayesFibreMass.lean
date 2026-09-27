/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesFibreFiniteness
import Grammar.PowerLogFaceCertificate

/-!
# The support and the fibre mass of the naive-Bayes pushforward density

For `λ ∈ (0,1)²` the fibre density `ρ(λ, ·)` vanishes outside `(−M₋, M₊)` — the Fréchet bounds
`M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`, `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))` (`nbFibreDensity_eq_zero_of_ge/le`,
from the quadrant product `P(t)/(t(1−t)) ≤ M` on `(0,1)`), so with DXCIV's closed form
`2 log(M±/|μ|) log(V/(M±|μ|))` on `0 < |μ| < M±` the fibre integral is finite for EVERY interior
`λ` and computable: `∫ ρ(λ, μ) dμ = m(λ) = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)`
(`lintegral_nbFibreDensity_eq_mass`, `integral_nbFixedDensity_eq_mass`), by the antiderivative
`z[(c₁ − log z)(c₂ − log z) + (c₁ + c₂ − 2 log z) + 2]` of `(c₁ − log z)(c₂ − log z)` and
`z log² z → 0`.  In particular the fixed-`λ` density is not normalised (Astra round 18: `m = 2`
at `λ = (½, ½)`); the conditional density of `μ` given `λ` is `ρ/m(λ)`.  Examples_slop §6.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- The upper Fréchet bound `M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`. -/
noncomputable def nbMplus (l₁ l₂ : ℝ) : ℝ := min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))

/-- The lower Fréchet bound `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`. -/
noncomputable def nbMminus (l₁ l₂ : ℝ) : ℝ := min (l₁ * l₂) ((1 - l₁) * (1 - l₂))

/-- The variance product `V = λ₁(1−λ₁)λ₂(1−λ₂)`. -/
noncomputable def nbV (l₁ l₂ : ℝ) : ℝ := l₁ * (1 - l₁) * (l₂ * (1 - l₂))

/-- The closed-form fibre density on one side, `2 log(M/z) log(V/(Mz))`. -/
noncomputable def nbClosed (M V z : ℝ) : ℝ := 2 * (Real.log (M / z) * Real.log (V / (M * z)))

/-- The fibre mass `m(λ) = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)`. -/
noncomputable def nbFibreMass (l₁ l₂ : ℝ) : ℝ :=
  2 * nbMplus l₁ l₂ * (Real.log (nbV l₁ l₂ / nbMplus l₁ l₂ ^ 2) + 2) +
    2 * nbMminus l₁ l₂ * (Real.log (nbV l₁ l₂ / nbMminus l₁ l₂ ^ 2) + 2)

/-! ### The support -/

section Quadrant

variable {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₁' : b₁ < 1) (hb₂ : 0 < b₂) (hb₂' : b₂ < 1)
include hb₁ hb₁' hb₂ hb₂'

/-- `P(t)/(t(1−t)) ≤ min(b₁(1−b₂), b₂(1−b₁))` on `(0,1)`. -/
theorem quadP_div_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quadP b₁ b₂ t / (t * (1 - t)) ≤ min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hc : 0 < t * (1 - t) := mul_pos ht0 ht1
  have hx₁ : 0 ≤ (1 - b₁) * t := mul_nonneg (sub_pos.mpr hb₁').le ht0.le
  have hy₁ : 0 ≤ b₁ * (1 - t) := mul_nonneg hb₁.le ht1.le
  have hx₂ : 0 ≤ (1 - b₂) * t := mul_nonneg (sub_pos.mpr hb₂').le ht0.le
  have hy₂ : 0 ≤ b₂ * (1 - t) := mul_nonneg hb₂.le ht1.le
  rw [div_le_iff₀ hc, quadP, min_mul_min_eq hx₁ hy₁ hx₂ hy₂, min_mul_of_nonneg _ _ hc.le]
  refine le_min (min_le_iff.2 (Or.inr (min_le_iff.2 (Or.inl (le_of_eq ?_)))))
    (min_le_iff.2 (Or.inl (min_le_iff.2 (Or.inr (le_of_eq ?_))))) <;> ring

/-- The quadrant integral vanishes at and beyond the Fréchet bound. -/
theorem quadJ_eq_zero_of_ge {z : ℝ} (hz : 0 < z)
    (hzM : min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) ≤ z) : quadJ b₁ b₂ z = 0 := by
  unfold quadJ
  refine (setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_).trans lintegral_zero
  have hQ0 : 0 ≤ quadP b₁ b₂ t / (t * (1 - t)) / z := by
    have := quadP_pos hb₁ hb₁' hb₂ hb₂' ht
    have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
    positivity
  have hQ : quadP b₁ b₂ t / (t * (1 - t)) / z ≤ 1 := by
    rw [div_le_one hz]; exact (quadP_div_le hb₁ hb₁' hb₂ hb₂' ht).trans hzM
  rw [max_eq_right (Real.log_nonpos hQ0 hQ), ENNReal.ofReal_zero, mul_zero]

end Quadrant

section Assemble

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

theorem nbMplus_pos : 0 < nbMplus l₁ l₂ :=
  lt_min (mul_pos h₁ (sub_pos.mpr h₂')) (mul_pos h₂ (sub_pos.mpr h₁'))

theorem nbMminus_pos : 0 < nbMminus l₁ l₂ :=
  lt_min (mul_pos h₁ h₂) (mul_pos (sub_pos.mpr h₁') (sub_pos.mpr h₂'))

theorem nbV_pos : 0 < nbV l₁ l₂ :=
  mul_pos (mul_pos h₁ (sub_pos.mpr h₁')) (mul_pos h₂ (sub_pos.mpr h₂'))

theorem nbMplus_sq_le : nbMplus l₁ l₂ ^ 2 ≤ nbV l₁ l₂ := by
  unfold nbMplus nbV
  have hm1 := min_le_left (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
  have hm2 := min_le_right (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
  have h0 : 0 ≤ min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) := le_min (by nlinarith) (by nlinarith)
  nlinarith [mul_le_mul hm1 hm2 h0 (by nlinarith)]

theorem nbMminus_sq_le : nbMminus l₁ l₂ ^ 2 ≤ nbV l₁ l₂ := by
  unfold nbMminus nbV
  have hm1 := min_le_left (l₁ * l₂) ((1 - l₁) * (1 - l₂))
  have hm2 := min_le_right (l₁ * l₂) ((1 - l₁) * (1 - l₂))
  have h0 : 0 ≤ min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) := le_min (by nlinarith) (by nlinarith)
  nlinarith [mul_le_mul hm1 hm2 h0 (by nlinarith)]

omit h₁ in
theorem nbMplus_le_one : nbMplus l₁ l₂ ≤ 1 :=
  (min_le_left _ _).trans (mul_le_one₀ h₁'.le (by linarith) (by linarith))

omit h₁ in
theorem nbMminus_le_one : nbMminus l₁ l₂ ≤ 1 :=
  (min_le_left _ _).trans (mul_le_one₀ h₁'.le h₂.le h₂'.le)

/-- ★★ The support theorem, `μ ≥ M₊`: the fibre density vanishes. -/
theorem nbFibreDensity_eq_zero_of_ge {z : ℝ} (hz : nbMplus l₁ l₂ ≤ z) :
    nbFibreDensity l₁ l₂ z = 0 := by
  have hz0 : 0 < z := lt_of_lt_of_le (nbMplus_pos h₁ h₁' h₂ h₂') hz
  have eM : min ((1 - l₁) * (1 - (1 - l₂))) ((1 - l₂) * (1 - (1 - l₁))) = nbMplus l₁ l₂ := by
    unfold nbMplus; rw [min_comm]; congr 1 <;> ring
  rw [nbFibreDensity_eq_quadJ_pos hz0, quadJ_eq_zero_of_ge h₁ h₁' h₂ h₂' hz0 hz,
    quadJ_eq_zero_of_ge (sub_pos.mpr h₁') (sub_lt_self 1 h₁) (sub_pos.mpr h₂') (sub_lt_self 1 h₂)
      hz0 (by rw [eM]; exact hz), add_zero]

/-- ★★ The support theorem, `μ ≤ −M₋`. -/
theorem nbFibreDensity_eq_zero_of_le {z : ℝ} (hz : z ≤ -nbMminus l₁ l₂) :
    nbFibreDensity l₁ l₂ z = 0 := by
  have hz0 : z < 0 := by linarith [nbMminus_pos h₁ h₁' h₂ h₂']
  have eM₁ : min (l₁ * (1 - (1 - l₂))) ((1 - l₂) * (1 - l₁)) = nbMminus l₁ l₂ := by
    unfold nbMminus; rw [sub_sub_cancel, mul_comm (1 - l₂) (1 - l₁)]
  have eM₂ : min ((1 - l₁) * (1 - l₂)) (l₂ * (1 - (1 - l₁))) = nbMminus l₁ l₂ := by
    unfold nbMminus; rw [min_comm, sub_sub_cancel, mul_comm l₂ l₁]
  rw [nbFibreDensity_eq_quadJ_neg hz0,
    quadJ_eq_zero_of_ge h₁ h₁' (sub_pos.mpr h₂') (sub_lt_self 1 h₂) (neg_pos.mpr hz0)
      (by rw [eM₁]; linarith),
    quadJ_eq_zero_of_ge (sub_pos.mpr h₁') (sub_lt_self 1 h₁) h₂ h₂' (neg_pos.mpr hz0)
      (by rw [eM₂]; linarith), add_zero]

omit h₁ h₁' h₂ h₂' in
theorem nbFibreDensity_zero : nbFibreDensity l₁ l₂ 0 = 0 := by
  unfold nbFibreDensity prodDensity
  simp

/-- The fibre density as the sum of the two closed-form pieces on `(0, M₊)` and `(−M₋, 0)`. -/
theorem nbFibreDensity_eq_indicator (z : ℝ) :
    nbFibreDensity l₁ l₂ z =
      (Ioo (0 : ℝ) (nbMplus l₁ l₂)).indicator
        (fun z => ENNReal.ofReal (nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂) z)) z +
      (Ioo (-nbMminus l₁ l₂) 0).indicator
        (fun z => ENNReal.ofReal (nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z))) z := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rw [indicator_of_notMem (fun h : z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂) =>
      absurd h.1 (not_lt.2 hz.le)),
      zero_add]
    rcases le_or_gt z (-nbMminus l₁ l₂) with hzM | hzM
    · rw [nbFibreDensity_eq_zero_of_le h₁ h₁' h₂ h₂' hzM,
        indicator_of_notMem (fun h : z ∈ Ioo (-nbMminus l₁ l₂) 0 => absurd h.1 (not_lt.2 hzM))]
    · rw [indicator_of_mem (show z ∈ Ioo (-nbMminus l₁ l₂) 0 from ⟨hzM, hz⟩),
        nbFibreDensity_closed_neg h₁ h₁' h₂ h₂' hz (by unfold nbMminus at hzM; linarith)]
      unfold nbClosed nbMminus nbV
      rfl
  · subst hz
    rw [nbFibreDensity_zero, indicator_of_notMem (fun h : (0 : ℝ) ∈ Ioo 0 (nbMplus l₁ l₂) =>
      lt_irrefl _ h.1), indicator_of_notMem (fun h : (0 : ℝ) ∈ Ioo (-nbMminus l₁ l₂) 0 =>
      lt_irrefl _ h.2), add_zero]
  · rw [indicator_of_notMem (fun h : z ∈ Ioo (-nbMminus l₁ l₂) 0 => absurd h.2 (not_lt.2 hz.le)),
      add_zero]
    rcases le_or_gt (nbMplus l₁ l₂) z with hzM | hzM
    · rw [nbFibreDensity_eq_zero_of_ge h₁ h₁' h₂ h₂' hzM,
        indicator_of_notMem (fun h : z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂) => absurd h.2 (not_lt.2 hzM))]
    · rw [indicator_of_mem (show z ∈ Ioo (0 : ℝ) (nbMplus l₁ l₂) from ⟨hz, hzM⟩),
        nbFibreDensity_closed_pos h₁ h₁' h₂ h₂' hz (by unfold nbMplus at hzM; exact hzM)]
      unfold nbClosed nbMplus nbV
      rfl

end Assemble

/-! ### The closed-form piece: integrability and the exact integral -/

theorem measurable_nbClosed (M V : ℝ) : Measurable (nbClosed M V) := by
  unfold nbClosed; fun_prop

theorem nbClosed_nonneg {M V z : ℝ} (hz : 0 < z) (hzM : z ≤ M) (hM2 : M ^ 2 ≤ V) :
    0 ≤ nbClosed M V z :=
  mul_nonneg two_pos.le (closed_nonneg hz hzM hM2)

/-- `|nbClosed M V z| ≤ 2(1 + |log M|)(1 + |log(V/M)|)(1 + |log z|)²` for `z > 0`. -/
theorem abs_nbClosed_le {M V z : ℝ} (hM : 0 < M) (hV : 0 < V) (hz : 0 < z) :
    |nbClosed M V z| ≤ 2 * ((1 + |Real.log M|) * (1 + |Real.log (V / M)|)) *
      (1 + |Real.log z|) ^ 2 := by
  unfold nbClosed
  rw [Real.log_div hM.ne' hz.ne', show V / (M * z) = V / M / z by rw [div_div],
    Real.log_div (div_pos hV hM).ne' hz.ne']
  have hL := abs_nonneg (Real.log z)
  have ha : |Real.log M - Real.log z| ≤ (1 + |Real.log M|) * (1 + |Real.log z|) := by
    have := abs_nonneg (Real.log M)
    calc |Real.log M - Real.log z| ≤ |Real.log M| + |Real.log z| := abs_sub _ _
      _ ≤ (1 + |Real.log M|) * (1 + |Real.log z|) := by nlinarith
  have hb : |Real.log (V / M) - Real.log z| ≤ (1 + |Real.log (V / M)|) * (1 + |Real.log z|) := by
    have := abs_nonneg (Real.log (V / M))
    calc |Real.log (V / M) - Real.log z| ≤ |Real.log (V / M)| + |Real.log z| := abs_sub _ _
      _ ≤ (1 + |Real.log (V / M)|) * (1 + |Real.log z|) := by nlinarith
  rw [abs_mul, abs_two, abs_mul]
  calc 2 * (|Real.log M - Real.log z| * |Real.log (V / M) - Real.log z|)
      ≤ 2 * (((1 + |Real.log M|) * (1 + |Real.log z|)) *
          ((1 + |Real.log (V / M)|) * (1 + |Real.log z|))) := by gcongr
    _ = 2 * ((1 + |Real.log M|) * (1 + |Real.log (V / M)|)) * (1 + |Real.log z|) ^ 2 := by ring

theorem integrableOn_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntegrableOn (nbClosed M V) (Ioo 0 M) := by
  have h := integrableOn_rpow_mul_logWeight (a := 0) (by norm_num) 2
  simp only [Real.rpow_zero, one_mul] at h
  have h' := (h.mono_set (Ioo_subset_Ioo_right hM1)).const_mul
    (2 * ((1 + |Real.log M|) * (1 + |Real.log (V / M)|)))
  refine h'.mono' (measurable_nbClosed M V).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun z hz => by
    rw [Real.norm_eq_abs]; exact abs_nbClosed_le hM hV hz.1

theorem intervalIntegrable_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntervalIntegrable (nbClosed M V) volume 0 M := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hM.le]
  exact integrableOn_nbClosed hM hM1 hV

/-- The antiderivative `2z[(c₁ − log z)(c₂ − log z) + (c₁ + c₂ − 2 log z) + 2]`. -/
theorem hasDerivAt_nbClosed_primitive {M V z : ℝ} (hM : 0 < M) (hV : 0 < V) (hz : 0 < z) :
    HasDerivAt (fun z : ℝ => 2 * (z * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) + 2))) (nbClosed M V z) z := by
  have hl := Real.hasDerivAt_log hz.ne'
  have h1 : HasDerivAt (fun z : ℝ => Real.log M - Real.log z) (-z⁻¹) z := hl.const_sub _
  have h2 : HasDerivAt (fun z : ℝ => Real.log (V / M) - Real.log z) (-z⁻¹) z := hl.const_sub _
  have h3 : HasDerivAt (fun z : ℝ => Real.log M + Real.log (V / M) - 2 * Real.log z)
      (-(2 * z⁻¹)) z := (hl.const_mul 2).const_sub _
  have h4 := ((h1.mul h2).add h3).add_const 2
  have h5 := (hasDerivAt_id' (x := z)).mul h4
  have h6 := h5.const_mul 2
  refine h6.congr_deriv ?_
  unfold nbClosed
  rw [Real.log_div hM.ne' hz.ne', show V / (M * z) = V / M / z by rw [div_div],
    Real.log_div (div_pos hV hM).ne' hz.ne']
  simp only [Pi.add_apply, Pi.mul_apply]
  set L := Real.log z with hL
  set c₁ := Real.log M with hc₁
  set c₂ := Real.log (V / M) with hc₂
  field_simp
  ring

/-- The primitive tends to `0` at `0⁺` (`z log z → 0`, `z log² z → 0`). -/
theorem tendsto_nbClosed_primitive_zero (M V : ℝ) :
    Tendsto (fun z : ℝ => 2 * (z * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) + 2))) (𝓝[>] 0) (𝓝 0) := by
  have t1 := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  simp only [Real.rpow_one] at t1
  have t2 := tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)
  simp only [← Real.sqrt_eq_rpow] at t2
  have t0 : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  set c₁ := Real.log M with hc₁
  set c₂ := Real.log (V / M) with hc₂
  have := ((t0.const_mul (2 * (c₁ * c₂ + c₁ + c₂ + 2))).sub
    (t1.const_mul (2 * (c₁ + c₂ + 2)))).add ((t2.mul t2).const_mul 2)
  simp only [mul_zero, sub_zero, add_zero] at this
  refine this.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz0 : (0 : ℝ) < z := hz
  have hs : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz0.le
  simp only
  rw [show Real.log z * Real.sqrt z * (Real.log z * Real.sqrt z) =
    Real.log z * Real.log z * (Real.sqrt z * Real.sqrt z) by ring, hs]
  ring

/-- ★★ `∫₀^M 2 log(M/z) log(V/(Mz)) dz = 2M(log(V/M²) + 2)`. -/
theorem integral_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (0 : ℝ) M, nbClosed M V z = 2 * M * (Real.log (V / M ^ 2) + 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hM.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hM
      (fun z hz => hasDerivAt_nbClosed_primitive hM hV hz.1) (intervalIntegrable_nbClosed hM hM1 hV)
      (tendsto_nbClosed_primitive_zero M V)
      ((hasDerivAt_nbClosed_primitive hM hV hM).continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
    sub_zero, Real.log_div hV.ne' (pow_pos hM 2).ne', Real.log_pow, Real.log_div hV.ne' hM.ne']
  push_cast
  ring

/-- The reflected piece: `∫_{−M}^0 nbClosed M V (−z) dz = 2M(log(V/M²) + 2)`. -/
theorem integral_nbClosed_neg {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (-M) (0 : ℝ), nbClosed M V (-z) = 2 * M * (Real.log (V / M ^ 2) + 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -M ≤ 0),
    intervalIntegral.integral_comp_neg (f := fun z => nbClosed M V z), neg_zero, neg_neg,
    intervalIntegral.integral_of_le hM.le, integral_Ioc_eq_integral_Ioo,
    integral_nbClosed hM hM1 hV]

theorem integrableOn_nbClosed_neg {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntegrableOn (fun z => nbClosed M V (-z)) (Ioo (-M) 0) := by
  have h := integrableOn_nbClosed hM hM1 hV
  rw [← integrable_indicator_iff measurableSet_Ioo] at h ⊢
  refine (Integrable.comp_neg h).congr (ae_of_all _ fun z => ?_)
  simp only [Set.indicator_apply, mem_Ioo]
  by_cases hz : -M < z ∧ z < 0
  · rw [if_pos hz, if_pos ⟨by linarith [hz.2], by linarith [hz.1]⟩]
  · rw [if_neg hz, if_neg (fun h => hz ⟨by linarith [h.2], by linarith [h.1]⟩)]

/-! ### The fibre mass -/

section Mass

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

theorem nbFibreMass_nonneg : 0 ≤ nbFibreMass l₁ l₂ := by
  have hM := nbMplus_pos h₁ h₁' h₂ h₂'
  have hMm := nbMminus_pos h₁ h₁' h₂ h₂'
  have hM2 := nbMplus_sq_le h₁ h₁' h₂ h₂'
  have hMm2 := nbMminus_sq_le h₁ h₁' h₂ h₂'
  have h1 : 0 ≤ Real.log (nbV l₁ l₂ / nbMplus l₁ l₂ ^ 2) :=
    Real.log_nonneg ((one_le_div (pow_pos hM 2)).2 hM2)
  have h2 : 0 ≤ Real.log (nbV l₁ l₂ / nbMminus l₁ l₂ ^ 2) :=
    Real.log_nonneg ((one_le_div (pow_pos hMm 2)).2 hMm2)
  unfold nbFibreMass
  positivity

/-- ★★★ **The fibre mass**: for every `λ ∈ (0,1)²`,
`∫ ρ(λ, μ) dμ = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)`. -/
theorem lintegral_nbFibreDensity_eq_mass :
    ∫⁻ z, nbFibreDensity l₁ l₂ z = ENNReal.ofReal (nbFibreMass l₁ l₂) := by
  have hM := nbMplus_pos h₁ h₁' h₂ h₂'
  have hMm := nbMminus_pos h₁ h₁' h₂ h₂'
  have hV := nbV_pos h₁ h₁' h₂ h₂'
  have hM1 := nbMplus_le_one h₁' h₂ h₂'
  have hMm1 := nbMminus_le_one h₁' h₂ h₂'
  have hM2 := nbMplus_sq_le h₁ h₁' h₂ h₂'
  have hMm2 := nbMminus_sq_le h₁ h₁' h₂ h₂'
  rw [lintegral_congr (nbFibreDensity_eq_indicator h₁ h₁' h₂ h₂'),
    lintegral_add_left ((measurable_nbClosed _ _).ennreal_ofReal.indicator measurableSet_Ioo),
    lintegral_indicator measurableSet_Ioo, lintegral_indicator measurableSet_Ioo]
  have hnnP : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) (nbMplus l₁ l₂))]
      nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂) :=
    (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun z hz =>
      nbClosed_nonneg hz.1 hz.2.le hM2)
  have hnnM : 0 ≤ᵐ[volume.restrict (Ioo (-nbMminus l₁ l₂) (0 : ℝ))]
      fun z => nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z) :=
    (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun z hz =>
      nbClosed_nonneg (neg_pos.2 hz.2) (by linarith [hz.1]) hMm2)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_nbClosed hM hM1 hV) hnnP,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_nbClosed_neg hMm hMm1 hV) hnnM,
    integral_nbClosed hM hM1 hV, integral_nbClosed_neg hMm hMm1 hV,
    ← ENNReal.ofReal_add (by
      have := Real.log_nonneg ((one_le_div (pow_pos hM 2)).2 hM2); positivity) (by
      have := Real.log_nonneg ((one_le_div (pow_pos hMm 2)).2 hMm2); positivity)]
  rfl

/-- ★★ Every interior fibre has finite mass. -/
theorem lintegral_nbFibreDensity_ne_top : ∫⁻ z, nbFibreDensity l₁ l₂ z ≠ ⊤ := by
  rw [lintegral_nbFibreDensity_eq_mass h₁ h₁' h₂ h₂']; exact ENNReal.ofReal_ne_top

/-- ★★ The real fixed-domain density is integrable in `μ` for every interior `λ`. -/
theorem integrable_nbFixedDensity : Integrable fun z : ℝ => nbFixedDensity ((l₁, l₂), z) := by
  rw [nbFixedDensity_eq_toReal' (l₁, l₂)]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_nbFibreDensity_right (l₁, l₂)).aemeasurable
    (lintegral_nbFibreDensity_ne_top h₁ h₁' h₂ h₂')

/-- ★★★ The real fibre mass: `∫ nbFixedDensity ((λ₁, λ₂), μ) dμ = m(λ)`. -/
theorem integral_nbFixedDensity_eq_mass :
    ∫ z : ℝ, nbFixedDensity ((l₁, l₂), z) = nbFibreMass l₁ l₂ := by
  have hm := measurable_nbFibreDensity_right (l₁, l₂)
  have hne := lintegral_nbFibreDensity_ne_top h₁ h₁' h₂ h₂'
  rw [nbFixedDensity_eq_toReal' (l₁, l₂), integral_toReal hm.aemeasurable (ae_lt_top hm hne),
    lintegral_nbFibreDensity_eq_mass h₁ h₁' h₂ h₂',
    ENNReal.toReal_ofReal (nbFibreMass_nonneg h₁ h₁' h₂ h₂')]

end Mass

/-- At `λ = (½, ½)` the fibre mass is `2`: the fixed-`λ` density is not normalised. -/
theorem nbFibreMass_half : nbFibreMass (1 / 2) (1 / 2) = 2 := by
  unfold nbFibreMass nbMplus nbMminus nbV
  norm_num

end Grammar
