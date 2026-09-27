/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensityPolar
import Grammar.TieFormulaSmooth
import Mathlib.Data.Real.Sign

/-!
# The polar distributions of the `log²` state density (the naive Bayes fibre)

The fibre density of the naive Bayes moment map at fixed means (examples_slop §6,
`nbFibreDensity_closed_pos/neg`) is `2 log²(√V/|μ|) − c + b·sgn μ` on `0 < |μ| < M`.  For
`ℓ = log √V`, a continuous test amplitude `φ` with `|φ(t) − φ(0)| ≤ L|t|`, and a cutoff `0 < M ≤ 1`,
the Mellin transform

  `F(s) = ∫_{−M}^{M} φ(t) (2 log²(√V/|t|) − c + b sgn t) |t|^{−2s} dt`

continues from `Re s < ½` to a neighbourhood of `½` with the principal part (★★★
`logSqMellinFull_polar`)

  `−φ(0)/(s−½)³ + 2ℓ φ(0)/(s−½)² + (c − 2ℓ²) φ(0)/(s−½)`,

i.e. `C_{½,3} = −δ₀`, `C_{½,2} = 2ℓ δ₀`, `C_{½,1} = (c − 2ℓ²) δ₀`: a triple pole (multiplicity three
as a formula), the `log V` shift in the second coefficient, and the constant and the log-square of
the scale in the third; the odd term `b sgn t` contributes no pole (its symmetrised amplitude
`b(φ(t) − φ(−t))` is `O(t)`), and the cutoff `M` only a holomorphic term.  Route: the log-square
Mellin integral `∫_0^1 t^{−2s} log²(1/t) dt = 2/(1−2s)³` by differentiating DXCIX's
`integral_cpow_log_Ioc` (`hasDerivAt_mellinIoc` with the log majorant), the strip identity for the
symmetrised amplitude on `(0,1]` (`logSqMellin_eq`), holomorphy of the remainder on `Re s < 1`
(`differentiableOn_logSqRem`), the cutoff piece as a Mellin integral with a large power bound, and
the uniqueness of principal parts.  Astra round-3 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The log-square Mellin integral -/

/-- `s ↦ ∫_0^1 t^{−2s}(−2 log t) dt` is differentiable on `Re s < ½` with derivative
`∫_0^1 t^{−2s}(−2 log t)² dt`. -/
theorem hasDerivAt_integral_cpow_log {s : ℂ} (hs : s.re < 1 / 2) :
    HasDerivAt (fun s : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)))
      (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)) *
        (-2 * (Real.log t : ℂ))) s := by
  set δ : ℝ := 1 / 2 - s.re with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hg : AEStronglyMeasurable (fun t : ℝ => (-2 * (Real.log t : ℂ)))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      Real.measurable_log.aestronglyMeasurable).const_mul _)
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(-2 * (Real.log t : ℂ))‖ ≤ 2 / δ * t ^ (-δ) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(-2 : ℂ)‖ = 2 by norm_num]
    have := abs_log_le_rpow_div hδpos ht
    calc 2 * |Real.log t| ≤ 2 * (t ^ (-δ) / δ) := by gcongr
      _ = 2 / δ * t ^ (-δ) := by ring
  have h := hasDerivAt_mellinIoc hg (by positivity) hb (s := s) (by rw [hδ]; linarith)
  unfold mellinIoc at h
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring

/-- `∫_0^1 t^{−2s} log²(1/t) dt = 2/(1 − 2s)³` for `Re s < ½`. -/
theorem integral_cpow_log_sq_Ioc {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (Real.log (1 / t) : ℂ) ^ 2 =
      2 / (1 - 2 * s) ^ 3 := by
  have h1 := hasDerivAt_integral_cpow_log hs
  have hne : (1 - 2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : HasDerivAt (fun s : ℂ => 2 / (1 - 2 * s) ^ 2) (8 / (1 - 2 * s) ^ 3) s := by
    have hlin : HasDerivAt (fun s : ℂ => 1 - 2 * s) (-2) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub 1
    have hmul := hlin.mul hlin
    have hinv := hmul.inv (mul_ne_zero hne hne)
    have e : (fun s : ℂ => 2 / (1 - 2 * s) ^ 2) = fun s => 2 * ((1 - 2 * s) * (1 - 2 * s))⁻¹ := by
      funext s; ring
    rw [e]
    refine (hinv.const_mul 2).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp
    ring
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : HasDerivAt (fun s : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) *
      (-2 * (Real.log t : ℂ))) (8 / (1 - 2 * s) ^ 3) s :=
    h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hopen.mem_nhds hs)
      fun z hz => integral_cpow_log_Ioc hz)
  have := h1.unique h3
  have e : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (Real.log (1 / t) : ℂ) ^ 2 =
      (1 / 4) * ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)) *
        (-2 * (Real.log t : ℂ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [one_div, Real.log_inv]
    push_cast
    ring
  rw [e, this]
  field_simp
  ring

/-! ### The log-square density on `(0, 1]` -/

/-- The even part of the density against a symmetrised amplitude: `(2(ℓ + log(1/t))² − c) ψ(t)`. -/
noncomputable def logSqAmp (ℓ c : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (((2 * (ℓ + Real.log (1 / t)) ^ 2 - c) * ψ t : ℝ) : ℂ)

noncomputable def logSqMellin (ℓ c : ℝ) (ψ : ℝ → ℝ) (s : ℂ) : ℂ := mellinIoc (logSqAmp ℓ c ψ) s

noncomputable def logSqRem (ℓ c : ℝ) (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellinIoc (logSqAmp ℓ c fun t => ψ t - ψ 0) s

/-- The rational principal part of the density itself. -/
noncomputable def logSqRat (ℓ c : ℝ) (s : ℂ) : ℂ :=
  2 * (ℓ : ℂ) ^ 2 / (1 - 2 * s) + 4 * (ℓ : ℂ) / (1 - 2 * s) ^ 2 + 4 / (1 - 2 * s) ^ 3 -
    (c : ℂ) / (1 - 2 * s)

noncomputable def logSqCont (ℓ c : ℝ) (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (ψ 0 : ℂ) * logSqRat ℓ c s + logSqRem ℓ c ψ s

theorem measurable_logSqAmp (ℓ c : ℝ) {ψ : ℝ → ℝ} (hψ : Measurable ψ) :
    Measurable (logSqAmp ℓ c ψ) := by
  unfold logSqAmp
  refine Complex.measurable_ofReal.comp (Measurable.mul ?_ hψ)
  exact (measurable_const.mul (((measurable_const.add
    (Real.measurable_log.comp (measurable_const.div measurable_id))).pow_const 2))).sub
    measurable_const

/-- The density integrated against the constant `1` on the strip: `2ℓ²/(1−2s) + 4ℓ/(1−2s)² +
4/(1−2s)³ − c/(1−2s)`. -/
theorem logSqMellin_one {ℓ c : ℝ} {s : ℂ} (hs : s.re < 1 / 2) :
    mellinIoc (logSqAmp ℓ c fun _ => 1) s = logSqRat ℓ c s := by
  have hi0 := (integrableOn_mellinIoc (g := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (C := 1) (b := 0) (fun t _ => by simp) (s := s) (by simpa using hs))
  simp only [one_mul] at hi0
  have hi1 := integrableOn_mellinIoc_log (g := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (C := 1) (b := 0) (fun t _ => by simp) (s := s) (by simpa using hs)
  simp only [one_mul] at hi1
  have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-2 * s) * (Real.log (1 / t) : ℂ) ^ 2)
      (Ioc (0 : ℝ) 1) := by
    set δ : ℝ := (1 / 2 - s.re) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have := integrableOn_mellinIoc (g := fun t : ℝ => (Real.log (1 / t) : ℂ) ^ 2)
      ((Complex.measurable_ofReal.comp (Real.measurable_log.comp
        (measurable_const.div measurable_id))).pow_const 2).aestronglyMeasurable
      (C := 1 / δ ^ 2) (b := -2 * δ) (fun t ht => by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, one_div, Real.log_inv, abs_neg]
        have h := abs_log_le_rpow_div hδpos ht
        calc |Real.log t| ^ 2 ≤ (t ^ (-δ) / δ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = 1 / δ ^ 2 * t ^ (-2 * δ) := by
            rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
            push_cast
            ring_nf) (s := s) (by rw [hδ]; linarith)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only
    ring
  unfold mellinIoc
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, logSqAmp ℓ c (fun _ => 1) t * (t : ℂ) ^ (-2 * s) =
      (2 * (ℓ : ℂ) ^ 2 - c) * ((t : ℂ) ^ (-2 * s)) +
        (2 * (ℓ : ℂ)) * ((t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ))) +
        2 * ((t : ℂ) ^ (-2 * s) * (Real.log (1 / t) : ℂ) ^ 2) := by
    intro t _
    unfold logSqAmp
    rw [one_div, Real.log_inv]
    push_cast
    ring
  have hA : IntegrableOn (fun t : ℝ => (2 * (ℓ : ℂ) ^ 2 - c) * ((t : ℂ) ^ (-2 * s)))
      (Ioc (0 : ℝ) 1) := hi0.const_mul _
  have hB : IntegrableOn (fun t : ℝ => (2 * (ℓ : ℂ)) * ((t : ℂ) ^ (-2 * s) *
      (-2 * (Real.log t : ℂ)))) (Ioc (0 : ℝ) 1) := hi1.const_mul _
  have hC : IntegrableOn (fun t : ℝ => 2 * ((t : ℂ) ^ (-2 * s) * (Real.log (1 / t) : ℂ) ^ 2))
      (Ioc (0 : ℝ) 1) := hi2.const_mul _
  have hAB : IntegrableOn (fun t : ℝ => (2 * (ℓ : ℂ) ^ 2 - c) * ((t : ℂ) ^ (-2 * s)) +
      (2 * (ℓ : ℂ)) * ((t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)))) (Ioc (0 : ℝ) 1) := hA.add hB
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hAB hC, integral_add hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_cpow_log_Ioc hs,
    integral_cpow_log_sq_Ioc hs]
  have h0 := mellinIoc_one hs
  unfold mellinIoc at h0
  simp only [one_mul] at h0
  rw [h0]
  unfold logSqRat
  have hne : (1 - 2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

/-- The density is bounded by a power: `|2(ℓ + log(1/t))² − c| ≤ (4ℓ² + |c| + 4/δ²) t^{−2δ}`. -/
theorem abs_logSq_density_le (ℓ c : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) := by
  have ht0 : 0 < t := ht.1
  have hlog := abs_log_le_rpow_div hδ ht
  have hlog' : |Real.log (1 / t)| ≤ t ^ (-δ) / δ := by rwa [one_div, Real.log_inv, abs_neg]
  have hsq : (ℓ + Real.log (1 / t)) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * (t ^ (-δ) / δ) ^ 2 := by
    have h1 : (ℓ + Real.log (1 / t)) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * Real.log (1 / t) ^ 2 := by
      nlinarith [sq_nonneg (ℓ - Real.log (1 / t))]
    have h2 : Real.log (1 / t) ^ 2 ≤ (t ^ (-δ) / δ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hlog' 2
    linarith
  have hpow : (t ^ (-δ) / δ) ^ 2 = t ^ (-2 * δ) / δ ^ 2 := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    push_cast
    ring_nf
  have ht2 : 1 ≤ t ^ (-2 * δ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht.2 (by linarith)
  calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c|
      ≤ |2 * (ℓ + Real.log (1 / t)) ^ 2| + |c| := abs_sub _ _
    _ = 2 * (ℓ + Real.log (1 / t)) ^ 2 + |c| := by rw [abs_of_nonneg (by positivity)]
    _ ≤ 2 * (2 * ℓ ^ 2 + 2 * (t ^ (-2 * δ) / δ ^ 2)) + |c| := by rw [← hpow]; linarith
    _ ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) := by
        have h3 : 4 * ℓ ^ 2 ≤ 4 * ℓ ^ 2 * t ^ (-2 * δ) :=
          le_mul_of_one_le_right (by positivity) ht2
        have h4 : |c| ≤ |c| * t ^ (-2 * δ) := le_mul_of_one_le_right (abs_nonneg _) ht2
        have e : 2 * (2 * ℓ ^ 2 + 2 * (t ^ (-2 * δ) / δ ^ 2)) =
            4 * ℓ ^ 2 + 4 / δ ^ 2 * t ^ (-2 * δ) := by ring
        rw [e]
        nlinarith

/-- The bound on the remainder amplitude: `|(2(ℓ + log(1/t))² − c)(ψ t − ψ 0)| ≤ C t^{1 − 2δ}`. -/
theorem norm_logSqAmp_sub_le (ℓ c : ℝ) {ψ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {δ : ℝ} (hδ : 0 < δ) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqAmp ℓ c (fun t => ψ t - ψ 0) t‖ ≤
      (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * L * t ^ (1 - 2 * δ) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  unfold logSqAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| * |ψ t - ψ 0|
      ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) * (L * t) :=
        mul_le_mul (abs_logSq_density_le ℓ c hδ ht) (hL t ht) (abs_nonneg _) (by positivity)
    _ = (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * L * t ^ (1 - 2 * δ) := by
        rw [show (1 : ℝ) - 2 * δ = -2 * δ + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
        ring

/-- The density against the constant `1` is a Mellin integrand with a power bound. -/
theorem norm_logSqAmp_one_le (ℓ c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqAmp ℓ c (fun _ => 1) t‖ ≤
      (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) := by
  intro t ht
  unfold logSqAmp
  rw [Complex.norm_real, Real.norm_eq_abs, mul_one]
  exact abs_logSq_density_le ℓ c hδ ht

/-- The strip identity: `M[ρ ψ](s) = ψ(0)·logSqRat(s) + R(ψ, s)` on `Re s < ½`. -/
theorem logSqMellin_eq (ℓ c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {s : ℂ} (hs : s.re < 1 / 2) :
    logSqMellin ℓ c ψ s = logSqCont ℓ c ψ s := by
  unfold logSqMellin logSqCont logSqRem
  rw [← logSqMellin_one hs]
  unfold mellinIoc
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, logSqAmp ℓ c ψ t * (t : ℂ) ^ (-2 * s) =
      (ψ 0 : ℂ) * (logSqAmp ℓ c (fun _ => 1) t * (t : ℂ) ^ (-2 * s)) +
        logSqAmp ℓ c (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s) := by
    intro t _
    unfold logSqAmp
    push_cast
    ring
  have hi1 : IntegrableOn (fun t : ℝ => logSqAmp ℓ c (fun _ => 1) t * (t : ℂ) ^ (-2 * s))
      (Ioc (0 : ℝ) 1) := by
    set δ : ℝ := (1 / 2 - s.re) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    exact integrableOn_mellinIoc (measurable_logSqAmp ℓ c measurable_const).aestronglyMeasurable
      (norm_logSqAmp_one_le ℓ c hδpos) (s := s) (by rw [hδ]; linarith)
  have hi2 : IntegrableOn (fun t : ℝ => logSqAmp ℓ c (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mellinIoc (measurable_logSqAmp ℓ c
      (hψ.sub continuous_const).measurable).aestronglyMeasurable
      (norm_logSqAmp_sub_le ℓ c hL (δ := 1 / 4) (by norm_num)) (s := s) (by norm_num; linarith)
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add (hi1.const_mul _) hi2,
    integral_const_mul]

/-- The remainder is holomorphic on `Re s < 1`. -/
theorem differentiableOn_logSqRem (ℓ c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    DifferentiableOn ℂ (logSqRem ℓ c ψ) {s : ℂ | s.re < 1} := by
  intro s hs
  have hs' : s.re < 1 := hs
  set δ : ℝ := (1 - s.re) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hL0 := nonneg_of_bound hL
  exact (hasDerivAt_mellinIoc (measurable_logSqAmp ℓ c
    (hψ.sub continuous_const).measurable).aestronglyMeasurable
    (C := (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * L) (by positivity)
    (norm_logSqAmp_sub_le ℓ c hL hδpos)
    (by rw [hδ]; linarith)).differentiableAt.differentiableWithinAt

/-- The polar data of the density at `½` (powers of `s − ½`): `a₀ = (c − 2ℓ²)ψ₀/2`, `a₁ = ℓψ₀`,
`a₂ = −ψ₀/2`. -/
noncomputable def logSqA (ℓ c : ℝ) (ψ₀ : ℝ) : ℕ → ℂ := fun q =>
  if q = 0 then ((c : ℂ) - 2 * ℓ ^ 2) * ψ₀ / 2
  else if q = 1 then (ℓ : ℂ) * ψ₀
  else if q = 2 then -(ψ₀ : ℂ) / 2 else 0

theorem polarPart_two_apply (a : ℕ → ℂ) (μ s : ℂ) :
    polarPart 2 a μ s = a 0 / (s - μ) + a 1 / (s - μ) ^ 2 + a 2 / (s - μ) ^ 3 := by
  simp [polarPart, Finset.sum_range_succ]

/-- The rational part is exactly its polar part at `½`. -/
theorem logSqRat_eq_polarPart (ℓ c ψ₀ : ℝ) {s : ℂ} (hs : s ≠ 1 / 2) :
    (ψ₀ : ℂ) * logSqRat ℓ c s = polarPart 2 (logSqA ℓ c ψ₀) (1 / 2 : ℂ) s := by
  have h1 : s - 1 / 2 ≠ 0 := sub_ne_zero.2 hs
  have h2 : (1 - 2 * s) ≠ 0 := by
    intro h; apply h1; linear_combination -h / 2
  have e : logSqRat ℓ c s = 2 * (ℓ : ℂ) ^ 2 / ((-2) * (s - 1 / 2)) +
      4 * (ℓ : ℂ) / ((-2) ^ 2 * (s - 1 / 2) ^ 2) + 4 / ((-2) ^ 3 * (s - 1 / 2) ^ 3) -
      (c : ℂ) / ((-2) * (s - 1 / 2)) := by
    unfold logSqRat
    rw [show (1 - 2 * s : ℂ) = (-2) * (s - 1 / 2) by ring, mul_pow, mul_pow]
  rw [e, polarPart_two_apply]
  simp only [logSqA, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  field_simp
  ring

/-- ★★★ **The polar distribution of the `log²` density on `(0,1]`**: principal part
`(c−2ℓ²)ψ₀/2 /(s−½) + ℓψ₀/(s−½)² − ψ₀/2 /(s−½)³`. -/
theorem logSqCont_sub_polarPart_isBigO (ℓ c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    (fun s => logSqCont ℓ c ψ s - polarPart 2 (logSqA ℓ c (ψ 0)) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | z.re < 1} := by
    change (1 / 2 : ℂ).re < 1; norm_num
  have hcont : ContinuousAt (logSqRem ℓ c ψ) (1 / 2) :=
    ((differentiableOn_logSqRem ℓ c hψ hL).differentiableAt
      ((isOpen_re_lt 1).mem_nhds hmem)).continuousAt
  have hO : logSqRem ℓ c ψ =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  beta_reduce
  unfold logSqCont
  rw [logSqRat_eq_polarPart ℓ c (ψ 0) hs]
  ring

theorem logSqCont_polarCoeff_unique (ℓ c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {a : ℕ → ℂ}
    (h : (fun s => logSqCont ℓ c ψ s - polarPart 2 a (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)]
      fun _ => (1 : ℂ)) : ∀ q ≤ 2, a q = logSqA ℓ c (ψ 0) q :=
  polarPart_eq_of_sub_isBigO_one (D := 2) (a := a) (b := logSqA ℓ c (ψ 0)) (μ := 1 / 2)
    (((logSqCont_sub_polarPart_isBigO ℓ c hψ hL).sub h).congr_left fun s => by ring)

/-! ### The full interval `(−M, M)` with the odd term and the cutoff -/

/-- Symmetrisation on `[−M, M]` (even density). -/
theorem integral_symm_M {M : ℝ} (hM : 0 < M) (f : ℝ → ℂ) (φ : ℝ → ℝ)
    (h₁ : IntervalIntegrable (fun t => f t * (φ t : ℂ)) volume 0 M)
    (h₂ : IntervalIntegrable (fun t => f t * (φ (-t) : ℂ)) volume 0 M) :
    IntervalIntegrable (fun t => f |t| * (φ t : ℂ)) volume (-M) M ∧
      ∫ t in (-M)..M, f |t| * (φ t : ℂ) = ∫ t in (0 : ℝ)..M, f t * ((φ t + φ (-t) : ℝ) : ℂ) := by
  have e₁ : ∫ t in (0 : ℝ)..M, f |t| * (φ t : ℂ) = ∫ t in (0 : ℝ)..M, f t * (φ t : ℂ) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hM.le] at ht
      simp [abs_of_nonneg ht.1]
  have e₂ : ∫ t in (0 : ℝ)..M, f t * (φ (-t) : ℂ) = ∫ t in (-M)..0, f |t| * (φ t : ℂ) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := M)
      (f := fun t => f |t| * (φ t : ℂ))
    simp only [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hM.le] at ht
      simp [abs_of_nonneg ht.1]
  have h₂' : IntervalIntegrable (fun t => f |(-t)| * (φ (-t) : ℂ)) volume 0 M := by
    refine h₂.congr fun t ht => ?_
    rw [uIoc_of_le hM.le] at ht
    simp [abs_of_nonneg ht.1.le]
  have h₃ : IntervalIntegrable (fun t => f |t| * (φ t : ℂ)) volume (-M) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (a := 0) (b := M)
      (f := fun t => f |(-t)| * (φ (-t) : ℂ))).1 h₂'
    simp only [neg_neg, neg_zero] at this
    exact this.symm
  have h₄ : IntervalIntegrable (fun t => f |t| * (φ t : ℂ)) volume 0 M := by
    refine h₁.congr fun t ht => ?_
    rw [uIoc_of_le hM.le] at ht
    simp [abs_of_nonneg ht.1.le]
  refine ⟨h₃.trans h₄, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h₃ h₄, e₁, ← e₂,
    ← intervalIntegral.integral_add h₂ h₁]
  exact intervalIntegral.integral_congr fun t _ => by push_cast; ring

/-- Symmetrisation on `[−M, M]` (odd density `sign t`). -/
theorem integral_antisymm_M {M : ℝ} (hM : 0 < M) (f : ℝ → ℂ) (φ : ℝ → ℝ)
    (h₁ : IntervalIntegrable (fun t => f t * (φ t : ℂ)) volume 0 M)
    (h₂ : IntervalIntegrable (fun t => f t * (φ (-t) : ℂ)) volume 0 M) :
    IntervalIntegrable (fun t => f |t| * ((Real.sign t * φ t : ℝ) : ℂ)) volume (-M) M ∧
      ∫ t in (-M)..M, f |t| * ((Real.sign t * φ t : ℝ) : ℂ) =
        ∫ t in (0 : ℝ)..M, f t * ((φ t - φ (-t) : ℝ) : ℂ) := by
  have e₁ : ∫ t in (0 : ℝ)..M, f |t| * ((Real.sign t * φ t : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..M, f t * (φ t : ℂ) :=
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hM.le] at ht
      simp [abs_of_pos ht.1, Real.sign_of_pos ht.1])
  have e₂ : ∫ t in (0 : ℝ)..M, f t * (φ (-t) : ℂ) =
      -∫ t in (-M)..0, f |t| * ((Real.sign t * φ t : ℝ) : ℂ) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := M)
      (f := fun t => f |t| * ((Real.sign t * φ t : ℝ) : ℂ))
    simp only [neg_zero] at this
    rw [← this, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hM.le] at ht
      simp [abs_of_pos ht.1, Real.sign_of_neg (neg_neg_of_pos ht.1)])
  have h₂' : IntervalIntegrable (fun t => f |(-t)| * ((Real.sign (-t) * φ (-t) : ℝ) : ℂ))
      volume 0 M := by
    refine (h₂.neg).congr fun t ht => ?_
    rw [uIoc_of_le hM.le] at ht
    simp [abs_of_pos ht.1, Real.sign_of_neg (neg_neg_of_pos ht.1)]
  have h₃ : IntervalIntegrable (fun t => f |t| * ((Real.sign t * φ t : ℝ) : ℂ)) volume (-M) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (a := 0) (b := M)
      (f := fun t => f |(-t)| * ((Real.sign (-t) * φ (-t) : ℝ) : ℂ))).1 h₂'
    simp only [neg_neg, neg_zero] at this
    exact this.symm
  have h₄ : IntervalIntegrable (fun t => f |t| * ((Real.sign t * φ t : ℝ) : ℂ)) volume 0 M := by
    refine h₁.congr fun t ht => ?_
    rw [uIoc_of_le hM.le] at ht
    simp [abs_of_pos ht.1, Real.sign_of_pos ht.1]
  refine ⟨h₃.trans h₄, ?_⟩
  have h₂n : IntervalIntegrable (fun t => -(f t * (φ (-t) : ℂ))) volume 0 M := h₂.neg
  rw [← intervalIntegral.integral_add_adjacent_intervals h₃ h₄, e₁, ← neg_neg (∫ t in (-M)..0, _),
    ← e₂, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_add h₂n h₁]
  exact intervalIntegral.integral_congr fun t _ => by push_cast; ring

/-- The odd amplitude `b(φ(t) − φ(−t))`. -/
noncomputable def logSqOddAmp (b : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℂ := ((b * (φ t - φ (-t)) : ℝ) : ℂ)

/-- The Mellin transform of the full fibre density on `(−M, M)`. -/
noncomputable def logSqMellinFull (ℓ c b M : ℝ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in (-M)..M, (((2 * (ℓ + Real.log (1 / |t|)) ^ 2 - c + b * Real.sign t) * φ t : ℝ) : ℂ) *
    ((|t| : ℝ) : ℂ) ^ (-2 * s)

/-- The holomorphic part of the continuation: the remainder of the even part, the odd part, and
the two cutoff pieces. -/
noncomputable def logSqHolo (ℓ c b M : ℝ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  logSqRem ℓ c (symmAmp φ) s - mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ))) s +
    (mellinIoc (logSqOddAmp b φ) s - mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ)) s)

/-- A Mellin integrand supported on `[M, 1]`, `M > 0`, is holomorphic on `Re s < 2`. -/
theorem differentiableOn_mellinIoc_cutoff {g : ℝ → ℂ} (hg : Measurable g) {K : ℝ} (hK : 0 ≤ K)
    {M : ℝ} (hM : 0 < M) (hb : ∀ t ∈ Ioc M 1, ‖g t‖ ≤ K) :
    DifferentiableOn ℂ (mellinIoc ((Ioc M 1).indicator g)) {s : ℂ | s.re < 2} := by
  have hmeas : AEStronglyMeasurable ((Ioc M 1).indicator g) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hg.indicator measurableSet_Ioc).aestronglyMeasurable
  have hM3 : 0 < M ^ (3 : ℝ) := Real.rpow_pos_of_pos hM _
  have hb' : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(Ioc M 1).indicator g t‖ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by
    intro t ht
    by_cases hmem : t ∈ Ioc M 1
    · rw [indicator_of_mem hmem]
      have h1 : M ^ (3 : ℝ) ≤ t ^ (3 : ℝ) := Real.rpow_le_rpow hM.le hmem.1.le (by norm_num)
      calc ‖g t‖ ≤ K := hb t hmem
        _ = K / M ^ (3 : ℝ) * M ^ (3 : ℝ) := by field_simp
        _ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by gcongr
    · rw [indicator_of_notMem hmem, norm_zero]
      have : 0 ≤ t ^ (3 : ℝ) := Real.rpow_nonneg ht.1.le _
      positivity
  have := differentiableOn_mellinIoc hmeas (by positivity) hb'
  rwa [show ((3 : ℝ) + 1) / 2 = 2 by norm_num] at this

/-- The cutoff piece is the integral over `(M, 1]`. -/
theorem mellinIoc_indicator (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (s : ℂ) :
    mellinIoc ((Ioc M 1).indicator g) s = ∫ t in Ioc M 1, g t * (t : ℂ) ^ (-2 * s) := by
  unfold mellinIoc
  have e : ∀ t : ℝ, (Ioc M 1).indicator g t * (t : ℂ) ^ (-2 * s) =
      (Ioc M 1).indicator (fun t => g t * (t : ℂ) ^ (-2 * s)) t := fun t => by
    by_cases h : t ∈ Ioc M 1 <;> simp [h]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_eq_right hM, min_self]

/-- The integral over `(0, M]` is the `(0, 1]` integral minus the cutoff piece. -/
theorem integral_Ioc_M_eq (g : ℝ → ℂ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) (s : ℂ)
    (hi : IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (-2 * s)) (Ioc 0 1)) :
    ∫ t in Ioc 0 M, g t * (t : ℂ) ^ (-2 * s) =
      mellinIoc g s - mellinIoc ((Ioc M 1).indicator g) s := by
  rw [mellinIoc_indicator g hM0.le]
  unfold mellinIoc
  rw [← Ioc_union_Ioc_eq_Ioc hM0.le hM1, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
    measurableSet_Ioc (hi.mono_set (Ioc_subset_Ioc_right hM1))
    (hi.mono_set (Ioc_subset_Ioc_left hM0.le))]
  ring

/-- ★★★ **The polar distribution of the naive Bayes fibre density**: for `0 < M ≤ 1` and a
continuous `φ` with `|φ(t) − φ(0)| ≤ L|t|`, the Mellin transform of
`(2 log²(√V/|t|) − c + b sgn t)` on `(−M, M)` (`ℓ = log √V`) equals `2φ(0)·logSqRat(s) + H(s)` on
`Re s < ½` with `H` holomorphic on `Re s < 1`; its principal part at `½` is
`(c − 2ℓ²)φ(0)/(s−½) + 2ℓφ(0)/(s−½)² − φ(0)/(s−½)³`. -/
theorem logSqMellinFull_eq (ℓ c b : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    DifferentiableOn ℂ (logSqHolo ℓ c b M φ) {s : ℂ | s.re < 1} ∧
      ∀ s : ℂ, s.re < 1 / 2 → logSqMellinFull ℓ c b M φ s =
        (2 * φ 0 : ℂ) * logSqRat ℓ c s + logSqHolo ℓ c b M φ s := by
  have hM := bounded_of_bound hL
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (by simpa using hL 1 ⟨by norm_num, le_rfl⟩)
  have hψ := continuous_symmAmp hφ
  have hψL := symmAmp_bound hL
  -- odd amplitude bound
  have hodd : ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ) := by
    intro t ht
    have h1 := hL t ⟨by linarith [ht.1], ht.2⟩
    have h2 := hL (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [abs_of_pos ht.1] at h1
    rw [abs_neg, abs_of_pos ht.1] at h2
    unfold logSqOddAmp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.rpow_one]
    have : |φ t - φ (-t)| ≤ 2 * L * t := by
      calc |φ t - φ (-t)| = |(φ t - φ 0) - (φ (-t) - φ 0)| := by ring_nf
        _ ≤ |φ t - φ 0| + |φ (-t) - φ 0| := abs_sub _ _
        _ ≤ 2 * L * t := by linarith
    calc |b| * |φ t - φ (-t)| ≤ |b| * (2 * L * t) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = 2 * |b| * L * t := by ring
  have hoddm : Measurable (logSqOddAmp b φ) := by
    unfold logSqOddAmp
    exact Complex.measurable_ofReal.comp (measurable_const.mul
      (hφ.measurable.sub (hφ.comp continuous_neg).measurable))
  -- the even amplitude: a power bound on `(0, 1]` and a constant bound on `(M, 1]`
  obtain ⟨Kψ, hKψ0, hKψ⟩ := exists_bound_Icc hψ
  set C₀ : ℝ := 4 * ℓ ^ 2 + |c| + 4 / (1 / 4 : ℝ) ^ 2 with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have heven_pow : ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqAmp ℓ c (symmAmp φ) t‖ ≤
      C₀ * Kψ * t ^ (-2 * (1 / 4 : ℝ)) := by
    intro t ht
    unfold logSqAmp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| * |symmAmp φ t|
        ≤ C₀ * t ^ (-2 * (1 / 4 : ℝ)) * Kψ :=
          mul_le_mul (abs_logSq_density_le ℓ c (by norm_num) ht) (hKψ t ⟨ht.1.le, ht.2⟩)
            (abs_nonneg _) (mul_nonneg hC₀0 (Real.rpow_nonneg ht.1.le _))
      _ = C₀ * Kψ * t ^ (-2 * (1 / 4 : ℝ)) := by ring
  have heven_cut : ∀ t ∈ Ioc M 1, ‖logSqAmp ℓ c (symmAmp φ) t‖ ≤
      C₀ * Kψ * M ^ (-2 * (1 / 4 : ℝ)) := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨lt_trans hM0 ht.1, ht.2⟩
    refine (heven_pow t ht').trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hM0 ht.1.le (by norm_num))
      (by positivity)
  have hevenm : Measurable (logSqAmp ℓ c (symmAmp φ)) := measurable_logSqAmp ℓ c hψ.measurable
  have hodd_cut : ∀ t ∈ Ioc M 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨lt_trans hM0 ht.1, ht.2⟩
    refine (hodd t ht').trans ?_
    rw [Real.rpow_one]
    exact mul_le_of_le_one_right (by positivity) ht.2
  constructor
  · -- holomorphy of the holomorphic part on `Re s < 1`
    have h1 := differentiableOn_logSqRem ℓ c hψ hψL
    have h2 := (differentiableOn_mellinIoc_cutoff hevenm (by positivity) hM0 heven_cut).mono
      (fun s (hs : s.re < 1) => show s.re < 2 by linarith)
    have h3 := differentiableOn_mellinIoc hoddm.aestronglyMeasurable (by positivity) hodd
    rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num] at h3
    have h4 := (differentiableOn_mellinIoc_cutoff hoddm (by positivity) hM0 hodd_cut).mono
      (fun s (hs : s.re < 1) => show s.re < 2 by linarith)
    exact (h1.sub h2).add (h3.sub h4)
  · intro s hs
    -- integrability of the pieces on `(0, 1]`
    set δ : ℝ := (1 / 2 - s.re) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hiE : IntegrableOn (fun t : ℝ => logSqAmp ℓ c (symmAmp φ) t * (t : ℂ) ^ (-2 * s))
        (Ioc (0 : ℝ) 1) := by
      refine integrableOn_mellinIoc hevenm.aestronglyMeasurable
        (C := (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * Kψ) (b := -2 * δ) ?_ (s := s) (by rw [hδ]; linarith)
      intro t ht
      unfold logSqAmp
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| * |symmAmp φ t|
          ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) * Kψ :=
            mul_le_mul (abs_logSq_density_le ℓ c hδpos ht) (hKψ t ⟨ht.1.le, ht.2⟩)
              (abs_nonneg _) (mul_nonneg (by positivity) (Real.rpow_nonneg ht.1.le _))
        _ = (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * Kψ * t ^ (-2 * δ) := by ring
    have hiO : IntegrableOn (fun t : ℝ => logSqOddAmp b φ t * (t : ℂ) ^ (-2 * s))
        (Ioc (0 : ℝ) 1) :=
      integrableOn_mellinIoc hoddm.aestronglyMeasurable hodd (s := s) (by norm_num; linarith)
    -- the two one-sided integrands
    set F : ℝ → ℂ := fun t => ((2 * (ℓ + Real.log (1 / t)) ^ 2 - c : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s)
      with hF
    set F' : ℝ → ℂ := fun t => (b : ℂ) * (t : ℂ) ^ (-2 * s) with hF'
    clear_value F F'
    -- integrability of `F t * φ(±t)` on `[0, M]`
    have hφm : Measurable φ := hφ.measurable
    have hFφ : ∀ χ : ℝ → ℝ, Measurable χ → (∀ t ∈ Icc (0 : ℝ) 1, |χ t| ≤ |φ 0| + L) →
        IntervalIntegrable (fun t => F t * (χ t : ℂ)) volume 0 M := by
      intro χ hχ hχb
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM0.le]
      have hgm : Measurable fun t : ℝ =>
          ((2 * (ℓ + Real.log (1 / t)) ^ 2 - c : ℝ) : ℂ) * (χ t : ℂ) := by
        fun_prop
      have := integrableOn_mellinIoc (g := fun t => ((2 * (ℓ + Real.log (1 / t)) ^ 2 - c : ℝ) : ℂ) *
        (χ t : ℂ)) hgm.aestronglyMeasurable
        (C := (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (|φ 0| + L)) (b := -2 * δ) (fun t ht => by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| * |χ t|
              ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * t ^ (-2 * δ) * (|φ 0| + L) :=
                mul_le_mul (abs_logSq_density_le ℓ c hδpos ht) (hχb t ⟨ht.1.le, ht.2⟩)
                  (abs_nonneg _) (mul_nonneg (by positivity) (Real.rpow_nonneg ht.1.le _))
            _ = (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (|φ 0| + L) * t ^ (-2 * δ) := by ring)
        (s := s) (by rw [hδ]; linarith)
      refine (this.mono_set (Ioc_subset_Ioc_right hM1)).congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [hF]
      ring
    have hF'φ : ∀ χ : ℝ → ℝ, Measurable χ → (∀ t ∈ Icc (0 : ℝ) 1, |χ t| ≤ |φ 0| + L) →
        IntervalIntegrable (fun t => F' t * (χ t : ℂ)) volume 0 M := by
      intro χ hχ hχb
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM0.le]
      have hgm : Measurable fun t : ℝ => (b : ℂ) * (χ t : ℂ) := by fun_prop
      have := integrableOn_mellinIoc (g := fun t => (b : ℂ) * (χ t : ℂ)) hgm.aestronglyMeasurable
        (C := |b| * (|φ 0| + L)) (b := 0) (fun t ht => by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.rpow_zero, mul_one]
          exact mul_le_mul_of_nonneg_left (hχb t ⟨ht.1.le, ht.2⟩) (abs_nonneg _))
        (s := s) (by simpa using hs)
      refine (this.mono_set (Ioc_subset_Ioc_right hM1)).congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [hF']
      ring
    have hφb : ∀ t ∈ Icc (0 : ℝ) 1, |φ t| ≤ |φ 0| + L := fun t ht =>
      hM t ⟨by linarith [ht.1], ht.2⟩
    have hφb' : ∀ t ∈ Icc (0 : ℝ) 1, |φ (-t)| ≤ |φ 0| + L := fun t ht =>
      hM (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨hIe, he⟩ := integral_symm_M hM0 F φ (hFφ φ hφm hφb)
      (hFφ (fun t => φ (-t)) (hφm.comp measurable_neg) hφb')
    obtain ⟨hIo, ho⟩ := integral_antisymm_M hM0 F' φ (hF'φ φ hφm hφb)
      (hF'φ (fun t => φ (-t)) (hφm.comp measurable_neg) hφb')
    -- split the full integrand into the even and odd parts
    have hsplit : logSqMellinFull ℓ c b M φ s =
        (∫ t in (-M)..M, F |t| * (φ t : ℂ)) +
          ∫ t in (-M)..M, F' |t| * ((Real.sign t * φ t : ℝ) : ℂ) := by
      unfold logSqMellinFull
      rw [← intervalIntegral.integral_add hIe hIo]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hF, hF']
      push_cast
      ring
    rw [hsplit, he, ho, intervalIntegral.integral_of_le hM0.le,
      intervalIntegral.integral_of_le hM0.le]
    have he' : ∫ t in Ioc 0 M, F t * ((φ t + φ (-t) : ℝ) : ℂ) =
        ∫ t in Ioc 0 M, logSqAmp ℓ c (symmAmp φ) t * (t : ℂ) ^ (-2 * s) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ => by
        simp only [hF, logSqAmp, symmAmp]
        push_cast
        ring
    have ho' : ∫ t in Ioc 0 M, F' t * ((φ t - φ (-t) : ℝ) : ℂ) =
        ∫ t in Ioc 0 M, logSqOddAmp b φ t * (t : ℂ) ^ (-2 * s) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ => by
        simp only [hF', logSqOddAmp]
        push_cast
        ring
    rw [he', ho', integral_Ioc_M_eq _ hM0 hM1 s hiE, integral_Ioc_M_eq _ hM0 hM1 s hiO]
    have hstrip := logSqMellin_eq ℓ c hψ hψL hs
    unfold logSqMellin logSqCont at hstrip
    rw [hstrip, symmAmp_zero]
    unfold logSqHolo
    push_cast
    ring

/-- ★★★ **The polar distributions of the naive Bayes fibre density**: the continuation
`2φ(0)·logSqRat + H` of the Mellin transform on `(−M, M)` has the principal part
`(c − 2ℓ²)φ(0)/(s−½) + 2ℓφ(0)/(s−½)² − φ(0)/(s−½)³` at `½`: `C_{½,3} = −δ₀`, `C_{½,2} = 2ℓδ₀`,
`C_{½,1} = (c − 2ℓ²)δ₀`, with `ℓ = log √V`; the odd term and the cutoff contribute nothing. -/
theorem logSqMellinFull_polar (ℓ c b : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    (fun s => (2 * φ 0 : ℂ) * logSqRat ℓ c s + logSqHolo ℓ c b M φ s -
      polarPart 2 (logSqA ℓ c (2 * φ 0)) (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | z.re < 1} := by
    change (1 / 2 : ℂ).re < 1; norm_num
  have hcont : ContinuousAt (logSqHolo ℓ c b M φ) (1 / 2) :=
    (((logSqMellinFull_eq ℓ c b hM0 hM1 hφ hL).1.differentiableAt
      ((isOpen_re_lt 1).mem_nhds hmem))).continuousAt
  have hO : logSqHolo ℓ c b M φ =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  beta_reduce
  have := logSqRat_eq_polarPart ℓ c (2 * φ 0) hs
  push_cast at this
  rw [← this]
  ring

end Grammar
