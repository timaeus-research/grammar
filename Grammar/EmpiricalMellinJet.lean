/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldFamilyJets
import Grammar.EmpiricalInnerTwoRegime
import Grammar.Smooth

/-!
# The Mellin–jet bridge: Mellin moments of the field jets are jets of `η · S_μ(ζ)`
(§20 unit 2 of consult #142)

The zeroth Mellin moment of a jet family `H τ v` in the coupling `τ` is the *Mellin field*
`mellinField H μ v = ∫₀^∞ s^{μ−1} e^{−s} H(√s, v) ds`. For the field family
`B_τ = η e^{τζ}` it is `η · S_μ(ζ)` with `S_μ` the fluctuation function (`mellinField_fieldFam`;
more generally `mellinMom (τ^r e^{aτ}) μ 0 = S_{μ+r/2}(a)`, ★ `mellinMom_pow_mul_exp_zero` — the
ladder: a `τ^r` factor shifts the `S`-index by `r/2`, not the exponent). Coordinate derivatives
commute with the Mellin integral on jet families (★ `pd_mellinField_isJet`, differentiation under
the integral dominated by the jet bound on a compact neighbourhood), hence
★★ `mellinMom_pdMulti_fieldFam_zero`:
`∫₀^∞ s^{μ−1} e^{−s} ∂^m_v[η e^{√s ζ}](v) ds = ∂^m_v[η(v) S_μ(ζ(v))]` for every multi-index —
the Mellin moments of the field jets are the jets of `η · S_μ(ζ)`. This is the mechanism behind
"the coefficients involve derivatives of the fluctuation functions". Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The zeroth Mellin moment -/

theorem mellinMom_zero_eq (G : ℝ → ℝ) (μ : ℝ) :
    mellinMom G μ 0 = ∫ s in Ioi (0 : ℝ), s ^ (μ - 1) * exp (-s) * G (Real.sqrt s) := by
  unfold mellinMom momKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [pow_zero, mul_one]
  ring

/-- ★ **The ladder**: `∫₀^∞ s^{μ−1} e^{−s} (√s)^r e^{a√s} ds = S_{μ+r/2}(a)`. -/
theorem mellinMom_pow_mul_exp_zero {μ a : ℝ} (r : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ 0 = fluctuation 1 (μ + r / 2) a := by
  rw [mellinMom_zero_eq]
  unfold fluctuation
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have h1 : Real.sqrt s ^ r = s ^ ((r : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    congr 1
    ring
  have h2 : s ^ (μ + r / 2 - 1) = s ^ (μ - 1) * s ^ ((r : ℝ) / 2) := by
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  have h3 : exp (-1 * s + 1 * a * Real.sqrt s) = exp (-s) * exp (a * Real.sqrt s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, h3]
  ring

theorem mellinMom_exp_zero {μ a : ℝ} :
    mellinMom (fun τ => exp (a * τ)) μ 0 = fluctuation 1 μ a := by
  have := mellinMom_pow_mul_exp_zero (μ := μ) (a := a) 0
  simpa using this

/-! ### The Mellin field of a jet family -/

/-- The Mellin field `v ↦ ∫₀^∞ s^{μ−1} e^{−s} H(√s, v) ds` of a coupling family. -/
noncomputable def mellinField (H : ℝ → (Fin d → ℝ) → ℝ) (μ : ℝ) (v : Fin d → ℝ) : ℝ :=
  mellinMom (fun τ => H τ v) μ 0

variable {η ζ : (Fin d → ℝ) → ℝ}

/-- The Mellin field of the field family is `η · S_μ(ζ)`. -/
theorem mellinField_fieldFam (μ : ℝ) :
    mellinField (fieldFam η ζ) μ = fun v => η v * fluctuation 1 μ (ζ v) := by
  funext v
  unfold mellinField fieldFam
  rw [mellinMom_zero_eq, ← mellinMom_exp_zero (μ := μ) (a := ζ v), mellinMom_zero_eq,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [mul_comm (Real.sqrt s) (ζ v)]
  ring

theorem pd_update_eq_deriv_line (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) (x : ℝ) :
    pd i G (Function.update v i x) = deriv (line G i v) x := by
  unfold pd
  rw [line_update, Function.update_self]

/-- ★ **Differentiation under the Mellin integral** on a jet family: `∂ᵢ` of the Mellin field is
the Mellin field of `∂ᵢ H`. -/
theorem pd_mellinField_isJet (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ}
    (h : IsJet ζ R H) {μ : ℝ} (hμ : 0 < μ) (i : Fin d) (v : Fin d → ℝ) :
    pd i (mellinField H μ) v = mellinField (fun τ => pd i (H τ)) μ v := by
  -- the compact neighbourhood `K = ∏ [vⱼ−1, vⱼ+1]`
  set K : Set (Fin d → ℝ) := Set.pi univ fun j => Icc (v j - 1) (v j + 1) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M', hM'⟩ := hKc.exists_bound_of_continuousOn hζ.continuous.continuousOn
  have hζM : ∀ w ∈ K, |ζ w| ≤ M' := fun w hw => by simpa [Real.norm_eq_abs] using hM' w hw
  obtain ⟨C₀, hC₀0, hC₀⟩ := h.bound_of_isCompact hKc hζM
  obtain ⟨C, hC0, hC⟩ := (h.pd hζ i).bound_of_isCompact hKc hζM
  have hmem : ∀ x ∈ Icc (v i - 1) (v i + 1), Function.update v i x ∈ K := by
    intro x hx j _
    by_cases hj : j = i
    · subst hj; simpa using hx
    · simp only [Function.update_of_ne hj]
      exact ⟨by linarith, by linarith⟩
  have hvK : v ∈ K := fun j _ => ⟨by linarith, by linarith⟩
  -- the integrands
  set F : ℝ → ℝ → ℝ := fun x s => s ^ (μ - 1) * exp (-s) * H (Real.sqrt s) (Function.update v i x)
    with hF
  set F' : ℝ → ℝ → ℝ := fun x s =>
    s ^ (μ - 1) * exp (-s) * deriv (line (H (Real.sqrt s)) i v) x with hF'
  have hFmeas : ∀ x, Measurable (F x) := fun x => by
    have hc : Continuous fun s : ℝ => H (Real.sqrt s) (Function.update v i x) :=
      (h.continuous_left _).comp Real.continuous_sqrt
    exact ((measurable_id.pow_const _).mul measurable_id.neg.exp).mul hc.measurable
  have hF'meas : Measurable (F' (v i)) := by
    have hc : Continuous fun s : ℝ => deriv (line (H (Real.sqrt s)) i v) (v i) := by
      have : (fun s : ℝ => deriv (line (H (Real.sqrt s)) i v) (v i)) =
          fun s => pd i (H (Real.sqrt s)) v := by
        funext s
        rw [← pd_update_eq_deriv_line, Function.update_eq_self]
      rw [this]
      exact ((h.pd hζ i).continuous_left v).comp Real.continuous_sqrt
    exact ((measurable_id.pow_const _).mul measurable_id.neg.exp).mul hc.measurable
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := v i) (s := Icc (v i - 1) (v i + 1))
    (bound := fun s => C * (s ^ (μ - 1) * |log s| ^ 0 *
      ((1 + Real.sqrt s) ^ (R + 1) * exp (M' * Real.sqrt s) * exp (-s))))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x => (hFmeas x).aestronglyMeasurable) ?_
    hF'meas.aestronglyMeasurable ?_ ((integrableOn_envelope (R + 1) M' hμ 0).const_mul C) ?_
  · -- assemble
    have hline : line (mellinField H μ) i v = fun x => ∫ s in Ioi (0 : ℝ), F x s := by
      funext x
      unfold line mellinField
      rw [mellinMom_zero_eq]
    unfold pd
    rw [hline, hkey.2.deriv]
    unfold mellinField
    rw [mellinMom_zero_eq]
  · -- integrability of `F (v i)`
    refine ((integrableOn_envelope R M' hμ 0).const_mul C₀).mono'
      (hFmeas (v i)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    have hp : 0 ≤ s ^ (μ - 1) := Real.rpow_nonneg hs0.le _
    have hb := hC₀ (Real.sqrt s) hsq v hvK
    simp only [hF, Function.update_eq_self]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (exp_pos _), pow_zero,
      mul_one]
    calc s ^ (μ - 1) * exp (-s) * |H (Real.sqrt s) v|
        ≤ s ^ (μ - 1) * exp (-s) * (C₀ * (1 + Real.sqrt s) ^ R * exp (M' * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · -- the derivative bound
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs x hx => ?_)
    have hs0 : 0 < s := hs
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    have hp : 0 ≤ s ^ (μ - 1) := Real.rpow_nonneg hs0.le _
    have hb := hC (Real.sqrt s) hsq _ (hmem x hx)
    simp only [hF']
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (exp_pos _),
      ← pd_update_eq_deriv_line, pow_zero, mul_one]
    calc s ^ (μ - 1) * exp (-s) * |pd i (H (Real.sqrt s)) (Function.update v i x)|
        ≤ s ^ (μ - 1) * exp (-s) * (C * (1 + Real.sqrt s) ^ (R + 1) * exp (M' * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · -- the pointwise derivative
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ x _ => ?_)
    simp only [hF, hF']
    exact (hasDerivAt_line (h.contDiff hζ (Real.sqrt s)) i v x).const_mul _

theorem pdPow_mellinField_isJet (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ}
    (h : IsJet ζ R H) {μ : ℝ} (hμ : 0 < μ) (i : Fin d) (n : ℕ) :
    pdPow i n (mellinField H μ) = mellinField (fun τ => pdPow i n (H τ)) μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdPow_succ', ih]
    funext v
    have := pd_mellinField_isJet hζ (h.pdPow hζ i n) hμ i v
    rw [this]
    simp only [pdPow_succ']

/-- ★★ Coordinate derivatives commute with the Mellin integral on jet families. -/
theorem pdMulti_mellinField_isJet (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ}
    (h : IsJet ζ R H) {μ : ℝ} (hμ : 0 < μ) (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (mellinField H μ) = mellinField (fun τ => pdMulti m l (H τ)) μ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, ih]
    have := pdPow_mellinField_isJet hζ (h.pdMulti hζ m l) hμ i (m i)
    rw [this]
    simp only [pdMulti_cons]

/-- ★★ **The Mellin moments of the field jets are the jets of `η · S_μ(ζ)`**:
`∫₀^∞ s^{μ−1} e^{−s} ∂^m_v[η e^{√s ζ}](v) ds = ∂^m_v[η(v) S_μ(ζ(v))]`. -/
theorem mellinMom_pdMulti_fieldFam_zero (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ}
    (hμ : 0 < μ) (m : Fin d → ℕ) (l : List (Fin d)) (v : Fin d → ℝ) :
    mellinMom (fun τ => pdMulti m l (fieldFam η ζ τ) v) μ 0 =
      pdMulti m l (fun v => η v * fluctuation 1 μ (ζ v)) v := by
  have h := congrFun (pdMulti_mellinField_isJet hζ (isJet_fieldFam hη) hμ m l) v
  rw [mellinField_fieldFam] at h
  exact h.symm

/-- The jets of `η · S_μ(ζ)` are smooth (they are Mellin fields of jets). -/
theorem contDiff_mul_fluctuation (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ} (hμ : 0 < μ) :
    ContDiff ℝ ∞ fun v => η v * fluctuation 1 μ (ζ v) :=
  hη.mul ((contDiff_fluctuation 1 μ one_pos hμ).comp hζ)

end SmoothEngine

end Grammar
