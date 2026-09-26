/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaRegularization
import Grammar.PrincipalPartUniqueness

/-!
# Chart zeta polar functionals (unit 5)

At a real point `μ` the face sum `chartZetaAtDepth p F h k` (unit 4) is a finite sum of terms
`faceW · innerFactor · chartZeta (faceAmp)`, and each inner factor is a product of the simple
rational functions `1/(mᵢ + hᵢ + 1 − 2kᵢ s)` over `i ∈ J`.  The coordinates with
`mᵢ + hᵢ + 1 = 2kᵢ μ` are *resonant* at `μ`; they contribute the pole `(μ − s)^{−c}` of order
`c = c(J, m, μ)` (the number of resonant coordinates) times the constant `∏_res (2kᵢ)⁻¹`, and the
remaining factors together with the complementary chart zeta function form a function
`faceHolo` holomorphic near `μ`.

The polar coefficients `chartPolarCoeff p F h k μ q` (the coefficient of `(s − μ)^{−(q+1)}`) are
the Taylor coefficients of the holomorphic factors, summed over the faces whose pole order
exceeds `q`, and the main theorem `chartZetaAtDepth_sub_polarPart_isBigO_one` states that
`chartZetaAtDepth − polarPart D (chartPolarCoeff …) μ = O(1)` on a punctured neighbourhood of
`μ`, which is the form consumed by the uniqueness theorem `polarCoeff_unique` of
`PrincipalPartUniqueness`.  The Taylor remainder bound for holomorphic functions
(`taylor_remainder_isBigO`) is derived from Mathlib's power-series remainder
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow` and the identification
`HasFPowerSeriesOnBall.factorial_smul` of the coefficients with iterated derivatives.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Taylor remainders of holomorphic functions -/

section Taylor

/-- Taylor remainder bound: a function holomorphic on a neighbourhood of `c` agrees with its
degree-`< n` Taylor polynomial at `c` up to `O(‖s − c‖^n)`. -/
theorem taylor_remainder_isBigO {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k)
      =O[𝓝 c] fun s => ‖s - c‖ ^ n := by
  obtain ⟨P, r, H⟩ := hf.analyticAt hU
  have hB := H.hasFPowerSeriesAt.isBigO_sub_partialSum_pow n
  have hpart : ∀ y : ℂ, P.partialSum n y =
      ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * y ^ k := by
    intro y
    unfold FormalMultilinearSeries.partialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := H.factorial_smul y k
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h1
    simp only [Finset.prod_const, Finset.card_fin, smul_eq_mul, nsmul_eq_mul] at h1
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    set A := (P k) fun _ => y
    set B := iteratedDeriv k f c
    clear_value A B
    field_simp
    linear_combination h1
  have hT : Tendsto (fun s : ℂ => s - c) (𝓝 c) (𝓝 0) := by
    have := (continuous_id.sub continuous_const).tendsto c (f := fun s : ℂ => s - c)
    simpa using this
  refine (hB.comp_tendsto hT).congr' ?_ ?_
  · filter_upwards with s
    simp [Function.comp, hpart]
  · filter_upwards with s
    rfl

/-- The principal part of `(c − s)^{−n} f(s)` at `c` for `f` holomorphic near `c`: the
coefficient of `(s − c)^{−(q+1)}` is `(−1)^n f^{(n−1−q)}(c)/(n−1−q)!`, and the difference is
bounded on a punctured neighbourhood of `c`. -/
theorem pole_taylor_isBigO_one {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => (c - s)⁻¹ ^ n * f s - ∑ q ∈ range n,
      (-1) ^ n * iteratedDeriv (n - 1 - q) f c / ((n - 1 - q)! : ℂ) / (s - c) ^ (q + 1))
      =O[𝓝[≠] c] fun _ => (1 : ℂ) := by
  obtain ⟨C, hC⟩ := (taylor_remainder_isBigO hU hf n).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsc
  have hsc' : s - c ≠ 0 := sub_ne_zero.2 hsc
  have hid : (c - s)⁻¹ ^ n * f s - ∑ q ∈ range n,
      (-1) ^ n * iteratedDeriv (n - 1 - q) f c / ((n - 1 - q)! : ℂ) / (s - c) ^ (q + 1) =
      (c - s)⁻¹ ^ n *
        (f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k) := by
    rw [mul_sub, Finset.mul_sum, ← Finset.sum_range_reflect
      (fun k => (c - s)⁻¹ ^ n * ((k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k)) n]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < n := Finset.mem_range.1 hq
    have hpow : (s - c) ^ n = (s - c) ^ (n - 1 - q) * (s - c) ^ (q + 1) := by
      rw [← pow_add]; congr 1; omega
    have hcs : c - s = -(s - c) := by ring
    rw [hcs, inv_neg, neg_pow (s - c)⁻¹, inv_pow, hpow]
    field_simp
  rw [hid, norm_mul, norm_pow, norm_inv, norm_sub_rev, norm_one, mul_one]
  calc ‖s - c‖⁻¹ ^ n * ‖f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k‖
      ≤ ‖s - c‖⁻¹ ^ n * (C * ‖‖s - c‖ ^ n‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = C := by
        have h0 : ‖s - c‖ ≠ 0 := norm_ne_zero_iff.2 hsc'
        rw [Real.norm_of_nonneg (by positivity), inv_pow, inv_mul_eq_div, mul_div_assoc,
          div_self (pow_ne_zero n h0), mul_one]

end Taylor

/-! ### Resonant coordinates and the factorisation of the inner factor -/

section Faces

variable {d : ℕ}

/-- The resonant coordinates of the face `(J, m)` at `μ`: `i ∈ J` with `mᵢ + hᵢ + 1 = 2kᵢ μ`. -/
noncomputable def faceResSet (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    Finset (Fin d) :=
  J.filter fun i => ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

theorem mem_faceResSet {h k : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ} {μ : ℝ}
    {i : Fin d} :
    i ∈ faceResSet h k J m μ ↔ i ∈ J ∧ ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ :=
  Finset.mem_filter

theorem faceResSet_subset (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    faceResSet h k J m μ ⊆ J :=
  Finset.filter_subset _ _

/-- The pole order `c(J, m, μ)` of the face `(J, m)` at `μ`. -/
noncomputable def poleOrder (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ℕ :=
  (faceResSet h k J m μ).card

theorem poleOrder_le_card (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ J.card :=
  Finset.card_le_card (faceResSet_subset h k J m μ)

theorem poleOrder_le (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ d :=
  (poleOrder_le_card h k J m μ).trans (by simpa using Finset.card_le_univ J)

/-- The resonant constant `∏_{i resonant} (2kᵢ)⁻¹`. -/
noncomputable def resConst (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ℂ :=
  ∏ i ∈ faceResSet h k J m μ, (2 * ((k i : ℕ) : ℂ))⁻¹

/-- The non-resonant part of the inner factor, holomorphic near `μ`. -/
noncomputable def regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    (μ : ℝ) (s : ℂ) : ℂ :=
  ∏ i ∈ J \ faceResSet h k J m μ, 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1)

/-- A resonant denominator is `2kᵢ (μ − s)`. -/
theorem denom_eq_of_mem_faceResSet {h k : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ}
    {μ : ℝ} {i : Fin d} (hi : i ∈ faceResSet h k J m μ) (s : ℂ) :
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 = 2 * ((k i : ℕ) : ℂ) * ((μ : ℂ) - s) := by
  have hres := (mem_faceResSet.1 hi).2
  have hC : ((m i : ℂ) + (h i : ℂ) + 1) = 2 * ((k i : ℕ) : ℂ) * (μ : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hres
    push_cast at this
    exact this
  push_cast
  linear_combination hC

/-- ★ **Factorisation of the inner factor at `μ`**:
`innerFactor = (∏_res (2kᵢ)⁻¹) · (μ − s)^{−c} · regularFactor`, valid for every `s`. -/
theorem innerFactor_eq_res (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ)
    (s : ℂ) :
    innerFactor h k J m s =
      resConst h k J m μ * ((μ : ℂ) - s)⁻¹ ^ poleOrder h k J m μ * regularFactor h k J m μ s := by
  unfold innerFactor resConst regularFactor poleOrder
  have e : (∏ i : {i // inJ J i},
      1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) =
      ∏ i ∈ J, 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1) :=
    (Finset.prod_subtype J (p := fun i => inJ J i) (fun _ => Iff.rfl)
      (fun i => 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1))).symm
  rw [e, ← Finset.prod_sdiff (faceResSet_subset h k J m μ), mul_comm]
  congr 1
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [denom_eq_of_mem_faceResSet hi s, one_div, mul_inv]

/-- The regular factor is holomorphic wherever its denominators do not vanish. -/
theorem differentiableOn_regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    (μ : ℝ) {U : Set ℂ}
    (hU : ∀ s ∈ U, ∀ i ∈ J \ faceResSet h k J m μ,
      ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0) :
    DifferentiableOn ℂ (regularFactor h k J m μ) U := by
  unfold regularFactor
  refine differentiableOn_finset_prod' _ fun i hi => ?_
  refine (differentiableOn_const _).div ?_ fun s hs => hU s hs i hi
  exact ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).add
    (differentiableOn_const _)

/-- The set on which the face `(J, m)` is regular at depth `p`: the flat strip minus the
zeros of the non-resonant denominators. -/
def faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) : Set ℂ :=
  {s | FlatStrip p h k s ∧ ∀ i ∈ J \ faceResSet h k J m μ,
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0}

theorem isOpen_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    IsOpen (faceRegSet p h k J m μ) := by
  have : faceRegSet p h k J m μ = {s | FlatStrip p h k s} ∩
      ⋂ i ∈ J \ faceResSet h k J m μ,
        {s : ℂ | ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0} := by
    ext s; simp [faceRegSet]
  rw [this]
  refine (FlatStrip.isOpen p h k).inter (isOpen_biInter_finset fun i _ => ?_)
  exact isOpen_ne_fun (((continuous_const).sub (continuous_const.mul continuous_id)).add
    continuous_const) continuous_const

/-- `μ` itself lies in the regular set once it lies in the flat strip. -/
theorem mem_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : (μ : ℂ) ∈ faceRegSet p h k J m μ := by
  refine ⟨hμ, fun i hi hden => ?_⟩
  have hi' := Finset.mem_sdiff.1 hi
  apply hi'.2
  refine mem_faceResSet.2 ⟨hi'.1, ?_⟩
  have := congrArg Complex.re hden
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.zero_re, mul_zero, sub_zero, zero_mul] at this
  push_cast at this ⊢
  linarith

theorem faceRegSet_mem_nhds (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : faceRegSet p h k J m μ ∈ 𝓝 (μ : ℂ) :=
  (isOpen_faceRegSet p h k J m μ).mem_nhds (mem_faceRegSet p h k J m hμ)

/-- The holomorphic factor of the face `(J, m)` at `μ`: the regular factor times the
complementary chart zeta function of the face amplitude. -/
noncomputable def faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) (s : ℂ) : ℂ :=
  regularFactor h k J m μ s *
    chartZeta (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s

theorem differentiableOn_faceHolo (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) :
    DifferentiableOn ℂ (faceHolo p F h k J m μ) (faceRegSet p h k J m μ) := by
  obtain ⟨C, hC, hflat⟩ := flatOn_faceAmp p J hF hp0 hm
  refine DifferentiableOn.mul ?_ ?_
  · exact differentiableOn_regularFactor h k J m μ fun s hs => hs.2
  · exact (differentiableOn_chartZeta_flat (continuous_faceAmp p J hF m).continuousOn hC
      hflat _ _).mono fun s hs => flatStrip_subtype J hs.1

/-- The face sum at depth `p`, with every inner factor factorised at `μ`. -/
theorem chartZetaAtDepth_eq_faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (s : ℂ) :
    chartZetaAtDepth p F h k s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s) := by
  unfold chartZetaAtDepth faceHolo
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [innerFactor_eq_res h k x.1 x.2 μ s]
  ring

end Faces

/-! ### The polar coefficients and the principal part -/

section Polar

variable {d : ℕ}

/-- ★ **The chart polar coefficients at `μ`.**  `chartPolarCoeff p F h k μ q` is the coefficient
of `(s − μ)^{−(q+1)}` in the face sum at depth `p`: over the faces of pole order `c ≥ q + 1`, the
face weight times the resonant constant times `(−1)^c` times the Taylor coefficient of order
`c − 1 − q` of the holomorphic factor at `μ`. -/
noncomputable def chartPolarCoeff (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℂ :=
  ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ poleOrder h k x.1 x.2 μ),
    ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
      ((-1) ^ poleOrder h k x.1 x.2 μ *
        iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
          ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ))

/-- The polar coefficients vanish beyond the maximal pole order. -/
theorem chartPolarCoeff_eq_zero (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) {q : ℕ} (hq : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ < q + 1) :
    chartPolarCoeff p F h k μ q = 0 := by
  unfold chartPolarCoeff
  rw [Finset.filter_false_of_mem fun x hx => not_le.2 (hq x hx)]
  simp

/-- `μ` is a candidate pole at depth `p` iff some face has positive pole order. -/
theorem poleAt_iff_poleOrder (p h k : Fin d → ℕ) (μ : ℝ) :
    PoleAt p h k (μ : ℂ) ↔ ∃ x ∈ SmoothEngine.faceIndex p, 0 < poleOrder h k x.1 x.2 μ := by
  unfold PoleAt poleOrder
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi, hden⟩
    refine ⟨i, mem_faceResSet.2 ⟨hi, ?_⟩⟩
    have := congrArg Complex.re hden
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.mul_re,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re, mul_zero, sub_zero, zero_mul] at this
    push_cast at this ⊢
    linarith
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_faceResSet.1 hi).1, by
      rw [denom_eq_of_mem_faceResSet hi]; simp⟩

theorem chartPolarCoeff_eq_zero_of_not_poleAt (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ)
    (h k : Fin d → ℕ) {μ : ℝ} (hμ : ¬ PoleAt p h k (μ : ℂ)) (q : ℕ) :
    chartPolarCoeff p F h k μ q = 0 := by
  refine chartPolarCoeff_eq_zero p F h k μ fun x hx => ?_
  rw [poleAt_iff_poleOrder] at hμ
  push Not at hμ
  have := hμ x hx
  omega

/-- The principal part of one face, in the form produced by `pole_taylor_isBigO_one`. -/
theorem face_sub_principal_isBigO_one (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) :
    (fun s : ℂ => ((μ : ℂ) - s)⁻¹ ^ poleOrder h k J m μ * faceHolo p F h k J m μ s -
      ∑ q ∈ range (poleOrder h k J m μ),
        (-1) ^ poleOrder h k J m μ *
          iteratedDeriv (poleOrder h k J m μ - 1 - q) (faceHolo p F h k J m μ) μ /
            ((poleOrder h k J m μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1))
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  pole_taylor_isBigO_one (faceRegSet_mem_nhds p h k J m hμ)
    (differentiableOn_faceHolo p hF h k hp0 J hm μ) _

/-- Rearrangement of the principal part `polarPart D (chartPolarCoeff …) μ` as a sum over
faces, for `D + 1` at least every pole order. -/
theorem polarPart_chartPolarCoeff_eq (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) (s : ℂ) :
    polarPart D (chartPolarCoeff p F h k μ) μ s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
          (-1) ^ poleOrder h k x.1 x.2 μ *
            iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
              ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1) := by
  unfold polarPart chartPolarCoeff
  simp_rw [Finset.sum_div, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hrange : (range (D + 1)).filter (fun q => q + 1 ≤ poleOrder h k x.1 x.2 μ) =
      range (poleOrder h k x.1 x.2 μ) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hD x hx
    omega
  rw [hrange]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- ★★ **The face sum minus its principal part is bounded near `μ`.**  For `F` smooth, at a
positive depth `p` whose flat strip contains `μ`, and for `D + 1` at least every pole order at
`μ`, `chartZetaAtDepth p F h k − polarPart D (chartPolarCoeff p F h k μ) μ = O(1)` on a
punctured neighbourhood of `μ`.  This is the input form of `polarCoeff_unique`. -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart D (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have hrw : ∀ s : ℂ, chartZetaAtDepth p F h k s - polarPart D (chartPolarCoeff p F h k μ) μ s =
      ∑ x ∈ SmoothEngine.faceIndex p,
        ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
          (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s -
            ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
              (-1) ^ poleOrder h k x.1 x.2 μ *
                iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
                  ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1)) := by
    intro s
    rw [chartZetaAtDepth_eq_faceHolo p F h k μ s, polarPart_chartPolarCoeff_eq p F h k μ hD s,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have key : (∑ x ∈ SmoothEngine.faceIndex p, fun s : ℂ =>
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s -
          ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
            (-1) ^ poleOrder h k x.1 x.2 μ *
              iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
                ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1)))
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
    IsBigO.sum fun x hx => (face_sub_principal_isBigO_one p hF h k hp0 hμ x.1
      (Finset.mem_sigma.1 hx).2).const_mul_left _
  refine key.congr_left fun s => ?_
  rw [Finset.sum_apply, hrw]

/-- The same with the universal degree bound `D = d` (every pole order is at most `d`). -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one' (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart d (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  chartZetaAtDepth_sub_polarPart_isBigO_one p hF h k hp0 hμ fun x _ =>
    (poleOrder_le h k x.1 x.2 μ).trans (Nat.le_succ d)

/-- Away from the candidate poles the face sum is itself bounded near `μ`. -/
theorem chartZetaAtDepth_isBigO_one_of_not_poleAt (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) (hpole : ¬ PoleAt p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s) =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have := chartZetaAtDepth_sub_polarPart_isBigO_one' p hF h k hp0 hμ
  have hz : ∀ s : ℂ, polarPart d (chartPolarCoeff p F h k μ) μ s = 0 := fun s => by
    unfold polarPart
    simp [chartPolarCoeff_eq_zero_of_not_poleAt p F h k hpole]
  simpa [hz] using this

end Polar

/-! ### The canonical depth -/

section Depth

variable {d : ℕ}

/-- At the depth `depthOf h k L` with `L ≥ L₀ h`, every real `μ < L` lies in the flat strip. -/
theorem flatStrip_depthOf {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) : FlatStrip (depthOf h k L) h k (μ : ℂ) := by
  intro i
  have hadd : ((depthOf h k L i : ℕ) : ℝ) + h i = 2 * k i * L := by
    exact_mod_cast depthOf_add hk hL i
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  rw [Complex.ofReal_re, hadd]
  nlinarith

/-- ★ The principal part of the face sum at the canonical depth `depthOf h k L`, for any real
`μ < L` (no candidate-pole hypothesis: the polar coefficients vanish when `μ` is not a pole). -/
theorem chartZetaAtDepth_depthOf_sub_polarPart_isBigO_one {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) :
    (fun s : ℂ => chartZetaAtDepth (depthOf h k L) F h k s -
      polarPart d (chartPolarCoeff (depthOf h k L) F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  chartZetaAtDepth_sub_polarPart_isBigO_one' _ hF h k (depthOf_pos hk hL)
    (flatStrip_depthOf hk hL hμ)

end Depth

end Grammar
