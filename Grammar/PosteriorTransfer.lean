/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LogRatioSymmetricMoments
import Grammar.FaceCoefficient

/-!
# Abstract posterior transfer

Unit 1 of consult #79 (`tide-log/gpt6_bigpicture_v79.md`): the leading-term certificates of two
integrals transfer to their ratio. With `HasLeadingTerm Z c λ k` meaning
`Z N / (N^{−λ} log^k N) → c`:

* a positive coefficient gives eventual positivity of `Z` (`HasLeadingTerm.eventually_pos`), a
  nonzero one eventual nonvanishing (`eventually_ne_zero`);
* at a common pair, `Z₁/Z₂ → c₁/c₂` whenever `c₂ ≠ 0` — the numerator coefficient may vanish
  (`tendsto_div_same_pair`);
* a numerator at a dominated pair gives `Z₁/Z₂ → 0` (`tendsto_div_zero_of_dominated`); a numerator
  with coefficient zero gives `Z₁/Z₂ = o(s₁/s₂)` at the scale ratio (`isLittleO_div_ratio`), and a
  nonzero one the relative equivalent `Z₁/Z₂ ~ (c₁/c₂)·(s₁/s₂)` (`div_isEquivalent`);
* **the posterior expectation** `E_N[φ] := Z_N[φ] / Z_N[1]` (totalised division; eventually the
  genuine normalised expectation once `Z_N[1] > 0`) of the resolved Boltzmann integral
  (`ResolutionCover.posteriorExpectation`): linearity of `Z_N[·]` in the observable
  (`boltzmannIntegral_add`, `boltzmannIntegral_const_mul`, `boltzmannIntegral_const`) and of the
  certificates (`hasLeadingTerm_boltzmannIntegral_add`, `_const_mul`), constant observables
  (`posteriorExpectation_const`), and the transfer theorem
  `tendsto_posteriorExpectation_of_hasLeadingTerm`: certificates of `Z_N[φ]` and `Z_N[1]` at a
  common pair with `c₁ > 0` give `Z_N[1] > 0` eventually and `E_N[φ] → c_φ / c₁`; a dominated
  observable has `E_N[φ] → 0` (`tendsto_posteriorExpectation_zero_of_dominated`).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

section Transfer

variable {Z Z₁ Z₂ : ℝ → ℝ} {c c₁ c₂ lam lam₁ lam₂ : ℝ} {k k₁ k₂ : ℕ}

/-- A positive leading coefficient makes the integral eventually positive. -/
theorem HasLeadingTerm.eventually_pos (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    ∀ᶠ N in atTop, 0 < Z N := by
  filter_upwards [h.eventually (eventually_gt_nhds hc), eventually_gt_atTop 1] with N hN hN1
  exact (div_pos_iff_of_pos_right (powLogScale_pos lam k hN1)).1 hN

/-- A nonzero leading coefficient makes the integral eventually nonzero. -/
theorem HasLeadingTerm.eventually_ne_zero (h : HasLeadingTerm Z c lam k) (hc : c ≠ 0) :
    ∀ᶠ N in atTop, Z N ≠ 0 := by
  filter_upwards [h.eventually (eventually_ne_nhds hc)] with N hN
  exact fun h0 => hN (by rw [h0, zero_div])

/-- **Same-pair ratio limit**: `Z₁/Z₂ → c₁/c₂` when both have certificates at the same pair and
`c₂ ≠ 0` (the numerator coefficient may be zero). -/
theorem HasLeadingTerm.tendsto_div_same_pair (h₁ : HasLeadingTerm Z₁ c₁ lam k)
    (h₂ : HasLeadingTerm Z₂ c₂ lam k) (hc₂ : c₂ ≠ 0) :
    Tendsto (fun N => Z₁ N / Z₂ N) atTop (𝓝 (c₁ / c₂)) := by
  refine (h₁.tendsto_div_ratio h₂ hc₂).congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  rw [div_self (powLogScale_pos lam k hN).ne', div_one]

/-- **Dominated numerator**: a certificate of `Z₁` at a pair dominated by that of `Z₂` gives
`Z₁/Z₂ → 0`. -/
theorem HasLeadingTerm.tendsto_div_zero_of_dominated (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) (hd : PairDominates lam₂ k₂ lam₁ k₁) :
    Tendsto (fun N => Z₁ N / Z₂ N) atTop (𝓝 0) := by
  have h := (h₁.of_dominated hd).tendsto_div_same_pair h₂ hc₂
  rwa [zero_div] at h

/-- **Vanishing numerator coefficient**: `Z₁/Z₂ = o(s₁/s₂)` at the ratio of scales. -/
theorem HasLeadingTerm.isLittleO_div_ratio (h₁ : HasLeadingTerm Z₁ 0 lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
    (fun N => Z₁ N / Z₂ N) =o[atTop]
      fun N => powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N := by
  have h := h₁.tendsto_div_ratio h₂ hc₂
  rw [zero_div] at h
  exact (isLittleO_iff_tendsto' ((eventually_gt_atTop 1).mono fun N hN h0 =>
    absurd h0 (div_pos (powLogScale_pos _ _ hN) (powLogScale_pos _ _ hN)).ne')).2 h

/-- **Relative equivalent**: with `c₁, c₂ ≠ 0`, `Z₁/Z₂ ~ (c₁/c₂)·(s₁/s₂)`. -/
theorem HasLeadingTerm.div_isEquivalent (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
    (fun N => Z₁ N / Z₂ N) ~[atTop]
      fun N => c₁ / c₂ * (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N) := by
  have hv : ∀ᶠ N in atTop,
      c₁ / c₂ * (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N) ≠ 0 :=
    (eventually_gt_atTop 1).mono fun N hN => mul_ne_zero (div_ne_zero hc₁ hc₂)
      (div_pos (powLogScale_pos _ _ hN) (powLogScale_pos _ _ hN)).ne'
  refine (isEquivalent_iff_tendsto_one hv).2 ?_
  have h := (h₁.tendsto_div_ratio h₂ hc₂).div_const (c₁ / c₂)
  rw [div_self (div_ne_zero hc₁ hc₂)] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only [Pi.div_apply]
  rw [div_div, mul_comm (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N)]

end Transfer

/-! ### The posterior expectation of the resolved Boltzmann integral -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- `Z_N[F]` as a set integral over the union of the chart images. -/
theorem boltzmannIntegral_eq (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    R.boltzmannIntegral F K p N =
      ∫ x in ⋃ i, R.image i, F x * p.w x * Real.exp (-N * K x) := rfl

theorem boltzmannIntegral_const_mul (a : ℝ) (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    R.boltzmannIntegral (fun x => a * F x) K p N = a * R.boltzmannIntegral F K p N := by
  rw [boltzmannIntegral_eq, boltzmannIntegral_eq, ← integral_const_mul]
  congr 1
  funext x
  ring

theorem boltzmannIntegral_const (a : ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    R.boltzmannIntegral (fun _ => a) K p N = a * R.boltzmannIntegral (fun _ => 1) K p N := by
  rw [boltzmannIntegral_eq, boltzmannIntegral_eq, ← integral_const_mul]
  congr 1
  funext x
  ring

theorem boltzmannIntegral_add {F G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hG : Integrable (fun x => G x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    R.boltzmannIntegral (fun x => F x + G x) K p N =
      R.boltzmannIntegral F K p N + R.boltzmannIntegral G K p N := by
  rw [boltzmannIntegral_eq, boltzmannIntegral_eq, boltzmannIntegral_eq,
    ← integral_add (R.integrable_boltzmann hF hK hK0 hN) (R.integrable_boltzmann hG hK hK0 hN)]
  congr 1
  funext x
  ring

/-- Certificates are additive in the observable. -/
theorem hasLeadingTerm_boltzmannIntegral_add {F G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hG : Integrable (fun x => G x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {c₁ c₂ lam : ℝ} {k : ℕ}
    (h₁ : HasLeadingTerm (R.boltzmannIntegral F K p) c₁ lam k)
    (h₂ : HasLeadingTerm (R.boltzmannIntegral G K p) c₂ lam k) :
    HasLeadingTerm (R.boltzmannIntegral (fun x => F x + G x) K p) (c₁ + c₂) lam k :=
  (h₁.add h₂).congr' ((eventually_ge_atTop 0).mono fun _ hN =>
    (R.boltzmannIntegral_add hF hG hK hK0 hN).symm)

/-- Certificates are homogeneous in the observable. -/
theorem hasLeadingTerm_boltzmannIntegral_const_mul {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (a : ℝ) {c lam : ℝ} {k : ℕ} (h : HasLeadingTerm (R.boltzmannIntegral F K p) c lam k) :
    HasLeadingTerm (R.boltzmannIntegral (fun x => a * F x) K p) (a * c) lam k :=
  (h.const_mul a).congr' (Eventually.of_forall fun N =>
    (R.boltzmannIntegral_const_mul a F K p N).symm)

/-- **The posterior expectation** of the observable `φ` at sample size `N`:
`E_N[φ] = Z_N[φ] / Z_N[1]` (totalised division; the genuine normalised expectation once
`Z_N[1] ≠ 0`). -/
noncomputable def posteriorExpectation (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (φ : (Fin d → ℝ) → ℝ) (N : ℝ) : ℝ :=
  R.boltzmannIntegral φ K p N / R.boltzmannIntegral (fun _ => 1) K p N

theorem posteriorExpectation_const (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (a : ℝ) {N : ℝ}
    (hN : R.boltzmannIntegral (fun _ => 1) K p N ≠ 0) :
    R.posteriorExpectation K p (fun _ => a) N = a := by
  unfold posteriorExpectation
  rw [boltzmannIntegral_const, mul_div_assoc, div_self hN, mul_one]

/-- **The transfer theorem**: certificates of `Z_N[φ]` and `Z_N[1]` at a common pair with a
positive normalising coefficient give an eventually positive normaliser and
`E_N[φ] → c_φ / c₁`. -/
theorem tendsto_posteriorExpectation_of_hasLeadingTerm {K φ : (Fin d → ℝ) → ℝ}
    {p : TubeWeight d} {cφ c₁ lam : ℝ} {k : ℕ}
    (hφ : HasLeadingTerm (R.boltzmannIntegral φ K p) cφ lam k)
    (h₁ : HasLeadingTerm (R.boltzmannIntegral (fun _ => 1) K p) c₁ lam k) (hc₁ : 0 < c₁) :
    (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p φ) atTop (𝓝 (cφ / c₁)) :=
  ⟨h₁.eventually_pos hc₁, hφ.tendsto_div_same_pair h₁ hc₁.ne'⟩

/-- **A dominated observable has vanishing posterior expectation.** -/
theorem tendsto_posteriorExpectation_zero_of_dominated {K φ : (Fin d → ℝ) → ℝ}
    {p : TubeWeight d} {cφ c₁ lam lam₁ : ℝ} {k k₁ : ℕ}
    (hφ : HasLeadingTerm (R.boltzmannIntegral φ K p) cφ lam k)
    (h₁ : HasLeadingTerm (R.boltzmannIntegral (fun _ => 1) K p) c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
    (hd : PairDominates lam₁ k₁ lam k) :
    Tendsto (R.posteriorExpectation K p φ) atTop (𝓝 0) :=
  hφ.tendsto_div_zero_of_dominated h₁ hc₁ hd

end ResolutionCover

end Grammar
