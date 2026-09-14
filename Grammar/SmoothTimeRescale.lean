/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral

/-!
# The smooth-amplitude expansion: rescaling the phase unit (consult #117 §3)

The phase scale `β` of the smooth-amplitude integral is a TIME rescaling: exactly
`smoothIntegral F h k β b N = smoothIntegral F h k 1 b (β N)` (`smoothIntegral_beta_eq`). On the
coefficient side, `(βN)^{−μ} log(βN)^j = β^{−μ} N^{−μ} (log β + log N)^j` expands by the binomial
theorem into the **coefficient rescaling operator**
`scaleCoeff D β c μ q = β^{−μ} ∑_{j=q}^{D} c μ j (j choose q) (log β)^{j−q}`, and
`absSpectralSum_mul_pos` shows the spectral sum of `c` at `βN` is the spectral sum of
`scaleCoeff D β c` at `N`. Hence ★ `CutoffExpansion.comp_mul_pos`: a cutoff expansion of `Z`
transports to one of `N ↦ Z (βN)` with coefficients `scaleCoeff D β c`, on the same lattice and
with the same logarithmic degree (the constant picks up `β^{−L} (1 + |log β|)^D`).

Combined with the zero-support of the canonical smooth coefficients off the lattice
(`smoothCoeff_eq_zero_of_not_lattice`) and above the degree (`smoothCoeff_eq_zero_of_degree_gt`),
canonicity (`CutoffExpansion.coeff_unique`) gives ★★ `smoothCoeff_beta_eq_scaleCoeff`: for EVERY
`μ` and `q`, `smoothCoeff F h k β b μ q = scaleCoeff (d − 1) β (smoothCoeff F h k 1 b) μ q`. So
the `β`-dependence of the whole smooth engine is the explicit algebraic operator `scaleCoeff`
applied to the unit-phase coefficients — no uniformity in `β` of the underlying bounds is needed.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Time rescaling of the integral -/

/-- The phase scale is a time rescaling: `Z_β(N) = Z_1(βN)`. -/
theorem smoothIntegral_beta_eq (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b N : ℝ) :
    smoothIntegral F h k β b N = smoothIntegral F h k 1 b (β * N) := by
  unfold smoothIntegral
  refine setIntegral_congr_fun (measurableSet_box b) fun v _ => ?_
  have : -(N * β) = -(β * N * 1) := by ring
  rw [this]

/-! ### The coefficient rescaling operator -/

/-- The coefficient rescaling operator:
`scaleCoeff D β c μ q = β^{−μ} ∑_{j=q}^{D} c μ j (j choose q) (log β)^{j−q}`. -/
noncomputable def scaleCoeff (D : ℕ) (β : ℝ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  β ^ (-μ) * ∑ j ∈ Finset.Ico q (D + 1), c μ j * (j.choose q) * Real.log β ^ (j - q)

theorem scaleCoeff_eq_zero_of_not_lattice {Q D : ℕ} {β : ℝ} {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Q) (q : ℕ) : scaleCoeff D β c μ q = 0 := by
  unfold scaleCoeff
  rw [Finset.sum_eq_zero fun j _ => by rw [hc μ hμ j, zero_mul, zero_mul], mul_zero]

theorem scaleCoeff_eq_zero_of_degree_gt {D : ℕ} {β : ℝ} {c : ℝ → ℕ → ℝ} {μ : ℝ} {q : ℕ}
    (hq : D < q) : scaleCoeff D β c μ q = 0 := by
  unfold scaleCoeff
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, mul_zero]

/-- The spectral sum of `c` at `βN` is the spectral sum of `scaleCoeff D β c` at `N`. -/
theorem absSpectralSum_mul_pos {Q D : ℕ} (c : ℝ → ℕ → ℝ) (L : ℝ) {β N : ℝ} (hβ : 0 < β)
    (hN : 0 < N) :
    absSpectralSum Q D c L (β * N) = absSpectralSum Q D (scaleCoeff D β c) L N := by
  unfold absSpectralSum scaleCoeff
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Real.mul_rpow hβ.le hN.le, Real.log_mul hβ.ne' hN.ne']
  have key : β ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * (log β + log N) ^ j =
      ∑ q ∈ Finset.range (D + 1),
        (β ^ (-μ) * ∑ j ∈ Finset.Ico q (D + 1), c μ j * (j.choose q) * log β ^ (j - q)) *
          log N ^ q := by
    simp only [add_comm (log β) (log N), add_pow, Finset.mul_sum]
    rw [sum_triangle D fun j q =>
      β ^ (-μ) * (c μ j * (log N ^ q * log β ^ (j - q) * (j.choose q : ℝ)))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← key]
  ring

/-- ★ **Transport of a cutoff expansion under time rescaling**: if `Z` has the cutoff expansion
`c`, then `N ↦ Z (βN)` has the cutoff expansion `scaleCoeff D β c`, on the same lattice and with
the same logarithmic degree. -/
theorem CutoffExpansion.comp_mul_pos {Q D : ℕ} {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) {β : ℝ} (hβ : 0 < β) :
    CutoffExpansion Q D (fun N => Z (β * N)) (scaleCoeff D β c) := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨|K| * β ^ (-L) * (1 + |log β|) ^ D, ?_⟩
  have hev : ∀ᶠ N : ℝ in atTop, |Z (β * N) - absSpectralSum Q D c L (β * N)| ≤
      K * ((β * N) ^ (-L) * (1 + log (β * N)) ^ D) :=
    ((tendsto_const_mul_atTop_of_pos hβ).2 tendsto_id).eventually hK
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop β⁻¹] with N hN hN1 hN2
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
  have hβN : 1 ≤ β * N := by
    have := mul_le_mul_of_nonneg_left hN2 hβ.le
    rwa [mul_inv_cancel₀ hβ.ne'] at this
  have hlog : 0 ≤ log β + log N := by
    have := Real.log_nonneg hβN
    rwa [Real.log_mul hβ.ne' hNpos.ne'] at this
  have hlogN := Real.log_nonneg hN1
  rw [absSpectralSum_mul_pos c L hβ hNpos] at hN
  refine hN.trans ?_
  rw [Real.mul_rpow hβ.le hNpos.le, Real.log_mul hβ.ne' hNpos.ne']
  have hb1 : 1 + (log β + log N) ≤ (1 + |log β|) * (1 + log N) := by
    nlinarith [le_abs_self (log β), abs_nonneg (log β), mul_nonneg (abs_nonneg (log β)) hlogN]
  have hpow : (1 + (log β + log N)) ^ D ≤ ((1 + |log β|) * (1 + log N)) ^ D :=
    pow_le_pow_left₀ (by linarith) hb1 D
  have hβL := Real.rpow_pos_of_pos hβ (-L)
  have hNL := Real.rpow_pos_of_pos hNpos (-L)
  calc K * (β ^ (-L) * N ^ (-L) * (1 + (log β + log N)) ^ D)
      ≤ |K| * (β ^ (-L) * N ^ (-L) * ((1 + |log β|) * (1 + log N)) ^ D) :=
        mul_le_mul (le_abs_self K) (mul_le_mul_of_nonneg_left hpow (mul_pos hβL hNL).le)
          (mul_nonneg (mul_pos hβL hNL).le (pow_nonneg (by linarith) D)) (abs_nonneg K)
    _ = |K| * β ^ (-L) * (1 + |log β|) ^ D * (N ^ (-L) * (1 + log N) ^ D) := by
        rw [mul_pow]; ring

/-! ### Zero-support of the canonical smooth coefficients -/

variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}

/-- The face coefficients vanish off the ambient lattice `Q⁻¹ℕ`. -/
theorem faceCoef_eq_zero_of_not_lattice (J : Finset (Fin d)) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) (e : Fin d → ℕ) {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) (j : ℕ) :
    faceCoef k β b J e μ j = 0 := by
  unfold faceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    refine faceMonoCoeff_eq_zero_of_not_lattice (ι := {i // inJ J i}) (fun i => k i) (fun i => e i)
      (fun i => hk i) hβ hb (fun m hm => ?_) j
    have hm' : μ = (m : ℝ) / (QJ k J : ℕ) := hm
    obtain ⟨r, hr⟩ := QJ_dvd_Qamb k J
    have hr0 : (r : ℝ) ≠ 0 := by
      refine Nat.cast_ne_zero.2 fun h0 => ?_
      rw [h0, mul_zero] at hr
      exact absurd hr (Qamb_pos k hk).ne'
    apply hμ (m * r)
    rw [hm', hr]
    push_cast
    rw [mul_div_mul_right _ _ hr0]
  · rfl

/-- The canonical smooth coefficients vanish off the ambient lattice `Q⁻¹ℕ`. -/
theorem smoothCoeff_eq_zero_of_not_lattice (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) (q : ℕ) : smoothCoeff F h k β b μ q = 0 := by
  unfold smoothCoeff smoothCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
  rw [faceCoef_eq_zero_of_not_lattice x.1 hk hβ hb _ hμ j, zero_mul, zero_mul]

/-- The canonical smooth coefficients vanish above the logarithmic degree `d − 1`. -/
theorem smoothCoeff_eq_zero_of_degree_gt {μ : ℝ} {q : ℕ} (hq : d - 1 < q) :
    smoothCoeff F h k β b μ q = 0 := by
  unfold smoothCoeff smoothCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.Ico_eq_empty_of_le (by have := DJ_le x.1; omega), Finset.sum_empty, mul_zero]

/-! ### The rescaling identity for the canonical coefficients -/

/-- ★★ **The phase scale acts on the canonical smooth coefficients by `scaleCoeff`**: for every
`μ` and `q`, `smoothCoeff F h k β b μ q = scaleCoeff (d − 1) β (smoothCoeff F h k 1 b) μ q`. -/
theorem smoothCoeff_beta_eq_scaleCoeff (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff F h k β b μ q = scaleCoeff (d - 1) β (smoothCoeff F h k 1 b) μ q := by
  have hQ := Qamb_pos k hk
  have h1 : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b)
      (scaleCoeff (d - 1) β (smoothCoeff F h k 1 b)) := by
    have hexp := CutoffExpansion.comp_mul_pos (smooth_cutoffExpansion hF hk one_pos hb (h := h)) hβ
    have hfun : (fun N => smoothIntegral F h k 1 b (β * N)) = smoothIntegral F h k β b :=
      funext fun N => (smoothIntegral_beta_eq F h k β b N).symm
    rwa [hfun] at hexp
  by_cases hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · by_cases hq : q ≤ d - 1
    · exact CutoffExpansion.coeff_unique hQ (smooth_cutoffExpansion hF hk hβ hb) h1 hμ hq
    · have hq' := not_le.1 hq
      rw [smoothCoeff_eq_zero_of_degree_gt hq', scaleCoeff_eq_zero_of_degree_gt hq']
  · have hμ' : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k := fun m hm => hμ ⟨m, hm⟩
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ' q,
      scaleCoeff_eq_zero_of_not_lattice (Q := Qamb k)
        (fun ν hν j => smoothCoeff_eq_zero_of_not_lattice hk one_pos hb hν j) hμ' q]

end SmoothEngine

end Grammar
