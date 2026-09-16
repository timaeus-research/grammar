/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.WickSeries

/-!
# Jets of powers: the deterministic bound and Bochner integrability from moments (§20, item 6)

The Wick theorem `integral_empCoeff_gaussian_wick` assumes Bochner integrability of every cube jet
`cubeJet R 1 (η (u^k ζ_o)^r)`.  Here this is reduced to finite moments of the jet norm of the
field itself:

* `norm_iteratedFDeriv_pow_le_of_forall_le`: `‖∂^n (Y^r)(x)‖ ≤ r^n M^r` when `‖∂^i Y(x)‖ ≤ M`
  for `i ≤ n` (Leibniz and the binomial theorem, induction on `r`);
* ★ `norm_cubeJet_mul_pow_le`: `‖J_R(η Y^r)‖ ≤ ‖J_R η‖ (r+1)^R ‖J_R Y‖^r` on any cube;
* ★★ `integrable_cubeJet_mul_pow_of_moment`: the jet of `η Y_o^r` is Bochner integrable as soon
  as it is strongly measurable and `E ‖J_R Y_o‖^r < ∞`;
* ★★★ `integral_empCoeff_gaussian_wick_of_moments`: the Wick series under measurability of the
  jets and finite moments of all jet norms `E ‖J_R (u^k ζ_o)‖^r < ∞` (in place of `hint`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ContDiff NNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-- Leibniz for powers: `‖∂^n (Y^r)(x)‖ ≤ r^n M^r` when all derivatives of `Y` at `x` up to
order `n` are bounded by `M`. -/
theorem norm_iteratedFDeriv_pow_le_of_forall_le {Y : (Fin d → ℝ) → ℝ} (hY : ContDiff ℝ ∞ Y)
    {x : Fin d → ℝ} {M : ℝ} (hM : 0 ≤ M) (r : ℕ) :
    ∀ n : ℕ, (∀ i ≤ n, ‖iteratedFDeriv ℝ i Y x‖ ≤ M) →
      ‖iteratedFDeriv ℝ n (fun v => Y v ^ r) x‖ ≤ (r : ℝ) ^ n * M ^ r := by
  induction r with
  | zero =>
    intro n _
    simp only [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [show (fun _ : Fin d → ℝ => (1 : ℝ)) = fun _ => (1 : ℝ) from rfl,
        iteratedFDeriv_const_of_ne hn.ne' (1 : ℝ)]
      simp [zero_pow hn.ne']
  | succ r ih =>
    intro n hn
    have hmul : (fun v => Y v ^ (r + 1)) = fun v => Y v * Y v ^ r := by
      funext v
      ring
    rw [hmul]
    have h1 := norm_iteratedFDeriv_mul_le hY (hY.pow r) x (n := n) (natCast_le_infty _)
    refine h1.trans ?_
    have hterm : ∀ i ∈ range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i Y x‖ * ‖iteratedFDeriv ℝ (n - i) (fun v => Y v ^ r) x‖
          ≤ (n.choose i : ℝ) * M * ((r : ℝ) ^ (n - i) * M ^ r) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hA := hn i hi'
      have hB := ih (n - i) fun j hj => hn j (hj.trans (Nat.sub_le n i))
      have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA hc) hB (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    have hbin := add_pow (1 : ℝ) (r : ℝ) n
    rw [show ((r + 1 : ℕ) : ℝ) = 1 + (r : ℝ) by push_cast; ring, hbin, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [one_pow, pow_succ]
    ring

/-- Leibniz for `η Y^r`: `‖∂^n (η Y^r)(x)‖ ≤ Mη (r+1)^n M^r`. -/
theorem norm_iteratedFDeriv_mul_pow_le_of_forall_le {η Y : (Fin d → ℝ) → ℝ}
    (hη : ContDiff ℝ ∞ η) (hY : ContDiff ℝ ∞ Y) {x : Fin d → ℝ} {Mη M : ℝ} (hMη : 0 ≤ Mη)
    (hM : 0 ≤ M) (r n : ℕ) (hnη : ∀ i ≤ n, ‖iteratedFDeriv ℝ i η x‖ ≤ Mη)
    (hn : ∀ i ≤ n, ‖iteratedFDeriv ℝ i Y x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun v => η v * Y v ^ r) x‖ ≤ Mη * ((r + 1 : ℝ) ^ n * M ^ r) := by
  have h1 := norm_iteratedFDeriv_mul_le hη (hY.pow r) x (n := n) (natCast_le_infty _)
  refine h1.trans ?_
  have hterm : ∀ i ∈ range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ * ‖iteratedFDeriv ℝ (n - i) (fun v => Y v ^ r) x‖
        ≤ (n.choose i : ℝ) * Mη * ((r : ℝ) ^ (n - i) * M ^ r) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hA := hnη i hi'
    have hB := norm_iteratedFDeriv_pow_le_of_forall_le hY hM r (n - i)
      fun j hj => hn j (hj.trans (Nat.sub_le n i))
    have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA hc) hB (norm_nonneg _) (by positivity)
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  have hbin := add_pow (1 : ℝ) (r : ℝ) n
  rw [show (r + 1 : ℝ) = 1 + (r : ℝ) by ring, hbin, sum_mul, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [one_pow]
  ring

/-- All derivatives of a smooth function on the cube up to order `R` are bounded by its jet
norm. -/
theorem norm_iteratedFDeriv_le_norm_cubeJet_of_le {Y : (Fin d → ℝ) → ℝ} (hY : ContDiff ℝ ∞ Y)
    {R : ℕ} {b : ℝ} {x : Fin d → ℝ} (hx : x ∈ closedBox d b) :
    ∀ i ≤ R, ‖iteratedFDeriv ℝ i Y x‖ ≤ ‖cubeJet R b Y hY‖ :=
  fun _ hi => norm_iteratedFDeriv_le_norm_cubeJet hY hi hx

/-- ★ **The jet of `η Y^r` is polynomially bounded by the jets of `η` and `Y`**:
`‖J_R(η Y^r)‖ ≤ ‖J_R η‖ (r+1)^R ‖J_R Y‖^r`. -/
theorem norm_cubeJet_mul_pow_le {η Y : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hY : ContDiff ℝ ∞ Y) (R : ℕ) (b : ℝ) (r : ℕ) :
    ‖cubeJet R b (fun v => η v * Y v ^ r) (hη.mul (hY.pow r))‖ ≤
      ‖cubeJet R b η hη‖ * ((r + 1 : ℝ) ^ R * ‖cubeJet R b Y hY‖ ^ r) := by
  have hMη : 0 ≤ ‖cubeJet R b η hη‖ := norm_nonneg _
  have hM : 0 ≤ ‖cubeJet R b Y hY‖ := norm_nonneg _
  have hC : 0 ≤ ‖cubeJet R b η hη‖ * ((r + 1 : ℝ) ^ R * ‖cubeJet R b Y hY‖ ^ r) := by positivity
  change ‖(cubeJet R b (fun v => η v * Y v ^ r) (hη.mul (hY.pow r))).toPi‖ ≤ _
  rw [pi_norm_le_iff_of_nonneg hC]
  intro n
  rw [ContinuousMap.norm_le _ hC]
  intro x
  have hn : n.1 ≤ R := Nat.lt_succ_iff.1 n.2
  calc ‖(cubeJet R b (fun v => η v * Y v ^ r) (hη.mul (hY.pow r))).toPi n x‖
      = ‖iteratedFDeriv ℝ n.1 (fun v => η v * Y v ^ r) x.1‖ := rfl
    _ ≤ ‖cubeJet R b η hη‖ * ((r + 1 : ℝ) ^ n.1 * ‖cubeJet R b Y hY‖ ^ r) :=
        norm_iteratedFDeriv_mul_pow_le_of_forall_le hη hY hMη hM r n.1
          (fun i hi => norm_iteratedFDeriv_le_norm_cubeJet hη (hi.trans hn) x.2)
          (fun i hi => norm_iteratedFDeriv_le_norm_cubeJet hY (hi.trans hn) x.2)
    _ ≤ ‖cubeJet R b η hη‖ * ((r + 1 : ℝ) ^ R * ‖cubeJet R b Y hY‖ ^ r) := by
        gcongr
        linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- ★★ **Bochner integrability of the jet of `η Y_o^r` from a moment of the jet norm**: a strongly
measurable jet with `E ‖J_R Y_o‖^r < ∞` is Bochner integrable in the jet space. -/
theorem integrable_cubeJet_mul_pow_of_moment {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    {Y : Ω → (Fin d → ℝ) → ℝ} (hY : ∀ o, ContDiff ℝ ∞ (Y o)) {R : ℕ} {b : ℝ} {r : ℕ}
    (hmeas : AEStronglyMeasurable
      (fun o => cubeJet R b (fun v => η v * Y o v ^ r) (hη.mul ((hY o).pow r))) P)
    (hmom : Integrable (fun o => ‖cubeJet R b (Y o) (hY o)‖ ^ r) P) :
    Integrable (fun o => cubeJet R b (fun v => η v * Y o v ^ r) (hη.mul ((hY o).pow r))) P := by
  refine Integrable.mono' (hmom.const_mul (‖cubeJet R b η hη‖ * (r + 1 : ℝ) ^ R)) hmeas
    (Eventually.of_forall fun o => ?_)
  calc ‖cubeJet R b (fun v => η v * Y o v ^ r) (hη.mul ((hY o).pow r))‖
      ≤ ‖cubeJet R b η hη‖ * ((r + 1 : ℝ) ^ R * ‖cubeJet R b (Y o) (hY o)‖ ^ r) :=
        norm_cubeJet_mul_pow_le hη (hY o) R b r
    _ = ‖cubeJet R b η hη‖ * (r + 1 : ℝ) ^ R * ‖cubeJet R b (Y o) (hY o)‖ ^ r := by ring

variable [IsProbabilityMeasure P] {h k : Fin d → ℕ}

/-- ★★★ **The Wick series under finite moments of the jet norms**: `hint` of
`integral_empCoeff_gaussian_wick` is replaced by strong measurability of the jets of
`η (u^k ζ_o)^r` and `E ‖J_R (u^k ζ_o)‖^r < ∞` for all `r, R`. -/
theorem integral_empCoeff_gaussian_wick_of_moments (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1)
    {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {ζ : Ω → (Fin d → ℝ) → ℝ}
    (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {W : (Fin d → ℝ) → ℝ} (hW : ContDiff ℝ ∞ W)
    (hW0 : ∀ x, 0 ≤ W x)
    (hlaw : ∀ x ∈ closedBox d 1,
      HasLaw (fun o => mono k x * ζ o x) (gaussianReal 0 ⟨W x, hW0 x⟩) P)
    (hmeas : ∀ r R : ℕ, AEStronglyMeasurable
      (fun o => cubeJet R 1 (fun v => η v * (mono k v * ζ o v) ^ r)
        (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) P)
    (hmom : ∀ r R : ℕ, Integrable
      (fun o => ‖cubeJet R 1 (fun v => mono k v * ζ o v) ((contDiff_mono k).mul (hζ o))‖ ^ r) P)
    (habs : Summable fun r : ℕ => ∫ o, |(1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P) :
    Integrable (fun o => empCoeff η (ζ o) h k μ q) P ∧
    ∫ o, empCoeff η (ζ o) h k μ q ∂P = ∑' j : ℕ, (1 / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q :=
  integral_empCoeff_gaussian_wick hk hμ hq hη hζ hW hW0 hlaw
    (fun r R => integrable_cubeJet_mul_pow_of_moment hη
      (fun o => (contDiff_mono k).mul (hζ o)) (hmeas r R) (hmom r R)) habs

end Grammar
