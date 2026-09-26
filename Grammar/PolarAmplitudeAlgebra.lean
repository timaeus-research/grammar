/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PrincipalPartUniqueness

/-!
# The polar amplitude algebra (polar-distribution programme, unit 1)

Consult #167 (`tide-log/gpt6_bigpicture_v167.md`, `plan_polar_distribution.md`). Let
`T(s) = Σ_{r=1}^{M} A_r/(μ−s)^r + H(s)` be a meromorphic pairing with polar functionals `A_r`
and let `g(s)` be an amplitude holomorphic in `s` near `μ`, with Taylor coefficients
`g_ℓ = ∂_s^ℓ g(μ)/ℓ!`. Writing `a j ℓ := A_{j+1}[∂_s^ℓ g(μ)]`, the polar part of `T(s)[g(s)]` at `μ`
is, in the library's convention `polarPart D a μ s = Σ_q a q/(s−μ)^{q+1}`, the array

  `polarAmplitudeCoeff D a q = Σ_{j ∈ [q, D]} (−1)^{j+1} a j (j−q)/(j−q)!`,

and the corresponding asymptotic coefficient (`polarCoeff c μ q = (−1)^{q+1} q! c_{μ,q}`) is

  `logAmplitudeCoeff D a q = (1/q!) Σ_{j ∈ [q, D]} (−1)^{j−q} a j (j−q)/(j−q)!`

(formula (*) of the plan). This unit isolates every sign, factorial and finite-sum identity
before any analysis: `polarAmplitudeCoeff_eq` relates the two arrays, and
`polarAmplitudeSum_sub_polarPart` is the exact identity

  `Σ_j P_j(s)/(μ−s)^{j+1} − polarPart D (polarAmplitudeCoeff D a) μ s
     = Σ_j Σ_{ℓ > j} (−1)^{j+1} a j ℓ (s−μ)^{ℓ−j−1}/ℓ!`   (`s ≠ μ`),

whose right side is a polynomial in `s`, with `P_j(s) = Σ_{ℓ ≤ D} a j ℓ (s−μ)^ℓ/ℓ!`. The
real-data coercion `polarAmplitudeCoeff_ofReal` identifies the array with `polarCoeff` of the
real coefficient system `logAmplitudeCoeffReal`. Zero `sorry`/`axiom`.
-/

open Finset

namespace Grammar

/-- The polar array `Σ_{j ∈ [q,D]} (−1)^{j+1} a j (j−q)/(j−q)!` of an amplitude family. -/
noncomputable def polarAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ j ∈ Ico q (D + 1), (-1 : ℂ) ^ (j + 1) * a j (j - q) / ((j - q).factorial : ℂ)

/-- The asymptotic coefficient `(1/q!) Σ_{j ∈ [q,D]} (−1)^{j−q} a j (j−q)/(j−q)!` (formula (*)). -/
noncomputable def logAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  (1 / (q.factorial : ℂ)) *
    ∑ j ∈ Ico q (D + 1), (-1 : ℂ) ^ (j - q) * a j (j - q) / ((j - q).factorial : ℂ)

/-- The real form of `logAmplitudeCoeff`, for real data `b`. -/
noncomputable def logAmplitudeCoeffReal (D : ℕ) (b : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  (1 / (q.factorial : ℝ)) *
    ∑ j ∈ Ico q (D + 1), (-1 : ℝ) ^ (j - q) * b j (j - q) / ((j - q).factorial : ℝ)

/-- The Taylor polynomial `P_j(s) = Σ_{ℓ ≤ D} a j ℓ (s−μ)^ℓ/ℓ!` of the `j`-th pairing. -/
noncomputable def polarTaylorPoly (D : ℕ) (a : ℕ → ℕ → ℂ) (μ : ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  ∑ ℓ ∈ range (D + 1), a j ℓ * (s - μ) ^ ℓ / (ℓ.factorial : ℂ)

/-- The polar sum `Σ_{j ≤ D} P_j(s)/(μ−s)^{j+1}`. -/
noncomputable def polarAmplitudeSum (D : ℕ) (a : ℕ → ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ j ∈ range (D + 1), polarTaylorPoly D a μ j s / (μ - s) ^ (j + 1)

/-- The holomorphic remainder `Σ_j Σ_{ℓ ∈ (j, D]} (−1)^{j+1} a j ℓ (s−μ)^{ℓ−j−1}/ℓ!`. -/
noncomputable def polarAmplitudeRemainder (D : ℕ) (a : ℕ → ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ j ∈ range (D + 1), ∑ ℓ ∈ Ico (j + 1) (D + 1),
    (-1 : ℂ) ^ (j + 1) * a j ℓ / (ℓ.factorial : ℂ) * (s - μ) ^ (ℓ - j - 1)

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
  rw [sq, neg_one_pow_mul_self]

theorem neg_sub_pow_eq (μ s : ℂ) (n : ℕ) : (μ - s) ^ n = (-1) ^ n * (s - μ) ^ n := by
  rw [← neg_sub, neg_eq_neg_one_mul, mul_pow]

/-- The two arrays differ by the sign and factorial of the library's `polarCoeff` convention. -/
theorem polarAmplitudeCoeff_eq (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) :
    polarAmplitudeCoeff D a q =
      (-1 : ℂ) ^ (q + 1) * (q.factorial : ℂ) * logAmplitudeCoeff D a q := by
  unfold polarAmplitudeCoeff logAmplitudeCoeff
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  rw [← mul_assoc, mul_assoc ((-1 : ℂ) ^ (q + 1)), mul_one_div_cancel hq, mul_one, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hqj : q ≤ j := (mem_Ico.1 hj).1
  have : j + 1 = (q + 1) + (j - q) := by omega
  rw [this, pow_add]; ring

/-- Real data: the polar array is `polarCoeff` of the real coefficient system
`logAmplitudeCoeffReal`. -/
theorem polarAmplitudeCoeff_ofReal (D : ℕ) (b : ℕ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) :
    polarAmplitudeCoeff D (fun j ℓ => (b j ℓ : ℂ)) q =
      polarCoeff (fun _ q => logAmplitudeCoeffReal D b q) μ₀ q := by
  rw [polarAmplitudeCoeff_eq, polarCoeff]
  congr 1
  unfold logAmplitudeCoeff logAmplitudeCoeffReal
  push_cast
  rfl

/-- The top array entry is the single term `(−1)^{D+1} a D 0`. -/
theorem polarAmplitudeCoeff_top (D : ℕ) (a : ℕ → ℕ → ℂ) :
    polarAmplitudeCoeff D a D = (-1 : ℂ) ^ (D + 1) * a D 0 := by
  unfold polarAmplitudeCoeff
  rw [Nat.Ico_succ_singleton, sum_singleton]; simp

/-- Entries above `D` vanish. -/
theorem polarAmplitudeCoeff_eq_zero_of_lt (D : ℕ) (a : ℕ → ℕ → ℂ) {q : ℕ} (hq : D < q) :
    polarAmplitudeCoeff D a q = 0 := by
  unfold polarAmplitudeCoeff
  rw [Finset.Ico_eq_empty (by omega), sum_empty]

/-- Zero padding: if the pairings vanish from order `M` on, so do the array entries. -/
theorem polarAmplitudeCoeff_eq_zero_of_forall (D : ℕ) (a : ℕ → ℕ → ℂ) {M q : ℕ} (hq : M ≤ q)
    (ha : ∀ j ℓ, M ≤ j → a j ℓ = 0) : polarAmplitudeCoeff D a q = 0 := by
  unfold polarAmplitudeCoeff
  refine sum_eq_zero fun j hj => ?_
  rw [ha j _ (le_trans hq (mem_Ico.1 hj).1)]; simp

/-- One term of the polar sum, `ℓ ≤ j`: the singular part. -/
theorem polar_term_le {μ s : ℂ} (hs : s ≠ μ) (c : ℂ) {ℓ j : ℕ} (hℓ : ℓ ≤ j) :
    c * (s - μ) ^ ℓ / (μ - s) ^ (j + 1) = (-1 : ℂ) ^ (j + 1) * c / (s - μ) ^ (j - ℓ + 1) := by
  have h0 : s - μ ≠ 0 := sub_ne_zero.2 hs
  have hsplit : (s - μ) ^ (j + 1) = (s - μ) ^ ℓ * (s - μ) ^ (j - ℓ + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [neg_sub_pow_eq μ s (j + 1), hsplit]
  have h1 : (-1 : ℂ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [neg_one_pow_sq, mul_one]

/-- One term of the polar sum, `ℓ > j`: the polynomial part. -/
theorem polar_term_gt {μ s : ℂ} (hs : s ≠ μ) (c : ℂ) {ℓ j : ℕ} (hℓ : j < ℓ) :
    c * (s - μ) ^ ℓ / (μ - s) ^ (j + 1) = (-1 : ℂ) ^ (j + 1) * c * (s - μ) ^ (ℓ - j - 1) := by
  have h0 : s - μ ≠ 0 := sub_ne_zero.2 hs
  have hsplit : (s - μ) ^ ℓ = (s - μ) ^ (j + 1) * (s - μ) ^ (ℓ - j - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [neg_sub_pow_eq μ s (j + 1), hsplit]
  have h1 : (-1 : ℂ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [neg_one_pow_sq, mul_one]

/-- **The polar amplitude identity.** For `s ≠ μ` the polar sum minus the library's polar part
of the array `polarAmplitudeCoeff D a` is the polynomial remainder. -/
theorem polarAmplitudeSum_sub_polarPart (D : ℕ) (a : ℕ → ℕ → ℂ) (μ : ℂ) {s : ℂ}
    (hs : s ≠ μ) :
    polarAmplitudeSum D a μ s - polarPart D (polarAmplitudeCoeff D a) μ s =
      polarAmplitudeRemainder D a μ s := by
  -- split every P_j into ℓ ≤ j and ℓ > j
  have hsplit : ∀ j ∈ range (D + 1), polarTaylorPoly D a μ j s / (μ - s) ^ (j + 1) =
      (∑ ℓ ∈ range (j + 1),
        (-1 : ℂ) ^ (j + 1) * (a j ℓ / (ℓ.factorial : ℂ)) / (s - μ) ^ (j - ℓ + 1)) +
      ∑ ℓ ∈ Ico (j + 1) (D + 1),
        (-1 : ℂ) ^ (j + 1) * a j ℓ / (ℓ.factorial : ℂ) * (s - μ) ^ (ℓ - j - 1) := by
    intro j hj
    have hjD : j + 1 ≤ D + 1 := by have := (mem_range.1 hj); omega
    unfold polarTaylorPoly
    rw [sum_div, ← Finset.sum_range_add_sum_Ico _ hjD]
    congr 1
    · refine sum_congr rfl fun ℓ hℓ => ?_
      have hℓj : ℓ ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hℓ)
      rw [show a j ℓ * (s - μ) ^ ℓ / (ℓ.factorial : ℂ) =
          (a j ℓ / (ℓ.factorial : ℂ)) * (s - μ) ^ ℓ by ring]
      exact polar_term_le hs _ hℓj
    · refine sum_congr rfl fun ℓ hℓ => ?_
      have hℓj : j < ℓ := (mem_Ico.1 hℓ).1
      rw [show a j ℓ * (s - μ) ^ ℓ / (ℓ.factorial : ℂ) =
          (a j ℓ / (ℓ.factorial : ℂ)) * (s - μ) ^ ℓ by ring, polar_term_gt hs _ hℓj]
      ring
  unfold polarAmplitudeSum polarAmplitudeRemainder
  rw [sum_congr rfl hsplit, sum_add_distrib, add_sub_right_comm, add_eq_right, sub_eq_zero]
  -- the singular part is the polar part: reindex ℓ = j − q and swap the sums
  unfold polarPart polarAmplitudeCoeff
  have hrefl : ∀ j ∈ range (D + 1),
      (∑ ℓ ∈ range (j + 1),
        (-1 : ℂ) ^ (j + 1) * (a j ℓ / (ℓ.factorial : ℂ)) / (s - μ) ^ (j - ℓ + 1)) =
      ∑ q ∈ range (j + 1),
        (-1 : ℂ) ^ (j + 1) * (a j (j - q) / ((j - q).factorial : ℂ)) / (s - μ) ^ (q + 1) := by
    intro j _
    rw [← Finset.sum_range_reflect]
    refine sum_congr rfl fun q hq => ?_
    have hqj : q ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hq)
    have h1 : j + 1 - 1 - q = j - q := by omega
    have h2 : j - (j - q) + 1 = q + 1 := by omega
    rw [h1, h2]
  rw [sum_congr rfl hrefl]
  rw [Finset.sum_comm' (t' := range (D + 1)) (s' := fun q => Ico q (D + 1))]
  · refine sum_congr rfl fun q _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    ring
  · intro j q
    simp only [mem_range, mem_Ico]
    omega

end Grammar
