/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TwoScaleDivision
import Grammar.MellinRegularization

/-!
# The quotient of two cutoff expansions to all orders (§20, posterior expectations)

Two cutoff expansions `Z₁, Z₂` on the lattice `Q⁻¹ℕ` (log degree `≤ D`) whose coefficients vanish
below the common leading index `m₀` (`VanishBelow`), with the denominator's leading block
`b₀(log N) = Σ_q c₂(m₀/Q, q) (log N)^q` bounded away from zero, have

★★★ `cutoff_div_isBigO`:
`Z₁(N)/Z₂(N) = Σ_{j<J} R_j(log N) N^{−j/Q} + O(N^{−J/Q} (1 + log N)^{D(J+1)})`,

where `R_j(L) = quotientBlocks (a_·(L)) (b_·(L)) j` are the pointwise quotient blocks of the
block polynomials `a_j(L) = Σ_q c₁((m₀+j)/Q, q) L^q`, `b_j` likewise (`blockPoly`).  This is the
deterministic all-orders expansion of the posterior expectation `E_N[φ]/E_N[1]` as exact
rational-log blocks (consult #158 item 3, #159 B(ii)); the first correction and its probabilistic
form live in the bridge (`Bridge/PosteriorQuotient`).

Route: `absSpectralSum_eq_sum_blocks` reindexes the spectral sum below `(m₀+J)/Q` by the block
index (`latticeBelow` is the image of `range`), `cutoffExpansion_normalised_isBigO` normalises by
`N^{m₀/Q}`, and `twoScale_div_isBigO` divides, with `x = N^{−1/Q}`, `g = (1 + log N)^D`
(`isBigO_rpow_neg_mul_one_add_log_pow`: power decay beats the log blocks).

Zero `sorry`/`axiom`.
-/

open Filter Topology Asymptotics Finset

namespace Grammar

variable {Q D : ℕ} {c : ℝ → ℕ → ℝ} {Z : ℝ → ℝ}

/-- Vanishing below the leading lattice index `m₀`: `c (m/Q) q = 0` for `m < m₀`. -/
def VanishBelow (Q : ℕ) (c : ℝ → ℕ → ℝ) (m₀ : ℕ) : Prop :=
  ∀ m : ℕ, m < m₀ → ∀ q, c ((m : ℝ) / Q) q = 0

/-- The `j`-th block polynomial above the leading index:
`blockPoly Q D c m₀ j L = Σ_{q≤D} c((m₀+j)/Q, q) L^q`. -/
noncomputable def blockPoly (Q D : ℕ) (c : ℝ → ℕ → ℝ) (m₀ j : ℕ) (L : ℝ) : ℝ :=
  ∑ q ∈ range (D + 1), c (((m₀ + j : ℕ) : ℝ) / Q) q * L ^ q

/-- The lattice below `(m₀+J)/Q` is the image of `range (m₀ + J)`. -/
theorem latticeBelow_natCast_div (hQ : 0 < Q) (n : ℕ) :
    latticeBelow Q ((n : ℝ) / Q) = (range n).image fun m : ℕ => (m : ℝ) / Q := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold latticeBelow
  rw [div_mul_cancel₀ _ hQ', Nat.ceil_natCast]

/-- The spectral sum below `(m₀+J)/Q` as `N^{−m₀/Q}` times the block expansion. -/
theorem absSpectralSum_eq_sum_blocks (hQ : 0 < Q) {m₀ : ℕ} (hvan : VanishBelow Q c m₀) (J : ℕ)
    {N : ℝ} (hN : 0 < N) :
    absSpectralSum Q D c (((m₀ + J : ℕ) : ℝ) / Q) N =
      N ^ (-((m₀ : ℝ) / Q)) *
        ∑ j ∈ range J, blockPoly Q D c m₀ j (Real.log N) * (N ^ (-(1 / (Q : ℝ)))) ^ j := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold absSpectralSum
  rw [latticeBelow_natCast_div hQ, Finset.sum_image (fun m _ n _ h => by
    exact_mod_cast (div_left_inj' hQ').1 h),
    ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_right m₀ J),
    Finset.sum_eq_zero fun m hm => by
      simp only [hvan m (mem_range.1 hm), zero_mul, Finset.sum_const_zero, mul_zero],
    zero_add, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpow : N ^ (-(((m₀ + k : ℕ) : ℝ) / Q)) =
      N ^ (-((m₀ : ℝ) / Q)) * (N ^ (-(1 / (Q : ℝ)))) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  rw [hpow]
  unfold blockPoly
  ring

/-- The block polynomials are bounded by `(Σ_q |c_q|) (1 + L)^D` for `L ≥ 0`. -/
theorem abs_blockPoly_le (Q D : ℕ) (c : ℝ → ℕ → ℝ) (m₀ j : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    |blockPoly Q D c m₀ j L| ≤
      (∑ q ∈ range (D + 1), |c (((m₀ + j : ℕ) : ℝ) / Q) q|) * (1 + L) ^ D := by
  unfold blockPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [abs_mul, abs_pow, abs_of_nonneg hL]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc L ^ q ≤ (1 + L) ^ q := pow_le_pow_left₀ hL (by linarith) q
    _ ≤ (1 + L) ^ D := pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.1 (mem_range.1 hq))

/-- ★★ **The normalised cutoff expansion in block form**:
`N^{m₀/Q} Z(N) − Σ_{j<J} a_j(log N) N^{−j/Q} = O(N^{−J/Q} (1 + log N)^D)`. -/
theorem cutoffExpansion_normalised_isBigO (hQ : 0 < Q) (hexp : CutoffExpansion Q D Z c) {m₀ : ℕ}
    (hvan : VanishBelow Q c m₀) {J : ℕ} (hJ : 1 ≤ J) :
    (fun N : ℝ => N ^ ((m₀ : ℝ) / Q) * Z N -
        ∑ j ∈ range J, blockPoly Q D c m₀ j (Real.log N) * (N ^ (-(1 / (Q : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ => (N ^ (-(1 / (Q : ℝ)))) ^ J * (1 + Real.log N) ^ D := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hL : (0 : ℝ) < ((m₀ + J : ℕ) : ℝ) / Q := by
    apply div_pos _ hQ0
    exact_mod_cast (by omega : 0 < m₀ + J)
  obtain ⟨K, hK⟩ := hexp _ hL
  refine IsBigO.of_bound K ?_
  filter_upwards [hK, eventually_ge_atTop 1] with N hKN hN1
  have hN : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hx : 0 < N ^ (-(1 / (Q : ℝ))) := Real.rpow_pos_of_pos hN _
  have hm : 0 < N ^ ((m₀ : ℝ) / Q) := Real.rpow_pos_of_pos hN _
  have hcancel : N ^ ((m₀ : ℝ) / Q) * N ^ (-((m₀ : ℝ) / Q)) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  have hid : N ^ ((m₀ : ℝ) / Q) * Z N -
      ∑ j ∈ range J, blockPoly Q D c m₀ j (Real.log N) * (N ^ (-(1 / (Q : ℝ)))) ^ j =
      N ^ ((m₀ : ℝ) / Q) * (Z N - absSpectralSum Q D c (((m₀ + J : ℕ) : ℝ) / Q) N) := by
    rw [absSpectralSum_eq_sum_blocks hQ hvan J hN, mul_sub, ← mul_assoc, hcancel, one_mul]
  have hscale : N ^ ((m₀ : ℝ) / Q) * (N ^ (-(((m₀ + J : ℕ) : ℝ) / Q))) =
      (N ^ (-(1 / (Q : ℝ)))) ^ J := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  rw [hid, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hm,
    abs_of_nonneg (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg (by linarith) _))]
  calc N ^ ((m₀ : ℝ) / Q) * |Z N - absSpectralSum Q D c (((m₀ + J : ℕ) : ℝ) / Q) N|
      ≤ N ^ ((m₀ : ℝ) / Q) *
        (K * (N ^ (-(((m₀ + J : ℕ) : ℝ) / Q)) * (1 + Real.log N) ^ D)) :=
        mul_le_mul_of_nonneg_left hKN hm.le
    _ = K * ((N ^ ((m₀ : ℝ) / Q) * N ^ (-(((m₀ + J : ℕ) : ℝ) / Q))) * (1 + Real.log N) ^ D) := by
        ring
    _ = K * ((N ^ (-(1 / (Q : ℝ)))) ^ J * (1 + Real.log N) ^ D) := by rw [hscale]

/-- `N^{−1/Q} (1 + log N)^D → 0`: power decay beats the log blocks. -/
theorem tendsto_rpow_neg_inv_mul_one_add_log_pow (hQ : 0 < Q) (D : ℕ) :
    Tendsto (fun N : ℝ => N ^ (-(1 / (Q : ℝ))) * (1 + Real.log N) ^ D) atTop (𝓝 0) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := isBigO_rpow_neg_mul_one_add_log_pow (U := 1 / (Q : ℝ)) (a := 1 / (2 * Q))
    (one_div_lt_one_div_of_lt hQ0 (by linarith)) D
  exact h.trans_tendsto (tendsto_rpow_neg_atTop (by positivity))

/-- ★★★ **The quotient of two cutoff expansions to all orders**:
`Z₁/Z₂ − Σ_{j<J} R_j(log N) N^{−j/Q} = O(N^{−J/Q} (1 + log N)^{D(J+1)})` with the pointwise
quotient blocks `R_j` of the block polynomials, provided the denominator's leading block is
eventually bounded away from zero. -/
theorem cutoff_div_isBigO (hQ : 0 < Q) {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂) {m₀ : ℕ}
    (hv₁ : VanishBelow Q c₁ m₀) (hv₂ : VanishBelow Q c₂ m₀) {J : ℕ} (hJ : 1 ≤ J) {cb : ℝ}
    (hcb : 0 < cb) (hb0 : ∀ᶠ N in atTop, cb ≤ |blockPoly Q D c₂ m₀ 0 (Real.log N)|) :
    (fun N : ℝ => Z₁ N / Z₂ N - ∑ j ∈ range J,
        quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) j * (N ^ (-(1 / (Q : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ => (N ^ (-(1 / (Q : ℝ)))) ^ J * ((1 + Real.log N) ^ D) ^ (J + 1) := by
  -- the block bound
  obtain ⟨Cab, hCab⟩ : ∃ Cab, Cab = ∑ j ∈ range J, (∑ q ∈ range (D + 1),
      |c₁ (((m₀ + j : ℕ) : ℝ) / Q) q| + ∑ q ∈ range (D + 1), |c₂ (((m₀ + j : ℕ) : ℝ) / Q) q|) :=
    ⟨_, rfl⟩
  have hCab0 : 0 ≤ Cab := hCab ▸ Finset.sum_nonneg fun j _ =>
    add_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hab : ∀ᶠ N in atTop, ∀ j < J, |blockPoly Q D c₁ m₀ j (Real.log N)| ≤
      Cab * (1 + Real.log N) ^ D ∧
      |blockPoly Q D c₂ m₀ j (Real.log N)| ≤ Cab * (1 + Real.log N) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with N hN1 j hj
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hg0 : 0 ≤ (1 + Real.log N) ^ D := pow_nonneg (by linarith) _
    have hle := Finset.single_le_sum (f := fun j => ∑ q ∈ range (D + 1),
      |c₁ (((m₀ + j : ℕ) : ℝ) / Q) q| + ∑ q ∈ range (D + 1), |c₂ (((m₀ + j : ℕ) : ℝ) / Q) q|)
      (fun j _ => add_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _)
        (Finset.sum_nonneg fun q _ => abs_nonneg _)) (mem_range.2 hj)
    rw [← hCab] at hle
    have h1 : 0 ≤ ∑ q ∈ range (D + 1), |c₁ (((m₀ + j : ℕ) : ℝ) / Q) q| :=
      Finset.sum_nonneg fun q _ => abs_nonneg _
    have h2 : 0 ≤ ∑ q ∈ range (D + 1), |c₂ (((m₀ + j : ℕ) : ℝ) / Q) q| :=
      Finset.sum_nonneg fun q _ => abs_nonneg _
    constructor
    · exact (abs_blockPoly_le Q D c₁ m₀ j hlog).trans
        (mul_le_mul_of_nonneg_right (by linarith) hg0)
    · exact (abs_blockPoly_le Q D c₂ m₀ j hlog).trans
        (mul_le_mul_of_nonneg_right (by linarith) hg0)
  have hg : ∀ᶠ N in atTop, 1 ≤ (1 + Real.log N) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have hmain := twoScale_div_isBigO (A := fun N => N ^ ((m₀ : ℝ) / Q) * Z₁ N)
    (B := fun N => N ^ ((m₀ : ℝ) / Q) * Z₂ N) (x := fun N => N ^ (-(1 / (Q : ℝ))))
    (g := fun N => (1 + Real.log N) ^ D) (a := fun j N => blockPoly Q D c₁ m₀ j (Real.log N))
    (b := fun j N => blockPoly Q D c₂ m₀ j (Real.log N)) hJ hcb hCab0 hg
    (tendsto_rpow_neg_inv_mul_one_add_log_pow hQ D) hab hb0
    (cutoffExpansion_normalised_isBigO hQ h₁ hv₁ hJ)
    (cutoffExpansion_normalised_isBigO hQ h₂ hv₂ hJ)
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hm : N ^ ((m₀ : ℝ) / Q) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  simp only [mul_div_mul_left _ _ hm]

end Grammar
