/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CutoffQuotientExpansion
import Grammar.SourceLog
import Grammar.EmpiricalLeadingConsistency

/-!
# The posterior variance to all orders (§20, posterior cumulants)

The posterior variance of an observable for a fixed sample is the second connected coefficient
`Z₃/Z₂ − (Z₁/Z₂)²` (`Z₁ = Z_N[ηf]`, `Z₂ = Z_N[η]`, `Z₃ = Z_N[ηf²]`; `SourceLog`).  Given the
all-orders quotient expansions `cutoff_div_isBigO` of `Z₁/Z₂` and `Z₃/Z₂` with quotient blocks
`R₁, R₃`, the variance has the all-orders expansion with the **variance blocks**
`κ₂(j) = R₃(j) − Σ_{i ≤ j} R₁(i) R₁(j − i)` (`varianceBlocks`):

★★ `cutoff_variance_isBigO`:
`Z₃/Z₂ − (Z₁/Z₂)² − Σ_{j<J} κ₂,j(log N) N^{−j/Q} = O(N^{−J/Q} (1 + log N)^{D(2J+2)})`.

Route: `twoScale_variance_isBigO` is the abstract two-scale statement (`x = N^{−1/Q}`,
`g = (1 + log N)^D`): with `E₁ = P₁ − S₁`, `E₃ = P₃ − S₃` the two quotient remainders and
`S₁² = Σ_{k<J} (Σ_{i≤k} R₁ i R₁ (k−i)) x^k + T` (`sum_mul_sum_eq_cauchy_add_tail`, the tail `T`
carrying the degrees `J ≤ k < 2J`), the variance error is `E₃ − E₁² − 2 S₁ E₁ − T`, each term
`O(x^J g^{2J+2})` from the quotient-block bounds `|R₁ i| ≤ M g^{i+1}`
(`exists_bound_quotientBlocks`).

Zero `sorry`/`axiom`.
-/

open Filter Topology Asymptotics Finset

namespace Grammar

/-- The product of two truncated series: the Cauchy terms of degree `< J` plus an explicit tail of
degrees `J ≤ k < 2J`. -/
theorem sum_mul_sum_eq_cauchy_add_tail (u v : ℕ → ℝ) (x : ℝ) (J : ℕ) :
    (∑ i ∈ range J, u i * x ^ i) * (∑ j ∈ range J, v j * x ^ j) =
      ∑ k ∈ range J, (∑ i ∈ range (k + 1), u i * v (k - i)) * x ^ k + ∑ k ∈ Ico J (2 * J),
        (∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          u p.1 * v p.2) * x ^ k := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product' (range J) (range J)
    (fun i j => u i * x ^ i * (v j * x ^ j))]
  have hmaps : ∀ p ∈ range J ×ˢ range J, (fun p : ℕ × ℕ => p.1 + p.2) p ∈ range (2 * J) := by
    intro p hp
    rw [mem_product, mem_range, mem_range] at hp
    rw [mem_range]
    change p.1 + p.2 < 2 * J
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps,
    ← Finset.sum_range_add_sum_Ico _ (by omega : J ≤ 2 * J)]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < J := mem_range.1 hk
    have hfib : (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k) =
        antidiagonal k := by
      ext p
      simp only [mem_filter, mem_product, mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    rw [hfib, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hpow : x ^ i * x ^ (k - i) = x ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hpow]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p.1 + p.2 = k := (mem_filter.1 hp).2
    rw [← hpk, pow_add]
    ring

/-- The truncated quotient is bounded by `J M g^J` when `|R₁ i| ≤ M g^{i+1}`, `0 ≤ x ≤ 1`,
`1 ≤ g`. -/
theorem abs_sum_blocks_le {R : ℕ → ℝ} {x g M : ℝ} {J : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hg : 1 ≤ g) (hM : 0 ≤ M) (hR : ∀ i < J, |R i| ≤ M * g ^ (i + 1)) :
    |∑ j ∈ range J, R j * x ^ j| ≤ J * M * g ^ J := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ j ∈ range J, |R j * x ^ j| ≤ M * g ^ J := by
    intro j hj
    have hj' : j < J := mem_range.1 hj
    rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    calc |R j| * x ^ j ≤ M * g ^ (j + 1) * 1 :=
          mul_le_mul (hR j hj') (pow_le_one₀ hx0 hx1) (pow_nonneg hx0 _)
            (by positivity)
      _ ≤ M * g ^ J := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg hj') hM
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The tail of `S₁²` is bounded by `J³ M² g^{2J+1} x^J`. -/
theorem abs_tail_le {R : ℕ → ℝ} {x g M : ℝ} {J : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hg : 1 ≤ g) (hM : 0 ≤ M) (hR : ∀ i < J, |R i| ≤ M * g ^ (i + 1)) :
    |∑ k ∈ Ico J (2 * J),
        (∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          R p.1 * R p.2) * x ^ k| ≤ J ^ 3 * M ^ 2 * g ^ (2 * J + 1) * x ^ J := by
  have hg0 : 0 ≤ g := by linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ k ∈ Ico J (2 * J), |(∑ p ∈ (range J ×ˢ range J).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = k), R p.1 * R p.2) * x ^ k| ≤
        J ^ 2 * M ^ 2 * g ^ (2 * J + 1) * x ^ J := by
    intro k hk
    have hkJ : J ≤ k := (mem_Ico.1 hk).1
    rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    have hinner : |∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
        R p.1 * R p.2| ≤ J ^ 2 * (M ^ 2 * g ^ (2 * J + 1)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          |R p.1 * R p.2| ≤ M ^ 2 * g ^ (2 * J + 1) := by
        intro p hp
        have hp1 : p.1 < J := (mem_range.1 (mem_product.1 (mem_filter.1 hp).1).1)
        have hp2 : p.2 < J := (mem_range.1 (mem_product.1 (mem_filter.1 hp).1).2)
        rw [abs_mul]
        calc |R p.1| * |R p.2| ≤ M * g ^ (p.1 + 1) * (M * g ^ (p.2 + 1)) :=
              mul_le_mul (hR _ hp1) (hR _ hp2) (abs_nonneg _) (by positivity)
          _ = M ^ 2 * g ^ (p.1 + 1 + (p.2 + 1)) := by rw [pow_add]; ring
          _ ≤ M ^ 2 * g ^ (2 * J + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg (by omega)) (by positivity)
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hcard := (Finset.card_filter_le (range J ×ˢ range J)
        (fun p : ℕ × ℕ => p.1 + p.2 = k))
      rw [card_product, card_range] at hcard
      calc (((range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k)).card : ℝ) ≤
            ((J * J : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (J : ℝ) ^ 2 := by push_cast; ring
    calc |∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          R p.1 * R p.2| * x ^ k ≤ J ^ 2 * (M ^ 2 * g ^ (2 * J + 1)) * x ^ J :=
          mul_le_mul hinner (pow_le_pow_of_le_one hx0 hx1 hkJ) (pow_nonneg hx0 _)
            (by positivity)
      _ = J ^ 2 * M ^ 2 * g ^ (2 * J + 1) * x ^ J := by ring
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [Nat.card_Ico, nsmul_eq_mul]
  have hc : ((2 * J - J : ℕ) : ℝ) = J := by
    rw [show 2 * J - J = J by omega]
  rw [hc]
  exact le_of_eq (by ring)

/-- ★ **Two-scale variance**: if `P₁ − Σ_{j<J} R₁ j x^j` and `P₃ − Σ_{j<J} R₃ j x^j` are
`O(x^J g^{J+1})` and the blocks `R₁` are bounded by `M g^{i+1}`, then
`P₃ − P₁² − Σ_{j<J} (R₃ j − Σ_{i≤j} R₁ i R₁ (j−i)) x^j = O(x^J g^{2J+2})`. -/
theorem twoScale_variance_isBigO {P₁ P₃ x g : ℝ → ℝ} {R₁ R₃ : ℕ → ℝ → ℝ} {J : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hx : ∀ᶠ N in atTop, 0 ≤ x N ∧ x N ≤ 1) (hg : ∀ᶠ N in atTop, 1 ≤ g N)
    (hR : ∀ᶠ N in atTop, ∀ i < J, |R₁ i N| ≤ M * g N ^ (i + 1))
    (h₁ : (fun N => P₁ N - ∑ j ∈ range J, R₁ j N * x N ^ j) =O[atTop]
      fun N => x N ^ J * g N ^ (J + 1))
    (h₃ : (fun N => P₃ N - ∑ j ∈ range J, R₃ j N * x N ^ j) =O[atTop]
      fun N => x N ^ J * g N ^ (J + 1)) :
    (fun N => P₃ N - P₁ N ^ 2 - ∑ j ∈ range J,
        (R₃ j N - ∑ i ∈ range (j + 1), R₁ i N * R₁ (j - i) N) * x N ^ j)
      =O[atTop] fun N => x N ^ J * g N ^ (2 * J + 2) := by
  obtain ⟨K₁, hK₁, hb₁⟩ := h₁.exists_pos
  obtain ⟨K₃, hK₃, hb₃⟩ := h₃.exists_pos
  refine IsBigO.of_bound (K₃ + K₁ ^ 2 + 2 * J * M * K₁ + J ^ 3 * M ^ 2) ?_
  filter_upwards [hx, hg, hR, hb₁.bound, hb₃.bound] with N ⟨hx0, hx1⟩ hg1 hRN he₁ he₃
  set X := x N with hX
  set G := g N with hG
  set S₁ := ∑ j ∈ range J, R₁ j N * X ^ j with hS₁
  set S₃ := ∑ j ∈ range J, R₃ j N * X ^ j with hS₃
  set E₁ := P₁ N - S₁ with hE₁
  set E₃ := P₃ N - S₃ with hE₃
  set T := ∑ k ∈ Ico J (2 * J), (∑ p ∈ (range J ×ˢ range J).filter
    (fun p : ℕ × ℕ => p.1 + p.2 = k), R₁ p.1 N * R₁ p.2 N) * X ^ k with hT
  clear_value X G S₁ S₃ E₁ E₃ T
  have hG0 : 0 ≤ G := by linarith
  have hXJ : 0 ≤ X ^ J := pow_nonneg hx0 _
  have hsq : S₁ ^ 2 = ∑ k ∈ range J, (∑ i ∈ range (k + 1), R₁ i N * R₁ (k - i) N) * X ^ k + T := by
    rw [sq, hS₁, sum_mul_sum_eq_cauchy_add_tail, hT]
  have hid : P₃ N - P₁ N ^ 2 - ∑ j ∈ range J,
      (R₃ j N - ∑ i ∈ range (j + 1), R₁ i N * R₁ (j - i) N) * X ^ j =
        E₃ - E₁ ^ 2 - 2 * S₁ * E₁ - T := by
    have hsplit : ∑ j ∈ range J, (R₃ j N - ∑ i ∈ range (j + 1), R₁ i N * R₁ (j - i) N) * X ^ j =
        S₃ - ∑ k ∈ range J, (∑ i ∈ range (k + 1), R₁ i N * R₁ (k - i) N) * X ^ k := by
      rw [hS₃, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    have hP₁ : P₁ N = E₁ + S₁ := by rw [hE₁]; ring
    have hP₃ : P₃ N = E₃ + S₃ := by rw [hE₃]; ring
    rw [hP₁, hP₃]
    linear_combination -hsq
  rw [hid]
  simp only [Real.norm_eq_abs] at he₁ he₃ ⊢
  rw [abs_of_nonneg (mul_nonneg hXJ (pow_nonneg hG0 _))] at he₁ he₃ ⊢
  have hS : |S₁| ≤ J * M * G ^ J := by
    rw [hS₁]
    exact abs_sum_blocks_le (R := fun i => R₁ i N) hx0 hx1 hg1 hM hRN
  have hTb : |T| ≤ J ^ 3 * M ^ 2 * G ^ (2 * J + 1) * X ^ J := by
    rw [hT]
    have h := abs_tail_le (R := fun i => R₁ i N) hx0 hx1 hg1 hM hRN
    simpa only using h
  -- monotonicity in the powers of `G` and `X`
  have hG1 : G ^ (J + 1) ≤ G ^ (2 * J + 2) := pow_le_pow_right₀ hg1 (by omega)
  have hG2 : G ^ J * G ^ (J + 1) = G ^ (2 * J + 1) := by rw [← pow_add]; congr 1; omega
  have hG3 : G ^ (2 * J + 1) ≤ G ^ (2 * J + 2) := pow_le_pow_right₀ hg1 (by omega)
  have hG4 : G ^ (J + 1) * G ^ (J + 1) = G ^ (2 * J + 2) := by rw [← pow_add]; congr 1; omega
  have hX2 : X ^ J * X ^ J ≤ X ^ J := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hE₁sq : |E₁| ^ 2 ≤ K₁ ^ 2 * (X ^ J * G ^ (2 * J + 2)) := by
    calc |E₁| ^ 2 ≤ (K₁ * (X ^ J * G ^ (J + 1))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) he₁ 2
      _ = K₁ ^ 2 * ((X ^ J * X ^ J) * (G ^ (J + 1) * G ^ (J + 1))) := by ring
      _ ≤ K₁ ^ 2 * (X ^ J * G ^ (2 * J + 2)) := by
          rw [hG4]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX2 (by positivity))
            (by positivity)
  have hSE : |S₁| * |E₁| ≤ J * M * K₁ * (X ^ J * G ^ (2 * J + 2)) := by
    calc |S₁| * |E₁| ≤ J * M * G ^ J * (K₁ * (X ^ J * G ^ (J + 1))) :=
          mul_le_mul hS he₁ (abs_nonneg _) (by positivity)
      _ = J * M * K₁ * (X ^ J * (G ^ J * G ^ (J + 1))) := by ring
      _ ≤ J * M * K₁ * (X ^ J * G ^ (2 * J + 2)) := by
          rw [hG2]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG3 hXJ) (by positivity)
  have hE₃' : |E₃| ≤ K₃ * (X ^ J * G ^ (2 * J + 2)) :=
    he₃.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG1 hXJ) hK₃.le)
  have hT' : |T| ≤ J ^ 3 * M ^ 2 * (X ^ J * G ^ (2 * J + 2)) := by
    refine hTb.trans ?_
    calc J ^ 3 * M ^ 2 * G ^ (2 * J + 1) * X ^ J = J ^ 3 * M ^ 2 * (X ^ J * G ^ (2 * J + 1)) := by
          ring
      _ ≤ J ^ 3 * M ^ 2 * (X ^ J * G ^ (2 * J + 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG3 hXJ) (by positivity)
  calc |E₃ - E₁ ^ 2 - 2 * S₁ * E₁ - T| ≤ |E₃| + |E₁| ^ 2 + 2 * (|S₁| * |E₁|) + |T| := by
        have h1 : |E₃ - E₁ ^ 2 - 2 * S₁ * E₁ - T| ≤ |E₃ - E₁ ^ 2 - 2 * S₁ * E₁| + |T| :=
          abs_sub _ _
        have h2 : |E₃ - E₁ ^ 2 - 2 * S₁ * E₁| ≤ |E₃ - E₁ ^ 2| + |2 * S₁ * E₁| := abs_sub _ _
        have h3 : |E₃ - E₁ ^ 2| ≤ |E₃| + |E₁ ^ 2| := abs_sub _ _
        rw [abs_pow] at h3
        rw [abs_mul, abs_mul, abs_two] at h2
        linarith
    _ ≤ K₃ * (X ^ J * G ^ (2 * J + 2)) + K₁ ^ 2 * (X ^ J * G ^ (2 * J + 2)) +
        2 * (J * M * K₁ * (X ^ J * G ^ (2 * J + 2))) +
          J ^ 3 * M ^ 2 * (X ^ J * G ^ (2 * J + 2)) := by
        linarith
    _ = (K₃ + K₁ ^ 2 + 2 * J * M * K₁ + J ^ 3 * M ^ 2) * (X ^ J * G ^ (2 * J + 2)) := by ring

variable {Q D : ℕ}

/-- The quotient blocks of the block polynomials are eventually bounded by `M (1 + log N)^{D(i+1)}`
(`i ≤ J`) once the denominator's leading block is bounded away from zero. -/
theorem exists_eventually_abs_quotientBlocks_blockPoly_le {c₁ c₂ : ℝ → ℕ → ℝ} (m₀ J : ℕ)
    {cb : ℝ} (hcb : 0 < cb)
    (hb0 : ∀ᶠ N in atTop, cb ≤ |blockPoly Q D c₂ m₀ 0 (Real.log N)|) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℝ in atTop, ∀ i ≤ J,
      |quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
        (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) i| ≤
          M * ((1 + Real.log N) ^ D) ^ (i + 1) := by
  obtain ⟨Cab, hCab⟩ : ∃ Cab, Cab = ∑ j ∈ range (J + 1), (∑ q ∈ range (D + 1),
      |c₁ (((m₀ + j : ℕ) : ℝ) / Q) q| + ∑ q ∈ range (D + 1), |c₂ (((m₀ + j : ℕ) : ℝ) / Q) q|) :=
    ⟨_, rfl⟩
  have hCab0 : 0 ≤ Cab := hCab ▸ Finset.sum_nonneg fun j _ =>
    add_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  obtain ⟨M, hM, hMb⟩ := exists_bound_quotientBlocks cb Cab hcb hCab0 J
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hb0] with N hN1 hb0N
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hg0 : 0 ≤ (1 + Real.log N) ^ D := pow_nonneg (by linarith) _
  have hg1 : 1 ≤ (1 + Real.log N) ^ D := one_le_pow₀ (by linarith)
  refine hMb _ _ _ hg1 hb0N fun j hj => ?_
  have hle := Finset.single_le_sum (f := fun j => ∑ q ∈ range (D + 1),
    |c₁ (((m₀ + j : ℕ) : ℝ) / Q) q| + ∑ q ∈ range (D + 1), |c₂ (((m₀ + j : ℕ) : ℝ) / Q) q|)
    (fun j _ => add_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)) (mem_range.2 (Nat.lt_succ_of_le hj))
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

/-- ★★ **The posterior variance to all orders**: for three cutoff expansions `Z₁, Z₂, Z₃`
(numerator `Z_N[ηf]`, denominator `Z_N[η]`, second moment `Z_N[ηf²]`) vanishing below the common
leading index `m₀` with the denominator's leading block bounded away from zero,
`Z₃/Z₂ − (Z₁/Z₂)² − Σ_{j<J} κ₂,j(log N) N^{−j/Q} = O(N^{−J/Q} (1 + log N)^{D(2J+2)})`
with the variance blocks `κ₂,j = varianceBlocks` of the pointwise block polynomials. -/
theorem cutoff_variance_isBigO (hQ : 0 < Q) {Z₁ Z₂ Z₃ : ℝ → ℝ} {c₁ c₂ c₃ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂)
    (h₃ : CutoffExpansion Q D Z₃ c₃) {m₀ : ℕ} (hv₁ : VanishBelow Q c₁ m₀)
    (hv₂ : VanishBelow Q c₂ m₀) (hv₃ : VanishBelow Q c₃ m₀) {J : ℕ} (hJ : 1 ≤ J) {cb : ℝ}
    (hcb : 0 < cb) (hb0 : ∀ᶠ N in atTop, cb ≤ |blockPoly Q D c₂ m₀ 0 (Real.log N)|) :
    (fun N : ℝ => Z₃ N / Z₂ N - (Z₁ N / Z₂ N) ^ 2 - ∑ j ∈ range J,
        varianceBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₂ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₃ m₀ i (Real.log N)) j * (N ^ (-(1 / (Q : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ =>
        (N ^ (-(1 / (Q : ℝ)))) ^ J * ((1 + Real.log N) ^ D) ^ (2 * J + 2) := by
  have hd₁ := cutoff_div_isBigO hQ h₁ h₂ hv₁ hv₂ hJ hcb hb0
  have hd₃ := cutoff_div_isBigO hQ h₃ h₂ hv₃ hv₂ hJ hcb hb0
  obtain ⟨M, hM, hR⟩ := exists_eventually_abs_quotientBlocks_blockPoly_le (Q := Q) (D := D)
    (c₁ := c₁) (c₂ := c₂) m₀ J hcb hb0
  have hx : ∀ᶠ N : ℝ in atTop, 0 ≤ N ^ (-(1 / (Q : ℝ))) ∧ N ^ (-(1 / (Q : ℝ))) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact ⟨Real.rpow_nonneg (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
        have : 0 ≤ 1 / (Q : ℝ) := by positivity
        linarith)⟩
  have hg : ∀ᶠ N : ℝ in atTop, 1 ≤ (1 + Real.log N) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have hR' : ∀ᶠ N : ℝ in atTop, ∀ i < J,
      |quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
        (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) i| ≤
          M * ((1 + Real.log N) ^ D) ^ (i + 1) := by
    filter_upwards [hR] with N hN i hi
    exact hN i hi.le
  have hmain := twoScale_variance_isBigO (P₁ := fun N => Z₁ N / Z₂ N)
    (P₃ := fun N => Z₃ N / Z₂ N) (x := fun N : ℝ => N ^ (-(1 / (Q : ℝ))))
    (g := fun N => (1 + Real.log N) ^ D)
    (R₁ := fun i N => quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
      (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) i)
    (R₃ := fun i N => quotientBlocks (fun i => blockPoly Q D c₃ m₀ i (Real.log N))
      (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) i) hM hx hg hR' hd₁ hd₃
  simpa only [varianceBlocks] using hmain

/-- The variant with the leading denominator block nonzero (automatic lower bound). -/
theorem cutoff_variance_isBigO' (hQ : 0 < Q) {Z₁ Z₂ Z₃ : ℝ → ℝ} {c₁ c₂ c₃ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂)
    (h₃ : CutoffExpansion Q D Z₃ c₃) {m₀ : ℕ} (hv₁ : VanishBelow Q c₁ m₀)
    (hv₂ : VanishBelow Q c₂ m₀) (hv₃ : VanishBelow Q c₃ m₀) {J : ℕ} (hJ : 1 ≤ J)
    (hne : ∃ q ∈ range (D + 1), c₂ ((m₀ : ℝ) / Q) q ≠ 0) :
    (fun N : ℝ => Z₃ N / Z₂ N - (Z₁ N / Z₂ N) ^ 2 - ∑ j ∈ range J,
        varianceBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₂ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₃ m₀ i (Real.log N)) j * (N ^ (-(1 / (Q : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ =>
        (N ^ (-(1 / (Q : ℝ)))) ^ J * ((1 + Real.log N) ^ D) ^ (2 * J + 2) := by
  have hne' : ∃ q ∈ range (D + 1), c₂ (((m₀ + 0 : ℕ) : ℝ) / Q) q ≠ 0 := by
    simpa only [Nat.add_zero] using hne
  obtain ⟨cb, hcb, hb0⟩ := exists_eventually_le_abs_blockPoly Q D c₂ m₀ 0 hne'
  exact cutoff_variance_isBigO hQ h₁ h₂ h₃ hv₁ hv₂ hv₃ hJ hcb hb0

section Empirical

open scoped ContDiff
open SmoothEngine

variable {d : ℕ} {η ζ f : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- Below a box-leading index every empirical coefficient family vanishes. -/
theorem vanishBelow_empCoeff (hk : ∀ i, 0 < k i) {lam : ℝ} {m m₀ : ℕ}
    (hBL : BoxLeading h k lam m) (hm₀ : (m₀ : ℝ) / Qamb k ≤ lam) :
    VanishBelow (Qamb k) (empCoeff η ζ h k) m₀ := by
  intro m hm q
  refine empCoeff_eq_zero_of_boxLeading_lt h k hk hBL (lt_of_lt_of_le ?_ hm₀) q
  have hQ : (0 : ℝ) < Qamb k := by exact_mod_cast Qamb_pos k hk
  exact div_lt_div_of_pos_right (by exact_mod_cast hm) hQ

/-- ★★★ **The posterior variance of a smooth observable to all orders, fixed sample**: for
`C^∞` weights `η`, field `ζ` and observable `f`, with the box-leading index `λ ≥ m₀/Q` and a
nonzero leading denominator block,
`Z_N[ηf²]/Z_N[η] − (Z_N[ηf]/Z_N[η])² − Σ_{j<J} κ₂,j(log N) N^{−j/Q}
  = O(N^{−J/Q} (1 + log N)^{(d−1)(2J+2)})`,
where `κ₂,j = varianceBlocks` are the variance blocks of the intrinsic coefficients
`empCoeff (ηf)`, `empCoeff η`, `empCoeff (ηf²)`. -/
theorem emp_variance_isBigO (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hf : ContDiff ℝ ∞ f)
    (hk : ∀ i, 0 < k i) {lam : ℝ} {m m₀ : ℕ} (hBL : BoxLeading h k lam m)
    (hm₀ : (m₀ : ℝ) / Qamb k ≤ lam) {J : ℕ} (hJ : 1 ≤ J)
    (hne : ∃ q ∈ range (d - 1 + 1), empCoeff η ζ h k ((m₀ : ℝ) / Qamb k) q ≠ 0) :
    (fun N : ℝ => empIntegral (fun v => η v * f v ^ 2) ζ h k N / empIntegral η ζ h k N -
        (empIntegral (fun v => η v * f v) ζ h k N / empIntegral η ζ h k N) ^ 2 -
        ∑ j ∈ range J, varianceBlocks
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff (fun v => η v * f v) ζ h k) m₀ i
            (Real.log N))
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff η ζ h k) m₀ i (Real.log N))
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff (fun v => η v * f v ^ 2) ζ h k) m₀ i
            (Real.log N)) j * (N ^ (-(1 / (Qamb k : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ =>
        (N ^ (-(1 / (Qamb k : ℝ)))) ^ J * ((1 + Real.log N) ^ (d - 1)) ^ (2 * J + 2) :=
  cutoff_variance_isBigO' (Qamb_pos k hk) (emp_cutoffExpansion (hη.mul hf) hζ hk)
    (emp_cutoffExpansion hη hζ hk) (emp_cutoffExpansion (hη.mul (hf.pow 2)) hζ hk)
    (vanishBelow_empCoeff hk hBL hm₀) (vanishBelow_empCoeff hk hBL hm₀)
    (vanishBelow_empCoeff hk hBL hm₀) hJ hne

end Empirical

end Grammar
