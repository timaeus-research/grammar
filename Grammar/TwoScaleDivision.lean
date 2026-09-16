/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.QuotientBlocks
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-scale division of asymptotic expansions (§20, the posterior quotient)

Deterministic division of two expansions with a common small scale `x` and block coefficients
bounded by a slowly varying `g ≥ 1` (for the posterior expectation: `x = n^{−1/Q}`, `g = (log n)^D`,
the blocks `a_j, b_j` polynomials in `log n` of degree `≤ D`):

★★ `twoScale_div_bound` (the pointwise quantitative estimate: an explicit smallness threshold `δ`
on `|x| g` and constant `C` depending only on `(J, c, C_ab, K_A, K_B)`) and
★★ `twoScale_div_isBigO`: if `A = Σ_{j<J} a_j x^j + O(x^J g)`, `B = Σ_{j<J} b_j x^j + O(x^J g)`,
`|a_j|, |b_j| ≤ C g`, `|b_0| ≥ c > 0`, and `x g → 0`, then with the pointwise quotient blocks
`R_j = quotientBlocks (a_· ) (b_·) j` (`QuotientBlocks`)

  `A/B − Σ_{j<J} R_j x^j = O(x^J g^{J+1})`.

Route (consult #159, B(ii)):
`Σ_{i<J} b_i x^i · Σ_{j<J} R_j x^j = Σ_{k<J} a_k x^k + (terms x^k, k ≥ J)`
exactly (`sum_mul_sum_quotientBlocks_eq`, from `sum_mul_quotientBlocks`); the blocks are bounded by
`M g^{j+1}` with `M = M(c, C, j)` uniform (`exists_bound_quotientBlocks`); `B/b_0 → 1` because power
decay beats the block growth, giving `|B| ≥ c/2` eventually.  The exponent `(J+1)` on `g` is
deliberately coarse.  The blocks are kept exact (rational in `log n`); their inverse-log expansion
is `RationalExpansionAtInfinity`.

Zero `sorry`/`axiom`.
-/

open Filter Topology Asymptotics Finset

namespace Grammar

/-- Uniform bounds on the quotient blocks: `|R_i| ≤ M g^{i+1}` for `i ≤ j` with `M = M(c, C, j)`
independent of the sequences. -/
theorem exists_bound_quotientBlocks (c Cab : ℝ) (hc : 0 < c) (hCab : 0 ≤ Cab) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a b : ℕ → ℝ) (g : ℝ), 1 ≤ g → c ≤ |b 0| →
      (∀ i ≤ j, |a i| ≤ Cab * g ∧ |b i| ≤ Cab * g) →
      ∀ i ≤ j, |quotientBlocks a b i| ≤ M * g ^ (i + 1) := by
  induction j with
  | zero =>
    refine ⟨Cab / c, div_nonneg hCab hc.le, fun a b g hg hb0 hab i hi => ?_⟩
    rw [Nat.le_zero.1 hi]
    have hb : b 0 ≠ 0 := fun h => by
      rw [h, abs_zero] at hb0
      linarith
    have hg0 : 0 < g := by linarith
    rw [quotientBlocks_zero a b hb, abs_div, pow_one]
    calc |a 0| / |b 0| ≤ (Cab * g) / c :=
          div_le_div₀ (mul_nonneg hCab hg0.le) (hab 0 le_rfl).1 hc hb0
      _ = Cab / c * g := by ring
  | succ j ih =>
    obtain ⟨M, hM, hMb⟩ := ih
    refine ⟨max M (Cab / c * (1 + (j + 1) * M)), le_max_of_le_left hM,
      fun a b g hg hb0 hab i hi => ?_⟩
    have hb : b 0 ≠ 0 := fun h => by
      rw [h, abs_zero] at hb0
      linarith
    have hg0 : 0 < g := by linarith
    have hCg : 0 ≤ Cab * g := mul_nonneg hCab hg0.le
    have hprev := hMb a b g hg hb0 fun i hi => hab i (by omega)
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · calc |quotientBlocks a b i| ≤ M * g ^ (i + 1) := hprev i (by omega)
        _ ≤ max M (Cab / c * (1 + (j + 1) * M)) * g ^ (i + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg0.le _)
    · have hi' : i = j + 1 := le_antisymm hi hge
      subst hi'
      rw [quotientBlocks_succ a b hb j, abs_div]
      have hterm : ∀ i ∈ range (j + 1),
          |b (i + 1) * quotientBlocks a b (j - i)| ≤ Cab * g * (M * g ^ (j + 1)) := by
        intro i hi
        have hi1 : i + 1 ≤ j + 1 := by
          have := mem_range.1 hi
          omega
        rw [abs_mul]
        refine mul_le_mul (hab (i + 1) hi1).2 ?_ (abs_nonneg _) hCg
        calc |quotientBlocks a b (j - i)| ≤ M * g ^ (j - i + 1) := hprev (j - i) (by omega)
          _ ≤ M * g ^ (j + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg (by omega)) hM
      have hsum : |∑ i ∈ range (j + 1), b (i + 1) * quotientBlocks a b (j - i)| ≤
          (j + 1) * (Cab * g * (M * g ^ (j + 1))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h := Finset.sum_le_card_nsmul _ _ _ hterm
        rw [card_range, nsmul_eq_mul] at h
        exact_mod_cast h
      have hnum : |a (j + 1) - ∑ i ∈ range (j + 1), b (i + 1) * quotientBlocks a b (j - i)| ≤
          Cab * g * (1 + (j + 1) * M) * g ^ (j + 1) := by
        calc |a (j + 1) - ∑ i ∈ range (j + 1), b (i + 1) * quotientBlocks a b (j - i)|
            ≤ |a (j + 1)| + |∑ i ∈ range (j + 1), b (i + 1) * quotientBlocks a b (j - i)| :=
              abs_sub _ _
          _ ≤ Cab * g + (j + 1) * (Cab * g * (M * g ^ (j + 1))) :=
              add_le_add (hab (j + 1) le_rfl).1 hsum
          _ ≤ Cab * g * g ^ (j + 1) + (j + 1) * (Cab * g * (M * g ^ (j + 1))) :=
              add_le_add (le_mul_of_one_le_right hCg (one_le_pow₀ hg)) le_rfl
          _ = Cab * g * (1 + (j + 1) * M) * g ^ (j + 1) := by ring
      have hpos : 0 ≤ Cab * g * (1 + (j + 1) * M) * g ^ (j + 1) := by
        have h1 : (0 : ℝ) ≤ 1 + (j + 1) * M := by
          have : (0 : ℝ) ≤ (j + 1) * M := mul_nonneg (by positivity) hM
          linarith
        exact mul_nonneg (mul_nonneg hCg h1) (pow_nonneg hg0.le _)
      calc |a (j + 1) - ∑ i ∈ range (j + 1), b (i + 1) * quotientBlocks a b (j - i)| / |b 0|
          ≤ (Cab * g * (1 + (j + 1) * M) * g ^ (j + 1)) / c := div_le_div₀ hpos hnum hc hb0
        _ = Cab / c * (1 + (j + 1) * M) * g ^ (j + 1 + 1) := by
            field_simp
            ring
        _ ≤ max M (Cab / c * (1 + (j + 1) * M)) * g ^ (j + 1 + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hg0.le _)

/-- **Exact product of the truncated denominator and the truncated quotient**: the terms of
degree `< J` reproduce the numerator blocks; the rest is an explicit finite sum of `x^k`,
`k ≥ J`. -/
theorem sum_mul_sum_quotientBlocks_eq (a b : ℕ → ℝ) (hb : b 0 ≠ 0) (x : ℝ) (J : ℕ) :
    (∑ i ∈ range J, b i * x ^ i) * (∑ j ∈ range J, quotientBlocks a b j * x ^ j) =
      ∑ k ∈ range J, a k * x ^ k + ∑ k ∈ Ico J (2 * J),
        (∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          b p.1 * quotientBlocks a b p.2) * x ^ k := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product' (range J) (range J)
    (fun i j => b i * x ^ i * (quotientBlocks a b j * x ^ j))]
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
    have hfib : (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k) = antidiagonal k := by
      ext p
      simp only [mem_filter, mem_product, mem_range, mem_antidiagonal]
      omega
    rw [hfib, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_mul_quotientBlocks a b hb k,
      Finset.sum_mul]
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

/-- ★★ **Quantitative two-scale division**: for the parameters `(J, c, Cab, KA, KB)` there are a
threshold `δ > 0` and a constant `C` such that whenever `1 ≤ g`, `|x| g ≤ δ`, the blocks are
bounded by `Cab g`, `|b_0| ≥ c`, and the two remainders are bounded by `KA |x|^J g`, `KB |x|^J g`,
then `|A/B − Σ_{j<J} R_j x^j| ≤ C |x|^J g^{J+1}` with the pointwise quotient blocks `R_j`. -/
theorem twoScale_div_bound {J : ℕ} (hJ : 1 ≤ J) {c Cab KA KB : ℝ} (hc : 0 < c) (hCab : 0 ≤ Cab)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (A B x g : ℝ) (a b : ℕ → ℝ), 1 ≤ g → |x| * g ≤ δ →
      (∀ j < J, |a j| ≤ Cab * g ∧ |b j| ≤ Cab * g) → c ≤ |b 0| →
      |A - ∑ j ∈ range J, a j * x ^ j| ≤ KA * (|x| ^ J * g) →
      |B - ∑ j ∈ range J, b j * x ^ j| ≤ KB * (|x| ^ J * g) →
      |A / B - ∑ j ∈ range J, quotientBlocks a b j * x ^ j| ≤ C * (|x| ^ J * g ^ (J + 1)) := by
  obtain ⟨M, hM, hMb⟩ := exists_bound_quotientBlocks c Cab hc hCab (J - 1)
  have hJC : (0 : ℝ) ≤ J * Cab := mul_nonneg (Nat.cast_nonneg _) hCab
  have hC0 : 0 ≤ 2 / c * (KA + KB * J * M + J ^ 3 * Cab * M) := by
    have h1 : 0 ≤ KB * J * M := mul_nonneg (mul_nonneg hKB (Nat.cast_nonneg _)) hM
    have h2 : (0 : ℝ) ≤ J ^ 3 * Cab * M := mul_nonneg (mul_nonneg (by positivity) hCab) hM
    exact mul_nonneg (div_nonneg two_pos.le hc.le) (by linarith)
  refine ⟨min 1 (c / (2 * (KB + J * Cab + 1))), 2 / c * (KA + KB * J * M + J ^ 3 * Cab * M),
    lt_min one_pos (div_pos hc (by linarith)), hC0, ?_⟩
  intro A B x g a b hgN hxgN habN hb0N hKAb hKBb
  have hδ1 : min 1 (c / (2 * (KB + J * Cab + 1))) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (c / (2 * (KB + J * Cab + 1))) ≤ c / (2 * (KB + J * Cab + 1)) :=
    min_le_right _ _
  have hgN0 : 0 < g := by linarith
  have hgJ : 0 < g ^ J := pow_pos hgN0 _
  have hxa : 0 ≤ |x| := abs_nonneg _
  have hx1 : |x| ≤ 1 := by
    calc |x| ≤ |x| * g := le_mul_of_one_le_right hxa hgN
      _ ≤ 1 := hxgN.trans hδ1
  have hxc : |x| * g ≤ c / (2 * (KB + J * Cab + 1)) := hxgN.trans hδ2
  have hbne : b 0 ≠ 0 := fun h => by
    rw [h, abs_zero] at hb0N
    linarith
  -- the quotient blocks and their bounds
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, R = quotientBlocks a b := ⟨_, rfl⟩
  have hRb : ∀ j < J, |R j| ≤ M * g ^ J := by
    intro j hj
    rw [hR]
    have h1 := hMb a b g hgN hb0N (fun i hi => habN i (by omega)) j (by omega)
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hgN (by omega)) hM)
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range J, R j * x ^ j := ⟨_, rfl⟩
  obtain ⟨SA, hSA⟩ : ∃ SA, SA = ∑ j ∈ range J, a j * x ^ j := ⟨_, rfl⟩
  obtain ⟨SB, hSB⟩ : ∃ SB, SB = ∑ j ∈ range J, b j * x ^ j := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ k ∈ Ico J (2 * J),
    (∑ p ∈ (range J ×ˢ range J).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
      b p.1 * R p.2) * x ^ k := ⟨_, rfl⟩
  have hprod : SB * S = SA + E := by
    rw [hSB, hS, hSA, hE, hR]
    exact sum_mul_sum_quotientBlocks_eq a b hbne x J
  rw [← hSA] at hKAb
  rw [← hSB] at hKBb
  -- bounds on the pieces
  have hSb : |S| ≤ J * (M * g ^ J) := by
    rw [hS]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := Finset.sum_le_card_nsmul (range J) (fun j => |R j * x ^ j|) (M * g ^ J)
      fun j hj => by
        rw [abs_mul, abs_pow]
        calc |R j| * |x| ^ j ≤ M * g ^ J * 1 :=
              mul_le_mul (hRb j (mem_range.1 hj)) (pow_le_one₀ hxa hx1) (pow_nonneg hxa _)
                (mul_nonneg hM hgJ.le)
          _ = M * g ^ J := mul_one _
    rw [card_range, nsmul_eq_mul] at h
    exact h
  have hCg : 0 ≤ Cab * g := mul_nonneg hCab hgN0.le
  have hEb : |E| ≤ J * (J * J * (Cab * g * (M * g ^ J)) * |x| ^ J) := by
    rw [hE]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _
      (J * J * (Cab * g * (M * g ^ J)) * |x| ^ J) fun k hk => ?_).trans ?_)
    · have hkJ : J ≤ k := (mem_Ico.1 hk).1
      rw [abs_mul, abs_pow]
      refine mul_le_mul ?_ (pow_le_pow_of_le_one hxa hx1 hkJ) (pow_nonneg hxa _) ?_
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h := Finset.sum_le_card_nsmul ((range J ×ˢ range J).filter
          (fun p : ℕ × ℕ => p.1 + p.2 = k)) (fun p => |b p.1 * R p.2|)
          (Cab * g * (M * g ^ J)) fun p hp => by
            have hp' := mem_product.1 (mem_filter.1 hp).1
            rw [abs_mul]
            exact mul_le_mul (habN p.1 (mem_range.1 hp'.1)).2 (hRb p.2 (mem_range.1 hp'.2))
              (abs_nonneg _) hCg
        rw [nsmul_eq_mul] at h
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCg (mul_nonneg hM hgJ.le)))
        have hcard := Finset.card_filter_le (range J ×ˢ range J) (fun p : ℕ × ℕ => p.1 + p.2 = k)
        rw [card_product, card_range] at hcard
        exact_mod_cast hcard
      · exact mul_nonneg (by positivity) (mul_nonneg hCg (mul_nonneg hM hgJ.le))
    · rw [Nat.card_Ico, nsmul_eq_mul, show 2 * J - J = J by omega]
  -- the denominator is bounded below
  have hSB0 : SB - b 0 = ∑ j ∈ Ico 1 J, b j * x ^ j := by
    rw [hSB, ← Finset.sum_range_add_sum_Ico _ hJ, Finset.sum_range_one, pow_zero, mul_one]
    ring
  have hIco : |∑ j ∈ Ico 1 J, b j * x ^ j| ≤ J * (Cab * g * |x|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := Finset.sum_le_card_nsmul (Ico 1 J) (fun j => |b j * x ^ j|) (Cab * g * |x|)
      fun j hj => by
        have hj' := mem_Ico.1 hj
        rw [abs_mul, abs_pow]
        refine mul_le_mul (habN j hj'.2).2 ?_ (pow_nonneg hxa _) hCg
        calc |x| ^ j ≤ |x| ^ 1 := pow_le_pow_of_le_one hxa hx1 hj'.1
          _ = |x| := pow_one _
    rw [Nat.card_Ico, nsmul_eq_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCg hxa))
    exact_mod_cast Nat.sub_le J 1
  have hxJ1 : |x| ^ J ≤ |x| := by
    calc |x| ^ J ≤ |x| ^ 1 := pow_le_pow_of_le_one hxa hx1 hJ
      _ = |x| := pow_one _
  have hxg0 : 0 ≤ |x| * g := mul_nonneg hxa hgN0.le
  have hBlow : c / 2 ≤ |B| := by
    have h1 : |B - b 0| ≤ (KB + J * Cab + 1) * (|x| * g) := by
      calc |B - b 0| = |(B - SB) + (SB - b 0)| := by ring_nf
        _ ≤ |B - SB| + |SB - b 0| := abs_add_le _ _
        _ ≤ KB * (|x| ^ J * g) + J * (Cab * g * |x|) := by
            rw [hSB0]
            exact add_le_add hKBb hIco
        _ ≤ KB * (|x| * g) + J * Cab * (|x| * g) := by
            refine add_le_add ?_ (le_of_eq (by ring))
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxJ1 hgN0.le) hKB
        _ = (KB + J * Cab) * (|x| * g) := by ring
        _ ≤ (KB + J * Cab + 1) * (|x| * g) :=
            mul_le_mul_of_nonneg_right (by linarith) hxg0
    have h2 : (KB + J * Cab + 1) * (|x| * g) ≤ c / 2 := by
      have hpos : 0 < KB + J * Cab + 1 := by linarith
      calc (KB + J * Cab + 1) * (|x| * g)
          ≤ (KB + J * Cab + 1) * (c / (2 * (KB + J * Cab + 1))) :=
            mul_le_mul_of_nonneg_left hxc hpos.le
        _ = c / 2 := by
            field_simp
    have h3 := abs_sub_abs_le_abs_sub (b 0) B
    rw [abs_sub_comm] at h3
    linarith
  have hBne : B ≠ 0 := fun h => by
    rw [h, abs_zero] at hBlow
    linarith
  -- assemble
  have hkey : A - B * S = (A - SA) - (B - SB) * S - E := by
    linear_combination (-1 : ℝ) * hprod
  have hgJ1 : g * g ^ J = g ^ (J + 1) := by ring
  have hgle : g ≤ g ^ (J + 1) := by
    calc g = g ^ 1 := (pow_one _).symm
      _ ≤ g ^ (J + 1) := pow_le_pow_right₀ hgN (by omega)
  have hxJg : 0 ≤ |x| ^ J := pow_nonneg hxa _
  have hnum : |A - B * S| ≤
      (KA + KB * J * M + J ^ 3 * Cab * M) * (|x| ^ J * g ^ (J + 1)) := by
    calc |A - B * S| = |(A - SA) - (B - SB) * S - E| := by rw [hkey]
      _ ≤ |A - SA| + |B - SB| * |S| + |E| := by
          have h1 := abs_sub ((A - SA) - (B - SB) * S) E
          have h2 := abs_sub (A - SA) ((B - SB) * S)
          rw [abs_mul] at h2
          linarith
      _ ≤ KA * (|x| ^ J * g) + KB * (|x| ^ J * g) * (J * (M * g ^ J)) +
            J * (J * J * (Cab * g * (M * g ^ J)) * |x| ^ J) := by
          refine add_le_add (add_le_add hKAb ?_) hEb
          exact mul_le_mul hKBb hSb (abs_nonneg _)
            (mul_nonneg hKB (mul_nonneg hxJg hgN0.le))
      _ ≤ KA * (|x| ^ J * g ^ (J + 1)) + KB * J * M * (|x| ^ J * g ^ (J + 1)) +
            J ^ 3 * Cab * M * (|x| ^ J * g ^ (J + 1)) := by
          refine add_le_add (add_le_add ?_ (le_of_eq ?_)) (le_of_eq ?_)
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgle hxJg) hKA
          · rw [← hgJ1]
            ring
          · rw [← hgJ1]
            ring
      _ = (KA + KB * J * M + J ^ 3 * Cab * M) * (|x| ^ J * g ^ (J + 1)) := by ring
  have hdiv : A / B - S = (A - B * S) / B := by
    rw [eq_div_iff hBne, sub_mul, div_mul_cancel₀ _ hBne]
    ring
  have hSgoal : ∑ j ∈ range J, quotientBlocks a b j * x ^ j = S := by
    rw [hS, hR]
  rw [hSgoal, hdiv, abs_div]
  calc |A - B * S| / |B| ≤ |A - B * S| / (c / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (half_pos hc) hBlow
    _ ≤ ((KA + KB * J * M + J ^ 3 * Cab * M) * (|x| ^ J * g ^ (J + 1))) / (c / 2) :=
        div_le_div_of_nonneg_right hnum (half_pos hc).le
    _ = 2 / c * (KA + KB * J * M + J ^ 3 * Cab * M) * (|x| ^ J * g ^ (J + 1)) := by
        field_simp

/-- ★★ **Two-scale division**: `A/B − Σ_{j<J} R_j x^j = O(x^J g^{J+1})` for the pointwise quotient
blocks `R_j` of the block coefficients. -/
theorem twoScale_div_isBigO {A B x g : ℝ → ℝ} {a b : ℕ → ℝ → ℝ} {J : ℕ} (hJ : 1 ≤ J)
    {c Cab : ℝ} (hc : 0 < c) (hCab : 0 ≤ Cab)
    (hg : ∀ᶠ N in atTop, 1 ≤ g N)
    (hxg : Tendsto (fun N => x N * g N) atTop (𝓝 0))
    (hab : ∀ᶠ N in atTop, ∀ j < J, |a j N| ≤ Cab * g N ∧ |b j N| ≤ Cab * g N)
    (hb0 : ∀ᶠ N in atTop, c ≤ |b 0 N|)
    (hA : (fun N => A N - ∑ j ∈ range J, a j N * x N ^ j) =O[atTop] fun N => x N ^ J * g N)
    (hB : (fun N => B N - ∑ j ∈ range J, b j N * x N ^ j) =O[atTop] fun N => x N ^ J * g N) :
    (fun N => A N / B N -
        ∑ j ∈ range J, quotientBlocks (fun i => a i N) (fun i => b i N) j * x N ^ j)
      =O[atTop] fun N => x N ^ J * g N ^ (J + 1) := by
  obtain ⟨KA, hKA⟩ := hA.bound
  obtain ⟨KB, hKB⟩ := hB.bound
  obtain ⟨δ, C, hδ, hC0, hbound⟩ :=
    twoScale_div_bound hJ hc hCab (le_max_right KA 0) (le_max_right KB 0)
  have hev : ∀ᶠ N in atTop, |x N * g N| ≤ δ :=
    hxg.abs.eventually_le_const (by simpa using hδ)
  refine IsBigO.of_bound C ?_
  filter_upwards [hg, hab, hb0, hKA, hKB, hev] with N hgN habN hb0N hKAN hKBN hevN
  have hgN0 : 0 < g N := by linarith
  have hxg0 : 0 ≤ |x N| ^ J * g N := mul_nonneg (pow_nonneg (abs_nonneg _) _) hgN0.le
  rw [abs_mul, abs_of_pos hgN0] at hevN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hgN0] at hKAN hKBN
  have hKAN' : |A N - ∑ j ∈ range J, a j N * x N ^ j| ≤ max KA 0 * (|x N| ^ J * g N) :=
    hKAN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxg0)
  have hKBN' : |B N - ∑ j ∈ range J, b j N * x N ^ j| ≤ max KB 0 * (|x N| ^ J * g N) :=
    hKBN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxg0)
  have h := hbound (A N) (B N) (x N) (g N) (fun i => a i N) (fun i => b i N) hgN hevN habN hb0N
    hKAN' hKBN'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (pow_pos hgN0 _)]
  exact h

end Grammar
