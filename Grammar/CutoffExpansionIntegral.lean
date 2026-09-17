/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SmoothAssemblyAlgebra
import Grammar.TailPowerLog

/-!
# Integrating a cutoff expansion

If `Z̃` has a cutoff expansion with coefficients `c̃` and no terms at exponents `≤ 1`, then
`Z(N) = ∫_N^∞ Z̃` has a cutoff expansion with coefficients
`intCoeff D c̃ μ i = Σ_q c̃ (μ+1) q · tailLogCoeff μ q i` (`CutoffExpansion.integral_Ioi`), and
these satisfy the exact shift recursion
`c̃ (μ+1) q = μ · intCoeff μ q − (q+1) · intCoeff μ (q+1)` (`intCoeff_shift`).  This is the
analytic half of the monomial-shift identity for the population
coefficients: the coefficients of `u^{2k} A` at exponent `μ+1` are read off those of `A` at `μ`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset

namespace Grammar

open SmoothEngine

/-- The coefficients of the integrated expansion. -/
noncomputable def intCoeff (D : ℕ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (i : ℕ) : ℝ :=
  ∑ q ∈ range (D + 1), c (μ + 1) q * tailLogCoeff μ q i

/-- ★ **The shift recursion**:
`c̃ (μ+1) q = μ · intCoeff μ q − (q+1) · intCoeff μ (q+1)`. -/
theorem intCoeff_shift {D : ℕ} (c : ℝ → ℕ → ℝ) {μ : ℝ} (hμ : 0 < μ) {q : ℕ} (hq : q ≤ D) :
    μ * intCoeff D c μ q - (q + 1) * intCoeff D c μ (q + 1) = c (μ + 1) q := by
  unfold intCoeff
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  have hterm : ∀ q' ∈ range (D + 1),
      μ * (c (μ + 1) q' * tailLogCoeff μ q' q) - (q + 1) * (c (μ + 1) q' * tailLogCoeff μ q'
(q + 1))
        = if q = q' then c (μ + 1) q' else 0 := fun q' _ => by
    have := tailLogCoeff_inv hμ q' q
    split_ifs with hqq
    · subst hqq
      rw [if_pos rfl] at this
      linear_combination c (μ + 1) q * this
    · rw [if_neg hqq] at this
      linear_combination c (μ + 1) q' * this
  rw [sum_congr rfl hterm, sum_ite_eq]
  rw [if_pos (mem_range.2 (Nat.lt_succ_of_le hq))]

/-- The top-order coefficient of the integrated expansion vanishes above `D`. -/
theorem intCoeff_eq_zero_of_lt {D : ℕ} (c : ℝ → ℕ → ℝ) (μ : ℝ) {i : ℕ} (hi : D < i) :
    intCoeff D c μ i = 0 := by
  unfold intCoeff
  refine sum_eq_zero fun q hq => ?_
  have : ¬ i ≤ q := by
    have := mem_range.1 hq
    omega
  simp [tailLogCoeff, this]

/-- The tail integral of a term of the spectral sum at an exponent `μ' > 1`. -/
theorem integral_rpow_neg_mul_log_pow_Ioi' {μ' : ℝ} (hμ : 1 < μ') (q : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in Ioi N, t ^ (-μ') * Real.log t ^ q =
      N ^ (-(μ' - 1)) * ∑ i ∈ range (q + 1), tailLogCoeff (μ' - 1) q i * Real.log N ^ i := by
  have := integral_rpow_neg_mul_log_pow_Ioi (sub_pos.2 hμ) q hN
  rwa [show -(μ' - 1) - 1 = -μ' by ring] at this

theorem integrableOn_rpow_neg_mul_log_pow_Ioi' {μ' : ℝ} (hμ : 1 < μ') (q : ℕ) {N : ℝ}
    (hN : 1 ≤ N) : IntegrableOn (fun t : ℝ => t ^ (-μ') * Real.log t ^ q) (Ioi N) := by
  have := integrableOn_rpow_neg_mul_log_pow_Ioi (sub_pos.2 hμ) q hN
  rwa [show -(μ' - 1) - 1 = -μ' by ring] at this


/-- A cutoff expansion is a property of the germ at `∞`. -/
theorem CutoffExpansion.congr_eventually {Q D : ℕ} {Z W : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) (hZW : Z =ᶠ[atTop] W) : CutoffExpansion Q D W c := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨K, ?_⟩
  filter_upwards [hK, hZW] with N hN hN'
  rwa [← hN']

/-- A continuous function with a cutoff expansion without terms at exponents `≤ 1` is eventually
integrable on `(N, ∞)`. -/
theorem CutoffExpansion.eventually_integrableOn_Ioi {Q D : ℕ} (hQ : 0 < Q) {Zt : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Zt c) (hcont : Continuous Zt)
    (hlow : ∀ m : ℕ, (m : ℝ) / Q ≤ 1 → ∀ q ≤ D, c ((m : ℝ) / Q) q = 0) :
    ∀ᶠ N in atTop, IntegrableOn Zt (Ioi N) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨K, hK⟩ := h 2 two_pos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hK
  have hinj : ∀ s : Finset ℕ, Set.InjOn (fun m : ℕ => (m : ℝ) / Q) s := fun s m _ m' _ hmm => by
    have := (div_left_inj' hQ'.ne').1 hmm
    exact_mod_cast this
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  -- the spectral sum at cutoff `2` as a double sum
  have hS : ∀ t : ℝ, absSpectralSum Q D c 2 t = ∑ m ∈ range ⌈(2 : ℝ) * Q⌉₊,
      ∑ q ∈ range (D + 1), c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q) :=
    fun t => by
    unfold absSpectralSum latticeBelow
    rw [sum_image (hinj _)]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    ring
  have hgint : ∀ (m q : ℕ), q ≤ D → IntegrableOn
      (fun t : ℝ => c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q)) (Ioi N) := by
    intro m q hq
    by_cases hm : 1 < (m : ℝ) / Q
    · exact (integrableOn_rpow_neg_mul_log_pow_Ioi' hm q hN1).const_mul _
    · have : (fun t : ℝ => c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q)) =
          fun _ => 0 := by
        funext t
        simp only [hlow m (not_lt.1 hm) q hq, zero_mul]
      rw [this]
      exact integrable_zero _ _ _
  have hSint : IntegrableOn (absSpectralSum Q D c 2) (Ioi N) := by
    rw [show absSpectralSum Q D c 2 = fun t => ∑ m ∈ range ⌈(2 : ℝ) * Q⌉₊, ∑ q ∈ range (D + 1),
      c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q) from funext hS]
    exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q hq =>
      hgint m q (Nat.lt_succ_iff.1 (mem_range.1 hq))
  have hScont : ContinuousOn (absSpectralSum Q D c 2) (Ioi N) := by
    rw [show absSpectralSum Q D c 2 = fun t => ∑ m ∈ range ⌈(2 : ℝ) * Q⌉₊, ∑ q ∈ range (D + 1),
      c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q) from funext hS]
    refine continuousOn_finsetSum _ fun m _ => continuousOn_finsetSum _ fun q _ => ?_
    refine continuousOn_const.mul (ContinuousOn.mul (fun t ht => ?_) ?_)
    · exact (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [mem_Ioi.1 ht]))).continuousWithinAt
    · exact (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ioi.1 ht]).pow q
  have hR : IntegrableOn (fun t => Zt t - absSpectralSum Q D c 2 t) (Ioi N) := by
    refine Integrable.mono'
      ((integrableOn_rpow_neg_mul_one_add_log_pow_Ioi (L := 2) (by norm_num) D hN1).const_mul K)
      ?_ ?_
    · exact (hcont.continuousOn.sub hScont).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact hN₀ t (hNN₀.trans (mem_Ioi.1 ht).le)
  have := hR.add hSint
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp

/-- ★★ **Integrating a cutoff expansion**: if `Z̃` has a cutoff expansion without terms at exponents
`≤ 1`, then `N ↦ ∫_N^∞ Z̃` has the cutoff expansion with coefficients `intCoeff D c̃`. -/
theorem CutoffExpansion.integral_Ioi {Q D : ℕ} (hQ : 0 < Q) {Zt : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Zt c) (hcont : Continuous Zt)
    (hlow : ∀ m : ℕ, (m : ℝ) / Q ≤ 1 → ∀ q ≤ D, c ((m : ℝ) / Q) q = 0) :
    CutoffExpansion Q D (fun N => ∫ t in Ioi N, Zt t) (intCoeff D c) := by
  intro L hL
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨K, hK⟩ := h (L + 2) (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hK
  have hK0 : 0 ≤ K := by
    have h1 := hN₀ (max N₀ 1) (le_max_left _ _)
    have hpos : 0 < (max N₀ 1 : ℝ) ^ (-(L + 2)) * (1 + Real.log (max N₀ 1)) ^ D := by
      have : (1 : ℝ) ≤ max N₀ 1 := le_max_right _ _
      have := Real.log_nonneg this
      positivity
    by_contra hneg
    have := (abs_nonneg _).trans h1
    nlinarith
  -- the index sets
  set A : ℕ := ⌈(L + 1) * Q⌉₊ with hA
  have hceil : ⌈(L + 2) * Q⌉₊ = A + Q := by
    have := Nat.ceil_add_natCast (a := (L + 1) * (Q : ℝ)) (by positivity) Q
    rw [hA, ← this]
    congr 1
    ring
  have hinj : ∀ s : Finset ℕ, Set.InjOn (fun m : ℕ => (m : ℝ) / Q) s := fun s m _ m' _ hmm => by
    have := (div_left_inj' hQ'.ne').1 hmm
    exact_mod_cast this
  -- the term functions
  set g : ℕ → ℕ → ℝ → ℝ := fun m q t => c ((m : ℝ) / Q) q * (t ^ (-((m : ℝ) / Q)) * Real.log t ^ q)
    with hg
  have hS : ∀ t : ℝ, absSpectralSum Q D c (L + 2) t = ∑ m ∈ range (A + Q), ∑ q ∈ range (D + 1),
      g m q t := fun t => by
    unfold absSpectralSum latticeBelow
    rw [sum_image (hinj _), hceil]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    simp only [hg]
    ring
  -- integrability and integrals of the terms, for `N ≥ 1`
  have hgint : ∀ {N : ℝ}, 1 ≤ N → ∀ (m q : ℕ), q ≤ D → IntegrableOn (g m q) (Ioi N) :=
    fun {N} hN m q hq => by
    by_cases hm : 1 < (m : ℝ) / Q
    · exact (integrableOn_rpow_neg_mul_log_pow_Ioi' hm q hN).const_mul _
    · have : g m q = fun _ => 0 := by
        funext t
        simp only [hg, hlow m (not_lt.1 hm) q hq, zero_mul]
      rw [this]
      exact integrable_zero _ _ _
  have hgval : ∀ {N : ℝ}, 1 ≤ N → ∀ m ∈ range A, ∀ q ≤ D,
      ∫ t in Ioi N, g (Q + m) q t = c ((m : ℝ) / Q + 1) q *
        (N ^ (-((m : ℝ) / Q)) * ∑ i ∈ range (q + 1), tailLogCoeff ((m : ℝ) / Q) q i *
          Real.log N ^ i) := fun {N} hN m _ q hq => by
    have hcast : (((Q + m : ℕ) : ℝ) / Q) = (m : ℝ) / Q + 1 := by
      push_cast
      field_simp
      ring
    simp only [hg, integral_const_mul, hcast]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have h1 : c 1 q = 0 := by
        have := hlow Q (by rw [div_self hQ'.ne']) q hq
        rwa [div_self hQ'.ne'] at this
      simp only [Nat.cast_zero, zero_div, zero_add, h1, zero_mul]
    · have hm : 1 < (m : ℝ) / Q + 1 := by
        have : (0 : ℝ) < (m : ℝ) / Q := by positivity
        linarith
      rw [integral_rpow_neg_mul_log_pow_Ioi' hm q hN, add_sub_cancel_right]
  -- the integrated spectral sum equals the target spectral sum
  have htarget : ∀ {N : ℝ}, 1 ≤ N →
      ∫ t in Ioi N, absSpectralSum Q D c (L + 2) t =
        absSpectralSum Q D (intCoeff D c) (L + 1) N := fun {N} hN => by
    have hint : ∀ m ∈ range (A + Q), Integrable (fun t => ∑ q ∈ range (D + 1), g m q t)
        (volume.restrict (Ioi N)) := fun m _ =>
      integrable_finsetSum _ fun q hq => hgint hN m q (Nat.lt_succ_iff.1 (mem_range.1 hq))
    calc ∫ t in Ioi N, absSpectralSum Q D c (L + 2) t
        = ∑ m ∈ range (A + Q), ∑ q ∈ range (D + 1), ∫ t in Ioi N, g m q t := by
          rw [show (fun t => absSpectralSum Q D c (L + 2) t) = fun t =>
            ∑ m ∈ range (A + Q), ∑ q ∈ range (D + 1), g m q t from funext hS]
          rw [integral_finsetSum _ hint]
          exact sum_congr rfl fun m _ => integral_finsetSum _ fun q hq =>
            hgint hN m q (Nat.lt_succ_iff.1 (mem_range.1 hq))
      _ = ∑ m ∈ range A, ∑ q ∈ range (D + 1), ∫ t in Ioi N, g (Q + m) q t := by
          rw [add_comm A Q, sum_range_add]
          have hzero : ∑ m ∈ range Q, ∑ q ∈ range (D + 1), ∫ t in Ioi N, g m q t = 0 := by
            refine sum_eq_zero fun m hm => sum_eq_zero fun q _ => ?_
            have hle : (m : ℝ) / Q ≤ 1 := by
              rw [div_le_one hQ']
              exact_mod_cast (mem_range.1 hm).le
            simp only [hg, hlow m hle q (Nat.lt_succ_iff.1 (mem_range.1 ‹q ∈ range (D + 1)›)),
              zero_mul, integral_zero]
          rw [hzero, zero_add]
      _ = absSpectralSum Q D (intCoeff D c) (L + 1) N := by
          unfold absSpectralSum latticeBelow
          rw [sum_image (hinj _)]
          refine sum_congr rfl fun m hm => ?_
          rw [sum_congr rfl fun q hq => hgval hN m hm q (Nat.lt_succ_iff.1 (mem_range.1 hq))]
          unfold intCoeff
          have hext : ∀ q ∈ range (D + 1), c ((m : ℝ) / Q + 1) q * (N ^ (-((m : ℝ) / Q)) *
              ∑ i ∈ range (q + 1), tailLogCoeff ((m : ℝ) / Q) q i * Real.log N ^ i) =
              ∑ i ∈ range (D + 1), N ^ (-((m : ℝ) / Q)) *
                (c ((m : ℝ) / Q + 1) q * tailLogCoeff ((m : ℝ) / Q) q i * Real.log N ^ i) := by
            intro q hq
            have hqD : q + 1 ≤ D + 1 := mem_range.1 hq
            rw [mul_sum, mul_sum]
            refine (sum_congr rfl fun i _ => by ring).trans
              (sum_subset (Finset.range_mono hqD) fun i _ hi => ?_)
            have : ¬ i ≤ q := fun hle => hi (mem_range.2 (Nat.lt_succ_of_le hle))
            simp [tailLogCoeff, this]
          rw [sum_congr rfl hext, mul_sum]
          simp only [sum_mul, mul_sum]
          exact sum_comm
  -- the estimate
  refine ⟨K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) +
    ∑ μ ∈ latticeBelow Q (L + 1), ∑ j ∈ range (D + 1), |intCoeff D c μ j|, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- the spectral sum is continuous on `(N, ∞)`
  have hScont : ContinuousOn (absSpectralSum Q D c (L + 2)) (Ioi N) := by
    rw [show absSpectralSum Q D c (L + 2) = fun t => ∑ m ∈ range (A + Q), ∑ q ∈ range (D + 1),
      g m q t from funext hS]
    refine continuousOn_finsetSum _ fun m _ => continuousOn_finsetSum _ fun q _ => ?_
    refine continuousOn_const.mul (ContinuousOn.mul (fun t ht => ?_) ?_)
    · exact (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [mem_Ioi.1 ht]))).continuousWithinAt
    · exact (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ioi.1 ht]).pow q
  -- the remainder is integrable and small
  have hR : IntegrableOn (fun t => Zt t - absSpectralSum Q D c (L + 2) t) (Ioi N) := by
    refine Integrable.mono'
      ((integrableOn_rpow_neg_mul_one_add_log_pow_Ioi (L := L + 2) (by linarith) D hN1).const_mul K)
      ?_ ?_
    · exact (hcont.continuousOn.sub hScont).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact hN₀ t (hNN₀.trans (mem_Ioi.1 ht).le)
  have hSint : IntegrableOn (absSpectralSum Q D c (L + 2)) (Ioi N) := by
    rw [show absSpectralSum Q D c (L + 2) = fun t => ∑ m ∈ range (A + Q), ∑ q ∈ range (D + 1),
      g m q t from funext hS]
    exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q hq =>
      hgint hN1 m q (Nat.lt_succ_iff.1 (mem_range.1 hq))
  have hsplit : ∫ t in Ioi N, Zt t = (∫ t in Ioi N, (Zt t - absSpectralSum Q D c (L + 2) t)) +
      ∫ t in Ioi N, absSpectralSum Q D c (L + 2) t := by
    rw [← integral_add hR hSint]
    congr 1
    funext t
    ring
  have hrem : |∫ t in Ioi N, (Zt t - absSpectralSum Q D c (L + 2) t)| ≤
      K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) * N ^ (-L) := by
    calc |∫ t in Ioi N, (Zt t - absSpectralSum Q D c (L + 2) t)|
        ≤ ∫ t in Ioi N, K * (t ^ (-(L + 2)) * (1 + Real.log t) ^ D) := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le
            ((integrableOn_rpow_neg_mul_one_add_log_pow_Ioi (L := L + 2) (by linarith) D
              hN1).const_mul K) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
          rw [Real.norm_eq_abs]
          exact hN₀ t (hNN₀.trans (mem_Ioi.1 ht).le)
      _ = K * ∫ t in Ioi N, t ^ (-(L + 2)) * (1 + Real.log t) ^ D := integral_const_mul _ _
      _ ≤ K * ((1 + 2 * D) ^ D * N ^ (-(L + 2) + 3 / 2) / (L + 2 - 3 / 2)) :=
          mul_le_mul_of_nonneg_left
            (integral_rpow_neg_mul_one_add_log_pow_Ioi_le (by linarith) D hN1) hK0
      _ ≤ K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) * N ^ (-L) := by
          have hp : N ^ (-(L + 2) + 3 / 2) ≤ N ^ (-L) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
          have hc : 0 ≤ K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) :=
            div_nonneg (mul_nonneg hK0 (by positivity)) (by linarith)
          calc K * ((1 + 2 * D) ^ D * N ^ (-(L + 2) + 3 / 2) / (L + 2 - 3 / 2))
              = K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) * N ^ (-(L + 2) + 3 / 2) := by ring
            _ ≤ K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) * N ^ (-L) :=
                mul_le_mul_of_nonneg_left hp hc
  have hlow' := absSpectralSum_sub_lower (D := D) hQ (intCoeff D c) (show L ≤ L + 1 by linarith) hN1
  have hone : 1 ≤ (1 + Real.log N) ^ D := one_le_pow₀ (by linarith)
  have hNL : 0 ≤ N ^ (-L) := Real.rpow_nonneg hN0.le _
  calc |(∫ t in Ioi N, Zt t) - absSpectralSum Q D (intCoeff D c) L N|
      = |(∫ t in Ioi N, (Zt t - absSpectralSum Q D c (L + 2) t)) +
          (absSpectralSum Q D (intCoeff D c) (L + 1) N -
            absSpectralSum Q D (intCoeff D c) L N)| := by
        rw [hsplit, htarget hN1]
        ring_nf
    _ ≤ |∫ t in Ioi N, (Zt t - absSpectralSum Q D c (L + 2) t)| +
          |absSpectralSum Q D (intCoeff D c) (L + 1) N -
            absSpectralSum Q D (intCoeff D c) L N| := abs_add_le _ _
    _ ≤ K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) * N ^ (-L) +
          (∑ μ ∈ latticeBelow Q (L + 1), ∑ j ∈ range (D + 1), |intCoeff D c μ j|) *
            (N ^ (-L) * (1 + Real.log N) ^ D) := add_le_add hrem hlow'
    _ ≤ (K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) +
          ∑ μ ∈ latticeBelow Q (L + 1), ∑ j ∈ range (D + 1), |intCoeff D c μ j|) *
            (N ^ (-L) * (1 + Real.log N) ^ D) := by
        have hc : 0 ≤ K * (1 + 2 * D) ^ D / (L + 2 - 3 / 2) :=
          div_nonneg (mul_nonneg hK0 (by positivity)) (by linarith)
        nlinarith [mul_nonneg hc hNL, mul_nonneg (mul_nonneg hc hNL) (sub_nonneg.2 hone)]

end Grammar
