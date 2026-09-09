/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingIsolation
import Grammar.MonomialShiftedMoments

/-!
# Two-term quotient algebra for the energy correction (Programme Q, N2, unit 316)

Abstract analysis for the first logarithmic correction of `E_N[K]`. Write `L = log N`.

* **Remainder at every log scale** (`population_remainder_tendsto_pow`): for a Taylor-tree
  conclusion on the unit box, `(𝒵(N) − N^{-λ} P(L))/(N^{-λ} L^j) → 0` for EVERY `j : ℕ`
  (the cutoff gap `L' = λ + 1/Q > λ` beats any fixed power of `L`); this is the stronger remainder
  control review v39 required for the next-log term (`j = m − 2`). The `m = 1` branch needs the
  MULTIPLICATIVE log version `(𝒵(N) − N^{-λ} P(L)) L^j / N^{-λ} → 0`
  (`population_remainder_tendsto_mul_pow`, same power gap), used at `j = 1`.
* **Two-term quotient, `m ≥ 2`** (`twoTerm_energy_quotient`): if
  `𝒵/(N^{-λ}L^{m−2}) − A L → B` and `𝒵_K/(N^{-(λ+1)}L^{m−2}) − A_K L → B_K` with `A ≠ 0`,
  `A_K = λA/β`, `B_K = (λB − (m−1)A)/β`, then `N L (𝒵_K/𝒵 − λ/(βN)) → −(m−1)/β`.
* **`m = 1` branch** (`oneTerm_energy_quotient`): if `L (𝒵/N^{-λ} − A) → 0` and
  `L (𝒵_K/N^{-(λ+1)} − A_K) → 0` with `A ≠ 0`, `A_K = λA/β`, then `N L (𝒵_K/𝒵 − λ/(βN)) → 0`.

Both quotient lemmas are exact algebra on an eventual set where `N > 1`, `L > 0` and `𝒵 ≠ 0`
(from the normalised limit and `A ≠ 0`), followed by `Tendsto` calculus. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Remainder at every log scale** on the unit box. -/
theorem population_remainder_tendsto_pow (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (j : ℕ) :
    Tendsto (fun N => (familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q) /
        (N ^ (-l) * Real.log N ^ j)) atTop (𝓝 0) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < 1 / latticeQ k := by
    have : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
    positivity
  set L : ℝ := l + 1 / latticeQ k with hLdef
  have hlL : l < L := by rw [hLdef]; linarith
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hL : 0 < L := hl0.trans hlL
  set K : ℝ := cutoffBound n k β L (CoeffFamily.scale cξ 1 0) (CoeffFamily.mass (CoeffFamily.scale
cη 1))
    (CoeffFamily.mass (CoeffFamily.scale cξ 1)) with hK
  have hbound : ∀ N : ℝ, 1 ≤ N →
      |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q| ≤
        |K| * (N ^ (-L) * (1 + Real.log N) ^ n) := by
    intro N hN
    have hrem := hC.remainder L hL N (by linarith) (by rw [boxScale_one]; exact hN)
    rw [boxScale_one, one_pow, one_mul, one_mul,
      spectralSum_isolated n h k hk hmin hatt C hC.vanish N] at hrem
    refine hrem.trans (mul_le_mul_of_nonneg_right (le_abs_self K) ?_)
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
    positivity
  have hmaj : Tendsto (fun N : ℝ => |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l))) atTop
      (𝓝 0) := by
    simpa using (tendsto_cutoff_ratio n hlL).const_mul |K|
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 ≤ N := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hN
  have hNpos : 0 < N := by linarith
  have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos hNpos _
  have hlogpow : 1 ≤ Real.log N ^ j := one_le_pow₀ hlog
  have hden : 0 < N ^ (-l) * Real.log N ^ j := mul_pos hpow (by linarith)
  have hX : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q|
      ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n) := hbound N hN1
    _ = |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l)) * N ^ (-l) := by
        rw [mul_assoc, div_mul_cancel₀ _ hpow.ne']
    _ ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l)) * (N ^ (-l) * Real.log N ^ j) := by
        apply mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hpow.le hlogpow)
        positivity

/-- **Strong remainder**: the cutoff remainder times any power of `log N`, normalised by
`N^{-λ}`, still tends to zero (the power gap beats every logarithm). -/
theorem population_remainder_tendsto_mul_pow (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (j : ℕ) :
    Tendsto (fun N => (familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q) * Real.log N ^ j /
        N ^ (-l)) atTop (𝓝 0) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < 1 / latticeQ k := by
    have : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
    positivity
  set L : ℝ := l + 1 / latticeQ k with hLdef
  have hlL : l < L := by rw [hLdef]; linarith
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hL : 0 < L := hl0.trans hlL
  set K : ℝ := cutoffBound n k β L (CoeffFamily.scale cξ 1 0)
    (CoeffFamily.mass (CoeffFamily.scale cη 1)) (CoeffFamily.mass (CoeffFamily.scale cξ 1)) with hK
  have hbound : ∀ N : ℝ, 1 ≤ N →
      |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q| ≤
        |K| * (N ^ (-L) * (1 + Real.log N) ^ n) := by
    intro N hN
    have hrem := hC.remainder L hL N (by linarith) (by rw [boxScale_one]; exact hN)
    rw [boxScale_one, one_pow, one_mul, one_mul,
      spectralSum_isolated n h k hk hmin hatt C hC.vanish N] at hrem
    refine hrem.trans (mul_le_mul_of_nonneg_right (le_abs_self K) ?_)
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
    positivity
  have hmaj : Tendsto (fun N : ℝ => |K| * (N ^ (-(L - l)) * (1 + Real.log N) ^ (n + j))) atTop
      (𝓝 0) := by
    simpa using (tendsto_rpow_neg_mul_one_add_log_pow (n + j) (sub_pos.2 hlL)).const_mul |K|
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hNpos : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos hNpos _
  have hsub : N ^ (-L) / N ^ (-l) = N ^ (-(L - l)) := by
    rw [show -(L - l) = -L - -l by ring, Real.rpow_sub hNpos]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, abs_mul, abs_pow, abs_of_nonneg hlog,
    div_le_iff₀ hpow]
  calc |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ q ∈ Finset.range (n + 1), C l q * Real.log N ^ q| * Real.log N ^ j
      ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n) * Real.log N ^ j :=
        mul_le_mul_of_nonneg_right (hbound N hN) (by positivity)
    _ ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n) * (1 + Real.log N) ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) j) (by positivity)
    _ = |K| * (N ^ (-(L - l)) * (1 + Real.log N) ^ (n + j)) * N ^ (-l) := by
        rw [← hsub, pow_add]
        field_simp

/-- **Two-term quotient algebra** (`m ≥ 2`): the first logarithmic correction of the energy
ratio. -/
theorem twoTerm_energy_quotient {Z ZK : ℝ → ℝ} {A B AK BK l β : ℝ} {r : ℕ} (hβ : 0 < β) (hA : A ≠ 0)
    (hAK : AK = l * A / β) (hBK : BK = (l * B - ((r : ℝ) + 1) * A) / β)
    (hZ : Tendsto (fun N => Z N / (N ^ (-l) * Real.log N ^ r) - A * Real.log N) atTop (𝓝 B))
    (hZK : Tendsto (fun N => ZK N / (N ^ (-(l + 1)) * Real.log N ^ r) - AK * Real.log N) atTop
      (𝓝 BK)) :
    Tendsto (fun N => N * Real.log N * (ZK N / Z N - l / (β * N))) atTop
      (𝓝 (-((r : ℝ) + 1) / β)) := by
  -- the normalised errors
  set ε : ℝ → ℝ := fun N => Z N / (N ^ (-l) * Real.log N ^ r) - A * Real.log N - B with hε
  set εK : ℝ → ℝ := fun N => ZK N / (N ^ (-(l + 1)) * Real.log N ^ r) - AK * Real.log N - BK
    with hεK
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have := hZ.sub_const B
    simpa [hε] using this
  have hεK0 : Tendsto εK atTop (𝓝 0) := by
    have := hZK.sub_const BK
    simpa [hεK] using this
  have hinvlog : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (𝓝 0) := tendsto_inv_log
  -- the limit expression
  have hlim : Tendsto (fun N => (A * (BK + εK N) - AK * (B + ε N)) /
      (A * (A + (B + ε N) * (Real.log N)⁻¹))) atTop
      (𝓝 ((A * (BK + 0) - AK * (B + 0)) / (A * (A + (B + 0) * 0)))) := by
    refine Tendsto.div ((tendsto_const_nhds.mul (tendsto_const_nhds.add hεK0)).sub
      (tendsto_const_nhds.mul (tendsto_const_nhds.add hε0)))
      (tendsto_const_nhds.mul (tendsto_const_nhds.add
        ((tendsto_const_nhds.add hε0).mul hinvlog))) ?_
    simp [hA]
  have hval : (A * (BK + 0) - AK * (B + 0)) / (A * (A + (B + 0) * 0)) = -((r : ℝ) + 1) / β := by
    rw [hAK, hBK]
    simp only [add_zero, mul_zero]
    rw [div_eq_div_iff (mul_ne_zero hA hA) hβ.ne']
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  -- eventually `Z N ≠ 0` (from the leading term) and the algebra identity
  have hZne : ∀ᶠ N in atTop, Z N ≠ 0 := by
    have hlead : Tendsto (fun N => Z N / (N ^ (-l) * Real.log N ^ (r + 1))) atTop (𝓝 A) := by
      have : Tendsto (fun N => (Z N / (N ^ (-l) * Real.log N ^ r) - A * Real.log N - B) *
          (Real.log N)⁻¹ + A + B * (Real.log N)⁻¹) atTop (𝓝 (0 * 0 + A + B * 0)) :=
        ((hε0.mul hinvlog).add tendsto_const_nhds).add (tendsto_const_nhds.mul hinvlog)
      simp only [mul_zero, zero_add, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp
      ring
    have := hlead.eventually (isOpen_ne.mem_nhds hA)
    filter_upwards [this] with N hN
    intro h0
    apply hN
    simp [h0]
  filter_upwards [hZne, eventually_gt_atTop (1 : ℝ)] with N hZN hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hpowK : N ^ (-(l + 1)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hpow' : N ^ (-(l + 1)) = N ^ (-l) * N⁻¹ := by
    rw [show -(l + 1) = -l + (-1 : ℝ) by ring, Real.rpow_add (by linarith), Real.rpow_neg_one]
  have hN0 : N ≠ 0 := by linarith
  -- express Z and ZK through ε, εK
  have hDdef : A * Real.log N + B + ε N = Z N / (N ^ (-l) * Real.log N ^ r) := by
    simp only [hε]
    ring
  have hZeq : Z N = N ^ (-l) * Real.log N ^ r * (A * Real.log N + B + ε N) := by
    rw [hDdef]
    field_simp
  have hD0 : A * Real.log N + B + ε N ≠ 0 := by
    intro h0
    apply hZN
    rw [hZeq, h0, mul_zero]
  have hDKdef : AK * Real.log N + BK + εK N = ZK N / (N ^ (-(l + 1)) * Real.log N ^ r) := by
    simp only [hεK]
    ring
  have hZKeq : ZK N = N ^ (-(l + 1)) * Real.log N ^ r * (AK * Real.log N + BK + εK N) := by
    rw [hDKdef]
    field_simp
  have hDL : A + (B + ε N) * (Real.log N)⁻¹ = (A * Real.log N + B + ε N) / Real.log N := by
    field_simp
    ring
  rw [hDL, hZeq, hZKeq, hpow', hAK]
  field_simp
  ring

/-- **The `m = 1` branch**: no logarithmic term, correction zero. -/
theorem oneTerm_energy_quotient {Z ZK : ℝ → ℝ} {A AK l β : ℝ} (hβ : 0 < β) (hA : A ≠ 0)
    (hAK : AK = l * A / β)
    (hZ : Tendsto (fun N => Real.log N * (Z N / N ^ (-l) - A)) atTop (𝓝 0))
    (hZK : Tendsto (fun N => Real.log N * (ZK N / N ^ (-(l + 1)) - AK)) atTop (𝓝 0)) :
    Tendsto (fun N => N * Real.log N * (ZK N / Z N - l / (β * N))) atTop (𝓝 0) := by
  set ε : ℝ → ℝ := fun N => Z N / N ^ (-l) - A with hε
  set εK : ℝ → ℝ := fun N => ZK N / N ^ (-(l + 1)) - AK with hεK
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have := hZ.mul tendsto_inv_log
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    simp only [hε]
    field_simp
  have hlim : Tendsto (fun N => (A * (Real.log N * εK N) - AK * (Real.log N * ε N)) /
      (A * (A + ε N))) atTop (𝓝 ((A * 0 - AK * 0) / (A * (A + 0)))) := by
    refine Tendsto.div ((tendsto_const_nhds.mul hZK).sub (tendsto_const_nhds.mul hZ))
      (tendsto_const_nhds.mul (tendsto_const_nhds.add hε0)) ?_
    simp [hA]
  simp only [mul_zero, sub_zero, add_zero, zero_div] at hlim
  refine hlim.congr' ?_
  have hZne : ∀ᶠ N in atTop, Z N ≠ 0 := by
    have hlead : Tendsto (fun N => Z N / N ^ (-l)) atTop (𝓝 A) := by
      have := hε0.add_const A
      simpa [hε] using this
    have := hlead.eventually (isOpen_ne.mem_nhds hA)
    filter_upwards [this] with N hN
    intro h0
    apply hN
    simp [h0]
  filter_upwards [hZne, eventually_gt_atTop (1 : ℝ)] with N hZN hN
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hpow' : N ^ (-(l + 1)) = N ^ (-l) * N⁻¹ := by
    rw [show -(l + 1) = -l + (-1 : ℝ) by ring, Real.rpow_add (by linarith), Real.rpow_neg_one]
  have hN0 : N ≠ 0 := by linarith
  have hZeq : Z N = N ^ (-l) * (A + ε N) := by
    have : A + ε N = Z N / N ^ (-l) := by
      simp only [hε]
      ring
    rw [this]
    field_simp
  have hpowK : N ^ (-(l + 1)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hZKeq : ZK N = N ^ (-(l + 1)) * (AK + εK N) := by
    have : AK + εK N = ZK N / N ^ (-(l + 1)) := by
      simp only [hεK]
      ring
    rw [this]
    field_simp
  have hAε : A + ε N ≠ 0 := by
    intro h0
    apply hZN
    rw [hZeq, h0, mul_zero]
  rw [hZeq, hZKeq, hpow', hAK]
  field_simp
  ring

end Grammar
