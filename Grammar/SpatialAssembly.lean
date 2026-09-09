/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialJointConvergence
import Grammar.FreeEnergyCorrection

/-!
# Finite-chart assembly at the next logarithmic order (unit 372; Astra #46 unit 1)

Given finitely many charts `i` with two-term expansions
`Z_i(N) = N^{-λ_i} L^{m_i-1} (F_i + B_i/L + o(1/L))`, let `λ = min λ_i`, `m = max{m_i : λ_i = λ}`,
`I₀ = {λ_i = λ, m_i = m}`, `I₁ = {λ_i = λ, m_i = m−1}`.  Then
```
∑_i Z_i(N) = N^{-λ} L^{m-1} (A + D/L + o(1/L)),   A = ∑_{I₀} F_i,   D = ∑_{I₀} B_i + ∑_{I₁} F_i
```
(`assembled_twoTerm`): **charts of multiplicity `m−1` contribute their leading coefficients to the
global next-log term**; charts with larger exponent or smaller multiplicity are negligible (power
beats log; `1/L` beats a constant).  Only the chartwise asymptotics and the finite-sum identity are
used — no charts or partitions of unity are constructed.  Corollaries: the assembled two-term
quotient for aligned numerator/denominator expansions (`assembled_quotient`), the assembled free
energy (`assembled_free_energy`), and the instantiation with spatial-phase charts of a common
dimension: the assembled evidence (`spatialAssembled_twoTerm`), the assembled energy correction
`L (E[NK] − A₁/A₀) → (A₀D₁ − A₁D₀)/A₀²` (`spatialAssembled_energy_correction`) and the assembled
free energy `−log ∑Z = λL − (m−1) log L − log A − D/(AL) + o(1/L)` (`spatialAssembled_free_energy`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-! ### The abstract assembly lemma -/

/-- Log powers are dominated by any power: `N^{-λ'} (1+L)^p / N^{-λ} → 0` for `λ < λ'`, and
the ratio of monomials `N^{-λ'} L^{p-1} L /(N^{-λ} L^{m-1})` is bounded by it for `L ≥ 1`. -/
theorem tendsto_shift_ratio {l l' : ℝ} (hll' : l < l') {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    Tendsto (fun N : ℝ => N ^ (-l') * Real.log N ^ (p - 1) * Real.log N /
      (N ^ (-l) * Real.log N ^ (m - 1))) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_cutoff_ratio p hll')
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hN
  have hL0 : 0 < Real.log N := by linarith
  have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos (by linarith) _
  have hpow' : 0 < N ^ (-l') := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hpow]
  have h1 : Real.log N ^ (p - 1) * Real.log N ≤ (1 + Real.log N) ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
    exact pow_le_pow_left₀ hL0.le (by linarith) p
  have h2 : 1 ≤ Real.log N ^ (m - 1) := one_le_pow₀ hL
  calc N ^ (-l') * Real.log N ^ (p - 1) * Real.log N * N ^ (-l)
      = N ^ (-l') * (Real.log N ^ (p - 1) * Real.log N) * N ^ (-l) := by ring
    _ ≤ N ^ (-l') * (1 + Real.log N) ^ p * N ^ (-l) := by gcongr
    _ ≤ N ^ (-l') * (1 + Real.log N) ^ p * (N ^ (-l) * Real.log N ^ (m - 1)) := by
        refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hpow.le h2) (by positivity)

open Classical in
/-- **Finite-chart assembly at the next logarithmic order.** -/
theorem assembled_twoTerm {ι : Type*} [Fintype ι] (Z : ι → ℝ → ℝ) (lam : ι → ℝ) (mult : ι → ℕ)
    (F B : ι → ℝ) {l : ℝ} {m : ℕ} (hl : ∀ i, l ≤ lam i) (hm : ∀ i, lam i = l → mult i ≤ m)
    (hm1 : ∀ i, 1 ≤ mult i)
    (hlead : ∀ i, Tendsto (fun N => Z i N / (N ^ (-lam i) * Real.log N ^ (mult i - 1))) atTop
      (𝓝 (F i)))
    (htwo : ∀ i, lam i = l → mult i = m → Tendsto (fun N => Real.log N *
      (Z i N / (N ^ (-l) * Real.log N ^ (m - 1)) - F i)) atTop (𝓝 (B i))) :
    Tendsto (fun N => Real.log N * ((∑ i, Z i N) / (N ^ (-l) * Real.log N ^ (m - 1)) -
        ∑ i, if lam i = l ∧ mult i = m then F i else 0)) atTop
      (𝓝 (∑ i, if lam i = l ∧ mult i = m then B i
        else if lam i = l ∧ mult i = m - 1 then F i else 0)) := by
  have hsum : ∀ N, Real.log N * ((∑ i, Z i N) / (N ^ (-l) * Real.log N ^ (m - 1)) -
      ∑ i, if lam i = l ∧ mult i = m then F i else 0) =
      ∑ i, Real.log N * (Z i N / (N ^ (-l) * Real.log N ^ (m - 1)) -
        if lam i = l ∧ mult i = m then F i else 0) := by
    intro N
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [hsum]
  refine tendsto_finsetSum _ fun i _ => ?_
  by_cases h0 : lam i = l ∧ mult i = m
  · rw [if_pos h0, if_pos h0]
    exact htwo i h0.1 h0.2
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : lam i = l ∧ mult i = m - 1
    · rw [if_pos h1]
      have hm2 : 2 ≤ m := by have := hm1 i; omega
      obtain ⟨q, hq⟩ : ∃ q, m - 1 = q + 1 := ⟨m - 2, by omega⟩
      have := hlead i
      rw [h1.1, h1.2, hq, Nat.add_sub_cancel] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      rw [sub_zero, hq, pow_succ]
      field_simp
    · rw [if_neg h1]
      by_cases hlam : lam i = l
      · -- `mult i ≤ m − 2`: one inverse log too many
        have hmi : mult i + 2 ≤ m := by
          have := hm i hlam
          have h0' : mult i ≠ m := fun h' => h0 ⟨hlam, h'⟩
          have h1' : mult i ≠ m - 1 := fun h' => h1 ⟨hlam, h'⟩
          omega
        obtain ⟨q, hq, hq1⟩ : ∃ q, m - 1 = mult i + q ∧ 1 ≤ q :=
          ⟨m - 1 - mult i, by omega, by omega⟩
        have h2 : Tendsto (fun N : ℝ => (Real.log N)⁻¹ ^ q) atTop (𝓝 0) := by
          have := tendsto_inv_log.pow q
          rwa [zero_pow (by omega)] at this
        have := (hlead i).mul h2
        rw [mul_zero, hlam] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
        have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
        have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        have hmi1 : Real.log N ^ (mult i - 1) * Real.log N = Real.log N ^ mult i := by
          rw [← pow_succ, Nat.sub_add_cancel (hm1 i)]
        rw [sub_zero, hq, pow_add, inv_pow]
        field_simp
        rw [mul_assoc, hmi1]
      · -- `λ < λ_i`: power beats log
        have hlt : l < lam i := lt_of_le_of_ne (hl i) (Ne.symm hlam)
        have := (hlead i).mul (tendsto_shift_ratio hlt (hm1 i) m)
        rw [mul_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
        have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
        have hpow : N ^ (-lam i) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        have hpow' : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        rw [sub_zero]
        field_simp

/-- **Assembled two-term quotient**: for aligned assembled expansions of a numerator and a
denominator (same charts, exponents `λ', λ`, common multiplicity data), with `A ≠ 0`,
`L (∑Z'/∑Z · N^{λ'-λ} − A'/A) → (A D' − A' D)/A²`. -/
theorem assembled_quotient {Z Z' : ℝ → ℝ} {A D A' D' l l' : ℝ} {m : ℕ} (hA : A ≠ 0)
    (hZ : Tendsto (fun N => Real.log N * (Z N / (N ^ (-l) * Real.log N ^ (m - 1)) - A)) atTop
      (𝓝 D))
    (hZ' : Tendsto (fun N => Real.log N * (Z' N / (N ^ (-l') * Real.log N ^ (m - 1)) - A')) atTop
      (𝓝 D')) :
    Tendsto (fun N => Real.log N * (Z' N / Z N * N ^ (l' - l) - A' / A)) atTop
      (𝓝 ((A * D' - A' * D) / A ^ 2)) := by
  refine (quotient_second_order hA hZ hZ').congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hL : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  rw [mul_div_assoc, div_self hL, mul_one]

/-- **Assembled free energy**: `−log ∑Z = λL − (m−1) log L − log A − D/(A L) + o(1/L)`. -/
theorem assembled_free_energy {Z : ℝ → ℝ} {A D l : ℝ} {m : ℕ} (hA : 0 < A)
    (hZ : Tendsto (fun N => Real.log N * (Z N / (N ^ (-l) * Real.log N ^ (m - 1)) - A)) atTop
      (𝓝 D)) :
    (∀ᶠ N in atTop, 0 < Z N) ∧
    Tendsto (fun N => Real.log N * (-Real.log (Z N) -
      (l * Real.log N - (m - 1 : ℕ) * Real.log (Real.log N) - Real.log A))) atTop (𝓝 (-D / A)) :=
  neg_log_twoTerm hA hZ

/-! ### Spatial-phase charts of a common dimension -/

section Spatial

variable {ι : Type*} [Fintype ι] (n : ℕ) (h k : ι → Fin (n + 1) → ℕ) (β : ℝ)
  (cξ cη : ι → CoeffFamily (n + 1)) (ξ η : ι → (Fin (n + 1) → ℝ) → ℝ) (lam : ι → ℝ)

/-- The assembled chart evidence `∑_i 𝒵_N[η_i; ξ_i]`. -/
noncomputable def spatialAssembled (N : ℝ) : ℝ :=
  ∑ i, origPhaseIntegral n (h i) (k i) β N 1 (ξ i) (η i)

open Classical in
/-- The assembled leading coefficient `A = ∑_{I₀} F_i`. -/
noncomputable def spatialAssembledFace (l : ℝ) (m : ℕ) : ℝ :=
  ∑ i, if lam i = l ∧ multCount (ratioExp (h i) (k i)) (lam i) = m then
    spatialFace (h i) (k i) (lam i) β (ξ i) (η i) else 0

open Classical in
/-- The assembled second coefficient `D = ∑_{I₀} B_i + ∑_{I₁} F_i`. -/
noncomputable def spatialAssembledSecond (l : ℝ) (m : ℕ) : ℝ :=
  ∑ i, if lam i = l ∧ multCount (ratioExp (h i) (k i)) (lam i) = m then
      spatialSecondCoeff n (h i) (k i) β (cξ i) (cη i) (lam i)
    else if lam i = l ∧ multCount (ratioExp (h i) (k i)) (lam i) = m - 1 then
      spatialFace (h i) (k i) (lam i) β (ξ i) (η i) else 0

/-- **Assembled two-term asymptotics for spatial-phase charts**: with `λ = min λ_i` and
`m = max{m_i : λ_i = λ}`, `L (∑_i 𝒵_N[η_i;ξ_i]/(N^{-λ}L^{m-1}) − A) → D`. -/
theorem spatialAssembled_twoTerm (hk : ∀ i j, 0 < k i j) (hβ : 0 < β)
    (hξ : ∀ i, AbsSummable (cξ i)) (hη : ∀ i, AbsSummable (cη i))
    (hξc : ∀ i, Continuous (ξ i)) (hηc : ∀ i, Continuous (η i))
    (hevξ : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cξ i) u = ξ i u)
    (hevη : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cη i) u = η i u)
    (hmin : ∀ i j, lam i ≤ ratioExp (h i) (k i) j) (hatt : ∀ i, ∃ j, ratioExp (h i) (k i) j = lam i)
    {l : ℝ} (hl : ∀ i, l ≤ lam i) {m : ℕ}
    (hm : ∀ i, lam i = l → multCount (ratioExp (h i) (k i)) (lam i) ≤ m) :
    Tendsto (fun N => Real.log N * (spatialAssembled n h k β ξ η N /
        (N ^ (-l) * Real.log N ^ (m - 1)) - spatialAssembledFace n h k β ξ η lam l m)) atTop
      (𝓝 (spatialAssembledSecond n h k β cξ cη ξ η lam l m)) := by
  classical
  unfold spatialAssembled spatialAssembledFace spatialAssembledSecond
  refine assembled_twoTerm (fun i N => origPhaseIntegral n (h i) (k i) β N 1 (ξ i) (η i)) lam
    (fun i => multCount (ratioExp (h i) (k i)) (lam i))
    (fun i => spatialFace (h i) (k i) (lam i) β (ξ i) (η i))
    (fun i => spatialSecondCoeff n (h i) (k i) β (cξ i) (cη i) (lam i)) hl hm
    (fun i => multCount_pos _ _ (hatt i)) (fun i => ?_) (fun i hli hmi => ?_)
  · exact spatialPhase_tendsto n (h i) (k i) (hk i) (lam i) β (ratioExp_min_pos _ _ (hk i) (hatt i))
      hβ (hmin i) (hatt i) (ξ i) (η i) (hξc i) (hηc i)
  · refine (spatialPhase_twoTerm_chart n (h i) (k i) (hk i) hβ (hξ i) (hη i) (hξc i) (hηc i)
      (hevξ i) (hevη i) (hmin i) (hatt i)).congr' (Eventually.of_forall fun N => ?_)
    simp only
    rw [hmi, hli]

/-- **Assembled next-log energy correction with spatial phases**: with the energy numerator
assembled from the shifted charts `h_i + 2k_i` (exponents `λ_i + 1`, same multiplicities),
`L (E[NK] − A₁/A₀) → (A₀ D₁ − A₁ D₀)/A₀²`. -/
theorem spatialAssembled_energy_correction (hk : ∀ i j, 0 < k i j) (hβ : 0 < β)
    (hξ : ∀ i, AbsSummable (cξ i)) (hη : ∀ i, AbsSummable (cη i))
    (hξc : ∀ i, Continuous (ξ i)) (hηc : ∀ i, Continuous (η i))
    (hevξ : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cξ i) u = ξ i u)
    (hevη : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cη i) u = η i u)
    (hmin : ∀ i j, lam i ≤ ratioExp (h i) (k i) j) (hatt : ∀ i, ∃ j, ratioExp (h i) (k i) j = lam i)
    {l : ℝ} (hl : ∀ i, l ≤ lam i) {m : ℕ}
    (hm : ∀ i, lam i = l → multCount (ratioExp (h i) (k i)) (lam i) ≤ m)
    (hA : spatialAssembledFace n h k β ξ η lam l m ≠ 0) :
    Tendsto (fun N => Real.log N *
        (N * spatialAssembled n (fun i j => h i j + 2 * k i j) k β ξ η N /
          spatialAssembled n h k β ξ η N -
        spatialAssembledFace n (fun i j => h i j + 2 * k i j) k β ξ η (fun i => lam i + 1)
          (l + 1) m / spatialAssembledFace n h k β ξ η lam l m)) atTop
      (𝓝 ((spatialAssembledFace n h k β ξ η lam l m *
          spatialAssembledSecond n (fun i j => h i j + 2 * k i j) k β cξ cη ξ η
            (fun i => lam i + 1) (l + 1) m -
        spatialAssembledFace n (fun i j => h i j + 2 * k i j) k β ξ η (fun i => lam i + 1)
          (l + 1) m * spatialAssembledSecond n h k β cξ cη ξ η lam l m) /
        spatialAssembledFace n h k β ξ η lam l m ^ 2)) := by
  have h0 := spatialAssembled_twoTerm n h k β cξ cη ξ η lam hk hβ hξ hη hξc hηc hevξ hevη hmin hatt
    hl hm
  have h1 := spatialAssembled_twoTerm n (fun i j => h i j + 2 * k i j) k β cξ cη ξ η
    (fun i => lam i + 1) hk hβ hξ hη hξc hηc hevξ hevη
    (fun i => hmin_shift (h i) (k i) (hk i) (hmin i))
    (fun i => hatt_shift (h i) (k i) (hk i) (hatt i))
    (l := l + 1) (fun i => by linarith [hl i]) (m := m) (fun i hli => by
      rw [multCount_shift (h i) (k i) (hk i)]
      exact hm i (by linarith))
  have hq := assembled_quotient hA h0 h1
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  rw [add_sub_cancel_left, Real.rpow_one]
  ring

/-- **Assembled free energy with spatial phases**:
`−log ∑_i 𝒵_N[η_i;ξ_i] = λL − (m−1) log L − log A − D/(A L) + o(1/L)` when `A > 0`. -/
theorem spatialAssembled_free_energy (hk : ∀ i j, 0 < k i j) (hβ : 0 < β)
    (hξ : ∀ i, AbsSummable (cξ i)) (hη : ∀ i, AbsSummable (cη i))
    (hξc : ∀ i, Continuous (ξ i)) (hηc : ∀ i, Continuous (η i))
    (hevξ : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cξ i) u = ξ i u)
    (hevη : ∀ i, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cη i) u = η i u)
    (hmin : ∀ i j, lam i ≤ ratioExp (h i) (k i) j) (hatt : ∀ i, ∃ j, ratioExp (h i) (k i) j = lam i)
    {l : ℝ} (hl : ∀ i, l ≤ lam i) {m : ℕ}
    (hm : ∀ i, lam i = l → multCount (ratioExp (h i) (k i)) (lam i) ≤ m)
    (hA : 0 < spatialAssembledFace n h k β ξ η lam l m) :
    (∀ᶠ N in atTop, 0 < spatialAssembled n h k β ξ η N) ∧
    Tendsto (fun N => Real.log N * (-Real.log (spatialAssembled n h k β ξ η N) -
      (l * Real.log N - (m - 1 : ℕ) * Real.log (Real.log N) -
        Real.log (spatialAssembledFace n h k β ξ η lam l m)))) atTop
      (𝓝 (-spatialAssembledSecond n h k β cξ cη ξ η lam l m /
        spatialAssembledFace n h k β ξ η lam l m)) :=
  assembled_free_energy hA
    (spatialAssembled_twoTerm n h k β cξ cη ξ η lam hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hl hm)

end Spatial

end Grammar
