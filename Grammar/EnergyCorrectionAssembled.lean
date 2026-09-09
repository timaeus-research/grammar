/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.IsolatedRemainder
import Grammar.PopulationEnergyAssembled

/-!
# The first logarithmic energy correction after finite chart assembly (unit 321)

The paper's `E[K] = λ/n − (m−1)/(n log n) + o(1/(n log n))` for the assembled population integral.
Coefficient transport commutes with tangential integration and finite chart sums
(`dataBoxCoeff_add_two_k`, `gCoeff_add_two_k`: the assembled coefficients obey
`C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` chart by chart, each chart shifting its own
`h_I ↦ h_I + 2k_I`),
the assembled integral is a cutoff expansion whose coefficients vanish below the global target
`(μ_*, m_*−1)` (Programme P), so the isolated two-term forms of `IsolatedRemainder` apply, and the
quotient lemmas of unit 316 give
```
N log N (𝒵_N[K∘π] / 𝒵_N − μ_*/(βN)) → −(m_*−1)/β
```
(`energy_correction_assembled`) for every `m_* ≥ 1`, under zero-noise joint data, external
decompositions with residuals `E, E_K` satisfying `E log N / N^{-μ_*} → 0` and
`E_K log N / N^{-(μ_*+1)} → 0`, and `A_* ≠ 0`; with the paper's exponentially small residuals
(`energy_correction_assembled_exp`). Charts of multiplicity `m_*−1` at exponent `μ_*` contribute to
the second coefficient `B_* = C(μ_*, m_*−2)` but not to `A_*`; the cancellation is done at the
aggregate level. Not claimed: any correction when `A_* = 0`; a probability-expectation
interpretation for signed amplitudes. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Canonical coefficients vanish above the ambient log degree `n` (empty binomial range). -/
theorem dataBoxCoeff_eq_zero_of_gt_degree (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) : dataBoxCoeff n h k β b x μ j = 0 := by
  unfold dataBoxCoeff boxCoeff
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, mul_zero]

/-- **Coefficient transport for zero-noise data**: `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β`
for the canonical coefficients of a datum with `ξ = 0` (all `j`). -/
theorem dataBoxCoeff_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (x : DataSpace (n + 1)) (hx : xiCoord x = 0) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    dataBoxCoeff n (fun i => h i + 2 * k i) k β 1 x (μ + 1) j =
      (μ * dataBoxCoeff n h k β 1 x μ j -
        ((j : ℝ) + 1) * dataBoxCoeff n h k β 1 x μ (j + 1)) / β := by
  rcases le_or_gt j n with hj | hj
  · rw [dataBoxCoeff_population n _ k β x hx (μ + 1) hj, dataBoxCoeff_population n h k β x hx μ hj,
      population_coeff_add_two_k n h k hk hβ (absSummable_etaCoord x) hμ j]
    rcases le_or_gt (j + 1) n with hj1 | hj1
    · rw [dataBoxCoeff_population n h k β x hx μ hj1]
    · rw [dataBoxCoeff_eq_zero_of_gt_degree n h k β 1 x μ hj1,
        population_coeff_eq_zero_of_gt_degree n h k hk hβ (absSummable_etaCoord x) hμ hj1]
  · rw [dataBoxCoeff_eq_zero_of_gt_degree n _ k β 1 x _ hj,
      dataBoxCoeff_eq_zero_of_gt_degree n h k β 1 x μ hj,
      dataBoxCoeff_eq_zero_of_gt_degree n h k β 1 x μ (by omega)]
    ring

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **Assembled coefficient transport**: the global coefficients of the energy-inserted integral
are the transported global coefficients, each chart shifting its own weight. -/
theorem gCoeff_add_two_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μ + 1) j =
      (μ * gCoeff ν h k β (fun _ => 1) x μ j -
        ((j : ℝ) + 1) * gCoeff ν h k β (fun _ => 1) x μ (j + 1)) / β := by
  unfold gCoeff
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun I _ => ?_
  unfold tanCoeff
  dsimp only
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub, ← integral_div]
  · congr 1
    funext v
    exact dataBoxCoeff_add_two_k (n I) (h I) (k I) (hk I) hβ (x.chart I v) (hx I v) hμ j
  · exact (integrable_dataBoxCoeff_tan (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I) μ
      j).const_mul μ
  · exact (integrable_dataBoxCoeff_tan (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I) μ
      (j + 1)).const_mul _

/-- **The first logarithmic energy correction after finite chart assembly**:
`N log N (𝒵_N[K∘π]/𝒵_N − μ_*/(βN)) → −(m_*−1)/β` for every `m_* ≥ 1`, for zero-noise joint data with
external decompositions whose residuals satisfy `E log N / N^{-μ_*} → 0` and
`E_K log N / N^{-(μ_*+1)} → 0`, when the assembled face functional `A_*` is nonzero. -/
theorem energy_correction_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms)
    (Zpop E ZK EK : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0))
    (hdecompK : ∀ N, ZK N = gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x N + EK N)
    (hEK : Tendsto (fun N => EK N * Real.log N / N ^ (-(μs + 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N * Real.log N * (ZK N / Zpop N - μs / (β * N))) atTop
      (𝓝 (-((ms : ℝ) - 1) / β)) := by
  have hlam : ∀ I, 0 < lam I := fun I => by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  have hμs : 0 < μs := by
    obtain ⟨I, hI⟩ := hμatt
    rw [← hI]
    exact hlam I
  have hQ : 0 < commonQ k := commonQ_pos k hk
  have hQ' : (0 : ℝ) < commonQ k := by exact_mod_cast hQ
  obtain ⟨a, ha⟩ := global_target_mem_lattice h k hk lam hatt hμatt
  have hmsD : ms - 1 ≤ commonD n := global_target_le_commonD h k lam hmatt
  have hms1 : 1 ≤ ms := by
    obtain ⟨I, -, hI⟩ := hmatt
    rw [← hI]
    exact multCount_pos _ _ (hatt I)
  -- the shifted data
  have hminK : ∀ I i, lam I + 1 ≤ ratioExp (fun i => h I i + 2 * k I i) (k I) i := fun I =>
    hmin_add_two_k (h I) (k I) (hk I) (hmin I)
  have hattK : ∀ I, ∃ i, ratioExp (fun i => h I i + 2 * k I i) (k I) i = lam I + 1 := fun I =>
    hatt_add_two_k (h I) (k I) (hk I) (hatt I)
  have hμK : ∀ I, μs + 1 ≤ lam I + 1 := fun I => by linarith [hμ I]
  have hmK : ∀ I, lam I + 1 = μs + 1 →
      multCount (ratioExp (fun i => h I i + 2 * k I i) (k I)) (lam I + 1) ≤ ms := fun I hI => by
    rw [multCount_add_two_k (h I) (k I) (hk I)]
    exact hm I (add_left_inj 1 |>.1 hI)
  have haK : μs + 1 = ((a + commonQ k : ℕ) : ℝ) / commonQ k := by
    rw [ha]
    push_cast
    rw [add_div, div_self hQ'.ne']
  -- cutoff expansions and predecessor vanishing
  have hcut : CutoffExpansion (commonQ k) (commonD n) (gInt ν h k β (fun _ => 1) x)
      (gCoeff ν h k β (fun _ => 1) x) :=
    cutoffExpansion_gInt ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
  have hcutK : CutoffExpansion (commonQ k) (commonD n)
      (gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x)
      (gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x) :=
    cutoffExpansion_gInt ν _ k β (fun _ => 1) hk hβ (fun _ => one_pos) x
  have hpred : ∀ m : ℕ, m < a → ∀ j,
      gCoeff ν h k β (fun _ => 1) x ((m : ℝ) / commonQ k) j = 0 := by
    intro m hm' j
    refine gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm
      (p := ((m : ℝ) / commonQ k, j)) (Or.inl ?_)
    change (m : ℝ) / commonQ k < μs
    rw [ha, div_lt_div_iff_of_pos_right hQ']
    exact_mod_cast hm'
  have hpredK : ∀ m : ℕ, m < a + commonQ k → ∀ j,
      gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x ((m : ℝ) / commonQ k) j = 0 := by
    intro m hm' j
    refine gCoeff_population_pred_eq_zero ν _ k β hk hβ x hx (fun I => lam I + 1) hminK hattK hμK
      hmK (p := ((m : ℝ) / commonQ k, j)) (Or.inl ?_)
    change (m : ℝ) / commonQ k < μs + 1
    rw [ha, div_lt_iff₀ hQ', add_mul, div_mul_cancel₀ _ hQ'.ne', one_mul]
    exact_mod_cast hm'
  -- the leading coefficient, the vanishing above it, and the transport
  have hAeq : gCoeff ν h k β (fun _ => 1) x μs (ms - 1) = assembledFace ν h k β x lam μs ms :=
    gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm
  have hA' : gCoeff ν h k β (fun _ => 1) x μs (ms - 1) ≠ 0 := by rw [hAeq]; exact hA
  have hzero : ∀ q, ms - 1 < q → gCoeff ν h k β (fun _ => 1) x μs q = 0 := fun q hq =>
    gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm (p := (μs, q))
      (Or.inr ⟨rfl, hq⟩)
  have htrans : ∀ j, gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) j =
      (μs * gCoeff ν h k β (fun _ => 1) x μs j -
        ((j : ℝ) + 1) * gCoeff ν h k β (fun _ => 1) x μs (j + 1)) / β :=
    fun j => gCoeff_add_two_k ν h k β hk hβ x hx hμs j
  have hE' : ∀ r : ℕ, Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ r)) atTop (𝓝 0) :=
    fun r => tendsto_div_powLog_of_tendsto_mul_log hE r
  have hEK' : ∀ r : ℕ, Tendsto (fun N => EK N / (N ^ (-(μs + 1)) * Real.log N ^ r)) atTop
      (𝓝 0) := fun r => tendsto_div_powLog_of_tendsto_mul_log hEK r
  rcases Nat.lt_or_ge ms 2 with hms | hms
  · -- multiplicity one
    have hms1' : ms = 1 := by omega
    subst hms1'
    have hA0 : gCoeff ν h k β (fun _ => 1) x μs 0 ≠ 0 := hA'
    have hz0 : ∀ q, 0 < q → gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← ha]
      exact hzero q (by omega)
    have h1 := oneTerm_of_isolated hQ hcut hpred hz0
    rw [← ha] at h1
    have hz0K : ∀ q, 0 < q → gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x
        (((a + commonQ k : ℕ) : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← haK, htrans q, hzero q (by omega), hzero (q + 1) (by omega)]
      ring
    have h1K := oneTerm_of_isolated hQ hcutK hpredK hz0K
    rw [← haK] at h1K
    have hZ : Tendsto (fun N => Real.log N *
        (Zpop N / N ^ (-μs) - gCoeff ν h k β (fun _ => 1) x μs 0)) atTop (𝓝 0) := by
      have := h1.add hE
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hdecomp N]
      ring
    have hZK : Tendsto (fun N => Real.log N * (ZK N / N ^ (-(μs + 1)) -
        gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) 0)) atTop (𝓝 0) := by
      have := h1K.add hEK
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hdecompK N]
      ring
    have hAK : gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) 0 =
        μs * gCoeff ν h k β (fun _ => 1) x μs 0 / β := by
      rw [htrans 0, hzero 1 (by omega)]
      ring
    have := oneTerm_energy_quotient hβ hA0 hAK hZ hZK
    simpa using this
  · -- multiplicity at least two
    obtain ⟨r, hr⟩ : ∃ r, ms = r + 2 := ⟨ms - 2, by omega⟩
    subst hr
    have hr1 : r + 1 ≤ commonD n := by
      have : r + 2 - 1 = r + 1 := by omega
      rwa [this] at hmsD
    have hA'' : gCoeff ν h k β (fun _ => 1) x μs (r + 1) ≠ 0 := by
      have : r + 2 - 1 = r + 1 := by omega
      rwa [this] at hA'
    have hz : ∀ q, r + 1 < q → gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← ha]
      exact hzero q (by omega)
    have h2 := twoTerm_of_isolated hQ hcut hpred hr1 hz
    rw [← ha] at h2
    have hzK : ∀ q, r + 1 < q → gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x
        (((a + commonQ k : ℕ) : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← haK, htrans q, hzero q (by omega), hzero (q + 1) (by omega)]
      ring
    have h2K := twoTerm_of_isolated hQ hcutK hpredK hr1 hzK
    rw [← haK] at h2K
    have hZ : Tendsto (fun N => Zpop N / (N ^ (-μs) * Real.log N ^ r) -
        gCoeff ν h k β (fun _ => 1) x μs (r + 1) * Real.log N) atTop
        (𝓝 (gCoeff ν h k β (fun _ => 1) x μs r)) := by
      have := h2.add (hE' r)
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hdecomp N]
      ring
    have hZK : Tendsto (fun N => ZK N / (N ^ (-(μs + 1)) * Real.log N ^ r) -
        gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) (r + 1) * Real.log N)
        atTop (𝓝 (gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) r)) := by
      have := h2K.add (hEK' r)
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hdecompK N]
      ring
    have hAK : gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) (r + 1) =
        μs * gCoeff ν h k β (fun _ => 1) x μs (r + 1) / β := by
      rw [htrans (r + 1), hzero (r + 1 + 1) (by omega)]
      ring
    have hBK : gCoeff ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x (μs + 1) r =
        (μs * gCoeff ν h k β (fun _ => 1) x μs r -
          ((r : ℝ) + 1) * gCoeff ν h k β (fun _ => 1) x μs (r + 1)) / β := htrans r
    have := twoTerm_energy_quotient hβ hA'' hAK hBK hZ hZK
    convert this using 2
    push_cast
    ring

/-- The assembled correction with the paper's exponentially small residuals. -/
theorem energy_correction_assembled_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms)
    (Zpop E ZK EK : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hdecompK : ∀ N, ZK N = gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x N + EK N)
    {ε : ℝ} (hε : 0 < ε) (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    (hEK : Tendsto (fun N => EK N * Real.exp (ε * N)) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N * Real.log N * (ZK N / Zpop N - μs / (β * N))) atTop
      (𝓝 (-((ms : ℝ) - 1) / β)) :=
  energy_correction_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E ZK EK
    hdecomp (tendsto_mul_log_div_of_exp E hε hE μs) hdecompK
    (tendsto_mul_log_div_of_exp EK hε hEK (μs + 1)) hA

end Grammar
