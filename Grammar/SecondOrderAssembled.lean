/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SecondOrderQuotient
import Grammar.EnergyCorrectionAssembled

/-!
# The second-order expectation quotient after finite chart assembly (unit 323)

The assembled population integral of zero-noise joint data has two-term data uniformly in the
global multiplicity (`population_twoTerm_assembled`): `log N (𝒵/(N^{-μ_*}L^{m_*−1}) − A_*) → B_*`,
with `A_*` the assembled face functional and `B_*` the assembled coefficient of `N^{-μ_*}L^{m_*−2}`
(`assembledSecondCoeff`; zero for `m_* = 1`), from the isolated remainders of the assembled cutoff
expansion and a residual with `E log N / N^{-μ_*} → 0`. Two such data on the same charts (weights
`h`, `h'`, tangential data `x`, `x'`; for an observable `φ` the numerator data are the chart
amplitudes of `φ∘π` with their vanishing-order shifts) give the paper's second-order posterior
expectation after assembly (`population_second_order_assembled`, `_exp` with `O(e^{-εN})`
residuals):
```
log N ( 𝒵[φ]/𝒵 · N^{μ_*'−μ_*} L^{m_*−1}/L^{m_*'−1} − A_*'/A_* ) → (A_* B_*' − A_*' B_*)/A_*².
```
Charts whose first candidate lies strictly below the global target in the ordering contribute to
`B_*` (multiplicity `m_*−1` at `μ_*`) but not to `A_*`. Not claimed: anything when `A_* = 0`; the
geometric decomposition. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- The assembled coefficient of `N^{-μ_*}(log N)^{m_*−2}` (zero when `m_* = 1`). -/
noncomputable def assembledSecondCoeff (x : JointData K n) (μs : ℝ) (ms : ℕ) : ℝ :=
  if 2 ≤ ms then gCoeff ν h k β (fun _ => 1) x μs (ms - 2) else 0

/-- **Two-term data of the assembled population integral**, uniformly in the multiplicity. -/
theorem population_twoTerm_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0)) :
    Tendsto (fun N => Real.log N * (Zpop N / (N ^ (-μs) * Real.log N ^ (ms - 1)) -
      assembledFace ν h k β x lam μs ms)) atTop (𝓝 (assembledSecondCoeff ν h k β x μs ms)) := by
  have hQ : 0 < commonQ k := commonQ_pos k hk
  have hQ' : (0 : ℝ) < commonQ k := by exact_mod_cast hQ
  obtain ⟨a, ha⟩ := global_target_mem_lattice h k hk lam hatt hμatt
  have hmsD : ms - 1 ≤ commonD n := global_target_le_commonD h k lam hmatt
  have hms1 : 1 ≤ ms := by
    obtain ⟨I, -, hI⟩ := hmatt
    rw [← hI]
    exact multCount_pos _ _ (hatt I)
  have hcut : CutoffExpansion (commonQ k) (commonD n) (gInt ν h k β (fun _ => 1) x)
      (gCoeff ν h k β (fun _ => 1) x) :=
    cutoffExpansion_gInt ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
  have hpred : ∀ m : ℕ, m < a → ∀ j,
      gCoeff ν h k β (fun _ => 1) x ((m : ℝ) / commonQ k) j = 0 := by
    intro m hm' j
    refine gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm
      (p := ((m : ℝ) / commonQ k, j)) (Or.inl ?_)
    change (m : ℝ) / commonQ k < μs
    rw [ha, div_lt_div_iff_of_pos_right hQ']
    exact_mod_cast hm'
  have hAeq : gCoeff ν h k β (fun _ => 1) x μs (ms - 1) = assembledFace ν h k β x lam μs ms :=
    gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm
  have hzero : ∀ q, ms - 1 < q → gCoeff ν h k β (fun _ => 1) x μs q = 0 := fun q hq =>
    gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm (p := (μs, q))
      (Or.inr ⟨rfl, hq⟩)
  have hE' : ∀ r : ℕ, Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ r)) atTop (𝓝 0) :=
    fun r => tendsto_div_powLog_of_tendsto_mul_log hE r
  rcases Nat.lt_or_ge ms 2 with hms | hms
  · -- multiplicity one
    have hms1' : ms = 1 := by omega
    subst hms1'
    have hz0 : ∀ q, 0 < q → gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← ha]
      exact hzero q (by omega)
    have h1 := oneTerm_of_isolated hQ hcut hpred hz0
    rw [← ha] at h1
    have := h1.add hE
    rw [add_zero] at this
    unfold assembledSecondCoeff
    rw [if_neg (by omega)]
    refine this.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [hdecomp N, ← hAeq]
    simp only [Nat.sub_self, pow_zero, mul_one]
    ring
  · -- multiplicity at least two
    obtain ⟨r, hr⟩ : ∃ r, ms = r + 2 := ⟨ms - 2, by omega⟩
    subst hr
    have e1 : r + 2 - 1 = r + 1 := by omega
    have e2 : r + 2 - 2 = r := by omega
    have hr1 : r + 1 ≤ commonD n := by rwa [e1] at hmsD
    have hz : ∀ q, r + 1 < q → gCoeff ν h k β (fun _ => 1) x ((a : ℝ) / commonQ k) q = 0 := by
      intro q hq
      rw [← ha]
      exact hzero q (by omega)
    have h2 := twoTerm_of_isolated hQ hcut hpred hr1 hz
    rw [← ha] at h2
    have := h2.add (hE' r)
    rw [add_zero] at this
    unfold assembledSecondCoeff
    rw [if_pos (by omega), e1, e2, ← hAeq, e1]
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-μs) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hlogr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlog
    rw [hdecomp N]
    field_simp
    ring

/-- **Second-order posterior expectation after finite chart assembly**: for two zero-noise joint
data on the same charts (denominator weights `h`, data `x`, target `(μ_*, m_*)`; numerator weights
`h'`, data `x'`, target `(μ_*', m_*')`), external decompositions with log-weighted residual control,
and `A_* ≠ 0`:
`log N ( 𝒵'/𝒵 · N^{μ_*'−μ_*} L^{m_*−1}/L^{m_*'−1} − A_*'/A_* ) → (A_* B_*' − A_*' B_*)/A_*²`. -/
theorem population_second_order_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N * Real.log N / N ^ (-μs)) atTop (𝓝 0))
    (h' : (I : Fin M) → Fin (n I + 1) → ℕ) (x' : JointData K n)
    (hx' : ∀ I v, xiCoord (x'.chart I v) = 0) (lam' : Fin M → ℝ)
    (hmin' : ∀ I i, lam' I ≤ ratioExp (h' I) (k I) i)
    (hatt' : ∀ I, ∃ i, ratioExp (h' I) (k I) i = lam' I)
    {μs' : ℝ} (hμ' : ∀ I, μs' ≤ lam' I) (hμatt' : ∃ I, lam' I = μs') {ms' : ℕ}
    (hm' : ∀ I, lam' I = μs' → multCount (ratioExp (h' I) (k I)) (lam' I) ≤ ms')
    (hmatt' : ∃ I, lam' I = μs' ∧ multCount (ratioExp (h' I) (k I)) (lam' I) = ms')
    (Z' E' : ℝ → ℝ) (hdecomp' : ∀ N, Z' N = gInt ν h' k β (fun _ => 1) x' N + E' N)
    (hE' : Tendsto (fun N => E' N * Real.log N / N ^ (-μs')) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => Real.log N * (Z' N / Zpop N *
        (N ^ (μs' - μs) * Real.log N ^ (ms - 1) / Real.log N ^ (ms' - 1)) -
        assembledFace ν h' k β x' lam' μs' ms' / assembledFace ν h k β x lam μs ms)) atTop
      (𝓝 ((assembledFace ν h k β x lam μs ms * assembledSecondCoeff ν h' k β x' μs' ms' -
        assembledFace ν h' k β x' lam' μs' ms' * assembledSecondCoeff ν h k β x μs ms) /
        assembledFace ν h k β x lam μs ms ^ 2)) :=
  quotient_second_order hA
    (population_twoTerm_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E
      hdecomp hE)
    (population_twoTerm_assembled ν h' k β hk hβ x' hx' lam' hmin' hatt' hμ' hμatt' hm' hmatt'
      Z' E' hdecomp' hE')

/-- The assembled second-order quotient with the paper's exponentially small residuals. -/
theorem population_second_order_assembled_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (h' : (I : Fin M) → Fin (n I + 1) → ℕ) (x' : JointData K n)
    (hx' : ∀ I v, xiCoord (x'.chart I v) = 0) (lam' : Fin M → ℝ)
    (hmin' : ∀ I i, lam' I ≤ ratioExp (h' I) (k I) i)
    (hatt' : ∀ I, ∃ i, ratioExp (h' I) (k I) i = lam' I)
    {μs' : ℝ} (hμ' : ∀ I, μs' ≤ lam' I) (hμatt' : ∃ I, lam' I = μs') {ms' : ℕ}
    (hm' : ∀ I, lam' I = μs' → multCount (ratioExp (h' I) (k I)) (lam' I) ≤ ms')
    (hmatt' : ∃ I, lam' I = μs' ∧ multCount (ratioExp (h' I) (k I)) (lam' I) = ms')
    (Z' E' : ℝ → ℝ) (hdecomp' : ∀ N, Z' N = gInt ν h' k β (fun _ => 1) x' N + E' N)
    {ε : ℝ} (hε : 0 < ε) (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    (hE' : Tendsto (fun N => E' N * Real.exp (ε * N)) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => Real.log N * (Z' N / Zpop N *
        (N ^ (μs' - μs) * Real.log N ^ (ms - 1) / Real.log N ^ (ms' - 1)) -
        assembledFace ν h' k β x' lam' μs' ms' / assembledFace ν h k β x lam μs ms)) atTop
      (𝓝 ((assembledFace ν h k β x lam μs ms * assembledSecondCoeff ν h' k β x' μs' ms' -
        assembledFace ν h' k β x' lam' μs' ms' * assembledSecondCoeff ν h k β x μs ms) /
        assembledFace ν h k β x lam μs ms ^ 2)) :=
  population_second_order_assembled ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E
    hdecomp (tendsto_mul_log_div_of_exp E hε hE μs) h' x' hx' lam' hmin' hatt' hμ' hμatt' hm'
    hmatt' Z' E' hdecomp' (tendsto_mul_log_div_of_exp E' hε hE' μs') hA

end Grammar
