/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationTangential
import Grammar.ClosingCorollaries

/-!
# Finite chart assembly of the population expansion (Astra #37 Theorem A(d), unit 301)

Finitely many normal-form charts `I : Fin M`, each with compact tangential space `K I`, finite
measure `ν I`, exponents `h I, k I`, unit normal box, and zero-noise tangential data
`x.chart I` (`xiCoord (x.chart I v) = 0`). Write `λ_I` for the minimal ratio of chart `I`, `m_I`
for its multiplicity, `A_I = ∫_{K_I} amplitudeCoeff (h I) (k I) λ_I β (η_{I,v}) dν_I(v)` for its
integrated face functional, and
```
μ_* = min_I λ_I,      m_* = max {m_I : λ_I = μ_*},      A_* = ∑_{λ_I = μ_*, m_I = m_*} A_I.
```
(all supplied as hypotheses on a candidate `μ_*`, `m_*`, so no `Finset.min'` bookkeeping). Then

* the assembled coefficient at the global target is `A_*` (`gCoeff_population_leading`): charts with
  `λ_I > μ_*` contribute nothing at `μ_*` (below their first candidate), charts with `λ_I = μ_*` but
  `m_I < m_*` contribute nothing at log degree `m_* − 1` (above their `m_I − 1`);
* every predecessor of `(μ_*, m_* − 1)` has zero assembled coefficient
  (`absPredSum_population_eq_zero`), so the ordered remainder of Programme S is the normalised
  integral itself;
* for `𝒵_pop(N) = ∑_I 𝒵^I(N; x_I) + E(N)` with `E` negligible at the target scale,
  `𝒵_pop(N)/(N^{-μ_*}(log N)^{m_*−1}) → A_*` (`population_assembled_tendsto`, via the frozen
  `tendsto_normalForm_pop`), asymptotic equivalence when `A_* ≠ 0`
  (`population_assembled_isEquivalent`), and the exponentially small residual of the paper
  (`E(N) e^{εN} → 0`) is negligible at every power-log scale (`tendsto_target_of_exp`,
  `population_assembled_tendsto_exp`).

The decomposition `𝒵_pop = ∑_I 𝒵^I + E` is an external hypothesis (Steps 1–3 of §3.5 and the
analytic admissibility of the chart amplitudes); sums of face functionals may cancel across charts,
which is why `A_* ≠ 0` is a hypothesis of the equivalence. If `A_* = 0` the theorem asserts only the
zero limit at this scale; the true leading term must be sought among later ordered coefficients.
Throughout, `(μ_*, m_*−1)` is the global FIRST CANDIDATE; it is the leading pair only when
`A_* ≠ 0` (cancellation among tied charts is possible), and no theorem here selects the leading
pair after such a cancellation.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

/-- **Exponentially small residuals are negligible at every power-log scale** (deterministic
form of `tendstoInMeasure_target_of_exp`). -/
theorem tendsto_target_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (μ₀ : ℝ) (j : ℕ) :
    Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0) := by
  have hdet : ∀ᶠ N : ℝ in atTop, 1 ≤ N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero μ₀ ε hε
    have h2 : ∀ᶠ N : ℝ in atTop, N ^ μ₀ * Real.exp (-ε * N) < 1 :=
      h1.eventually (gt_mem_nhds one_pos)
    filter_upwards [h2, eventually_ge_atTop (Real.exp 1)] with N hN1 hNe
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNe
    have hlog1 : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
    have hlj : 1 ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hpos : 0 < N ^ μ₀ * Real.exp (-ε * N) := by positivity
    have hinv : 1 ≤ N ^ (-μ₀) * Real.exp (ε * N) := by
      have : N ^ (-μ₀) * Real.exp (ε * N) = (N ^ μ₀ * Real.exp (-ε * N))⁻¹ := by
        rw [Real.rpow_neg hN0.le, mul_inv, ← Real.exp_neg]
        congr 1; congr 1; ring
      rw [this]
      exact one_le_inv_iff₀.2 ⟨hpos, hN1.le⟩
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (N ^ (-μ₀) * Real.exp (ε * N)) * Real.log N ^ j :=
          mul_le_mul hinv hlj zero_le_one (by positivity)
      _ = _ := by ring
  refine squeeze_zero_norm' ?_ (tendsto_norm_zero.comp hE)
  filter_upwards [hdet] with N hN
  have hD : 0 < N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) := by linarith
  have hexp : 0 < Real.exp (ε * N) := Real.exp_pos _
  have hden : 0 < N ^ (-μ₀) * Real.log N ^ j := by
    by_contra hle
    rw [not_lt] at hle
    have : N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hexp.le
    linarith
  simp only [Function.comp, Real.norm_eq_abs, abs_div, abs_of_pos hden, abs_mul,
    abs_of_pos hexp]
  rw [div_le_iff₀ hden]
  calc |E N| = |E N| * 1 := (mul_one _).symm
    _ ≤ |E N| * (N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N)) :=
        mul_le_mul_of_nonneg_left hN (abs_nonneg _)
    _ = |E N| * Real.exp (ε * N) * (N ^ (-μ₀) * Real.log N ^ j) := by ring

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- The integrated face functional of chart `I` at its own first candidate `λ_I`. -/
noncomputable def chartFace (x : JointData K n) (lam : Fin M → ℝ) (I : Fin M) : ℝ :=
  ∫ v, amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v)) ∂(ν I)

/-- The assembled first-candidate coefficient `∑_{λ_I = μ_*, m_I = m_*} A_I`. -/
noncomputable def assembledFace (x : JointData K n) (lam : Fin M → ℝ) (μs : ℝ) (ms : ℕ) : ℝ :=
  ∑ I, if lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms then chartFace ν h k β x lam I
    else 0

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- **The assembled coefficient at the global target is the assembled face functional.** -/
theorem gCoeff_population_leading (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) :
    gCoeff ν h k β (fun _ => 1) x μs (ms - 1) = assembledFace ν h k β x lam μs ms := by
  unfold gCoeff assembledFace
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · obtain ⟨hIμ, hIm⟩ := hI
    unfold chartFace
    rw [← hIμ, ← hIm]
    exact tanCoeff_population_leading (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I) (hx I)
      (hmin I) (hatt I)
  · by_cases hIμ : lam I = μs
    · have hlt : multCount (ratioExp (h I) (k I)) (lam I) < ms :=
        lt_of_le_of_ne (hm I hIμ) fun hE => hI ⟨hIμ, hE⟩
      have hpos := multCount_pos (ratioExp (h I) (k I)) (lam I) (hatt I)
      rw [← hIμ]
      exact tanCoeff_population_eq_zero_of_gt (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I)
        (hx I) (hmin I) (hatt I) (by omega)
    · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
        (hmin I) (lt_of_le_of_ne (hμ I) (Ne.symm hIμ)) _

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- Every assembled coefficient at a predecessor of the global target vanishes. -/
theorem gCoeff_population_pred_eq_zero (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) {p : ℝ × ℕ}
    (hp : precedes p (μs, ms - 1)) : gCoeff ν h k β (fun _ => 1) x p.1 p.2 = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  rcases hp with hlt | ⟨heq, hgt⟩
  · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
      (hmin I) (lt_of_lt_of_le hlt (hμ I)) _
  · have heq' : p.1 = μs := heq
    have hgt' : ms - 1 < p.2 := hgt
    rw [heq']
    by_cases hIμ : lam I = μs
    · rw [← hIμ]
      exact tanCoeff_population_eq_zero_of_gt (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I)
        (hx I) (hmin I) (hatt I) (by have := hm I hIμ; omega)
    · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
        (hmin I) (lt_of_le_of_ne (hμ I) (Ne.symm hIμ)) _

/-- **General wrapper**: if every assembled coefficient at a predecessor of the target vanishes,
the assembled predecessor sum vanishes. -/
theorem absPredSum_eq_zero_of_pred {Q D : ℕ} (c : ℝ → ℕ → ℝ) {μ : ℝ} {j : ℕ}
    (hc : ∀ p : ℝ × ℕ, precedes p (μ, j) → c p.1 p.2 = 0) (N : ℝ) :
    absPredSum Q D c μ j N = 0 := by
  unfold absPredSum
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨-, hprec⟩ := mem_predSet_iff.1 hp
  unfold absTerm
  rw [hc p hprec, zero_mul]

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- The assembled predecessor sum at the global target vanishes identically. -/
theorem absPredSum_population_eq_zero (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) (N : ℝ) :
    absPredSum (commonQ k) (commonD n) (gCoeff ν h k β (fun _ => 1) x) μs (ms - 1) N = 0 := by
  exact absPredSum_eq_zero_of_pred _
    (fun p hp => gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm hp) N

/-- The global first candidate lies on the common lattice. -/
theorem global_target_mem_lattice (hk : ∀ I i, 0 < k I i) (lam : Fin M → ℝ)
    (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I) {μs : ℝ} (hμatt : ∃ I, lam I = μs) :
    ∃ m : ℕ, μs = (m : ℝ) / commonQ k := by
  obtain ⟨I, hI⟩ := hμatt
  obtain ⟨i, hi⟩ := hatt I
  obtain ⟨m', -, hm'⟩ := ratio_mem_lattice (k I) (hk I) i (h I i)
  obtain ⟨c, hc⟩ := latticeQ_dvd_commonQ k I
  have hQ : (0 : ℝ) < latticeQ (k I) := by exact_mod_cast latticeQ_pos (k I) (hk I)
  have hcQ : (0 : ℝ) < commonQ k := by exact_mod_cast commonQ_pos k hk
  have hc0 : (0 : ℝ) < c := by
    have : (commonQ k : ℝ) = latticeQ (k I) * c := by exact_mod_cast hc
    nlinarith
  refine ⟨m' * c, ?_⟩
  rw [← hI, ← hi]
  unfold ratioExp
  rw [hm']
  push_cast
  rw [hc]
  push_cast
  field_simp

/-- The global multiplicity index is within the common degree. -/
theorem global_target_le_commonD (lam : Fin M → ℝ) {μs : ℝ} {ms : ℕ}
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) :
    ms - 1 ≤ commonD n := by
  obtain ⟨I, -, hI⟩ := hmatt
  have h1 := multCount_le_card (ratioExp (h I) (k I)) (lam I)
  have h2 := le_commonD (n := n) I
  omega

/-- **Theorem A(d): the assembled population expansion at the global first candidate.** For
`𝒵_pop(N) = ∑_I 𝒵^I(N; x_I) + E(N)` with `E` negligible at the scale `N^{-μ_*}(log N)^{m_*−1}`,
`𝒵_pop(N)/(N^{-μ_*}(log N)^{m_*−1}) → A_* = ∑_{λ_I = μ_*, m_I = m_*} A_I`. -/
theorem population_assembled_tendsto (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0)) :
    Tendsto (fun N => Zpop N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (assembledFace ν h k β x lam μs ms)) := by
  have hT := tendsto_normalForm_pop ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
    (global_target_mem_lattice h k hk lam hatt hμatt) (global_target_le_commonD h k lam hmatt)
    Zpop E hdecomp hE
  rw [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [absPredSum_population_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm, sub_zero]

/-- Asymptotic equivalence of the assembled population integral when `A_* ≠ 0`. -/
theorem population_assembled_isEquivalent (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Zpop ~[atTop] fun N => assembledFace ν h k β x lam μs ms *
      (N ^ (-μs) * Real.log N ^ (ms - 1)) := by
  have := isEquivalent_normalForm_pop ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
    (global_target_mem_lattice h k hk lam hatt hμatt) (global_target_le_commonD h k lam hmatt)
    Zpop E hdecomp hE (absPredSum_population_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm)
    (by rwa [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm])
  rwa [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm] at this

/-- **Theorem A(d) with the paper's exponentially small residual** `E(N) e^{εN} → 0`. -/
theorem population_assembled_tendsto_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) :
    Tendsto (fun N => Zpop N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (assembledFace ν h k β x lam μs ms)) :=
  population_assembled_tendsto ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E hdecomp
    (tendsto_target_of_exp E hε hE μs (ms - 1))

/-- Asymptotic equivalence with the paper's exponentially small residual, when `A_* ≠ 0`. -/
theorem population_assembled_isEquivalent_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Zpop ~[atTop] fun N => assembledFace ν h k β x lam μs ms *
      (N ^ (-μs) * Real.log N ^ (ms - 1)) :=
  population_assembled_isEquivalent ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E
    hdecomp (tendsto_target_of_exp E hε hE μs (ms - 1)) hA

end Grammar
