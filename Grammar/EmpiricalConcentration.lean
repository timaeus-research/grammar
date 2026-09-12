/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LeadingTermNegligible
import Grammar.PosteriorPerturbationTransfer

/-!
# Concentration of a perturbed Gibbs posterior near the zero set (CCLXXXVIII)

The C2/C3 package of the statistical-transfer programme (consult #87): the deterministic
concentration estimate for a Gibbs posterior with an approximately known phase, its pathwise and
almost-sure consequences, the constant-on-minimisers observable theorem, and the coefficient
consistency `c_φ = φ₀ c_1`.

**The deterministic inequality.** For a finite prior `π`, a phase `K ≥ 0`, an approximate phase
`K̂` with `|K̂ − K| ≤ e` (`π`-a.e.) and `0 < a < κ`:
`∫_{K ≥ κ} e^{−n K̂} dπ ≤ π(univ) e^{−n(κ − e)}`, `Ẑ_n = ∫ e^{−n K̂} dπ ≥ π{K < a} e^{−n(a + e)}`,
hence `μ̂_n{K ≥ κ} ≤ (π(univ)/π{K < a}) e^{−n(κ − a − 2e)}` (`gibbsMass_ge_le`) — the denominator
uses a SMALLER sublevel than the tail threshold (consult #87's correction).

**Pathwise and almost surely.** With `|K̂_n − K| ≤ e_n → 0` (uniformly on the support) the tail
mass is eventually `≤ C e^{−nκ/2}`, so it tends to `0` (`tendsto_gibbsMass_ge`); the almost-sure
wrapper is the same statement under `∀ᵐ ω` (`ae_tendsto_gibbsMass_ge`). No compactness, no
population certificate, no rate beyond `e_n = o(1)`; the uniform convergence of the empirical
phase is a HYPOTHESIS (a uniform law of large numbers, not derived here from bounded losses on a
compact set alone).

**Constant-on-minimisers observables.** On a compact support with `K`, `φ` continuous and
`φ ≡ φ₀` on the zero set, every `ε` has a `κ` with `|φ − φ₀| < ε` on `{K < κ}` (the compact bad set
`{|φ − φ₀| ≥ ε}` carries a positive minimum of `K`, `exists_sublevel_of_eq_on_zeroSet`), and
`|μ̂_n(φ) − φ₀| ≤ ε + B μ̂_n{K ≥ κ}` (`abs_expectation_sub_le`), so `μ̂_n(φ) → φ₀`
(`tendsto_expectation_of_eq_on_zeroSet`) — the deterministic special case that survives the
empirical fluctuation.

**Coefficient consistency.** If `a_n Z_n[1] → c_1 > 0` and `a_n Z_n[φ] → c_φ` for the population
posterior (the case `K̂ = K`) and `φ` is as above, then `c_φ = φ₀ c_1`
(`coeff_eq_of_eq_on_zeroSet`, `coeff_eq_of_hasLeadingTerm`), by uniqueness of limits — no
coefficient-linearity API. The certificate corollary `|log Ẑ_n − log Z_n| ≤ n e_n`
(`abs_log_normaliser_sub_le`) transfers `log Z_n / n → 0` to the empirical normaliser
(`tendsto_log_normaliser_div`).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace Gibbs

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]

/-- The Gibbs normaliser `Ẑ = ∫ e^{−n K̂} dπ`. -/
noncomputable def normaliser (Kh : W → ℝ) (n : ℝ) : ℝ := ∫ w, Real.exp (-n * Kh w) ∂π

/-- The Gibbs mass of a set `E`: `∫_E e^{−n K̂} dπ / Ẑ`. -/
noncomputable def mass (Kh : W → ℝ) (n : ℝ) (E : Set W) : ℝ :=
  (∫ w in E, Real.exp (-n * Kh w) ∂π) / normaliser π Kh n

/-- The Gibbs expectation `∫ φ e^{−n K̂} dπ / Ẑ`. -/
noncomputable def expectation (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ :=
  (∫ w, φ w * Real.exp (-n * Kh w) ∂π) / normaliser π Kh n

variable {K Kh : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKhm : Measurable Kh)
  {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

include hK0 hKhm he in
/-- The Boltzmann factor of the approximate phase is integrable (it is bounded by `e^{n e}`). -/
theorem integrable_exp {n : ℝ} (hn : 0 ≤ n) :
    Integrable (fun w => Real.exp (-n * Kh w)) π := by
  refine (integrable_const (Real.exp (n * e))).mono'
    (Real.measurable_exp.comp (measurable_const.mul hKhm)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  have h1 := (abs_le.1 (he w)).1
  have h2 := hK0 w
  nlinarith

include hK0 hKm hKhm he in
/-- **The tail bound**: `∫_{K ≥ κ} e^{−n K̂} dπ ≤ π(univ) e^{−n(κ − e)}` for `n ≥ 0`. -/
theorem setIntegral_exp_ge_le {κ n : ℝ} (hn : 0 ≤ n) :
    ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π ≤ π.real univ * Real.exp (-n * (κ - e)) := by
  have hmeas : MeasurableSet {w | κ ≤ K w} := measurableSet_le measurable_const hKm
  calc ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π
      ≤ ∫ _ in {w | κ ≤ K w}, Real.exp (-n * (κ - e)) ∂π := by
        refine setIntegral_mono_on ((integrable_exp π hK0 hKhm he hn).integrableOn)
          (integrableOn_const (measure_ne_top _ _)) hmeas fun w hw => ?_
        rw [Real.exp_le_exp]
        have h1 := (abs_le.1 (he w)).1
        have hw' : κ ≤ K w := hw
        nlinarith
    _ = π.real {w | κ ≤ K w} * Real.exp (-n * (κ - e)) := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ π.real univ * Real.exp (-n * (κ - e)) :=
        mul_le_mul_of_nonneg_right (measureReal_mono (subset_univ _)) (Real.exp_pos _).le

include hK0 hKm hKhm he in
/-- **The normaliser lower bound**: `Ẑ ≥ π{K < a} e^{−n(a + e)}` for `n ≥ 0`. -/
theorem normaliser_ge {a n : ℝ} (hn : 0 ≤ n) :
    π.real {w | K w < a} * Real.exp (-n * (a + e)) ≤ normaliser π Kh n := by
  have hmeas : MeasurableSet {w | K w < a} := measurableSet_lt hKm measurable_const
  unfold normaliser
  calc π.real {w | K w < a} * Real.exp (-n * (a + e))
      = ∫ _ in {w | K w < a}, Real.exp (-n * (a + e)) ∂π := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ w in {w | K w < a}, Real.exp (-n * Kh w) ∂π := by
        refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
          ((integrable_exp π hK0 hKhm he hn).integrableOn) hmeas fun w hw => ?_
        rw [Real.exp_le_exp]
        have h1 := (abs_le.1 (he w)).2
        have hw' : K w < a := hw
        nlinarith
    _ ≤ ∫ w, Real.exp (-n * Kh w) ∂π :=
        setIntegral_le_integral (integrable_exp π hK0 hKhm he hn)
          (Eventually.of_forall fun w => (Real.exp_pos _).le)

include hK0 hKm hKhm he in
/-- ★ **The concentration inequality**: for `0 < a < κ`, `π{K < a} > 0` and `n ≥ 0`,
`μ̂_n{K ≥ κ} ≤ (π(univ)/π{K < a}) e^{−n(κ − a − 2e)}`. -/
theorem gibbsMass_ge_le {κ a n : ℝ} (hn : 0 ≤ n) (ha : 0 < π.real {w | K w < a}) :
    mass π Kh n {w | κ ≤ K w} ≤
      π.real univ / π.real {w | K w < a} * Real.exp (-n * (κ - a - 2 * e)) := by
  unfold mass
  have hZ := normaliser_ge π hK0 hKm hKhm he (a := a) hn
  have hZpos : 0 < normaliser π Kh n :=
    lt_of_lt_of_le (mul_pos ha (Real.exp_pos _)) hZ
  rw [div_le_iff₀ hZpos]
  calc ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π
      ≤ π.real univ * Real.exp (-n * (κ - e)) := setIntegral_exp_ge_le π hK0 hKm hKhm he hn
    _ = π.real univ / π.real {w | K w < a} * Real.exp (-n * (κ - a - 2 * e)) *
          (π.real {w | K w < a} * Real.exp (-n * (a + e))) := by
        have hexp : Real.exp (-n * (κ - a - 2 * e)) * Real.exp (-n * (a + e)) =
            Real.exp (-n * (κ - e)) := by rw [← Real.exp_add]; congr 1; ring
        rw [← hexp]
        field_simp
    _ ≤ π.real univ / π.real {w | K w < a} * Real.exp (-n * (κ - a - 2 * e)) *
          normaliser π Kh n :=
        mul_le_mul_of_nonneg_left hZ (by positivity)

end Gibbs

/-! ### Pathwise asymptotics -/

namespace Gibbs

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {K : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

include hK0 hKm hpos hKhm hunif in
/-- ★ **Pathwise concentration**: with the approximate phases converging uniformly to `K`, the mass
of every sublevel complement `{K ≥ κ}`, `κ > 0`, tends to `0`. -/
theorem tendsto_gibbsMass_ge {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => mass π (Kh n) n {w | κ ≤ K w}) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop, |mass π (Kh n) n {w | κ ≤ K w}| ≤
      π.real univ / π.real {w | K w < κ / 4} * Real.exp (-(κ / 4) * n) := by
    filter_upwards [hunif (κ / 8) (by positivity), eventually_ge_atTop 0] with n hn hn0
    have hnn : 0 ≤ mass π (Kh n) n {w | κ ≤ K w} := by
      unfold mass
      exact div_nonneg (setIntegral_nonneg (measurableSet_le measurable_const hKm)
        fun w _ => (Real.exp_pos _).le) (integral_nonneg fun w => (Real.exp_pos _).le)
    rw [abs_of_nonneg hnn]
    refine (gibbsMass_ge_le π hK0 hKm (hKhm n) hn (a := κ / 4) (Nat.cast_nonneg n)
      (hpos _ (by positivity))).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (div_nonneg measureReal_nonneg measureReal_nonneg)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine squeeze_zero_norm' hbound ?_
  have h : Tendsto (fun n : ℕ => Real.exp (-(κ / 4 * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  have h' := h.const_mul (π.real univ / π.real {w | K w < κ / 4})
  rw [mul_zero] at h'
  refine h'.congr' (Eventually.of_forall fun n => ?_)
  simp only [neg_mul]

include hK0 hKm hpos in
/-- **The almost-sure wrapper**: if the empirical phases converge uniformly almost surely (a
uniform law of large numbers, stated as a hypothesis), the sublevel-complement mass tends to `0`
almost surely. -/
theorem ae_tendsto_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
    (hunif : ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n ω w - K w| ≤ ε)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => mass π (Kh n ω) n {w | κ ≤ K w}) atTop (𝓝 0) := by
  filter_upwards [hunif] with ω hω
  exact tendsto_gibbsMass_ge π hK0 hKm hpos (fun n => Kh n ω) (hKhm · ω) hω hκ

include hK0 hKm hpos in
/-- **The in-probability wrapper**: if the uniform deviation exceeds each `ε` with vanishing
probability, the sublevel-complement mass exceeds each `δ > 0` with vanishing probability. -/
theorem tendsto_measure_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
    (hunif : ∀ ε > 0,
      Tendsto (fun n : ℕ => P {ω | ¬ ∀ w, |Kh n ω w - K w| ≤ ε}) atTop (𝓝 0))
    {κ : ℝ} (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P {ω | δ ≤ mass π (Kh n ω) n {w | κ ≤ K w}}) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => π.real univ / π.real {w | K w < κ / 4} *
      Real.exp (-(κ / 4 * (n : ℝ)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0:ℝ) < κ / 4))).const_mul
      (π.real univ / π.real {w | K w < κ / 4})
    rw [mul_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hunif (κ / 8)
    (by positivity)) (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hexp.eventually (gt_mem_nhds hδ)] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hgood
  have hle := gibbsMass_ge_le π hK0 hKm (hKhm n ω) hgood (κ := κ) (a := κ / 4)
    (Nat.cast_nonneg n) (hpos _ (by positivity))
  have h2 : Real.exp (-(n : ℝ) * (κ - κ / 4 - 2 * (κ / 8))) ≤ Real.exp (-(κ / 4 * (n : ℝ))) := by
    rw [Real.exp_le_exp]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h3 : π.real univ / π.real {w | K w < κ / 4} *
      Real.exp (-(n : ℝ) * (κ - κ / 4 - 2 * (κ / 8))) ≤
        π.real univ / π.real {w | K w < κ / 4} * Real.exp (-(κ / 4 * (n : ℝ))) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg measureReal_nonneg measureReal_nonneg)
  linarith

end Gibbs

/-! ### The certificate corollary -/

namespace Gibbs

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {K Kh : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKhm : Measurable Kh)
  {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

include hK0 hKm hKhm he in
/-- **Two-sided normaliser comparison**: `e^{−n e} Z_n ≤ Ẑ_n ≤ e^{n e} Z_n` for `n ≥ 0`. -/
theorem normaliser_le_normaliser {n : ℝ} (hn : 0 ≤ n) :
    Real.exp (-n * e) * normaliser π K n ≤ normaliser π Kh n ∧
      normaliser π Kh n ≤ Real.exp (n * e) * normaliser π K n := by
  have hKe : ∀ w, |K w - K w| ≤ e := fun w => by
    simp only [sub_self, abs_zero]; exact (abs_nonneg _).trans (he w)
  have hI := integrable_exp π hK0 hKm hKe hn
  have hI' := integrable_exp π hK0 hKhm he hn
  unfold normaliser
  constructor
  · rw [← integral_const_mul]
    refine integral_mono (hI.const_mul _) hI' fun w => ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    have := (abs_le.1 (he w)).2
    nlinarith
  · rw [← integral_const_mul]
    refine integral_mono hI' (hI.const_mul _) fun w => ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    have := (abs_le.1 (he w)).1
    nlinarith

include hK0 hKm hKhm he in
/-- **Log-normaliser comparison**: `|log Ẑ_n − log Z_n| ≤ n e` when `π ≠ 0` and `n ≥ 0`. -/
theorem abs_log_normaliser_sub_le [NeZero π] {n : ℝ} (hn : 0 ≤ n) :
    |Real.log (normaliser π Kh n) - Real.log (normaliser π K n)| ≤ n * e := by
  have hKe : ∀ w, |K w - K w| ≤ e := fun w => by
    simp only [sub_self, abs_zero]; exact (abs_nonneg _).trans (he w)
  have hZ : 0 < normaliser π K n := integral_exp_pos (integrable_exp π hK0 hKm hKe hn)
  have hZ' : 0 < normaliser π Kh n := integral_exp_pos (integrable_exp π hK0 hKhm he hn)
  obtain ⟨h1, h2⟩ := normaliser_le_normaliser π hK0 hKm hKhm he hn
  rw [abs_le, ← Real.log_div hZ'.ne' hZ.ne']
  constructor
  · have : Real.exp (-n * e) ≤ normaliser π Kh n / normaliser π K n := by
      rw [le_div_iff₀ hZ]; exact h1
    have := Real.log_le_log (Real.exp_pos _) this
    rwa [Real.log_exp, neg_mul] at this
  · have : normaliser π Kh n / normaliser π K n ≤ Real.exp (n * e) := by
      rw [div_le_iff₀ hZ]; exact h2
    have := Real.log_le_log (div_pos hZ' hZ) this
    rwa [Real.log_exp] at this

end Gibbs

namespace Gibbs

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π] [NeZero π]
  {K : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

include hK0 hKm hKhm hunif in
/-- ★ **The certificate corollary**: if the population free energy satisfies `log Z_n / n → 0`
(true under any leading-term certificate) and the empirical phases converge uniformly, then the
empirical free energy satisfies `log Ẑ_n / n → 0` as well. -/
theorem tendsto_log_normaliser_div
    (hZ : Tendsto (fun n : ℕ => Real.log (normaliser π K n) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (normaliser π (Kh n) n) / n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hZ ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hZ (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (hunif (ε / 2) (by positivity)).exists_forall_of_atTop
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn1 : (1:ℕ) ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have h1 := hN₁ n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have h2 := abs_log_normaliser_sub_le π hK0 hKm (hKhm n)
    (hN₂ n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))) (Nat.cast_nonneg n)
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have key : |Real.log (normaliser π (Kh n) n) / n - Real.log (normaliser π K n) / n| ≤ ε / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    linarith
  calc |Real.log (normaliser π (Kh n) n) / n|
      = |(Real.log (normaliser π (Kh n) n) / n - Real.log (normaliser π K n) / n) +
          Real.log (normaliser π K n) / n| := by ring_nf
    _ ≤ |Real.log (normaliser π (Kh n) n) / n - Real.log (normaliser π K n) / n| +
          |Real.log (normaliser π K n) / n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end Gibbs

/-! ### Constant-on-minimisers observables -/

namespace Gibbs

/-- **The compact gap lemma**: on a compact set `S` with `K ≥ 0` and `φ` continuous, `φ ≡ φ₀` on
`S ∩ {K = 0}` gives, for every `ε > 0`, a `κ > 0` with `|φ − φ₀| < ε` on `S ∩ {K < κ}`. -/
theorem exists_sublevel_of_eq_on_zeroSet {W : Type*} [TopologicalSpace W] [T2Space W]
    {S : Set W} (hS : IsCompact S) {K φ : W → ℝ} (hKc : ContinuousOn K S)
    (hφc : ContinuousOn φ S) (hK0 : ∀ w ∈ S, 0 ≤ K w) {φ₀ : ℝ}
    (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ > 0, ∀ w ∈ S, K w < κ → |φ w - φ₀| < ε := by
  set B : Set W := S ∩ (fun w => |φ w - φ₀|) ⁻¹' Ici ε with hB
  have hBc : IsCompact B := hS.of_isClosed_subset
    (((hφc.sub continuousOn_const).abs).preimage_isClosed_of_isClosed hS.isClosed isClosed_Ici)
    inter_subset_left
  by_cases hne : B.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hBc.exists_isMinOn hne (hKc.mono inter_subset_left)
    have hw₀S : w₀ ∈ S := hw₀.1
    have hpos : 0 < K w₀ := by
      rcases (hK0 w₀ hw₀S).lt_or_eq with h | h
      · exact h
      · exfalso
        have := hφ0 w₀ hw₀S h.symm
        have h2 : ε ≤ |φ w₀ - φ₀| := hw₀.2
        rw [this, sub_self, abs_zero] at h2
        exact absurd h2 (not_le.2 hε)
    refine ⟨K w₀, hpos, fun w hw hlt => ?_⟩
    by_contra hcon
    have hwB : w ∈ B := ⟨hw, not_lt.1 hcon⟩
    exact absurd (hmin hwB) (not_le.2 hlt)
  · refine ⟨1, one_pos, fun w hw _ => ?_⟩
    by_contra hcon
    exact hne ⟨w, hw, not_lt.1 hcon⟩

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hπS : ∀ᵐ w ∂π, w ∈ S) {K Kh φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (hKhm : Measurable Kh) (hφm : Measurable φ) {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

include hπS hK0 hKm hKhm hφm he in
/-- **The observable bound**: if `|φ − φ₀| < ε` on `S ∩ {K < κ}` and `|φ − φ₀| ≤ B` on `S`
(`π`-a.e. supported on `S`), then `|μ̂_n(φ) − φ₀| ≤ ε + B μ̂_n{K ≥ κ}` for `n ≥ 0`, provided the
normaliser is positive. -/
theorem abs_expectation_sub_le {φ₀ ε B κ n : ℝ} (hn : 0 ≤ n) (hZ : 0 < normaliser π Kh n)
    (hεS : ∀ w ∈ S, K w < κ → |φ w - φ₀| ≤ ε) (hBS : ∀ w ∈ S, |φ w - φ₀| ≤ B) (hε : 0 ≤ ε) :
    |expectation π Kh n φ - φ₀| ≤ ε + B * mass π Kh n {w | κ ≤ K w} := by
  have hI := integrable_exp π hK0 hKhm he hn
  have hφI : Integrable (fun w => (φ w - φ₀) * Real.exp (-n * Kh w)) π := by
    refine (hI.const_mul B).mono' ((hφm.sub measurable_const).mul
      (Real.measurable_exp.comp (measurable_const.mul hKhm))).aestronglyMeasurable ?_
    filter_upwards [hπS] with w hw
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hBS w hw) (Real.exp_pos _).le
  have hφI' : Integrable (fun w => φ w * Real.exp (-n * Kh w)) π := by
    have : (fun w => φ w * Real.exp (-n * Kh w)) =
        fun w => (φ w - φ₀) * Real.exp (-n * Kh w) + φ₀ * Real.exp (-n * Kh w) := by
      funext w; ring
    rw [this]; exact hφI.add (hI.const_mul _)
  have hmeas : MeasurableSet {w | κ ≤ K w} := measurableSet_le measurable_const hKm
  -- the numerator identity
  have hnum : expectation π Kh n φ - φ₀ =
      (∫ w, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π) / normaliser π Kh n := by
    have : ∫ w, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π =
        (∫ w, φ w * Real.exp (-n * Kh w) ∂π) - φ₀ * normaliser π Kh n := by
      unfold normaliser
      rw [← integral_const_mul, ← integral_sub hφI' (hI.const_mul _)]
      congr 1; funext w; ring
    unfold expectation
    rw [this, sub_div, mul_div_assoc, div_self hZ.ne', mul_one]
  rw [hnum, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  -- split the integral
  have hsplit : ∫ w, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π =
      (∫ w in {w | κ ≤ K w}ᶜ, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π) +
        ∫ w in {w | κ ≤ K w}, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π := by
    rw [← integral_add_compl hmeas hφI, add_comm]
  have hZsplit : normaliser π Kh n =
      (∫ w in {w | κ ≤ K w}ᶜ, Real.exp (-n * Kh w) ∂π) +
        ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π := by
    unfold normaliser; rw [← integral_add_compl hmeas hI, add_comm]
  have h1 : |∫ w in {w | κ ≤ K w}ᶜ, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π| ≤
      ε * ∫ w in {w | κ ≤ K w}ᶜ, Real.exp (-n * Kh w) ∂π := by
    rw [← integral_const_mul]
    refine (norm_integral_le_of_norm_le (f := fun w => (φ w - φ₀) * Real.exp (-n * Kh w))
      ((hI.const_mul ε).integrableOn) ?_)
    rw [ae_restrict_iff' hmeas.compl]
    filter_upwards [hπS] with w hw hwc
    have hwc' : K w < κ := not_le.1 hwc
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hεS w hw hwc') (Real.exp_pos _).le
  have h2 : |∫ w in {w | κ ≤ K w}, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π| ≤
      B * ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π := by
    rw [← integral_const_mul]
    refine (norm_integral_le_of_norm_le (f := fun w => (φ w - φ₀) * Real.exp (-n * Kh w))
      ((hI.const_mul B).integrableOn) ?_)
    rw [ae_restrict_iff' hmeas]
    filter_upwards [hπS] with w hw _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hBS w hw) (Real.exp_pos _).le
  have hc0 : 0 ≤ ∫ w in {w | κ ≤ K w}ᶜ, Real.exp (-n * Kh w) ∂π :=
    setIntegral_nonneg hmeas.compl fun w _ => (Real.exp_pos _).le
  have hc1 : 0 ≤ ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π :=
    setIntegral_nonneg hmeas fun w _ => (Real.exp_pos _).le
  have hmass : B * mass π Kh n {w | κ ≤ K w} * normaliser π Kh n =
      B * ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π := by
    unfold mass; field_simp
  calc |∫ w, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π|
      ≤ |∫ w in {w | κ ≤ K w}ᶜ, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π| +
          |∫ w in {w | κ ≤ K w}, (φ w - φ₀) * Real.exp (-n * Kh w) ∂π| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ ε * (∫ w in {w | κ ≤ K w}ᶜ, Real.exp (-n * Kh w) ∂π) +
          B * ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π := add_le_add h1 h2
    _ ≤ ε * normaliser π Kh n + B * mass π Kh n {w | κ ≤ K w} * normaliser π Kh n := by
        rw [hmass, hZsplit]
        have : 0 ≤ ε * ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π := mul_nonneg hε hc1
        nlinarith
    _ = (ε + B * mass π Kh n {w | κ ≤ K w}) * normaliser π Kh n := by ring

end Gibbs

namespace Gibbs

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 hKhm hunif in
/-- ★★ **Constant-on-minimisers observables concentrate**: on a compact support, an observable
continuous on the support and equal to `φ₀` on the zero set of `K` has empirical posterior
expectation converging to `φ₀`, provided the empirical phases converge uniformly to `K` (all
sublevel sets of `K` have positive prior mass). -/
theorem tendsto_expectation_of_eq_on_zeroSet :
    Tendsto (fun n : ℕ => expectation π (Kh n) n φ) atTop (𝓝 φ₀) := by
  obtain ⟨B₀, hB₀⟩ := hS.exists_bound_of_continuousOn hφc
  set B : ℝ := |B₀| + |φ₀| with hBdef
  have hBS : ∀ w ∈ S, |φ w - φ₀| ≤ B := fun w hw => by
    have := hB₀ w hw
    rw [Real.norm_eq_abs] at this
    calc |φ w - φ₀| ≤ |φ w| + |φ₀| := abs_sub _ _
      _ ≤ B := by rw [hBdef]; linarith [le_abs_self B₀]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨κ, hκ, hκS⟩ := exists_sublevel_of_eq_on_zeroSet hS hKc hφc (fun w _ => hK0 w) hφ0
    (half_pos hε)
  have hmass := tendsto_gibbsMass_ge π hK0 hKm hpos Kh hKhm hunif hκ
  have hsmall : ∀ᶠ n : ℕ in atTop, B * mass π (Kh n) n {w | κ ≤ K w} < ε / 2 := by
    have h := hmass.const_mul B
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N₁, hN₁⟩ := hsmall.exists_forall_of_atTop
  obtain ⟨N₂, hN₂⟩ := (hunif 1 one_pos).exists_forall_of_atTop
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ := hN₁ n (le_trans (le_max_left _ _) hn)
  have hn₂ := hN₂ n (le_trans (le_max_right _ _) hn)
  have hZ : 0 < normaliser π (Kh n) n :=
    lt_of_lt_of_le (mul_pos (hpos 1 one_pos) (Real.exp_pos _))
      (normaliser_ge π hK0 hKm (hKhm n) hn₂ (a := 1) (Nat.cast_nonneg n))
  have hle := abs_expectation_sub_le π hπS hK0 hKm (hKhm n) hφm hn₂ (Nat.cast_nonneg n) hZ
    (fun w hw hlt => (hκS w hw hlt).le) hBS (half_pos hε).le
  rw [Real.dist_eq]
  linarith

omit [T2Space W] [MeasurableSpace W] in
include hS hK0 hKc in
/-- **Neighbourhoods of the zero set contain sublevels**: on a compact `S` with `K ≥ 0` continuous,
an open `U` containing `S ∩ {K = 0}` contains `S ∩ {K < κ}` for some `κ > 0` (the compact set
`S \ U` carries a positive minimum of `K`). -/
theorem exists_sublevel_subset_of_isOpen {U : Set W} (hU : IsOpen U)
    (hU0 : ∀ w ∈ S, K w = 0 → w ∈ U) : ∃ κ > 0, ∀ w ∈ S, K w < κ → w ∈ U := by
  have hBc : IsCompact (S \ U) := hS.diff hU
  by_cases hne : (S \ U).Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hBc.exists_isMinOn hne (hKc.mono sdiff_subset)
    have hpos : 0 < K w₀ := by
      rcases (hK0 w₀).lt_or_eq with h | h
      · exact h
      · exact absurd (hU0 w₀ hw₀.1 h.symm) hw₀.2
    refine ⟨K w₀, hpos, fun w hw hlt => ?_⟩
    by_contra hcon
    exact absurd (hmin ⟨hw, hcon⟩) (not_le.2 hlt)
  · refine ⟨1, one_pos, fun w hw _ => ?_⟩
    by_contra hcon
    exact hne ⟨w, hw, hcon⟩

omit [T2Space W] in
include hS hπS hK0 hKm hKc hpos hKhm hunif in
/-- ★ **Concentration on every neighbourhood of the zero set**: on a compact set carrying the
prior, with `K` continuous, the empirical posterior mass of the complement of any open
neighbourhood of `S ∩ {K = 0}` tends to `0` under uniform convergence of the empirical phases. -/
theorem tendsto_mass_compl_of_isOpen {U : Set W} (hU : IsOpen U)
    (hU0 : ∀ w ∈ S, K w = 0 → w ∈ U) :
    Tendsto (fun n : ℕ => mass π (Kh n) n Uᶜ) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hκU⟩ := exists_sublevel_subset_of_isOpen hS hK0 hKc hU hU0
  have hmass := tendsto_gibbsMass_ge π hK0 hKm hpos Kh hKhm hunif hκ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmass
    (Eventually.of_forall fun n => ?_) ?_
  · unfold mass
    exact div_nonneg (setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun w =>
      (Real.exp_pos _).le)) (integral_nonneg fun w => (Real.exp_pos _).le)
  · filter_upwards [hunif 1 one_pos] with n hn
    unfold mass
    refine div_le_div_of_nonneg_right ?_ (integral_nonneg fun w => (Real.exp_pos _).le)
    refine setIntegral_mono_set ((integrable_exp π hK0 (hKhm n) hn
      (Nat.cast_nonneg n)).integrableOn) (Eventually.of_forall fun w => (Real.exp_pos _).le) ?_
    filter_upwards [hπS] with w hw
    intro hwU
    by_contra hlt
    exact hwU (hκU w hw (not_le.1 hlt))

end Gibbs

/-! ### Coefficient consistency -/

namespace Gibbs

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)

include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 in
/-- **The population special case**: the population posterior expectation of a
constant-on-minimisers observable converges to `φ₀` (the case `K̂_n = K`). -/
theorem tendsto_expectation_of_eq_on_zeroSet_population :
    Tendsto (fun n : ℕ => expectation π K n φ) atTop (𝓝 φ₀) :=
  tendsto_expectation_of_eq_on_zeroSet π hS hπS hK0 hKm hKc hφm hφc hpos hφ0 (fun _ => K)
    (fun _ => hKm) fun ε hε => Eventually.of_forall fun _ w => by
      simp only [sub_self, abs_zero]; exact hε.le

include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 in
/-- ★ **Coefficient consistency**: if `a_n Z_n[1] → c₁ > 0` and `a_n Z_n[φ] → c_φ` along the
population posterior, then `c_φ = φ₀ c₁` — by uniqueness of limits, with no linearity API for
the coefficient functional. -/
theorem coeff_eq_of_eq_on_zeroSet {a : ℕ → ℝ} {c₁ cφ : ℝ} (hc₁ : 0 < c₁)
    (h₁ : Tendsto (fun n : ℕ => a n * normaliser π K n) atTop (𝓝 c₁))
    (hφ : Tendsto (fun n : ℕ => a n * ∫ w, φ w * Real.exp (-(n : ℝ) * K w) ∂π) atTop (𝓝 cφ)) :
    cφ = φ₀ * c₁ := by
  have hdiv := hφ.div h₁ hc₁.ne'
  have hZ : ∀ n : ℕ, 0 < normaliser π K n := fun n =>
    lt_of_lt_of_le (mul_pos (hpos 1 one_pos) (Real.exp_pos _))
      (normaliser_ge π hK0 hKm hKm (Kh := K) (e := 0) (fun w => by simp) (a := 1)
        (Nat.cast_nonneg n))
  have ha : ∀ᶠ n : ℕ in atTop, a n ≠ 0 := by
    filter_upwards [h₁.eventually (eventually_ne_nhds hc₁.ne')] with n hn
    exact fun h0 => hn (by rw [h0, zero_mul])
  have hlim : Tendsto (fun n : ℕ => expectation π K n φ) atTop (𝓝 (cφ / c₁)) := by
    refine hdiv.congr' (ha.mono fun n hn => ?_)
    unfold expectation
    simp only [Pi.div_apply]
    rw [mul_div_mul_left _ _ hn]
  have := tendsto_nhds_unique hlim
    (tendsto_expectation_of_eq_on_zeroSet_population π hS hπS hK0 hKm hKc hφm hφc hpos hφ0)
  rw [div_eq_iff hc₁.ne'] at this
  exact this

include hS hπS hK0 hKm hKc hφm hφc hpos hφ0 in
/-- **Coefficient consistency from certificates** (real sample-size variable): if the
population normaliser and the `φ`-weighted integral have leading-term certificates at the same
pair with `c₁ > 0`, then `c_φ = φ₀ c₁`. -/
theorem coeff_eq_of_hasLeadingTerm {c₁ cφ lam : ℝ} {k : ℕ} (hc₁ : 0 < c₁)
    (h₁ : HasLeadingTerm (fun N => normaliser π K N) c₁ lam k)
    (hφ : HasLeadingTerm (fun N => ∫ w, φ w * Real.exp (-N * K w) ∂π) cφ lam k) :
    cφ = φ₀ * c₁ :=
  coeff_eq_of_eq_on_zeroSet π hS hπS hK0 hKm hKc hφm hφc hpos hφ0 (a := fun n : ℕ =>
      (powLogScale lam k n)⁻¹) hc₁
    ((h₁.comp tendsto_natCast_atTop_atTop).congr' (Eventually.of_forall fun n => by
      simp only [Function.comp, div_eq_inv_mul]))
    ((hφ.comp tendsto_natCast_atTop_atTop).congr' (Eventually.of_forall fun n => by
      simp only [Function.comp, div_eq_inv_mul]))

end Gibbs

end Grammar
