import Grammar.CovarianceInterpolation
import Grammar.GaussianBound

/-!
# Compact base I: finite quantisation and the compact-base denominator

For a nonempty compact metric space `K` with a finite Borel measure `ρ`, the finite-resolution
quantities of the quartet have compact-base analogues: `D_ρ(g) = ∫_K S_λ(g(x)) dρ(x)`,
`M₂,ρ(g) = ∫ S_{λ+1}(g)/D`, `H_ρ(g) = ∫ g S_{λ+1/2}(g)/D`. This file provides

* **finite quantisation** (`exists_measurable_finiteRange_approx`): for every `ε > 0` a measurable
  map `q : K → K` with finite range and `dist x (q x) < ε` (Mathlib's nearest-point simple
  functions along a dense sequence, with a finite subcover to fix the depth); the pushforward
  `ρ.map q` is a mass-preserving finitely supported approximation of `ρ`;
* **partition-independent deterministic bounds** in terms of `R = ‖g‖_∞` and `M = ρ(K)`:
  `M e^{−2β} λ^{−1}(1+R)^{−2λ} ≤ D_ρ(g) ≤ M e^{βR²/2}(β/2)^{−λ}Γ(λ)` (`compactD_le`, `le_compactD`),
  hence `D_ρ(g) > 0` and `|log D_ρ(g)| ≤ |log M| + C_{β,λ} + βR²/2 + 2λR` (`abs_log_compactD_le`);
* **pathwise convergence under quantisation**: for continuous `g`, `∫ f∘q_n dρ → ∫ f dρ` when the
  mesh `ε_n → 0` (`tendsto_integral_comp_quantise`, dominated convergence with the sup norm), so
  `D_{ρ∘q_n⁻¹}(g) → D_ρ(g)`, `log D → log D`, and likewise for `M₂` and `H`
  (`tendsto_compactD_map`, `tendsto_log_compactD_map`, `tendsto_compactM2_map`,
  `tendsto_compactH_map`).

Convergence is pathwise for each fixed `g`; it is not uniform on sup-norm balls of `C(K)`. The
covariance functional `Q` and `V` (which need the kernel) and the transfer of the Gaussian
identities are the next unit. Non-claims: no Gaussian process is constructed here.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Quantise

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K]

/-- **Finite quantisation of a compact metric space**: for every `ε > 0` there is a measurable map
with finite range moving every point by less than `ε`. -/
theorem exists_measurable_finiteRange_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ q : K → K, Measurable q ∧ (Set.range q).Finite ∧ ∀ x, dist x (q x) < ε := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq K
  have hcover : (Set.univ : Set K) ⊆ ⋃ k : ℕ, Metric.ball (e k) ε := fun x _ => by
    obtain ⟨k, hk⟩ := he.exists_dist_lt x hε
    exact Set.mem_iUnion.2 ⟨k, Metric.mem_ball.2 hk⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun k => Metric.ball (e k) ε)
    (fun k => Metric.isOpen_ball) hcover
  refine ⟨SimpleFunc.nearestPt e (t.sup id), (SimpleFunc.nearestPt e (t.sup id)).measurable,
    (SimpleFunc.nearestPt e (t.sup id)).finite_range, fun x => ?_⟩
  obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have hkN : k ≤ t.sup id := Finset.le_sup (f := id) hkt
  have h := SimpleFunc.edist_nearestPt_le e x hkN
  rw [dist_comm, ← edist_lt_ofReal]
  refine lt_of_le_of_lt h (edist_lt_ofReal.2 ?_)
  rw [dist_comm]
  exact Metric.mem_ball.1 hxk

/-- A sequence of quantisations with mesh `1/(n+1)`. -/
theorem exists_quantisation_seq :
    ∃ q : ℕ → K → K, (∀ n, Measurable (q n)) ∧ (∀ n, (Set.range (q n)).Finite) ∧
      ∀ n x, dist x (q n x) < 1 / ((n : ℝ) + 1) := by
  choose q hq using fun n : ℕ =>
    exists_measurable_finiteRange_approx (K := K) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  exact ⟨q, fun n => (hq n).1, fun n => (hq n).2.1, fun n => (hq n).2.2⟩

omit [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K] in
/-- Convergence of the quantised points. -/
theorem tendsto_quantise {q : ℕ → K → K} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) (x : K) : Tendsto (fun n => q n x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hε
  rw [dist_comm]
  exact (hqε n x).le

omit [Nonempty K] in
/-- **Pathwise convergence under quantisation**: for a continuous `f` on the compact base,
`∫ f∘q_n dρ → ∫ f dρ` when the mesh tends to zero. -/
theorem tendsto_integral_comp_quantise (ρ : Measure K) [IsFiniteMeasure ρ] (f : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => ∫ x, f (q n x) ∂ρ) atTop (𝓝 (∫ x, f x ∂ρ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp (hq n)).aestronglyMeasurable) (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun x => ?_)
  exact (f.continuous.tendsto x).comp (tendsto_quantise hε hqε x)

omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] in
/-- The pushforward `ρ.map q` has the same total mass. -/
theorem map_quantise_univ (ρ : Measure K) {q : K → K} (hq : Measurable q) :
    ρ.map q univ = ρ univ := by
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ]

end Quantise

/-! ### The compact-base denominator and its bounds -/

section CompactD

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ}

/-- `D_ρ(g) = ∫_K S_λ(g(x)) dρ(x)`. -/
noncomputable def compactD (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  ∫ x, fluctuation β lam (g x) ∂ρ

/-- `M₂,ρ(g) = ∫ S_{λ+1}(g) dρ / D_ρ(g)`. -/
noncomputable def compactM2 (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  (∫ x, fluctuation β (lam + 1) (g x) ∂ρ) / compactD β lam ρ g

/-- `H_ρ(g) = ∫ g S_{λ+1/2}(g) dρ / D_ρ(g)`. -/
noncomputable def compactH (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  (∫ x, g x * fluctuation β (lam + 1 / 2) (g x) ∂ρ) / compactD β lam ρ g

/-- The Gaussian upper bound on `S_λ` over `|a| ≤ R`. -/
theorem fluctuation_le_of_abs_le (hβ : 0 < β) (hlam : 0 < lam) {a R : ℝ} (ha : |a| ≤ R) :
    fluctuation β lam a ≤ Real.exp (β * R ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam := by
  refine (fluctuation_le_gaussian β a lam hβ hlam).trans ?_
  have hR : 0 ≤ R := (abs_nonneg a).trans ha
  have : a ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith))
    (Real.rpow_nonneg (by positivity) _)) ((Real.Gamma_pos_of_pos hlam).le)

/-- The lower bound on `S_λ` over `|a| ≤ R`. -/
theorem le_fluctuation_of_abs_le (hβ : 0 < β) (hlam : 0 < lam) {a R : ℝ} (ha : |a| ≤ R) :
    Real.exp (-2 * β) / lam * (1 + R) ^ (-(2 * lam)) ≤ fluctuation β lam a := by
  refine le_trans ?_ (fluctuation_ge_lower hβ hlam a)
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.exp_pos _).le hlam.le)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

variable (ρ : Measure K) [IsFiniteMeasure ρ]

theorem integrable_fluctuation_comp (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    Integrable (fun x => fluctuation β lam (g x)) ρ :=
  Integrable.of_bound (((continuous_fluctuation β lam hβ hlam).comp
    g.continuous).measurable.aestronglyMeasurable)
    (Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (fluctuation_pos β lam _ hβ hlam)]
      exact fluctuation_le_of_abs_le hβ hlam
        ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm x))

/-- `D_ρ(g) ≤ ρ(K) e^{βR²/2}(β/2)^{−λ}Γ(λ)` for `‖g‖ ≤ R`. -/
theorem compactD_le (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {R : ℝ} (hR : ‖g‖ ≤ R) :
    compactD β lam ρ g ≤
      ρ.real univ * (Real.exp (β * R ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam) := by
  unfold compactD
  rw [← smul_eq_mul, ← integral_const]
  exact integral_mono (integrable_fluctuation_comp ρ hβ hlam g) (integrable_const _) fun x =>
    fluctuation_le_of_abs_le hβ hlam (((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm x).trans hR)

/-- `ρ(K) e^{−2β}λ^{−1}(1+R)^{−2λ} ≤ D_ρ(g)` for `‖g‖ ≤ R`. -/
theorem le_compactD (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {R : ℝ} (hR : ‖g‖ ≤ R) :
    ρ.real univ * (Real.exp (-2 * β) / lam * (1 + R) ^ (-(2 * lam))) ≤ compactD β lam ρ g := by
  unfold compactD
  rw [← smul_eq_mul, ← integral_const]
  exact integral_mono (integrable_const _) (integrable_fluctuation_comp ρ hβ hlam g) fun x =>
    le_fluctuation_of_abs_le hβ hlam (((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm x).trans hR)

theorem compactD_pos (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) :
    0 < compactD β lam ρ g := by
  have hM : 0 < ρ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hρ) (measure_ne_top _ _)
  refine lt_of_lt_of_le ?_ (le_compactD ρ hβ hlam g le_rfl)
  exact mul_pos hM (mul_pos (div_pos (Real.exp_pos _) hlam)
    (Real.rpow_pos_of_pos (by positivity) _))

/-- **The quadratic log bound**, partition-independent:
`|log D_ρ(g)| ≤ |log ρ(K)| + C_{β,λ} + βR²/2 + 2λR` for `‖g‖ ≤ R`. -/
theorem abs_log_compactD_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ‖g‖ ≤ R) :
    |Real.log (compactD β lam ρ g)| ≤
      |Real.log (ρ.real univ)| +
        (|Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)| + 2 * β + |Real.log lam|) +
        β * R ^ 2 / 2 + 2 * lam * R := by
  have hM : 0 < ρ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hρ) (measure_ne_top _ _)
  have hD := compactD_pos ρ hβ hlam hρ g
  have hΓ : 0 < (β / 2) ^ (-lam) * Real.Gamma lam :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hlam)
  have hup : Real.log (compactD β lam ρ g) ≤
      Real.log (ρ.real univ) + Real.log ((β / 2) ^ (-lam) * Real.Gamma lam) + β * R ^ 2 / 2 := by
    calc Real.log (compactD β lam ρ g)
        ≤ Real.log (ρ.real univ * (Real.exp (β * R ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam)) :=
          Real.log_le_log hD (compactD_le ρ hβ hlam g hR)
      _ = Real.log (ρ.real univ) + Real.log ((β / 2) ^ (-lam) * Real.Gamma lam) +
            β * R ^ 2 / 2 := by
          rw [show Real.exp (β * R ^ 2 / 2) * (β / 2) ^ (-lam) * Real.Gamma lam =
            Real.exp (β * R ^ 2 / 2) * ((β / 2) ^ (-lam) * Real.Gamma lam) by ring,
            Real.log_mul hM.ne' (mul_pos (Real.exp_pos _) hΓ).ne',
            Real.log_mul (Real.exp_pos _).ne' hΓ.ne', Real.log_exp]
          ring
  have hlow : Real.log (ρ.real univ) - 2 * β - Real.log lam - 2 * lam * R ≤
      Real.log (compactD β lam ρ g) := by
    have h1R : 0 < 1 + R := by linarith
    have hlogR : Real.log (1 + R) ≤ R := by
      have := Real.log_le_sub_one_of_pos h1R
      linarith
    have hpos : 0 < Real.exp (-2 * β) / lam * (1 + R) ^ (-(2 * lam)) :=
      mul_pos (div_pos (Real.exp_pos _) hlam) (Real.rpow_pos_of_pos h1R _)
    calc Real.log (ρ.real univ) - 2 * β - Real.log lam - 2 * lam * R
        ≤ Real.log (ρ.real univ) + (-2 * β - Real.log lam + -(2 * lam) * Real.log (1 + R)) := by
          nlinarith [mul_le_mul_of_nonneg_left hlogR (by linarith : (0 : ℝ) ≤ 2 * lam)]
      _ = Real.log (ρ.real univ * (Real.exp (-2 * β) / lam * (1 + R) ^ (-(2 * lam)))) := by
          rw [Real.log_mul hM.ne' hpos.ne', Real.log_mul (div_pos (Real.exp_pos _) hlam).ne'
            (Real.rpow_pos_of_pos h1R _).ne', Real.log_div (Real.exp_pos _).ne' hlam.ne',
            Real.log_exp, Real.log_rpow h1R]
      _ ≤ Real.log (compactD β lam ρ g) :=
          Real.log_le_log (mul_pos hM hpos) (le_compactD ρ hβ hlam g hR)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (ρ.real univ)),
      abs_nonneg (Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)), le_abs_self (Real.log lam),
      mul_nonneg hβ.le (sq_nonneg R)]
  · linarith [le_abs_self (Real.log (ρ.real univ)),
      le_abs_self (Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)), abs_nonneg (Real.log lam),
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlam.le) hR0]

/-! ### Convergence under mass-preserving atomic approximation -/

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactD_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactD β lam (ρ.map q) g = ∫ x, fluctuation β lam (g (q x)) ∂ρ := by
  unfold compactD
  exact integral_map hq.aemeasurable
    ((continuous_fluctuation β lam hβ hlam).comp g.continuous).measurable.aestronglyMeasurable

/-- The continuous map `x ↦ S_λ(g x)`. -/
noncomputable def fluctuationC (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    C(K, ℝ) :=
  ⟨fun x => fluctuation β lam (g x), (continuous_fluctuation β lam hβ hlam).comp g.continuous⟩

/-- The continuous map `x ↦ g x * S_λ(g x)`. -/
noncomputable def fluctuationMulC (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    C(K, ℝ) :=
  ⟨fun x => g x * fluctuation β lam (g x),
    g.continuous.mul ((continuous_fluctuation β lam hβ hlam).comp g.continuous)⟩

/-- **`D` converges under quantisation**: `D_{ρ∘q_n⁻¹}(g) → D_ρ(g)` for each continuous `g`. -/
theorem tendsto_compactD_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : ℕ → K → K}
    (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => compactD β lam (ρ.map (q n)) g) atTop (𝓝 (compactD β lam ρ g)) := by
  simp_rw [compactD_map ρ hβ hlam g (hq _)]
  exact tendsto_integral_comp_quantise ρ (fluctuationC β lam hβ hlam g) hq hε hqε

theorem tendsto_log_compactD_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => Real.log (compactD β lam (ρ.map (q n)) g)) atTop
      (𝓝 (Real.log (compactD β lam ρ g))) :=
  (Real.continuousAt_log (compactD_pos ρ hβ hlam hρ g).ne').tendsto.comp
    (tendsto_compactD_map ρ hβ hlam g hq hε hqε)

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactM2_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactM2 β lam (ρ.map q) g =
      (∫ x, fluctuation β (lam + 1) (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactM2
  rw [integral_map (f := fun x => fluctuation β (lam + 1) (g x)) hq.aemeasurable
    ((continuous_fluctuation β (lam + 1) hβ (by linarith)).comp
      g.continuous).measurable.aestronglyMeasurable]

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactH_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactH β lam (ρ.map q) g =
      (∫ x, g (q x) * fluctuation β (lam + 1 / 2) (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactH
  rw [integral_map (f := fun x => g x * fluctuation β (lam + 1 / 2) (g x)) hq.aemeasurable
    (g.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ
      (by linarith)).comp g.continuous)).measurable.aestronglyMeasurable]

/-- **`M₂` converges under quantisation.** -/
theorem tendsto_compactM2_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => compactM2 β lam (ρ.map (q n)) g) atTop (𝓝 (compactM2 β lam ρ g)) := by
  simp_rw [compactM2_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantise ρ (fluctuationC β (lam + 1) hβ (by linarith) g) hq hε
    hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

/-- **`H` converges under quantisation.** -/
theorem tendsto_compactH_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n => compactH β lam (ρ.map (q n)) g) atTop (𝓝 (compactH β lam ρ g)) := by
  simp_rw [compactH_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantise ρ (fluctuationMulC β (lam + 1 / 2) hβ (by linarith) g)
    hq hε hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

omit [CompactSpace K] [IsFiniteMeasure ρ] in
/-- The quantised measure is finitely supported: `ρ.map q` is carried by the finite set
`range q`. -/
theorem map_quantise_compl_range {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite) : ρ.map q (Set.range q)ᶜ = 0 := by
  rw [Measure.map_apply hq hfin.measurableSet.compl]
  have : q ⁻¹' (Set.range q)ᶜ = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

end CompactD

end Grammar
