# Fidelity review v39 — units 313–315 (Programme Q, N2 gate: exact energy identity, moment recurrence, coefficient transport)

Context: your #38 design (N2 Route B; gate after two units: "exhibit the coefficient recurrence and the precise two-term remainder requirement") and review v38 §6 (GO for 313–315 with side conditions: `μ > 0`, `β > 0` for the moment recurrence; the `i = 0` case harmless; coefficient transport as a theorem about the actual `coeffAt` representation under shift; `C(λ,m) = 0` for the specialisations; split `m = 1` explicitly in the correction). Units 313–315 (four files: 313, 314, 315a shift lemmas, 315 transport) are done; everything compiles (branch `tide/programme-q`, no `sorry`, no added `axiom`). This is the gate review before the two-term quotient (unit 316).

Frozen interfaces (beyond earlier reviews):
```lean
noncomputable def fluctMoment (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t
theorem phaseKernel_zero_zero (β t : ℝ) : phaseKernel β 0 0 t = Real.exp (-(β * t))
theorem integrableOn_fluct (β a : ℝ) (hβ : 0 < β) (p : ℕ) {ν : ℝ} (hν : 0 < ν) (i : ℕ) : IntegrableOn (fun t => t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) (Ioi 0)
theorem integral_Ioi_mul_deriv_eq_deriv_mul (hu : ∀ x ∈ Ioi a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Ioi a, HasDerivAt v (v' x) x) (huv' : IntegrableOn (u * v') (Ioi a)) (hu'v : IntegrableOn (u' * v) (Ioi a)) (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) : ∫ x in Ioi a, u x * v' x = b' - a' - ∫ x in Ioi a, u' x * v x   -- Mathlib
theorem tendsto_log_mul_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) : Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0)   -- Mathlib
abbrev PowLogRep := List (ℝ × ℕ × ℝ)   -- triples (exponent, log degree, coefficient)
def PowLogRep.smul (r : ℝ) (c : PowLogRep) : PowLogRep := c.map fun t => (t.1, t.2.1, r * t.2.2)
def PowLogRep.shift (a : ℝ) (c : PowLogRep) : PowLogRep := c.map fun t => (t.1 + a, t.2.1, t.2.2)
noncomputable def gRep (α : ℝ) : ℕ → PowLogRep | 0 => [(1, 0, 1 / α), (α + 1, 0, -(1 / α))] | j + 1 => (1, j + 1, 1 / α) :: PowLogRep.smul (-(((j : ℝ) + 1) / α)) (gRep α j)
noncomputable def PowLogRep.basisConv (w : ℝ) (t : ℝ × ℕ × ℝ) : PowLogRep := if t.1 = w + 1 then [(t.1, t.2.1 + 1, t.2.2 / ((t.2.1 : ℝ) + 1))] else PowLogRep.smul t.2.2 (PowLogRep.shift (t.1 - 1) (gRep (w - t.1 + 1) t.2.1))
noncomputable def PowLogRep.conv (w : ℝ) (c : PowLogRep) : PowLogRep := c.flatMap (PowLogRep.basisConv w)
noncomputable def stateDensityRep : (n : ℕ) → (Fin (n + 1) → ℝ) → PowLogRep | 0, w => [(w 0 + 1, 0, 1)] | n + 1, w => PowLogRep.conv (w 0) (stateDensityRep n (Fin.tail w))
noncomputable def PowLogRep.coeffAt (c : PowLogRep) (μ : ℝ) (j : ℕ) : ℝ := ((c.filter fun t => t.1 = μ ∧ t.2.1 = j).map fun t => t.2.2).sum
theorem PowLogRep.coeffAt_cons (t) (c) (μ) (j) : coeffAt (t :: c) μ j = (if t.1 = μ ∧ t.2.1 = j then t.2.2 else 0) + coeffAt c μ j
noncomputable def monoWeights {d : ℕ} (h k : Fin d → ℕ) : Fin d → ℝ := fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1
noncomputable def kernelS (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ) (γ : Fin (n + 1) → ℕ) : ℝ := ∑ q ∈ Finset.Ico j (n + 1), PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) * fluctMoment β a p μ (q - j)
noncomputable def kernelFunctional … (f : CoeffFamily (n + 1)) : ℝ := (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ * kernelS n h k β a p μ j γ
theorem summable_kernel_term (n) (h k) (hk) (β a) (hβ : 0 < β) (p) {μ} (hμ : 0 < μ) (j) {f} (hf : AbsSummable f) : Summable fun γ => |f γ * kernelS n h k β a p μ j γ|
theorem familySpectralCoeff_population (n) (h k) (hk) (β) (hβ) {cη} (hη : AbsSummable cη) {μ} (hμ : 0 < μ) (j) : familySpectralCoeff n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη   -- unit 291
theorem Nat.choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k)   -- Mathlib
-- unit 303: popWeight h k β N x = (∏ i, x i ^ h i) * exp (-(β * N * ∏ i, x i ^ (2 * k i))); origPhaseIntegral_population_eq_weight : origPhaseIntegral n h k β N 1 (fun _ => 0) η = ∫ x in unitBox (n+1), η x * popWeight h k β N x
-- Mathlib: hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀) (hF_meas) (hF_int : Integrable (F x₀) μ) (hF'_meas) (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable) (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) : Integrable (F' x₀) μ ∧ HasDerivAt (fun n => ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
```

## The four files (complete)

### Grammar/EnergyDerivative.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationBounded

/-!
# The exact energy identity `𝒵_N[K∘π] = −(1/β) d/dN 𝒵_N[1]` (Programme Q, N2, unit 313)

For a continuous amplitude `η` on the unit box the population integral
`𝒵(N) = ∫ η u^h e^{-βN u^{2k}} du` is differentiable in `N > 0` with
```
𝒵'(N) = −β ∫ (u^{2k} η) u^h e^{-βN u^{2k}} du = −β 𝒵_K(N),
```
where `𝒵_K` inserts the energy `K∘π = u^{2k}` (`hasDerivAt_popIntegral`; differentiation under the
integral, dominated on the neighbourhood `|N − N₀| < N₀/2` by `β |η| u^h u^{2k}`, since the
exponential factor is at most one for `N > 0`). Hence `𝒵_K(N) = −(1/β) 𝒵'(N)`
(`energy_eq_neg_deriv`), the paper's `𝒵_n[K] = −𝒵_n'(n)` at `β = 1`. This is an identity of
integrals at every `N > 0`, obtained from the integrands; it is not, and must not be, used to
differentiate an asymptotic expansion. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Differentiation under the population integral**: `d/dN ∫ η u^h e^{-βN u^{2k}} =
−β ∫ (u^{2k} η) u^h e^{-βN u^{2k}}` at every `N₀ > 0`. -/
theorem hasDerivAt_popIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    HasDerivAt (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η)
      (-β * origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u))
      N₀ := by
  set c : (Fin (n + 1) → ℝ) → ℝ := fun x => ∏ i, x i ^ (2 * k i) with hc
  set a : (Fin (n + 1) → ℝ) → ℝ := fun x => η x * ∏ i, x i ^ h i with ha
  have hcc : Continuous c := continuous_prod_pow _
  have hac : Continuous a := hηc.mul (continuous_prod_pow _)
  set G : ℝ → (Fin (n + 1) → ℝ) → ℝ := fun N x => a x * Real.exp (-(β * N * c x)) with hG
  set G' : ℝ → (Fin (n + 1) → ℝ) → ℝ :=
    fun N x => a x * (Real.exp (-(β * N * c x)) * (-(β * c x))) with hG'
  have hGc : ∀ N, Continuous (G N) := fun N =>
    hac.mul (Real.continuous_exp.comp ((continuous_const.mul hcc).neg))
  have hG'c : ∀ N, Continuous (G' N) := fun N =>
    hac.mul ((Real.continuous_exp.comp ((continuous_const.mul hcc).neg)).mul
      (continuous_const.mul hcc).neg)
  -- the integrals in terms of `G`, `G'`
  have hZ : ∀ N, origPhaseIntegral n h k β N 1 (fun _ => 0) η =
      ∫ x in unitBox (n + 1), G N x := by
    intro N
    rw [origPhaseIntegral_population_eq_weight]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => ?_
    simp only [hG, ha, popWeight]
    ring
  have hZK : origPhaseIntegral n h k β N₀ 1 (fun _ => 0)
      (fun u => (∏ i, u i ^ (2 * k i)) * η u) = ∫ x in unitBox (n + 1), (-β)⁻¹ * G' N₀ x := by
    rw [origPhaseIntegral_population_eq_weight]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => ?_
    simp only [hG', ha, hc, popWeight]
    field_simp
  -- differentiation under the integral
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (unitBox (n + 1))) (F := G) (F' := G') (x₀ := N₀)
    (s := Metric.ball N₀ (N₀ / 2)) (bound := fun x => |a x| * (β * c x))
    (Metric.ball_mem_nhds _ (by positivity))
    (Eventually.of_forall fun N => (hGc N).aestronglyMeasurable)
    (integrableOn_unitBox_of_continuous _ (hGc N₀)) (hG'c N₀).aestronglyMeasurable ?_
    (integrableOn_unitBox_of_continuous _ (hac.abs.mul (continuous_const.mul hcc))) ?_
  · simp_rw [hZ]
    rw [hZK, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.2 hβ.ne'), one_mul]
    exact key.2
  · -- the dominating bound on the neighbourhood
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun x hx N hN => ?_
    have hc0 : 0 ≤ c x := Finset.prod_nonneg fun i _ => pow_nonneg (Set.mem_univ_pi.1 hx i).1.le _
    have hNpos : 0 < N := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hN
      linarith [hN.1]
    have hexp : Real.exp (-(β * N * c x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ β * N * c x := by positivity
      linarith
    simp only [hG', Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ β * c x)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_of_le_one_left (by positivity) hexp
  · -- pointwise differentiability in `N`
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun x _ N _ => ?_
    have hd := (((hasDerivAt_id N).const_mul (-(β * c x))).exp).const_mul (a x)
    refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [hG', id, mul_one]
      ring_nf
    · change a x * Real.exp (-(β * y * c x)) = a x * Real.exp (-(β * c x) * id y)
      congr 2
      simp only [id]
      ring

/-- The derivative of the population integral is `−β` times the energy insertion. -/
theorem deriv_popIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    deriv (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) N₀ =
      -β * origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u) :=
  (hasDerivAt_popIntegral n h k hβ η hηc hN₀).deriv

/-- **The exact energy identity** `𝒵_N[K∘π] = −(1/β) 𝒵_N'[1]` for `N > 0`. -/
theorem energy_eq_neg_deriv (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    origPhaseIntegral n h k β N₀ 1 (fun _ => 0) (fun u => (∏ i, u i ^ (2 * k i)) * η u) =
      -(1 / β) * deriv (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) N₀ := by
  rw [deriv_popIntegral n h k hβ η hηc hN₀]
  field_simp

end Grammar
```

### Grammar/MomentRecurrence.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationGammaMoment
import Grammar.MonomialPhaseTail

/-!
# The exponent recurrence of the zero-phase moments (Programme Q, N2, unit 314)

The zero-phase kernel moments `M(μ,i) = fluctMoment β 0 0 μ i = ∫₀^∞ t^{μ−1}(−log t)^i e^{−βt} dt`
satisfy, for `μ > 0`, `β > 0`, the integration-by-parts recurrence
```
M(μ+1, i) = (μ M(μ, i) − i M(μ, i−1)) / β                     (fluctMoment_succ_exponent)
```
(`u = t^μ(−log t)^i`, `v' = e^{−βt}`; the boundary terms vanish at `0⁺` because `μ > 0` and at `∞`
by exponential decay). For `i = 0` the second term is `0 · M(μ, 0)`. This is the analytic input to
the coefficient transport `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` (unit 315): inserting the
energy `u^{2k}` shifts the state-density exponents by one and the kernel moments by one in `μ`. The
recurrence is stated only for `μ > 0` (Astra #38 / review v38: no totalised-integral shortcuts).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Derivative of `t^μ (−log t)^i` for `t > 0`. -/
theorem hasDerivAt_powNegLog (μ : ℝ) (i : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ μ * (-Real.log t) ^ i)
      (μ * t ^ (μ - 1) * (-Real.log t) ^ i - (i : ℝ) * t ^ (μ - 1) * (-Real.log t) ^ (i - 1)) t :=
by
  have h1 : HasDerivAt (fun t : ℝ => t ^ μ) (μ * t ^ (μ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => (-Real.log t) ^ i)
      ((i : ℝ) * (-Real.log t) ^ (i - 1) * (-t⁻¹)) t :=
    ((Real.hasDerivAt_log ht.ne').neg).pow i
  refine (h1.mul h2).congr_deriv ?_
  rw [Real.rpow_sub_one ht.ne']
  field_simp
  ring

/-- `t^μ (−log t)^i e^{−βt} → 0` as `t → 0⁺` for `μ > 0`. -/
theorem tendsto_powNegLog_exp_nhdsGT_zero {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (β : ℝ) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t))) (𝓝[>] 0) (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(β * t))) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun t : ℝ => Real.exp (-(β * t))) (𝓝 0) (𝓝 (Real.exp (-(β * 0)))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i) (𝓝[>] 0) (𝓝 0) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp only [pow_zero, mul_one]
      have := (Real.continuousAt_rpow_const 0 μ (Or.inr hμ.le)).tendsto
      rw [Real.zero_rpow hμ.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have hpos : (0 : ℝ) < μ / i := by positivity
      have h := ((tendsto_log_mul_rpow_nhdsGT_zero hpos).neg).pow i
      rw [neg_zero, zero_pow hi.ne'] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
      rw [neg_mul_eq_neg_mul, mul_pow, ← Real.rpow_natCast (t ^ (μ / i)) i, ← Real.rpow_mul ht0.le,
        div_mul_cancel₀ _ hi', mul_comm]
  simpa using hmain.mul hexp

/-- `t^μ (−log t)^i e^{−βt} → 0` as `t → ∞` for `β > 0`. -/
theorem tendsto_powNegLog_exp_atTop (μ : ℝ) (i : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t))) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (μ + i) β hβ
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogle : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
    abs_of_pos (Real.exp_pos _), abs_pow, abs_neg, abs_of_nonneg hlog0, Real.rpow_add ht0,
    Real.rpow_natCast, show -β * t = -(β * t) by ring]
  gcongr

/-- **The exponent recurrence** `M(μ+1, i) = (μ M(μ,i) − i M(μ,i−1))/β` for `μ > 0`, `β > 0`. -/
theorem fluctMoment_succ_exponent {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    fluctMoment β 0 0 (μ + 1) i =
      (μ * fluctMoment β 0 0 μ i - (i : ℝ) * fluctMoment β 0 0 μ (i - 1)) / β := by
  set u : ℝ → ℝ := fun t => t ^ μ * (-Real.log t) ^ i with hu
  set u' : ℝ → ℝ := fun t => μ * t ^ (μ - 1) * (-Real.log t) ^ i -
    (i : ℝ) * t ^ (μ - 1) * (-Real.log t) ^ (i - 1) with hu'
  set v : ℝ → ℝ := fun t => -(Real.exp (-(β * t)) / β) with hv
  set v' : ℝ → ℝ := fun t => Real.exp (-(β * t)) with hv'
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t ht => hasDerivAt_powNegLog μ i ht
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(β * t)) (-β) t := by
      have h0 := (hasDerivAt_id t).const_mul (-β)
      refine (h0.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp only [id]
      ring
    have h2 := (h1.exp.div_const β).neg
    refine h2.congr_deriv ?_
    simp only [hv']
    field_simp
  have hA := integrableOn_fluct β 0 hβ 0 hμ i
  have hB := integrableOn_fluct β 0 hβ 0 hμ (i - 1)
  simp only [phaseKernel_zero_zero] at hA hB
  have hI1 : IntegrableOn (fun t => u t * v' t) (Ioi 0) := by
    have := integrableOn_fluct β 0 hβ 0 (ν := μ + 1) (by linarith) i
    simp only [phaseKernel_zero_zero] at this
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hu, hv', add_sub_cancel_right]
  have hI2 : IntegrableOn (fun t => u' t * v t) (Ioi 0) := by
    have h := ((hA.const_mul μ).sub (hB.const_mul (i : ℝ))).const_mul (-(1 / β))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hu', hv, Pi.sub_apply]
    field_simp
  have h0 : Tendsto (fun t => u t * v t) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_powNegLog_exp_nhdsGT_zero hμ i β).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hinf : Tendsto (fun t => u t * v t) atTop (𝓝 0) := by
    have := ((tendsto_powNegLog_exp_atTop μ i hβ).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd hI1 hI2 h0 hinf
  unfold fluctMoment
  simp only [phaseKernel_zero_zero]
  have hL : ∫ t in Ioi (0 : ℝ), t ^ (μ + 1 - 1) * (-Real.log t) ^ i * Real.exp (-(β * t)) =
      ∫ t in Ioi (0 : ℝ), u t * v' t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu, hv', add_sub_cancel_right]
  have hR : ∫ t in Ioi (0 : ℝ), u' t * v t = -(1 / β) *
      ((μ * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))) -
        (i : ℝ) * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ (i - 1) *
          Real.exp (-(β * t))) := by
    calc ∫ t in Ioi (0 : ℝ), u' t * v t = ∫ t in Ioi (0 : ℝ), -(1 / β) *
          (μ * (t ^ (μ - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))) -
            (i : ℝ) * (t ^ (μ - 1) * (-Real.log t) ^ (i - 1) * Real.exp (-(β * t)))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hu', hv]
          field_simp
      _ = _ := by
          rw [integral_const_mul, integral_sub (hA.const_mul μ) (hB.const_mul (i : ℝ)),
            integral_const_mul, integral_const_mul]
  rw [hL, hibp, hR]
  field_simp
  ring

end Grammar
```

### Grammar/PowLogShift.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensityLeadCoeff
import Grammar.SpectralCoefficients

/-!
# Shifting the state density by one exponent (Programme Q, N2, unit 315a)

Inserting the energy `u^{2k}` multiplies the state density of `u^{h+γ}` (with respect to
`K = u^{2k}`) by `t`: in the power–log representation every exponent moves up by one and the
coefficients are unchanged. Formally the convolution calculus commutes with the shift
(`PowLogRep.conv_shift`), so `stateDensityRep n (w + 1) = shift 1 (stateDensityRep n w)`
(`stateDensityRep_shift`), coefficient extraction transports (`PowLogRep.coeffAt_shift`), and the
monomial weights of `h + 2k` are those of `h` plus one (`monoWeights_add_two_k`). Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real

namespace Grammar

namespace PowLogRep

theorem shift_smul (a r : ℝ) (c : PowLogRep) : shift a (smul r c) = smul r (shift a c) := by
  unfold shift smul
  simp [List.map_map, Function.comp_def]

theorem shift_shift (a b : ℝ) (c : PowLogRep) : shift a (shift b c) = shift (b + a) c := by
  unfold shift
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext t
  simp only [Prod.mk.injEq, and_true]
  ring

theorem shift_cons (a : ℝ) (t : ℝ × ℕ × ℝ) (c : PowLogRep) :
    shift a (t :: c) = (t.1 + a, t.2.1, t.2.2) :: shift a c := rfl

theorem shift_flatMap (a : ℝ) (c : PowLogRep) (f : ℝ × ℕ × ℝ → PowLogRep) :
    shift a (c.flatMap f) = c.flatMap fun t => shift a (f t) := by
  unfold shift
  rw [List.map_flatMap]

/-- The basis convolution commutes with the unit shift. -/
theorem basisConv_shift (w : ℝ) (t : ℝ × ℕ × ℝ) :
    basisConv (w + 1) (t.1 + 1, t.2.1, t.2.2) = shift 1 (basisConv w t) := by
  unfold basisConv
  by_cases h : t.1 = w + 1
  · rw [if_pos (by simp [h]), if_pos h]
    rfl
  · rw [if_neg (by simpa using h), if_neg h, shift_smul, shift_shift]
    simp only
    congr 2
    · ring
    · congr 1
      ring

/-- The convolution commutes with the unit shift. -/
theorem conv_shift (w : ℝ) (c : PowLogRep) : conv (w + 1) (shift 1 c) = shift 1 (conv w c) := by
  unfold conv
  rw [shift_flatMap]
  conv_lhs => unfold shift
  rw [List.flatMap_map]
  congr 1
  funext t
  exact basisConv_shift w t

/-- Coefficient extraction transports along the unit shift. -/
theorem coeffAt_shift (c : PowLogRep) (μ : ℝ) (q : ℕ) :
    coeffAt (shift 1 c) (μ + 1) q = coeffAt c μ q := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    rw [shift_cons, coeffAt_cons, coeffAt_cons, ih]
    congr 1
    simp only [add_left_inj]

end PowLogRep

/-- **The state density of the shifted weights is the shifted state density.** -/
theorem stateDensityRep_shift : ∀ (n : ℕ) (w : Fin (n + 1) → ℝ),
    stateDensityRep n (fun i => w i + 1) = PowLogRep.shift 1 (stateDensityRep n w)
  | 0, w => rfl
  | n + 1, w => by
    rw [stateDensityRep_succ, stateDensityRep_succ]
    have htail : (Fin.tail fun i => w i + 1) = fun i => Fin.tail w i + 1 := rfl
    rw [htail, stateDensityRep_shift n (Fin.tail w)]
    exact PowLogRep.conv_shift (w 0) _

/-- The monomial weights of `h + 2k` are those of `h` plus one. -/
theorem monoWeights_add_two_k {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    monoWeights (fun i => h i + 2 * k i) k = fun i => monoWeights h k i + 1 := by
  funext i
  unfold monoWeights
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  field_simp
  push_cast
  ring

end Grammar
```

### Grammar/CoefficientTransport.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MomentRecurrence
import Grammar.PowLogShift
import Grammar.PopulationCoefficient

/-!
# Coefficient transport under the energy insertion (Programme Q, N2, unit 315)

Inserting the energy `K∘π = u^{2k}` into a population integral shifts the weight `h ↦ h + 2k`. At
the level of the Taylor-tree coefficient formula this shifts the state-density exponents by one
(`stateDensityRep_shift`, `coeffAt_shift`) and the kernel moments by one in the exponent
(`fluctMoment_succ_exponent`). The binomial identity `C(q,j)(q−j) = (j+1) C(q,j+1)` then gives, for
every `μ > 0` and every log degree `j`,
```
C_K(μ+1, j) = (μ C(μ, j) − (j+1) C(μ, j+1)) / β                 (population_coeff_add_two_k)
```
where `C` are the population coefficients of `(h, η)` and `C_K` those of `(h + 2k, η)` (both as
`familySpectralCoeff … 0 cη`, the canonical Taylor-tree coefficients at `b = 1`). This is Route B of
Astra #38: the transport is proved by coefficient algebra, never by differentiating a remainder.
At the first candidate `(λ, m−1)` it recovers `A_K = (λ/β) A` (unit 304) since `C(λ, m) = 0`, and at
`(λ, m−2)` it gives the log-correction coefficient `B_K = (λ B − (m−1) A)/β`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Kernel transport**: the zero-phase kernel of the shifted weight at `(μ+1, j)`. -/
theorem kernelS_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
    {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) :
    kernelS n (fun i => h i + 2 * k i) k β 0 0 (μ + 1) j γ =
      (μ * kernelS n h k β 0 0 μ j γ - ((j : ℝ) + 1) * kernelS n h k β 0 0 μ (j + 1) γ) / β := by
  have hw : monoWeights ((fun i => h i + 2 * k i) + γ) k =
      fun i => monoWeights (h + γ) k i + 1 := by
    have : ((fun i => h i + 2 * k i) + γ : Fin (n + 1) → ℕ) = fun i => (h + γ) i + 2 * k i := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [this, monoWeights_add_two_k (h + γ) k hk]
  unfold kernelS
  rw [hw, stateDensityRep_shift]
  simp only [PowLogRep.coeffAt_shift]
  set c : ℕ → ℝ := fun q => PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q
    with hc
  have hM : ∀ q ∈ Finset.Ico j (n + 1),
      c q * (q.choose j : ℝ) * fluctMoment β 0 0 (μ + 1) (q - j) =
        (μ * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β := by
    intro q _
    rw [fluctMoment_succ_exponent hβ hμ (q - j)]
    field_simp
  have hsecond : ∑ q ∈ Finset.Ico j (n + 1),
      ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1)) =
      ((j : ℝ) + 1) * ∑ q ∈ Finset.Ico (j + 1) (n + 1),
        c q * (q.choose (j + 1) : ℝ) * fluctMoment β 0 0 μ (q - (j + 1)) := by
    rcases le_or_gt j n with hjn | hjn
    · rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn)]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hcast : ((q - j : ℕ) : ℝ) * (q.choose j : ℝ) = ((j : ℝ) + 1) * (q.choose (j + 1) : ℝ) :=
by
        have h2 : ((q.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((q.choose j * (q - j) : ℕ) : ℝ) := by
          rw [Nat.choose_succ_right_eq]
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_succ] at h2
        linarith
      rw [Nat.sub_sub, show ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) *
          fluctMoment β 0 0 μ (q - (j + 1))) = (((q - j : ℕ) : ℝ) * (q.choose j : ℝ)) *
          (c q * fluctMoment β 0 0 μ (q - (j + 1))) by ring, hcast]
      ring
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
      simp
  calc ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β 0 0 (μ + 1) (q - j)
      = ∑ q ∈ Finset.Ico j (n + 1), (μ * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j)) -
          ((q - j : ℕ) : ℝ) * (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β :=
        Finset.sum_congr rfl hM
    _ = (μ * ∑ q ∈ Finset.Ico j (n + 1), c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j) -
          ∑ q ∈ Finset.Ico j (n + 1), ((q - j : ℕ) : ℝ) *
            (c q * (q.choose j : ℝ) * fluctMoment β 0 0 μ (q - j - 1))) / β := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hsecond]

/-- The zero-phase kernel vanishes above the top log degree. -/
theorem kernelS_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) {j : ℕ}
    (hj : n < j) (γ : Fin (n + 1) → ℕ) : kernelS n h k β a p μ j γ = 0 := by
  unfold kernelS
  rw [Finset.Ico_eq_empty_of_le (by omega)]
  rfl

/-- **Kernel-functional transport.** -/
theorem kernelFunctional_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    kernelFunctional n (fun i => h i + 2 * k i) k β 0 0 (μ + 1) j f =
      (μ * kernelFunctional n h k β 0 0 μ j f -
        ((j : ℝ) + 1) * kernelFunctional n h k β 0 0 μ (j + 1) f) / β := by
  unfold kernelFunctional
  simp only [kernelS_add_two_k n h k hk hβ hμ _ _]
  have h1 : Summable fun γ => f γ * kernelS n h k β 0 0 μ j γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β 0 hβ 0 hμ j hf
  have h2 : Summable fun γ => f γ * kernelS n h k β 0 0 μ (j + 1) γ := by
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β 0 hβ 0 hμ (j + 1) hf
  have hfun : (fun γ => f γ * ((μ * kernelS n h k β 0 0 μ j γ -
      ((j : ℝ) + 1) * kernelS n h k β 0 0 μ (j + 1) γ) / β)) =
      fun γ => (1 / β) * (μ * (f γ * kernelS n h k β 0 0 μ j γ) -
        ((j : ℝ) + 1) * (f γ * kernelS n h k β 0 0 μ (j + 1) γ)) := by
    funext γ
    field_simp
  rw [hfun, tsum_mul_left, Summable.tsum_sub (h1.mul_left μ) (h2.mul_left _), tsum_mul_left,
    tsum_mul_left]
  field_simp

/-- **Coefficient transport under the energy insertion**: for the population coefficients of an
admissible amplitude family, `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` (`μ > 0`). -/
theorem population_coeff_add_two_k (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n (fun i => h i + 2 * k i) k β 0 cη (μ + 1) j =
      (μ * familySpectralCoeff n h k β 0 cη μ j -
        ((j : ℝ) + 1) * familySpectralCoeff n h k β 0 cη μ (j + 1)) / β := by
  rw [familySpectralCoeff_population n _ k hk β hβ hη (by linarith) j,
    familySpectralCoeff_population n h k hk β hβ hη hμ j,
    familySpectralCoeff_population n h k hk β hβ hη hμ (j + 1)]
  exact kernelFunctional_add_two_k n h k hk hβ hμ j hη

/-- Population coefficients vanish above the top log degree. -/
theorem population_coeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) {j : ℕ}
    (hj : n < j) : familySpectralCoeff n h k β 0 cη μ j = 0 := by
  rw [familySpectralCoeff_population n h k hk β hβ hη hμ j]
  unfold kernelFunctional
  simp [kernelS_eq_zero_of_lt n h k β 0 0 μ hj]

end Grammar
```

## Questions
1. u313: is the differentiation under the integral sound (neighbourhood `|N − N₀| < N₀/2`, bound `|a| β c` with `a = η u^h`, `c = u^{2k}`, using `e^{-βNc} ≤ 1` for `N > 0`), and is the identity correctly normalised (`𝒵_K = −(1/β)𝒵'`; `β > 0` assumed)? Any issue with the totalised `deriv` in `energy_eq_neg_deriv` (it is justified by the `HasDerivAt`)?
2. u314: is `fluctMoment_succ_exponent` correct with its hypotheses `μ > 0`, `β > 0`, including `i = 0` (natural `i − 1 = 0`, coefficient `(0:ℝ)`); are the boundary limits and integrability arguments right (`u v → 0` at `0⁺` via `log t · t^{μ/i} → 0`, at `∞` via `t^{μ+i} e^{−βt}`)?
3. u315a: is `basisConv_shift`/`conv_shift` a correct proof that the convolution calculus commutes with the unit shift (the `else` branch: `shift (t.1+1−1) (smul … (gRep (w+1−(t.1+1)+1) …)) = smul … (shift (t.1−1+1) (gRep (w−t.1+1) …))`), and is `stateDensityRep_shift` the actual `coeffAt`-level transport you required (with `coeffAt_shift`)?
4. u315: is `kernelS_add_two_k` correct — in particular the handling of the `q = j` term (factor `(q−j) = 0`), the binomial step `C(q,j)(q−j) = (j+1)C(q,j+1)` via `Nat.choose_succ_right_eq`, the `j > n` case (both sums empty), and the passage `kernelS → kernelFunctional` (tsum linearity with `summable_kernel_term`) → `familySpectralCoeff` (via unit 291)? Is the theorem's generality (every real `μ > 0`, every `j`) honest?
5. **Gate decision** for unit 316 (two-term quotient). Plan: (a) generalise `population_remainder_tendsto` to division by `N^{-λ}(log N)^j` for any `j` (same proof; `(log N)^j ≥ 1` for `N ≥ e`); (b) with `C(λ,q) = 0` for `q > m−1`, `P(x) = A x^{m−1} + B x^{m−2} + lower`, get `Z/(N^{-λ}(log N)^{m−2}) − A log N → B` for `m ≥ 2` (`B := C(λ, m−2)`), and for the shifted weight `Z_K/(N^{-(λ+1)}(log N)^{m−2}) − A_K log N → B_K` with `A_K = λA/β`, `B_K = (λB − (m−1)A)/β` from u315 + `C(λ,m) = 0`; (c) algebra: `N log N (Z_K/Z − λ/(βN)) = [A(B_K+ε_K) − A_K(B+ε)] / (A (A + (B+ε)/log N)) → (A B_K − A_K B)/A² = −(m−1)/β` for `A ≠ 0`; (d) `m = 1` separately: `Z = N^{-λ}(A + ε)`, `Z_K = N^{-λ-1}(A_K + ε_K)` with `ε log N → 0`, `ε_K log N → 0`, giving the same limit `0 = −(m−1)/β`. Final statement `Tendsto (fun N => N * log N * (Z_K N / Z N − λ/(β N))) atTop (𝓝 (−(m−1)/β))` for all `m ≥ 1` (proved by the two branches). Is this the right formulation and is anything missing (e.g. eventual nonvanishing of `Z` from `A ≠ 0`, which follows from `Z ~ A N^{-λ} log^{m−1}`)? Should the assembled version be attempted within the remaining N2 budget (needs residuals `o(N^{-λ} log^{m−2})` and `o(N^{-λ-1} log^{m−2})`) or left out?

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
