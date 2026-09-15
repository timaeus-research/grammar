/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalBranchTuples
import Grammar.UniformCompactTransfer

/-!
# The empirical partition function with a random root field: convergence in distribution

Rank 4 of the empirical programme. The space of continuous branch tuples `E = BranchTuple` carries
its Borel σ-algebra. The normalised core sum `f ↦ T_N(f)/s_N` and the face limit `f ↦ T(f)` are
continuous on `E` (Lipschitz on every ball: `continuous_tupleZ`, `continuous_tupleLimit`), and the
uniform convergence on compact sets of CDLXXIV transfers convergence in distribution:

★★★ `tendstoInDistribution_empZ_div`: if the branch tuples `ξ̂_n` of random root fields `ξ_n`
converge in distribution to `G` in `E` with tight laws, and the global field bounds `M_n` are
`O_p(1)`, then at a chart-leading pair `(λ, m)`
`Z^{emp}_n[F; ξ_n] / (n^{−λ}(log n)^{m−1}) ⇒ T(G) = Σ_p ∫ boxFaceLimit_p(G_p) dν_p`
in distribution. The proof is `tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts` for
the core sum and Slutsky (`TendstoInDistribution.add_of_tendstoInMeasure_const`) for the
exponentially small random tail. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The Borel structure on branch tuples -/

instance : MeasurableSpace (Ξ.BranchTuple Y) := borel _

instance : BorelSpace (Ξ.BranchTuple Y) := ⟨rfl⟩

/-! ### Continuity of the core sum and of the face limit -/

/-- A map that is Lipschitz on every ball is continuous. -/
theorem continuous_of_lipschitz_on_balls {E : Type*} [NormedAddCommGroup E] {T : E → ℝ}
    (h : ∀ R : ℝ, ∃ L : ℝ, ∀ f g : E, ‖f‖ ≤ R → ‖g‖ ≤ R → |T f - T g| ≤ L * ‖f - g‖) :
    Continuous T := by
  rw [continuous_iff_continuousAt]
  intro f₀
  obtain ⟨L, hL⟩ := h (‖f₀‖ + 1)
  have hlip : LipschitzOnWith (Real.toNNReal L) T (Metric.closedBall 0 (‖f₀‖ + 1)) := by
    refine LipschitzOnWith.of_dist_le_mul fun f hf g hg => ?_
    rw [Real.dist_eq, dist_eq_norm]
    rw [mem_closedBall_zero_iff] at hf hg
    exact (hL f g hf hg).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  refine (hlip.continuousOn.mono Metric.ball_subset_closedBall).continuousAt ?_
  exact Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith))

/-- The core sum at fixed `N ≥ 0` is Lipschitz on every ball. -/
theorem exists_lipschitz_tupleZ {N : ℝ} (hN : 0 ≤ N) (R : ℝ) :
    ∃ L : ℝ, ∀ f g : Ξ.BranchTuple Y, ‖f‖ ≤ R → ‖g‖ ≤ R →
      |Ξ.tupleZ Y f N - Ξ.tupleZ Y g N| ≤ L * ‖f - g‖ := by
  choose A hA using fun p => Ξ.exists_amp_bound Y p
  exact ⟨Ξ.tupleLipConst Y A R N, fun f g hf hg => Ξ.abs_tupleZ_sub_le Y f g hN hf hg hA⟩

/-- The core sum at fixed `N ≥ 0` is continuous on branch tuples. -/
theorem continuous_tupleZ {N : ℝ} (hN : 0 ≤ N) : Continuous fun f => Ξ.tupleZ Y f N :=
  continuous_of_lipschitz_on_balls (Ξ.exists_lipschitz_tupleZ Y hN)

/-- The face limit `T` is Lipschitz on every ball (inherited from the normalised core sums). -/
theorem exists_lipschitz_tupleLimit {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) (R : ℝ) :
    ∃ L : ℝ, ∀ f g : Ξ.BranchTuple Y, ‖f‖ ≤ R → ‖g‖ ≤ R →
      |Ξ.tupleLimit Y f lam m - Ξ.tupleLimit Y g lam m| ≤ L * ‖f - g‖ := by
  obtain ⟨L, hL⟩ := Ξ.exists_eventually_lipschitz_tupleZ_div Y hm hlead R
  refine ⟨L, fun f g hf hg => ?_⟩
  have h := abs_limit_sub_le_of_eventually_lipschitz
    (T := fun N f => Ξ.tupleZ Y f N / powLogScale lam (m - 1) N)
    (Tlim := fun f => Ξ.tupleLimit Y f lam m) (C := Metric.closedBall 0 R) (L := L)
    (fun f _ => Ξ.hasLeadingTerm_tupleZ Y f hm hlead)
    (hL.mono fun N hN f hf g hg => by
      rw [mem_closedBall_zero_iff] at hf hg
      rw [dist_eq_norm]
      exact hN f g hf hg)
    (mem_closedBall_zero_iff.2 hf) (mem_closedBall_zero_iff.2 hg)
  rwa [dist_eq_norm] at h

/-- The face limit `T` is continuous on branch tuples. -/
theorem continuous_tupleLimit {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) :
    Continuous fun f => Ξ.tupleLimit Y f lam m :=
  continuous_of_lipschitz_on_balls (Ξ.exists_lipschitz_tupleLimit Y hm hlead)

/-- Uniform convergence on compacts along the integer sample sizes. -/
theorem tendstoUniformlyOn_tupleZ_nat {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {C : Set (Ξ.BranchTuple Y)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (n : ℕ) f => Ξ.tupleZ Y f n / powLogScale lam (m - 1) n)
      (fun f => Ξ.tupleLimit Y f lam m) atTop C := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := Metric.tendstoUniformlyOn_iff.1 (Ξ.tendstoUniformlyOn_tupleZ Y hm hlead hC) ε hε
  exact tendsto_natCast_atTop_atTop.eventually h

/-! ### The random-field limit theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★★ **Convergence in distribution of the normalised core sums** at the random branch tuples:
if `L n ⇒ G` in `E` with tight laws, then `T_n(L n)/s_n ⇒ T(G)`. -/
theorem tendstoInDistribution_tupleZ_div {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {L : ℕ → Ω → Ξ.BranchTuple Y} (hLm : ∀ n, Measurable (L n))
    {G : Ω' → Ξ.BranchTuple Y} (hLG : TendstoInDistribution L atTop G (fun _ => P) P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (L n))) :
    TendstoInDistribution (fun (n : ℕ) w => Ξ.tupleZ Y (L n w) n / powLogScale lam (m - 1) n)
      atTop (fun w' => Ξ.tupleLimit Y (G w') lam m) (fun _ => P) P' :=
  tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts hLm hLG htight
    (T := fun (n : ℕ) f => Ξ.tupleZ Y f n / powLogScale lam (m - 1) n)
    (fun n => (Ξ.continuous_tupleZ Y (Nat.cast_nonneg n)).div_const _)
    (Ξ.continuous_tupleLimit Y hm hlead)
    (fun _ hC => Ξ.tendstoUniformlyOn_tupleZ_nat Y hm hlead hC)

/-- `powLogScale` is nonnegative at every natural sample size. -/
theorem powLogScale_nonneg_nat (lam : ℝ) (q n : ℕ) : 0 ≤ powLogScale lam q n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg (Real.log_natCast_nonneg n) _)

/-- The exponential tail rate beats every power–log scale. -/
theorem tendsto_exp_div_powLogScale {δ : ℝ} (hδ : 0 < δ) (lam : ℝ) (q : ℕ) :
    Tendsto (fun N : ℝ => Real.exp (-(δ / 2) * N) / powLogScale lam q N) atTop (𝓝 0) := by
  have hexp : Tendsto (fun N : ℝ => N ^ lam * Real.exp (-(δ / 2) * N)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (δ / 2) (by linarith)
  have h0 := hexp.zero_mul_isBoundedUnder_le (SmoothEngine.isBoundedUnder_inv_log_pow q)
  refine h0.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  unfold powLogScale
  rw [Real.rpow_neg hN0.le]
  field_simp

omit [IsProbabilityMeasure P] in
/-- The normalised tail of a random root field is `o_p(1)` when the global field bounds are
`O_p(1)`. -/
theorem tendstoInMeasure_tail_div (ξ : ℕ → Ω → Ξ.RootField Y) {M : ℕ → Ω → ℝ}
    (hM : ∀ n w Q, |(ξ n w).ψ Q| ≤ M n w) (hM0 : ∀ n w, 0 ≤ M n w)
    (hMt : ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < M n w} ≤ η) (lam : ℝ) (q : ℕ) :
    TendstoInMeasure P (fun (n : ℕ) w =>
      (∫ Q, Ξ.empIntegrand Y (ξ n w) n Q ∂Y.tailU) / powLogScale lam q n) atTop 0 := by
  set C0 : ℝ := ∫ Q, |Ξ.F Q| ∂Y.tailU with hC0
  have hC00 : 0 ≤ C0 := integral_nonneg fun Q => abs_nonneg _
  refine tendstoInMeasure_zero_of_tight_bound (M := M) (c := fun x => Real.exp (x ^ 2 / 2) * C0)
    (r := fun n : ℕ => Real.exp (-(Y.T.δ / 2) * n) / powLogScale lam q n) ?_ hM0 ?_ ?_ ?_ hMt
  · intro x hx y _ hxy
    simp only
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hC00
    have hx0 : 0 ≤ x := hx
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    linarith
  · intro n w
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs := powLogScale_nonneg_nat lam q n
    rw [abs_div, abs_of_nonneg hs]
    calc |∫ Q, Ξ.empIntegrand Y (ξ n w) n Q ∂Y.tailU| / powLogScale lam q n
        ≤ (Real.exp (M n w ^ 2 / 2) * C0) * Real.exp (-(Y.T.δ / 2) * n) / powLogScale lam q n :=
          div_le_div_of_nonneg_right (Ξ.abs_integral_tail_le Y (ξ n w) hn0 (hM n w)) hs
      _ = Real.exp (M n w ^ 2 / 2) * C0 * (Real.exp (-(Y.T.δ / 2) * n) / powLogScale lam q n) := by
          ring
  · exact (tendsto_exp_div_powLogScale Y.T.δ_pos lam q).comp tendsto_natCast_atTop_atTop
  · intro n
    exact div_nonneg (Real.exp_pos _).le (powLogScale_nonneg_nat lam q n)

/-- ★★★ **The empirical partition function with a random root field converges in distribution**:
at a chart-leading pair `(λ, m)`, if the branch tuples `ξ̂_n` of the random root fields converge
in distribution to `G` in the space of continuous branch tuples with tight laws, and the global
field bounds are `O_p(1)`, then
`Z^{emp}_n[F; ξ_n] / (n^{−λ}(log n)^{m−1}) ⇒ T(G) = Σ_p ∫ boxFaceLimit_p(G_p) dν_p`. -/
theorem tendstoInDistribution_empZ_div {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) (ξ : ℕ → Ω → Ξ.RootField Y)
    (hLm : ∀ n, Measurable fun w => (ξ n w).tuple)
    (hZm : ∀ n, AEMeasurable (fun w => Ξ.empZ Y (ξ n w) n) P)
    {G : Ω' → Ξ.BranchTuple Y}
    (hLG : TendstoInDistribution (fun n w => (ξ n w).tuple) atTop G (fun _ => P) P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map fun w => (ξ n w).tuple))
    {M : ℕ → Ω → ℝ} (hM : ∀ n w Q, |(ξ n w).ψ Q| ≤ M n w) (hM0 : ∀ n w, 0 ≤ M n w)
    (hMt : ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < M n w} ≤ η) :
    TendstoInDistribution (fun (n : ℕ) w => Ξ.empZ Y (ξ n w) n / powLogScale lam (m - 1) n)
      atTop (fun w' => Ξ.tupleLimit Y (G w') lam m) (fun _ => P) P' := by
  have hcore := Ξ.tendstoInDistribution_tupleZ_div Y hm hlead hLm hLG htight
  have htail := Ξ.tendstoInMeasure_tail_div Y ξ hM hM0 hMt lam (m - 1)
  have hXm : ∀ n, AEMeasurable (fun w => Ξ.tupleZ Y (ξ n w).tuple n / powLogScale lam (m - 1) n)
      P := fun n => (((Ξ.continuous_tupleZ Y (Nat.cast_nonneg n)).div_const _).measurable.comp
        (hLm n)).aemeasurable
  have hYm : ∀ n, AEMeasurable (fun w =>
      (∫ Q, Ξ.empIntegrand Y (ξ n w) n Q ∂Y.tailU) / powLogScale lam (m - 1) n) P := by
    intro n
    have heq : (fun w => (∫ Q, Ξ.empIntegrand Y (ξ n w) n Q ∂Y.tailU) / powLogScale lam (m - 1) n)
        = fun w => Ξ.empZ Y (ξ n w) n / powLogScale lam (m - 1) n -
          Ξ.tupleZ Y (ξ n w).tuple n / powLogScale lam (m - 1) n := by
      funext w
      rw [← sub_div, Ξ.empZ_eq_tupleZ_add_tail Y (ξ n w) (Nat.cast_nonneg n) (hM n w),
        add_sub_cancel_left]
    rw [heq]
    exact (hZm n).div_const _ |>.sub (hXm n)
  have htail' : TendstoInMeasure P (fun (n : ℕ) w =>
      (∫ Q, Ξ.empIntegrand Y (ξ n w) n Q ∂Y.tailU) / powLogScale lam (m - 1) n) atTop
      (fun _ => (0 : ℝ)) := htail
  have h := hcore.add_of_tendstoInMeasure_const htail' hYm
  convert h using 1
  · funext n w
    rw [Pi.add_apply, ← add_div, ← Ξ.empZ_eq_tupleZ_add_tail Y (ξ n w) (Nat.cast_nonneg n) (hM n w)]
  · funext w'
    simp

end ResolvedData

end SmoothEngine

end Grammar
