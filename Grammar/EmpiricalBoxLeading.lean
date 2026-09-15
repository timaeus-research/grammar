/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BoxDilation
import Grammar.SpatialPhaseLeading
import Grammar.SmoothResolvedLeadingOne

/-!
# The empirical box integral on a positive box: leading term, domination, lower pairs

Headline XIX (`spatialPhase_tendsto`) gives the leading term of the standard integral with a
continuous spatially varying phase on the unit box. This module transports it to a box
`(0,b]^{n+1}` (`spatialPhase_box_tendsto`, via the exact dilation
`origPhaseIntegral_dilation_phase`), bounds the empirical box integral by the zero-phase integral
at half temperature (`abs_origPhaseIntegral_le_zero_phase`, from `√N u^k ξ ≤ N u^{2k}/2 + M²/2`),
and shows that a box whose own leading pair is preceded by `(λ, m−1)` contributes nothing at that
scale (`tendsto_origPhaseIntegral_div_zero_of_precedes`). These are the fibrewise inputs of the
empirical piece theorem. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Exact dilation with a phase**: for `N ≥ 0`,
`𝒵_b(N; ξ, η) = b^{|h|+n+1} 𝒵_1(N b^{2|k|}; ξ(b·), η(b·))`. -/
theorem origPhaseIntegral_dilation_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N b : ℝ}
    (hN : 0 ≤ N) (hb : 0 < b) (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N b ξ η =
      b ^ (∑ i, h i + (n + 1)) * origPhaseIntegral n h k β (N * b ^ (2 * ∑ i, k i)) 1
        (fun v => ξ (b • v)) (fun v => η (b • v)) := by
  set F : (Fin (n + 1) → ℝ) → ℝ := fun u => η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u) with hF
  set G : (Fin (n + 1) → ℝ) → ℝ := fun v => η (b • v) * (∏ i, v i ^ h i) *
    Real.exp (-(β * (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ (2 * k i)) +
      β * (Real.sqrt (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ k i) * ξ (b • v)) with hG
  have hsqrt : Real.sqrt (N * b ^ (2 * ∑ i, k i)) = Real.sqrt N * b ^ (∑ i, k i) := by
    rw [Real.sqrt_mul hN, show b ^ (2 * ∑ i, k i) = (b ^ (∑ i, k i)) ^ 2 by
      rw [← pow_mul, mul_comm], Real.sqrt_sq (pow_nonneg hb.le _)]
  have hFG : ∀ v, F (b • v) = b ^ (∑ i, h i) * G v := by
    intro v
    simp only [hF, hG, Pi.smul_apply, smul_eq_mul]
    have h1 : ∏ i, (b * v i) ^ h i = b ^ (∑ i, h i) * ∏ i, v i ^ h i := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    have h2 : ∏ i, (b * v i) ^ (2 * k i) = b ^ (2 * ∑ i, k i) * ∏ i, v i ^ (2 * k i) := by
      rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    have h3 : ∏ i, (b * v i) ^ k i = b ^ (∑ i, k i) * ∏ i, v i ^ k i := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    rw [h1, h2, h3, hsqrt]
    ring_nf
  have hind : ∀ v, (piBox (n + 1) (Ioc 0 b)).indicator F (b • v) =
      (unitBox (n + 1)).indicator (fun v => b ^ (∑ i, h i) * G v) v := by
    intro v
    by_cases hv : v ∈ unitBox (n + 1)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((smul_mem_piBox_Ioc_iff hb v).2 hv), hFG]
    · rw [Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (fun h' => hv ((smul_mem_piBox_Ioc_iff hb v).1 h'))]
  have hscale := Measure.integral_comp_smul (volume : Measure (Fin (n + 1) → ℝ))
    ((piBox (n + 1) (Ioc 0 b)).indicator F) b
  rw [Module.finrank_fin_fun, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hb.le _)),
    integral_indicator (measurableSet_piBox _ _ measurableSet_Ioc)] at hscale
  simp_rw [hind] at hscale
  rw [integral_indicator (measurableSet_unitBox _), integral_const_mul] at hscale
  have hpos : (0 : ℝ) < b ^ (n + 1) := pow_pos hb _
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  unfold origPhaseIntegral
  rw [hset]
  have hZ : ∫ u in piBox (n + 1) (Ioc 0 b), F u =
      b ^ (n + 1) * (b ^ (∑ i, h i) * ∫ v in unitBox (n + 1), G v) := by
    rw [hscale]
    field_simp
  simp only [hF, hG] at hZ
  rw [hZ, pow_add]
  ring

/-- **The empirical leading term on a positive box** `(0,b]^{n+1}` with a continuous phase. -/
theorem spatialPhase_box_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ)
    (hηc : Continuous η) :
    Tendsto (fun N => origPhaseIntegral n h k β N b ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        spatialFace h k l β (fun v => ξ (b • v)) (fun v => η (b • v)))) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hT := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt (fun v => ξ (b • v))
    (fun v => η (b • v)) (continuous_rescale b hξc) (continuous_rescale b hηc)
  have hM : Tendsto (fun N : ℝ => N * c) atTop atTop := tendsto_id.atTop_mul_const hc0
  have hTc := hT.comp hM
  have hlog : Tendsto (fun N : ℝ => (1 + Real.log c * (Real.log N)⁻¹) ^ (m - 1)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_log).const_add (1 : ℝ)).pow
      (m - 1)
    simpa using this
  have hmain := (hTc.mul hlog).const_mul (b ^ (∑ i, h i + (n + 1)) * c ^ (-l))
  rw [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (1 / c)] with N hN hNc
  have hN0 : 0 < N := by linarith
  have hNc1 : 1 < N * c := by rwa [div_lt_iff₀ hc0] at hNc
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  simp only [Function.comp]
  rw [origPhaseIntegral_dilation_phase n h k β hN0.le hb ξ η, ← hc,
    Real.mul_rpow hN0.le hc0.le, Real.log_mul hN0.ne' hc0.ne']
  simp only [← hm]
  have hone : 1 + Real.log c * (Real.log N)⁻¹ = (Real.log N + Real.log c) / Real.log N := by
    field_simp
  rw [hone, div_pow]
  have hpowN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpowc : c ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hlogM : Real.log N + Real.log c ≠ 0 := by
    have := Real.log_pos hNc1
    rw [Real.log_mul hN0.ne' hc0.ne'] at this
    exact this.ne'
  have hlogMpow : (Real.log N + Real.log c) ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogM
  have hlogNpow : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogN
  field_simp

/-- **Domination by the zero-phase integral at half temperature**: if `|ξ| ≤ M` on the box,
`|𝒵_b(N; ξ, η)| ≤ e^{βM²/2} 𝒵_b^{β/2}(N; 0, |η|)`. -/
theorem abs_origPhaseIntegral_le_zero_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {N b : ℝ} (hN : 0 ≤ N) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) {M : ℝ}
    (hM : ∀ u ∈ piBox (n + 1) (Ioc 0 b), |ξ u| ≤ M) :
    |origPhaseIntegral n h k β N b ξ η| ≤
      Real.exp (β * M ^ 2 / 2) *
        origPhaseIntegral n h k (β / 2) N b (fun _ => 0) fun u => |η u| := by
  unfold origPhaseIntegral
  have hbox : IsCompact (piBox (n + 1) (Icc 0 b)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : piBox (n + 1) (Ioc 0 b) ⊆ piBox (n + 1) (Icc 0 b) :=
    Set.pi_mono fun _ _ => Ioc_subset_Icc_self
  have hint : IntegrableOn (fun u : Fin (n + 1) → ℝ => |η u| * (∏ i, u i ^ h i) *
      Real.exp (-(β / 2 * N * ∏ i, u i ^ (2 * k i)) +
        β / 2 * (Real.sqrt N * ∏ i, u i ^ k i) * 0)) (piBox (n + 1) (Ioc 0 b)) :=
    ((hηc.abs.mul (by fun_prop)).mul (Real.continuous_exp.comp (by fun_prop))).continuousOn
      |>.integrableOn_compact hbox |>.mono_set hsub
  rw [← integral_const_mul]
  have hle := norm_integral_le_of_norm_le (μ := volume.restrict (piBox (n + 1) (Ioc 0 b)))
    (f := fun u : Fin (n + 1) → ℝ => η u * (∏ i, u i ^ h i) *
      Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u))
    (hint.const_mul (Real.exp (β * M ^ 2 / 2))) ?_
  · rwa [Real.norm_eq_abs] at hle
  · rw [ae_restrict_iff' (measurableSet_piBox _ _ measurableSet_Ioc)]
    refine Eventually.of_forall fun u hu => ?_
    have hupos : ∀ i, 0 < u i := fun i => (hu i (mem_univ i)).1
    set P1 : ℝ := ∏ i, u i ^ k i with hP1
    set P2 : ℝ := ∏ i, u i ^ (2 * k i) with hP2
    set Ph : ℝ := ∏ i, u i ^ h i with hPh
    have hP1pos : 0 < P1 := Finset.prod_pos fun i _ => pow_pos (hupos i) _
    have hPh0 : 0 ≤ Ph := (Finset.prod_pos fun i _ => pow_pos (hupos i) _).le
    have hsq : P2 = P1 ^ 2 := by
      rw [hP1, hP2, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
    have hξu : ξ u ≤ M := (le_abs_self (ξ u)).trans (hM u hu)
    have hs : 0 ≤ Real.sqrt N * P1 := mul_nonneg (Real.sqrt_nonneg _) hP1pos.le
    have hamgm : Real.sqrt N * P1 * M ≤ (Real.sqrt N * P1) ^ 2 / 2 + M ^ 2 / 2 := by
      nlinarith [sq_nonneg (Real.sqrt N * P1 - M)]
    have hsqN : (Real.sqrt N * P1) ^ 2 = N * P2 := by rw [mul_pow, Real.sq_sqrt hN, hsq]
    rw [hsqN] at hamgm
    have h1 : Real.sqrt N * P1 * ξ u ≤ Real.sqrt N * P1 * M := mul_le_mul_of_nonneg_left hξu hs
    have hexp : Real.exp (-(β * N * P2) + β * (Real.sqrt N * P1) * ξ u) ≤
        Real.exp (β * M ^ 2 / 2) *
          Real.exp (-(β / 2 * N * P2) + β / 2 * (Real.sqrt N * P1) * 0) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans hamgm) hβ.le]
    calc ‖η u * Ph * Real.exp (-(β * N * P2) + β * (Real.sqrt N * P1) * ξ u)‖
        = |η u| * Ph * Real.exp (-(β * N * P2) + β * (Real.sqrt N * P1) * ξ u) := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), abs_of_nonneg hPh0]
      _ ≤ |η u| * Ph * (Real.exp (β * M ^ 2 / 2) *
            Real.exp (-(β / 2 * N * P2) + β / 2 * (Real.sqrt N * P1) * 0)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) hPh0)
      _ = Real.exp (β * M ^ 2 / 2) *
            (|η u| * Ph * Real.exp (-(β / 2 * N * P2) + β / 2 * (Real.sqrt N * P1) * 0)) := by
          ring

/-- **Lower pairs contribute nothing**: if the box's own leading pair `(l, m−1)` is preceded by
`(λ, q)`, the empirical box integral normalised at `(λ, q)` tends to `0`. -/
theorem tendsto_origPhaseIntegral_div_zero_of_precedes (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) {lam : ℝ} {q : ℕ}
    (hpre : SmoothEngine.Precedes lam q l (multCount (ratioExp h k) l - 1)) :
    Tendsto (fun N => origPhaseIntegral n h k β N b ξ η / (N ^ (-lam) * Real.log N ^ q)) atTop
      (𝓝 0) := by
  have hT := spatialPhase_box_tendsto n h k hk β hβ hb hmin hatt ξ η hξc hηc
  have hS := SmoothEngine.tendsto_normalised_scale_of_precedes hpre
  have hprod := hT.mul hS
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have h1 : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have h2 : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ hlog
  have h3 : N ^ (-lam) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have h4 : Real.log N ^ q ≠ 0 := pow_ne_zero _ hlog
  have h5 : N ^ lam = (N ^ (-lam))⁻¹ := by rw [Real.rpow_neg hN0.le, inv_inv]
  rw [h5]
  field_simp

end Grammar
