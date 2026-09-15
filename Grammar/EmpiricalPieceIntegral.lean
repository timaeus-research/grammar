/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalPieceLeading
import Grammar.EmpiricalStratumMeasure
import Grammar.IntegratedLeadingTerm

/-!
# The empirical piece integral: transport, domination and leading term

For a piece `p` of the resolved chart transport and a root field `ξ`, the empirical core integral
`∫ F e^{−N K∘π + √N √(K∘π) ψ} dcoreMeasure_p` is transported to the box:
`∫_{Base} empBoxIntegral h k N b (loc_p(s,·)) (amp s) dν(s)` (`integral_coreMeasure_empIntegrand`).
The fibrewise integrals are dominated by `e^{M²/2} A · empBoxIntegral h k (N/2) b 0 1`
(`abs_empBoxIntegral_le`), whose normalisation is eventually bounded, so by dominated convergence
the empirical piece integral has the leading term `∫_{Base} boxFaceLimit(s) dν(s)` at a
chart-leading pair (`hasLeadingTerm_empPieceInt`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

/-! ### Domination of the empirical box integral -/

theorem SmoothEngine.mono_two_mul_eq_sq {ι : Type*} [Fintype ι] (k : ι → ℕ) (u : ι → ℝ) :
    SmoothEngine.mono (fun i => 2 * k i) u = SmoothEngine.mono k u ^ 2 := by
  unfold SmoothEngine.mono
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

variable {d : ℕ}

/-- **Domination**: for `|ξ| ≤ M` and `|η| ≤ A` on the box and `N ≥ 0`,
`|empBoxIntegral h k N b ξ η| ≤ e^{M²/2} A · empBoxIntegral h k (N/2) b 0 1`. -/
theorem abs_empBoxIntegral_le (h k : Fin d → ℕ) {N b : ℝ} (hN : 0 ≤ N)
    {ξ η : (Fin d → ℝ) → ℝ} {M A : ℝ} (hM : ∀ u ∈ SmoothEngine.box (Fin d) b, |ξ u| ≤ M)
    (hA : ∀ u ∈ SmoothEngine.box (Fin d) b, |η u| ≤ A) :
    |empBoxIntegral h k N b ξ η| ≤
      Real.exp (M ^ 2 / 2) * A * empBoxIntegral h k (N / 2) b (fun _ => 0) fun _ => 1 := by
  unfold empBoxIntegral
  beta_reduce
  have hcont : Continuous fun u : Fin d → ℝ => Real.exp (M ^ 2 / 2) * A *
      (1 * SmoothEngine.mono h u * Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt (N / 2) * SmoothEngine.mono k u * 0)) := by
    have := SmoothEngine.continuous_mono (ι := Fin d) h
    have := SmoothEngine.continuous_mono (ι := Fin d) (fun i => 2 * k i)
    have := SmoothEngine.continuous_mono (ι := Fin d) k
    fun_prop
  have hint : IntegrableOn (fun u : Fin d → ℝ => Real.exp (M ^ 2 / 2) * A *
      (1 * SmoothEngine.mono h u * Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt (N / 2) * SmoothEngine.mono k u * 0))) (SmoothEngine.box (Fin d) b) :=
    (hcont.continuousOn.integrableOn_compact (SmoothEngine.isCompact_closedBox b)).mono_set
      (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)
  rw [← integral_const_mul]
  have hle := norm_integral_le_of_norm_le (μ := volume.restrict (SmoothEngine.box (Fin d) b))
    (f := fun u : Fin d → ℝ => η u * SmoothEngine.mono h u *
      Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt N * SmoothEngine.mono k u * ξ u)) hint ?_
  · rwa [Real.norm_eq_abs] at hle
  rw [ae_restrict_iff' (SmoothEngine.measurableSet_box b)]
  refine Eventually.of_forall fun u hu => ?_
  have hm1 : 0 ≤ SmoothEngine.mono k u :=
    Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hu i).le _
  have hmh : 0 ≤ SmoothEngine.mono h u :=
    Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hu i).le _
  have hsq := SmoothEngine.mono_two_mul_eq_sq k u
  have hξu : ξ u ≤ M := (le_abs_self (ξ u)).trans (hM u hu)
  have hs : 0 ≤ Real.sqrt N * SmoothEngine.mono k u := mul_nonneg (Real.sqrt_nonneg _) hm1
  have hamgm : Real.sqrt N * SmoothEngine.mono k u * M ≤
      (Real.sqrt N * SmoothEngine.mono k u) ^ 2 / 2 + M ^ 2 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt N * SmoothEngine.mono k u - M)]
  have hsqN : (Real.sqrt N * SmoothEngine.mono k u) ^ 2 =
      N * SmoothEngine.mono (fun i => 2 * k i) u := by rw [mul_pow, Real.sq_sqrt hN, hsq]
  rw [hsqN] at hamgm
  have h1 : Real.sqrt N * SmoothEngine.mono k u * ξ u ≤ Real.sqrt N * SmoothEngine.mono k u * M :=
    mul_le_mul_of_nonneg_left hξu hs
  have hexp : Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
      Real.sqrt N * SmoothEngine.mono k u * ξ u) ≤
      Real.exp (M ^ 2 / 2) * Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt (N / 2) * SmoothEngine.mono k u * 0) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [h1.trans hamgm]
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA u hu)
  calc ‖η u * SmoothEngine.mono h u * Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt N * SmoothEngine.mono k u * ξ u)‖
      = |η u| * SmoothEngine.mono h u * Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
          Real.sqrt N * SmoothEngine.mono k u * ξ u) := by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), abs_of_nonneg hmh]
    _ ≤ A * SmoothEngine.mono h u * (Real.exp (M ^ 2 / 2) *
          Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
            Real.sqrt (N / 2) * SmoothEngine.mono k u * 0)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hA u hu) hmh) hexp (Real.exp_pos _).le
          (mul_nonneg hA0 hmh)
    _ = Real.exp (M ^ 2 / 2) * A * (1 * SmoothEngine.mono h u *
          Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
            Real.sqrt (N / 2) * SmoothEngine.mono k u * 0)) := by ring

/-- The half-temperature dominating sequence, normalised at a chart-leading pair, is eventually
bounded. -/
theorem exists_eventually_bound_empBoxIntegral_half (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) :
    ∃ C : ℝ, ∀ᶠ N in atTop, |empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) /
      (N ^ (-lam) * Real.log N ^ (m - 1))| ≤ C := by
  have hT := tendsto_empBoxIntegral_div_boxFaceLimit h k hk hb hm hlead (fun _ => 0) (fun _ => 1)
    continuous_const continuous_const
  have hhalf : Tendsto (fun N : ℝ => N / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
  have hTc := hT.comp hhalf
  have hlog : Tendsto (fun N : ℝ => (1 - Real.log 2 * (Real.log N)⁻¹) ^ (m - 1)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := Real.log 2)).mul tendsto_inv_log).const_sub (1 : ℝ)).pow
      (m - 1)
    simpa using this
  have hprod := (hTc.mul hlog).const_mul ((2 : ℝ) ^ lam)
  set L := (2 : ℝ) ^ lam * (boxFaceLimit h k lam m b (fun _ => 0) (fun _ => 1) * 1) with hL
  refine ⟨|L| + 1, ?_⟩
  have hev := Metric.tendsto_nhds.1 hprod 1 one_pos
  filter_upwards [hev, eventually_gt_atTop (2 : ℝ)] with N hN hN2
  have hN0 : 0 < N := by linarith
  have hN1 : 1 < N := by linarith
  have hN20 : 0 < N / 2 := by linarith
  have hN21 : 1 < N / 2 := by linarith
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hkey : empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) /
      (N ^ (-lam) * Real.log N ^ (m - 1)) =
      (2 : ℝ) ^ lam * (empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) /
        ((N / 2) ^ (-lam) * Real.log (N / 2) ^ (m - 1)) *
          (1 - Real.log 2 * (Real.log N)⁻¹) ^ (m - 1)) := by
    have h1 : (N / 2) ^ (-lam) = N ^ (-lam) * (2 : ℝ) ^ lam := by
      rw [Real.div_rpow hN0.le two_pos.le, Real.rpow_neg two_pos.le, div_eq_mul_inv, inv_inv]
    have h2 : Real.log (N / 2) = Real.log N - Real.log 2 := Real.log_div hN0.ne' two_ne_zero
    have h3 : 1 - Real.log 2 * (Real.log N)⁻¹ = (Real.log N - Real.log 2) / Real.log N := by
      field_simp
    rw [h1, h2, h3, div_pow]
    have h4 : (N ^ (-lam) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have h5 : ((2 : ℝ) ^ lam) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    have h6 : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogN
    have h7 : (Real.log N - Real.log 2) ^ (m - 1) ≠ 0 := by
      rw [← h2]
      exact pow_ne_zero _ (Real.log_pos hN21).ne'
    field_simp
  rw [hkey]
  set X := (2 : ℝ) ^ lam * (empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) /
    ((N / 2) ^ (-lam) * Real.log (N / 2) ^ (m - 1)) *
      (1 - Real.log 2 * (Real.log N)⁻¹) ^ (m - 1)) with hX
  have hdist : |X - L| < 1 := by
    rw [← Real.dist_eq]
    simpa [Function.comp, hX] using hN
  have := abs_sub_abs_le_abs_sub X L
  linarith

theorem empBoxIntegral_zero_one_nonneg (h k : Fin d → ℕ) (N b : ℝ) :
    0 ≤ empBoxIntegral h k N b (fun _ => 0) fun _ => 1 := by
  unfold empBoxIntegral
  refine setIntegral_nonneg (SmoothEngine.measurableSet_box b) fun u hu => ?_
  have hmh : 0 ≤ SmoothEngine.mono h u :=
    Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hu i).le _
  positivity

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The empirical integrand and its piece transport -/

/-- The empirical integrand `e^{−N K∘π + √N √(K∘π) ψ} · F` on `U`. -/
noncomputable def empIntegrand (ξ : Ξ.RootField Y) (N : ℝ) (P : Ξ.R.U) : ℝ :=
  Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P) * Ξ.F P

theorem measurable_empFactor (ξ : Ξ.RootField Y) (N : ℝ) :
    Measurable fun P => Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P) :=
  Real.measurable_exp.comp (((Ξ.measurable_phaseU.const_mul _).add
    ((Ξ.measurable_phaseU.sqrt.const_mul _).mul ξ.ψ_meas)))

/-- The empirical factor is bounded by `e^{M²/2}` when `|ψ| ≤ M` and `N ≥ 0`. -/
theorem empFactor_le (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M)
    (P : Ξ.R.U) :
    Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P) ≤
      Real.exp (M ^ 2 / 2) := by
  refine Real.exp_le_exp.2 ?_
  have hK := Ξ.phaseU_nonneg P
  have hs : 0 ≤ Real.sqrt N * Real.sqrt (Ξ.phaseU P) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1 : Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P ≤
      Real.sqrt N * Real.sqrt (Ξ.phaseU P) * M :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM P)) hs
  have hsq : (Real.sqrt N * Real.sqrt (Ξ.phaseU P)) ^ 2 = N * Ξ.phaseU P := by
    rw [mul_pow, Real.sq_sqrt hN, Real.sq_sqrt hK]
  nlinarith [sq_nonneg (Real.sqrt N * Real.sqrt (Ξ.phaseU P) - M), mul_nonneg hN hK]

theorem integrable_empIntegrand (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ}
    (hM : ∀ P, |ξ.ψ P| ≤ M) : Integrable (Ξ.empIntegrand Y ξ N) Ξ.μU :=
  Ξ.F_int.bdd_mul (Ξ.measurable_empFactor Y ξ N).aestronglyMeasurable
    (Eventually.of_forall fun P => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Ξ.empFactor_le Y ξ hN hM P)

theorem coreMeasure_le_μU (p : (Ξ.X Y).PIdx) : Ξ.coreMeasure Y p ≤ Ξ.μU := by
  have h := (Ξ.decomp Y).core_le ((Ξ.X Y).en.symm p)
  have e : (Ξ.decomp Y).core ((Ξ.X Y).en.symm p) = Ξ.coreMeasure Y p := by
    change Ξ.coreMeasure Y ((Ξ.X Y).en ((Ξ.X Y).en.symm p)) = _
    rw [Equiv.apply_symm_apply]
  rw [e] at h
  exact h

/-- The empirical box kernel of a piece at the base point `s`. -/
noncomputable def empPieceKernel (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) N (Y.T.a p.1) (fun v => ξ.loc p (s, v))
    fun v => (Ξ.amp Y p).amp s v

/-- The empirical piece integral: the kernel integrated over the base. -/
noncomputable def empPieceInt (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ) : ℝ :=
  ∫ s, Ξ.empPieceKernel Y p ξ N s ∂(Ξ.piecePresentation Y p).ν

/-- The face limit of a piece at the pair `(λ, m)`, at the base point `s`. -/
noncomputable def pieceFaceLimit (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m (Y.T.a p.1) (fun v => ξ.loc p (s, v))
    fun v => (Ξ.amp Y p).amp s v

/-- The chart-leading condition: every piece is chart-leading at `(λ, m)`. -/
def ChartLeading (lam : ℝ) (m : ℕ) : Prop :=
  ∀ p : (Ξ.X Y).PIdx, BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m

theorem continuous_amp_uncurry (p : (Ξ.X Y).PIdx) :
    Continuous fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      (Ξ.amp Y p).amp z.1 z.2 :=
  (Ξ.contDiff_G Y p.1).continuous.comp ((Ξ.X Y).continuous_Tm p)

/-- The chart map of the piece presentation is the divisor point on the box. -/
theorem piecePresentation_Φ_eq_divPt (p : (Ξ.X Y).PIdx)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)}
    (hz : z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1)) :
    (Ξ.piecePresentation Y p).Φ z = Ξ.divPt Y p z.1 z.2 := by
  have hv : z.2 ∈ closedBox _ (Y.T.a p.1) :=
    mem_closedBox.2 fun i => Ioc_subset_Icc_self (hz i (Set.mem_univ i))
  change Y.chartInv p.1 (Ξ.facePt Y p z.1 z.2) = _
  rw [Y.chartInv_eq p.1 (Ξ.facePt_mem_target Y p z.1 hv)]
  rfl

/-- ★★ **Transport of the empirical core integral to the box**:
`∫ e^{−NK∘π + √N√(K∘π)ψ} F dcore_p = ∫_{Base} empBoxIntegral h k N b (loc_p(s,·)) (amp s) dν`. -/
theorem integral_coreMeasure_empIntegrand (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {N : ℝ}
    (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    ∫ P, Ξ.empIntegrand Y ξ N P ∂(Ξ.coreMeasure Y p) = Ξ.empPieceInt Y p ξ N := by
  set C := Ξ.piecePresentation Y p with hC
  have hint : Integrable (Ξ.empIntegrand Y ξ N) (Ξ.coreMeasure Y p) :=
    (Ξ.integrable_empIntegrand Y ξ hN hM).mono_measure (Ξ.coreMeasure_le_μU Y p)
  have hmeas : AEStronglyMeasurable (Ξ.empIntegrand Y ξ N) (Ξ.coreMeasure Y p) :=
    hint.aestronglyMeasurable
  have htr : ((smoothChartMeasure C.ν _ C.b).withDensity fun z =>
      ((SmoothEngine.mono C.h z.2 * C.ρ z).toNNReal : ℝ≥0∞)).map C.Φ = Ξ.coreMeasure Y p :=
    C.transport
  rw [← htr] at hmeas hint
  have hdens := C.measurable_density.real_toNNReal
  -- the pointwise identity on the box
  have hkey : ∀ᵐ z ∂smoothChartMeasure C.ν _ C.b,
      (SmoothEngine.mono C.h z.2 * C.ρ z).toNNReal • Ξ.empIntegrand Y ξ N (C.Φ z) =
        (Ξ.amp Y p).amp z.1 z.2 * SmoothEngine.mono ((Ξ.X Y).hA p) z.2 *
          Real.exp (-N * SmoothEngine.mono (fun i => 2 * (Ξ.X Y).kA p i) z.2 +
            Real.sqrt N * SmoothEngine.mono ((Ξ.X Y).kA p) z.2 * ξ.loc p (z.1, z.2)) := by
    filter_upwards [C.nonneg_ρ, C.phase_normal, C.amplitude_eq, C.ae_snd_mem_box] with z hρ hK hA hz
    have hmh : 0 ≤ SmoothEngine.mono C.h z.2 :=
      Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hz i).le _
    have hm1 : 0 < SmoothEngine.mono C.k z.2 :=
      Finset.prod_pos fun i _ => pow_pos (SmoothEngine.pos_of_mem_box hz i) _
    have hβ : C.βf z.1 = 1 := Y.phaseConst_eq_one p.1
    have hphase : Ξ.phaseU (C.Φ z) = SmoothEngine.mono (fun i => 2 * C.k i) z.2 := by
      have := hK
      rw [Ξ.D_phase] at this
      rw [this, hβ, one_mul]
    have hsqrt : Real.sqrt (Ξ.phaseU (C.Φ z)) = SmoothEngine.mono C.k z.2 := by
      rw [hphase, SmoothEngine.mono_two_mul_eq_sq, Real.sqrt_sq hm1.le]
    have hψ : ξ.ψ (C.Φ z) = ξ.loc p (z.1, z.2) := by
      rw [Ξ.piecePresentation_Φ_eq_divPt Y p hz, ← ξ.loc_eq p (z.1, z.2) hz]
    rw [NNReal.smul_def, Real.coe_toNNReal _ (mul_nonneg hmh hρ), smul_eq_mul]
    unfold empIntegrand
    rw [hsqrt, hψ, hphase]
    have hAz : (Ξ.amp Y p).amp z.1 z.2 = C.ρ z * Ξ.F (C.Φ z) := hA
    have hh : C.h = (Ξ.X Y).hA p := rfl
    have hk : C.k = (Ξ.X Y).kA p := rfl
    rw [hAz, hh, hk]
    ring
  have key : ∫ z, Ξ.empIntegrand Y ξ N z ∂(((smoothChartMeasure C.ν _ C.b).withDensity fun z =>
      ((SmoothEngine.mono C.h z.2 * C.ρ z).toNNReal : ℝ≥0∞)).map C.Φ) = Ξ.empPieceInt Y p ξ N := by
    rw [integral_map C.measurable_Φ.aemeasurable hmeas, integral_withDensity_eq_integral_smul hdens,
      integral_congr_ae hkey]
    have hint2 : Integrable (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
        (Fin ((Ξ.X Y).da p) → ℝ) => (Ξ.amp Y p).amp z.1 z.2 * SmoothEngine.mono ((Ξ.X Y).hA p) z.2 *
          Real.exp (-N * SmoothEngine.mono (fun i => 2 * (Ξ.X Y).kA p i) z.2 +
            Real.sqrt N * SmoothEngine.mono ((Ξ.X Y).kA p) z.2 * ξ.loc p (z.1, z.2)))
        (smoothChartMeasure C.ν _ C.b) := by
      have := (integrable_map_measure hmeas C.measurable_Φ.aemeasurable).1 hint
      rw [integrable_withDensity_iff_integrable_smul hdens] at this
      exact this.congr hkey
    unfold smoothChartMeasure at hint2 ⊢
    rw [integral_prod _ hint2]
    rfl
  rwa [htr] at key

/-! ### The leading term of the empirical piece integral -/

theorem continuous_empPieceKernel_uncurry (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ) :
    Continuous fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      (Ξ.amp Y p).amp z.1 z.2 * SmoothEngine.mono ((Ξ.X Y).hA p) z.2 *
        Real.exp (-N * SmoothEngine.mono (fun i => 2 * (Ξ.X Y).kA p i) z.2 +
          Real.sqrt N * SmoothEngine.mono ((Ξ.X Y).kA p) z.2 * ξ.loc p (z.1, z.2)) := by
  have h1 := Ξ.continuous_amp_uncurry Y p
  have hmh := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) ((Ξ.X Y).hA p)
  have hm2 := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) fun i => 2 * (Ξ.X Y).kA p i
  have hmk := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) ((Ξ.X Y).kA p)
  have hloc : Continuous fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      ξ.loc p (z.1, z.2) := ξ.loc_cont p
  fun_prop

theorem aestronglyMeasurable_empPieceKernel (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ) :
    AEStronglyMeasurable (Ξ.empPieceKernel Y p ξ N) (Ξ.piecePresentation Y p).ν :=
  ((Ξ.continuous_empPieceKernel_uncurry Y p ξ N).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1)))).aestronglyMeasurable

/-- A uniform bound on the amplitude of a piece over `Base × [0,b]^d`. -/
theorem exists_amp_bound (p : (Ξ.X Y).PIdx) : ∃ A : ℝ, ∀ s (v : Fin ((Ξ.X Y).da p) → ℝ),
    v ∈ closedBox _ (Y.T.a p.1) → |(Ξ.amp Y p).amp s v| ≤ A := by
  obtain ⟨A, hA⟩ := (isCompact_univ.prod (isCompact_closedBox (d := (Ξ.X Y).da p)
    (Y.T.a p.1))).exists_bound_of_continuousOn (Ξ.continuous_amp_uncurry Y p).continuousOn
  exact ⟨A, fun s v hv => by simpa [Real.norm_eq_abs] using hA (s, v) ⟨Set.mem_univ _, hv⟩⟩

/-- ★★★ **The leading term of the empirical piece integral** at a chart-leading pair: the base
integral of the piece face limit. -/
theorem hasLeadingTerm_empPieceInt (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    HasLeadingTerm (Ξ.empPieceInt Y p ξ) (∫ s, Ξ.pieceFaceLimit Y p ξ lam m s
      ∂(Ξ.piecePresentation Y p).ν) lam (m - 1) := by
  obtain ⟨M, -, hM⟩ := ξ.exists_bound
  obtain ⟨A, hA⟩ := Ξ.exists_amp_bound Y p
  obtain ⟨C, hC⟩ := exists_eventually_bound_empBoxIntegral_half ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
    ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hm hlead
  have hbox : ∀ v : Fin ((Ξ.X Y).da p) → ℝ, v ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) →
      v ∈ closedBox _ (Y.T.a p.1) := fun v hv =>
    mem_closedBox.2 fun i => Ioc_subset_Icc_self (hv i (Set.mem_univ i))
  have hint := hasLeadingTerm_integral_of_dominated_kernel (μ := (Ξ.piecePresentation Y p).ν)
    (lam := lam) (k := m - 1) (L := fun N s => Ξ.empPieceKernel Y p ξ N s)
    (ℓ := fun s => Ξ.pieceFaceLimit Y p ξ lam m s) (β := fun _ => 1)
    (G := fun _ => Real.exp (M ^ 2 / 2) * |A| * C)
    (Eventually.of_forall fun N => by
      simpa [one_mul] using Ξ.aestronglyMeasurable_empPieceKernel Y p ξ N)
    (Eventually.of_forall fun s => by
      have := tendsto_empBoxIntegral_div_boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
        ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hm hlead (fun v => ξ.loc p (s, v))
        (fun v => (Ξ.amp Y p).amp s v) ((ξ.loc_cont p).comp (Continuous.prodMk_right s))
        ((Ξ.amp Y p).smooth s).continuous
      exact this)
    ?_ ?_
  · unfold empPieceInt
    simpa [one_mul] using hint
  · filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with N hN hN1
    refine Eventually.of_forall fun s => ?_
    have hN0 : 0 ≤ N := by linarith
    have hscale : 0 < powLogScale lam (m - 1) N := powLogScale_pos _ _ hN1
    have hdom := abs_empBoxIntegral_le ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (b := Y.T.a p.1) hN0
      (ξ := fun v => ξ.loc p (s, v)) (η := fun v => (Ξ.amp Y p).amp s v) (M := M) (A := |A|)
      (fun v hv => hM p (s, v) (hbox v hv)) (fun v hv => (hA s v (hbox v hv)).trans (le_abs_self _))
    have hE0 := empBoxIntegral_zero_one_nonneg ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1)
    rw [abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
    calc |Ξ.empPieceKernel Y p ξ N s|
        ≤ Real.exp (M ^ 2 / 2) * |A| *
          empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
            (fun _ => 1) := hdom
      _ = Real.exp (M ^ 2 / 2) * |A| *
          (|empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
            (fun _ => 1) / powLogScale lam (m - 1) N| * powLogScale lam (m - 1) N) := by
          rw [abs_div, abs_of_pos hscale, abs_of_nonneg hE0, div_mul_cancel₀ _ hscale.ne']
      _ ≤ Real.exp (M ^ 2 / 2) * |A| * (C * powLogScale lam (m - 1) N) := by
          gcongr
          exact hN
      _ = Real.exp (M ^ 2 / 2) * |A| * C * powLogScale lam (m - 1) N := by ring
  · exact integrable_const _

end ResolvedData

end SmoothEngine

end Grammar
