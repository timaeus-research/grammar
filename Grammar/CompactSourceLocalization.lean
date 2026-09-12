/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceDecompositionAssembly
import Grammar.MonomialChartProductBox

/-!
# Compact source localisation on a monomial chart (CCLXXVII)

The honest unconditional localisation theorem (consult #85 unit 4). For hironaka's monomial chart
`IsMonomialChart K φ dom e h W` and a continuous nonnegative **source amplitude** `a` with compact
support inside the open monomial neighbourhood `W`, the source amplitude integral
`sourceAmpIntegral φ K a p N = ∫ a · |det Dφ| · (p∘φ) · e^{−N K∘φ}` splits, exactly for every
`N ≥ 0`, into finitely many source-weighted integrals over centred product boxes at divisor points
(the boxes of CCLXX, which are closed sup-balls `productBox_eq_closedBall`) with continuous
localised amplitudes `χ_k = a θ_k ≤ a` supported inside the open boxes, plus an exponentially small
remainder (`SourceLocalization`, ★ `IsMonomialChart.exists_sourceLocalization`):

* the supported zero locus `Z = tsupport a ∩ {y^e = 0}` is compact and covered by the open
  half-boxes of finitely many divisor points (`IsCompact.elim_finite_subcover`);
* the plateau bumps `plateau c ρ = clamp(3 − 4·dist(·,c)/ρ)` (equal to `1` on the closed half-ball,
  `0` off the `3ρ/4`-ball) are normalised by `θ_k = b_k / max(1, ∑ b)` — the elementary Euclidean
  route, no partition-of-unity API: `0 ≤ ∑ θ ≤ 1`, `∑ θ = 1` on the open union of the half-balls,
  a neighbourhood of `Z` (`theta`, `sum_theta_eq_one`);
* the remainder amplitude `a(1 − ∑θ)` has compact support disjoint from the zero set, so the phase
  has a positive gap there and the remainder is exponentially small (CCLXXIII).

A localisation is a certified source decomposition over the cover of box charts with the box
packages (`SourceLocalization.toSourceDecomposition`), so CCLXXVI applies:
★ `SourceLocalization.hasLeadingTerm` (`∫ a … = c N^{−λ*}(log N)^{k*} + o(·)` at the extremal pair
over the boxes), `SourceLocalization.isEquivalent` under the source dominant-face positivity of one
tied box, and `hasExponentialBound_of_isEmpty` when there is no divisor point in the support.

Not included: the unweighted localisation of an arbitrary compact chart domain (the box at a
divisor point need not lie in the domain, and a continuous cutoff cannot remove the part of the box
outside it — `dom = [0,1]`, `K = x²`: the whole-domain coefficient is `√π/2`, not that of the
bilateral box).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

/-! ### The product box is the closed ball -/

section BoxBall

variable {d : ℕ} {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} {ρ : ℝ}

theorem closedBall_subset_productBox (hρ : 0 < ρ) : Metric.closedBall y₀ ρ ⊆ productBox e y₀ ρ := by
  intro y hy
  rw [Metric.mem_closedBall, dist_pi_le_iff hρ.le] at hy
  have h1 : zeroOn (restrictExp e (divisorSet e y₀)).support y ∈ boxBase e y₀ ρ := by
    rw [support_restrictExp_divisor]
    intro j _
    by_cases hj : j ∈ divisorSet e y₀
    · simp only [if_pos hj, mem_singleton_iff]
      exact zeroOn_apply_of_mem _ hj y
    · simp only [if_neg hj, mem_Icc, zeroOn_apply_of_notMem _ hj]
      have := hy j
      rw [Real.dist_eq, abs_le] at this
      constructor <;> linarith [this.1, this.2]
  have h2 : ∀ j ∈ (restrictExp e (divisorSet e y₀)).support, |y j| ≤ ρ := fun j hj => by
    rw [support_restrictExp_divisor] at hj
    have := hy j
    rwa [Real.dist_eq, (mem_divisorSet.1 hj).2, sub_zero] at this
  exact And.intro h1 h2

theorem productBox_eq_closedBall (hρ : 0 < ρ) : productBox e y₀ ρ = Metric.closedBall y₀ ρ :=
  Subset.antisymm (productBox_subset_closedBall hρ) (closedBall_subset_productBox hρ)

end BoxBall

/-! ### Plateau bumps and their normalisation -/

section Plateau

variable {d : ℕ}

/-- **The plateau bump** at `c` of radius `ρ`: `1` on the closed `ρ/2`-ball, `0` off the open
`3ρ/4`-ball, values in `[0, 1]`. -/
noncomputable def plateau (c : Fin d → ℝ) (ρ : ℝ) (y : Fin d → ℝ) : ℝ :=
  max 0 (min 1 (3 - 4 * dist y c / ρ))

variable {c y : Fin d → ℝ} {ρ : ℝ}

theorem plateau_nonneg : 0 ≤ plateau c ρ y := le_max_left _ _

theorem plateau_le_one : plateau c ρ y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_plateau (c : Fin d → ℝ) (ρ : ℝ) : Continuous (plateau c ρ) :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    ((continuous_const.mul (continuous_id.dist continuous_const)).div_const ρ)))

theorem plateau_eq_one (hρ : 0 < ρ) (hy : dist y c ≤ ρ / 2) : plateau c ρ y = 1 := by
  unfold plateau
  have h1 : 1 ≤ 3 - 4 * dist y c / ρ := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hρ]
    linarith
  rw [min_eq_left h1, max_eq_right zero_le_one]

theorem plateau_eq_zero (hρ : 0 < ρ) (hy : 3 * ρ / 4 ≤ dist y c) : plateau c ρ y = 0 := by
  unfold plateau
  have h1 : 3 - 4 * dist y c / ρ ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hρ]
    linarith
  exact max_eq_left (min_le_of_right_le h1)

theorem support_plateau_subset (hρ : 0 < ρ) :
    Function.support (plateau c ρ) ⊆ Metric.ball c (3 * ρ / 4) := fun y hy => by
  rw [Function.mem_support] at hy
  rw [Metric.mem_ball]
  by_contra h
  exact hy (plateau_eq_zero hρ (not_lt.1 h))

theorem tsupport_plateau_subset (hρ : 0 < ρ) : tsupport (plateau c ρ) ⊆ Metric.ball c ρ :=
  (closure_mono (support_plateau_subset hρ)).trans
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith)))

variable {ι : Type*} [Fintype ι] (pt : ι → (Fin d → ℝ)) (ρs : ι → ℝ)

/-- **The normalised plateau family** `θ_k = b_k / max(1, ∑ b)`. -/
noncomputable def theta (k : ι) (y : Fin d → ℝ) : ℝ :=
  plateau (pt k) (ρs k) y / max 1 (∑ k', plateau (pt k') (ρs k') y)

theorem one_le_max_bumpSum (y : Fin d → ℝ) : 1 ≤ max 1 (∑ k', plateau (pt k') (ρs k') y) :=
  le_max_left _ _

theorem theta_nonneg (k : ι) (y : Fin d → ℝ) : 0 ≤ theta pt ρs k y :=
  div_nonneg plateau_nonneg (zero_le_one.trans (one_le_max_bumpSum pt ρs y))

theorem theta_le_plateau (k : ι) (y : Fin d → ℝ) : theta pt ρs k y ≤ plateau (pt k) (ρs k) y :=
  div_le_self plateau_nonneg (one_le_max_bumpSum pt ρs y)

theorem continuous_theta (k : ι) : Continuous (theta pt ρs k) :=
  (continuous_plateau _ _).div
    (continuous_const.max (continuous_finsetSum _ fun k' _ => continuous_plateau (pt k') (ρs k')))
    fun y => (lt_of_lt_of_le one_pos (one_le_max_bumpSum pt ρs y)).ne'

theorem sum_theta (y : Fin d → ℝ) :
    ∑ k, theta pt ρs k y =
      (∑ k', plateau (pt k') (ρs k') y) / max 1 (∑ k', plateau (pt k') (ρs k') y) := by
  unfold theta
  rw [Finset.sum_div]

theorem sum_theta_le_one (y : Fin d → ℝ) : ∑ k, theta pt ρs k y ≤ 1 := by
  rw [sum_theta]
  exact div_le_one_of_le₀ (le_max_right _ _)
    (zero_le_one.trans (one_le_max_bumpSum pt ρs y))

theorem sum_theta_nonneg (y : Fin d → ℝ) : 0 ≤ ∑ k, theta pt ρs k y :=
  Finset.sum_nonneg fun k _ => theta_nonneg pt ρs k y

/-- The normalised family sums to `1` on the open union of the half-balls. -/
theorem sum_theta_eq_one {k₀ : ι} (hρ : 0 < ρs k₀) {y : Fin d → ℝ}
    (hy : dist y (pt k₀) < ρs k₀ / 2) : ∑ k, theta pt ρs k y = 1 := by
  rw [sum_theta]
  have hB : 1 ≤ ∑ k', plateau (pt k') (ρs k') y := by
    calc (1 : ℝ) = plateau (pt k₀) (ρs k₀) y := (plateau_eq_one hρ hy.le).symm
      _ ≤ ∑ k', plateau (pt k') (ρs k') y :=
        Finset.single_le_sum (fun k _ => plateau_nonneg) (Finset.mem_univ k₀)
  rw [max_eq_right hB]
  exact div_self (zero_lt_one.trans_le hB).ne'

theorem tsupport_theta_subset (k : ι) (hρ : 0 < ρs k) :
    tsupport (theta pt ρs k) ⊆ Metric.ball (pt k) (ρs k) := by
  refine (closure_mono ?_).trans (tsupport_plateau_subset hρ)
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  apply hy
  unfold theta
  rw [h0, zero_div]

end Plateau

/-! ### The source amplitude integral -/

section AmpIntegral

variable {d : ℕ}

/-- **The source amplitude integral** `∫ a · |det Dφ| · (p∘φ) · e^{−N K∘φ}`. -/
noncomputable def sourceAmpIntegral (φ : (Fin d → ℝ) → (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y, a y * |(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))

/-- A continuous compactly supported factor times a function continuous on the support is
integrable. -/
theorem integrable_mul_of_tsupport_subset {T : Set (Fin d → ℝ)} (hT : IsCompact T)
    {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ T) (hg : ContinuousOn g T) :
    Integrable fun y => f y * g y := by
  have hsub : Function.support (fun y => f y * g y) ⊆ T :=
    (Function.support_mul_subset_left _ _).trans ((subset_tsupport f).trans hfs)
  exact (integrableOn_iff_integrable_of_support_subset hsub).1
    ((hf.continuousOn.mul hg).integrableOn_compact hT)

variable {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W)

include hc in
/-- The Jacobian determinant of a monomial chart is continuous on the monomial neighbourhood. -/
theorem IsMonomialChart.continuousOn_absDet : ContinuousOn (fun y => |(fderiv ℝ φ y).det|) W :=
  (ContinuousLinearMap.continuous_det.comp_continuousOn
    ((hc.analyticOnNhd.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hc.isOpen le_rfl)).abs

include hc in
/-- The pulled-back phase is continuous on the monomial neighbourhood. -/
theorem IsMonomialChart.continuousOn_phase : ContinuousOn (fun y => K (φ y)) W := by
  obtain ⟨u, hu, -, hKu⟩ := hc.exists_unit
  exact (hu.mul (continuous_monomialEval e).continuousOn).congr fun y hy => hKu y hy

include hc in
/-- Off the zero set of the monomial the pulled-back phase is positive. -/
theorem IsMonomialChart.phase_pos_of_monomialEval_ne_zero (hK0 : ∀ x, 0 ≤ K x) {y : Fin d → ℝ}
    (hy : y ∈ W) (h0 : monomialEval y e ≠ 0) : 0 < K (φ y) := by
  obtain ⟨u, -, hu0, hKu⟩ := hc.exists_unit
  refine lt_of_le_of_ne (hK0 _) fun h => ?_
  rw [hKu y hy] at h
  exact mul_ne_zero (hu0 y hy) h0 h.symm

variable {y₀ : Fin d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
  (hball : Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W)

include hc hρ hball in
/-- The source chart integral of a box chart with an amplitude vanishing off the box is the source
amplitude integral. -/
theorem sourceChartIntegral_boxChart_eq {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hG : ∀ y ∉ productBox e y₀ ρ, G y = 0) (N : ℝ) :
    (ResolutionCover.ofChart (IsMonomialChart.boxChart hc hρ hball)).sourceChartIntegral () G K p
      N = sourceAmpIntegral φ K G p N := by
  rw [ResolutionCover.ofChart_sourceChartIntegral]
  unfold ResolutionChart.jac
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    rw [hG y hy, zero_mul, zero_mul, zero_mul]

end AmpIntegral

/-! ### Source localisations -/

/-- **A finite source localisation** of the amplitude `a` on a monomial chart: finitely many divisor
points with box radii, continuous localised amplitudes `χ_k ≤ a` supported inside the open boxes,
a uniform cutoff `ε ≤ ρ_k`, and the exact decomposition of the source amplitude integral with an
exponentially small remainder. -/
structure SourceLocalization {d : ℕ} (φ : (Fin d → ℝ) → (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ)
    (e : Fin d →₀ ℕ) (W : Set (Fin d → ℝ)) (a : (Fin d → ℝ) → ℝ) (p : TubeWeight d) where
  /-- The index type of the boxes. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The divisor points. -/
  pt : ι → (Fin d → ℝ)
  /-- The box radii. -/
  ρ : ι → ℝ
  ρ_pos : ∀ k, 0 < ρ k
  ball_subset : ∀ k, Metric.closedBall (pt k) (ρ k) ⊆ restrictNhd e (divisorSet e (pt k)) W
  divisor : ∀ k, monomialEval (pt k) e = 0
  /-- The localised amplitudes. -/
  χ : ι → (Fin d → ℝ) → ℝ
  χ_cont : ∀ k, Continuous (χ k)
  χ_nonneg : ∀ k y, 0 ≤ χ k y
  χ_le : ∀ k y, χ k y ≤ a y
  χ_support : ∀ k, tsupport (χ k) ⊆ Metric.ball (pt k) (ρ k)
  /-- A uniform cutoff below all radii. -/
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ∀ k, ε ≤ ρ k
  /-- The remainder. -/
  rem : ℝ → ℝ
  rem_bound : HasExponentialBound rem
  decomp : ∀ N : ℝ, 0 ≤ N →
    sourceAmpIntegral φ K a p N = (∑ k, sourceAmpIntegral φ K (χ k) p N) + rem N

namespace SourceLocalization

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} {a : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (L : SourceLocalization φ K e W a p)
  (hc : IsMonomialChart K φ dom e h W)

attribute [instance] SourceLocalization.fintype

theorem χ_eq_zero_of_notMem_box (k : L.ι) {y : Fin d → ℝ}
    (hy : y ∉ productBox e (L.pt k) (L.ρ k)) : L.χ k y = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hy
    (closedBall_subset_productBox (L.ρ_pos k) (Metric.ball_subset_closedBall (L.χ_support k hmem)))

include hc in
/-- **The cover of box charts.** -/
noncomputable def cover : ResolutionCover d L.ι :=
  ⟨fun k => IsMonomialChart.boxChart hc (L.ρ_pos k) (L.ball_subset k)⟩

include hc in
/-- **The box packages.** -/
noncomputable def packages :
    ∀ k, ProductMonomialChartVar (ResolutionCover.ofChart ((L.cover hc).chart k)) () K :=
  fun k => IsMonomialChart.boxPackage hc (L.ρ_pos k) (L.ball_subset k)

theorem packages_b (k : L.ι) : (L.packages hc k).b = L.ρ k := rfl

theorem packages_W (k : L.ι) : (L.packages hc k).W = restrictNhd e (divisorSet e (L.pt k)) W := rfl

theorem packages_r (k : L.ι) (x : Fin d → ℝ) : (L.packages hc k).r x = 1 := rfl

theorem packages_isActive (k : L.ι) : (L.packages hc k).IsActive :=
  IsMonomialChart.boxPackage_isActive hc (L.ρ_pos k) (L.ball_subset k) (L.divisor k)

theorem activeCharts_eq : (L.cover hc).activeCharts (L.packages hc) = Finset.univ := by
  classical
  exact Finset.filter_true_of_mem fun k _ => L.packages_isActive hc k

theorem activeCharts_nonempty [Nonempty L.ι] :
    ((L.cover hc).activeCharts (L.packages hc)).Nonempty := by
  rw [L.activeCharts_eq hc]
  exact Finset.univ_nonempty

/-- **A source localisation is a certified source decomposition** over the box cover. -/
noncomputable def toSourceDecomposition :
    (L.cover hc).SourceDecomposition L.χ K p (sourceAmpIntegral φ K a p) where
  rem := L.rem
  decomp := fun N hN => by
    rw [L.decomp N hN]
    congr 1
    exact Finset.sum_congr rfl fun k _ =>
      (sourceChartIntegral_boxChart_eq hc (L.ρ_pos k) (L.ball_subset k)
        (fun y hy => L.χ_eq_zero_of_notMem_box k hy) N).symm

variable (hK0 : ∀ x, 0 ≤ K x) (hK : Measurable K) (hpc : ContinuousOn (fun y => p.w (φ y)) W)

include hK0 hK hpc in
/-- ★ **The leading term of a localised source amplitude integral** at the extremal pair over the
boxes, with coefficient the sum of the tied source coefficients (possibly zero). -/
theorem hasLeadingTerm [Nonempty L.ι] :
    HasLeadingTerm (sourceAmpIntegral φ K a p)
      ((L.cover hc).sourceDecompCoeff (L.packages hc) L.χ hK0 L.ε_pos L.ε_le
        (fun _ => hpc.mono (restrictNhd_subset _ _ _)) (fun k => (L.χ_cont k).measurable)
        (fun k => (L.χ_cont k).continuousOn) hK (L.activeCharts_nonempty hc))
      ((L.cover hc).partitionLam' (L.packages hc) (L.activeCharts_nonempty hc))
      ((L.cover hc).partitionDeg' (L.packages hc) (L.activeCharts_nonempty hc)) :=
  (L.cover hc).hasLeadingTerm_of_sourceDecomposition_exponential (L.packages hc) L.χ hK0 L.ε_pos
    L.ε_le (fun _ => hpc.mono (restrictNhd_subset _ _ _))
    (fun k => (L.χ_cont k).measurable) (fun k => (L.χ_cont k).continuousOn) hK
    (L.activeCharts_nonempty hc) (L.toSourceDecomposition hc) L.rem_bound

include hK0 hK hpc in
/-- ★★ **Asymptotic equivalence of a localised source amplitude integral** with an explicit
positive coefficient, when some tied box has an all-minimal stratum at the pair whose source
dominant face has positive measure. -/
theorem isEquivalent [Nonempty L.ι] (hp0 : ∀ x, 0 ≤ p.w x) (k₀ : L.ι)
    (htied : (L.cover hc).chartLam' (L.packages hc) k₀ =
        (L.cover hc).partitionLam' (L.packages hc) (L.activeCharts_nonempty hc) ∧
      (L.cover hc).chartDeg' (L.packages hc) k₀ =
        (L.cover hc).partitionDeg' (L.packages hc) (L.activeCharts_nonempty hc))
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (L.packages hc k₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (L.packages hc k₀).ratio j = (L.cover hc).chartLam' (L.packages hc) k₀)
    (hdeg : I₀.card - 1 = (L.cover hc).chartDeg' (L.packages hc) k₀)
    (hpos : 0 < volume ((L.packages hc k₀).sourceDominantFace
      (fun _ => (L.packages hc k₀).e.support) L.ε I₀ hne₀ (L.χ k₀) p)) :
    0 < (L.cover hc).sourceDecompCoeff (L.packages hc) L.χ hK0 L.ε_pos L.ε_le
        (fun _ => hpc.mono (restrictNhd_subset _ _ _)) (fun k => (L.χ_cont k).measurable)
        (fun k => (L.χ_cont k).continuousOn) hK (L.activeCharts_nonempty hc) ∧
      sourceAmpIntegral φ K a p ~[atTop] fun N =>
        (L.cover hc).sourceDecompCoeff (L.packages hc) L.χ hK0 L.ε_pos L.ε_le
          (fun _ => hpc.mono (restrictNhd_subset _ _ _)) (fun k => (L.χ_cont k).measurable)
          (fun k => (L.χ_cont k).continuousOn) hK (L.activeCharts_nonempty hc) *
        powLogScale ((L.cover hc).partitionLam' (L.packages hc) (L.activeCharts_nonempty hc))
          ((L.cover hc).partitionDeg' (L.packages hc) (L.activeCharts_nonempty hc)) N :=
  (L.cover hc).isEquivalent_of_sourceDecomposition (L.packages hc) L.χ hK0 L.ε_pos
    L.ε_le (fun _ => hpc.mono (restrictNhd_subset _ _ _))
    (fun k => (L.χ_cont k).measurable) (fun k => (L.χ_cont k).continuousOn) hK
    (L.activeCharts_nonempty hc) (L.toSourceDecomposition hc)
    (L.rem_bound.isLittleO_powLogScale _ _) L.χ_nonneg hp0
    (fun k x => by rw [L.packages_r hc k x]; exact zero_le_one) k₀
    (L.packages_isActive hc k₀) htied I₀ hI₀ hne₀ hall hdeg hpos

/-- With no divisor point in the support the source amplitude integral is exponentially small. -/
theorem hasExponentialBound_of_isEmpty [IsEmpty L.ι] :
    HasExponentialBound (sourceAmpIntegral φ K a p) := by
  obtain ⟨C, hC, κ, hκ, hb⟩ := L.rem_bound
  refine ⟨C, hC, κ, hκ, fun N hN => ?_⟩
  rw [L.decomp N hN, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  exact hb N hN

end SourceLocalization

/-! ### The construction -/

section Construction

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W)

include hc in
/-- ★ **Compact source localisation**: every continuous nonnegative amplitude with compact support
inside the monomial neighbourhood has a finite source localisation. -/
theorem IsMonomialChart.exists_sourceLocalization (hK0 : ∀ x, 0 ≤ K x) {p : TubeWeight d}
    (hpc : ContinuousOn (fun y => p.w (φ y)) W) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a)
    (ha0 : ∀ y, 0 ≤ a y) (hsupp : IsCompact (tsupport a)) (hsW : tsupport a ⊆ W) :
    Nonempty (SourceLocalization φ K e W a p) := by
  classical
  -- the supported zero locus and its finite cover by half-balls of divisor points
  set Z : Set (Fin d → ℝ) := tsupport a ∩ {y | monomialEval y e = 0} with hZdef
  have hZ : IsCompact Z :=
    hsupp.inter_right (isClosed_eq (continuous_monomialEval e) continuous_const)
  have hex : ∀ z : Z, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (z : Fin d → ℝ) r ⊆ restrictNhd e (divisorSet e z) W := fun z =>
    exists_closedBall_subset_restrictNhd hc.isOpen e (hsW z.2.1)
  choose ρ' hρ' hball' using hex
  have hZcov : Z ⊆ ⋃ z : Z, Metric.ball (z : Fin d → ℝ) (ρ' z / 2) := fun y hy =>
    mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hρ' ⟨y, hy⟩))⟩
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun z : Z => Metric.ball (z : Fin d → ℝ) (ρ' z / 2))
    (fun _ => Metric.isOpen_ball) hZcov
  -- the data
  let ι := {z : Z // z ∈ t}
  let pt : ι → (Fin d → ℝ) := fun k => (k.1 : Fin d → ℝ)
  let ρs : ι → ℝ := fun k => ρ' k.1
  have hρs : ∀ k, 0 < ρs k := fun k => hρ' k.1
  let χ : ι → (Fin d → ℝ) → ℝ := fun k y => a y * theta pt ρs k y
  let U : Set (Fin d → ℝ) := ⋃ k : ι, Metric.ball (pt k) (ρs k / 2)
  have hU : IsOpen U := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hZU : Z ⊆ U := fun y hy => by
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion.2 ⟨⟨z, hz⟩, hyz⟩
  have hsumU : ∀ y ∈ U, ∑ k, theta pt ρs k y = 1 := fun y hy => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    exact sum_theta_eq_one pt ρs (hρs k) (Metric.mem_ball.1 hk)
  -- the remainder
  let S : Set (Fin d → ℝ) := tsupport a \ U
  have hS : IsCompact S := hsupp.diff hU
  have hSW : S ⊆ W := fun y hy => hsW hy.1
  have hSpos : ∀ y ∈ S, 0 < K (φ y) := fun y hy => by
    exact IsMonomialChart.phase_pos_of_monomialEval_ne_zero hc hK0 (hSW hy) fun h0 =>
      hy.2 (hZU ⟨hy.1, h0⟩)
  let g : (Fin d → ℝ) → ℝ := fun y =>
    a y * (1 - ∑ k, theta pt ρs k y) * |(fderiv ℝ φ y).det| * p.w (φ y)
  have hgS : IntegrableOn g S := by
    refine ContinuousOn.integrableOn_compact hS ?_
    refine ((ha.continuousOn.mul (continuous_const.sub
      (continuous_finsetSum _ fun k _ => continuous_theta pt ρs k)).continuousOn).mul
      ((IsMonomialChart.continuousOn_absDet hc).mono hSW)).mul (hpc.mono hSW)
  let rem : ℝ → ℝ := fun N => ∫ y in S, g y * Real.exp (-N * K (φ y))
  have hrem : HasExponentialBound rem :=
    hasExponentialBound_setIntegral_of_isCompact hS hgS
      ((IsMonomialChart.continuousOn_phase hc).mono hSW) hSpos
  -- the cutoff
  let ε : ℝ := if hne : (Finset.univ : Finset ι).Nonempty then Finset.univ.inf' hne ρs / 2 else 1
  have hε : 0 < ε := by
    unfold ε
    split_ifs with hne
    · exact half_pos ((Finset.lt_inf'_iff hne).2 fun k _ => hρs k)
    · exact one_pos
  have hεle : ∀ k, ε ≤ ρs k := fun k => by
    unfold ε
    rw [dif_pos ⟨k, Finset.mem_univ k⟩]
    have := Finset.inf'_le ρs (Finset.mem_univ k)
    linarith [hρs k]
  -- the exact decomposition
  have hdecomp : ∀ N : ℝ, 0 ≤ N → sourceAmpIntegral φ K a p N =
      (∑ k, sourceAmpIntegral φ K (χ k) p N) + rem N := fun N hN => by
    -- integrability of the pieces on the support of `a`
    have hcontN : ContinuousOn (fun y => |(fderiv ℝ φ y).det| * p.w (φ y) *
        Real.exp (-N * K (φ y))) (tsupport a) :=
      (((IsMonomialChart.continuousOn_absDet hc).mono hsW).mul (hpc.mono hsW)).mul
        (Real.continuous_exp.comp_continuousOn
          (continuousOn_const.mul ((IsMonomialChart.continuousOn_phase hc).mono hsW)))
    have hint : ∀ k, Integrable fun y => χ k y * (|(fderiv ℝ φ y).det| * p.w (φ y) *
        Real.exp (-N * K (φ y))) := fun k =>
      integrable_mul_of_tsupport_subset hsupp (ha.mul (continuous_theta pt ρs k))
        tsupport_mul_subset_left hcontN
    have hintrem : Integrable fun y => (a y * (1 - ∑ k, theta pt ρs k y)) *
        (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))) :=
      integrable_mul_of_tsupport_subset hsupp (ha.mul (continuous_const.sub
        (continuous_finsetSum _ fun k _ => continuous_theta pt ρs k))) tsupport_mul_subset_left
        hcontN
    -- the pointwise identity
    have hpt : ∀ y, a y * |(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y)) =
        (∑ k, χ k y * (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y)))) +
          (a y * (1 - ∑ k, theta pt ρs k y)) *
            (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))) := fun y => by
      simp only [χ]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    -- the remainder as an integral over the whole space
    have hremeq : rem N = ∫ y, (a y * (1 - ∑ k, theta pt ρs k y)) *
        (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))) := by
      simp only [rem]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (μ := volume)
        (f := fun y => (a y * (1 - ∑ k, theta pt ρs k y)) *
          (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y)))) fun y hy => ?_]
      · refine setIntegral_congr_fun hS.measurableSet fun y _ => ?_
        simp only [g]
        ring
      · beta_reduce
        by_cases hya : y ∈ tsupport a
        · have hyU : y ∈ U := by
            by_contra hyU
            exact hy ⟨hya, hyU⟩
          rw [hsumU y hyU, sub_self, mul_zero, zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport hya, zero_mul, zero_mul]
    -- assemble
    unfold sourceAmpIntegral
    calc ∫ y, a y * |(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))
        = ∫ y, (∑ k, χ k y * (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y)))) +
            (a y * (1 - ∑ k, theta pt ρs k y)) *
              (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = (∑ k, ∫ y, χ k y * (|(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y)))) +
            rem N := by
          rw [integral_add (integrable_finset_sum _ fun k _ => hint k) hintrem,
            integral_finset_sum _ fun k _ => hint k, hremeq]
      _ = (∑ k, ∫ y, χ k y * |(fderiv ℝ φ y).det| * p.w (φ y) * Real.exp (-N * K (φ y))) +
            rem N := by
          congr 1
          refine Finset.sum_congr rfl fun k _ =>
            integral_congr_ae (Eventually.of_forall fun y => ?_)
          ring
  exact ⟨{ ι := ι
           fintype := inferInstance
           pt := pt
           ρ := ρs
           ρ_pos := hρs
           ball_subset := fun k => hball' k.1
           divisor := fun k => k.1.2.2
           χ := χ
           χ_cont := fun k => ha.mul (continuous_theta pt ρs k)
           χ_nonneg := fun k y => mul_nonneg (ha0 y) (theta_nonneg pt ρs k y)
           χ_le := fun k y => mul_le_of_le_one_right (ha0 y)
             ((theta_le_plateau pt ρs k y).trans plateau_le_one)
           χ_support := fun k =>
             tsupport_mul_subset_right.trans (tsupport_theta_subset pt ρs k (hρs k))
           ε := ε
           ε_pos := hε
           ε_le := hεle
           rem := rem
           rem_bound := hrem
           decomp := hdecomp }⟩

end Construction

end Grammar
