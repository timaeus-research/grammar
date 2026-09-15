/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldLipschitz
import Grammar.EmpiricalResolvedLeading
import Grammar.UniformCompactFamilies

/-!
# Continuous branch tuples and uniform asymptotics on compact field families

The empirical core sum depends on a root field only through its branch representatives on the
closed parameter boxes `Base_p × [0,b_p]^{d_p}` of the pieces. This unit defines the normed space
of *continuous branch tuples* `E = ∏_p C(Base_p × [0,b_p]^{d_p}, ℝ)` (sup norm), the core sum
`T_N(f) = Σ_p ∫_{Base_p} empBoxIntegral(f_p(s,·), amp_p(s)) dν_p` and its face limit `T(f)` on all
of `E`, and proves:

* `hasLeadingTerm_tupleZ`: `T_N(f)/(N^{−λ}(log N)^{m−1}) → T(f)` for every tuple at a
  chart-leading pair;
* `abs_tupleZ_sub_le`: the finite-`N` Lipschitz bound
  `|T_N(f) − T_N(g)| ≤ e^{R²} ‖f − g‖ Σ_p A_p ν_p(Base_p) · empBoxIntegral_p(N/2, 0, 1)` on the
  ball of radius `R`;
* `tendstoUniformlyOn_tupleZ` ★★★: **uniform asymptotics on compact field families** — on every
  compact `C ⊆ E` the normalised core sums converge uniformly to `T`;
* the bridge to root fields: `T_N(ξ̂) = Z^{emp}_N[F; ξ] − tail_N` (`empZ_eq_tupleZ_add_tail`) and
  `T(ξ̂) = Σ_p ∫ pieceFaceLimit_p` (`tupleLimit_tuple_eq`), so the limit of the empirical
  partition function is the value of `T` at the tuple of branch representatives.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### The clamp to the closed box -/

variable {d : ℕ}

/-- The coordinatewise clamp of `ℝ^d` onto `[0,b]^d`. -/
def clampBox (b : ℝ) (v : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min b (v i))

theorem continuous_clampBox (b : ℝ) : Continuous (clampBox (d := d) b) := by
  unfold clampBox
  fun_prop

theorem clampBox_mem_closedBox {b : ℝ} (hb : 0 ≤ b) (v : Fin d → ℝ) :
    clampBox b v ∈ closedBox d b :=
  mem_closedBox.2 fun _ => ⟨le_max_left _ _, max_le hb (min_le_left _ _)⟩

theorem clampBox_eq_of_mem {b : ℝ} {v : Fin d → ℝ} (hv : v ∈ closedBox d b) :
    clampBox b v = v := by
  funext i
  have hi := mem_closedBox.1 hv i
  unfold clampBox
  rw [min_eq_right hi.2, max_eq_right hi.1]

instance (b : ℝ) : CompactSpace ↥(closedBox d b) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBox b)

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Branch tuples -/

/-- The closed parameter domain of a piece, `Base_p × [0,b_p]^{d_p}` (compact). -/
abbrev PieceDom (p : (Ξ.X Y).PIdx) : Type :=
  Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ↥(closedBox ((Ξ.X Y).da p) (Y.T.a p.1))

/-- The normed space of continuous branch tuples, `∏_p C(Base_p × [0,b_p]^{d_p}, ℝ)` with the
sup norm. -/
abbrev BranchTuple : Type := ∀ p : (Ξ.X Y).PIdx, C(Ξ.PieceDom Y p, ℝ)

/-- The field of a tuple on the full parameter space of a piece, through the clamp. -/
noncomputable def tupleField (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)) : ℝ :=
  f p (z.1, ⟨clampBox (Y.T.a p.1) z.2, clampBox_mem_closedBox (Y.T.a_pos p.1).le _⟩)

theorem continuous_tupleField (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) :
    Continuous (Ξ.tupleField Y f p) := by
  unfold tupleField
  exact (f p).continuous.comp (continuous_fst.prodMk
    (((continuous_clampBox _).comp continuous_snd).subtype_mk _))

theorem tupleField_eq_of_mem (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)}
    (hz : z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1)) :
    Ξ.tupleField Y f p z = f p (z.1, ⟨z.2, hz⟩) := by
  unfold tupleField
  congr 2
  exact Subtype.ext (clampBox_eq_of_mem hz)

theorem abs_tupleField_le (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)) :
    |Ξ.tupleField Y f p z| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousMap.norm_coe_le_norm (f p) _).trans (norm_le_pi_norm f p)

theorem tupleField_sub (f g : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)) :
    Ξ.tupleField Y (f - g) p z = Ξ.tupleField Y f p z - Ξ.tupleField Y g p z := by
  unfold tupleField
  rw [Pi.sub_apply, ContinuousMap.sub_apply]

theorem abs_tupleField_sub_le (f g : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)) :
    |Ξ.tupleField Y f p z - Ξ.tupleField Y g p z| ≤ ‖f - g‖ := by
  rw [← Ξ.tupleField_sub Y f g p z]
  exact Ξ.abs_tupleField_le Y (f - g) p z

/-! ### The core sum and its face limit on all tuples -/

/-- The box kernel of a tuple on a piece at the base point `s`. -/
noncomputable def tupleKernel (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (N : ℝ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) N (Y.T.a p.1)
    (fun v => Ξ.tupleField Y f p (s, v)) fun v => (Ξ.amp Y p).amp s v

/-- The piece integral of a tuple. -/
noncomputable def tuplePieceInt (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (N : ℝ) : ℝ :=
  ∫ s, Ξ.tupleKernel Y f p N s ∂(Ξ.piecePresentation Y p).ν

/-- `T_N(f)`: the core sum of a tuple. -/
noncomputable def tupleZ (f : Ξ.BranchTuple Y) (N : ℝ) : ℝ := ∑ p, Ξ.tuplePieceInt Y f p N

/-- The face limit of a tuple on a piece at the base point `s`. -/
noncomputable def tupleFaceLimit (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (lam : ℝ) (m : ℕ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m (Y.T.a p.1)
    (fun v => Ξ.tupleField Y f p (s, v)) fun v => (Ξ.amp Y p).amp s v

/-- `T(f)`: the summed face limit of a tuple. -/
noncomputable def tupleLimit (f : Ξ.BranchTuple Y) (lam : ℝ) (m : ℕ) : ℝ :=
  ∑ p, ∫ s, Ξ.tupleFaceLimit Y f p lam m s ∂(Ξ.piecePresentation Y p).ν

theorem continuous_tupleKernel_uncurry (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (N : ℝ) :
    Continuous fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      (Ξ.amp Y p).amp z.1 z.2 * SmoothEngine.mono ((Ξ.X Y).hA p) z.2 *
        Real.exp (-N * SmoothEngine.mono (fun i => 2 * (Ξ.X Y).kA p i) z.2 +
          Real.sqrt N * SmoothEngine.mono ((Ξ.X Y).kA p) z.2 * Ξ.tupleField Y f p (z.1, z.2)) := by
  have h1 := Ξ.continuous_amp_uncurry Y p
  have hmh := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) ((Ξ.X Y).hA p)
  have hm2 := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) fun i => 2 * (Ξ.X Y).kA p i
  have hmk := SmoothEngine.continuous_mono (ι := Fin ((Ξ.X Y).da p)) ((Ξ.X Y).kA p)
  have hloc : Continuous fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      Ξ.tupleField Y f p (z.1, z.2) := Ξ.continuous_tupleField Y f p
  fun_prop

theorem aestronglyMeasurable_tupleKernel (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (N : ℝ) :
    AEStronglyMeasurable (Ξ.tupleKernel Y f p N) (Ξ.piecePresentation Y p).ν :=
  ((Ξ.continuous_tupleKernel_uncurry Y f p N).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1)))).aestronglyMeasurable

theorem box_mem_closedBox (p : (Ξ.X Y).PIdx) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1)) :
    v ∈ closedBox _ (Y.T.a p.1) :=
  mem_closedBox.2 fun i => Ioc_subset_Icc_self (hv i (Set.mem_univ i))

/-- Domination of the tuple kernel by the half-temperature zero-field integral. -/
theorem abs_tupleKernel_le (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {N : ℝ} (hN : 0 ≤ N)
    {A : ℝ} (hA : ∀ s (v : Fin ((Ξ.X Y).da p) → ℝ), v ∈ closedBox _ (Y.T.a p.1) →
      |(Ξ.amp Y p).amp s v| ≤ A) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    |Ξ.tupleKernel Y f p N s| ≤ Real.exp (‖f‖ ^ 2 / 2) * A *
      empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0) fun _ => 1 :=
  abs_empBoxIntegral_le ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) hN
    (fun v _ => Ξ.abs_tupleField_le Y f p (s, v))
    (fun v hv => hA s v (Ξ.box_mem_closedBox Y p hv))

/-- ★★ **Pointwise leading term of a tuple's piece integral** at a chart-leading pair. -/
theorem hasLeadingTerm_tuplePieceInt (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    HasLeadingTerm (Ξ.tuplePieceInt Y f p) (∫ s, Ξ.tupleFaceLimit Y f p lam m s
      ∂(Ξ.piecePresentation Y p).ν) lam (m - 1) := by
  obtain ⟨A, hA⟩ := Ξ.exists_amp_bound Y p
  obtain ⟨C, hC⟩ := exists_eventually_bound_empBoxIntegral_half ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
    ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hm hlead
  have hA' : ∀ s (v : Fin ((Ξ.X Y).da p) → ℝ), v ∈ closedBox _ (Y.T.a p.1) →
      |(Ξ.amp Y p).amp s v| ≤ |A| := fun s v hv => (hA s v hv).trans (le_abs_self _)
  have hint := hasLeadingTerm_integral_of_dominated_kernel (μ := (Ξ.piecePresentation Y p).ν)
    (lam := lam) (k := m - 1) (L := fun N s => Ξ.tupleKernel Y f p N s)
    (ℓ := fun s => Ξ.tupleFaceLimit Y f p lam m s) (β := fun _ => 1)
    (G := fun _ => Real.exp (‖f‖ ^ 2 / 2) * |A| * C)
    (Eventually.of_forall fun N => by
      simpa [one_mul] using Ξ.aestronglyMeasurable_tupleKernel Y f p N)
    (Eventually.of_forall fun s => by
      have := tendsto_empBoxIntegral_div_boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
        ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hm hlead (fun v => Ξ.tupleField Y f p (s, v))
        (fun v => (Ξ.amp Y p).amp s v)
        ((Ξ.continuous_tupleField Y f p).comp (Continuous.prodMk_right s))
        ((Ξ.amp Y p).smooth s).continuous
      exact this)
    ?_ ?_
  · unfold tuplePieceInt
    simpa [one_mul] using hint
  · filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with N hN hN1
    refine Eventually.of_forall fun s => ?_
    have hN0 : 0 ≤ N := by linarith
    have hscale : 0 < powLogScale lam (m - 1) N := powLogScale_pos _ _ hN1
    have hdom := Ξ.abs_tupleKernel_le Y f p hN0 hA' s
    have hE0 := empBoxIntegral_zero_one_nonneg ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1)
    rw [abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
    calc |Ξ.tupleKernel Y f p N s|
        ≤ Real.exp (‖f‖ ^ 2 / 2) * |A| *
          empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
            (fun _ => 1) := hdom
      _ = Real.exp (‖f‖ ^ 2 / 2) * |A| *
          (|empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
            (fun _ => 1) / powLogScale lam (m - 1) N| * powLogScale lam (m - 1) N) := by
          rw [abs_div, abs_of_pos hscale, abs_of_nonneg hE0, div_mul_cancel₀ _ hscale.ne']
      _ ≤ Real.exp (‖f‖ ^ 2 / 2) * |A| * (C * powLogScale lam (m - 1) N) := by
          gcongr
          exact hN
      _ = Real.exp (‖f‖ ^ 2 / 2) * |A| * C * powLogScale lam (m - 1) N := by ring
  · exact integrable_const _

/-- ★★ **Pointwise leading term of the core sum** of a tuple: `T_N(f)/s_N → T(f)`. -/
theorem hasLeadingTerm_tupleZ (f : Ξ.BranchTuple Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    HasLeadingTerm (Ξ.tupleZ Y f) (Ξ.tupleLimit Y f lam m) lam (m - 1) :=
  HasLeadingTerm.sum (lam := lam) (k := m - 1) Finset.univ
    (Z := fun p N => Ξ.tuplePieceInt Y f p N)
    (c := fun p => ∫ s, Ξ.tupleFaceLimit Y f p lam m s ∂(Ξ.piecePresentation Y p).ν)
    fun p _ => Ξ.hasLeadingTerm_tuplePieceInt Y f p hm (hlead p)

/-! ### The finite-`N` Lipschitz bound -/

/-- Lipschitz bound for the tuple kernel: on the ball of radius `R`,
`|K_N(f)(s) − K_N(g)(s)| ≤ e^{R²} ‖f − g‖ A · empBoxIntegral(N/2, 0, 1)`. -/
theorem abs_tupleKernel_sub_le (f g : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {N : ℝ} (hN : 0 ≤ N)
    {R : ℝ} (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R)
    {A : ℝ} (hA : ∀ s (v : Fin ((Ξ.X Y).da p) → ℝ), v ∈ closedBox _ (Y.T.a p.1) →
      |(Ξ.amp Y p).amp s v| ≤ A) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    |Ξ.tupleKernel Y f p N s - Ξ.tupleKernel Y g p N s| ≤ Real.exp (R ^ 2) * ‖f - g‖ * A *
      empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0) fun _ => 1 :=
  abs_empBoxIntegral_sub_le ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) hN
    ((Ξ.continuous_tupleField Y f p).comp (Continuous.prodMk_right s))
    ((Ξ.continuous_tupleField Y g p).comp (Continuous.prodMk_right s))
    ((Ξ.amp Y p).smooth s).continuous
    (fun v _ => (Ξ.abs_tupleField_le Y f p (s, v)).trans hf)
    (fun v _ => (Ξ.abs_tupleField_le Y g p (s, v)).trans hg)
    (fun v _ => Ξ.abs_tupleField_sub_le Y f g p (s, v))
    (fun v hv => hA s v (Ξ.box_mem_closedBox Y p hv))

theorem integrable_tupleKernel (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (Ξ.tupleKernel Y f p N) (Ξ.piecePresentation Y p).ν := by
  obtain ⟨A, hA⟩ := Ξ.exists_amp_bound Y p
  refine Integrable.of_bound (Ξ.aestronglyMeasurable_tupleKernel Y f p N)
    (Real.exp (‖f‖ ^ 2 / 2) * A * empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2)
      (Y.T.a p.1) (fun _ => 0) fun _ => 1) (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  exact Ξ.abs_tupleKernel_le Y f p hN hA s

/-- Lipschitz bound for the piece integral of a tuple. -/
theorem abs_tuplePieceInt_sub_le (f g : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {N : ℝ} (hN : 0 ≤ N)
    {R : ℝ} (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R)
    {A : ℝ} (hA : ∀ s (v : Fin ((Ξ.X Y).da p) → ℝ), v ∈ closedBox _ (Y.T.a p.1) →
      |(Ξ.amp Y p).amp s v| ≤ A) :
    |Ξ.tuplePieceInt Y f p N - Ξ.tuplePieceInt Y g p N| ≤ Real.exp (R ^ 2) * ‖f - g‖ * A *
      empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0) (fun _ => 1) *
      ((Ξ.piecePresentation Y p).ν).real univ := by
  unfold tuplePieceInt
  rw [← integral_sub (Ξ.integrable_tupleKernel Y f p hN) (Ξ.integrable_tupleKernel Y g p hN),
    ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]
    exact Ξ.abs_tupleKernel_sub_le Y f g p hN hf hg hA s)

/-- The finite-`N` Lipschitz constant of the core sum (before normalisation), given amplitude
bounds `A p`. -/
noncomputable def tupleLipConst (A : (Ξ.X Y).PIdx → ℝ) (R N : ℝ) : ℝ :=
  Real.exp (R ^ 2) * ∑ p, A p *
    empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0) (fun _ => 1) *
    ((Ξ.piecePresentation Y p).ν).real univ

/-- ★★ **Finite-`N` Lipschitz bound for the core sum**: on the ball of radius `R`,
`|T_N(f) − T_N(g)| ≤ tupleLipConst A R N · ‖f − g‖`. -/
theorem abs_tupleZ_sub_le (f g : Ξ.BranchTuple Y) {N : ℝ} (hN : 0 ≤ N)
    {R : ℝ} (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R)
    {A : (Ξ.X Y).PIdx → ℝ} (hA : ∀ p s (v : Fin ((Ξ.X Y).da p) → ℝ),
      v ∈ closedBox _ (Y.T.a p.1) → |(Ξ.amp Y p).amp s v| ≤ A p) :
    |Ξ.tupleZ Y f N - Ξ.tupleZ Y g N| ≤ Ξ.tupleLipConst Y A R N * ‖f - g‖ := by
  unfold tupleZ tupleLipConst
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  refine (Ξ.abs_tuplePieceInt_sub_le Y f g p hN hf hg (hA p)).trans (le_of_eq ?_)
  ring

/-! ### Uniform asymptotics on compact families -/

/-- The normalised core sums are eventually uniformly Lipschitz on every ball. -/
theorem exists_eventually_lipschitz_tupleZ_div {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) (R : ℝ) :
    ∃ L : ℝ, ∀ᶠ N in atTop, ∀ f g : Ξ.BranchTuple Y, ‖f‖ ≤ R → ‖g‖ ≤ R →
      |Ξ.tupleZ Y f N / powLogScale lam (m - 1) N - Ξ.tupleZ Y g N / powLogScale lam (m - 1) N| ≤
        L * ‖f - g‖ := by
  choose A hA using fun p => Ξ.exists_amp_bound Y p
  choose Cb hCb using fun p => exists_eventually_bound_empBoxIntegral_half ((Ξ.X Y).hA p)
    ((Ξ.X Y).kA p) ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hm (hlead p)
  have hA' : ∀ p s (v : Fin ((Ξ.X Y).da p) → ℝ), v ∈ closedBox _ (Y.T.a p.1) →
      |(Ξ.amp Y p).amp s v| ≤ |A p| := fun p s v hv => (hA p s v hv).trans (le_abs_self _)
  refine ⟨Real.exp (R ^ 2) * ∑ p, |A p| * Cb p * ((Ξ.piecePresentation Y p).ν).real univ, ?_⟩
  filter_upwards [eventually_all.2 hCb, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  intro f g hf hg
  have hN0 : 0 ≤ N := by linarith
  have hscale : 0 < powLogScale lam (m - 1) N := powLogScale_pos _ _ hN1
  have hpl : powLogScale lam (m - 1) N = N ^ (-lam) * Real.log N ^ (m - 1) := rfl
  rw [← sub_div, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
  have hL : Ξ.tupleLipConst Y (fun p => |A p|) R N ≤ (Real.exp (R ^ 2) *
      ∑ p, |A p| * Cb p * ((Ξ.piecePresentation Y p).ν).real univ) * powLogScale lam (m - 1) N := by
    unfold tupleLipConst
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (Real.exp_pos _).le
    have hE0 := empBoxIntegral_zero_one_nonneg ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1)
    have hb : empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
        (fun _ => 1) ≤ Cb p * powLogScale lam (m - 1) N := by
      have := hN p
      rw [← hpl, abs_div, abs_of_pos hscale, abs_of_nonneg hE0, div_le_iff₀ hscale] at this
      exact this
    have hν : 0 ≤ ((Ξ.piecePresentation Y p).ν).real univ := measureReal_nonneg
    calc |A p| * empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (N / 2) (Y.T.a p.1) (fun _ => 0)
          (fun _ => 1) * ((Ξ.piecePresentation Y p).ν).real univ
        ≤ |A p| * (Cb p * powLogScale lam (m - 1) N) *
          ((Ξ.piecePresentation Y p).ν).real univ := by gcongr
      _ = |A p| * Cb p * ((Ξ.piecePresentation Y p).ν).real univ * powLogScale lam (m - 1) N := by
          ring
  calc |Ξ.tupleZ Y f N - Ξ.tupleZ Y g N|
      ≤ Ξ.tupleLipConst Y (fun p => |A p|) R N * ‖f - g‖ :=
        Ξ.abs_tupleZ_sub_le Y f g hN0 hf hg hA'
    _ ≤ (Real.exp (R ^ 2) * ∑ p, |A p| * Cb p * ((Ξ.piecePresentation Y p).ν).real univ) *
          powLogScale lam (m - 1) N * ‖f - g‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = (Real.exp (R ^ 2) * ∑ p, |A p| * Cb p * ((Ξ.piecePresentation Y p).ν).real univ) *
          ‖f - g‖ * powLogScale lam (m - 1) N := by ring

/-- ★★★ **Uniform asymptotics on compact field families**: at a chart-leading pair `(λ, m)`, the
normalised core sums `T_N(f)/(N^{−λ}(log N)^{m−1})` converge to `T(f)` uniformly over every
compact set `C` of continuous branch tuples. -/
theorem tendstoUniformlyOn_tupleZ {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m)
    {C : Set (Ξ.BranchTuple Y)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun N f => Ξ.tupleZ Y f N / powLogScale lam (m - 1) N)
      (fun f => Ξ.tupleLimit Y f lam m) atTop C := by
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  obtain ⟨L, hL⟩ := Ξ.exists_eventually_lipschitz_tupleZ_div Y hm hlead R
  refine tendstoUniformlyOn_of_eventually_lipschitz (L := L) hC
    (fun f _ => Ξ.hasLeadingTerm_tupleZ Y f hm hlead) ?_
  filter_upwards [hL] with N hN
  intro f hf g hg
  rw [dist_eq_norm]
  exact hN f g (hR f hf) (hR g hg)

/-! ### The bridge to root fields -/

/-- The branch tuple of a root field: the representatives restricted to the closed boxes. -/
noncomputable def RootField.tuple (ξ : Ξ.RootField Y) : Ξ.BranchTuple Y := fun p =>
  ⟨fun z => ξ.loc p (z.1, z.2.1), (ξ.loc_cont p).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

theorem tupleField_tuple (ξ : Ξ.RootField Y) (p : (Ξ.X Y).PIdx)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)}
    (hz : z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1)) :
    Ξ.tupleField Y ξ.tuple p z = ξ.loc p z := by
  rw [Ξ.tupleField_eq_of_mem Y ξ.tuple p hz]
  rfl

/-- The empirical piece kernel of a root field is the tuple kernel of its branch tuple. -/
theorem empPieceKernel_eq_tupleKernel (ξ : Ξ.RootField Y) (p : (Ξ.X Y).PIdx) (N : ℝ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    Ξ.empPieceKernel Y p ξ N s = Ξ.tupleKernel Y ξ.tuple p N s := by
  unfold empPieceKernel tupleKernel empBoxIntegral
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box _) fun v hv => ?_
  simp only
  rw [Ξ.tupleField_tuple Y ξ p (Ξ.box_mem_closedBox Y p hv)]

theorem empPieceInt_eq_tuplePieceInt (ξ : Ξ.RootField Y) (p : (Ξ.X Y).PIdx) (N : ℝ) :
    Ξ.empPieceInt Y p ξ N = Ξ.tuplePieceInt Y ξ.tuple p N := by
  unfold empPieceInt tuplePieceInt
  simp_rw [Ξ.empPieceKernel_eq_tupleKernel Y ξ p N]

/-- ★★ **The empirical partition function is the core sum at the branch tuple plus the tail**. -/
theorem empZ_eq_tupleZ_add_tail (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ}
    (hM : ∀ P, |ξ.ψ P| ≤ M) :
    Ξ.empZ Y ξ N = Ξ.tupleZ Y ξ.tuple N + ∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU := by
  rw [Ξ.empZ_eq_sum Y ξ hN hM]
  unfold tupleZ
  congr 1
  exact Finset.sum_congr rfl fun p _ => Ξ.empPieceInt_eq_tuplePieceInt Y ξ p N

/-- The normalised empirical partition function and the normalised core sum at the branch tuple
differ by the normalised tail, which is `O(e^{−δN/2}/s_N)`. -/
theorem abs_empZ_div_sub_tupleZ_div_le (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 < N) {M : ℝ}
    (hM : ∀ P, |ξ.ψ P| ≤ M) (lam : ℝ) (q : ℕ) :
    |Ξ.empZ Y ξ N / powLogScale lam q N - Ξ.tupleZ Y ξ.tuple N / powLogScale lam q N| ≤
      (Real.exp (M ^ 2 / 2) * ∫ P, |Ξ.F P| ∂Y.tailU) * Real.exp (-(Y.T.δ / 2) * N) /
        |powLogScale lam q N| := by
  rw [← sub_div, abs_div, Ξ.empZ_eq_tupleZ_add_tail Y ξ hN.le hM, add_sub_cancel_left]
  exact div_le_div_of_nonneg_right (Ξ.abs_integral_tail_le Y ξ hN.le hM) (abs_nonneg _)

/-- ★★ **The face limit of a root field is `T` at its branch tuple**: the limit of the empirical
partition function is the value of the summed face functional on the tuple of representatives. -/
theorem tupleLimit_tuple_eq (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    Ξ.tupleLimit Y ξ.tuple lam m =
      ∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
  have h1 := Ξ.hasLeadingTerm_tupleZ Y ξ.tuple hm hlead
  have h2 := Ξ.hasLeadingTerm_empZ Y ξ hm hlead hM
  have h3 := (h1.add (Ξ.hasLeadingTerm_tail_zero Y ξ hM lam (m - 1)))
  rw [add_zero] at h3
  have h4 : HasLeadingTerm (Ξ.empZ Y ξ) (Ξ.tupleLimit Y ξ.tuple lam m) lam (m - 1) := by
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    exact (Ξ.empZ_eq_tupleZ_add_tail Y ξ hN hM).symm
  exact tendsto_nhds_unique h4 h2

end ResolvedData

end SmoothEngine

end Grammar
