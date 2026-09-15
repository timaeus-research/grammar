/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedStratumFormula
import Grammar.SmoothFaceMonoTop

/-!
# Positivity and values-only dependence of the graded stratum functional

Consult #130, Unit E3. On the EXACT STRATUM `S^μ_c = Z₀ ∩ {depth = c} ∩ {r_μ = c}`
(`exactStratum`) assume the ZERO-ORDER condition (`ZeroOrder`): every wall through a point of
`S^μ_c` has ratio exactly `μ`, `2kμ = h + 1`. Then for observables `F` vanishing near the deep
zero fibre `Z₀ ∩ {depth ≥ c+1}`:

* every face contributing to the stratum sum has resonant Taylor order `α_J = 0`, or its face
  point lies off the prior support and all amplitude jets vanish there (`stratum_or_jets_zero`:
  a face point with exactly the `J`-coordinates zero is a divisor point of the exact stratum,
  CDXLVIII, so the zero-order condition forces `α_J = 0`);
* hence `𝒯^U_{μ,c−1}[F] ≥ 0` for `F ≥ 0` (★★★ `coeff_nonneg_of_deep`: the face integrands are
  `amplitude · (positive power weight)` with `amplitude = ω|b|·prior∘π·F ≥ 0`, and the top face
  coefficients are the positive constants of CDXLVII);
* and `𝒯^U_{μ,c−1}[F]` depends only on the VALUES of `F` on `S^μ_c`
  (★★★ `coeff_eq_of_eqOn_exactStratum`, via `coeff_eq_zero_of_eqOn_zero_exactStratum`).

This is the positive stratum measure of Theorem E: on `𝓘_{c+1}` the functional is integration
against a positive density on the exact stratum, locally finite away from deeper strata. The
slogan "each stratum carries its own positive leading functional" holds exactly for strata whose
incident wall ratios coincide (Astra #130). Non-claims: finite total mass after adjoining the
deeper boundary; a Riesz representation. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The face derivative along the face list equals the full derivative for orders vanishing off
the face. -/
theorem pdMulti_lJ_eq_finRange_of_zero_off {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (hm : ∀ i ∉ J, m i = 0) :
    pdMulti m (lJ J) G = pdMulti m (List.finRange d) G := by
  rw [← pdMulti_perm hG m (lJ_append_lK_perm J), pdMulti_append,
    pdMulti_congr (m := m) (m' := 0) (l := lK J) (fun i hi => hm i ((mem_lK J).1 hi)) G,
    pdMulti_zero]

theorem mono_nonneg_of_mem_box {ι : Type*} [Fintype ι] {b : ℝ} {w : ι → ℝ} (hw : w ∈ box ι b)
    (a : ι → ℕ) : 0 ≤ mono a w :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hw i (Set.mem_univ i)).1.le _

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The exact stratum `S^μ_c = Z₀ ∩ {depth = c} ∩ {r_μ = c}`. -/
def exactStratum (μ : ℝ) (c : ℕ) : Set Ξ.R.U :=
  {P | P ∈ Ξ.zeroFibre ∧ depth Ξ.R Ξ.hK0 P = c ∧ resonanceCount Ξ.R Ξ.hK0 μ P = c}

/-- **The zero-order condition**: every wall through a point of the exact stratum has ratio
exactly `μ`. -/
def ZeroOrder (μ : ℝ) (c : ℕ) : Prop :=
  ∀ P ∈ Ξ.exactStratum μ c, ∀ q ∈ pairs Ξ.R Ξ.hK0 P, 2 * (q.1 : ℝ) * μ = q.2 + 1

/-! ### The chart fields of a piece -/

theorem chart_k (I : Fin (Fintype.card (Ξ.X Y).PIdx)) :
    ((Ξ.decomp Y).chart I).k = (Ξ.X Y).kA ((Ξ.X Y).en I) := rfl

theorem chart_h (I : Fin (Fintype.card (Ξ.X Y).PIdx)) :
    ((Ξ.decomp Y).chart I).h = (Ξ.X Y).hA ((Ξ.X Y).en I) := rfl

theorem chart_b (I : Fin (Fintype.card (Ξ.X Y).PIdx)) :
    ((Ξ.decomp Y).chart I).b = Y.T.a ((Ξ.X Y).en I).1 := rfl

theorem chart_βf (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
    ((Ξ.decomp Y).chart I).βf s = Y.T.phaseConst ((Ξ.X Y).en I).1 := rfl

theorem chart_amp (I : Fin (Fintype.card (Ξ.X Y).PIdx)) :
    ((Ξ.decomp Y).chart I).amp = Ξ.amp Y ((Ξ.X Y).en I) := rfl

/-! ### Face points -/

theorem glue_zero_mem_closedBox (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    glue J 0 w ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) :=
  mem_closedBox.2 fun i => glue_zero_mem_Icc J (Y.T.a_pos p.1) hw i

theorem glue_zero_eq_zero_iff (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1))
    (i : Fin ((Ξ.X Y).da p)) : glue J 0 w i = 0 ↔ i ∈ J := by
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi, Pi.zero_apply]
    exact ⟨fun _ => hi, fun _ => rfl⟩
  · rw [glue_apply_of_not_mem J _ _ hi]
    exact ⟨fun h0 => absurd h0 (hw ⟨i, fun h => hi (inJ_iff.1 h)⟩ (Set.mem_univ _)).1.ne',
      fun h => absurd h hi⟩

/-- The phase vanishes at the divisor point of a nonempty face. -/
theorem phase_divPt_eq_zero (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJne : J.Nonempty) (hvJ : ∀ i ∈ J, v i = 0) :
    Ξ.K (Ξ.R.gv (Ξ.divPt Y p s v)) = 0 := by
  have hu₀t : Ξ.facePt Y p s v ∈ (Y.φ p.1).target := Ξ.facePt_mem_target Y p s hv
  have hu₀V : Ξ.facePt Y p s v ∈ Y.T.V p.1 := (Y.V_eq p.1) ▸ hu₀t
  obtain ⟨i, hi⟩ := hJne
  have hψ : Y.T.ψ p.1 (Ξ.facePt Y p s v) = Ξ.R.gv (Ξ.divPt Y p s v) := Y.ψ_eq p.1 _ hu₀t
  rw [← hψ, Y.T.phase_eq p.1 _ hu₀V]
  refine mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ ((Ξ.X Y).eqv p i).1) ?_))
  rw [Ξ.facePt_apply_eq_zero Y p s (hvJ i hi)]
  exact zero_pow (mul_ne_zero two_ne_zero (Nat.pos_iff_ne_zero.1 ((Ξ.X Y).kA_pos p i)))

/-- The amplitude jets vanish at a face point whose divisor point lies off the prior support. -/
theorem pdMulti_amp_eq_zero_of_not_mem_tsupport (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) (hsupp : Ξ.R.gv (Ξ.divPt Y p s v) ∉ tsupport Ξ.prior)
    (α : Fin ((Ξ.X Y).da p) → ℕ) : pdMulti α (List.finRange _) ((Ξ.amp Y p).amp s) v = 0 := by
  have hu₀t : Ξ.facePt Y p s v ∈ (Y.φ p.1).target := Ξ.facePt_mem_target Y p s hv
  have hu₀V : Ξ.facePt Y p s v ∈ Y.T.V p.1 := (Y.V_eq p.1) ▸ hu₀t
  have hcontψ : ContinuousAt (Y.T.ψ p.1) (Ξ.facePt Y p s v) :=
    ((Y.T.ψ_analytic p.1).continuousOn).continuousAt ((Y.T.V_open p.1).mem_nhds hu₀V)
  have hψQ : Y.T.ψ p.1 (Ξ.facePt Y p s v) = Ξ.R.gv (Ξ.divPt Y p s v) := Y.ψ_eq p.1 _ hu₀t
  have h1 : ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Ξ.Gloc Y p.1 u = 0 := by
    have h2 : ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Y.T.ψ p.1 u ∉ tsupport Ξ.prior :=
      hcontψ.eventually_mem ((isClosed_tsupport Ξ.prior).isOpen_compl.mem_nhds
        (by rw [hψQ]; exact hsupp))
    filter_upwards [h2] with u hu
    have hpr : (Ξ.X Y).prior ((Ξ.X Y).T.ψ p.1 u) = 0 := image_eq_zero_of_notMem_tsupport hu
    unfold Gloc BridgeInputs.ρloc
    rw [hpr]
    simp
  obtain ⟨N, hN, hNo, hu₀N⟩ := mem_nhds_iff.1 h1
  have hO : IsOpen ((Ξ.facePt Y p s) ⁻¹' N) := hNo.preimage (Ξ.continuous_facePt Y p s)
  refine pdMulti_eq_zero_of_eqOn_inter_closedBox ((Ξ.amp Y p).smooth s) (Y.T.a_pos p.1) hO
    (fun w hw => ?_) ⟨hu₀N, hv⟩ α
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hw.2)]
  exact hN hw.1

/-- ★★ **Zero order or vanishing jets**: under the zero-order condition, a face of size `c` all of
whose walls resonate exactly has resonant Taylor order `0` and its face point is a divisor point of
the exact stratum, or the face point lies off the prior support and all amplitude jets vanish. -/
theorem stratum_or_jets_zero {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJc : J.card = c)
    (hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA p i : ℝ) * μ =
      resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i + (Ξ.X Y).hA p i + 1)
    {w : {i // ¬ inJ J i} → ℝ} (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    (Ξ.divPt Y p s (glue J 0 w) ∈ Ξ.exactStratum μ c ∧
        resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J = 0) ∨
      ∀ α, pdMulti α (List.finRange _) ((Ξ.amp Y p).amp s) (glue J 0 w) = 0 := by
  have hv : glue J 0 w ∈ closedBox _ (Y.T.a p.1) := Ξ.glue_zero_mem_closedBox Y p J hw
  have hJ : ∀ i, glue J 0 w i = 0 ↔ i ∈ J := Ξ.glue_zero_eq_zero_iff Y p J hw
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  by_cases hsupp : Ξ.R.gv (Ξ.divPt Y p s (glue J 0 w)) ∈ tsupport Ξ.prior
  · left
    have hres : ∀ i ∈ J, Resonates μ ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i) := fun i hi =>
      ⟨resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i, by
        have := hex i hi
        simp only
        linarith⟩
    have hmem : Ξ.divPt Y p s (glue J 0 w) ∈ Ξ.exactStratum μ c :=
      ⟨⟨hsupp, Ξ.phase_divPt_eq_zero Y p s hv hJne fun i hi => (hJ i).2 hi⟩,
        by rw [Ξ.depth_divPt_eq Y p s hv hJ, hJc],
        by rw [Ξ.resonanceCount_divPt_eq Y p s hv hJ hres, hJc]⟩
    refine ⟨hmem, ?_⟩
    funext i
    rw [Pi.zero_apply]
    by_cases hi : i ∈ J
    · have hpair : ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i) ∈
          pairs Ξ.R Ξ.hK0 (Ξ.divPt Y p s (glue J 0 w)) := by
        rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
          Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv, Ξ.wallsAt_facePt_eq Y p s hJ, Finset.map_val,
          Multiset.map_map]
        exact Multiset.mem_map.2 ⟨i, by rw [Finset.mem_val]; exact hi, rfl⟩
      have h1 := hzero _ hmem _ hpair
      have h2 := hex i hi
      simp only at h1
      have : (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i : ℝ) = 0 := by linarith
      exact_mod_cast this
    · exact resOrder_of_not_mem hi
  · right
    exact Ξ.pdMulti_amp_eq_zero_of_not_mem_tsupport Y p s hv hsupp

/-! ### Positivity -/

theorem amp_nonneg_of_nonneg (hF0 : ∀ P, 0 ≤ Ξ.F P) (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) : 0 ≤ (Ξ.amp Y p).amp s v := by
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hv)]
  unfold Gloc
  refine mul_nonneg ?_ (hF0 _)
  rw [← (Ξ.X Y).ρf_eq p.1 (Ξ.facePt_mem_box Y p s hv)]
  exact (Ξ.X Y).ρf_nonneg p.1 _

theorem pieceStratumSum_nonneg {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF0 : ∀ P, 0 ≤ Ξ.F P) (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
    0 ≤ Ξ.pieceStratumSum Y I s μ c := by
  unfold pieceStratumSum
  simp only [Ξ.chart_k Y, Ξ.chart_h Y, Ξ.chart_b Y, Ξ.chart_βf Y, Ξ.chart_amp Y]
  refine Finset.sum_nonneg fun J hJ => ?_
  have hJc : J.card = c := (mem_filter.1 hJ).2
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
  refine mul_nonneg (faceW_nonneg _ _) ?_
  by_cases hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ =
      resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
        (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1
  · refine mul_nonneg ?_ ?_
    · rw [← hDJ]
      exact (faceCoef_top_pos _ ((Ξ.X Y).kA_pos _) (Y.T.phaseConst_pos _) (Y.T.a_pos _) J hJne _
        fun j hj => by push_cast; exact hex j hj).le
    · unfold faceCoeffInt
      refine setIntegral_nonneg (measurableSet_box _) fun w hw => ?_
      rcases Ξ.stratum_or_jets_zero Y hc hzero ((Ξ.X Y).en I) s hJc hex hw with ⟨-, h0⟩ | hjets
      · rw [h0, pdMulti_zero, pow_zero, mul_one]
        exact mul_nonneg (mul_nonneg (Ξ.amp_nonneg_of_nonneg Y hF0 _ s
          (Ξ.glue_zero_mem_closedBox Y _ J hw)) (mono_nonneg_of_mem_box hw _))
          (Real.rpow_nonneg (mono_nonneg_of_mem_box hw _) _)
      · rw [pdMulti_lJ_eq_finRange_of_zero_off ((Ξ.amp Y _).smooth s) J _
          fun i hi => resOrder_of_not_mem hi]
        beta_reduce
        rw [hjets, zero_mul, zero_mul, zero_mul]
  · obtain ⟨i, hi, hne⟩ : ∃ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ ≠
        resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
          (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1 := by
      by_contra h
      exact hex fun i hi => by_contra fun hne => h ⟨i, hi, hne⟩
    rw [← hDJ, faceCoef_top_eq_zero_of_not_exact _ ((Ξ.X Y).kA_pos _) (Y.T.phaseConst_pos _)
      (Y.T.a_pos _) J _ hi (by push_cast; exact hne), zero_mul]

theorem stratumSum_nonneg {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF0 : ∀ P, 0 ≤ Ξ.F P) : 0 ≤ Ξ.stratumSum Y μ c :=
  Finset.sum_nonneg fun I _ => integral_nonneg fun s => Ξ.pieceStratumSum_nonneg Y hc hzero hF0 I s

/-- ★★★ **Positivity of the graded stratum functional**: under the zero-order condition, a
nonnegative observable vanishing near the deep zero fibre has nonnegative `(μ, c−1)`
coefficient. -/
theorem coeff_nonneg_of_deep {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (hF0 : ∀ P, 0 ≤ Ξ.F P) :
    0 ≤ Ξ.coeff Y μ (c - 1) := by
  rw [Ξ.coeff_eq_stratumSum Y hc hF μ]
  exact Ξ.stratumSum_nonneg Y hc hzero hF0

/-! ### Values-only dependence -/

theorem pieceStratumSum_eq_zero_of_eqOn_zero {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) (hF0 : ∀ P ∈ Ξ.exactStratum μ c, Ξ.F P = 0)
    (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
    Ξ.pieceStratumSum Y I s μ c = 0 := by
  unfold pieceStratumSum
  simp only [Ξ.chart_k Y, Ξ.chart_h Y, Ξ.chart_b Y, Ξ.chart_βf Y, Ξ.chart_amp Y]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJc : J.card = c := (mem_filter.1 hJ).2
  have hDJ : DJ J = c - 1 := by rw [DJ_eq, hJc]
  by_cases hex : ∀ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ =
      resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
        (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1
  · rw [faceCoeffInt_eq_zero_of_forall _ _ _ _ _ fun w hw => ?_, mul_zero, mul_zero]
    rcases Ξ.stratum_or_jets_zero Y hc hzero ((Ξ.X Y).en I) s hJc hex hw with ⟨hmem, h0⟩ | hjets
    · have hv := Ξ.glue_zero_mem_closedBox Y ((Ξ.X Y).en I) J hw
      rw [h0, pdMulti_zero, Ξ.amp_apply, Ξ.G_eq Y _ (Ξ.facePt_mem_box Y _ s hv)]
      unfold Gloc
      rw [Y.chartInv_eq _ (Ξ.facePt_mem_target Y _ s hv)]
      change (Ξ.X Y).ρloc _ _ * Ξ.F (Ξ.divPt Y ((Ξ.X Y).en I) s (glue J 0 w)) = 0
      rw [hF0 _ hmem, mul_zero]
    · rw [pdMulti_lJ_eq_finRange_of_zero_off ((Ξ.amp Y _).smooth s) J _
        fun i hi => resOrder_of_not_mem hi]
      rw [hjets]
  · obtain ⟨i, hi, hne⟩ : ∃ i ∈ J, 2 * ((Ξ.X Y).kA ((Ξ.X Y).en I) i : ℝ) * μ ≠
        resOrder ((Ξ.X Y).hA ((Ξ.X Y).en I)) ((Ξ.X Y).kA ((Ξ.X Y).en I)) μ J i +
          (Ξ.X Y).hA ((Ξ.X Y).en I) i + 1 := by
      by_contra h
      exact hex fun i hi => by_contra fun hne => h ⟨i, hi, hne⟩
    rw [← hDJ, faceCoef_top_eq_zero_of_not_exact _ ((Ξ.X Y).kA_pos _) (Y.T.phaseConst_pos _)
      (Y.T.a_pos _) J _ hi (by push_cast; exact hne), zero_mul, mul_zero]

theorem stratumSum_eq_zero_of_eqOn_zero {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF0 : ∀ P ∈ Ξ.exactStratum μ c, Ξ.F P = 0) : Ξ.stratumSum Y μ c = 0 :=
  Finset.sum_eq_zero fun I _ => integral_eq_zero_of_ae (Eventually.of_forall fun s =>
    Ξ.pieceStratumSum_eq_zero_of_eqOn_zero Y hc hzero hF0 I s)

/-- Under the zero-order condition, an observable vanishing near the deep zero fibre and on the
exact stratum has vanishing `(μ, c−1)` coefficient. -/
theorem coeff_eq_zero_of_eqOn_zero_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (hF0 : ∀ P ∈ Ξ.exactStratum μ c, Ξ.F P = 0) : Ξ.coeff Y μ (c - 1) = 0 := by
  rw [Ξ.coeff_eq_stratumSum Y hc hF μ]
  exact Ξ.stratumSum_eq_zero_of_eqOn_zero Y hc hzero hF0

/-- ★★★ **Values-only dependence on the exact stratum**: under the zero-order condition, two
observables vanishing near the deep zero fibre and agreeing on the exact stratum `S^μ_c` have the
same `(μ, c−1)` coefficient. -/
theorem coeff_eq_of_eqOn_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0) (heq : EqOn G G' (Ξ.exactStratum μ c)) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hev : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P + (-1 : ℝ) * G' P = 0 := by
    filter_upwards [hG0, hG0'] with P h1 h2
    rw [h1, h2]
    ring
  have hzero' : (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).ZeroOrder μ c := hzero
  have hdiff := (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P)
    hsum).coeff_eq_zero_of_eqOn_zero_exactStratum Y hc hzero' hev fun P hP => by
      change G P + (-1 : ℝ) * G' P = 0
      rw [heq hP]
      ring
  have h1 := Ξ.coeff_add Y hG hG'' μ (c - 1)
  have h2 := Ξ.coeff_smul Y hG' (-1) μ (c - 1)
  linarith

end ResolvedData

end SmoothEngine

end Grammar
