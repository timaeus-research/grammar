/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceSumCollapse
import Grammar.SmoothResolvedResonantSupport

/-!
# The graded stratum formula on the resolved manifold

Consult #130, Unit E2. Let `D_{c+1} = Z₀ ∩ {depth ≥ c+1}` be the DEEP ZERO FIBRE
(`deepZeroFibre`, compact). For an observable `F` vanishing on a neighbourhood of `D_{c+1}`
(the class `𝓘_{c+1}`), the resolved coefficient at the top logarithmic power `(μ, c − 1)` is the
STRATUM SUM (★★★ `coeff_eq_stratumSum`): over the pieces of the resolved core transport and the
base points, the sum over the faces `J` of size `c` of the piece box of
`faceW · faceCoef · ∫_{face} ∂_J^{α_J}(amplitude) · (power weight)` (`pieceStratumSum`,
`stratumSum`) — the engine collapse (CDXLVI) applied piecewise, since the amplitude jets vanish on
the deep set of every piece box (`jetsZeroOn_amp_deep`: near a face point with `≥ c+1` vanishing
coordinates the divisor point has depth `≥ c+1`, so either `F` vanishes near it or it lies off the
prior support). The geometric reading (`depth_divPt_eq`, `resonanceCount_divPt_eq`): a face point
with exactly the `J`-coordinates zero is a divisor point of depth exactly `|J| = c`, and when every
face wall resonates with `μ` its resonance count is `c` — the face integrals are integrals over the
exact stratum `{depth = c, r_μ = c}`. The total is intrinsic (it equals `𝒯^U_{μ,c−1}[F]`), and
descends to `𝓘_{c+1}/𝓘_c` (`coeff_eq_zero_of_deep` for `q ≥ c`, CDXXXV). Non-claims: the
individual chart-piece integrals are not asserted to be canonical; integrability of the face
integrand is a separate statement. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The deep zero fibre `D_{c+1} = Z₀ ∩ {depth ≥ c + 1}`. -/
def deepZeroFibre (c : ℕ) : Set Ξ.R.U := Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (c + 1)

theorem isCompact_deepZeroFibre (c : ℕ) : IsCompact (Ξ.deepZeroFibre c) :=
  Ξ.isCompact_zeroFibre.inter_right (isClosed_depthGE Ξ.R Ξ.hK0 Ξ.hKc (c + 1))

/-- Observables vanishing near the deep zero fibre have no coefficients of log power `≥ c`. -/
theorem coeff_eq_zero_of_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {q : ℕ}
    (hq : c ≤ q) (μ : ℝ) : Ξ.coeff Y μ q = 0 :=
  Ξ.coeff_eq_zero_of_eventually_zero_depth Y
    (hF.filter_mono (nhdsSet_mono (inter_subset_inter_right _ (depthGE_antitone Ξ.R Ξ.hK0
      (by omega)))))

/-- The depth of the divisor point of a face is at least the size of the face. -/
theorem card_le_depth_divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (J : Finset (Fin ((Ξ.X Y).da p))) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) (hvJ : ∀ i ∈ J, v i = 0) :
    J.card ≤ depth Ξ.R Ξ.hK0 (Ξ.divPt Y p s v) := by
  rw [depth_eq_card_wallsAt Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv]
  calc J.card = (J.map ⟨fun i => ((Ξ.X Y).eqv p i).1, fun _ _ h =>
        (Ξ.X Y).eqv p |>.injective (Subtype.ext h)⟩).card := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card (Ξ.map_subset_wallsAt Y p s J hvJ)

/-- The local amplitude vanishes near a face point with at least `c + 1` vanishing coordinates
when `F` vanishes near the deep zero fibre. -/
theorem Gloc_eventually_zero_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (J : Finset (Fin ((Ξ.X Y).da p))) (hJ : c + 1 ≤ J.card) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) (hvJ : ∀ i ∈ J, v i = 0) :
    ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Ξ.Gloc Y p.1 u = 0 := by
  have hu₀t : Ξ.facePt Y p s v ∈ (Y.φ p.1).target := Ξ.facePt_mem_target Y p s hv
  have hu₀V : Ξ.facePt Y p s v ∈ Y.T.V p.1 := (Y.V_eq p.1) ▸ hu₀t
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hK0 : Ξ.K (Ξ.R.gv (Ξ.divPt Y p s v)) = 0 := by
    obtain ⟨i, hi⟩ := hJne
    have hψ : Y.T.ψ p.1 (Ξ.facePt Y p s v) = Ξ.R.gv (Ξ.divPt Y p s v) :=
      Y.ψ_eq p.1 _ hu₀t
    rw [← hψ, Y.T.phase_eq p.1 _ hu₀V]
    refine mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ ((Ξ.X Y).eqv p i).1) ?_))
    rw [Ξ.facePt_apply_eq_zero Y p s (hvJ i hi)]
    exact zero_pow (mul_ne_zero two_ne_zero (Nat.pos_iff_ne_zero.1 ((Ξ.X Y).kA_pos p i)))
  by_cases hsupp : Ξ.R.gv (Ξ.divPt Y p s v) ∈ tsupport Ξ.prior
  · have hQmem : Ξ.divPt Y p s v ∈ Ξ.deepZeroFibre c :=
      ⟨⟨hsupp, hK0⟩, hJ.trans (Ξ.card_le_depth_divPt Y p s J hv hvJ)⟩
    have hFQ : ∀ᶠ P in 𝓝 (Ξ.divPt Y p s v), Ξ.F P = 0 :=
      eventually_nhdsSet_iff_forall.1 hF _ hQmem
    have hcont := Ξ.continuousAt_symm_facePt Y p s hv
    have h1 : ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Ξ.F ((Y.φ p.1).symm u) = 0 := hcont.eventually hFQ
    filter_upwards [h1, Ξ.chartInv_eventuallyEq_symm Y p s hv] with u hu hci
    unfold Gloc
    rw [hci, hu, mul_zero]
  · have hcontψ : ContinuousAt (Y.T.ψ p.1) (Ξ.facePt Y p s v) :=
      ((Y.T.ψ_analytic p.1).continuousOn).continuousAt ((Y.T.V_open p.1).mem_nhds hu₀V)
    have hψQ : Y.T.ψ p.1 (Ξ.facePt Y p s v) = Ξ.R.gv (Ξ.divPt Y p s v) := Y.ψ_eq p.1 _ hu₀t
    have h1 : ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Y.T.ψ p.1 u ∉ tsupport Ξ.prior :=
      hcontψ.eventually_mem ((isClosed_tsupport Ξ.prior).isOpen_compl.mem_nhds
        (by rw [hψQ]; exact hsupp))
    filter_upwards [h1] with u hu
    have hpr : (Ξ.X Y).prior ((Ξ.X Y).T.ψ p.1 u) = 0 := image_eq_zero_of_notMem_tsupport hu
    unfold Gloc BridgeInputs.ρloc
    rw [hpr]
    simp

/-- ★★ **The amplitude jets vanish on the deep set of a piece box** when `F` vanishes near the
deep zero fibre. -/
theorem jetsZeroOn_amp_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    JetsZeroOn ((Ξ.amp Y p).amp s) (deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) := by
  intro α v hv
  obtain ⟨hvbox, hcard⟩ := hv
  have hvJ : ∀ i ∈ (univ : Finset (Fin ((Ξ.X Y).da p))).filter (fun i => v i = 0), v i = 0 :=
    fun i hi => (mem_filter.1 hi).2
  obtain ⟨N, hN, hNo, hu₀N⟩ :=
    mem_nhds_iff.1 (Ξ.Gloc_eventually_zero_deep Y hF p s _ hcard hvbox hvJ)
  have hO : IsOpen ((Ξ.facePt Y p s) ⁻¹' N) := hNo.preimage (Ξ.continuous_facePt Y p s)
  refine pdMulti_eq_zero_of_eqOn_inter_closedBox ((Ξ.amp Y p).smooth s) (Y.T.a_pos p.1) hO
    (fun w hw => ?_) ⟨hu₀N, hvbox⟩ α
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hw.2)]
  exact hN hw.1

/-! ### The stratum sum -/

/-- The stratum term of a piece at a base point: the sum over the faces of size `c` of the piece
box of `faceW · faceCoef · ∫_{face} ∂_J^{α_J}(amplitude) · (power weight)`. -/
noncomputable def pieceStratumSum (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin ((Ξ.X Y).da ((Ξ.X Y).en I))))).filter (fun J => J.card = c),
    faceW J (resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k μ J) *
      (faceCoef ((Ξ.decomp Y).chart I).k (((Ξ.decomp Y).chart I).βf s) ((Ξ.decomp Y).chart I).b J
          (fun i => resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k μ J i +
            ((Ξ.decomp Y).chart I).h i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k
            μ J) (lJ J) (((Ξ.decomp Y).chart I).amp.amp s) (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => ((Ξ.decomp Y).chart I).h i)
          (fun i => 2 * ((Ξ.decomp Y).chart I).k i) ((Ξ.decomp Y).chart I).b μ 0)

/-- The stratum sum: the piece stratum terms integrated over the bases and summed over the
pieces. -/
noncomputable def stratumSum (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ I, ∫ s, Ξ.pieceStratumSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν

/-- ★★★ **The graded stratum formula**: for an observable vanishing near the deep zero fibre
`Z₀ ∩ {depth ≥ c+1}`, the coefficient at `(μ, c − 1)` is the stratum sum. -/
theorem coeff_eq_stratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (μ : ℝ) :
    Ξ.coeff Y μ (c - 1) = Ξ.stratumSum Y μ c := by
  unfold coeff SmoothCoreDecomposition.coeff stratumSum
  refine Finset.sum_congr rfl fun I _ => ?_
  unfold familyCoeff
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact smoothCoeff_eq_faceSum_top (((Ξ.decomp Y).chart I).amp.smooth s) _ _
    ((Ξ.decomp Y).chart I).k_pos (((Ξ.decomp Y).chart I).β_pos s) ((Ξ.decomp Y).chart I).b_pos μ
    hc (Ξ.jetsZeroOn_amp_deep Y hF ((Ξ.X Y).en I) s)

/-! ### The exact stratum of a face -/

/-- The walls through the chart point of a face with exactly the `J`-coordinates zero are the
`J`-coordinates. -/
theorem wallsAt_facePt_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} {J : Finset (Fin ((Ξ.X Y).da p))}
    (hJ : ∀ i, v i = 0 ↔ i ∈ J) :
    wallsAt (Y.evenChartBox p.1) (Ξ.facePt Y p s v) =
      J.map ⟨fun i => ((Ξ.X Y).eqv p i).1, fun _ _ h =>
        (Ξ.X Y).eqv p |>.injective (Subtype.ext h)⟩ := by
  refine le_antisymm (fun j hj => ?_) (Ξ.map_subset_wallsAt Y p s J fun i hi => (hJ i).2 hi)
  rw [wallsAt, mem_filter] at hj
  obtain ⟨hact, hzero⟩ := hj
  have hj' : j ∈ (Ξ.X Y).act p.1 := by
    rw [(Ξ.X Y).mem_act]
    exact (mem_active _).1 hact
  set i : Fin ((Ξ.X Y).da p) := ((Ξ.X Y).eqv p).symm ⟨j, hj'⟩ with hi
  have hfp : Ξ.facePt Y p s v j = WaterFilling.sgn p.2 j * v i := by
    unfold facePt BridgeInputs.Tm
    exact affineMap_apply_of_mem _ _ _ v hj'
  rw [hfp] at hzero
  have hvi : v i = 0 := by
    rcases mul_eq_zero.1 hzero with h0 | h0
    · exact absurd h0 (WaterFilling.sgn_ne_zero p.2 j)
    · exact h0
  refine Finset.mem_map.2 ⟨i, (hJ i).1 hvi, ?_⟩
  change (((Ξ.X Y).eqv p) (((Ξ.X Y).eqv p).symm ⟨j, hj'⟩)).1 = j
  rw [Equiv.apply_symm_apply]

/-- ★★ **The divisor point of a face with exactly the `J`-coordinates zero has depth `|J|`.** -/
theorem depth_divPt_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : ∀ i, v i = 0 ↔ i ∈ J) :
    depth Ξ.R Ξ.hK0 (Ξ.divPt Y p s v) = J.card := by
  rw [depth_eq_card_wallsAt Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv, Ξ.wallsAt_facePt_eq Y p s hJ, Finset.card_map]

open Classical in
/-- ★★ **The resonance count of a face point all of whose walls resonate is `|J|`.** -/
theorem resonanceCount_divPt_eq (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1))
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : ∀ i, v i = 0 ↔ i ∈ J) {μ : ℝ}
    (hres : ∀ i ∈ J, Resonates μ ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i)) :
    resonanceCount Ξ.R Ξ.hK0 μ (Ξ.divPt Y p s v) = J.card := by
  unfold resonanceCount
  rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv, Ξ.wallsAt_facePt_eq Y p s hJ, Finset.map_val,
    Multiset.map_map, Multiset.filter_eq_self.2 ?_, Multiset.card_map, Finset.card_val]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
  rw [Finset.mem_val] at hi
  exact hres i hi

end ResolvedData

end SmoothEngine

end Grammar
