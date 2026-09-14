/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedCoefficient
import Grammar.ResolvedDepthLocal

/-!
# Resonant faces of the resolved decomposition: the chart amplitudes vanish there

Consult #127, Unit D6b (geometric half). Fix resolved data `Ξ` and a resolved core transport `Y`.
The resolved expansion is assembled from the pieces `p` (a resolution chart and an orthant): the
engine expands the chart amplitude `G_p(T_p(s, v))` (`ρ · F ∘ φ_p⁻¹` extended smoothly off the
box) in the active coordinates `v ∈ [0, a]^{d_p}`. A **face** `J` of the active box is the
coordinate subspace `{v_i = 0 : i ∈ J}`; its points are carried by the chart to the divisor
points `Q = φ_p⁻¹(T_p(s, v))` whose intrinsic pair data contain the pairs `(k_i, h_i)`, `i ∈ J`
(the local coordinate formula of CDXXXI in the even chart box of the piece). Hence:

* `resonanceCount_ge_face`: the resonance count of such a `Q` is at least the number of
  resonant coordinates of the face;
* if the observable `F` vanishes on a neighbourhood of the **resonant zero fibre**
  `Z₀ ∩ {r_μ ≥ q + 1}` (`resonantZeroFibre`), then near every point of a face with at least
  `q + 1` resonant coordinates the chart amplitude vanishes — either because `F` vanishes near
  the corresponding divisor point, or because that point lies off the support of the prior so the
  transported density vanishes (`Gloc_eventually_zero`);
* consequently every coordinate derivative of the amplitude family vanishes on such faces
  (`pdMulti_amp_eq_zero_on_face`; the jets at the boundary of the closed box are limits of the
  jets at interior points, `pdMulti_eq_zero_of_eqOn_inter_closedBox`).

This is the input that, combined with the engine's resonant-support lemma (Unit D6a), gives
`𝒯^U_{μ,q}[F] = 0` for such `F` — the support of the resolved coefficient functional in the
resonant locus `{r_μ ≥ q+1}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Jets at the boundary of the closed box -/

theorem pd_zero_fun' (i : Fin d) : pd i (0 : (Fin d → ℝ) → ℝ) = 0 := by
  funext v
  unfold pd line
  simp only [Pi.zero_apply, deriv_const]

theorem pdPow_zero_fun (i : Fin d) (m : ℕ) : pdPow i m (0 : (Fin d → ℝ) → ℝ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold pdPow at ih ⊢
    rw [Function.iterate_succ_apply', ih, pd_zero_fun']

theorem pdMulti_zero_fun (α : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti α l (0 : (Fin d → ℝ) → ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [pdMulti_cons, ih, pdPow_zero_fun]

/-- The interior of the closed box is the open box. -/
theorem interior_closedBox {b : ℝ} :
    interior (closedBox d b) = Set.pi univ fun _ => Ioo 0 b := by
  unfold closedBox
  rw [interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

/-- Every point of the closed box is a limit of interior points along the segment to the centre.
-/
theorem mem_closure_inter_interior_closedBox {b : ℝ} (hb : 0 < b) {O : Set (Fin d → ℝ)}
    (hO : IsOpen O) {v₀ : Fin d → ℝ} (hv₀ : v₀ ∈ O ∩ closedBox d b) :
    v₀ ∈ closure (O ∩ interior (closedBox d b)) := by
  set c : Fin d → ℝ := fun _ => b / 2 with hc
  set u : ℕ → Fin d → ℝ := fun m => v₀ + (1 / ((m : ℝ) + 1)) • (c - v₀) with hu
  have hlim : Tendsto u atTop (𝓝 v₀) := by
    have h1 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1)) • (c - v₀)) atTop
        (𝓝 ((0 : ℝ) • (c - v₀))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _
    rw [zero_smul] at h1
    have h2 := tendsto_const_nhds (x := v₀) |>.add h1
    rwa [add_zero] at h2
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [hlim.eventually (hO.mem_nhds hv₀.1)] with m hm
  refine ⟨hm, ?_⟩
  rw [interior_closedBox, Set.mem_univ_pi]
  intro i
  have hvi : v₀ i ∈ Icc 0 b := (mem_closedBox.1 hv₀.2) i
  have ht0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have ht1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  simp only [hu, hc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mem_Ioo]
  constructor <;> nlinarith [hvi.1, hvi.2]

/-- **Jets at the boundary**: a smooth function vanishing on `O ∩ [0,b]^d` (`O` open) has all its
coordinate derivatives vanishing at every point of `O ∩ [0,b]^d`, including boundary points. -/
theorem pdMulti_eq_zero_of_eqOn_inter_closedBox {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    {b : ℝ} (hb : 0 < b) {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    (h0 : ∀ v ∈ O ∩ closedBox d b, F v = 0) {v₀ : Fin d → ℝ} (hv₀ : v₀ ∈ O ∩ closedBox d b)
    (α : Fin d → ℕ) : pdMulti α (List.finRange d) F v₀ = 0 := by
  have hopen : IsOpen (O ∩ interior (closedBox d b)) := hO.inter isOpen_interior
  have hzero : EqOn F 0 (O ∩ interior (closedBox d b)) := fun v hv =>
    h0 v ⟨hv.1, interior_subset hv.2⟩
  have hjets : EqOn (pdMulti α (List.finRange d) F) (pdMulti α (List.finRange d) 0)
      (O ∩ interior (closedBox d b)) := pdMulti_eqOn_of_isOpen hopen hzero α _
  rw [pdMulti_zero_fun] at hjets
  have hcl := hjets.closure (contDiff_pdMulti hF α _).continuous continuous_const
  exact hcl (mem_closure_inter_interior_closedBox hb hO hv₀)

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resonant zero fibre `Z₀ ∩ {r_μ ≥ q + 1}`. -/
def resonantZeroFibre (μ : ℝ) (q : ℕ) : Set Ξ.R.U :=
  Ξ.zeroFibre ∩ resonanceGE Ξ.R Ξ.hK0 μ (q + 1)

theorem isCompact_resonantZeroFibre (μ : ℝ) (q : ℕ) : IsCompact (Ξ.resonantZeroFibre μ q) :=
  Ξ.isCompact_zeroFibre.inter_right (isClosed_resonanceGE Ξ.R Ξ.hK0 Ξ.hKc μ (q + 1))

/-! ### Face points of a piece and their divisor points -/

/-- The chart point of a piece face point. -/
noncomputable def facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Fin d → ℝ := (Ξ.X Y).Tm p s v

/-- The divisor point of a piece face point. -/
noncomputable def divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Ξ.R.U := (Y.φ p.1).symm (Ξ.facePt Y p s v)

theorem facePt_mem_box (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.facePt Y p s v ∈ centeredBox d (Y.T.a p.1) :=
  (Ξ.X Y).Tm_mem_box p s fun j => (mem_closedBox.1 hv) j

theorem facePt_mem_target (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.facePt Y p s v ∈ (Y.φ p.1).target :=
  Y.box_subset_target p.1 (Ξ.facePt_mem_box Y p s hv)

theorem divPt_mem_source (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.divPt Y p s v ∈ (Y.φ p.1).source :=
  (Y.φ p.1).map_target (Ξ.facePt_mem_target Y p s hv)

theorem φ_divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Y.φ p.1 (Ξ.divPt Y p s v) = Ξ.facePt Y p s v :=
  (Y.φ p.1).right_inv (Ξ.facePt_mem_target Y p s hv)

/-- On a face `{v_i = 0 : i ∈ J}` the corresponding active chart coordinates vanish. -/
theorem facePt_apply_eq_zero (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} {i : Fin ((Ξ.X Y).da p)} (hi : v i = 0) :
    Ξ.facePt Y p s v ((Ξ.X Y).eqv p i).1 = 0 := by
  unfold facePt BridgeInputs.Tm
  rw [affineMap_apply_face, hi, mul_zero]

/-- The active coordinates of the piece are the active coordinates of its even chart box. -/
theorem mem_active_evenChartBox (p : (Ξ.X Y).PIdx) (i : Fin ((Ξ.X Y).da p)) :
    ((Ξ.X Y).eqv p i).1 ∈ active (Y.evenChartBox p.1) :=
  (mem_active _).2 ((Ξ.X Y).mem_act.1 ((Ξ.X Y).eqv p i).2)

/-- The face coordinates `J` embed into the walls through the divisor point. -/
theorem map_subset_wallsAt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (J : Finset (Fin ((Ξ.X Y).da p))) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hvJ : ∀ i ∈ J, v i = 0) :
    J.map ⟨fun i => ((Ξ.X Y).eqv p i).1, fun _ _ h =>
      (Ξ.X Y).eqv p |>.injective (Subtype.ext h)⟩ ⊆
      wallsAt (Y.evenChartBox p.1) (Ξ.facePt Y p s v) := by
  intro j hj
  rw [Finset.mem_map] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact Finset.mem_filter.2
    ⟨Ξ.mem_active_evenChartBox Y p i, Ξ.facePt_apply_eq_zero Y p s (hvJ i hi)⟩

open Classical in
/-- The number of resonant coordinates of a face of the piece. -/
noncomputable def faceResonant (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) (μ : ℝ) :
    ℕ :=
  ((J.val.map fun i => ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i)).filter (Resonates μ)).card

open Classical in
/-- ★★ **The resonance count at a face point** is at least the number of resonant coordinates of
the face. -/
theorem faceResonant_le_resonanceCount (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (J : Finset (Fin ((Ξ.X Y).da p)))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) (hvJ : ∀ i ∈ J, v i = 0)
    (μ : ℝ) :
    Ξ.faceResonant Y p J μ ≤ resonanceCount Ξ.R Ξ.hK0 μ (Ξ.divPt Y p s v) := by
  unfold resonanceCount
  rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s hv),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s hv]
  set e : Fin ((Ξ.X Y).da p) ↪ Fin d := ⟨fun i => ((Ξ.X Y).eqv p i).1, fun _ _ h =>
    (Ξ.X Y).eqv p |>.injective (Subtype.ext h)⟩ with he
  have hsub := Ξ.map_subset_wallsAt Y p s J hvJ
  calc Ξ.faceResonant Y p J μ
      = (((J.map e).val.map fun j => ((Y.evenChartBox p.1).k j, (Y.evenChartBox p.1).h j)).filter
          (Resonates μ)).card := by
        rw [Finset.map_val, Multiset.map_map]
        rfl
    _ ≤ _ := Multiset.card_le_card (Multiset.filter_le_filter _
        (Multiset.map_le_map (Finset.val_le_iff.2 hsub)))

/-! ### The chart amplitude vanishes near resonant face points -/

theorem continuousAt_symm_facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    ContinuousAt (Y.φ p.1).symm (Ξ.facePt Y p s v) :=
  (Y.φ p.1).continuousOn_symm.continuousAt
    ((Y.φ p.1).open_target.mem_nhds (Ξ.facePt_mem_target Y p s hv))

theorem chartInv_eventuallyEq_symm (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Y.chartInv p.1 =ᶠ[𝓝 (Ξ.facePt Y p s v)] (Y.φ p.1).symm :=
  eventually_of_mem ((Y.φ p.1).open_target.mem_nhds (Ξ.facePt_mem_target Y p s hv))
    fun _ hu => Y.chartInv_eq p.1 hu

/-- ★★ **The local amplitude vanishes near a resonant face point**: if `F` vanishes on a
neighbourhood of the resonant zero fibre, then near the chart point of a face with at least
`q + 1` resonant coordinates the local amplitude `ρ · F ∘ φ⁻¹` vanishes (either `F` vanishes
near the divisor point, or the divisor point lies off the prior support and the density
vanishes). -/
theorem Gloc_eventually_zero {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (J : Finset (Fin ((Ξ.X Y).da p)))
    (hJ : q + 1 ≤ Ξ.faceResonant Y p J μ) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) (hvJ : ∀ i ∈ J, v i = 0) :
    ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Ξ.Gloc Y p.1 u = 0 := by
  have hu₀t : Ξ.facePt Y p s v ∈ (Y.φ p.1).target := Ξ.facePt_mem_target Y p s hv
  have hu₀V : Ξ.facePt Y p s v ∈ Y.T.V p.1 := (Y.V_eq p.1) ▸ hu₀t
  -- the chart point is a wall point: the phase vanishes there
  have hJne : J.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hJ
    simp [faceResonant] at hJ
  have hK0 : Ξ.K (Ξ.R.gv (Ξ.divPt Y p s v)) = 0 := by
    obtain ⟨i, hi⟩ := hJne
    have hψ : Y.T.ψ p.1 (Ξ.facePt Y p s v) = Ξ.R.gv (Ξ.divPt Y p s v) :=
      Y.ψ_eq p.1 _ hu₀t
    rw [← hψ, Y.T.phase_eq p.1 _ hu₀V]
    refine mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ ((Ξ.X Y).eqv p i).1) ?_))
    rw [Ξ.facePt_apply_eq_zero Y p s (hvJ i hi)]
    exact zero_pow (mul_ne_zero two_ne_zero (Nat.pos_iff_ne_zero.1 ((Ξ.X Y).kA_pos p i)))
  by_cases hsupp : Ξ.R.gv (Ξ.divPt Y p s v) ∈ tsupport Ξ.prior
  · -- the divisor point lies in the resonant zero fibre: `F` vanishes near it
    have hQmem : Ξ.divPt Y p s v ∈ Ξ.resonantZeroFibre μ q :=
      ⟨⟨hsupp, hK0⟩, hJ.trans (Ξ.faceResonant_le_resonanceCount Y p s J hv hvJ μ)⟩
    have hFQ : ∀ᶠ P in 𝓝 (Ξ.divPt Y p s v), Ξ.F P = 0 :=
      eventually_nhdsSet_iff_forall.1 hF _ hQmem
    have hcont := Ξ.continuousAt_symm_facePt Y p s hv
    have h1 : ∀ᶠ u in 𝓝 (Ξ.facePt Y p s v), Ξ.F ((Y.φ p.1).symm u) = 0 := hcont.eventually hFQ
    filter_upwards [h1, Ξ.chartInv_eventuallyEq_symm Y p s hv] with u hu hci
    unfold Gloc
    rw [hci, hu, mul_zero]
  · -- the divisor point lies off the prior support: the density vanishes near the chart point
    have hcontψ : ContinuousAt (Y.T.ψ p.1) (Ξ.facePt Y p s v) :=
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

/-- The amplitude family of a piece, evaluated at a base point, is the extended amplitude along
the chart coordinate. -/
theorem amp_apply (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : (Ξ.amp Y p).amp s v = Ξ.G Y p.1 (Ξ.facePt Y p s v) := rfl

theorem continuous_facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    Continuous (Ξ.facePt Y p s) :=
  ((Ξ.X Y).continuous_Tm p).comp (Continuous.prodMk_right s)

/-- ★★★ **Vanishing of the amplitude jets on resonant faces**: every coordinate derivative of the
piece amplitude vanishes on the closed face `{v ∈ [0,a]^{d_p} : v_i = 0, i ∈ J}` whenever the face
has at least `q + 1` resonant coordinates and `F` vanishes near the resonant zero fibre. -/
theorem pdMulti_amp_eq_zero_on_face {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) (p : (Ξ.X Y).PIdx)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (J : Finset (Fin ((Ξ.X Y).da p)))
    (hJ : q + 1 ≤ Ξ.faceResonant Y p J μ) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) (hvJ : ∀ i ∈ J, v i = 0) (α : Fin ((Ξ.X Y).da p) → ℕ) :
    pdMulti α (List.finRange _) ((Ξ.amp Y p).amp s) v = 0 := by
  obtain ⟨N, hN, hNo, hu₀N⟩ := mem_nhds_iff.1 (Ξ.Gloc_eventually_zero Y hF p s J hJ hv hvJ)
  have hO : IsOpen ((Ξ.facePt Y p s) ⁻¹' N) := hNo.preimage (Ξ.continuous_facePt Y p s)
  refine pdMulti_eq_zero_of_eqOn_inter_closedBox ((Ξ.amp Y p).smooth s) (Y.T.a_pos p.1) hO
    (fun w hw => ?_) ⟨hu₀N, hv⟩ α
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hw.2)]
  exact hN hw.1

end ResolvedData

end SmoothEngine

end Grammar
