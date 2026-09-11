/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularBridge

/-!
# The lifted foot from strucdual's analytic tube (local, unconditional)

`TubularBridge` proves the tubular equivalence `Ψ (x, n) = emb x + n` between the frame-built
normal bundle and a certified tube, *conditional* on a `LiftedFoot`: a smooth injective
parametrisation `emb` of the stratum together with a smooth left inverse `P` along the tube. This
file discharges that hypothesis, locally, for every compact analytic LCI stratum, with no
hypotheses beyond strucdual's atlas:

* `restrictTube` — a normal tubular chart restricts to any open piece `S ∩ V'` of its base (the
  tube becomes `U ∩ proj⁻¹ V'`; all fields inherit, membership through uniqueness).
* `TangentGraphChart` / `exists_tangentGraphChart` — near `s ∈ S ∩ V_i`, the stratum is the
  graph of a smooth map over an open piece `W` of the tangent space `T_s = ker J_i(s)`: the
  analytic inverse function theorem for `F x = (G_i x, π_T (x − s))` (whose derivative at `s`
  is `J_i(s) ⊕ π_T`, injective by `ker J_i(s) = T_s` and bijective by the rank count) gives
  `emb z = F⁻¹(0, z)` with left inverse `ft x = π_T (x − s)` on `S ∩ V'`.
* `rowFrame` / `rowCoframe` — the Jacobian rows `c ↦ J_i(x)ᵀ c` frame the normal space
  (`range_rowFrame`), with the Gram left inverse `(J Jᵀ)⁻¹ J`; both are `C^∞` in `x`
  (`contDiffAt_rowFrame`, `contDiffAt_rowCoframe`, through `fderiv` of the analytic `G_i`,
  transposition as a continuous linear operator on operators, and smoothness of inversion at an
  invertible operator).
* `graphFrameData` — the resulting frame–coframe atlas over the base manifold `↥W` (an open
  subset of the normed space `T_s`, charted by `Opens.instChartedSpace`), and
  `liftedFoot_graph` — the `LiftedFoot` for the restricted tube.
* `exists_liftedFoot_of_compact` / `exists_local_tubular_equivalence` /
  `exists_local_tubular_equivalence_analytic` — the headline: for a compact analytic LCI stratum
  and any `s ∈ S`, strucdual's analytic tube restricted to a neighbourhood of `s` in `S` is
  equivalent to the normal bundle over `W` at every grade (`C^∞`, and real-analytic), via
  `Ψ (z, n) = emb z + Σ_a n_a ∇G_a(emb z)`, with inverse
  `y ↦ (π_T (proj y − s), (J Jᵀ)⁻¹ J (y − proj y))`.

Everything is stated for `Fin d → ℝ` with strucdual's dot-product annihilators (no inner product
space structure is used; the Gram inverse replaces the Moore–Penrose pseudo-inverse of
`FrameAtlasOfCoframes`).
-/

open scoped Manifold ContDiff Matrix
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology

namespace Grammar

section Restrict

variable {d : ℕ} {N : (Fin d → ℝ) → Submodule ℝ (Fin d → ℝ)} {S : Set (Fin d → ℝ)}

/-- **Restriction of a tube to an open piece of the base.** The tube over `S ∩ V'` is
`U ∩ proj⁻¹ V'`; every field of the chart is inherited. -/
def restrictTube (T : NormalTubularChart N S) (V' : Set (Fin d → ℝ)) (hV' : IsOpen V') :
    NormalTubularChart N (S ∩ V') where
  eps := T.eps
  eps_pos := T.eps_pos
  U := T.U ∩ T.proj ⁻¹' V'
  mem_U_iff := fun x => by
    constructor
    · rintro ⟨hxU, hxV⟩
      exact ⟨T.proj x, ⟨T.proj_mem hxU, hxV⟩, x - T.proj x, T.ncoord_mem hxU,
        T.ncoord_norm_lt hxU, by abel⟩
    · rintro ⟨s, ⟨hsS, hsV⟩, n, hn, hlt, rfl⟩
      have hU : s + n ∈ T.U := (T.mem_U_iff _).2 ⟨s, hsS, n, hn, hlt, rfl⟩
      refine ⟨hU, ?_⟩
      change T.proj (s + n) ∈ V'
      rw [(T.proj_eq_of_decomp hU hsS hn hlt rfl).1]
      exact hsV
  isOpen_U := isOpen_iff_mem_nhds.2 fun x hx =>
    Filter.inter_mem (T.isOpen_U.mem_nhds hx.1)
      ((T.contDiffAt_proj hx.1).continuousAt.preimage_mem_nhds (hV'.mem_nhds hx.2))
  proj := T.proj
  proj_mem := fun hx => ⟨T.proj_mem hx.1, hx.2⟩
  ncoord_mem := fun hx => T.ncoord_mem hx.1
  ncoord_norm_lt := fun hx => T.ncoord_norm_lt hx.1
  unique := fun h₁ h₂ hn₁ hn₂ hl₁ hl₂ heq => T.unique h₁.1 h₂.1 hn₁ hn₂ hl₁ hl₂ heq
  contDiffAt_proj := fun hx => T.contDiffAt_proj hx.1

@[simp] theorem restrictTube_U (T : NormalTubularChart N S) (V' : Set (Fin d → ℝ))
    (hV' : IsOpen V') : (restrictTube T V' hV').U = T.U ∩ T.proj ⁻¹' V' := rfl

@[simp] theorem restrictTube_proj (T : NormalTubularChart N S) (V' : Set (Fin d → ℝ))
    (hV' : IsOpen V') : (restrictTube T V' hV').proj = T.proj := rfl

end Restrict

section Operators

variable (d r : ℕ)

/-- **Transposition as an operator on operators**: `L ↦ (matrix of L)ᵀ` acting by `mulVec`, a
continuous linear map `((ℝ^d →L ℝ^r) →L (ℝ^r →L ℝ^d))`. -/
noncomputable def transposeCLM :
    ((Fin d → ℝ) →L[ℝ] (Fin r → ℝ)) →L[ℝ] ((Fin r → ℝ) →L[ℝ] (Fin d → ℝ)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((Matrix.toLin'.toLinearMap.comp
        (Matrix.transposeLinearEquiv (Fin r) (Fin d) ℝ ℝ).toLinearMap).comp
        LinearMap.toMatrix'.toLinearMap)).comp (ContinuousLinearMap.coeLM ℝ))

theorem transposeCLM_apply (L : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ)) :
    transposeCLM d r L =
      (LinearMap.toMatrix' (L : (Fin d → ℝ) →ₗ[ℝ] (Fin r → ℝ)))ᵀ.mulVecLin.toContinuousLinearMap :=
  rfl

theorem transposeCLM_mulVecLin (J : Matrix (Fin r) (Fin d) ℝ) :
    transposeCLM d r J.mulVecLin.toContinuousLinearMap = Jᵀ.mulVecLin.toContinuousLinearMap := by
  rw [transposeCLM_apply, LinearMap.coe_toContinuousLinearMap,
    show LinearMap.toMatrix' J.mulVecLin = J from LinearMap.toMatrix'_toLin' J]

variable {d r}

/-- The Gram operator `L Lᵀ` of an operator `L : ℝ^d →L ℝ^r`. -/
noncomputable def gramCLM (L : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ)) : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
  L ∘L transposeCLM d r L

/-- The Gram operator of a full-row-rank Jacobian is invertible. -/
theorem isInvertible_gramCLM {J : Matrix (Fin r) (Fin d) ℝ} (hJ : FullRowRank J) :
    (gramCLM J.mulVecLin.toContinuousLinearMap).IsInvertible := by
  have hinj : Injective (J * Jᵀ).mulVecLin := gram_mulVec_injective hJ
  have hsurj : Surjective (J * Jᵀ).mulVecLin := LinearMap.injective_iff_surjective.1 hinj
  refine ⟨(LinearEquiv.ofBijective (J * Jᵀ).mulVecLin ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  rw [gramCLM, transposeCLM_mulVecLin]
  refine ContinuousLinearMap.ext fun v => ?_
  change (J * Jᵀ).mulVec v = J.mulVec (Jᵀ.mulVec v)
  rw [Matrix.mulVec_mulVec]

end Operators

section RowFrames

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S) (i : A.ι)
  {n : ℕ∞ω}

/-- The derivative of a chart map is its Jacobian field. -/
theorem fderiv_G_eq (x : Fin d → ℝ) :
    fderiv ℝ (A.G i) x = (A.J i x).mulVecLin.toContinuousLinearMap := (A.hJG i x).fderiv

/-- **The row frame** of chart `i` at `x`: `c ↦ J_i(x)ᵀ c = Σ_a c_a ∇G_a(x)`. -/
noncomputable def rowFrame (x : Fin d → ℝ) : (Fin r → ℝ) →L[ℝ] (Fin d → ℝ) :=
  transposeCLM d r (fderiv ℝ (A.G i) x)

/-- **The row coframe** of chart `i` at `x`: the Gram left inverse `(J Jᵀ)⁻¹ J`. -/
noncomputable def rowCoframe (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ) :=
  (gramCLM (fderiv ℝ (A.G i) x)).inverse ∘L fderiv ℝ (A.G i) x

theorem rowFrame_eq (x : Fin d → ℝ) :
    rowFrame A i x = (A.J i x)ᵀ.mulVecLin.toContinuousLinearMap := by
  rw [rowFrame, fderiv_G_eq, transposeCLM_mulVecLin]

/-- On the stratum, the row frame spans the ambient normal space. -/
theorem range_rowFrame {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) :
    LinearMap.range (rowFrame A i x : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = A.normal x := by
  rw [rowFrame_eq, LinearMap.coe_toContinuousLinearMap, A.normal_eq_chart i hx hxi]
  rfl

theorem isInvertible_gramCLM_fderiv {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) :
    (gramCLM (fderiv ℝ (A.G i) x)).IsInvertible := by
  rw [fderiv_G_eq]
  exact isInvertible_gramCLM (A.fullRank i hx hxi)

/-- The row coframe is a left inverse of the row frame on the stratum. -/
theorem rowCoframe_rowFrame {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) (v : Fin r → ℝ) :
    rowCoframe A i x (rowFrame A i x v) = v := by
  exact (isInvertible_gramCLM_fderiv A i hx hxi).inverse_apply_self v

/-- The row frame is `C^n` (indeed analytic) in the base point. -/
theorem contDiffAt_rowFrame (x : Fin d → ℝ) : ContDiffAt ℝ n (rowFrame A i) x :=
  (transposeCLM d r).contDiff.contDiffAt.comp x (A.analyticAt_G i x).fderiv.contDiffAt

/-- The row coframe is `C^n` (indeed analytic) at every point of the stratum in the chart
domain. -/
theorem contDiffAt_rowCoframe {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) :
    ContDiffAt ℝ n (rowCoframe A i) x := by
  have hfd : ContDiffAt ℝ n (fderiv ℝ (A.G i)) x := (A.analyticAt_G i x).fderiv.contDiffAt
  have hT : ContDiffAt ℝ n (fun x => transposeCLM d r (fderiv ℝ (A.G i) x)) x :=
    (transposeCLM d r).contDiff.contDiffAt.comp x hfd
  have hgram : ContDiffAt ℝ n (fun x => gramCLM (fderiv ℝ (A.G i) x)) x := hfd.clm_comp hT
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse (gramCLM (fderiv ℝ (A.G i) x)) :=
    (isInvertible_gramCLM_fderiv A i hx hxi).contDiffAt_map_inverse
  exact (hinv.comp x hgram).clm_comp hfd

end RowFrames

section Graph

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S)

/-- **A tangent-graph chart** of the stratum at `s` in chart `i`: an open piece `W` of the tangent
space `T_s = ker J_i(s)`, an open `V' ⊆ V_i` around `s`, a real-analytic parametrisation `emb`
of `S ∩ V'` by `W`, and its analytic left inverse `ft` (the tangential coordinate). -/
structure TangentGraphChart (i : A.ι) (s : Fin d → ℝ) where
  /-- The parameter domain in the tangent space. -/
  W : Opens ↥(tangentSpaceOf (A.J i s))
  /-- The ambient neighbourhood of `s` on which the graph description holds. -/
  V' : Set (Fin d → ℝ)
  isOpen_V' : IsOpen V'
  V'_subset : V' ⊆ A.V i
  s_mem : s ∈ S ∩ V'
  /-- The graph parametrisation. -/
  emb : ↥(tangentSpaceOf (A.J i s)) → Fin d → ℝ
  contDiffOn_emb : ContDiffOn ℝ ω emb (W : Set ↥(tangentSpaceOf (A.J i s)))
  emb_mem : ∀ z ∈ W, emb z ∈ S ∩ V'
  emb_injOn : InjOn emb (W : Set ↥(tangentSpaceOf (A.J i s)))
  /-- The tangential coordinate. -/
  ft : (Fin d → ℝ) → ↥(tangentSpaceOf (A.J i s))
  contDiff_ft : ContDiff ℝ ω ft
  ft_mem : ∀ x ∈ S ∩ V', ft x ∈ W
  emb_ft : ∀ x ∈ S ∩ V', emb (ft x) = x

/-- **Existence of a tangent-graph chart** at every `s ∈ S ∩ V_i`, by the analytic inverse
function theorem for `F x = (G_i x, π_T (x − s))`. -/
theorem exists_tangentGraphChart (i : A.ι) {s : Fin d → ℝ} (hs : s ∈ S) (hsi : s ∈ A.V i) :
    Nonempty (TangentGraphChart A i s) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (tangentSpaceOf (A.J i s))
  let pT : (Fin d → ℝ) →L[ℝ] ↥(tangentSpaceOf (A.J i s)) :=
    LinearMap.toContinuousLinearMap ((tangentSpaceOf (A.J i s)).projectionOnto Q hQ)
  have hπ : ∀ v (hv : v ∈ tangentSpaceOf (A.J i s)), pT v = ⟨v, hv⟩ := fun v hv =>
    Submodule.projectionOnto_apply_left hQ ⟨v, hv⟩
  let L₀ : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ) := (A.J i s).mulVecLin.toContinuousLinearMap
  let DF : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ) × ↥(tangentSpaceOf (A.J i s)) := L₀.prod pT
  let F : (Fin d → ℝ) → (Fin r → ℝ) × ↥(tangentSpaceOf (A.J i s)) :=
    fun x => (A.G i x, pT (x - s))
  have hFd : HasFDerivAt F DF s := by
    have h1 : HasFDerivAt (fun x => pT (x - s)) pT s := by
      have h0 := pT.hasFDerivAt.comp s ((hasFDerivAt_id s).sub_const s)
      rw [ContinuousLinearMap.comp_id] at h0
      exact h0
    exact (A.hJG i s).prodMk h1
  have hinj : Injective DF := by
    refine (injective_iff_map_eq_zero DF).2 fun u hu => ?_
    have h1 : L₀ u = 0 := congrArg Prod.fst hu
    have h2 : pT u = 0 := congrArg Prod.snd hu
    have hu' : u ∈ tangentSpaceOf (A.J i s) := h1
    have h3 : (⟨u, hu'⟩ : ↥(tangentSpaceOf (A.J i s))) = 0 := by rw [← hπ u hu', h2]
    simpa using congrArg Subtype.val h3
  have hdim : Module.finrank ℝ (Fin d → ℝ) =
      Module.finrank ℝ ((Fin r → ℝ) × ↥(tangentSpaceOf (A.J i s))) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A.J i s).mulVecLin
    have hr : LinearMap.range (A.J i s).mulVecLin = ⊤ :=
      LinearMap.range_eq_top.2 (fullRowRank_iff_surjective.1 (A.fullRank i hs hsi))
    rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    have hker : Module.finrank ℝ ↥(tangentSpaceOf (A.J i s)) =
      Module.finrank ℝ ↥(LinearMap.ker (A.J i s).mulVecLin) := rfl
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, hker]
    omega
  let Deq : (Fin d → ℝ) ≃L[ℝ] (Fin r → ℝ) × ↥(tangentSpaceOf (A.J i s)) :=
    ((DF : (Fin d → ℝ) →ₗ[ℝ] _).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hDeq : (Deq : (Fin d → ℝ) →L[ℝ] _) = DF :=
    ContinuousLinearMap.ext fun v => LinearMap.linearEquivOfInjective_apply hinj hdim v
  have hFa : AnalyticAt ℝ F s :=
    (A.analyticAt_G i s).prod
      ((pT.analyticAt _).comp (g := pT) (f := fun x => x - s) (analyticAt_id.sub analyticAt_const))
  have hFc : ContDiffAt ℝ ω F s := hFa.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hFd' : HasFDerivAt F (Deq : (Fin d → ℝ) →L[ℝ] _) s := by rw [hDeq]; exact hFd
  have hstrict : HasStrictFDerivAt F (Deq : (Fin d → ℝ) →L[ℝ] _) s :=
    hFc.hasStrictFDerivAt' hFd' hn
  set ψ₀ := hstrict.toOpenPartialHomeomorph F with hψ₀def
  have hψ₀ : ⇑ψ₀ = F := hstrict.toOpenPartialHomeomorph_coe
  have hs₀ : s ∈ ψ₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hinvA : AnalyticAt ℝ ψ₀.symm (F s) := (hFc.to_localInverse hFd' hn).analyticAt
  obtain ⟨O, hO, hOopen, hFsO⟩ := eventually_nhds_iff.1 hinvA.eventually_analyticAt
  have hOsm : ContDiffOn ℝ ω ψ₀.symm O :=
    (show AnalyticOnNhd ℝ ψ₀.symm O from fun y hy => hO y hy).contDiffOn hOopen.uniqueDiffOn
  set ψ := ψ₀.restrOpen (A.V i) (A.isOpen_V i) with hψdef
  have hψc : ⇑ψ = F := by rw [hψdef, OpenPartialHomeomorph.coe_restrOpen, hψ₀]
  have hψsrc : ψ.source = ψ₀.source ∩ A.V i := ψ₀.restrOpen_source _ _
  have hsψ : s ∈ ψ.source := by rw [hψsrc]; exact ⟨hs₀, hsi⟩
  have hFs0 : F s = (0, 0) := by
    change (A.G i s, pT (s - s)) = (0, 0)
    rw [(A.zero_iff i hsi).1 hs, sub_self, map_zero]
  let V' : Set (Fin d → ℝ) := ψ.source ∩ ψ ⁻¹' O
  have hV'open : IsOpen V' := ψ.isOpen_inter_preimage hOopen
  have hsV' : s ∈ V' := ⟨hsψ, by change ψ s ∈ O; rw [hψc]; exact hFsO⟩
  have hV'sub : V' ⊆ A.V i := fun x hx => by
    have := hx.1
    rw [hψsrc] at this
    exact this.2
  let Wset : Set ↥(tangentSpaceOf (A.J i s)) :=
    {z | ((0 : Fin r → ℝ), z) ∈ ψ.target ∩ O}
  have hWopen : IsOpen Wset :=
    (ψ.open_target.inter hOopen).preimage (continuous_const.prodMk continuous_id)
  let W : Opens ↥(tangentSpaceOf (A.J i s)) := ⟨Wset, hWopen⟩
  let emb : ↥(tangentSpaceOf (A.J i s)) → Fin d → ℝ := fun z => ψ.symm (0, z)
  let ft : (Fin d → ℝ) → ↥(tangentSpaceOf (A.J i s)) := fun x => pT (x - s)
  have hGzero : ∀ x ∈ ψ.source, x ∈ S → ψ x = (0, ft x) := by
    intro x hx hxS
    have hxV : x ∈ A.V i := by rw [hψsrc] at hx; exact hx.2
    rw [hψc]
    change (A.G i x, pT (x - s)) = (0, pT (x - s))
    rw [(A.zero_iff i hxV).1 hxS]
  have hft_mem : ∀ x ∈ S ∩ V', ft x ∈ W := by
    rintro x ⟨hxS, hxsrc, hxO⟩
    change ((0 : Fin r → ℝ), ft x) ∈ ψ.target ∩ O
    rw [← hGzero x hxsrc hxS]
    exact ⟨ψ.map_source hxsrc, hxO⟩
  have hemb_ft : ∀ x ∈ S ∩ V', emb (ft x) = x := by
    rintro x ⟨hxS, hxsrc, -⟩
    change ψ.symm (0, ft x) = x
    rw [← hGzero x hxsrc hxS]
    exact ψ.left_inv hxsrc
  have hemb_mem : ∀ z ∈ W, emb z ∈ S ∩ V' := by
    intro z hz
    obtain ⟨hzt, hzO⟩ := (hz : ((0 : Fin r → ℝ), z) ∈ ψ.target ∩ O)
    have hsrc : ψ.symm (0, z) ∈ ψ.source := ψ.map_target hzt
    have hri : ψ (ψ.symm (0, z)) = (0, z) := ψ.right_inv hzt
    have hxV : ψ.symm (0, z) ∈ A.V i := by rw [hψsrc] at hsrc; exact hsrc.2
    have hG : A.G i (ψ.symm (0, z)) = 0 := by
      have := congrArg Prod.fst hri
      rw [hψc] at this
      exact this
    exact ⟨(A.zero_iff i hxV).2 hG, hsrc, by change ψ (ψ.symm (0, z)) ∈ O; rw [hri]; exact hzO⟩
  have hemb_inj : InjOn emb (W : Set ↥(tangentSpaceOf (A.J i s))) := by
    intro z₁ hz₁ z₂ hz₂ h
    have h₁ : ((0 : Fin r → ℝ), z₁) ∈ ψ.symm.source := by
      rw [ψ.symm_source]; exact (hz₁ : ((0 : Fin r → ℝ), z₁) ∈ ψ.target ∩ O).1
    have h₂ : ((0 : Fin r → ℝ), z₂) ∈ ψ.symm.source := by
      rw [ψ.symm_source]; exact (hz₂ : ((0 : Fin r → ℝ), z₂) ∈ ψ.target ∩ O).1
    exact (Prod.mk.inj (ψ.symm.injOn h₁ h₂ h)).2
  have hemb_smooth : ContDiffOn ℝ ω emb (W : Set ↥(tangentSpaceOf (A.J i s))) := by
    have h1 : ContDiffOn ℝ ω (fun z : ↥(tangentSpaceOf (A.J i s)) => ((0 : Fin r → ℝ), z))
        (W : Set ↥(tangentSpaceOf (A.J i s))) := (contDiff_const.prodMk contDiff_id).contDiffOn
    exact hOsm.comp h1 fun z hz => (hz : ((0 : Fin r → ℝ), z) ∈ ψ.target ∩ O).2
  exact ⟨⟨W, V', hV'open, hV'sub, ⟨hs, hsV'⟩, emb, hemb_smooth, hemb_mem, hemb_inj, ft,
    pT.contDiff.comp (contDiff_id.sub contDiff_const), hft_mem, hemb_ft⟩⟩

end Graph

section Lift

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {i : A.ι}
  {s : Fin d → ℝ} {n : ℕ∞ω}

/-- A `C^n` map on an open subset of a normed space is `C^n` as a map on the `Opens` manifold. -/
theorem contMDiff_comp_val {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (W : Opens E) {f : E → F}
    (hf : ContDiffOn ℝ n f (W : Set E)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n (fun z : ↥W => f z.1) :=
  (contMDiffOn_iff_contDiffOn.2 hf).comp_contMDiff contMDiff_subtype_val fun z => z.2

/-- Regularity of a map into an `Opens` manifold is regularity of its composite with the
inclusion — Mathlib's `ContMDiffWithinAt.subtypeVal_comp_iff` at every grade `n` (the underlying
`liftPropWithinAt_subtypeVal_comp_iff` is grade-free). -/
theorem contMDiffWithinAt_subtypeVal_comp_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (W : Opens F) (f : E → ↥W)
    (t : Set E) (x : E) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) n (Subtype.val ∘ f) t x ↔
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f t x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f t x

/-- The graph parametrisation as a map on the base manifold `↥W`. -/
def graphEmb (C : TangentGraphChart A i s) : ↥C.W → Fin d → ℝ := fun z => C.emb z.1

open Classical in
/-- The lifted foot: the tangential coordinate of the foot point, landing in `W` on the
restricted tube (and sent to `ft s` elsewhere). -/
noncomputable def graphFoot (C : TangentGraphChart A i s) (T : NormalTubularChart A.normal S) :
    (Fin d → ℝ) → ↥C.W := fun y =>
  if h : C.ft (T.proj y) ∈ C.W then ⟨C.ft (T.proj y), h⟩ else ⟨C.ft s, C.ft_mem s C.s_mem⟩

theorem graphEmb_mem (C : TangentGraphChart A i s) (z : ↥C.W) : graphEmb C z ∈ S ∩ C.V' :=
  C.emb_mem z.1 z.2

/-- **The frame–coframe atlas of the Jacobian rows along the graph**, over the base `↥W`, at any
grade `n` (the data are analytic). -/
noncomputable def graphFrameData (n : ℕ∞ω) (C : TangentGraphChart A i s) :
    FrameCoframeData 𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))) (Fin r → ℝ) n
      (fun z : ↥C.W => A.normal (graphEmb C z)) Unit where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := ()
  mem_baseSet_at _ := mem_univ _
  frame _ z := rowFrame A i (graphEmb C z)
  range_frame _ z _ := range_rowFrame A i (graphEmb_mem C z).1 (C.V'_subset (graphEmb_mem C z).2)
  contMDiffOn_frame _ :=
    (contMDiff_comp_val C.W (f := fun x => rowFrame A i (C.emb x)) fun z hz =>
      (contDiffAt_rowFrame A i _).comp_contDiffWithinAt z
        ((C.contDiffOn_emb.of_le le_top) z hz)).contMDiffOn
  coframe _ z := rowCoframe A i (graphEmb C z)
  coframe_frame _ z _ v :=
    rowCoframe_rowFrame A i (graphEmb_mem C z).1 (C.V'_subset (graphEmb_mem C z).2) v
  contMDiffOn_coframe _ :=
    (contMDiff_comp_val C.W (f := fun x => rowCoframe A i (C.emb x)) fun z hz =>
      (contDiffAt_rowCoframe A i (C.emb_mem z hz).1
        (C.V'_subset (C.emb_mem z hz).2)).comp_contDiffWithinAt z
          ((C.contDiffOn_emb.of_le le_top) z hz)).contMDiffOn

theorem graphFoot_mem_W (C : TangentGraphChart A i s) (T : NormalTubularChart A.normal S)
    {y : Fin d → ℝ} (hy : y ∈ (restrictTube T C.V' C.isOpen_V').U) :
    C.ft (T.proj y) ∈ C.W :=
  C.ft_mem _ ⟨T.proj_mem hy.1, hy.2⟩

theorem graphFoot_val (C : TangentGraphChart A i s) (T : NormalTubularChart A.normal S)
    {y : Fin d → ℝ} (hy : y ∈ (restrictTube T C.V' C.isOpen_V').U) :
    (graphFoot C T y).1 = C.ft (T.proj y) := by
  simp only [graphFoot, dif_pos (graphFoot_mem_W C T hy)]

/-- The lifted foot has the grade of the foot projection on the restricted tube. -/
theorem contMDiffOn_graphFoot (C : TangentGraphChart A i s) (T : NormalTubularChart A.normal S)
    (hproj : ∀ y ∈ T.U, ContDiffAt ℝ n T.proj y) :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))) n (graphFoot C T)
      (restrictTube T C.V' C.isOpen_V').U := by
  intro y hy
  rw [← contMDiffWithinAt_subtypeVal_comp_iff]
  refine ContMDiffWithinAt.congr (f := fun y => C.ft (T.proj y)) ?_
    (fun y' hy' => graphFoot_val C T hy') (graphFoot_val C T hy)
  exact contMDiffWithinAt_iff_contDiffWithinAt.2
    ((C.contDiff_ft.of_le le_top).contDiffAt.comp y (hproj y hy.1)).contDiffWithinAt

/-- **The lifted foot from strucdual's tube**: over a tangent-graph chart, the restricted tube,
the graph parametrisation, the Jacobian-row atlas and the tangential foot form a `LiftedFoot` at
every grade `n` carried by the foot projection (`n = ∞` for any chart, `n = ω` for an analytic
chart). -/
theorem liftedFoot_graph (C : TangentGraphChart A i s) (T : NormalTubularChart A.normal S)
    (hproj : ∀ y ∈ T.U, ContDiffAt ℝ n T.proj y) :
    LiftedFoot (restrictTube T C.V' C.isOpen_V') (graphEmb C) (graphFrameData n C)
      (graphFoot C T) where
  contMDiff_emb := contMDiff_comp_val C.W (C.contDiffOn_emb.of_le le_top)
  emb_mem z := graphEmb_mem C z
  emb_injective z₁ z₂ h := Subtype.ext (C.emb_injOn z₁.2 z₂.2 h)
  contMDiffOn_P := contMDiffOn_graphFoot C T hproj
  emb_P y hy := by
    change C.emb (graphFoot C T y).1 = T.proj y
    rw [graphFoot_val C T hy]
    exact C.emb_ft _ ⟨T.proj_mem hy.1, hy.2⟩
  contDiffAt_ncoord y hy := contDiffAt_id.sub (hproj y hy.1)

end Lift

section Headline

variable {d r : ℕ} {S : Set (Fin d → ℝ)}

/-- An analytic normal tubular chart has a foot projection of every grade on its tube. -/
theorem analyticTube_contDiffAt_proj {N : (Fin d → ℝ) → Submodule ℝ (Fin d → ℝ)}
    (T : AnalyticNormalTubularChart N S) (n : ℕ∞ω) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    ContDiffAt ℝ n T.proj y :=
  (T.analyticAt_proj hy).contDiffAt

/-- **The lifted foot exists for compact analytic LCI strata, at every grade.** For every `s ∈ S`,
strucdual's analytic tube, restricted to a neighbourhood of `s` in `S`, carries a `LiftedFoot` of
grade `n` over the tangent-graph base `↥W` — discharging the hypothesis of the conditional tubular
equivalence (`n = ∞`: smooth; `n = ω`: real-analytic). -/
theorem exists_liftedFoot_of_compact (n : ℕ∞ω) (hS : IsCompact S)
    (A : CompatibleAnalyticLCIAtlas r S) {s : Fin d → ℝ} (hs : s ∈ S) :
    ∃ (T : AnalyticNormalTubularChart A.normal S) (i : A.ι) (C : TangentGraphChart A i s),
      LiftedFoot (restrictTube T.toNormalTubularChart C.V' C.isOpen_V') (graphEmb C)
        (graphFrameData n C) (graphFoot C T.toNormalTubularChart) := by
  obtain ⟨T⟩ := exists_analyticNormalTubularChart_of_atlas hS A
  obtain ⟨i, hsi⟩ := A.cover hs
  obtain ⟨C⟩ := exists_tangentGraphChart A i hs hsi
  exact ⟨T, i, C, liftedFoot_graph C _ fun y hy => analyticTube_contDiffAt_proj T n hy⟩

/-- **The local tubular equivalence for compact analytic LCI strata (unconditional, every
grade).** Near every `s ∈ S` there is a tangent-graph chart `C` (with `s ∈ C.V'` open) and an open
partial homeomorphism `Ψ` from the certified domain of the Jacobian-row normal bundle over `↥C.W`
onto the restricted tube `U ∩ proj⁻¹ V'`, `Ψ (z, n) = emb z + Σ_a n_a ∇G_a(emb z)`, of grade `n`
in both directions. -/
theorem exists_local_tubular_equivalence (n : ℕ∞ω) (hS : IsCompact S)
    (A : CompatibleAnalyticLCIAtlas r S) {s : Fin d → ℝ} (hs : s ∈ S) :
    ∃ (T : AnalyticNormalTubularChart A.normal S) (i : A.ι) (C : TangentGraphChart A i s),
      s ∈ C.V' ∧ IsOpen C.V' ∧
      ∃ Ψ : OpenPartialHomeomorph
          (TotalSpace (Fin r → ℝ) (graphFrameData n C).toAtlas.toCore.Fiber) (Fin d → ℝ),
        Ψ.source = tubeDom (restrictTube T.toNormalTubularChart C.V' C.isOpen_V') (graphEmb C)
          (graphFrameData n C) ∧
        Ψ.target = T.U ∩ T.proj ⁻¹' C.V' ∧
        (∀ p, Ψ p = C.emb p.1.1 + (graphFrameData n C).toAtlas.realise p) ∧
        ContMDiff (𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))).prod 𝓘(ℝ, Fin r → ℝ)) 𝓘(ℝ, Fin d → ℝ) n Ψ ∧
        ContMDiffOn 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))).prod 𝓘(ℝ, Fin r → ℝ)) n
          Ψ.symm Ψ.target := by
  obtain ⟨T, i, C, h⟩ := exists_liftedFoot_of_compact n hS A hs
  exact ⟨T, i, C, C.s_mem.2, C.isOpen_V', tubeHomeomorph h, rfl, rfl, fun _ => rfl,
    contMDiff_tubeMap h, contMDiffOn_tubeInv h⟩

/-- **The local tubular equivalence is real-analytic**: the grade-`ω` instance of
`exists_local_tubular_equivalence` — `Ψ` and its inverse are real-analytic (the regularity the
paper's analyticity remark for tubular neighbourhoods requires, obtained without a metric from the
analytic inverse function theorem and strucdual's analytic tube). -/
theorem exists_local_tubular_equivalence_analytic (hS : IsCompact S)
    (A : CompatibleAnalyticLCIAtlas r S) {s : Fin d → ℝ} (hs : s ∈ S) :
    ∃ (T : AnalyticNormalTubularChart A.normal S) (i : A.ι) (C : TangentGraphChart A i s),
      s ∈ C.V' ∧ IsOpen C.V' ∧
      ∃ Ψ : OpenPartialHomeomorph
          (TotalSpace (Fin r → ℝ) (graphFrameData ω C).toAtlas.toCore.Fiber) (Fin d → ℝ),
        Ψ.source = tubeDom (restrictTube T.toNormalTubularChart C.V' C.isOpen_V') (graphEmb C)
          (graphFrameData ω C) ∧
        Ψ.target = T.U ∩ T.proj ⁻¹' C.V' ∧
        (∀ p, Ψ p = C.emb p.1.1 + (graphFrameData ω C).toAtlas.realise p) ∧
        ContMDiff (𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))).prod 𝓘(ℝ, Fin r → ℝ)) 𝓘(ℝ, Fin d → ℝ) ω Ψ ∧
        ContMDiffOn 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, ↥(tangentSpaceOf (A.J i s))).prod 𝓘(ℝ, Fin r → ℝ)) ω
          Ψ.symm Ψ.target :=
  exists_local_tubular_equivalence ω hS A hs

end Headline

end Grammar
