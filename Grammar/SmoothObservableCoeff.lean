/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothJetDetermination
import Grammar.SmoothCoefficientLinearity

/-!
# The observable coefficient functional of the resolution bridge (consult #123, units C0a–C0b, C3)

For fixed bridge inputs `X` (phase `K`, prior, normalised core transport) and a fixed index
`(μ, q)`, the intrinsic coefficient of `N^{−μ} (log N)^q` in the expansion of
`Z_N[f] = ∫ prior · f · e^{−N K}` is a function of the smooth observable `f` alone:

  `observableCoeff X μ q f hf := (X.withObs f hf).decomp.coeff μ q`.

This file establishes the algebraic and geometric facts that make this functional the
*coefficient distribution* of the next unit:

* **linearity** (`observableCoeff_add`, `observableCoeff_smul`, `observableCoeff_zero`), by the
  certificate calculus of `SmoothCoefficientLinearity` and the uniqueness theorem
  `SmoothExpansionCertificate.coeff_eq` — never by unfolding the engine;
* **intrinsicness** (`observableCoeff_eq_of_eq`): two bridge presentations of the same phase and
  prior (arbitrary chart families, weights, box sizes) define the same functional;
* the **core image** `⋃ᵢ ψᵢ([−aᵢ,aᵢ]^d)` and the **wall image** `⋃ᵢ ψᵢ(activeWalls i)` are compact,
  and the wall image lies in the zero set of the phase (`wallImage_subset_zeroSet`) — by the
  monomial normal form on each chart, without any continuity assumption on `K`;
* **support**: the functional vanishes on observables whose support avoids the wall image
  (`observableCoeff_eq_zero_of_tsupport_subset`, from finite-jet determination against the zero
  observable: a function vanishing near every wall point has vanishing chart jets on the walls)
  and on observables whose support avoids the support of the prior
  (`observableCoeff_eq_zero_of_disjoint_prior`, since then `Z_N[f] ≡ 0`).

Coordinate derivatives of functions agreeing on an open set agree there
(`pd_eqOn_of_isOpen`, `pdMulti_eqOn_of_isOpen`; no regularity needed), which is the local-zero
jet helper used for the support theorem.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Coordinate derivatives are local -/

/-- Coordinate derivatives of two functions agreeing on an open set agree on that set. -/
theorem pd_eqOn_of_isOpen {W : Set (Fin d → ℝ)} (hW : IsOpen W) {F G : (Fin d → ℝ) → ℝ}
    (h : EqOn F G W) (i : Fin d) : EqOn (pd i F) (pd i G) W := by
  intro v hv
  unfold pd
  apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous fun t : ℝ => Function.update v i t :=
    continuous_const.update i continuous_id
  have hmem : ∀ᶠ t in 𝓝 (v i), Function.update v i t ∈ W := by
    have : Function.update v i (v i) ∈ W := by rwa [Function.update_eq_self]
    exact hcont.continuousAt.eventually_mem (hW.mem_nhds this)
  exact hmem.mono fun t ht => h ht

theorem pdPow_eqOn_of_isOpen {W : Set (Fin d → ℝ)} (hW : IsOpen W) {F G : (Fin d → ℝ) → ℝ}
    (h : EqOn F G W) (i : Fin d) (n : ℕ) : EqOn (pdPow i n F) (pdPow i n G) W := by
  induction n generalizing F G with
  | zero => exact h
  | succ n ih => rw [pdPow_succ, pdPow_succ]; exact ih (pd_eqOn_of_isOpen hW h i)

theorem pdMulti_eqOn_of_isOpen {W : Set (Fin d → ℝ)} (hW : IsOpen W) {F G : (Fin d → ℝ) → ℝ}
    (h : EqOn F G W) (m : Fin d → ℕ) (l : List (Fin d)) :
    EqOn (pdMulti m l F) (pdMulti m l G) W := by
  induction l generalizing F G with
  | nil => exact h
  | cons i l ih => exact pdPow_eqOn_of_isOpen hW (ih h) i (m i)

theorem pd_zeroFun (i : Fin d) : pd i (fun _ : Fin d → ℝ => (0 : ℝ)) = fun _ => 0 := by
  funext v
  unfold pd line
  simp

theorem pdPow_zeroFun (i : Fin d) (n : ℕ) :
    pdPow i n (fun _ : Fin d → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pdPow_succ, pd_zeroFun, ih]

theorem pdMulti_zeroFun (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun _ : Fin d → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [pdMulti_cons, ih, pdPow_zeroFun]

/-! ### The partition function with a variable observable -/

/-- `Z_N[f] = ∫ prior · f · e^{−N K}`. -/
noncomputable def partitionObs (K prior f : (Fin d → ℝ) → ℝ) (N : ℝ) : ℝ :=
  ∫ y, prior y * f y * Real.exp (-N * K y)

namespace BridgeInputs

variable (X : BridgeInputs d)

/-- ★ **The observable coefficient functional**: the intrinsic coefficient of `N^{−μ}(log N)^q`
in the expansion of `∫ prior · f · e^{−NK}`, as a function of the smooth observable `f`. -/
noncomputable def observableCoeff (μ : ℝ) (q : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ℝ :=
  (X.withObs f hf).decomp.coeff μ q

theorem observableCoeff_obs (μ : ℝ) (q : ℕ) :
    X.observableCoeff μ q X.obs X.obs_smooth = X.decomp.coeff μ q := rfl

theorem withObs_withObs {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (X.withObs f hf).withObs g hg = X.withObs g hg := rfl

theorem withObs_Z {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (N : ℝ) :
    (X.withObs f hf).D.Z N = partitionObs X.K X.prior f N := (X.withObs f hf).Z_eq N

/-- The certificate of the expansion of `Z_N[f]` produced by the bridge. -/
noncomputable def obsCertificate {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    SmoothExpansionCertificate (partitionObs X.K X.prior f) :=
  (X.withObs f hf).decomp.toCertificate.congr (Eventually.of_forall fun N => X.withObs_Z hf N)

theorem obsCertificate_coeff {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : ℝ) (q : ℕ) :
    (X.obsCertificate hf).coeff μ q = X.observableCoeff μ q f hf := rfl

/-- ★★ **Intrinsicness**: two bridge presentations of the same phase and prior define the same
observable coefficient functional. -/
theorem observableCoeff_eq_of_eq {Y : BridgeInputs d} (hK : X.K = Y.K) (hp : X.prior = Y.prior)
    (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    X.observableCoeff μ q f hf = Y.observableCoeff μ q f hf := by
  have hZ : partitionObs Y.K Y.prior f = partitionObs X.K X.prior f := by rw [hK, hp]
  exact SmoothExpansionCertificate.coeff_eq (X.obsCertificate hf)
    ((Y.obsCertificate hf).congr (Filter.EventuallyEq.of_eq hZ)) μ q

/-! ### Linearity in the observable -/

theorem Z_withObs_add {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℝ} (hN : 0 ≤ N) :
    (X.withObs (fun y => f y + g y) (hf.add hg)).D.Z N =
      (X.withObs f hf).D.Z N + (X.withObs g hg).D.Z N := by
  have hX := (X.withObs f hf).D.integrable_integrand hN
  have hY := (X.withObs g hg).D.integrable_integrand hN
  unfold LocalisationData.Z
  change ∫ z, (X.withObs _ (hf.add hg)).D.integrand N z ∂X.priorMeasure =
    ∫ z, (X.withObs f hf).D.integrand N z ∂X.priorMeasure +
      ∫ z, (X.withObs g hg).D.integrand N z ∂X.priorMeasure
  change Integrable _ X.priorMeasure at hX hY
  rw [← integral_add hX hY]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change (f w + g w) * Real.exp (-N * X.K w) =
    f w * Real.exp (-N * X.K w) + g w * Real.exp (-N * X.K w)
  ring

theorem Z_withObs_smul {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) (N : ℝ) :
    (X.withObs (fun y => r * f y) (contDiff_const.mul hf)).D.Z N = r * (X.withObs f hf).D.Z N := by
  unfold LocalisationData.Z
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change r * f w * Real.exp (-N * X.K w) = r * (f w * Real.exp (-N * X.K w))
  ring

theorem Z_withObs_zero (N : ℝ) :
    (X.withObs (fun _ => (0 : ℝ)) contDiff_const).D.Z N = 0 := by
  unfold LocalisationData.Z
  refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
  change (0 : ℝ) * Real.exp (-N * X.K w) = 0
  ring

/-- ★★ **Additivity** of the observable coefficient functional. -/
theorem observableCoeff_add (μ : ℝ) (q : ℕ) {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    X.observableCoeff μ q (fun y => f y + g y) (hf.add hg) =
      X.observableCoeff μ q f hf + X.observableCoeff μ q g hg := by
  have hev : (fun N => (X.withObs f hf).D.Z N + (X.withObs g hg).D.Z N) =ᶠ[atTop]
      (X.withObs (fun y => f y + g y) (hf.add hg)).D.Z :=
    (eventually_ge_atTop (0 : ℝ)).mono fun N hN => (X.Z_withObs_add hf hg hN).symm
  exact SmoothExpansionCertificate.coeff_eq (X.withObs _ (hf.add hg)).decomp.toCertificate
    (((X.withObs f hf).decomp.toCertificate.add (X.withObs g hg).decomp.toCertificate).congr hev)
    μ q

/-- ★ **Homogeneity** of the observable coefficient functional. -/
theorem observableCoeff_smul (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) :
    X.observableCoeff μ q (fun y => r * f y) (contDiff_const.mul hf) =
      r * X.observableCoeff μ q f hf := by
  have hev : (fun N => r * (X.withObs f hf).D.Z N) =ᶠ[atTop]
      (X.withObs (fun y => r * f y) (contDiff_const.mul hf)).D.Z :=
    Eventually.of_forall fun N => (X.Z_withObs_smul hf r N).symm
  exact SmoothExpansionCertificate.coeff_eq
    (X.withObs _ (contDiff_const.mul hf)).decomp.toCertificate
    (((X.withObs f hf).decomp.toCertificate.smul r).congr hev) μ q

/-- The zero observable has zero coefficients. -/
theorem observableCoeff_zero (μ : ℝ) (q : ℕ) :
    X.observableCoeff μ q (fun _ => (0 : ℝ)) contDiff_const = 0 := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
      (X.withObs (fun _ => (0 : ℝ)) contDiff_const).D.Z :=
    Eventually.of_forall fun N => (X.Z_withObs_zero N).symm
  exact SmoothExpansionCertificate.coeff_eq (X.withObs _ contDiff_const).decomp.toCertificate
    (SmoothExpansionCertificate.zero.congr hev) μ q

/-- The functional depends on the observable only through its values (the smoothness proof is
irrelevant), and observables equal as functions give equal coefficients. -/
theorem observableCoeff_congr (μ : ℝ) (q : ℕ) {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h : f = g) :
    X.observableCoeff μ q f hf = X.observableCoeff μ q g hg := by
  subst h; rfl

/-! ### The core image and the wall image -/

/-- The union of the chart images of the closed chart boxes. -/
def coreImage : Set (Fin d → ℝ) := ⋃ i, X.T.ψ i '' centeredBox d (X.T.a i)

/-- The union of the chart images of the active walls: the image of the resolved zero divisor. -/
def wallImage : Set (Fin d → ℝ) := ⋃ i, X.T.ψ i '' X.activeWalls i

theorem continuousOn_ψ_box (i : X.T.ι) : ContinuousOn (X.T.ψ i) (centeredBox d (X.T.a i)) :=
  (X.T.ψ_analytic i).continuousOn.mono (X.T.box_subset_V i)

theorem activeWalls_subset_box (i : X.T.ι) : X.activeWalls i ⊆ centeredBox d (X.T.a i) :=
  inter_subset_left

theorem isClosed_wallSet (i : X.T.ι) : IsClosed {u : Fin d → ℝ | ∃ j, 0 < X.T.k i j ∧ u j = 0} := by
  have : {u : Fin d → ℝ | ∃ j, 0 < X.T.k i j ∧ u j = 0} =
      ⋃ j, {u : Fin d → ℝ | 0 < X.T.k i j ∧ u j = 0} := by
    ext u; simp [mem_iUnion]
  rw [this]
  refine isClosed_iUnion_of_finite fun j => ?_
  by_cases hj : 0 < X.T.k i j
  · have : {u : Fin d → ℝ | 0 < X.T.k i j ∧ u j = 0} = {u | u j = 0} := by ext u; simp [hj]
    rw [this]
    exact isClosed_eq (continuous_apply j) continuous_const
  · have : {u : Fin d → ℝ | 0 < X.T.k i j ∧ u j = 0} = ∅ := by ext u; simp [hj]
    rw [this]
    exact isClosed_empty

theorem isCompact_activeWalls (i : X.T.ι) : IsCompact (X.activeWalls i) :=
  (isCompact_centeredBox d (X.T.a i)).inter_right (X.isClosed_wallSet i)

theorem isCompact_coreImage : IsCompact X.coreImage :=
  isCompact_iUnion fun i =>
    (isCompact_centeredBox d (X.T.a i)).image_of_continuousOn (X.continuousOn_ψ_box i)

theorem isCompact_wallImage : IsCompact X.wallImage :=
  isCompact_iUnion fun i => (X.isCompact_activeWalls i).image_of_continuousOn
    ((X.continuousOn_ψ_box i).mono (X.activeWalls_subset_box i))

theorem isClosed_wallImage : IsClosed X.wallImage := X.isCompact_wallImage.isClosed

theorem wallImage_subset_coreImage : X.wallImage ⊆ X.coreImage :=
  iUnion_mono fun i => image_mono (X.activeWalls_subset_box i)

/-- ★ **The wall image lies in the zero set of the phase**: on each chart the phase is the
monomial `c ∏ u_j^{2k_j}`, which vanishes on the active walls. -/
theorem wallImage_subset_zeroSet : X.wallImage ⊆ {x | X.K x = 0} := by
  intro x hx
  obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.1 hx |>.imp fun i h => h
  obtain ⟨j, hkj, huj⟩ := hu.2
  change X.K (X.T.ψ i u) = 0
  rw [X.T.phase_eq i u (X.T.box_subset_V i hu.1)]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [huj]
  exact zero_pow (by omega)

theorem mem_wallImage_of_mem_activeWalls {i : X.T.ι} {u : Fin d → ℝ} (hu : u ∈ X.activeWalls i) :
    X.T.ψ i u ∈ X.wallImage :=
  mem_iUnion.2 ⟨i, mem_image_of_mem _ hu⟩

/-! ### Support -/

/-- ★★ **Vanishing off the wall image**: an observable whose support avoids the wall image has
zero coefficients (finite-jet determination against the zero observable). -/
theorem observableCoeff_eq_zero_of_tsupport_subset (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ X.wallImageᶜ) :
    X.observableCoeff μ q f hf = 0 := by
  rw [← X.observableCoeff_zero μ q]
  unfold observableCoeff
  rw [← X.withObs_withObs hf contDiff_const]
  refine (X.withObs f hf).coeff_congr_of_jets contDiff_const (fun i => ?_) q
  intro α _ u hu
  have hfu : f (X.T.ψ i u) = 0 := by
    have : X.T.ψ i u ∉ tsupport f := fun h => hsupp h (X.mem_wallImage_of_mem_activeWalls hu)
    exact image_eq_zero_of_notMem_tsupport this
  -- `f ∘ ψ i` vanishes on the open set `(ψ i)⁻¹((tsupport f)ᶜ) ∩ V i`, which contains `u`
  have hW : IsOpen (X.T.V i ∩ X.T.ψ i ⁻¹' (tsupport f)ᶜ) :=
    (X.T.ψ_analytic i).continuousOn.isOpen_inter_preimage (X.T.V_open i)
      (isClosed_tsupport f).isOpen_compl
  have huW : u ∈ X.T.V i ∩ X.T.ψ i ⁻¹' (tsupport f)ᶜ :=
    ⟨X.T.box_subset_V i hu.1, fun h => hsupp h (X.mem_wallImage_of_mem_activeWalls hu)⟩
  have heq : EqOn ((X.withObs f hf).obs ∘ X.T.ψ i) ((fun _ => (0 : ℝ)) ∘ X.T.ψ i)
      (X.T.V i ∩ X.T.ψ i ⁻¹' (tsupport f)ᶜ) := fun v hv =>
    (image_eq_zero_of_notMem_tsupport hv.2 : f (X.T.ψ i v) = 0)
  exact pdMulti_eqOn_of_isOpen hW heq α (List.finRange d) huW

/-- ★ **Vanishing off the prior**: an observable vanishing on the support of the prior has zero
coefficients, since then `Z_N[f] ≡ 0`. -/
theorem observableCoeff_eq_zero_of_prior_mul_eq_zero (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (h : ∀ y, X.prior y * f y = 0) : X.observableCoeff μ q f hf = 0 := by
  have hZ : partitionObs X.K X.prior f = fun _ => 0 := by
    funext N
    unfold partitionObs
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    change X.prior y * f y * Real.exp (-N * X.K y) = 0
    rw [h y, zero_mul]
  exact SmoothExpansionCertificate.coeff_eq (X.obsCertificate hf)
    (SmoothExpansionCertificate.zero.congr (Filter.EventuallyEq.of_eq hZ.symm)) μ q

theorem observableCoeff_eq_zero_of_disjoint_prior (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ (tsupport X.prior)ᶜ) :
    X.observableCoeff μ q f hf = 0 := by
  refine X.observableCoeff_eq_zero_of_prior_mul_eq_zero μ q hf fun y => ?_
  by_cases hy : y ∈ tsupport X.prior
  · rw [image_eq_zero_of_notMem_tsupport fun h => hsupp h hy, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

end BridgeInputs

end SmoothEngine

end Grammar
