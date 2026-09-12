# Consult #100 — design of phase G: signed coordinates `[−a,a]^d` (both sides of every divisor)

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 636 modules, zero sorry/axiom, all theorems below axiom-clean), companion to
*Grammar (Expectations and the Exceptional Divisor)* (Gerraty–Murfet 2026). Your consult #99 audited phase 3
(passed), and its recommended hygiene phase has LANDED: CCCXXXIII (`HasCoordFreeExpansion.congr`: the
expansion depends on `(ϕ,φ)` only through the integral over `W` and the `ν_I`-a.e. germs of `φ`;
`ResolvedCertificate.ae_stratumMeasure`: pointwise properties of the compact bases hold a.e. for the
stratum measures), CCCXXXIV (measurable representatives `1_U·Re H∘complexify` on the real domain
`U = complexify⁻¹ Ω`; ★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_local k hk A hd ha hϕ0W` with
ONLY the packet, `0<d`, `0<a`, prior `≥ 0` on the box; named produced certificates
`producedCertificate`/`producedCoeffCertificate`), CCCXXXV (polynomial instances: `ofPolynomials P Q`,
`flatPolynomial Q`, ★★ `hasCoordFreeExpansion_polynomial`, ★★ `hasCoordFreeExpansion_flat_polynomial`).
Your stopping gate for that phase is met. (Engineering note for future designs: a `▸`-cast proof term used as
an ARGUMENT of a data-valued certificate makes the kernel time out when two statements are compared — it
tries to reduce the equality proof — so certificate statements now use named proof constants such as
`integrable_posPart`.)

You ranked **(iii) G: signed boxes** as the next investment, with the finite reflection cover
`R_ε(u)_i = ε_i u_i`, `ε ∈ {±1}^d`. This consult asks for the precise design of G: the target statement, the
assembly mechanism, the unit breakdown, Mathlib routes, pitfalls, and a stopping gate.

## 1. What exists (coordinate model)

* Geometry on ALL of `ℝ^d`: `CoordModel.geometry d k h hk : ResolvedGeometry d (Fin d → ℝ)` with `π = id`,
  components `E_i = {u : u_i = 0}`, so the strata `S_I = {u : u_i = 0 ⇔ i ∈ I}` are the full coordinate
  hyperplane arrangement (NOT restricted to the box). Phase `CoordModel.phase d k w = ∏ i, w i ^ (2 * k i)`
  (even in every coordinate). Normal data `normalData d k h hk`: `N_I = span{e_i : i ∈ I} ⊆ Amb d`
  (`Amb d = EuclideanSpace ℝ (Fin d)`), conormal differentials `du_i`, tubular germ `Φ_I s v = s + v`.
* `HasCoordFreeExpansion ν B spec W K ϕ φ : Prop :=
    ∀ A : ℝ, (fun n => globalLaplace W K (fun w => φ w * ϕ w) n − ∑ q ∈ spec A, D.expansionCoefficient ν B φ q * q.scale n) =o[atTop] fun n => n^(−A)`
  with `globalLaplace W K a t = ∫ w in W, a w * exp(−t K w)`,
  `expansionCoefficient ν B φ q = ∑ I, ∫ s, ∑' r, (r!)⁻¹ * (B I r q s).pair (D.normalDifferential φ I s r) ∂ν I`,
  `normalDifferential φ I s r = iteratedFDeriv ℝ r (fun n : N_I s => φ (π (Φ_I s n))) 0 : JetForm (N_I s) r`
  (`JetForm V r = ContinuousMultilinearMap ℝ (fun _ : Fin r => V) ℝ`), `MomentTensor V r = JetForm V r →L[ℝ] ℝ`,
  `B : D.MomentCoefficientField = ∀ I r, PowerLogIndex → ∀ s : Stratum I, MomentTensor (N_I s) r`,
  `spec : ℝ → Finset PowerLogIndex`, `q.scale n = n^(−q.α) (log n)^q.j`.
* The positive-box producer (CCCXXIV–CCCXXXV): for `A : HolomorphicBoxExtension a ϕ φ` (open `Ω ⊆ ℂ^d ⊇`
  complexified box `[0,a]^d`, holomorphic `Hϕ Hφ`, `ϕ = Re Hϕ∘complexify` on the real slice), `0<d`, `0<a`,
  `∀ w ∈ [0,a]^d, 0 ≤ ϕ w`:
  `∃ δ hδ hδa hsmall, HasCoordFreeExpansion (producedCertificate …).stratumMeasure (producedCoeffCertificate …).field (spectrumLe (commonQ (producedCertificate …).cores.k) (d−1)) (piBox d (Icc 0 a)) (phase d k) ϕ φ`.
  The stratum measures are supported on the compact bases inside the box (`ae_stratumMeasure_mem_box`), the
  spectrum is `{(α, j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ d−1}` with `Q = commonQ (cores.k)` (depends only on `k`, so is
  the same for every reflected copy — please confirm this reading: `commonQ` is a common lattice of the
  cores' exponents `k`, which are the `k_i`, `i ∈ I`, of each stratum).
* Congruence: `HasCoordFreeExpansion.congr (hW : MeasurableSet W) (hprod : ∀ w ∈ W, φ' w * ϕ' w = φ w * ϕ w) (hgerm : ∀ I, ∀ᵐ s ∂ν I, φ' =ᶠ[𝓝 (π s)] φ) : HasCoordFreeExpansion ν B spec W K ϕ' φ' → HasCoordFreeExpansion ν B spec W K ϕ φ`;
  `normalDifferential_congr`, `expansionCoefficient_congr`; `rawNormalJet_congr` (in `Φ`).
* Existing reflection material: `OrthantReflection.lean` (from the resolution-input chain — a coordinate
  reflection of the integral over orthants, statement below) and `posPart`.

## 2. Questions

1. **Target statement.** Propose the exact Lean-level statement of the signed-box theorem. Candidates:
   (a) `HasCoordFreeExpansion ν B spec (piBox d (Icc (−a) a)) (phase d k) ϕ φ` with a SINGLE assembled
   `ν = ∑_ε (R_ε)_* ν_ε` and a single field `B` defined piecewise by the sign pattern of `s` off `I` (on the
   stratum `S_I` the coordinates off `I` are nonzero, so the reflected bases `R_ε(K_I)` for distinct `ε|_{Iᶜ}` are
   DISJOINT — is that right, and does it make `B(s) := (R_ε)_* B_ε(R_ε s)` well defined and measurable?), with the
   sign transformation of the moment tensors (the normal differentials of `φ` at `R_ε s` and of `φ∘R_ε` at `s`
   differ by `(R_ε|_{N_I})^{⊗r}`); versus (b) a weaker "sum of expansions" statement; versus (c) an even/odd
   decomposition. Which should the library state, and what exactly does the paper want here?
2. **Assembly lemma.** Is there a clean general lemma "finite a.e.-disjoint decomposition of `W` into pieces
   each with an expansion on a COMMON spectrum ⇒ expansion on `W` with summed `ν` and glued `B`"? What
   hypotheses (measurability of the pieces, null overlaps, disjointness of the supports of the stratum measures
   so that the glued `B` is unambiguous)? Should `B` be glued via `Set.piecewise`/indicator on the strata or via
   a `Finset.sum` of fields each multiplied by indicator functions (the coefficient is linear in `B`)?
3. **Transport of a certificate along a reflection** vs transport of the EXPANSION: it is much cheaper to
   transport the expansion statement (a Prop about integrals and stratum integrals) than the certificate
   structure. Confirm that G should transport expansions, not certificates, and list the exact identities:
   change of variables `∫_{R_ε W} f = ∫_W f∘R_ε` (Lebesgue is reflection-invariant), stratum-measure pushforward
   `∫ g d((R_ε)_*ν) = ∫ g∘R_ε dν`, and the jet identity `normalDifferential φ I (R_ε s) r = (normalDifferential (φ∘R_ε) I s r) ∘ (R_ε|_{N_I})^{⊗r}`
   (with `R_ε` mapping `S_I` to itself and `N_I` to itself).
4. **Pullback of the analytic packet**: `HolomorphicBoxExtension a (ϕ∘R_ε) (φ∘R_ε)` from
   `HolomorphicBoxExtension` over the SIGNED box (open `Ω ⊇ complexify [−a,a]^d`), via the complex-linear
   reflection — trivial? Also `posPart` commutes with `R_ε` (`(ϕ⁺)∘R_ε = (ϕ∘R_ε)⁺`), but the hygiene theorem
   only needs `ϕ ≥ 0` on the signed box, so is `posPart` needed at all in G?
5. **Mathlib routes**: reflection as `LinearIsometryEquiv`/`MeasurableEquiv` on `Fin d → ℝ`
   (`MeasurePreserving` for `volume` — e.g. via `MeasureTheory.Measure.map_pi`/`volume_preserving_piCongrLeft`
   or `Measure.IsAddHaarMeasure` and `map_linearMap_addHaar_eq_smul_addHaar` with `|det| = 1`), the cover
   `[−a,a]^d = ⋃_ε R_ε [0,a]^d` with overlaps in `⋃_i {w_i = 0}` (Lebesgue-null: `volume_pi_… ` / `Measure.addHaar_submodule`?),
   `Finset.sum` of `IsLittleO`s, and `iteratedFDeriv` under composition with a continuous linear map
   (`ContinuousLinearMap.iteratedFDeriv_comp_right`? we have used `iteratedFDerivWithin_comp_right` on open sets).
6. **Unit plan** (4–6 units per your estimate): statements, dependencies, sizes, pitfalls; a stopping gate; and
   what the paper may then claim (the two-sided coordinate model as the local model for a real divisor).

## 3. Material

### OrthantReflection.lean (existing)
```lean
30:def signReflect (s : Fin d → ℝ) (y : Fin d → ℝ) : Fin d → ℝ := fun i => s i * y i
33:def signReflectLinear (s : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
36:theorem reflectLinear_apply (s y : Fin d → ℝ) : signReflectLinear s y = signReflect s y := by
40:theorem measurable_signReflect (s : Fin d → ℝ) : Measurable (signReflect s) :=
43:theorem signReflect_signReflect {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) (y : Fin d → ℝ) :
52:theorem det_diagonal_abs_eq_one {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) :
58:theorem map_signReflect_volume {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) :
68:theorem mono_signReflect_of_even {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) {e : Fin d → ℕ}
78:def absMono (h : Fin d → ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, |y i| ^ h i
80:theorem absMono_signReflect {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) (h : Fin d → ℕ) (y : Fin d → ℝ) :
86:theorem absMono_eq_mono_of_pos {h : Fin d → ℕ} {y : Fin d → ℝ} (hy : ∀ i, 0 ≤ y i) :
91:theorem measurable_absMono (h : Fin d → ℕ) : Measurable (absMono h) :=
97:def signReflectBox (s : Fin d → ℝ) (B : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := signReflect s ⁻¹' B
101:theorem map_signReflect_weightedPosBox {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) {B : Set (Fin d → ℝ)}
```

### CoordinateResolvedGeometry.lean (geometry, phase, normal data)
```lean
namespace CoordModel

variable (d : ℕ) (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i)

/-- The monomial phase `K(u) = ∏ u_i^{2k_i}`. -/
def phase (w : Fin d → ℝ) : ℝ := ∏ i, w i ^ (2 * k i)

omit h hk in
theorem phase_nonneg (w : Fin d → ℝ) : 0 ≤ phase d k w :=
  Finset.prod_nonneg fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

omit h hk in
theorem measurable_phase : Measurable (phase d k) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

omit h hk in
theorem continuous_phase : Continuous (phase d k) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

/-- **The coordinate model geometry**: `ℝ^d`, `π = id`, components `{u_i = 0}`, orders `k, h`. -/
noncomputable def geometry : ResolvedGeometry d (Fin d → ℝ) where
  π := id
  continuous_π := continuous_id
  proper_π := isProperMap_id
  Component := Fin d
  E := fun i => {u : Fin d → ℝ | u i = 0}
  isClosed_E := fun i => isClosed_eq (continuous_apply i) continuous_const
  k := k
  h := h
  k_pos := hk

/-! ### Normal data -/

/-- The ambient Euclidean space. -/
abbrev Amb := EuclideanSpace ℝ (Fin d)

/-- The coordinate vector `e_i`. -/
noncomputable def basisVec (i : Fin d) : Amb d := EuclideanSpace.single i 1

omit k h hk in
theorem basisVec_eq : basisVec d = ⇑(EuclideanSpace.basisFun (Fin d) ℝ) := by
  funext i
  simp [basisVec, EuclideanSpace.basisFun_apply]

omit k h hk in
theorem linearIndependent_basisVec : LinearIndependent ℝ (basisVec d) := by
  rw [basisVec_eq]
  exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.linearIndependent

/-- The normal space of `S_I`: `span{e_i : i ∈ I}`. -/
noncomputable def normalSpace (I : Finset (Fin d)) : Submodule ℝ (Amb d) :=
  Submodule.span ℝ (Set.range fun i : I => basisVec d (i : Fin d))

omit k h hk in
theorem linearIndependent_basisVec_restrict (I : Finset (Fin d)) :
    LinearIndependent ℝ fun i : I => basisVec d (i : Fin d) :=
  (linearIndependent_basisVec d).comp _ Subtype.val_injective
    exact absurd (Finset.mem_univ j) hj

/-- **The normal data of the coordinate model**: `N_I = span{e_i : i ∈ I}`, coordinate conormal
differentials, tubular germ `Φ_s(v) = s + v`. -/
noncomputable def normalData : ResolvedNormalData (geometry d k h hk) (Amb d) where
  N := fun I _ => normalSpace d I
  finrank_N := fun I _ => finrank_normalSpace d I
  finiteDimensional_N := fun _ _ => inferInstance
  du := fun I _ => du d I
  du_linearIndependent := fun I _ => linearIndependent_du d I
  Φ := fun _ s v => fun i => s.1 i + (v : Amb d) i
  Φ_zero := fun _ s => by
    funext i
    simp
  continuousAt_Φ := fun _ _ =>
    (continuous_pi fun i => continuous_const.add
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val)).continuousAt

theorem normalData_Φ (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I)
    (v : normalSpace d I) : (normalData d k h hk).Φ I s v = fun i => s.1 i + (v : Amb d) i := rfl

```

### ResolvedNormalData.lean (jets, coefficients, expansion)
```lean
/-! ### Moment tensors -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Moment tensors** of degree `r` on `V`: the continuous dual of the `r`-forms (the pairing
representation of `Sym^r V`). -/
abbrev MomentTensor (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (r : ℕ) : Type _ :=
  JetForm V r →L[ℝ] ℝ

namespace MomentTensor

/-- The pairing `⟨D, M⟩ = M(D)`. -/
noncomputable def pair {r : ℕ} (M : MomentTensor V r) (D : JetForm V r) : ℝ := M D

theorem pair_add {r : ℕ} (M : MomentTensor V r) (D D' : JetForm V r) :
    M.pair (D + D') = M.pair D + M.pair D' := map_add M D D'

theorem pair_smul {r : ℕ} (M : MomentTensor V r) (c : ℝ) (D : JetForm V r) :
    M.pair (c • D) = c * M.pair D := map_smul M c D

theorem add_pair {r : ℕ} (M M' : MomentTensor V r) (D : JetForm V r) :
    (⨁ i : I, D.conormalLine I s i) ≃ₗ[ℝ] Grammar.conormalOf (D.du I s) :=
  Grammar.conormalSplitting (D.du I s) (D.du_linearIndependent I s)

/-- **The normal differential** `D^r_⊥(φ∘π)(s) = D^r((φ∘π)∘Φ_s)(0)` of an observable on the
parameter space, along the stratum `S_I`. -/
noncomputable def normalDifferential (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component)
    (s : R.Stratum I) (r : ℕ) : JetForm (D.N I s) r :=
  Grammar.normalDifferential (D.N I) (D.Φ I) (φ ∘ R.π) s r

/-- Degree zero is the value of the observable at the image point. -/
theorem normalDifferential_zero (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component) (s : R.Stratum I)
    (m : Fin 0 → D.N I s) : D.normalDifferential φ I s 0 m = φ (R.π s) := by
  unfold normalDifferential
  rw [normalDifferential_zero_apply, Function.comp_apply, D.Φ_zero]

/-! ### Stratum coefficients and the expansion coefficient -/

variable [MeasurableSpace U]

/-- **A moment coefficient field**: for every stratum, degree and power–log index, a moment tensor
at each point of the stratum. -/
abbrev MomentCoefficientField : Type _ :=
  ∀ (I : Finset R.Component) (r : ℕ), PowerLogIndex → ∀ s : R.Stratum I, MomentTensor (D.N I s) r

/-- **The stratum coefficient** `(1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π)(s), B(s)⟩ dν_I(s)`. -/
noncomputable def stratumCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component) (r : ℕ)
    (B : ∀ s : R.Stratum I, MomentTensor (D.N I s) r) : ℝ :=
  (r.factorial : ℝ)⁻¹ * ∫ s, (B s).pair (D.normalDifferential φ I s r) ∂ν I

/-- **The expansion coefficient of a power–log index**: the sum over the strata of the stratum
integrals of the normal-order series `∑_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩`. (The series is
summed pointwise inside the stratum integral: at a tied crossing the normal order is not locally
finite, and the pointwise series is the object the fibre analysis controls; when the summands are
integrable with summable integrals this is `∑_I ∑_r stratumCoefficient`.) -/
noncomputable def expansionCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) : ℝ :=
  ∑ I : Finset R.Component, ∫ s, ∑' r : ℕ,
    (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential φ I s r) ∂ν I

/-- ★ **The coordinate-free expansion** of the original integral `∫_W φ ϕ e^{−nK}`: for every cutoff
`A`, subtracting the terms `expansionCoefficient(q) · n^{−α}(log n)^j` over the finite index set
`spec A` leaves `o(n^{−A})`. The index sets `spec A` are an indexing envelope supplied together with
the expansion (no spectral condition is imposed on them here; the truncation to exponents `≤ A` is a
corollary, `hasCoordFreeExpansion_le`). The coefficient formula uses only the strata, the normal
differentials, the moment-tensor coefficient fields, the stratum densities and `π`. -/
def HasCoordFreeExpansion (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (spec : ℝ → Finset PowerLogIndex) (W : Set (Fin d → ℝ))
    (K ϕ φ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ A : ℝ, (fun n : ℝ => globalLaplace W K (fun w => φ w * ϕ w) n -
      ∑ q ∈ spec A, D.expansionCoefficient ν B φ q * q.scale n) =o[atTop]
    fun n : ℝ => n ^ (-A)

/-- The stratum coefficient at degree `0` is an ordinary stratum integral of the observable: the
leading-measure shape. -/
theorem stratumCoefficient_zero (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
```

### ResolvedCoordFreeExpansion.lean (stratum measures of a certificate)
```lean
theorem measurableEmbedding_val (J : Fin C.M) :
    MeasurableEmbedding (Subtype.val : ↥(C.base J) → R.Stratum (C.strat J)) :=
  MeasurableEmbedding.subtype_coe (C.measurableSet_base J)

/-- The pushforward of the chart base measure to its stratum. -/
noncomputable def pushedMeasure (J : Fin C.M) : Measure (R.Stratum (C.strat J)) :=
  (C.cores.ν J).map Subtype.val

instance (J : Fin C.M) : IsFiniteMeasure (C.pushedMeasure J) := Measure.isFiniteMeasure_map _ _

/-- Transport of a measure along an identification of strata. -/
def transportMeasure {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (μ : Measure (R.Stratum (C.strat J))) : Measure (R.Stratum I) := by
  subst hJ
  exact μ

    (hJ : C.strat J = I) (μ : Measure (R.Stratum (C.strat J))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.transportMeasure hJ μ) :=
  ⟨by rw [C.transportMeasure_univ]; exact measure_lt_top _ _⟩

/-- **The stratum density** `ν_I`: the sum over the charts presenting `S_I` of the pushforwards
of their base measures. -/
noncomputable def stratumMeasure (I : Finset R.Component) : Measure (R.Stratum I) :=
  ∑ J, if hJ : C.strat J = I then C.transportMeasure hJ (C.pushedMeasure J) else 0

instance (I : Finset R.Component) : IsFiniteMeasure (C.stratumMeasure I) := by
  refine ⟨?_⟩
  unfold stratumMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J _ => ?_
  split_ifs with hJ
  · rw [C.transportMeasure_univ]
    exact measure_lt_top _ _
  · simp

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem pushed_le {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I) :
```

### ExpansionCongruence.lean (CCCXXXIII, full)
```lean
(`ResolvedCertificate.ae_stratumMeasure`); for the compact-box certificate the bases lie in the
box (`mem_box_of_mem_baseStratum`, `ae_stratumMeasure_mem_box`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section rawJet

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
  [TopologicalSpace M]

/-- Two functions agreeing near `Φ_s 0` have the same raw normal jets at `s`. -/
theorem rawNormalJet_congr_fun (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) {F F' : M → ℝ} (s : S)
    (hΦ : ContinuousAt (Φ s) 0) (h : F' =ᶠ[𝓝 (Φ s 0)] F) (r : ℕ) :
    rawNormalJet N Φ F' s r = rawNormalJet N Φ F s r := by
  unfold rawNormalJet
  have := ((h.comp_tendsto hΦ).iteratedFDeriv (𝕜 := ℝ) r).eq_of_nhds
  exact this

end rawJet

section normalData

variable {d : ℕ} {U : Type*} [TopologicalSpace U] {R : ResolvedGeometry d U} {A : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] (D : ResolvedNormalData R A)

namespace ResolvedNormalData

/-- **Normal differentials depend only on the germ of the observable at `π s`.** -/
theorem normalDifferential_congr {φ φ' : (Fin d → ℝ) → ℝ} (I : Finset R.Component)
    (s : R.Stratum I) (h : φ' =ᶠ[𝓝 (R.π s)] φ) (r : ℕ) :
    D.normalDifferential φ' I s r = D.normalDifferential φ I s r := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential
  apply rawNormalJet_congr_fun _ _ _ (D.continuousAt_Φ I s)
  rw [D.Φ_zero]
  exact h.comp_tendsto R.continuous_π.continuousAt

variable [MeasurableSpace U]

/-- **Expansion coefficients depend only on the `ν_I`-a.e. germs of the observable.** -/
theorem expansionCoefficient_congr (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) {φ φ' : (Fin d → ℝ) → ℝ}
    (h : ∀ I, ∀ᵐ (s : R.Stratum I) ∂ν I, φ' =ᶠ[𝓝 (R.π (s : U))] φ) (q : PowerLogIndex) :
    D.expansionCoefficient ν B φ' q = D.expansionCoefficient ν B φ q := by
  unfold ResolvedNormalData.expansionCoefficient
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae ?_
  filter_upwards [h I] with s hs
  exact tsum_congr fun r => by rw [D.normalDifferential_congr I s hs r]

variable {D} in
/-- ★ **Congruence of the coordinate-free expansion**: the expansion transfers between pairs
`(ϕ', φ')` and `(ϕ, φ)` whose products agree on `W` and whose observables have the same germs
`ν_I`-a.e. on every stratum. -/
theorem HasCoordFreeExpansion.congr {ν : ∀ I : Finset R.Component, Measure (R.Stratum I)}
    {B : D.MomentCoefficientField} {spec : ℝ → Finset PowerLogIndex} {W : Set (Fin d → ℝ)}
    {K ϕ φ ϕ' φ' : (Fin d → ℝ) → ℝ} (hW : MeasurableSet W)
    (hprod : ∀ w ∈ W, φ' w * ϕ' w = φ w * ϕ w)
    (hgerm : ∀ I, ∀ᵐ (s : R.Stratum I) ∂ν I, φ' =ᶠ[𝓝 (R.π (s : U))] φ)
    (h : D.HasCoordFreeExpansion ν B spec W K ϕ' φ') :
    D.HasCoordFreeExpansion ν B spec W K ϕ φ := by
  intro A
  have hL : ∀ n : ℝ, globalLaplace W K (fun w => φ w * ϕ w) n =
      globalLaplace W K (fun w => φ' w * ϕ' w) n := fun n => by
    unfold globalLaplace
    exact setIntegral_congr_fun hW fun w hw => by simp only [hprod w hw]
  have hc : ∀ q, D.expansionCoefficient ν B φ q = D.expansionCoefficient ν B φ' q :=
    fun q => (D.expansionCoefficient_congr ν B hgerm q).symm
  simp only [hL, hc]
  exact h A

end ResolvedNormalData

end normalData

section certificate

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)}
  {K ϕ φ : (Fin d → ℝ) → ℝ}

namespace ResolvedCertificate

variable (C : ResolvedCertificate R D W K ϕ φ)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- Transport along an identification of strata preserves a.e. properties of the underlying
points. -/
theorem ae_transportMeasure {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (μ : Measure (R.Stratum (C.strat J))) {P : U → Prop}
    (h : ∀ᵐ (s : R.Stratum (C.strat J)) ∂μ, P (s : U)) :
    ∀ᵐ (s : R.Stratum I) ∂C.transportMeasure hJ μ, P (s : U) := by
  subst hJ
  exact h

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Pointwise properties of the bases hold a.e. for the stratum measures**: the stratum
measure is a sum of pushforwards of the base measures. -/
theorem ae_stratumMeasure {P : U → Prop} (hP : MeasurableSet {u | P u})
    (hbase : ∀ (J : Fin C.M) (t : ↥(C.base J)), P (t.1 : U)) (I : Finset R.Component) :
    ∀ᵐ (s : R.Stratum I) ∂C.stratumMeasure I, P (s : U) := by
  have hP' : ∀ J : Finset R.Component, MeasurableSet {s : R.Stratum J | P (s : U)} :=
    fun J => hP.preimage measurable_subtype_coe
  unfold stratumMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff' (hP' I)]
  intro J
  split_ifs with hJ
  · refine C.ae_transportMeasure hJ _ ?_
    unfold pushedMeasure
    rw [ae_map_iff measurable_subtype_coe.aemeasurable (hP' _)]
    exact Eventually.of_forall fun t => hbase J t
  · simp

end ResolvedCertificate

end certificate

namespace WaterFilling

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ)

/-- The compact bases of the collar lie in the box. -/
theorem mem_box_of_mem_baseStratum (ha : 0 < a) (I : Finset (Fin d)) (s : KI k hk a δ I) :
    (s.1 : Fin d → ℝ) ∈ piBox d (Icc 0 a) := by
  intro i _
  by_cases hi : i ∈ I
  · have h0 : (s.1 : Fin d → ℝ) i = 0 := (s.1.2 i).2 hi
    rw [h0]
    exact ⟨le_rfl, ha.le⟩
  · have ht := s.2 ⟨i, hi⟩
    exact ⟨ht.1, ht.2.1⟩

variable (hδ : 0 < δ) (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
  (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I)

/-- ★ **The stratum measures of the compact-box certificate live in the box.** -/
theorem ae_stratumMeasure_mem_box (I : Finset (Fin d)) :
    ∀ᵐ (s : (CoordModel.geometry d k (zeroOrders d) hk).Stratum I)
      ∂(certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).stratumMeasure I,
      (s : Fin d → ℝ) ∈ piBox d (Icc 0 a) :=
  (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).ae_stratumMeasure (measurableSet_W a)
    (fun _ t => mem_box_of_mem_baseStratum k hk a δ ha _ t) I

end WaterFilling

end Grammar
```

### LocalAnalyticInputs.lean (CCCXXXIV): the produced certificates and the local-input theorem
```lean
    mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _) (mem_ae_iff.1 (ae_restrict_mem hW)))
  filter_upwards [hae] with w hw
  exact hBφ w hw

end HolomorphicBoxExtension

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (A : HolomorphicBoxExtension a ϕ φ) (hd : 0 < d)
  (ha : 0 < a) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)

/-- **The produced certificate**: the compact-box certificate of the positive part of the prior
representative and the observable representative at collar level `δ`, from the face series of
the representatives' packet. -/
noncomputable def producedCertificate :
    ResolvedCertificate (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk)
      (piBox d (Icc 0 a)) (CoordModel.phase d k) (posPart A.priorRep) A.obsRep :=
  certificate k hk a δ hδ (posPart A.priorRep) A.obsRep (measurable_posPart A.measurable_priorRep)
    (posPart_nonneg A.priorRep)
    (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa fun I =>
      ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd
        ha hδa (A.priorRep_nonneg_on hϕ0W)

/-- **The produced coefficient certificate.** -/
noncomputable def producedCoeffCertificate :
    (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).CoefficientCertificate :=
  coeffCertificate k hk a δ hδ (posPart A.priorRep) A.obsRep
    (measurable_posPart A.measurable_priorRep) (posPart_nonneg A.priorRep)
    (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa fun I =>
      ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd
        ha hδa (A.priorRep_nonneg_on hϕ0W)

omit δ hδ hδa hsmall in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box, with local inputs
only**: the hypotheses are the extension packet, `0 < d`, `0 < a` and nonnegativity of the prior
on the box. For some collar level `δ`, the original integral `∫_{[0,a]^d} φ ϕ e^{−nK}` has the
coordinate-free expansion with the stratum measures and the coefficient field of the produced
certificates (`producedCertificate`, `producedCoeffCertificate`). -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension_local :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).stratumMeasure
        (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).field
        (spectrumLe (commonQ (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).cores.k)
          (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  obtain ⟨δ, hδ, hδa, hsmall, h⟩ :=
    hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on a k hk A.priorRep A.obsRep
      A.toRep hd ha A.measurable_priorRep A.measurable_obsRep A.integrable_obsRep
      (A.priorRep_nonneg_on hϕ0W)
  refine ⟨δ, hδ, hδa, hsmall, ?_⟩
  refine h.congr (measurableSet_W a) ?_ ?_
  · intro w hw
    rw [A.obsRep_eq_of_mem (A.box_subset_realDomain hw),
      A.priorRep_eq_of_mem (A.box_subset_realDomain hw)]
  · intro I
    filter_upwards [ae_stratumMeasure_mem_box k hk a δ hδ (posPart A.priorRep) A.obsRep
      (measurable_posPart A.measurable_priorRep) (posPart_nonneg A.priorRep)
      (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa
      (fun I => ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k
        hk a δ hδ hd ha hδa (A.priorRep_nonneg_on hϕ0W)) I] with s hs
    exact eventually_of_mem (A.isOpen_realDomain.mem_nhds (A.box_subset_realDomain hs))
      fun w hw => A.obsRep_eq_of_mem hw

end WaterFilling

end Grammar
```

### HolomorphicBoxBuffer.lean: the packet
```lean
/-- **Holomorphic box extension**: holomorphic extensions of the prior and the observable on a
complex neighbourhood of the box, agreeing with them on its real slice. -/
structure HolomorphicBoxExtension (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the complex neighbourhood -/
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω
  /-- the holomorphic extensions -/
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re

```

### spectrumLe / commonQ
```lean
Grammar/ChartAssemblyGlobal.lean:118:def commonQ (k : (I : Fin M) → Fin (n I + 1) → ℕ) : ℕ := ∏ I, latticeQ (k I)
Grammar/ChartAssemblyGlobal.lean-119-
Grammar/ChartAssemblyGlobal.lean-120-theorem commonQ_pos (hk : ∀ I i, 0 < k I i) : 0 < commonQ k :=
Grammar/ChartAssemblyGlobal.lean-121-  Finset.prod_pos fun I _ => latticeQ_pos (k I) (hk I)
Grammar/ChartAssemblyGlobal.lean-122-
--
Grammar/ChartAssemblyGlobal.lean:127:def commonD (n : Fin M → ℕ) : ℕ := Finset.univ.sup n
Grammar/ChartAssemblyGlobal.lean-128-
Grammar/ChartAssemblyGlobal.lean-129-theorem le_commonD (I : Fin M) : n I ≤ commonD n := Finset.le_sup (Finset.mem_univ I)
Grammar/ChartAssemblyGlobal.lean-130-
Grammar/ChartAssemblyGlobal.lean-131-/-- The global integral `∑_I 𝒵^I(N; x_I)`. -/
--
Grammar/CoordFreeExpansionCompletion.lean:86:noncomputable def spectrumLe (Q Dg : ℕ) (A : ℝ) : Finset PowerLogIndex :=
Grammar/CoordFreeExpansionCompletion.lean-87-  (spectrumBelow Q Dg A).filter fun q => q.exponent ≤ A
Grammar/CoordFreeExpansionCompletion.lean-88-
Grammar/CoordFreeExpansionCompletion.lean-89-/-- A power–log term with exponent `α > A` is `o(n^{−A})`, whatever its log degree. -/
Grammar/CoordFreeExpansionCompletion.lean-90-theorem isLittleO_scale_of_lt {A α : ℝ} (hα : A < α) (j : ℕ) :
```
