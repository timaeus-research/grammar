# Consult #102 — E0: the obligation table for the cube blow-up (projector model in chart form) and the design of the weighted producer

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 643 modules, zero sorry/axiom). Phase G is closed (your audit #101; the G7
regression fixtures landed: `reflTensor_evalV_basis_pair`, `synthetic_cancellation` (odd observable → 0),
`synthetic_order_zero` (→ 2), `signedStratumMeasure_univ`). You asked for E0 next: the actual chart equations
and a compile-checked obligation table for the projector blow-up, before generalising any producer. Here is
what the library ALREADY has for that model, the E0 table as we read it, and the design questions.

## 1. What exists: the blow-up cover of the cube (CCLXXXIII–CCXCV, landed 2026-09-11/12)

Hironaka's standard blow-up of the origin of `ℝ^d` (`d ≥ 2`) in chart form, on the unit cube with the
quadratic phase `K(x) = ∑ x_i²`:
* charts `φ_β : ℝ^d → ℝ^d`, `φ_β(y)_β = y_β`, `φ_β(y)_γ = y_β y_γ` (`γ ≠ β`), analytic, `det Dφ_β = y_β^{d−1}`
  (`det_φ`, hironaka's axiom-clean `det_fderiv_blowUpChart`);
* `K ∘ φ_β = unit_β(y) · y_β²` with `unit_β(y) = 1 + ∑_{γ≠β} y_γ² ∈ [1, d]` on the cube — a positive analytic
  unit depending ONLY on the tangential coordinates `y_γ, γ ≠ β` (`K_φ`, `unit_pos`);
* each chart is a hironaka `IsMonomialChart K (φ β) (cube d) (expo β) (jexp β) univ` with `e = 2δ_β`,
  `h = (d−1)δ_β` (`isMonomialChart`); the divisor in chart `β` is `{y_β = 0}` only (`divisorSet_zero`);
* images = wedges `{|x_β| ≤ 1, |x_γ| ≤ |x_β| ∀γ}` (`image_eq`), covering the cube (`iUnion_wedge`), meeting on
  the null diagonals `{x_β = ±x_γ}` (`volume_wedge_inter`, via `Measure.addHaar_submodule`);
* the derived leading term ★★ `cubeIntegral_isEquivalent : ∫_{[−1,1]^d} F p e^{−N|x|²} ~ c N^{−d/2}` (all
  charts active with pair `(d/2, 0)`), ★★★ `coeff_eq_pi_rpow : c = π^{d/2}` for `F = p = 1` (CCLXXXIV),
  ★★★ `BlowUpCube.leadingMeasure_eq : leadingMeasure = π^{d/2} δ₀` (CCXCV) — the face pieces of every chart are
  pushed to the origin, and `hasLeadingMeasure_cube`, `tendsto_cube_laplace`.
So the chart-level change of variables, cover, null overlaps, Jacobian and unit are all in place at the level
of LEADING terms and leading measures. What does not exist: the FULL coordinate-free expansion (all orders,
strata measures + moment fields) for this geometry — the producer chain (CCCXVI–CCCXLII) is for the
coordinate monomial model `K = ∏ w_i^{2k_i}` on boxes with `zeroOrders`, all coordinates active (`0 < k_i`), no
unit.

## 2. E0 — the obligation table for chart `β` of the cube blow-up

| Obligation | Status / reading |
|---|---|
| blow-down map and domain | `φ_β`, domain the `y`-cube `[−1,1]^d` (a SIGNED box), image the wedge | done (CCLXXXIII) |
| coverage and null overlaps | `⋃_β wedge β = cube`, `volume (wedge β ∩ wedge γ) = 0` | done |
| change of variables | `∫_{wedge β} F p e^{−NK} = ∫_{cube} (F∘φ_β)(p∘φ_β)|y_β|^{d−1} e^{−N unit_β y_β²}` | done at chart level (hironaka `ofChart_sourceChartIntegral`) |
| exact phase pullback | `K∘φ_β = unit_β(y') · y_β²`: ONE active coordinate `y_β` with `k_β = 1`; unit purely TANGENTIAL | done (`K_φ`) |
| Jacobian and order family | `|det Dφ_β| = |y_β|^{d−1}`: `h_β = d − 1`, `h_γ = 0`; even in `y_β` iff `d` odd; on each orthant `= y_β^{d−1}` | done (`det_φ`) |
| active normal vs tangential coordinates | active `A = {β}`; the `d − 1` coordinates `y_γ` are tangential and INACTIVE (`K` does not vanish on `{y_γ = 0}`) | the coordinate model has no inactive coordinates: `geometry d k h hk` makes every `{w_i = 0}` a component and requires `0 < k_i` |
| transformed analytic packets | `F, p` analytic near the cube ⇒ `F∘φ_β`, `p∘φ_β` analytic (polynomial composition); on the orthant `σ` of the `y`-cube the weighted prior `y_β^{d−1}·(p∘φ_β∘R_σ)` is analytic with a holomorphic representative | routine (CCCXXIX/CCCXXXVI style) |
| unit absorption | the water-filling collar already carries tangentially varying normal widths `λ_I(s)` with the normalisation `tanUnit(s)·∏λ^{2k} = β` (`NormalisedBox.Data.hnorm`); a tangential unit `u(s)` can enter the same identity `u(s)·tanUnit(s)·∏λ^{2k} = 1` | mechanism exists; not wired |
| spectrum | `(h + 1 + m)/(2k) = (d + m)/2`, leading `d/2`, log degree `0` | consistent with CCLXXXIII |
| global resolved space | the honest projector blow-up `U = {(x, P) : P ∈ 𝒫₁, Px = x}` (your #92 §4.2) is NOT constructed; the strata of the `d` charts are not glued into the exceptional divisor | open |

## 3. Design questions

1. **The chart model.** The producer chain must be generalised from the coordinate model to a *chart model*:
   active set `A ⊆ Fin d` with `k_i > 0` for `i ∈ A`, orders `h_i` for `i ∈ A`, phase `u(y_tan)·∏_{i∈A} y_i^{2k_i}`
   with a positive analytic TANGENTIAL unit `u`, Jacobian weight `∏_{i∈A} |y_i|^{h_i}`, on a signed box; strata
   indexed by `I ⊆ A`; normal spaces `span{e_i : i ∈ I}`; tangential coordinates `Fin d \ I` (inactive ones
   always tangential). Is this the right generality for E (and for the charts of a general real SNC resolution
   with tangential units), or should the unit be allowed to depend on the normal coordinates (then it cannot be
   absorbed by tangential widths)? Please give the precise structure/fields.
2. **Which existing modules change.** Our reading: `CoordinateResolvedGeometry` (`geometry`, `normalData`:
   components `A`), `WaterFillingCollar` (`tanUnit` over active tangential coordinates only; `q_I`, `ell`, `side`,
   `lamT` with the unit), `CollarDecomposition` (covering of `{u·∏y^{2k} < δ}`, thresholds), `NormalisedBoxCore`
   (`core.h := fun _ => 0` → the order family; `chartDensity h c` already carries `∏ v^h`; the transport identity
   picks up `∏ λ_i^{h_i}` into the amplitude `c`), `CoordinateBoxCertificate/Inputs/NormalCompatibility`
   (bases inside strata of `A`), the analytic bridge (CCCXXVIII–CCCXXXII: face series in the normal
   variables of `I ⊆ A` — unchanged in mechanism), and G (`refl σ` on all coordinates; the weight `|y_i|^{h_i}`
   even under reflection). The certificate consumers (`ResolvedCertificate`, `CoefficientCertificate`,
   `expansionCoefficient`, `HasCoordFreeExpansion`, `hasCoordFreeExpansion_le`) are generic in `R, D`. Do you
   agree; what are the hidden `Fin d = A` assumptions to look for (e.g. `Finset.univ` as the deepest stratum,
   `numCores d`, `NonemptyIdx d`, `σI I : Fin (nI I + 1) ≃ ↥I`)?
3. **E1 pilot vs E2–E3.** Your E1 (absorb `∏ y^h` into the prior orthantwise, zero-order geometry) is blocked
   by the inactive coordinates: the current signed-box theorem cannot be applied to chart `β` because
   `y_γ` are not active. Is there a cheaper pilot that is not blocked — e.g. `d = 2` only? (For `d = 2` the
   chart is `(y_β, y_γ) ↦ (y_β, y_β y_γ)`, one inactive coordinate; still blocked.) Or should E1 be replaced by
   "E1′ = the chart model with `h = 0` and a tangential unit but WITH inactive coordinates", i.e. do the
   generalisation of the geometry first and the orders second? Please order the steps by risk.
4. **Absorbing `|y_β|^{d−1}` vs recording `h`.** For the paper's certified resolved geometry the certificate
   should record `h = d − 1` (target 2). How much of `NormalisedBoxCore`'s transport proof (`map_Φ`,
   `density_ae`, `c_eq_of_mem_box`, `presentation`'s `cBound`) changes when `h ≠ 0` — the density becomes
   `J(s)·∏λ_i(s)^{h_i}·∏v_i^{h_i}·ϕ`, and `chartDensity h c` already has the `∏ v^h` factor, so is it only the
   amplitude `c := J·∏λ^h·fϕ` and the `Mellin`/`dataBoxCoeff` pole arithmetic (`(h_i + 1 + m_i)/(2k_i)`) that
   need touching, with the spectrum lattice `commonQ` unchanged (same denominators)?
5. **Gluing the `d` charts.** After each chart has its coordinate-free expansion on its own `y`-cube with its own
   strata `{y_β = 0} ≅ ℝ^{d−1}`, the ORIGINAL integral over the cube is the sum over `β` (a.e.-disjoint wedges).
   To state a coordinate-free expansion on a resolved space `U`, the chart strata must be identified with
   pieces of the exceptional divisor `E ≅ ℝℙ^{d−1}`. Minimal honest option: define `U` as the disjoint union of
   the `d` chart cubes modulo nothing (a "chart atlas geometry") with a.e.-disjoint images — you said in #92 this
   is not the projective blow-up. Is a statement on the disjoint-union geometry acceptable as E5 for the paper
   ("the assembled chart expansions"), with the honest projector space as a later gluing step? What is the
   cheapest route to a theorem about the ORIGINAL cube integral with all orders and strata-integral
   coefficients?
6. Unit plan with sizes and gates for what you recommend as the next 4–6 units.

## 4. Material

### CoordinateResolvedGeometry.lean (geometry, normal data)
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

### NormalisedBoxCore.lean: Data and core (the λ mechanism, h := 0)
```lean
compact base, positive normal widths with the normalisation identity, and uniform normal-series
families for the prior and the observable in the normalised normal variables. -/
structure Data (k : Fin d → ℕ) (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
    (W : Set (Fin d → ℝ)) (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the identification of box coordinates with the normal coordinates -/
  σ : Fin (n + 1) ≃ Nrm I
  /-- the tangential coordinates of the base -/
  e : K → (Tan I → ℝ)
  he : Continuous e
  he_inj : Function.Injective e
  /-- the normal widths -/
  lamT : (Tan I → ℝ) → (Nrm I → ℝ)
  hlamT : Measurable lamT
  hlam_cont : ContinuousOn lamT (range e)
  hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j
  /-- the normalised unit -/
  β : ℝ
  hnorm : ∀ t ∈ range e, tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β
  /-- the box side and the series radius -/
  b : ℝ
  b' : ℝ
  hb : 0 < b
  hbb' : b < b'
  hW : image I e lamT b ⊆ W
  /-- the prior and observable series in the normalised normal variables -/
  Fϕ : UniformSeriesFamily K (n + 1) b'
  Fφ : UniformSeriesFamily K (n + 1) b'
noncomputable def core : CorePresentation L (L.μ.restrict (image I D.e D.lamT D.b)) K n D.β where
  ν := baseMeasure I D.e
  isFiniteMeasure_ν := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
  h := fun _ => 0
  k := kι k I D.σ
  k_pos := fun _ => hk _
  b := D.b
  b_pos := D.hb
  Φ := Φ I D.σ D.e D.lamT
  measurable_Φ := measurable_Φ I D.σ (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT
  c := c I D.e D.lamT D.b D.b' D.hb D.Fϕ
  measurable_c :=
    (((continuous_J I D.e D.he D.lamT D.hlam_cont).comp continuous_fst).mul
      (D.Fϕ.continuous_evalF_clamp D.hb.le D.hbb'.le)).measurable
  nonneg_c := by
    have := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
    filter_upwards [ae_snd_mem_box (baseMeasure I D.e) n D.b]
    rintro ⟨s, v⟩ hv
    rw [c_eq_of_mem_box I D.σ D.e D.lamT ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq s hv]
    exact mul_nonneg (J_pos I D.e D.lamT D.hpos s).le
      (hϕ0 _ (D.hW (mem_image_Φ I D.σ D.e D.lamT D.hpos s hv)))
  x := xData I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ
  transport := by
    have h := map_Φ I D.σ D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT D.hpos
      hϕm.ennreal_ofReal
    rw [show (baseMeasure I D.e).prod (volume.restrict (box (ι := Fin (n + 1)) D.b)) =
      chartMeasure (baseMeasure I D.e) n D.b from rfl] at h
    rw [withDensity_congr_ae
      (density_ae I D.σ D.e D.he D.he_inj D.lamT D.hpos ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq), hLμ,
      ← restrict_withDensity hWm, Measure.restrict_restrict
      (measurableSet_image I D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT),
      inter_eq_left.2 D.hW]
```

### WaterFillingCollar.lean: water level, widths, base set
```lean

variable {d : ℕ} (k : Fin d → ℕ) (I : Finset (Fin d)) (a δ : ℝ)

/-- The tangential coordinates of a point. -/
def tan (w : Fin d → ℝ) : Tan I → ℝ := fun j => w j.1

/-- The water level `q_I(t) = (δ / t_I(t))^{1/|I|}`. -/
noncomputable def q (t : Tan I → ℝ) : ℝ := (δ / tanUnit k I t) ^ ((I.card : ℝ)⁻¹)

/-- The base `B_I`: `0 ≤ t_j ≤ a` and `δ ≤ t_I(t)·(t_j^{2k_j})^{|I|}` for every `j ∉ I`. -/
def baseSet : Set (Tan I → ℝ) :=
  {t | ∀ j, 0 ≤ t j ∧ t j ≤ a ∧ δ ≤ tanUnit k I t * (t j ^ (2 * k j.1)) ^ I.card}

/-- The physical normal width `ℓ_{I,i}(t) = q_I(t)^{1/(2k_i)}`. -/
noncomputable def ell (t : Tan I → ℝ) (i : Nrm I) : ℝ := q k I δ t ^ (((2 * k i.1 : ℕ) : ℝ)⁻¹)

/-- The common normalised side `b_I = δ^{1/(2Σ_{i∈I} k_i)}`. -/
noncomputable def side : ℝ := δ ^ (((2 * ∑ i ∈ I, k i : ℕ) : ℝ)⁻¹)

/-- The normalised widths `λ_{I,i}(t) = ℓ_{I,i}(t) / b_I`. -/
noncomputable def lamT (t : Tan I → ℝ) (i : Nrm I) : ℝ := ell k I δ t i / side k I δ

theorem tanUnit_tan (w : Fin d → ℝ) :
    tanUnit k I (tan I w) = ∏ j : Tan I, w j.1 ^ (2 * k j.1) := rfl

theorem tanUnit_eq_prod_compl (w : Fin d → ℝ) :
    tanUnit k I (tan I w) = ∏ j ∈ Iᶜ, w j ^ (2 * k j) := by
  rw [tanUnit_tan]
  exact (Finset.prod_subtype (p := fun x => ¬ x ∈ I) (F := inferInstance) Iᶜ
    (fun x => Finset.mem_compl) fun j => w j ^ (2 * k j)).symm
```

### CorePresentation / chartDensity
```lean
structure CorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ)
    where
  /-- the base measure on the compact stratum piece -/
  ν : Measure K
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the normal exponents of the Jacobian -/
  h : Fin (n + 1) → ℕ
  /-- the normal exponents of the phase, all positive -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the chart map into the resolved space -/
  Φ : K × (Fin (n + 1) → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the density factor (prior, Jacobian unit, tangential cutoff) -/
  c : K × (Fin (n + 1) → ℝ) → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p
  /-- the tangential datum realising the amplitude -/
  x : TangentialData K (n + 1)
  transport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity h c p).toNNReal : ENNReal)).map Φ = target
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b,
    CoeffFamily.evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)
  fluct_zero : ∀ v, xiCoord (x v) = 0

attribute [instance] CorePresentation.isFiniteMeasure_ν
def chartDensity {K : Type*} {n : ℕ} (h : Fin (n + 1) → ℕ) (c : K × (Fin (n + 1) → ℝ) → ℝ)
    (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  (∏ i, p.2 i ^ h i) * c p

```

### BlowUpCubeCharts.lean statements
```lean
45:def B (d : ℕ) : Fin d ↪ Fin d := Function.Embedding.refl (Fin d)
48:noncomputable def φ (β : Fin d) : (Fin d → ℝ) → (Fin d → ℝ) := blowUpChart (B d) β
50:theorem φ_self (β : Fin d) (y : Fin d → ℝ) : φ β y β = y β := blowUpChart_apply_scaling (B d) y
52:theorem φ_other (β : Fin d) (y : Fin d → ℝ) {γ : Fin d} (hγ : γ ≠ β) : φ β y γ = y β * y γ :=
55:theorem det_φ (β : Fin d) (y : Fin d → ℝ) : (fderiv ℝ (φ β) y).det = y β ^ (d - 1) := by
60:theorem analyticOnNhd_φ (β : Fin d) : AnalyticOnNhd ℝ (φ β) univ := by
72:theorem continuous_φ (β : Fin d) : Continuous (φ β) := continuous_blowUpChart (B d) β
75:def cube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc (-1) 1
77:theorem mem_cube {x : Fin d → ℝ} : x ∈ cube d ↔ ∀ j, |x j| ≤ 1 := by
80:theorem isCompact_cube : IsCompact (cube d) := isCompact_univ_pi fun _ => isCompact_Icc
82:theorem zero_mem_cube : (0 : Fin d → ℝ) ∈ cube d := mem_cube.2 fun _ => by simp
84:theorem cube_eq_closedBall : cube d = Metric.closedBall 0 1 := by
89:theorem cube_eq_centeredBox : cube d = centeredBox d 1 := by
95:noncomputable def K (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2
97:theorem K_nonneg (x : Fin d → ℝ) : 0 ≤ K x := Finset.sum_nonneg fun _ _ => sq_nonneg _
99:theorem continuous_K : Continuous (K (d := d)) := by
104:noncomputable def unit (β : Fin d) (y : Fin d → ℝ) : ℝ := 1 + ∑ γ ∈ Finset.univ.erase β, y γ ^ 2
106:theorem unit_pos (β : Fin d) (y : Fin d → ℝ) : 0 < unit β y :=
109:theorem continuous_unit (β : Fin d) : Continuous (unit β) := by
113:theorem K_φ (β : Fin d) (y : Fin d → ℝ) : K (φ β y) = unit β y * y β ^ 2 := by
126:noncomputable def expo (β : Fin d) : Fin d →₀ ℕ := Finsupp.single β 2
129:noncomputable def jexp (β : Fin d) : Fin d →₀ ℕ := Finsupp.single β (d - 1)
131:theorem monomialEval_single (y : Fin d → ℝ) (β : Fin d) (k : ℕ) :
136:theorem expo_support (β : Fin d) : (expo β).support = {β} :=
139:theorem monomialEval_expo (β : Fin d) (y : Fin d → ℝ) : monomialEval y (expo β) = y β ^ 2 :=
142:theorem monomialEval_jexp (β : Fin d) (y : Fin d → ℝ) :
150:theorem isMonomialChart (β : Fin d) :
175:theorem divisorSet_zero (β : Fin d) : divisorSet (expo β) 0 = {β} :=
179:theorem ball_subset (β : Fin d) :
186:theorem cube_eq_productBox (β : Fin d) : cube d = productBox (expo β) 0 1 := by
192:def wedge (β : Fin d) : Set (Fin d → ℝ) := {x | |x β| ≤ 1 ∧ ∀ γ, |x γ| ≤ |x β|}
194:theorem wedge_subset_cube (β : Fin d) : wedge β ⊆ cube d := fun _ ⟨h1, h2⟩ =>
197:theorem image_eq (β : Fin d) : φ β '' cube d = wedge β := by
226:theorem blowUpChartBox_one (β : Fin d) : blowUpChartBox (B d) β 1 = cube d := by
238:theorem iUnion_wedge [NeZero d] : ⋃ β, wedge β = cube d := by
247:noncomputable def diagonal (β γ : Fin d) (c : ℝ) : Submodule ℝ (Fin d → ℝ) :=
250:theorem mem_diagonal {β γ : Fin d} {c : ℝ} {x : Fin d → ℝ} :
255:theorem diagonal_ne_top {β γ : Fin d} (hβγ : β ≠ γ) (c : ℝ) : diagonal β γ c ≠ ⊤ := by
262:theorem volume_diagonal {β γ : Fin d} (hβγ : β ≠ γ) (c : ℝ) :
269:theorem volume_wedge_inter {β γ : Fin d} (hβγ : β ≠ γ) : volume (wedge β ∩ wedge γ) = 0 := by
281:noncomputable def chart (β : Fin d) : ResolutionChart d :=
286:noncomputable def R : ResolutionCover d (Fin d) := ⟨chart hd⟩
290:noncomputable def Ps :
294:theorem R_image (β : Fin d) : (R hd).image β = wedge β := by
298:theorem iUnion_image_eq [NeZero d] : ⋃ β, (R hd).image β = cube d := by
302:theorem aeDisjointImages : (R hd).AEDisjointImages := fun β γ hβγ => by
306:theorem Ps_isActive (β : Fin d) : (Ps hd β).IsActive :=
309:theorem Ps_b (β : Fin d) : (Ps hd β).b = 1 := rfl
311:theorem Ps_W (β : Fin d) : (Ps hd β).W = restrictNhd (expo β) (divisorSet (expo β) 0) univ := rfl
313:theorem Ps_r (β : Fin d) (x : Fin d → ℝ) : (Ps hd β).r x = 1 := rfl
315:theorem hne [NeZero d] : ((R hd).activeCharts (Ps hd)).Nonempty :=
318:theorem ratio_eq (β : Fin d) : (Ps hd β).ratio β = d / 2 := by
327:theorem Ps_e_support (β : Fin d) : (Ps hd β).e.support = {β} := by
331:theorem coverLamV_eq (β : Fin d) (hact) :
347:theorem coverDegV_eq (β : Fin d) (hact) :
366:theorem chartLam'_eq (β : Fin d) : (R hd).chartLam' (Ps hd) β = d / 2 := by
370:theorem chartDeg'_eq (β : Fin d) : (R hd).chartDeg' (Ps hd) β = 0 := by
374:theorem partitionLam'_eq [NeZero d] : (R hd).partitionLam' (Ps hd) (hne hd) = d / 2 := by
380:theorem partitionDeg'_eq [NeZero d] : (R hd).partitionDeg' (Ps hd) (hne hd) = 0 := by
384:theorem hεb : ∀ β, (1 : ℝ) ≤ (Ps hd β).b := fun _ => le_rfl
393:theorem hFcR : ∀ β, ContinuousOn (fun y => F (((R hd).chart β).φ y)) (Ps hd β).W := fun β =>
398:theorem hpcR : ∀ β, ContinuousOn (fun y => p.w (((R hd).chart β).φ y)) (Ps hd β).W := fun β =>
404:noncomputable def coeff : ℝ :=
409:theorem hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ β, (R hd).image β)) := by
414:theorem φ_mem_cube (β : Fin d) {y : Fin d → ℝ} (hy : y ∈ cube d) : φ β y ∈ cube d :=
420:theorem coeff_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
463:theorem cubeIntegral_isEquivalent (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
theorem isMonomialChart (β : Fin d) :
    IsMonomialChart K (φ β) (cube d) (expo β) (jexp β) univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_φ β
  injOn := fun a ha b hb hab => by
    have ha' : monomialEval a (jexp β) ≠ 0 := ha.2
    have hb' : monomialEval b (jexp β) ≠ 0 := hb.2
    rw [monomialEval_jexp] at ha' hb'
    exact blowUpChart_injOn_compl_pivotHyperplane (B d) β
      (fun h0 => ha' (by
        rw [show a (B d β) = a β from rfl] at h0
        rw [h0]
        exact zero_pow (by omega)))
      (fun h0 => hb' (by
        rw [show b (B d β) = b β from rfl] at h0
        rw [h0]
        exact zero_pow (by omega)))
      hab
  exists_unit := ⟨unit β, (continuous_unit β).continuousOn, fun y _ => (unit_pos β y).ne',
    fun y _ => by rw [K_φ, monomialEval_expo]⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero,
    fun y _ => by rw [det_φ, monomialEval_jexp, one_mul]⟩

/-- The divisor set of the origin is the support. -/
theorem divisorSet_zero (β : Fin d) : divisorSet (expo β) 0 = {β} :=
```

### HEADLINES rows CCLXXXIII, CCXCV, CCCXXIV, CCCXLI
| **CCCXLI** | ★★★ **THE COORDINATE-FREE EXPANSION ON THE SIGNED BOX (u659; phase G unit G6, consult #100 §1, §7–8 — PHASE G STOPPING GATE)**: for the even monomial phase on `[−a,a]^d` and a SIGNED analytic packet `HolomorphicSignedBoxExtension a ϕ φ`, the `2^d` orthant pieces carry the expansions transported from the positive box (pulled-back packets, one common collar level via `exists_delta_common`; `pieceCertificate`, `pieceCoeff`, `pieceMeasure = (R_σ)_* ν_σ`, `pieceField = (R_σ)_* B_σ`, `piece_expansion`) and ASSEMBLE (CCCXL) into one expansion with the assembled stratum measures ★★ `signedStratumMeasure I = ∑_σ (R_σ)_* ν_{σ,I}` (exact spec `signedStratumMeasure_eq`; finite; a.e. in the signed box `ae_signedStratumMeasure_mem_signedBox`) and the assembled moment field ★★ `signedMomentField = ∑_σ w_σ • (R_σ)_* B_σ` (Radon–Nikodym weights — all normal sides at a stratum point averaged in one fibre), on the unchanged full coordinate strata and the unchanged spectrum `spectrumLe (coordCommonQ k) (d−1)` (spectrum normalisation `pieceCertificate_cores_k`, `commonQ_piece`: the cores' exponents `coordCoresK k` are packet-independent, by `rfl`). ★★★ `hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local k hk A hd ha hϕ0`: hypotheses = the signed packet, `0 < d`, `0 < a`, prior `≥ 0` on the signed box; at-level form `hasCoordFreeExpansion_signed_at`; coefficient-sum spec ★ `expansionCoefficient_signed : C_signed(φ,q) = ∑_σ C_σ(φ∘R_σ, q)`; the Laplace integrand is integrable on the signed box from the packet (`integrableOn_signedBox`); the piece series are summable everywhere and integrable (`piece_summable`, `piece_integrable`, via CCCXXXIX with germ agreement `piece_germ`). Polynomial instance ★★ `hasCoordFreeExpansion_signed_polynomial` (`HolomorphicSignedBoxExtension.ofPolynomials`; prior `≥ 0` on the signed box only). Non-claims: Jacobian orders other than `zeroOrders`; a nonconstant analytic unit; general chart gluing; reflection-sensitive regression tests not yet included. Axiom-clean | SignedBoxExpansion.lean |
| **CCCXXIV** | ★★★ **THE COMPACT-BOX CERTIFICATE ON THE COORDINATE MODEL — THE GENERAL PRODUCER FROM LOCAL NORMAL SERIES (u642; consult #96 unit 5a)**: on the coordinate model (`CoordModel.geometry d k 0`, `normalData`) with the monomial phase on `W = [0,a]^d`, a measurable nonnegative prior `ϕ` and an observable `φ` (integrable against `ϕ·Leb|_W`), the water-filling collar is assembled into the certificates: the bases `baseStratum I ⊆ S_I` are the stratum points with tangential coordinates in `B_I` (COMPACT — the continuous image of `B_I` under the lift `t ↦ (0,t)`, `compactSpace_KI`; embedded by the tangential coordinates `eI`, `range_eI`, `eI_injective`); the frames `frameI s : ℝ^{|I|} ≃L N_I = span{e_i : i∈I}` are the reindexed diagonal scalings `u ↦ Σ_i λ_{I,i}(s) u_{σ⁻¹i} e_i` built from `Module.Basis.span`, `LinearEquiv.piCongrRight` and `smulOfNeZero` (`coe_frameI_apply`), and ★ `Φ_eq_frame` identifies the core parametrisation `s + Σ λ_i v_i e_i` with the coordinate model's tubular germ `s + ξ`, `ξ = frame u`. Input: `FaceSeries` — for every nonempty `I`, uniform series families `Fϕ Fφ` over the base in the NORMALISED normal variables at radius `2b_I`, with `ϕ∘Φ = evalF Fϕ` on the box and `φ∘Φ = evalF Fφ` on the ball. Then ★★ `WaterFilling.certificate : ResolvedCertificate geometry normalData W K ϕ φ` (`M = numCores`, `β = 1`, cores = the collar, presentations from the observable series), ★★ `coeffCertificate` (density family `J·fϕ`, jets `fφ` via `jetFamily_obsFibre`, datum identity `toEta_core_x`; `cc_abs_aux`, `jet_abs_aux`, `datum_eq_aux` on concrete indices), and ★★★ `hasCoordFreeExpansion_collar : HasCoordFreeExpansion certificate.stratumMeasure coeffCertificate.field (spectrumLe (commonQ cores.k) (commonD n)) W K ϕ φ` — the coordinate-free expansion of `∫_{[0,a]^d} φϕe^{−nK}` as a finite sum indexed by ALL nonempty coordinate strata, with the certificate's induced measures supported on their compact collar bases, produced from uniform COLLAR-BASE normal series (`FaceSeries` is collar-adapted: series over the compact base `baseStratum I ⊆ S_I ∩ X_I` in the normalised variables at radius `2b_I`, not over the whole closed face; the original-variable face-series adapter is CCCXXV). The log degree is explicit: `commonD_collar : commonD = d − 1` (attained at the deepest stratum), so `hasCoordFreeExpansion_collar'` states the spectrum `{(α,j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ d−1}`. This is consult #96's recommended stopping theorem for the phase minus the analytic-neighbourhood bridge. Non-claims: face series are hypotheses in normalised variables (rescaling adapter `UniformSeriesFamily.rescale` available); spectrum stated as the cores' common lattice; the `Data.hnorm`/frames are the coordinate model's, not derived SNC geometry. Axiom-clean | CoordinateBoxCertificate.lean |
| **CCXCV** | ★★★ **THE LEADING MEASURE OF THE GAUSSIAN CUBE IS `π^{d/2} δ₀`; LEADING MEASURES OF PARTIAL RESOLUTIONS (u613; consult #89, unit 7)**: for the blow-up cover of `[−1,1]^d` with `K = |x|²` (CCLXXXIII–IV), every tied face piece is pushed by the blow-up chart to the origin (the face is the exceptional divisor `{y_β = 0}`, collapsed by `φ_β`; the single normal coordinate is minimal so `faceProj = 0`, `ae_Φ_facePoint_eq_zero`), so each piece's target measure is a point mass (`coverPieces_targetMeasure_eq`) and ★★★ `BlowUpCube.leadingMeasure_eq : leadingMeasure = ofReal(π^{d/2}) • δ₀` (total mass from CCLXXXIV's `coeff_eq_pi_rpow` through `aeDisjointCoeff_eq_integral`); hence ★★★ `hasLeadingMeasure_cube : HasLeadingMeasure (cube d) K (d/2) 0 (π^{d/2} δ₀)` and the classical Laplace statement from the general machine, `tendsto_cube_laplace : ∫_{[−1,1]^d} a(x) e^{−t|x|²} dx / t^{−d/2} → π^{d/2} a(0)` for every bounded continuous `a`. Partial resolutions: a hironaka monomial partial resolution of a compact `N` with a.e.-disjoint images and supplied packages has a leading measure on `N` itself (`hasLeadingMeasure_ofPartialResolution`, via `HasLeadingMeasure.of_ae_eq_set` and `R.cover`) | BlowUpCubeLeadingMeasure.lean |
| **CCLXXXIII** | ★★ **ONE BLOW-UP SUFFICES: THE UNIT CUBE IN EVERY DIMENSION (u601; consult #86, A3)**: hironaka's standard blow-up of the origin of `ℝ^d` (`blowUpChart` with the full block, `d ≥ 2`), `φ_β(y)_β = y_β`, `φ_β(y)_γ = y_β y_γ` on the unit cube, for the quadratic phase `K = ∑ x_i²`: `K ∘ φ_β = y_β²(1 + ∑_{γ≠β} y_γ²)` and `det Dφ_β = y_β^{d−1}` (hironaka's axiom-clean `det_fderiv_blowUpChart`), so each chart is a monomial chart by hand (`isMonomialChart`, `e = 2δ_β`, `h = (d−1)δ_β`, unit `1 + ∑_{γ≠β} y_γ²`), the cube is its box at the origin (`cube_eq_productBox`, admissible with `W = univ`), the images are the wedges `{|x_β| ≤ 1, |x_γ| ≤ |x_β| ∀γ}` (`image_eq`) covering the cube exactly (hironaka's argmax cover `blowUpChartBox_cover`, `iUnion_wedge`) and meeting on the null diagonals `{x_β = ±x_γ}` (`volume_wedge_inter`, `Measure.addHaar_submodule`); the cover of the `d` box charts with CCLXX's `boxPackage`s has a.e.-disjoint images (`aeDisjointImages`), all charts active with pair `(d/2, 0)` (`ratio_eq`, `partitionLam'_eq`, `partitionDeg'_eq`); ★★ `cubeIntegral_isEquivalent`: for `F`, `p` continuous, nonnegative and positive on the cube, `∫_{[−1,1]^d} F p e^{−N ∑ x_i²} ~ c N^{−d/2}` with `c = coeff > 0` the sum of the `d` whole-box source coefficients (`coeff_pos` via CCLXXXI at cutoff `1/2` and CCLXXXII's cutoff independence) — the certificate DERIVED from the chart data, for a genuine multi-chart resolution in every dimension. The identification `c = π^{d/2}` for `F = p = 1` is CCLXXXIV | BlowUpCubeCharts.lean |
