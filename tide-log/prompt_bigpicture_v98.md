# Consult #98 — phase 3: the analytic-neighbourhood bridge to closed-face normal series

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 627 modules, zero sorry/axiom), companion to *Grammar (Expectations and the
Exceptional Divisor)* (Gerraty–Murfet 2026). Consult #97's stopping gate for phase 2 is met: the compact-box
producer on the coordinate model takes as input `OriginalFaceSeries` — uniform normal-series families for the
prior and the observable over the CLOSED FACES `X_I = {w ∈ [0,a]^d : w_i = 0, i ∈ I}` in the original normal
variables at a radius `ρ_I` — and, under `2δ^{1/(2k_i d)} < ρ_I`, produces both certificates and the coordinate-free
expansion (CCCXXV `hasCoordFreeExpansion_collar_of_face`); the chart jets are identified with the coordinate-free
normal differentials along the frames (CCCXXVI). You recommended that the derivation of the face series from
analyticity near the box be a SEPARATE phase (5b), cheapest via a COMPLEX neighbourhood and Cauchy estimates with a
strict radius shrink, reusing `AnalyticFamilyData`/`polyRealCoeff`. This consult asks for the precise design of that
phase: statements, unit breakdown, Mathlib routes, pitfalls.

## 1. What exists

* The target input structure (CCCXXV), with `originalNormalMap I s z = s + Σ_i z_i e_{σI I i}` in box coordinates
  `Fin (nI I + 1)` (`σI I : Fin (|I|−1+1) ≃ ↥I`), `faceSet a I = {w ∈ [0,a]^d : ∀ i ∈ I, w i = 0}`:
  `OriginalFaceSeries a ϕ φ I` = `ρ > 0`, `Fϕ Fφ : UniformSeriesFamily ↥(faceSet a I) (nI I + 1) ρ`, and
  `∀ s z, ‖z‖ < ρ → ϕ (originalNormalMap I s z) = evalF (Fϕ.f s) z` (same for φ). Here
  `UniformSeriesFamily X d b'` = `f : X → CoeffFamily d` coordinatewise continuous, `M : CoeffFamily d` with
  `|f x γ| ≤ M γ` and `Σ_γ |M_γ| b'^{|γ|} < ∞`; `CoeffFamily d = (Fin d → ℕ) → ℝ`, `evalF f u = Σ'_γ f_γ ∏ u_i^{γ_i}`.
* `hasCoordFreeExpansion_collar_of_face (hϕ0 : ∀ w, 0 ≤ ϕ w) (O : ∀ I, OriginalFaceSeries a ϕ φ I)
  (hsmall : ∀ I i, 2 * δ ^ ((d:ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ):ℝ)⁻¹) < (O I).ρ) : HasCoordFreeExpansion …`
  (also needs `0 < d`, `0 < a`, `0 < δ`, `δ^{1/d} < a^{2k_i}`, `Measurable ϕ`, `Measurable φ`,
  `Integrable φ (ϕ·Leb|_W)`), and the positive-part wrapper for `∀ w ∈ W, 0 ≤ ϕ w`.
* The existing COMPLEX route for ONE chart (Programme Q, `PolyCoeffParam` + `AnalyticFamilyData`): for
  `F : X → (Fin d → ℂ) → ℂ` holomorphic on the open polydisc of radius `R` with joint continuity and a uniform
  bound `M` on the closed polydisc of radius `r < R`, `polyRealCoeff d r (F x)` (real Cauchy coefficients at radius
  `r`) gives a datum continuous into the ℓ¹ data space (`continuous_analyticDatum`, majorant `M r^{-|γ|}`, summable
  because the datum scale is 1 < r), and the represented amplitude is `Re (F x)` on the closed cube
  (`dataAmplitude_analyticDatum`, `evalF_polyRealCoeff_of_lt`). Declarations below.


### Grammar/PolyCoeffParam.lean
/-!
# Cauchy coefficients depend continuously on a parameter (Programme Q, N3, unit 310)

For a family `F : X → (Fin d → ℂ) → ℂ` jointly continuous on `X × (closed polydisc of radius r)`,
each Cauchy coefficient `polyCoeff d r (F x) γ = A_r^{[d]}(w ↦ F x w ∏ wᵢ^{-γᵢ})` is a continuous
function of `x` (`continuous_polyCoeff_param`): the integrand is jointly continuous on
`X × torus`, where every `wᵢ` has modulus `r > 0`, and the iterated circle operator is continuous in
parameters (`continuousOn_iterOp_param`). With the uniform Cauchy estimate
`‖polyCoeff d r (F x) γ‖ ≤ M r^{-|γ|}` (`norm_polyCoeff_le`) this is the coordinatewise input to
the ℓ¹ criterion of unit 309. Zero `sorry`/`axiom`.
-/
```lean
theorem continuousOn_torus_monomial_inv {d : ℕ} {r : ℝ} (hr : 0 < r) (γ : Fin d → ℕ) :
    ContinuousOn (fun w : Fin d → ℂ => ∏ i, (w i)⁻¹ ^ γ i) (torusSet d r) := by

theorem continuous_polyCoeff_param {X : Type*} [TopologicalSpace X] {d : ℕ} {r : ℝ} (hr : 0 < r)
    {F : X → (Fin d → ℂ) → ℂ}
    (hF : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (γ : Fin d → ℕ) : Continuous fun x => polyCoeff d r (F x) γ := by

theorem continuous_polyRealCoeff_param {X : Type*} [TopologicalSpace X] {d : ℕ} {r : ℝ}
    (hr : 0 < r) {F : X → (Fin d → ℂ) → ℂ}
    (hF : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (γ : Fin d → ℕ) : Continuous fun x => (polyCoeff d r (F x) γ).re :=

```

### Grammar/AnalyticFamilyData.lean
/-!
# Analytic families of amplitudes are admissible tangential data (Programme Q, N3, unit 311)

The paper's chart amplitude after a tangential-only cutoff is `ρ_I(v) c(v,u) (φ∘π)(v,u)`: for each
tangential point `v` an analytic function of the normal variable `u`, jointly continuous in `(v,u)`.
This file turns such a family into the zero-noise tangential data of Programme S/P without any
geometric construction. Hypotheses on `F : X → (Fin d → ℂ) → ℂ` (radii `1 < r < R`):

* each `F x` is holomorphic on the open polydisc of radius `R`;
* `(x, w) ↦ F x w` is continuous on `X × closedPolydisc d r`;
* `‖F x w‖ ≤ M` on `X × closedPolydisc d r` (uniform bound; automatic from joint continuity when `X`
  is compact, but stated as a hypothesis).

Then `analyticDatum F x := ofFamilies 1 0 (polyRealCoeff d r (F x))` (zero phase, real Cauchy
coefficients at radius `r`) is a datum with `xiCoord = 0` and `etaCoord = polyRealCoeff d r (F x)`;
the map `x ↦ analyticDatum F x` is continuous into `DataSpace d` (`continuous_analyticDatum`, by the
ℓ¹ criterion with coordinatewise continuity and the geometric majorant `M r^{-|γ|}`, summable since
`r > 1`); and the represented amplitude is the real part of `F x` on the closed cube
(`dataAmplitude_analyticDatum`, reconstruction). For a compact `K` this gives
`analyticTangential F : TangentialData K d` with zero noise (`xiCoord_analyticTangential`).

This closes the non-claim "analytic admissibility of localised amplitudes" for the case the paper
uses (tangential-only cutoffs), given a common holomorphic neighbourhood with a strict radius gap;
it does not construct such a neighbourhood or the cutoff. Zero `sorry`/`axiom`.
-/
```lean
noncomputable def analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    DataSpace d :=

theorem analyticDatum_inl {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    (γ : Fin d → ℕ) : analyticDatum hr hrR h1r F hF x (Sum.inl γ) = 0 := by

theorem analyticDatum_inr {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    (γ : Fin d → ℕ) :
    analyticDatum hr hrR h1r F hF x (Sum.inr γ) = (polyCoeff d r (F x) γ).re := by

theorem xiCoord_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    xiCoord (analyticDatum hr hrR h1r F hF x) = 0 := by

theorem etaCoord_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    etaCoord (analyticDatum hr hrR h1r F hF x) = polyRealCoeff d r (F x) := by

noncomputable def geomMajorant (d : ℕ) (r M : ℝ) : DataIdx d → ℝ :=

theorem summable_geomMajorant (d : ℕ) {r : ℝ} (h1r : 1 < r) (M : ℝ) :
    Summable (geomMajorant d r M) := by

theorem continuous_analyticDatum {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ x, ∀ w ∈ closedPolydisc d r, ‖F x w‖ ≤ M) :
    Continuous (analyticDatum hr hrR h1r F hF) := by

theorem evalF_polyRealCoeff_of_lt {R r : ℝ} (hr : 0 < r) (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) {u : Fin d → ℝ}
    (hu : ∀ i, ‖(u i : ℂ)‖ < r) :
    evalF (polyRealCoeff d r F) u = (F fun i => (u i : ℂ)).re := by

theorem dataAmplitude_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataAmplitude (analyticDatum hr hrR h1r F hF x) u = (F x fun i => (u i : ℂ)).re := by

noncomputable def analyticTangential {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) : TangentialData K d :=

theorem analyticTangential_apply {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) :
    analyticTangential hr hrR h1r F hF hFc hM v = analyticDatum hr hrR h1r F hF v := rfl

theorem xiCoord_analyticTangential {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) :
    xiCoord (analyticTangential hr hrR h1r F hF hFc hM v) = 0 :=

```

### Grammar/CoordinateBoxInputs.lean
/-!
# Public inputs of the compact-box producer (CCCXXV)

Consult #97 §1.2 and §1.4: two adapters that turn the collar-adapted interface of CCCXXIV into
paper-facing hypotheses.

* **Original-variable face series.** `OriginalFaceSeries I` carries uniform series families for
  the prior and the observable over the CLOSED FACE `X_I = {w ∈ [0,a]^d : w_i = 0, i ∈ I}` in the
  ORIGINAL normal variables `z` (the insertion `Ψ_I(s,z) = s + Σ_i z_i e_{σ i}`,
  `originalNormalMap`) at a radius `ρ_I`, with the evaluation identities on the open normal ball.
  Under the smallness condition `2 δ^{1/(2k_i d)} < ρ_I` (`i ∈ I`) the water-filling widths satisfy
  `λ_{I,i}(s) ≤ L_i := δ^{1/(2k_i d)}/b_I` with `2 b_I L_i = 2δ^{1/(2k_i d)}`, so restriction to the
  collar base (`UniformSeriesFamily.precomp`) and rescaling (`UniformSeriesFamily.rescale`) produce
  the collar-base series `FaceSeries` of CCCXXIV (`OriginalFaceSeries.toFaceSeries`), and the
  expansion follows (`hasCoordFreeExpansion_collar_of_face`).
* **Box-local nonnegativity.** For a prior nonnegative only on the box, the positive part
  `ϕ⁺ = max ϕ 0` is globally nonnegative, agrees with `ϕ` on `[0,a]^d`, defines the same
  prior-weighted measure, has the same collar-base series and the same observable; hence the
  coordinate-free expansion of `∫_{[0,a]^d} φ ϕ e^{−nK}` holds with the certificate of `ϕ⁺`
  (`hasCoordFreeExpansion_collar_of_nonneg_on`), stated precisely with that certificate.

Zero `sorry`/`axiom`.
-/
```lean
def precomp (F : UniformSeriesFamily X d b') (g : Y → X) (hg : Continuous g) :
    UniformSeriesFamily Y d b' where

theorem precomp_f (F : UniformSeriesFamily X d b') (g : Y → X) (hg : Continuous g) (y : Y) :
    (F.precomp g hg).f y = F.f (g y) := rfl

def faceSet (I : Finset (Fin d)) : Set (Fin d → ℝ) :=

noncomputable def originalNormalMap (I : NonemptyIdx d) (s : Fin d → ℝ) (z : Fin (nI I + 1) → ℝ) :
    Fin d → ℝ :=

structure OriginalFaceSeries (I : NonemptyIdx d) where
  /-- the normal radius -/
  ρ : ℝ
  hρ : 0 < ρ
  Fϕ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
  Fφ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
  hϕ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
    ϕ (originalNormalMap I s.1 z) = evalF (Fϕ.f s) z
  hφ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
    φ (originalNormalMap I s.1 z) = evalF (Fφ.f s) z

theorem mem_faceSet_of_KI (ha : 0 < a) (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    s.1.1 ∈ faceSet a I.1 := by

def toFace (ha : 0 < a) (I : NonemptyIdx d) (s : KI k hk a δ I.1) : ↥(faceSet a I.1) :=

theorem continuous_toFace (ha : 0 < a) (I : NonemptyIdx d) : Continuous (toFace k hk a δ ha I) :=

noncomputable def widths (I : NonemptyIdx d) (s : KI k hk a δ I.1) (i : Fin (nI I + 1)) : ℝ :=

noncomputable def widthBound (I : NonemptyIdx d) (i : Fin (nI I + 1)) : ℝ :=

theorem continuous_widths (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    Continuous fun s => widths k hk a δ I s i :=

theorem widths_pos (hδ : 0 < δ) (I : NonemptyIdx d) (s : KI k hk a δ I.1) (i : Fin (nI I + 1)) :
    0 < widths k hk a δ I s i :=

theorem widthBound_pos (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    0 < widthBound k δ I i :=

theorem abs_widths_le (hδ : 0 < δ) (hd : 0 < d) (I : NonemptyIdx d) (s : KI k hk a δ I.1)
    (i : Fin (nI I + 1)) : |widths k hk a δ I s i| ≤ widthBound k δ I i := by

theorem widthBound_mul (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    widthBound k δ I i * (2 * side k I.1 δ) =
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) := by

theorem Φ_eq_originalNormalMap (I : NonemptyIdx d) (s : KI k hk a δ I.1)
    (v : Fin (nI I + 1) → ℝ) :
    Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v) =
      originalNormalMap I s.1.1 fun i => widths k hk a δ I s i * v i := by

theorem norm_widths_mul_lt (hδ : 0 < δ) (hd : 0 < d) (I : NonemptyIdx d) {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ∀ i : Fin (nI I + 1), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < ρ)
    (s : KI k hk a δ I.1) {v : Fin (nI I + 1) → ℝ} (hv : ‖v‖ < 2 * side k I.1 δ) :
    ‖fun i => widths k hk a δ I s i * v i‖ < ρ := by

noncomputable def OriginalFaceSeries.toFaceSeries {I : NonemptyIdx d}
    (O : OriginalFaceSeries a ϕ φ I) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
    (hsmall : ∀ i : Fin (nI I + 1), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < O.ρ) :
    FaceSeries k hk a δ ϕ φ I where

theorem hasCoordFreeExpansion_collar_of_face (hϕ0 : ∀ w, 0 ≤ ϕ w)
    (O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I)
    (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ) :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=

def posPart (ϕ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun w => max (ϕ w) 0

theorem posPart_nonneg (ϕ : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : 0 ≤ posPart ϕ w :=

theorem measurable_posPart (hϕm : Measurable ϕ) : Measurable (posPart ϕ) :=

theorem posPart_eq_of_mem (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc 0 a)) : posPart ϕ w = ϕ w :=

theorem withDensity_posPart (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) :
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (posPart ϕ w)) =
      (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w) := by

noncomputable def FaceSeries.toPosPart {I : NonemptyIdx d} (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
    (F : FaceSeries k hk a δ ϕ φ I) : FaceSeries k hk a δ (posPart ϕ) φ I where

theorem globalLaplace_congr_on {K a' a'' : (Fin d → ℝ) → ℝ}
    (h : ∀ w ∈ piBox d (Icc 0 a), a' w = a'' w) (N : ℝ) :
    globalLaplace (piBox d (Icc 0 a)) K a' N = globalLaplace (piBox d (Icc 0 a)) K a'' N := by

theorem hasCoordFreeExpansion_collar_of_nonneg_on (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
    (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I) :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
        ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).stratumMeasure
      (coeffCertificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
        ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).field
      (spectrumLe (commonQ (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
        (posPart_nonneg ϕ) ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).cores.k) (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by

```

Headline rows (verbatim) for CCCXXV–CCCXXVI:

| **CCCXXVI** | ★★ **COORDINATE NORMAL COMPATIBILITY — THE FIRST COMPATIBILITY SLICE (u644; consult #97 §2)**: `CoordinateNormalCompatibility I K N base e inc du tube lamT` connects, at a stratum `S_I` of the coordinate model, the base points (`base_normal`, `base_tangent`), the normal space with its inclusion and the COORDINATE CONORMALS `du_j = inc(·)_j` (`du_coordinate`, `inc_tangent`), the FIXED tubular map `tube s ξ = base s + inc ξ` (`tubular_eq`) and a frame whose conormal pairings are DIAGONAL with scale `λ_j(e s)` (`frame_conormal`; `du_frame_single`: diagonal entry `λ_i(s)`, not `1`). Consequences are theorems, not fields: ★ `tube_frame_eq_normalisedBox : tube s (frame s u) = Φ(s,u)` (the tubular parametrisation along the frame IS the normalised box parametrisation), `phase_tube_frame` (the phase along it is the tangential unit times the normalised monomial). CONSTRUCTIVE CONSUMER: from the compatibility packet, a box geometry packet `BoxBounds` and series in TUBULAR-FRAME notation (`TubularFrameSeries`: `ϕ(tube_s(frame_s u))`, `φ(tube_s(frame_s u))`), `toNormalisedBoxData` and ★★ `produceCore_of_coordinateCompat : CorePresentation …` + `producePresentation` build a core WITHOUT assuming transport, the phase normal form or a coefficient certificate; acceptance test `obsFibre_produceCore : obsFibre s u = φ(tube_s(frame_s u))`, `jetFamily_produceCore`. FIXED-GERM INTERPRETATION: ★ `iteratedFDeriv_comp_cle_zero` (`D^r(G∘F)(0) = D^rG(0)∘(F,…,F)` for a CLE `F` and `G` analytic near 0, via `iteratedFDerivWithin_comp_right` on an open set), `normalJet_comp_cle_of_series`, ★ `normalJet_produceCore` (the fibre jets are the jets of the fixed normal germ `φ∘tube_s` pulled back along the frame — no base derivative, no derivative of the frame scale). INSTANCE: ★ `waterFillingCompat` (bases in the strata, `normalSpace`, `normalDu`, the germ `s + ξ`, the frames `frameI`; `waterFillingCompat_tube_frame` reproduces `Φ_eq_frame`) and ★★ `normalJet_stratumCore_eq_normalDifferential`: for every core of the water-filling certificate, `normalJet (obsFibre_s) r = D^r_⊥(φ∘π)(s) ∘ (frameI s,…)` — the chart jets ARE the coordinate-free normal differentials of `HasCoordFreeExpansion` pulled back along the frame. Non-claims: an exact coordinate specialisation, not general SNC compatibility; higher jets depend on the chosen tubular germ (here the straight germ `s + ξ`). Consult #97 stopping gate items 2–5 met. Axiom-clean | CoordinateNormalCompatibility.lean |
| **CCCXXV** | ★★★ **PUBLIC INPUTS OF THE COMPACT-BOX PRODUCER (u643; consult #97 §1.2, §1.4)**: (i) the ORIGINAL-VARIABLE FACE-SERIES ADAPTER — `OriginalFaceSeries I` carries uniform series families for the prior and the observable over the CLOSED FACE `X_I = {w ∈ [0,a]^d : w_i = 0, i ∈ I}` (`faceSet`) in the ORIGINAL normal variables (insertion `Ψ_I(s,z) = s + Σ_i z_i e_{σi}`, `originalNormalMap`) at a radius `ρ_I` with the evaluation identities on the open normal ball; under `2δ^{1/(2k_i d)} < ρ_I` (`i ∈ I`) the water-filling widths obey `λ_{I,i}(s) ≤ L_i = δ^{1/(2k_i d)}/b_I` (`abs_widths_le`) with `2b_I L_i = 2δ^{1/(2k_i d)}` (`widthBound_mul`), the core parametrisation is `Ψ_I(s, λ(s)·v)` (`Φ_eq_originalNormalMap`), and restriction to the collar base (`UniformSeriesFamily.precomp`) plus rescaling (`UniformSeriesFamily.rescale`) give the collar-base series of CCCXXIV: ★ `OriginalFaceSeries.toFaceSeries`, ★★★ `hasCoordFreeExpansion_collar_of_face`. (ii) BOX-LOCAL NONNEGATIVITY — for a prior nonnegative only on the box, `posPart ϕ = max ϕ 0` is globally nonnegative, agrees with `ϕ` on the box, defines the same prior-weighted measure (`withDensity_posPart`), has the same collar-base series (`FaceSeries.toPosPart`) and the same observable, so ★★★ `hasCoordFreeExpansion_collar_of_nonneg_on` gives the expansion of `∫_{[0,a]^d} φϕe^{−nK}` with the certificate and coefficient field of `ϕ⁺` (stated precisely with that certificate; `globalLaplace_congr_on`). These are the paper-facing hypotheses of the collar producer; the analytic-neighbourhood bridge (from analyticity near the box to such face series) is a separate phase. Axiom-clean | CoordinateBoxInputs.lean |

## 2. Questions

**Q1 (the theorem).** State precisely the bridge theorem you would accept, in the form we should formalise.
Our draft: for `d > 0`, `a > 0`, `k_i > 0`; an open `Ω ⊆ ℂ^d` (as `Fin d → ℂ`) containing the embedded box
`{(w_i : ℂ) : w ∈ [0,a]^d}`; holomorphic `Hϕ Hφ : (Fin d → ℂ) → ℂ` on `Ω` (`DifferentiableOn ℂ H Ω`); with
`ϕ w = Re (Hϕ (ofReal ∘ w))` and `φ w = Re (Hφ (ofReal ∘ w))` on a REAL neighbourhood of the box (or only on the
box, with the extension caveat of #97 §1.3). Conclusion: `∃ ρ > 0, ∀ I : NonemptyIdx d, Nonempty (OriginalFaceSeries a ϕ φ I)`
with the common radius `ρ` (i.e. `(O I).ρ = ρ`), and then the small-`δ` selection lemma
`∃ δ > 0, (∀ i, δ^{1/d} < a^{2k_i}) ∧ (∀ i, 2 δ^{1/(2k_i d)} < ρ)`. Is a COMMON radius `ρ` the right normal
form, or per-face radii? Should the identity `ϕ = Re Hϕ` be required on all of `ℝ^d ∩ Ω`, on a real
neighbourhood, or only on `[0,a]^d` (then which extension does the theorem talk about)? Where does
`Re`-of-holomorphic vs a real-analytic `ϕ` (with `Hϕ` its complexification) sit best for the paper?

**Q2 (the construction).** For a closed-face parameter `s ∈ X_I` and the recentred normal function
`z ↦ H(s + insert_I z)` (`insert_I z = Σ_i z_{σ⁻¹…} e_i` in complex coordinates), we must produce
`Fϕ.f s : CoeffFamily (nI I + 1)` (real Cauchy coefficients at radius `R'` on the normal polydisc), prove
(a) coordinatewise continuity in `s` (parameter-dependent Cauchy integrals — `continuous_polyRealCoeff_param`
exists for a jointly continuous family on a FIXED polydisc; here the polydisc is recentred at `s`: is the
right move to define `G_s(z) := H(s + insert z)` as a family `X_I → (Fin m → ℂ) → ℂ` and reuse the existing
one-chart machinery verbatim?), (b) the uniform majorant `M R'^{-|γ|}` from a uniform bound on the union of
the recentred closed polydiscs (compactness of `X_I` + openness of `Ω`: a thin uniform complex neighbourhood
— which Mathlib lemma gives `∃ ε > 0, ∀ s ∈ compact, closedPolydisc(s, ε) ⊆ Ω`? `IsCompact.exists_thickening_subset_open`?),
(c) summability at `ρ < R'` (`Σ M (ρ/R')^{|γ|} = M(1−ρ/R')^{−m}` — do we have `summable_prodGeom`? yes in
`AnalyticFamilyData`), (d) the evaluation identity `ϕ(originalNormalMap I s z) = evalF (Fϕ.f s) z` for
real `‖z‖ < ρ` from `evalF_polyRealCoeff_of_lt`-type reconstruction plus `ϕ = Re H` on the real slice.
Please give the exact sequence of lemmas, which existing declarations to reuse verbatim and which to
generalise (e.g. the existing route fixes the box scale 1 and radius `r > 1`; we need radius `ρ` with
`polyRealCoeff` at radius `R'` and summability at `ρ < R'`), and the type-level handling of the parameter
space `↥(faceSet a I)` (a compact subtype of `ℝ^d`) and of the complex insertion.

**Q3 (Mathlib inventory).** Which Mathlib results carry the load: Cauchy integral formula on polydiscs
(we have our own `polyCoeff`/torus integrals in `PolyCoeffParam` — see the declarations), uniform bounds on
compact sets (`IsCompact.exists_bound_of_continuousOn`), holomorphic ⇒ continuous, the open-neighbourhood
thickening lemma, and the real-slice identity. Any known gaps (e.g. several-variable Cauchy estimates are
NOT in Mathlib; we rely on our torus-integral coefficients) and how our existing `norm_polyCoeff_le`
(bound `M r^{-|γ|}` on the torus of radius `r`) suffices.

**Q4 (units and sizes).** Break the phase into units of 200–500 lines with gates; name the first unit and
its exact statement. Estimate total effort. Say what the final user-facing theorem of the whole programme
reads (holomorphic data near the box ⇒ the coordinate-free expansion with strata integrals), and whether
anything in CCCXXV's interface should change first (e.g. `OriginalFaceSeries.ρ` per face vs common).

**Q5 (honesty).** Anything in the CCCXXV/CCCXXVI headline rows (above) that overclaims, and the wording of
the paper-facing sentence for phase 3 once done.

Be concrete and mathematically precise; flag every place our current interface is wrong or too narrow.
