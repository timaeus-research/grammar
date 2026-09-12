# Consult #95 — the fundamentals of the certified resolved geometry

Context: Lean 4 formalisation of the grammar paper (Gerraty–Murfet), repo `timaeus-research/grammar`, 616 modules,
axiom-clean. The coordinate-free expansion programme (#92–#94) is closed at your stopping point: the representation
theorem `hasCoordFreeExpansion_le` (conditional on `ResolvedCertificate` + `CoefficientCertificate`), canonicity of the
assembled scalar coefficients, the leading term and leading-measure bridge, `jetFamily = monoFamily`, and hand-built
instances with checked closed-form coefficients (`∫_0^ρ P e^{−nx²}`: `Γ((m+1)/2)/2·f_m`; tied crossing
`∫_{[0,b]²} P e^{−nx²y²}`: `√π/4·P(0)` at `n^{−1/2} log n`). The user now says: **"let's proceed on the fundamentals of
the certified resolved geometry"**. This consult asks you to design that: what the resolved-geometry side must carry to be
geometrically honest, how curved sublevel sets are handled, and how certificates are PRODUCED from geometry rather than
assumed.

## The current interface (Lean, verbatim)

### `ResolvedGeometry` (CCXCVIII)
structure ResolvedGeometry (d : ℕ) (U : Type*) [TopologicalSpace U] where
  /-- The resolution map. -/
  π : U → (Fin d → ℝ)
  continuous_π : Continuous π
  proper_π : IsProperMap π
  /-- The index type of the divisor components. -/
  Component : Type
  [fintype : Fintype Component]
  [decEq : DecidableEq Component]
  /-- The divisor components. -/
  E : Component → Set U
  isClosed_E : ∀ i, IsClosed (E i)
  /-- The half phase orders `k_i` (the phase vanishes to order `2k_i` along `E_i`). -/
  k : Component → ℕ
  /-- The Jacobian orders `h_i`. -/
  h : Component → ℕ
  k_pos : ∀ i, 0 < k i

attribute [instance] ResolvedGeometry.fintype ResolvedGeometry.decEq

69:def stratumSet (I : Finset R.Component) : Set U := {u | ∀ i, u ∈ R.E i ↔ i ∈ I}
70-
71-/-- The stratum as a type. -/
72:abbrev Stratum (I : Finset R.Component) : Type _ := ↥(R.stratumSet I)
73-
74-/-- The incidence set of a point: the components passing through it. -/
--
156:noncomputable def ratio (i : R.Component) : ℝ := ((R.h i : ℝ) + 1) / (2 * (R.k i : ℝ))
157-
158-theorem ratio_pos (i : R.Component) : 0 < R.ratio i := by
--
164:noncomputable def stratumLam (I : Finset R.Component) (hne : I.Nonempty) : ℝ :=
165-  I.inf' hne R.ratio
166-
--
209:def IsResolutionOf (K : (Fin d → ℝ) → ℝ) : Prop := ∀ u, K (R.π u) = 0 ↔ u ∈ R.divisor
210-
211-theorem image_divisor_subset {K : (Fin d → ℝ) → ℝ} (hK : R.IsResolutionOf K) :

### `ResolvedNormalData` (CCXCIX + CCCIV)

/-! ### Resolved normal data -/

variable {d : ℕ} {U : Type*} [TopologicalSpace U]

/-- **Resolved normal data** of a resolved geometry: normal spaces, labelled conormal
differentials and tubular germs along every stratum. -/
structure ResolvedNormalData (R : ResolvedGeometry d U) (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  /-- The normal space at a point of the stratum `S_I`. -/
  N : ∀ I : Finset R.Component, R.Stratum I → Submodule ℝ A
  finrank_N : ∀ (I : Finset R.Component) (s : R.Stratum I), Module.finrank ℝ (N I s) = I.card
  finiteDimensional_N : ∀ (I : Finset R.Component) (s : R.Stratum I), FiniteDimensional ℝ (N I s)
  /-- The labelled conormal differentials `du_i(s)`, `i ∈ I`. -/
  du : ∀ (I : Finset R.Component) (s : R.Stratum I), I → Module.Dual ℝ (N I s)
  du_linearIndependent : ∀ (I : Finset R.Component) (s : R.Stratum I), LinearIndependent ℝ (du I s)
  /-- The tubular germs `Φ_s : N_s → U`. -/
  Φ : ∀ (I : Finset R.Component) (s : R.Stratum I), N I s → U
  Φ_zero : ∀ (I : Finset R.Component) (s : R.Stratum I), Φ I s 0 = (s : U)
120:noncomputable def normalDifferential (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component)
121-    (s : R.Stratum I) (r : ℕ) : JetForm (D.N I s) r :=
122-  Grammar.normalDifferential (D.N I) (D.Φ I) (φ ∘ R.π) s r
123-

### `ResolvedCertificate` (CCC) — built on the library's `AdaptedStrataData` (sublevel-set partition into chart presentations)
    (W : Set (Fin d → ℝ)) (K ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- The localisation datum on the resolved space. -/
  L : LocalisationData U
  obs_eq : L.obs = φ ∘ R.π
  phase_eq : L.phase = K ∘ R.π
  /-- The resolved measure pushes forward to the prior-weighted Lebesgue measure on `W`. -/
  transport : L.μ.map R.π = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w)
  /-- The number of pieces. -/
  M : ℕ
  /-- The normal dimensions minus one. -/
  n : Fin M → ℕ
  /-- The stratum presented by each piece. -/
  strat : Fin M → Finset R.Component
  /-- The compact piece of the stratum carrying the base measure (the support of the adapted
  partition weight). -/
  base : ∀ I, Set (R.Stratum (strat I))
  isCompact_base : ∀ I, IsCompact (base I)
  /-- The inverse temperature of the normal form. -/
  β : ℝ
  β_pos : 0 < β
  /-- The adapted strata data, with the compact stratum pieces as base spaces. -/
  adapted : AdaptedStrataData L M (fun I => ↥(base I)) n β
  /-- The normal-moment presentations (analytic fibre observables). -/
  T : ∀ I, NormalMomentPresentation (adapted.chart I)
  /-- The frames `ℝ^{n_I+1} ≃ N_s` identifying box normal coordinates with the normal space. -/
  frame : ∀ I (s : ↥(base I)), (Fin (n I + 1) → ℝ) ≃L[ℝ] D.N (strat I) s.1
  /-- The box parametrisation is the tubular germ in the frame. -/
  Φ_eq : ∀ I (s : ↥(base I)) (u : Fin (n I + 1) → ℝ),
    (adapted.chart I).Φ (s, u) = D.Φ (strat I) s.1 (frame I s u)

namespace ResolvedCertificate

variable {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}
  (C : ResolvedCertificate R D W K ϕ φ)

instance (I : Fin C.M) : CompactSpace ↥(C.base I) := isCompact_iff_compactSpace.1
  (C.isCompact_base I)

`ChartPresentation D ρ K n β` (library, pre-existing): base measure `ν` on compact `K`, exponents `h k`, box side `b`,
`Φ : K × (Fin (n+1) → ℝ) → U` measurable, density `c`, tangential datum `x : C(K, DataSpace)`,
`transport : ((ν ⊗ vol|_{(0,b]^{n+1}}).withDensity (u^h c)).map Φ = (μ|_{K<δ}).withDensity ρ`,
`phase_normal : phase (Φ p) = β ∏ u_i^{2k_i}` a.e., `amplitude_eq : evalF (toEta b (x v)) u = c(v,u) · obs(Φ(v,u))` a.e.,
`fluct_zero`. `LocalisationObstruction.lean` records that a chart-exact analytic amplitude cannot absorb an exact
sublevel cutoff — so for phases with CURVED sublevel sets (`K = x²y²` on a square larger than the sublevel) product-box
charts cannot partition `{K < δ}` and `AdaptedStrataData` is uninhabitable; our tied instance dodged this by taking the
square inside the sublevel set. The library has the alternative interface:

### `CorePresentation` / `AnalyticCoreDecomposition` (library, pre-existing; cores + phase-gap tail)
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
structure AnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
    (n : Fin M → ℕ) (β : ℝ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the core presentations -/
268:theorem cutoffExpansion (hβ : 0 < β) :
269-    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) := by
270-  have h := (cutoffExpansion_gInt A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x).add
271-    (cutoffExpansion_of_exp_small (commonQ A.k) (commonD n) (half_pos A.δ₀_pos)
(`AnalyticCoreDecomposition.cutoffExpansion : CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x)`
exists; the moment-series representation of CCC is not restated for cores.)

### `CoefficientCertificate` (CCCIII) and `ofSeries` (CCCIX)

/-- **A coefficient certificate**: along every chart, a `b`-weighted ℓ¹ **factorisation family**
`cc` (the intended reading is the Taylor family of the density factor `c(s, ·)`, but the
certificate only asks for the factorisation below), the `b`-weighted ℓ¹ summability of the
observable's Taylor family, and the identification of the chart's amplitude datum with the
Cauchy product `cc ⋆ jetFamily`. -/
structure CoefficientCertificate where
  /-- The factorisation family at the base point `s` (intended: the Taylor family of `c(s, ·)`). -/
  cc : ∀ J, ↥(C.base J) → CoeffFamily (C.n J + 1)
  cc_abs : ∀ J s, AbsSummableAt (cc J s) (C.adapted.b J)
  /-- The observable's Taylor family on the box is `b`-weighted ℓ¹. -/
  jet_abs : ∀ J s,
    AbsSummableAt (jetFamily (C.n J) ((C.adapted.chart J).obsFibre s)) (C.adapted.b J)
  /-- The amplitude datum is the Cauchy product of the density family and the observable's
  Taylor family. -/
  datum_eq : ∀ J s, toEta (C.adapted.b J) ((C.adapted.chart J).x s) =

### The coordinate model (CCCXIII): `ℝ^d`, `π = id`, `E_i = {u_i = 0}`, `K = ∏ u_i^{2k_i}`, `N_I = span{e_i : i ∈ I}`,
`du_i = ` coordinate functionals, `Φ_s(v) = s + v`. The hironaka interface exposes `PartialResolution`: finitely many
compact chart domains with analytic maps into `W`, images covering a compact set a.e. with finite multiplicity,
`IsMonomialChart` per chart — no common resolved space, no `π`, no transitions, no global divisor components.

## Your #93 remarks to address
- "`du` is an independent family of covectors and `Φ` is merely continuous at zero. Those fields alone do not establish
  genuine divisor conormals or tubular geometry … describe this as chosen normal data, and add the missing geometric
  compatibility before claiming an intrinsic conormal construction."
- I (core + phase-gap interface): "highest infrastructure value if the next goal is transferring general geometric models
  into the expansion theorem … map precisely which existing `BlowUpCube` outputs would satisfy the new interface."
- E (projector blow-up) "pays a substantial interface cost; reassess after I or a clear adapter design."

## Questions

1. **Geometric compatibility axioms.** Specify, at the level of Lean fields, what `ResolvedNormalData` should additionally
   assert so that `N_s`, `du_i(s)`, `Φ_s` are genuinely the normal space, the divisor conormals and a tubular germ of the
   normal crossing `⋃_{i∈I} E_i` at `s ∈ S_I`. Candidates: (a) `Φ_s` is a homeomorphism/local diffeomorphism from a
   neighbourhood of `0 ∈ N_s` onto a neighbourhood of `s` in a transversal slice, (b) `Φ_s(v) ∈ E_i ↔ du_i(s)(v) = 0` for
   `i ∈ I` near `0`, (c) `Φ_s(v) ∉ E_j` for `j ∉ I` near `0`, (d) the phase pulled back is a monomial times a unit:
   `K(π(Φ_s v)) = unit(v) · ∏_{i∈I} du_i(v)^{2k_i}`, (e) the Jacobian pulls back to `∏ |du_i|^{h_i}` times a unit,
   (f) smooth/analytic dependence on `s` (a chosen normal family / `IsGlobalNormalSection` already exists in the library:
   `GlobalNormalSections.lean`, `LabelledNormalBundle.lean` with `LabelledDefiningEquations`, `TubularBridge.lean`).
   Which of these are needed for which THEOREM (not for aesthetics)? Which are theorems about the certificate (derivable
   from `ChartPresentation.phase_normal` + `Φ_eq`) rather than new axioms?
2. **The core route (I).** Design `ResolvedCoreCertificate` on `AnalyticCoreDecomposition` (cores + phase-gap tail) with the
   same downstream API as `ResolvedCertificate` (per-chart `x, b, obsFibre, fluct_zero, k_pos`, `cutoffExpansion`), so
   CCCIII–CCCX transfer. What is the minimal abstraction: a structure `ChartData` with the fields the expansion theorem
   actually uses, with two constructors (from `AdaptedStrataData`, from `AnalyticCoreDecomposition`)? Give the field list.
3. **Producing certificates from geometry (the real fundamentals).** For the coordinate model with a monomial phase and an
   ANALYTIC density `ϕ` and observable `φ` on a product box `∏[0,b_i]` (or a cube around the origin with all `2^d`
   orthants), state the theorem "there exists a `ResolvedCoreCertificate`" — the chart cover by orthants, the stratum
   pieces `S_I ∩ box`, cores = orthant boxes near each stratum piece, the tail = complement with a phase gap, the base
   measures, the analytic amplitude data via `polySeriesD`/`ofSeries`. Which parts are genuinely hard (partition of the
   cube into product pieces adapted to ALL strata, with a positive phase gap on the remainder; the analytic amplitude datum
   as a `C(K, DataSpace)` — continuity of the Taylor family in the base point)? Propose the unit sequence and gates.
4. **Lifting hironaka's interface.** What minimal extension of `PartialResolution` (a common `U`, transition data, or merely
   an a.e.-disjoint refinement of the chart images as in CCXCIII) would allow a `ResolvedGeometry`/`ResolvedCoreCertificate`
   to be CONSTRUCTED for a general analytic `K`? If none is realistic, say so and identify the honest conditional form.
5. **Ranking, gates, sizes**, and the first two units to write. Prefer statements that produce theorems; no bookkeeping
   rounds.

Answer in sections 1–5, tersely, with Lean-level field lists where relevant.
