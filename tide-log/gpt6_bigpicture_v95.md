## 1. Geometric compatibility: strengthen the interpretation, not the expansion hypotheses

The present structures encode **chosen normal data**, not yet the normal geometry of an SNC divisor. In particular, the current `Φ_zero` does not even assert continuity.

I would keep them backward-compatible and add separate compatibility structures. The following are schematic Lean field lists, not proposed compilable declarations.

### A. Genuine normal-crossing geometry

First give `U` a differentiable/analytic manifold structure and identify each stratum as an embedded submanifold. Then add:

```lean
structure SNCNormalCompatibility ... where
  -- Embedded stratum and its tangent bundle.
  stratumEmbedding : ...
  -- N is a model of the genuine normal quotient, not just a space of the right rank.
  normalEquiv :
    ∀ I s, D.N I s ≃L[ℝ] NormalQuotient (R.Stratum I) U s

  -- Local labelled defining equations.
  definingEquations : LabelledDefiningEquations ...
  defining_zero :
    ... -- E_i agrees locally with {f_i = 0}
  conormal_eq :
    ... -- du_i corresponds to df_i on the normal quotient

  -- A tubular parametrisation on a neighbourhood of the zero section.
  tube : ...
  tube_zero : ...
  tube_isLocalDiffeomorph : ...
  tube_verticalDerivative :
    ... -- derivative induces normalEquiv

  -- Existing fibre maps represent its germs.
  Φ_germ_eq : ...
```

A fibre `N_s → U` cannot be a local diffeomorphism onto an open subset of `U` unless the stratum is zero-dimensional. Either specify a transversal slice, or, preferably, use a map from the **total normal bundle** near its zero section.

Add straightening compatibility:

```lean
incident_eq :
  ∀ I s i, ∀ᶠ v in 𝓝 (0 : D.N I s),
    D.Φ I s v ∈ R.E i ↔ D.du I s i v = 0

nonincident_avoid :
  ∀ I s j, j ∉ I →
    ∀ᶠ v in 𝓝 (0 : D.N I s), D.Φ I s v ∉ R.E j
```

Here `i : I` in `incident_eq`. The second assertion follows from continuity, closedness, and the definition of the stratum; it should be a theorem, not an independent axiom.

Use `LabelledDefiningEquations`, `LabelledNormalBundle`, and `TubularBridge` wherever their existing conclusions suffice. Audit their actual statements before introducing parallel structures.

### B. Phase and density compatibility

These belong to a resolution of a **phase and measure**, rather than to bare normal data:

```lean
structure MonomialPhaseCompatibility ... where
  phaseUnit : ...
  phaseUnit_analytic : ...
  phaseUnit_pos : ...
  phase_eq_germ :
    ... -- K ∘ π ∘ Φ = phaseUnit * ∏ du_i^(2 * k_i)
```

Positivity requires the intended nonnegative-phase setting. An arbitrary analytic phase only gives a nonvanishing, possibly signed unit.

For the density, formulate a **full-dimensional change-of-variables statement** in stratum-and-normal coordinates:

```lean
structure ResolvedDensityCompatibility ... where
  baseDensity : ...
  jacobianUnit : ...
  jacobianUnit_regular : ...
  jacobianUnit_pos : ...
  pullback_density :
    ... -- tangential density ⊗ ∏ |u_i|^(h_i) du, times the unit
```

There is no ordinary full-dimensional Jacobian determinant of the normal fibre map alone. Distinguish the Jacobian unit of `π` from the prior factor, which may vanish.

### C. Which theorem needs what?

| Conclusion | Needed compatibility |
|---|---|
| Existing conditional scalar expansion | Existing analytic presentation and coefficient hypotheses |
| Jets expressed through the chosen `Φ` | Fibre differentiability/analyticity and `Φ_eq` |
| Jets interpreted as genuine geometric normal derivatives | Normal-quotient identification, derivative compatibility, tubular regularity |
| SNC incidence interpretation | Defining equations and straightening |
| Producing exact monomial chart presentations | Phase unit, a proved unit-normalisation construction, and domain control |
| Producing chart transport | Full change of variables, multiplicity control, density regularity |
| Continuous coefficient data over compact bases | Parameter-dependent analyticity with uniform radius/bounds |

Higher normal jets are generally **dependent on the tubular choice**; these additions do not make arbitrary tubular constructions canonical.

Also add to a geometrically certified chart:

```lean
label : Fin (n J + 1) ≃ ↥(strat J)
k_eq : ∀ a, chart.k a = R.k (label a)
h_eq : ∀ a, chart.h a = R.h (label a)
frame_conormal :
  ... -- du_(label a) ∘ frame is the corresponding
      -- coordinate functional times a nonzero scale
```

Without these, the chart exponents need not describe the advertised divisor.

`phase_normal` plus `Φ_eq` already yields the **a.e. exact phase identity on the presented positive box**. It does not yield SNC geometry, label matching, a neighbourhood identity, or the claimed Jacobian order. An upgrade from a.e. equality to pointwise equality needs continuity and appropriate support assumptions.

## 2. The core route: extract the shared analytic kernel

**Yes: use cores as the primary production interface.** Keep exact-sublevel certificates as a supported special case.

Separate chart data from the localisation mechanism.

### Shared chart data

```lean
structure ExpansionChartData ... where
  M : ℕ
  Base : Fin M → Type*
  -- TopologicalSpace, MeasurableSpace, BorelSpace as needed
  compactSpace_base : ...
  ν : ∀ J, Measure (Base J)
  finite_ν : ...

  n : Fin M → ℕ
  h k : ∀ J, Fin (n J + 1) → ℕ
  k_pos : ∀ J a, 0 < k J a
  b : Fin M → ℝ
  b_pos : ∀ J, 0 < b J
  β : ℝ
  β_pos : 0 < β

  x : ∀ J, TangentialData (Base J) (n J + 1)
  fluct_zero : ...

  Φ : ∀ J, Base J × (Fin (n J + 1) → ℝ) → U
  measurable_Φ : ...
  c : ∀ J, Base J × (Fin (n J + 1) → ℝ) → ℝ
  measurable_c : ...
  nonneg_c : ...

  phase_normal : ...
  amplitude_eq : ...
```

Define rather than store:

```lean
obsFibre J s := fun u => L.obs (Φ J (s, u))
```

For the scalar expansion alone, `Φ`, `c`, and their identities are unnecessary. They are needed for the coefficient-factorisation and geometric interpretation API.

Keep localisation separate:

```lean
structure ExpansionLocalisation (F : ExpansionChartData L) where
  remainder : ℝ → ℝ
  integral_eq :
    ... -- L.Z = sum of chart integrals + remainder
  remainder_exp_small :
    ... -- using the library's exponential-smallness predicate
```

The two adapters **prove** this structure:

* `AdaptedStrataData`: existing sublevel decomposition plus its off-sublevel remainder.
* `AnalyticCoreDecomposition`: core measure decomposition plus phase-gap tail.

Do not replace this proof obligation by a field asserting the desired expansion.

### Resolved core certificate

```lean
structure ResolvedCoreCertificate ... where
  L : LocalisationData U
  obs_eq : L.obs = φ ∘ R.π
  phase_eq : L.phase = K ∘ R.π
  transport : ...

  M : ℕ
  n : Fin M → ℕ
  strat : Fin M → Finset R.Component
  base : ∀ J, Set (R.Stratum (strat J))
  isCompact_base : ...
  β : ℝ
  β_pos : 0 < β

  cores :
    AnalyticCoreDecomposition L M (fun J => ↥(base J)) n β

  T : ... -- core version of NormalMomentPresentation
  frame : ...
  Φ_eq : ...
  label : ...
  k_eq : ...
  h_eq : ...
```

The core moment presentation is a genuine missing lemma/interface, not supplied merely by the existing `cutoffExpansion`.

**Transfer strategy:** generalise `CoefficientCertificate` and `ofSeries` over the shared chart kernel; generalise the moment-series argument over kernel plus localisation. Keep the old theorem names as wrappers. This avoids duplicating CCCIII–CCCX.

## 3. Producing certificates: start with a theorem whose hypotheses actually suffice

There are two different milestones.

### A. Immediate producer: analytic series on a whole rectangular box

For `d > 0`, `k_i > 0`, positive side lengths, monomial phase, and nonnegative prior:

```lean
theorem exists_resolvedCoreCertificate_of_boxSeries
    (hϕ : ... uniform absolutely summable series on a larger polydisc ...)
    (hφ : ... same ...)
    (hϕ_nonneg : ∀ w ∈ W, 0 ≤ ϕ w) :
    ∃ C : ResolvedCoreCertificate R D W K ϕ φ,
      Nonempty (CoefficientCertificate C.toExpansionChartData)
```

Here:

* For a positive rectangle, use **one chart**, based at the origin.
* For a symmetric cube, use the `2^d` signed orthants.
* Rescale to a common coordinate box; for example `b = 1` and
  `β = ∏ b_i^(2*k_i)`.
* The base measure is a Dirac mass on the singleton origin stratum.
* Cores are the restricted prior-weighted orthant measures.
* Boundary overlap is Lebesgue-null.
* The tail is zero.
* `h = 0`; the density contains the constant linear-change-of-variables factor.
* Produce the actual density series and observable series, then invoke the Cauchy-product/`ofSeries` machinery.

**No all-strata partition is needed here.** Faces of the normal box already account for approach to the other strata.

Crucially, “real analytic on a neighbourhood of the closed box” does **not** imply that the Taylor series at the origin converges on that box. The larger-polydisc/series hypothesis is substantive.

### B. General compact-box analytic producer

The intended next theorem is:

> For a positive-dimensional coordinate monomial model on a compact rectangular box, with prior and observable analytic on a neighbourhood of that box and prior nonnegative there, construct a finite resolved core certificate and its coefficient certificate.

Treat this as a **target theorem**, not as an immediate consequence of the current interfaces.

Its geometric lemma must produce:

1. Compact patches contained in exact strata—not `S_I ∩ box` indiscriminately, which is generally noncompact.
2. Finite positive measures represented by normal product boxes.
3. Exact coverage of a neighbourhood of the entire zero divisor, modulo null sets.
4. A positive residual measure supported where the phase has a uniform positive lower bound.
5. Chart densities analytic in normal variables, with uniform coefficient bounds and continuous dependence on the compact base.

The main trap is:

\[
K(s+u)=\left(\prod_{j\notin I}s_j^{2k_j}\right)
        \prod_{i\in I}u_i^{2k_i}.
\]

Normalising this tangential unit changes normal widths. Naively partitioning into small/large coordinate rectangles therefore does **not** immediately give constant-`β` presentations. Nor may one hide the resulting boundaries in an analytic amplitude.

Likewise, a smooth partition of unity is not automatically analytic in the normal variables. The required partition must have a proved normal-analytic form, or its nonanalytic part must lie entirely in the phase-gap region.

### Curved sublevels

The core route avoids partitioning `{K < δ}` altogether. Cores may cross that boundary. What matters is:

\[
\mu=\sum_J\mu_J+\mu_{\rm tail},
\qquad K\geq\delta_0>0\quad\mu_{\rm tail}\text{-a.e.}
\]

The tail estimate also needs the relevant integrability of the observable. The phase gap alone is not enough.

### Producer sequence and gates

1. **Rectangular series producer.** Gate: arbitrary admissible density/observable series, not another hand-built polynomial instance.
2. **Parameterised series producer.** From a uniform analytic extension/bound on a larger normal polydisc, construct the continuous weighted coefficient datum. Gate: continuity in the actual `DataSpace` topology, not merely coefficientwise continuity.
3. **Normal-unit normalisation.** Gate: exact phase identity, transformed density, and explicit domain control.
4. **Finite analytic-normal collar decomposition.** Gate: positive exact measure decomposition and uniform tail gap.
5. **General compact-box producer.** Assemble the preceding theorems.

`polySeriesD` supplies Taylor coefficients; it does not by itself discharge gates 2–4.

## 4. Hironaka: measure refinement is not resolved geometry

There are two distinct adapters.

### A. A chart-level analytic expansion adapter

A common resolved manifold is unnecessary if `PartialResolution` is strengthened to provide:

```lean
sourceMeasures : ...
transport_sum : ∑ chartPushforwards = targetMeasure
localCoreDecompositions : ...
analytic_normal_densities : ...
phase_gap_remainders : ...
```

These outputs can be assembled into a core expansion theorem on the original space or on a disjoint union of chart spaces.

An a.e.-disjoint refinement of chart images solves **multiplicity bookkeeping only**. Its characteristic functions can destroy normal analyticity. Weighting by reciprocal multiplicity has the same problem unless regularity is proved.

### B. An honestly geometric resolved certificate

For genuine `ResolvedGeometry` with SNC normal compatibility, require either:

* an actual proper analytic resolution `π : U → ℝ^d`, with compatible SNC atlas and change-of-variables theorem; or
* transition data sufficient to construct that object, including the necessary topological gluing properties.

The current finite family of analytic maps does not provide this.

A disjoint union can sometimes manufacture the present **weak** `ResolvedGeometry`: compact chart domains can give properness, and component labels can remain chart-local. It does not manufacture an intrinsic global resolution or repair analytic multiplicity weights.

The honest conditional theorem is therefore:

> A proper SNC resolution equipped with a proved analytic-normal core decomposition and uniform coefficient bounds produces a resolved core certificate and coordinate-free expansion.

Do not claim that `PartialResolution` currently discharges those hypotheses.

For `BlowUpCube`, the audit should check concrete outputs against four gates:

1. exact positive measure transport, including multiplicity;
2. constant-monomial phase on actual product domains;
3. analytic normal density with uniform parameter bounds;
4. coverage near the full zero locus and a phase-gap remainder.

The supplied context does not establish that its existing outputs pass these gates.

## 5. Ranking, sizes, and the first two units

Sizes below mean proof units, not verified module counts.

| Priority | Work | Rough size | Acceptance gate |
|---|---|---:|---|
| 1 | Shared chart kernel and core transfer | 2–4 | Existing coefficient/representation results work for cores |
| 2 | Rectangular series certificate producer | 2–4 | Produces both certificates for a family of inputs |
| 3 | Genuine SNC/tubular compatibility | 3–6 | Coordinate model satisfies it; normal/conormal interpretation proved |
| 4 | Uniform parameterised analytic data | 3–6 | Continuous `DataSpace`-valued amplitude constructed |
| 5 | Unit normalisation and collar decomposition | 6–12+ | General compact-box analytic producer |
| 6 | Hironaka adapter | Unbounded until audited | Four output gates above |
| 7 | Projector blow-up | Defer | Clear consumer and adapter first |

### First unit

**`CoreNormalMomentRepresentation`**

Extract the chart-local moment argument so that it applies to `CorePresentation`. Prove the finite-core moment representation with an exponentially small remainder.

Gate: a theorem for cores, not just new projection definitions.

### Second unit

**`CoordinateBoxCoreCertificate`**

Construct the resolved core certificate—and its actual density-series coefficient certificate—for positive rectangles and signed orthants under explicit larger-box series hypotheses.

Gate: exact transport, exponent/label matching, `Φ_eq`, zero tail, and checked coefficient factorisation.

These two units change the programme from **“assume a certificate”** to **“produce certificates for a substantial geometric class”**, without pretending that the difficult analytic collar decomposition has already been solved.
