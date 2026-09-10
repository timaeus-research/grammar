## Recommendation

**Proceed. There is no longer a mathematical reason to postpone the embedded-Euclidean bundle programme.** The remaining work is mostly bundle packaging and local-to-global compatibility—not a new tubular-neighbourhood proof.

There are, however, three boundaries to preserve:

1. **An LCI atlas is not yet a Mathlib manifold structure on its zero set.**
2. **A uniform-radius tubular theorem is not a theorem for every noncompact embedded submanifold.** Retain all hypotheses of StrucDual’s existence results.
3. **A bundle theorem for an embedded \(X\subset E\) is not yet a theorem about the paper’s resolved manifold \(U\).** The current resolution interface does not supply that object.

I recommend eight files, numbered **units 8–15**. The dependency spine is:

```text
8  StrucDual adapter
9  smooth normal bundle from local frames
10 embedded-manifold normal frames
11 analytic LCI specialisation
12 conormal bundle exactness and labelled splitting
13 global normal-form sections
14 normal-bundle tubular equivalence
15 coordinate normal-crossing application
```

Unit 13 can proceed after unit 9; unit 14 after units 8 and 11.

All new declaration names below are proposals. Lean snippets are signatures in spirit, not claims about the exact parameter order of Mathlib’s bundle classes.

---

# 1. Programme: eight files

## Unit 8 — `StrucDualNormalFamily.lean`

### Inputs

A ported StrucDual `NormalTubularChart` or `AnalyticNormalTubularChart`, with its **actual domain and existence hypotheses retained**.

Write \(X\subset E\), \(N_x\subset E\), and let the tubular map be addition.

### Deliverables

Define the chosen-normal family by

```lean
def tubularNormalFamily ... : ChosenNormalFamily ... :=
  -- N x is the supplied normal submodule
  -- Φ x n = (x : E) + (n : E)
```

The family map can be defined on every fibre even though its tubular interpretation is restricted to the certified domain.

Prove:

```lean
theorem tubularNormalFamily_map ...
    : Φ x n = (x : E) + (n : E)

theorem tubularNormalFamily_proj ...
    (h : CertifiedTubeDomain x n) :
    tube.proj (Φ x n) = x

theorem tubularNormalFamily_ncoord ...
    (h : CertifiedTubeDomain x n) :
    tube.ncoord (Φ x n) = n

theorem tubularNormalFamily_decomp ...
    (hy : y ∈ tube.U) :
    Φ (tube.proj y) (tube.ncoord y) = y
```

Subtype/coercion versions will be needed; do not make later files repeatedly solve these.

Use `rawNormalJet_additive` to obtain the full-form identity

\[
J_r(F)(x)=D^rF(x)\circ(\iota_x,\ldots,\iota_x).
\]

For chart-local StrucDual coefficients, prove an explicit bridge

\[
\operatorname{normalCoeff}(F,b,x)
 =\frac{\partial_u^b[F(x+e_xu)]_{u=0}}{b!},
\]

**only after checking the definition of `normalCoeff`.** Iterated derivatives along *varying* normal vector fields need not equal fixed-fibre derivatives. In `ChartLocalTubular`, the constant coordinate-normal setting should make this bridge straightforward.

Transport `analyticAt_normalCoeff` through that bridge.

### API

StrucDual:

- `NormalTubularChart.decomp`, `proj_eq_of_decomp`, `proj_eq_self`;
- `ncoord`, `contDiffAt_ncoord`, `analyticAt_ncoord`;
- `stratum_analyticTubularChart`;
- `normalCoeff`, `analyticAt_normalCoeff`.

Grammar:

- `rawNormalJet_additive`;
- the CLXVI–CLXVIII coefficient and factorial bridges.

### Mirror impact

Certifies the chosen-normal construction **for an actual supplied Euclidean tube**, and gives the chart-local content of `rem:analytic_tubular`.

It does not yet certify an existence statement on the resolved \(U\).

### Stop rule

Do not rebuild the inverse-function theorem, enlarge StrucDual’s hypotheses, or introduce bundle topology here. If the coefficient bridge exposes a convention mismatch, record and repair the bridge—not the jet definition.

---

## Unit 9 — `NormalBundleOfFrames.lean`

### Inputs

A finite-dimensional smooth manifold \(X\), a family of submodules \(N_x\subset E\), a fixed fibre model \(V\), and a covering by local frames

\[
e_a(x):V\xrightarrow{\;\simeq_L\;}N_x.
\]

Require:

- continuity of the frame in ambient coordinates;
- continuity of its coordinate inverse;
- smooth transition functions
  \[
  t_{ab}(x)=e_a(x)^{-1}e_b(x):V\to V.
  \]

These are construction data, not a theorem that arbitrary submodule families form bundles.

### Deliverables

A reusable constructor giving the total space

```lean
Bundle.TotalSpace V (fun x => N x)
```

its vector-bundle topology and smooth vector-bundle structure.

Schematic endpoint:

```lean
def normalVectorPrebundle (A : NormalFrameAtlas I N V) : VectorPrebundle ...

instance normalBundle_fiberBundle ...
instance normalBundle_vectorBundle ...
instance normalBundle_contMDiffVectorBundle ...
```

Also prove:

- the supplied frames are smooth local trivialisations;
- the fibre inclusion \(N_x\hookrightarrow E\) is a smooth fibrewise-linear bundle map;
- a coordinate criterion for smooth sections of \(N\).

Use `Bundle.TotalSpace`, not an unrelated sigma-type topology.

### API

Mathlib:

- `Topology/VectorBundle/Basic` and the `VectorPrebundle` machinery;
- `Geometry/Manifold/VectorBundle/Basic`;
- `FiberwiseLinear.lean`;
- `LocalFrame.lean`.

The exact constructor connecting a `VectorPrebundle` to `ContMDiffVectorBundle` should be checked in v4.33.1. Expect to provide smoothness of coordinate changes explicitly.

**Do not assume `LocalFrame.lean` constructs a bundle from no topology:** some of its API starts with an existing bundle.

### Mirror impact

Supplies the genuine normal-bundle object required by the later dots. No paper theorem is complete merely from this constructor.

### Stop rule

Stop at bundles of subspaces of a fixed finite-dimensional \(E\). No general subbundle or quotient-bundle framework.

---

## Unit 10 — `EmbeddedNormalBundle.lean`

### Inputs

An existing finite-dimensional smooth manifold \(X\), a smooth embedding

\[
\iota:X\longrightarrow E,
\]

and a fixed codimension. Define

\[
T_x^{\mathrm{amb}}X=\operatorname{range}(d\iota_x),\qquad
N_x=(T_x^{\mathrm{amb}}X)^\perp.
\]

Using an abstract \(X\) first avoids making every proof depend on subtype manifold construction.

### Deliverables

Construct the local normal frames needed by unit 9, hence:

```lean
def embeddedNormalSpace (x : X) : Submodule ℝ E :=
  (LinearMap.range (dι x)).orthogonal

-- Schematic:
instance embeddedNormalBundle_contMDiffVectorBundle ...
```

Also produce a smooth fibrewise equivalence between the tangent bundle of \(X\) and its image in the ambient trivial bundle.

### Recommended frame construction

Avoid Gram–Schmidt.

In a local tangent trivialisation, obtain an injective smooth family

\[
A(x):W\to E
\]

whose range is \(T_x^{\mathrm{amb}}X\). Then

\[
P_T(x)=A(x)(A(x)^*A(x))^{-1}A(x)^*,
\qquad Q(x)=1-P_T(x).
\]

At a centre \(x_0\), choose a linear frame \(B:V\simeq N_{x_0}\). After shrinking,

\[
e(x)=Q(x)\circ B
\]

is a frame of \(N_x\). Injectivity persists near \(x_0\); equal dimensions give surjectivity onto \(N_x\).

This yields orthogonal-normal frames without producing orthonormal ones.

### API

Mathlib:

- `IsSmoothEmbedding`, its `contMDiff`;
- `IsImmersionAtOfComplement` and its normal-form chart data;
- `VectorBundle/Tangent.lean`, `FiberwiseLinear.lean`;
- finite-dimensional adjoints, orthogonal projections, matrix inversion.

`IsImmersionAtOfComplement` is a useful way to obtain the local tangent parametrisation and complement. It does **not** immediately identify its chosen complement with the metric orthogonal complement.

Precise smooth-inversion lemma names should be checked; a matrix-coordinate proof is an acceptable and often simpler implementation.

### Mirror impact

Makes “the normal bundle of an embedded submanifold” literal. It remains an embedded-model theorem, not a construction of the resolved space.

### Stop rule

Require a genuine manifold and smooth embedding as input. Do not solve arbitrary-subset recognition here. Fixed codimension is sufficient; locally varying rank is out of scope.

---

## Unit 11 — `LCINormalBundle.lean`

### Inputs

StrucDual’s `CompatibleAnalyticLCIAtlas r S`, with all its rank and zero-set hypotheses.

### Deliverables

There are two distinct tasks.

**A. Give \(S\) its induced embedded-manifold structure.**

Use local regular-level-set charts to build a `ChartedSpace` on the subtype and prove that the inclusion is a smooth embedding.

Prefer existing submersion/immersion normal-form APIs. If these do not directly consume the StrucDual local charts, expose a small adapter from those charts to the required manifold charts.

**B. Construct the normal bundle directly from Jacobian frames.**

On patch \(a\),

\[
e_a(x)c=J_a(x)^*c,\qquad
e_a(x)^{-1}n=(J_aJ_a^*)^{-1}J_an.
\]

On an overlap,

\[
t_{ab}(x)
 =(J_aJ_a^*)^{-1}J_aJ_b^*.
\]

Prove that these are inverse fibre coordinates and satisfy the cocycle laws. Feed them to unit 9.

Finally identify this bundle with unit 10’s bundle:

\[
\operatorname{range}J_a(x)^*
 =(\ker J_a(x))^\perp
 =(\operatorname{range}d\iota_x)^\perp.
\]

This last tangent-space identification is essential; matching names such as `tangent` is not enough.

### Analytic deliverable

Prove analytic transition coefficients in local analytic coordinates. Since inversion is analytic on invertible matrices, the displayed formula is the right proof.

If v4.33.1’s manifold/bundle regularity API supports the needed analytic order cleanly, package that instance too. Otherwise deliver:

- an honest `ContMDiffVectorBundle` structure;
- a separately stated analytic transition theorem.

Do not advertise an “analytic vector bundle instance” merely from the smooth one.

### API

StrucDual:

- `CompatibleAnalyticLCIAtlas`;
- `normal_eq_chart`, `analyticAt_J`;
- `normalSpaceOf_eq_orthogonalSubmodule_tangent`;
- `gram_isUnit`, `fullRowRank_iff_surjective`;
- the local analytic inverse charts used by its tubular construction.

Mathlib:

- `Submersion.lean`, `Immersion.lean`;
- `ChartedSpace`/`IsManifold` construction APIs;
- unit 9’s frame constructor.

### Mirror impact

An actual smooth normal bundle—and analytically varying local frames—for regular analytic Euclidean strata.

### Stop rule

The subtype manifold structure must either be constructed or supplied by an explicit intermediate hypothesis. If only the latter lands, label it **conditional**, not “LCI atlas produces a normal bundle” without qualification.

No manifold gluing for the resolution.

---

## Unit 12 — `ConormalBundleExact.lean`

### Inputs

Unit 10’s embedded manifold and normal bundle.

### Deliverables

Realise the conormal bundle using the metric dual of the orthogonal normal bundle:

\[
n\longmapsto \langle n,-\rangle\in E^*.
\]

Define the actual bundle maps in

\[
0\longrightarrow N^*X
 \xrightarrow{j}X\times E^*
 \xrightarrow{\mathrm{res}}T^*X
 \longrightarrow0,
\]

where

\[
\mathrm{res}_x(\lambda)=\lambda\circ d\iota_x.
\]

Prove:

- both maps are smooth fibrewise-linear maps;
- `j x` is injective;
- `res x` is surjective;
- `range (j x) = ker (res x)` for every \(x\).

That is a genuine exact sequence of bundles: smooth bundle maps plus fibrewise exactness. No categorical exactness framework is required.

Package \(T^*X\) through the existing Hom-bundle machinery, or through the local dual transition maps if the particular Hom instance is awkward.

### Labelled normal-crossing addition

Under explicit labelled local defining equations \(u_i\), independent differentials, and overlap laws

\[
u'_i=g_i u_i,\qquad g_i|_X\ne0,
\]

construct the line bundles

\[
\mathcal L_i|_x=\mathbb R(du_i)_x
\]

and a smooth bundle isomorphism

\[
\bigoplus_i\mathcal L_i\simeq N^*X.
\]

For finite labels, a fibrewise dependent product is an adequate model of the direct sum.

Require label preservation. If transitions permute components, the individually labelled global line bundles need not exist.

### API

Grammar’s `ConormalSplitting.lean`, especially:

- `conormalSplitting`;
- `fderiv_mul_of_eq_zero`;
- `conormalLine_unit_mul`;
- metric-annihilator identification.

Mathlib’s `Hom.lean`, `FiberwiseLinear.lean`, and finite-dimensional duality.

### Mirror impact

- `eq:conormal_sequence`: honest embedded-manifold theorem.
- `eq:decomp_nx`: honest bundle theorem under the labelled normal-crossing transition hypotheses.

### Stop rule

No quotient bundle, no sheaves, no general exact category. Prove exactness of these maps and smoothness of this splitting.

---

## Unit 13 — `GlobalNormalSections.lean`

### Inputs

The normal bundle with its smooth frame atlas, and chosen fibre maps \(\Phi_x\).

### Deliverables

Define compatible symmetric-form sections without constructing a symmetric-power bundle.

A suitable shape is:

```lean
structure IsGlobalNormalSection
    (A : NormalFrameAtlas I N V)
    (r : ℕ)
    (σ : ∀ x, JetForm (N x) r) : Prop where
  symmetric : ∀ x, IsSymmForm (σ x)
  smooth_coord :
    ∀ a, SmoothOnFrameDomain a
      (fun x => pullForm (A.frame a x) (σ x))
```

Here

\[
\operatorname{pullForm}(e)(\alpha)=\alpha\circ(e,\ldots,e).
\]

`SmoothOnFrameDomain` should be implemented either on the open-domain subtype or by a `ContMDiffOn` coordinate expression. Avoid arbitrary dependent functions outside the frame domain.

Prove:

1. smoothness in the selected covering frames implies smoothness in **every smoothly compatible local frame**;
2. equivalent frame atlases define the same predicate;
3. degree-zero compatibility;
4. global normal Taylor forms:

\[
\sigma_r(x)=\frac1{r!}D^r(F\circ\Phi_x)(0).
\]

The hypotheses must ensure that, locally,

\[
G_a(x,u)=F(\Phi_x(e_a(x)u))
\]

is jointly smooth near the zero section.

For the currently available symmetry API, the first clean theorem can require \(G_a(x,\cdot)\) analytic at zero, or explicitly require symmetry of its \(r\)-jet. Do not silently infer that CLXVIII already supplies smooth Schwarz symmetry.

For the additive realisation and analytic ambient \(F\), give the unconditional application theorem.

Also globalise the labelled weight components under the diagonal transition hypotheses from unit 12.

### API

Grammar:

- `rawNormalJet_comp_equiv`;
- `normalTaylorForm_comp_equiv`;
- `contDiff_normalTaylorCoeff`;
- `weightForm_compDiag`;
- `normalJet_weight_tensor_invariant`.

For the transition proof, fixed-dimensional coordinates reduce smoothness to finite sums and products of matrix entries and form components.

### Mirror impact

The “global section” clauses of `defn:normal_diff` and `lem:normal_deriv`, **relative to a chosen normal family**. The weight-line clause requires the labelled splitting.

### Stop rule

No `Sym^r` bundle functor and no multilinear-map bundle library. No claim of independence from the chosen tube.

---

## Unit 14 — `NormalBundleTubularEquiv.lean`

### Inputs

A unit-11 normal bundle and a StrucDual tube, with their normal fibres identified.

### Deliverables

Define

\[
A(x,n)=\iota(x)+n
\]

on the **certified open domain** \(D\subset NX\), and

\[
B(y)=\bigl(p(y),y-\iota(p(y))\bigr),\qquad y\in U.
\]

Prove:

- \(D\) is open in the normal-bundle total space;
- \(U\) is open;
- \(A(D)=U\);
- \(A\circ B=\mathrm{id}\), \(B\circ A=\mathrm{id}\);
- both maps are smooth.

Package at least a diffeomorphism of open subtypes:

```lean
noncomputable def normalTubeDiffeomorph :
    Diffeomorph ... (OpenDomain D) (OpenDomain tube.U)
```

The exact notation for open subtypes and `Diffeomorph` parameters is to be checked.

An `OpenPartialHomeomorph` on the full total space is also useful, especially since StrucDual already works with that object. There is little value in making `IsLocalDiffeomorph` the main endpoint once a global inverse on \(D\) is available.

Prove the zero-section and retraction equations.

For the analytic tube, additionally prove analytic coordinate expressions for both maps.

### Domain caution

Do **not** guess that

\[
D=\{(x,n):\|n\|<\varepsilon\}
\]

from the name `NormalTubularChart`. Read the record’s coverage, base, and membership clauses. Some constructions distinguish a compact core from a larger stratum patch.

Use the actual domain. Identify it with a full radius band only when the record proves that fact.

### API

StrucDual:

- `isOpen_embTube`, `analyticAt_embProj`;
- `exists_analyticNormalTubularChart_of_atlas`;
- `exists_normalTubularChart_of_atlas`;
- `NormalTubularChart` inverse identities.

Mathlib:

- bundle total-space manifold machinery;
- `Diffeomorph.lean`, `LocalDiffeomorph.lean`;
- `OpenPartialHomeomorph`.

### Mirror impact

The tubular-neighbourhood existence sentence and `rem:analytic_tubular` **for the precise embedded-Euclidean hypotheses exported by StrucDual**.

### Stop rule

No variable-radius theorem unless StrucDual already supplies one. No exponential map, geodesics, intrinsic Riemannian tubular theorem, or extension to an arbitrary ambient manifold.

---

## Unit 15 — `CoordinateNCBundles.lean`

### Inputs

A coordinate normal-crossing configuration in an ambient Euclidean chart, with a labelled stratum and its open chart domain.

### Deliverables

Apply the whole construction to coordinate strata:

- constant tangent and normal subspaces;
- the trivial normal bundle;
- the labelled conormal line bundles;
- the bundle exact sequence and splitting;
- the coordinate tubular map from `stratum_analyticTubularChart`;
- global-in-the-chart normal Taylor sections;
- agreement with `chartNormal`, `topFrame`, and CLXXII’s contractions.

Conclude with an application interface for resolution charts:

```lean
theorem resolutionChart_normal_geometry
    (c : ...) (hc : IsMonomialChart ...)
    (hgeom : RequiredChartStratumGeometry c) :
    ...
```

Any `hgeom` not derivable from the current resolution API must remain visible. In particular, monomial phase data alone should not be used as evidence of a glued resolved manifold.

### Mirror impact

Concrete, non-vacuous instances of all preceding statements on the strata actually used by the chart-local calculation.

### Stop rule

No cross-chart gluing of the resolved space. No manifold densities or integration. End by connecting to the existing measure-theoretic chart theorem.

---

# 2. Which normal-bundle route is best?

## For the immediate project: Jacobian frames

For StrucDual’s LCI atlas, the least painful route is unequivocally

\[
J_a^*:\mathbb R^r\overset{\sim}{\longrightarrow}N_x,
\qquad
(J_aJ_a^*)^{-1}J_a:N_x\overset{\sim}{\longrightarrow}\mathbb R^r.
\]

Advantages:

- the frames already match StrucDual’s normal spaces;
- full row rank and Gram invertibility already exist;
- transitions have an explicit matrix formula;
- smoothness and analyticity use the same formula;
- no square roots, orthonormalisation, or frame-selection theorem.

This is the route that gets the tubular application landed fastest.

## For arbitrary smooth embeddings: projected fixed frames

Use immersion charts or local tangent frames to construct \(P_T(x)\), then project a fixed complement frame by \(1-P_T(x)\).

This is a worthwhile general theorem, but it should be separate from the LCI adapter. It carries more tangent-bundle and manifold-calculus overhead.

## Gram–Schmidt: not the first implementation

It is mathematically valid, and can preserve analyticity locally under the appropriate nondegeneracy conditions. But orthonormality is not needed for:

- the normal bundle;
- smooth transition laws;
- Taylor forms;
- the tubular equivalence.

Its extra normalisation lemmas buy little here.

## What is the base?

**An actual `ChartedSpace` manifold.**

For an embedded subset, the subtype `S` is a good carrier, but the induced topology alone is insufficient. Equip it with the regular-level-set atlas and prove the inclusion is a smooth embedding.

Until that construction is present, one can honestly have a topological vector bundle over `S` and ambient-coordinate regularity statements. One cannot honestly call that a `ContMDiffVectorBundle` over a manifold without supplying the manifold structure.

---

# 3. Global sections: what exactly is invariant?

The clean definition starts with a fibre family

\[
\sigma_x\in\operatorname{SymForms}^r(N_x;\mathbb R).
\]

Compatibility is automatic at the fibre level: there is only one \(\sigma_x\). The nontrivial condition is smoothness of its frame coefficients.

If

\[
t_{ab}=e_a^{-1}e_b,
\]

then

\[
\sigma_b
 =\sigma_a\circ(t_{ab},\ldots,t_{ab}).
\]

This is the theorem that makes the definition independent of the covering frame atlas.

### The global Taylor-section theorem

A precise sufficient statement is:

> If the chosen normal family has jointly smooth local frame realisations near the zero section, \(F\) has the required regularity there, and the fibre jets are symmetric, then \(x\mapsto D_\perp^rF(x)\) is a global normal section.

For \(C^\infty\) data, all degrees are smooth. For finite regularity, one must track the loss of \(r\) derivatives.

For the first landed application, use analytic ambient \(F\) and additive normal maps, where the existing symmetry theorem applies.

### Important non-invariance

This does **not** make \(D_\perp^rF\) independent of the tubular choice.

Changing a frame in the same normal fibre is linear and gives the proved tensor transformation law. Changing the tubular parametrisation can introduce nonlinear fibre terms and alter higher normal jets. The paper’s wording should retain the chosen tubular structure.

### `Tensoriality.lean`

It is not the primary tool here.

Tensoriality lemmas are useful for recognising fibrewise tensors from suitably linear operations on sections. Here the fibre forms and their transition laws already exist. The missing task is smooth coordinate compatibility, which is simpler to prove directly.

Do not make this programme depend on a speculative use of that file.

---

# 4. What tubular theorem should we claim?

There are two endpoints:

1. **StrucDual’s Euclidean theorem:** a tube, projection, normal-coordinate decomposition, uniqueness, regularity.
2. **The bundle wrapper:** addition gives a diffeomorphism from an open neighbourhood of the zero section in \(NX\) onto an ambient open tube.

The second is the conventional bundle-level tubular statement and is worth doing. It is mostly a topology/smoothness adapter over the first.

But **uniform \(\varepsilon\) is an additional geometric conclusion, not part of every tubular-neighbourhood theorem**. Noncompact embedded submanifolds may require a variable radius. Preserve compactness, closedness, atlas, buffer, and coverage hypotheses exactly as they appear in the StrucDual theorem.

For the analytic claim, use analyticity of addition and of the supplied projection/inverse in analytic bundle coordinates. There is no need for analytic partitions of unity.

Do not attempt:

- an intrinsic exponential-map construction;
- arbitrary Riemannian ambient manifolds;
- a general analytic tubular theorem assembled using analytic bump functions;
- a uniform-radius theorem with the existing geometric hypotheses erased.

---

# 5. Can we cheaply construct the resolved \(U\)?

**Not from monomiality certificates alone.**

A cheap `ChartedSpace` construction is possible only once one already has:

- a common carrier, or a justified quotient of chart domains;
- genuine coordinate embeddings;
- specified overlaps and transition maps;
- cocycle laws;
- smooth or analytic transition regularity;
- the required separation and countability properties;
- compatibility of the resolution map and divisor labels.

`IsMonomialChart` describes the phase or map in coordinates. It does not, by itself, provide this gluing package.

Even the quotient of a finite collection of chart domains is not automatically Hausdorff, nor does it automatically carry the intended exceptional divisor.

Therefore:

> Keep this programme in the embedded-Euclidean model and apply it to coordinate strata chart by chart.

That matches the current resolution API and the actual asymptotic computation. A later resolved-space construction should be a separately authorised project, with its input contract established before any topology is built.

---

# 6. Dot policy at the end

Use three categories: **proved general embedded theorem**, **proved chart application**, and **not instantiated on the paper’s \(U\)**.

| Paper statement | Honest outcome |
|---|---|
| `eq:conormal_sequence` | **Yes:** smooth bundle maps and fibrewise exactness for an embedded manifold. **Not yet** its instantiation on resolved \(U\). |
| `eq:decomp_nx` | **Yes:** smooth labelled line-bundle splitting under normal-crossing overlap/unit hypotheses. Coordinate-chart instances are concrete. |
| `eq:decomp_sym_nx` | **Yes in compatible-family language:** global weight lines/components under diagonal labelled transitions. **No claim** of a constructed symmetric-power bundle functor. |
| `defn:normal_diff`: “defines a global section” | **Yes:** a smooth compatible family of symmetric fibre forms, relative to the chosen normal family and explicit regularity hypotheses. |
| `lem:normal_deriv`: frame invariance/globality | **Yes:** smooth frame covariance and labelled weight-tensor globality. |
| Tubular-neighbourhood existence sentence | **Yes:** embedded-Euclidean theorem with StrucDual’s actual hypotheses; explicit coordinate-stratum instances. **No:** an unrestricted ambient-manifold theorem. |
| `rem:analytic_tubular` | **Yes:** analytic embedded/chart model under the supplied analytic LCI/tube hypotheses. **No:** automatic instantiation on the unresolved formal object \(U\). |
| Smooth density pushforward on manifolds | **No:** deliberately outside this programme. |
| Tubular measure disintegration on general manifolds | **No:** existing results remain product-fibre measure theorems. |
| Independence from the choice of tube | **No:** generally false for higher normal jets without additional qualifications. |
| Corrected Taylor–moment identities | Already proved; this programme supplies genuine geometric instances, not stronger asymptotic claims. |
| \( \widetilde M_\gamma=c_0M_\gamma+\text{subleading}\) at coefficient level | Still **no**: bundles do not repair the coefficient error. |
| A global normal-crossing divisor on the formal resolved \(U\) | **No within this programme:** requires a new resolved-space interface and gluing construction. |

**Bottom line:** authorise the bundle work, but call the endpoint **“smooth normal bundles and tubular equivalences for embedded Euclidean strata, with coordinate-resolution applications.”** That is substantial new geometry, directly usable by Grammar, and does not disguise the missing resolved-manifold object.
