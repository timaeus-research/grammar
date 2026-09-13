## Recommendation

Build this in three layers:

1. **A parameterised, weighted active-coordinate collar**, reusing the combinatorics of CCCXXII–XXIV and the cores of E2.
2. **A domain-sector integration layer**, handling selected orthants, rectangular scaling, and restricted exact transport.
3. **An ambient-geometry realisation layer**, assembling those local certificates into a geometry for which properness and the required normal-data axioms actually hold.

Two qualifications should be explicit from the outset:

- The first producer covers a **tangential-unit domain-sector atlas**, not the present unrestricted `ProductSectorAtlas`: its phase unit may depend on active coordinates.
- Compact box sheets solve the **properness** problem, but do not automatically solve the **normal-geometry** problem. Restrictions of E1 to boxes need a separate construction and possibly a corner-aware interface.

No frontier positivity assumption is needed. The gap is a **collar-complement gap**, not a gap along `∂W`.

---

## 1. The per-chart producer

### 1.1 Choose (b), with a small extraction from (a)

I recommend **parameter reduction**, implemented by extracting the reusable active-coordinate combinatorics from CCCXXII–XXIV.

Do not begin by globally weakening every hypothesis in the existing full-active development. Although zero exponents are harmless in some products, they are not harmless in formulas involving inverse exponents, nonempty active faces, or positivity of sums of orders.

Use:

```lean
Active := ↥A
Inactive := ↥(Aᶜ)
```

and the coordinate equivalence

```lean
(Fin d → ℝ) ≃ₗ[ℝ] (Active → ℝ) × (Inactive → ℝ)
```

The existing full-active collar combinatorics then runs on `Active`. Inactive coordinates are compact parameters. For a face `I ⊆ A`, the base consists of:

- the active coordinates in `A \ I`, subject to the water-filling inequalities;
- all inactive coordinates, in their prescribed tangential ranges.

This is **not** a Fubini-only reduction to numerical expansions at each parameter. The construction must retain the parameter in the core base and establish uniform packet/series bounds there. Otherwise it does not produce the desired geometric certificate.

### 1.2 A useful explicit normalisation

Allow a rectangular positive box with widths `a_j > 0`. Write the phase as

\[
P(x)=u(z)\prod_{j\in A}x_j^{2k_j},
\qquad z=x|_{A^c},
\]

with `u` positive and tangential.

For a nonempty `I ⊆ A`, put

\[
p_I=\sum_{j\in I}2k_j,
\]

and define, at a tangential point `t`,

\[
\ell_I(t)=
\left(
\frac{\beta}
 {u(z)\,
  \prod_{j\in A\setminus I}t_j^{2k_j}\,
  \prod_{j\in I}a_j^{2k_j}}
\right)^{1/p_I},
\qquad
\lambda_j(t)=a_j\ell_I(t),\quad j\in I.
\]

The base imposes the usual water-filling inequalities

\[
t_j/a_j\geq \ell_I(t),\quad j\in A\setminus I,
\]

together with the box constraints. The core has `0 ≤ x_j ≤ λ_j(t)` for `j ∈ I`.

Then E2’s required identity is exactly

\[
u(z)\,
\underbrace{\prod_{j\in A\setminus I}t_j^{2k_j}}_{t_I(t)}
\prod_{j\in I}\lambda_j(t)^{2k_j}
=\beta.
\]

After `x_j = λ_j(t)v_j` in the normal coordinates,

\[
P(\Phi_I(t,v))=\beta\prod_{j\in I}v_j^{2k_j}.
\]

Thus the tangential unit belongs in `WData.hnorm`; it is not expanded into a perturbative normal-phase series.

A convenient global smallness condition is

\[
0<\beta<
\min_z u(z)\prod_{j\in A}a_j^{2k_j}.
\]

Further smallness may be imposed to fit the normal holomorphic radius.

The generalised collar should prove:

- finitely many cores indexed by nonempty `I ⊆ A`;
- compact bases and positive widths;
- pairwise a.e.-disjointness;
- coverage of `{P < β}` within the box;
- consequently, `P ≥ β` on the remaining box region, a.e.

Retain the existing tie convention if it already gives these conclusions.

### 1.3 Put weights in E2, not in the collar combinatorics

The water-filling construction depends on the phase, not on `h`.

For

\[
b(x)\prod_jx_j^{h_j}\,dx
\]

on a positive box, E2 already provides the normal/tangential factorisation. The additional collar proof should establish its measure identity first for restricted Lebesgue measure, then pass to the weighted measure by absolute continuity.

This avoids reproving disjointness or coverage separately for each Jacobian order.

The analytic amplitude supplied to the producer is, schematically,

\[
b=(\varphi\circ\phi_i)\,|\mathrm{jacUnit}_i|,
\]

including any constant scaling factors. On a connected chart box, `jacUnit` has constant sign, so its absolute value there is represented by either `jacUnit` or `-jacUnit`, both analytic.

### 1.4 Packet and face-series interfaces

There should be two theorem levels.

**Low-level certificate theorem**

Inputs include:

- `A`, `k`, `hk : ∀ j ∈ A, 0 < k j`;
- `h : Fin d → ℕ`;
- positive box widths;
- a positive tangential phase unit;
- the finite family of E2 `WData`;
- weighted face-series data for the scaled amplitudes and observables on their compact bases;
- nonnegativity and integrability hypotheses required by the certificate API.

Outputs:

```lean
ResolvedCertificate ...
CoefficientCertificate ...
```

and the collar expansion theorem.

**High-level packet theorem**

A schematic name is:

```lean
hasCoordFreeExpansion_of_holomorphicTangentialWeightedBoxExtension_local
```

Its packet should supply holomorphic extensions of the amplitude and observable near the **closed box**, with the uniform bounds needed to construct the face series. It also supplies, or is paired with, the positive tangential-unit data.

The intended chain is:

```text
holomorphic weighted box packet
    → common-radius original face series over all nonempty I ⊆ A
    → E2-scaled weighted face series
    → coefficient certificates for the cores
    → collar certificate and expansion.
```

The important new packet lemma is **uniformity over the parameter-dependent compact bases**. Pointwise holomorphic extension at every base point is not the final API.

Handle `A = ∅` separately: there are no low-phase cores, and compactness plus positivity of `u` gives an all-tail certificate. The expansion coefficients are zero.

### 1.5 Tangential units are the right stopping point

Yes. They cover:

- unit-free Watanabe-form charts;
- the cube charts;
- their reflections and origin-preserving diagonal scalings.

They do **not** cover arbitrary `Q'`-style units.

Moreover, absorbing a general unit by

\[
x_b' = x_b\,u(x)^{1/(2k_b)}
\]

is only a local analytic-coordinate argument. Even where the inverse function theorem applies, it generally turns a rectangular domain into a curved domain. Therefore:

> General-unit absorption and preservation/reconstruction of product sectors are a separate theorem package.

Do not describe the remaining work as “just IFT”.

---

## 2. Selected orthants, rectangular boxes, and inert boundary coordinates

### 2.1 Generalise the assembly interface, not the old coordinate model

Extract an assembly theorem whose inputs are already-built piece certificates:

```text
finite set of signs
+ per-sign localisation/certificate/coefficient data
+ reflection/scaling transport identities
+ a.e.-disjointness of piece measures
→ summed certificate and expansion.
```

Then the existing full signed-box theorem is the special case `signs = univ`.

The new `pieceCertificate σ` should instantiate the weighted tangential-unit producer, not the old full-active coordinate-model producer.

Under

\[
x_j=\epsilon_{\sigma,j}a_jv_j,
\]

the even phase orders are unchanged; the phase unit acquires the positive constant
\(\prod_{j\in A}a_j^{2k_j}\); and the density acquires the appropriate
\(\prod_j a_j^{h_j+1}\). Reflection transports the remaining analytic factors.

### 2.2 Do not translate active zero faces

A general box `[lo, hi]` cannot simply be affinely sent to a centred cube: translating an active coordinate destroys its monomial zero face.

Use origin-preserving scaling after the orthant split:

- if an interval crosses zero, its two sides have possibly different lengths;
- if it has zero as an endpoint, retain its one nondegenerate side;
- if it is bounded away from zero, treat that coordinate as a parameter on that piece.

For the last case, its phase monomial becomes part of the positive tangential unit. Thus the piece’s effective active set can be smaller than the atlas’s formal set `{j | k_j > 0}`.

A clean first high-level API can require **zero-adapted rectangles**. Add a preprocessing theorem for arbitrary nondegenerate boxes afterward. Rectangular widths already cover the cube’s `ρ`/`1` asymmetry without any problematic translation.

### 2.3 Inert boundary coordinates

Your interpretation is correct:

> A sign-constrained coordinate with `k_j = 0` is a one-sided tangential parameter, not a phase stratum and not a new core index.

Its order `h_j` can still contribute to the tangential density. It may describe a boundary divisor of `W`, but it is not a component of the zero divisor of the phase.

For finite orthant families, the overlaps are contained in

\[
\bigcup_j\{x_j=0\},
\]

which is Lebesgue-null in a nondegenerate full-dimensional box. Hence it is null for the absolutely continuous chart weights as well.

The required domain statement is:

\[
1_{\mathrm{dom}_i\cap\phi_i^{-1}(W)}
=
1_{\mathrm{dom}_i\cap\bigcup_{\sigma\in S_i}O_\sigma}
\quad\text{a.e. for chart Lebesgue measure}.
\]

This is the statement consumed by transport. A separate theorem that `∂W` is globally null is not needed for certificate assembly.

---

## 3. The hironaka domain-refined atlas

### 3.1 Suggested record boundary

Keep domain rectilinearity separate from tangentialisation:

```lean
structure DomainSectorAtlas ... extends ProductSectorAtlas ... where
  W : Set (Fin n → ℝ)
  measurableSet_W : MeasurableSet W
  W_subset : W ⊆ Ω
  signs : ι → Finset (CoordSign n)
  domain_ae :
    ∀ i, dom i ∩ φ i ⁻¹' W =ᵐ[volume]
      dom i ∩ selectedOrthants (signs i)
```

Depending on the existing convention, state the equality using `volume.restrict (dom i)` instead.

The domain `exactTransport` should preferably be a **derived theorem**, not another independent field. Apply the original atlas identity to `a * 1_W`, use `W ⊆ Ω`, then use `domain_ae` and orthant a.e.-disjointness. Schematically:

\[
\sum_{i,\sigma\in S_i}
(\phi_i)_*
\left(
1_{\mathrm{dom}_i\cap O_\sigma}
(a\circ\phi_i)J_i\,dy
\right)
=
1_Wa\,dw.
\]

For nonnegative measure-valued weights this is direct; signed observables remain outside the density and are handled by integrability.

Add a separate property or refinement:

```lean
HasTangentialPhaseUnits A
```

or a `TangentialDomainSectorAtlas` wrapper. The first producer theorem should visibly require it.

### 3.2 Constructor from jointly monomialised boundary functions

For each boundary function and chart, allow either:

```text
identically zero on the chart
```

or

\[
\pi_j\circ\phi_i
=
u_{ij}\prod_l y_l^{m_{ijl}},
\]

with `u_ij` continuous and nonvanishing on the connected box.

Choose its constant sign `ε_ij ∈ {−1,+1}`. An open orthant is admissible exactly when, for every nonzero boundary pullback,

\[
\epsilon_{ij}
\prod_l\epsilon_{\sigma,l}^{m_{ijl}}=+1.
\]

This is equivalent to your odd-exponent formula.

The proof splits into:

1. exact sign computation away from coordinate walls;
2. nullity of the finite union of walls.

Use **closed** orthants for compact pieces if desired; the resulting differences are on those walls.

### 3.3 Edge cases that must be represented

- **Identically zero boundary pullback:** the constraint is automatically satisfied. It must not discard the chart.
- **Domain consisting only of walls:** for example `x ≥ 0` and `−x ≥ 0`. There may be no admissible full-dimensional orthants, although the domain is nonempty. This is correct a.e. for ambient Lebesgue integration.
- **Positive-measure zero sets of boundary functions:** an identically zero constraint is the relevant analytic case on a connected open chart; it imposes no restriction. Do not infer that its zero set is null.
- **Nonclosed `W`:** measurable a.e. transport can still work, but compact packet production can fail. “Analytic near `W`” need not give analytic control near its missing limit points.

For the intended Watanabe setting, require compact `W` with analytic defining functions on a neighbourhood, or directly require packets on neighbourhoods of all selected compact chart pieces. If `W` is only relatively closed in `Ω`, check that the selected chart images stay inside the region where those packets exist.

There is also a **phase parity issue** for existence: nonnegativity of `K` only on `W` does not force even phase orders. For example, `K(x)=x` on `W=[0,1]` has an odd boundary order. To obtain the current even-order atlas, require the appropriate neighbourhood nonnegativity hypothesis, or allow general positive integer phase orders, or introduce justified power substitutions. Joint resolution alone does not fix parity.

### 3.4 What to seek in the existing joint-resolution exports

Yes: survey the family-resolution outputs before implementing another geometric existence theorem. I cannot infer the exact fields of `(E3)/(E5)` from the supplied description.

The useful statement is:

> For a finite analytic family containing `K` and all the `π_j`, there is one proper modification, with local coordinates in which every nonzero family member is a nonvanishing analytic unit times a coordinate monomial, and the Jacobian has a compatible monomial form.

Specifically inspect whether it supplies:

- one modification for the whole family, rather than separate resolutions;
- zero-function cases;
- principalisation only, or actual monomial forms for **each member**;
- analytic coordinate domains and unit nonvanishing;
- finite chart extraction over the relevant compact set;
- Jacobian monomialisation;
- sign/unit normalisation for `K`.

Principalisation of the ideal generated by the family is not, by itself, the required simultaneous individual monomialisation.

Even the desired local theorem does not yet supply finite, a.e.-disjoint product sectors with `exactTransport`.

---

## 4. Compact geometry and assembly

### 4.1 Use box sheets, not clamped Euclidean sheets—but audit normal data first

Between the two proposed constructions, prefer

\[
U=\coprod_i \mathrm{dom}_i
\]

with subtype sheets and

\[
\pi(i,y)=\phi_i(y).
\]

Finite compact boxes make `U` compact; continuity gives properness into the usual Hausdorff target.

Clamping a map defined on all of `ℝ^d` does **not** recover properness. Its image is compact, so the inverse image of that compact image is the entire noncompact sheet. It also breaks the global monomial phase identity outside the unclamped region.

However, there is a genuine additional proof obligation:

> Restricting a coordinate resolved geometry to a closed box does not automatically preserve its stratum and normal-data axioms.

Strata acquire corners or boundaries. If a box ends at an active zero face, even the normal direction is one-sided.

Audit the exact types of:

- strata and their manifold/topological structure;
- normal parameter domains;
- the phase-normalisation identity;
- core maps;
- the hypotheses of `mapAmbient`.

In particular, if a core map is required on **all** normal vectors and satisfies
\[
K(\pi(\Phi(s,v)))=\beta\prod v_j^{2k_j}
\]
for all such vectors, a compact target is impossible for a nonempty active normal set: the left side is bounded and the right side is unbounded. Such an API must be localised to the normal domain used by the core before a compact-sheet construction can work.

### 4.2 Recommended transport addition

Do not try to discharge the existing global `mapAmbient` compatibility with a clamp.

Add either:

- a box-native core constructor, whose normal maps land in the subtype on their actual parameter domain; or
- a supported/local-domain transport theorem, requiring pointwise phase compatibility where the core maps are used, and a.e. observable compatibility where the measure is used.

The exact statement depends on the existing `CorePresentation` quantifiers. It must preserve genuine pointwise normalisation on the relevant normal domain, not merely replace everything with an a.e. phase assertion.

If `ResolvedGeometry` fundamentally requires a boundaryless resolution manifold, use the actual resolved manifold as ambient—as in CCCLXVII—and retain boxes only as compact localisation supports. Properness does **not** require compact `U`; compactness is sufficient, not necessary. A proper noncompact resolution is another valid solution.

Thus compact box geometry should be an early **go/no-go unit**, not something postponed until after all analytic producers are complete.

### 4.3 Localisation and exact transport

On the box-sheet space, define the localisation measure by summing the selected sector densities on their respective sheets. Set the phase and observable by composition with the chart maps.

Then domain `exactTransport` identifies its pushforward with the original weighted measure on `W`.

The integral identity and the geometric assembly are separate:

- `exactTransport` proves the integral identity;
- the box/native-resolution geometry and transported normal data prove that this identity is witnessed by the desired certificate.

The former does not automatically supply the latter.

### 4.4 The tail gap

For each positive-active piece choose its collar threshold `β_p > 0`. For each empty-active piece use the positive minimum of its phase. Since there are finitely many pieces, choose a common positive lower bound `δ`.

The assembled remainder satisfies

\[
K\circ\pi\geq\delta
\quad\text{a.e. on the tail}.
\]

Coordinate boundary faces in the low-phase region are already part of the cores or their tangential bases. They do not need a separate frontier gap.

The a.e. chart/domain coverage leaves only null sets, not an additional positive-measure remainder requiring a new estimate.

---

## 5. Order, work units, and stopping rule

These are planning estimates, not measurements of the branch. Using one “tide” as the repository’s ordinary proof-development unit:

| Unit | Deliverable | Rough size |
|---|---|---:|
| A | `DomainSectorAtlas`, selected orthants, restricted exact transport | 1–2 tides |
| B | Boundary-monomial constructor, including zero pullbacks | 1–2 |
| C | Compact ambient/normal-domain feasibility spike | 1–2 initially |
| D | Extract active-coordinate water-filling lemmas; old theorem as special case | 2–3 |
| E | Parameterised tangential-unit collar and E2 core assembly | 2–4 |
| F | Weighted common-radius packets and coefficient producer | 2–4 |
| G | Rectangular selected-sign producer | 1–2 |
| H | Final geometry realisation, transport, assembly, congruence | 2–4, **conditional on C** |
| I | Cube and unit-free regression instances | about 1 |

Do A–C first. Then D–F. G and parts of B can proceed independently. H must not conceal a redesign discovered in C.

### First stopping theorem

The honest first target is schematically:

```lean
hasCoordFreeExpansion_of_domainSectorAtlas
  (A : DomainSectorAtlas ...)
  (hunit : A.HasTangentialPhaseUnits)
  (hboxes : A.HasSupportedProductSectorGeometry)
  (packets : A.SelectedSectorHolomorphicPackets ...)
  ...
```

If the name is intended to mean “from a `DomainSectorAtlas` alone”, use a narrower name until those extra hypotheses are built into a specialised atlas type.

The stopping rule should require:

- `ResolvedCertificate` and `CoefficientCertificate`, not just a finite-sum asymptotic;
- domain-restricted exact transport;
- boundary-only test cases;
- empty-active and empty-sign cases;
- the cube recovered through the generic producer;
- explicit compatibility of the assembled geometry with the certificate API.

Suggested non-claims:

> This theorem produces certificates from supplied finite domain-sector data with tangential phase units and suitable compact packet/geometry data. It does not yet establish existence of such an atlas for every jointly resolved analytic family, nor preservation of rectangular sectors under general-unit absorption.

### Transition to existence

The boundary favours **joint analytic rectilinearisation**, not a frontier-positive reduction.

The next existence target is stronger than ordinary local resolution:

```text
joint resolution of K and the boundary family
+ domain rectilinearity
+ finite product-sector localisation
+ exact multiplicity/transport control
+ phase-unit form compatible with the producer.
```

The difficult distinction is between:

1. normal-crossing local charts with orthant descriptions; and
2. a finite a.e.-disjoint rectangular sector atlas with exact transport and analytic packet-compatible weights.

Ordinary chart covers overlap. Disjointification can destroy rectangularity; smooth partitions of unity do not automatically preserve the holomorphic-amplitude interface. These issues need an explicit construction.

The descriptions of R1/R2/R6 are not included here, so I would not assign those labels speculatively. Prefer whichever route constructs joint domain-aware rectilinearisation and retains genuine proper geometry; use an existing Watanabe-form export if it actually carries that data. Keep unrestricted-unit `Q'` rectification as a later route unless it also controls the transformed domain.

---

## 6. Corrections and cautions in §§1–3

The reported existing producers are consistent with the proposed reuse. The main corrections are to the proposed deductions:

1. **Zero exponents do not justify a blind in-place generalisation.** Extract the positive-active combinatorics and treat inactive variables as parameters.
2. **General boxes require origin-preserving handling.** Arbitrary affine translation does not preserve monomial active faces.
3. **The unrestricted phase-unit atlas is stronger than the first producer supports.**
4. **Unit absorption may destroy product domains.**
5. **Compactness proves properness, not restricted normal geometry.**
6. **Clamped Euclidean sheets are not a properness solution.**
7. **Joint principalisation of an ideal is not automatically simultaneous monomialisation of every boundary function.**
8. **Identically zero boundary pullbacks must be allowed and ignored as constraints.**
9. **Analyticity near a nonclosed `W` is insufficient for uniform compact packets.**
10. **Even phase orders need justification beyond nonnegativity only on `W`.**
11. **Inert boundary faces are tangential for the phase certificate**, though they remain part of the domain-divisor data.
12. **The desired gap is off the cores, not on the frontier.**

The central reuse opportunity is substantial: E2 already contains the difficult weighted normalised-core machinery. The missing analytic producer is primarily a **uniform parameterised collar and face-series assembly**. The principal architectural risk is the proposed compact ambient geometry, not the boundary-sign calculation.
