## Executive recommendation

There is a genuine gap here, not a missing finite-cover adapter:

> **The exported local resolution theorem does not, by itself, give a finite a.e.-disjoint box atlas.**

Moreover, multiplicity correction does **not** repair this while preserving the current holomorphic-box hypotheses.

I recommend separating two programmes:

1. **Keep the existing analytic-box producer unchanged.** Prove conditional existence adapters and explicit, jointly monomial examples. Treat finite box transport and holomorphic packets as explicit hypotheses.
2. **For general existence from resolution, use smooth localization on the resolved manifold.** This avoids disjointness, but requires a genuinely new analytic-engine theorem for smoothly localized amplitudes. It is not a unit-scale wrapper around the current producer.

For joint resolution, the promising small mathematical lemma is **factorization of analytic factors of a coordinate monomial**, not the proposed real-zero-set criterion.

I cannot inspect the local fork here. Consequently, statements below about what the current exports imply are based on the signatures you supplied; I would not attribute an additional disjointness or joint-resolution theorem to `Q'_all` without its exact declaration.

---

## 1. Audit of the proposed steps

### (a) Properness and finite boxes: correct locally, with two important limitations

Write `Ω₀` for the open target of the modification, to distinguish it from the integration domain `W`.

For compact `K₀ ⊆ Ω₀`, properness into `Ω₀` makes
\[
g^{-1}(K₀)
\]
compact. The compactness assertion must be made for `K₀` regarded as a compact subset of the open subtype; this is an ordinary adapter, not a mathematical obstruction.

Near points above `{K = 0}`, choose smaller centered closed boxes whose **interiors** cover the points. Extract a finite subcover of the zero fibre over `K₀`. The centered Watanabe charts have nonempty active sets: evaluating their phase identity at the origin rules out all exponents being zero.

The limitations are:

* **Covering `g⁻¹ K₀` by boxes does not give boxes contained in `g⁻¹ K₀`.** Restricting them to that set destroys the box domains.
* **Compact support does not give exact transport on all of `W`.** It can give an identity for a particular supported density. Your `domainTransport`, an identity for arbitrary `a`, is stronger.

An arbitrary compact cutoff region introduces another boundary. It must be resolved, otherwise encoded, or handled by localization. Also, a nonzero real-analytic prior cannot have compact support inside a connected open analytic domain. Thus “compact support region” and “analytic prior” need a careful, explicit interpretation.

Off the zero set, the inactive charts are indeed tails. In fact, for the existence programme it is often easier to retain **one measurable tail region**, rather than build an atlas for it.

### (b) Disjoint box images: the decisive obstruction

Your diagnosis is correct. Neither compactness nor chart shrinking supplies a finite disjoint box decomposition.

Removing earlier images produces non-box domains. Dividing by image multiplicity generally produces nonanalytic amplitudes. Passing to overlap-pattern sets merely moves the non-box problem.

There is no cheap finite-cover argument that fixes this.

### (c) Tangential units: Watanabe is preferable, but joint resolution changes the picture

For resolving `K` alone, Watanabe’s exact unit `1` is ideal.

After resolving the product
\[
F=K\prod_j\pi_j,
\]
factor extraction will generally give
\[
K\circ g=v(y)y^{2k},
\qquad v>0,
\]
not unit `1`. Thus the product-resolution route still needs **unit absorption**.

At a centered chart with `k_j>0`, set
\[
z_j=y_jv(y)^{1/(2k_j)},\qquad z_\ell=y_\ell\quad(\ell\ne j).
\]
At the origin its derivative is invertible. After shrinking, this is an analytic coordinate change and the phase becomes exactly `z^{2k}`.

It also preserves boundary monomialization: its inverse has
\[
y_j=z_j\,q(z),\qquad q>0,
\]
so each old boundary monomial becomes a new boundary monomial times a nonvanishing analytic unit. The Jacobian has the same kind of monomial-times-unit form.

**But:** the coordinate change does not send the original box to a box. One chooses a new box inside its image. This is fine for local charts, but does not preserve a previously established exact disjoint box tiling.

### (d) Joint boundary forms: the proposed zero-set lemma is false over `ℝ`

The implication
\[
Z(a)\subseteq\bigcup_i\{y_i=0\}
\quad\Longrightarrow\quad
a=\text{unit}\cdot y^\alpha
\]
is false for real-analytic functions.

For example,
\[
a(x,y)=x^2+y^2
\]
vanishes only at the origin, hence only on the union of the coordinate axes, but is not a unit times a coordinate monomial at the origin.

The **divisibility identity**, however, is sufficient. See §3 below.

### (e) Complexification: mathematically available, not an automatic adapter

Real analyticity near a compact real box does imply a holomorphic extension to some complex neighbourhood, with full real agreement. But obtaining that result from Mathlib’s current API is a separate project.

For this programme, keep the packet interface initially. Polynomial or entire `prior` and `obs` alone do not solve it: the chart maps and Jacobian units must also be complexified.

### (f) Box normalization and tails: mostly ordinary adapters

An origin-preserving diagonal scaling normalizes a **centered rectangular box**
\[
\prod_j[-r_j,r_j]
\]
to `[-a,a]^d`. It does not normalize an arbitrary rectangle `[lo,hi]` to a centered box.

The scaling changes the phase by a positive constant and changes the Jacobian unit by the expected positive scaling factors. Thus tangentiality survives; exact phase unit `1` need not.

For tails, the useful statement is simply
\[
\left|\int_T \mathrm{obs}\,\mathrm{prior}\,e^{-nK}\right|
\le e^{-n\delta}\int_T|\mathrm{obs}|\,\mathrm{prior}
\]
when `K ≥ δ > 0` on `T`.

---

## 2. The disjointness decision

### 2.1 What the supplied `Q'` statements actually give

From your description, `PartialResolution` gives:

* finitely many charts;
* compact chart domains;
* smoothness near those domains;
* a.e. coverage;
* Jacobian data.

You have identified `aeDisjoint` as an **additional field of `ProductSectorAtlas`**. Therefore:

> Nothing in the supplied `Q'`/`PartialResolution` description establishes `ProductSectorAtlas.aeDisjoint`.

Likewise, the supplied description does not establish exact box domains.

A bound on
\[
m(x)=\sum_i1_{\phi_i(\mathrm{dom}_i)}(x)
\]
is not disjointness. Indeed `m(x) ≤ card ι` follows immediately from finiteness. A sharper theorem may be useful, but still does not imply `m = 1` a.e.

There is another distinction to check in the actual declaration:

* **image multiplicity** counts charts containing `x`;
* **area-formula multiplicity** counts preimages, including multiple preimages within one chart.

The image-multiplicity correction is valid only after establishing the relevant within-chart a.e. injectivity/change-of-variables statement. For charts inherited from a modification, the isomorphism off the exceptional set is the natural source of that fact.

The appropriate audit request for `Q'_all` is its exact conclusion concerning:

1. chart domains;
2. within-chart injectivity;
3. image multiplicity versus fibre multiplicity;
4. the measure with respect to which exceptional sets are null.

Do not infer these from the phrase “multiplicity bound.”

### 2.2 Why multiplicity weighting does not preserve the current engine

Assuming the required chartwise area formula, the correction is
\[
\frac{
 |\det D\phi_i(y)|\,a(\phi_i(y))
}{
 m(\phi_i(y))
}.
\]

This gives the intended measure identity on the covered set, but the resulting amplitude usually has jumps across overlap walls.

Even “multiplicity is locally constant a.e.” is insufficient for the current packet: it requires holomorphic extension across a neighbourhood of the **entire box**, not merely analyticity on pieces away from the walls.

A compatible special case is:

> For each chart, `m ∘ φ_i = c_i` a.e. on the relevant sectors, with `c_i` a positive constant.

Then multiply its holomorphic amplitude by `1/c_i`. This is a useful conditional adapter, but it is not a general existence argument.

Pattern-set splitting needs an additional theorem resolving or parametrizing the pattern regions by admissible boxes. It is not the solution to the problem it restates.

### 2.3 Dominant-coordinate blow-up charts: useful explicit construction, not a consequence of admissibility

For the standard blow-up of a coordinate subspace, dominance can select the normal-coordinate chart. Ties lie on walls, and the one-step bounded sectors often have product form.

For composites, however:

* the inverse image of a previous selected region need not be a product box;
* local coordinate changes need not preserve dominance inequalities;
* shrinking to resolution-normal-form neighbourhoods introduces further cuts;
* admissible centres being coordinate subspaces is a **local** assertion in suitable coordinates, not a single global cubical structure.

Thus the statement worth proving is conditional:

> **A finite composite equipped with compatible cubical sector refinements has an exact sector transport atlas.**

It is not:
> Every admissible composite automatically has such a cubical refinement.

`IsAdmissibleComposite` and `ChartData` alone, as described, do not supply the extra refinement data.

### 2.4 The standard general solution is smooth localization

Choose smooth functions `χ_i` on the resolved manifold, subordinate to finitely many chart interiors, with
\[
\sum_i\chi_i=1
\]
on the relevant inverse-image region. In chart coordinates `ψ_i`, use
\[
d\mu_i(y)=
 \chi_i(\psi_i^{-1}y)\,
 |\det D(g\circ\psi_i^{-1})(y)|\,
 a(g(\psi_i^{-1}y))\,dy,
\]
restricted to the boundary-admissible orthants.

Then chart overlap is harmless: the partition sums to one **on the manifold**, before blow-down. The exceptional locus is removed by the usual a.e. change-of-variables argument.

This suggests a **chart-localized transport interface**, with chart-dependent densities, rather than a multiplicity-weighted atlas.

The cost is substantial and explicit:

* nontrivial subordinate compactly supported cutoffs are smooth, not analytic;
* the holomorphic packet theorem does not apply directly;
* a smooth-amplitude monomial expansion theorem is required, with appropriate Taylor remainders and coefficient compatibility.

Such an engine is mathematically natural for all-orders asymptotic expansions. It is nevertheless a new theorem, not permission to pass smooth weights through the existing holomorphic theorem.

**Design choice:** do not generalize to arbitrary multiplicity weights as the main existence route. Either retain the current conditional exact-box interface, or build the smoothly localized route deliberately.

---

## 3. The smallest joint-monomialization lemma

The product route has a particularly economical algebraic core.

### 3.1 A factor-of-monomial germ lemma

A suitable theorem is:

> Let `a`, `b`, and `u` be real-analytic germs at `0 ∈ ℝ^d`, with `u` a unit. If
> \[
> ab=u\,y^N,
> \]
> then there exist `α, β ∈ ℕ^d` and analytic unit germs `v,w` such that
> \[
> \alpha+\beta=N,\qquad
> a=v\,y^\alpha,\qquad
> b=w\,y^\beta.
> \]

This does **not** require a general UFD theorem or Weierstrass preparation.

A proof needs these analytic-germ ingredients:

1. Germs form an integral domain.
2. Restriction to `y_j = 0` lands in an integral domain.
3. A germ whose restriction to `y_j = 0` is zero is divisible by `y_j` in analytic germs.

Consequently `y_j` is prime. Induct on `∑ N_j`, allocating each coordinate factor to one of `a,b`. At the end the residual product is a unit, so both residual factors are units.

Coordinate division can be proved directly by shifting convergent power-series coefficients. Whether that is a small Lean implementation depends on the available multivariate analytic APIs. It is a credible isolated unit/project; I would not promise a short proof without checking those APIs.

Iterate the binary theorem for finitely many factors.

### 3.2 Promote the germ identity to one box

Apply it to
\[
(K\circ g)\prod_j(\pi_j\circ g)=S\,y^N.
\]

After intersecting finitely many neighbourhoods and shrinking, obtain on a single centered box
\[
K\circ g=v_0y^\alpha,\qquad
\pi_j\circ g=v_jy^{m_j},
\]
where every `v_j` is analytic and nonvanishing near the box.

Nonvanishing units have constant sign on the connected box. Since `K ≥ 0` on a full neighbourhood:

* every component of `α` is even;
* `v₀` is positive.

Then absorb `v₀` along an active coordinate. The boundary monomial forms survive, as described above.

This produces exactly the **local** joint-normal-form packet needed by `ofBoundaryMonomials`. It does not produce finite exact transport.

### 3.3 Necessary nondegeneracy handling

Before applying Watanabe to `F`, address:

* boundary functions identically zero on the relevant connected neighbourhood: their inequalities are vacuous and should be removed;
* `K` identically zero: excluded by the stated Watanabe theorem and outside the nonempty-active-set programme;
* the choice of base point and translation to the theorem’s origin;
* nontriviality of the product germ.

For nonzero analytic factors on a connected open neighbourhood, analytic uniqueness supplies the needed nontriviality locally. This should be a named hypothesis/lemma, not silently assumed.

### 3.4 Does the tuple `Q'` already give this?

Not from the statements supplied.

A formula
\[
\Delta.D(\psi y)=u(y)y^\delta
\]
gives forms for the boundary factors **only if** an existing identity or divisibility theorem relates each desired `π_j ∘ φ` to this `D ∘ ψ`, in the correct coordinate spaces.

Merely putting the boundary functions in `fp` does not establish that relationship. The low-order branch condition about derivatives of `f_p` is not boundary monomialization.

Accordingly, the honest current answer is:

> No joint boundary-form export has been identified in the supplied declarations. Use a conditional joint chart packet, or add the factor-of-monomial theorem and apply it to a resolved product.

For this purpose I recommend Watanabe-plus-factor-extraction over `Q'`: it avoids having to eliminate the low-order branch as well.

---

## 4. Holomorphic packets: keep now, produce separately

### Immediate policy

Keep `HolomorphicSignedBoxExtension` as a hypothesis for the general adapter.

Produce it first for explicit charts where the relevant real functions are restrictions of known holomorphic functions:

* polynomial charts and polynomial amplitudes;
* rational charts with denominators nonzero near the real box;
* explicitly complexified charts, with polynomial or entire priors and observables.

A Gaussian of a polynomial expression has an entire complex extension. A Gaussian composed with an abstract real-analytic chart still needs the chart’s complexification.

The absolute Jacobian causes no special complexification obstruction: after shrinking to a neighbourhood where the real Jacobian unit has fixed sign `ε`, complexify `ε · jacUnit`, not an absolute-value operation.

### A reasonably small general complexification architecture

The gluing need not begin with a very general several-complex-variables sheaf theorem.

One can aim for:

1. complexification of a real-analytic germ to a complex ball centered at a real point;
2. uniqueness of holomorphic functions agreeing on a real open ball;
3. gluing extensions on complex balls with real centers;
4. a finite cover of the compact real box.

For two such balls, a nonempty intersection has a nonempty real slice: take the real part of a point in the intersection. The intersection is convex. Agreement on its real slice gives holomorphic agreement by the totally-real uniqueness lemma, obtainable locally from repeated one-variable uniqueness.

This is a concrete separate project. Its output should guarantee agreement on **all real points of the chosen complex neighbourhood**, exactly as your packet requires.

---

## 5. Ranked implementation programme

### Hironaka side

| Rank | Unit | Scope |
|---|---|---|
| **H1** | A conditional `JointEvenBoxChart` packet | Centered box, exact even phase, Jacobian monomial, boundary monomials and unit signs. No existence claim. |
| **H2** | Explicit monomial-box boundary atlas constructors | Exercise existing transport and `ofBoundaryMonomials`; no global resolution needed. |
| **H3** | Centered-box normalization | Positive diagonal scaling, including phase/Jacobian/boundary transformations. |
| **H4** | Analytic coordinate division and factor-of-monomial germs | The genuine algebraic prerequisite for product resolution. |
| **H5** | Finite-factor neighbourhood extraction | Joint local boundary forms from the resolved product. |
| **H6** | Positive-unit absorption preserving monomial divisors | Local exact-phase packet after shrinking. |
| **H7** | Properness-to-finite-local-cover adapter | Explicitly a cover, not a disjoint or transport atlas. |
| **H8** | General finite localized transport | Only after choosing the smooth-localization programme; substantial. |

In parallel, useful optional units are:

* constant-multiplicity transport with analytic constant weights;
* one-step dominant-coordinate blow-up transport with explicit compatible box data.

Do not label either a general atlas-existence theorem.

### Grammar side

| Rank | Unit | Scope |
|---|---|---|
| **G1** | Joint-box-packet → existing `SheetInputs` adapter | Reuse the current theorem; retain transport and holomorphic packets as hypotheses. |
| **G2** | Explicit boundary regression | Detailed below. |
| **G3** | Inactive-region exponential-tail theorem and assembly | Avoid requiring every chart in a global cover to be active. |
| **G4** | Polynomial/rational holomorphic-packet constructors | Enough for explicit regressions. |
| **G5** | Smoothly localized box expansion | New engine theorem, prerequisite to general manifold localization. |

Empty selected-sign families should be removable. A chart touching `W` only in a null boundary does not justify a nonempty `signs i`; it should contribute no sector and normally be discarded.

### Stopping rule

After **H1–H3 and G1–G4**, stop and record:

> Explicit and conditional jointly monomial domain-sector atlases feed the coordinate-free expansion theorem. General extraction of finite exact box transport from a proper analytic modification remains unproved.

Continue to H4–H7 if local joint-normal-form existence is itself the next deliverable.

Do **not** spend those units under the expectation that finite disjointness will then follow automatically. Before H8, make the explicit decision to develop G5 or to import/prove a stronger rectilinearization theorem with the necessary transport structure.

---

## 6. First genuine boundary regression

I recommend the two-dimensional crossing rather than `d = 1`:

\[
K(x,y)=x^2y^2,\qquad
B=[-1,1]^2,\qquad
W=B\cap\{x\ge0\},
\]
with identity chart, prior `1`, observable `1`, and Jacobian unit `1`.

Encode the outer box as the existing compact atlas region—or, if the domain presentation requires an open `Ω`, include its analytic inequalities explicitly.

The boundary data are:
\[
\pi(x,y)=x,\qquad u=1,\qquad m=(1,0).
\]
The selected orthants are exactly those with positive `x` sign; both `y` signs remain.

This tests:

* actual sign filtering by `ofBoundaryMonomials`;
* a proper subset of the orthants;
* two active coordinates;
* a crossing divisor;
* nontrivial logarithmic degree;
* trivial holomorphic packets.

For an independent numerical/asymptotic check,
\[
I(n)=\int_0^1\int_{-1}^1e^{-nx^2y^2}\,dy\,dx
\sim \frac{\sqrt\pi}{2}\,n^{-1/2}\log n.
\]

Unlike the cube regression, this exercises a logarithmic term and a genuine boundary selection simultaneously. It tests the boundary-to-producer bridge, although deliberately **not** the unresolved general resolution-to-atlas step.

A second small regression can use `π(x,y)=xy`, selecting the two same-sign orthants. That tests parity/sign products involving more than one coordinate.

---

## Bottom line

The clean claim hierarchy is:

1. **Done:** an appropriate `DomainSectorAtlas` plus analytic packets produces the coordinate-free expansion.
2. **Next, feasible:** explicit boundary examples and conditional jointly monomial chart adapters.
3. **Separate local theorem:** product resolution → individual monomial factors → even phase with unit absorbed.
4. **Still substantial:** proper local resolution → finite exact integration decomposition compatible with the analytic engine.
5. **Independent analytic infrastructure:** compact real-analytic data → holomorphic packets.

The two corrections that matter most are:

* **Real zero-set containment does not imply monomial-times-unit; actual factorization of a monomial does.**
* **Finite overlapping resolution charts cannot be converted to the present holomorphic box inputs by ordinary multiplicity correction.**

Keeping those distinctions explicit will preserve the axiom-clean work without overstating the existence theorem it currently supports.
