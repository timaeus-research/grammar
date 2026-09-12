## Bottom line

I recommend a **source-amplitude and certified-assembly programme**, not yet a global resolved-manifold programme.

There are two separate missing ingredients:

1. **Across charts:** ownership of overlapping resolution images.
2. **Within a chart:** compatibility between its arbitrary compact `dom` and the new product boxes.

Moving the partition upstairs solves the first problem **only if there is an upstairs space on which the charts are compatible**. Independently, it does not authorize replacing integration over `dom ∩ box` by integration over `box`.

That second issue requires a correction to your proposed units 3–4:

> From the supplied interfaces, an arbitrary monomial `ResolutionChart` does **not** automatically have an explicit whole-image coefficient obtained by covering its divisor locus with centred product boxes.

The boxes from CCLXX deliberately need not lie in the old `dom`. That is excellent for local geometry, but prevents the proposed whole-domain decomposition without further ownership/domain data.

The useful, unconditional replacement is:

> A continuous source amplitude compactly supported in `interior dom` can be localized into finitely many product boxes, with an exponentially small remainder.

Then separately assemble these localized integrals using an exact decomposition certificate.

---

# Q1. The certificate and source-amplitude interface

## 1. Separate geometry, amplitudes, and decomposition

Your proposed shape is right, with three changes:

* Do not put `χ` into `ProductMonomialChartVar`.
* Do not require `χ = 0` outside the box in the basic local interface.
* Separate the exact identity from the remainder estimate.

For example, schematically—these are interface sketches, not claims about existing argument order:

```lean
def sourceBoxIntegral
    (C : ResolutionChart d) (χ F K : Space d → ℝ)
    (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y in C.dom,
    χ y * |(fderiv ℝ C.φ y).det| *
      F (C.φ y) * p.w (C.φ y) *
      Real.exp (-N * K (C.φ y))
```

Use each box as a **singleton cover**. Its existing weight factor is then `1` on its domain. This avoids mixing three different concepts:

* counting weights;
* tangential factors `r ∘ zeroOn`;
* arbitrary source amplitudes.

A separate structure can package the amplitude:

```lean
structure SourceAmplitude (P : ProductMonomialChartVar ...) where
  χ : Space d → ℝ
  continuousOn : ContinuousOn χ P.W
  nonneg : ∀ y ∈ P.W, 0 ≤ χ y
```

Restricted measurability and boundedness on the compact domain should ordinarily be derived. If a global measurability field makes the implementation materially simpler, including it is harmless, but continuity only on `W` does not imply global measurability of an arbitrary extension.

The decomposition itself should be minimal:

```lean
structure SourceDecomposition
    (ι : Type*) [Fintype ι]
    (Rg : Set (Space d)) (F K : Space d → ℝ) (p : TubeWeight d)
    (C : ι → ResolutionChart d) (χ : ι → Space d → ℝ) where
  rem : ℝ → ℝ
  decomp : ∀ N ≥ 0,
    targetIntegral Rg F K p N =
      (∑ i, sourceBoxIntegral (C i) (χ i) F K p N) + rem N
```

Parameterizing the index type is easier than storing a universe-bearing type and its instances inside the structure.

### Fields versus hypotheses

**Structural fields:**

* exact decomposition;
* local geometry and its `ProductMonomialChartVar` certificates;
* continuity/nonnegativity of a packaged source amplitude.

**Theorem hypotheses, or separate reusable certificates:**

* integrability;
* assumptions on `F`, `p`, and `K`;
* exponential or little-o remainder control;
* nonemptiness of the active family;
* positivity of the assembled leading coefficient.

In particular, make exponential control a separate predicate:

```lean
def HasExponentialBound (r : ℝ → ℝ) : Prop :=
  ∃ C ≥ 0, ∃ κ > 0, ∀ N ≥ 0,
    |r N| ≤ C * Real.exp (-κ * N)
```

A decomposition can then be reused with either exponential control or directly supplied little-o control.

For posterior expectations, the scalar certificate depending on `F` is a good minimal interface. A later, stronger certificate may quantify over an admissible class of observables. Do not make that abstraction a prerequisite for the scalar theorem.

## 2. Generalize the amplitude bridge, not the geometric package

Your diagnosis of where the change belongs is correct: the arbitrary continuous cell amplitude already accommodates multiplication by `χ`.

I recommend new source-weighted definitions and bridge lemmas:

```lean
sourcePieceAmp χ ...
sourceProductCoeff χ ...
exists_varPieceAtlas_of_chart_data_source ...
```

with compatibility lemmas at `χ = 1`.

The geometry remains unchanged:

* `e`, `h`, `u`, `v`;
* product-domain data;
* sector/unit changes;
* extremal ratio and multiplicity.

Only the amplitude and coefficient bookkeeping change.

Do **not** reinterpret the existing `r` as `χ`: its inactive-coordinate factorization is a genuine hypothesis used by the current bridge.

### Essential design point: permit zero coefficients

The foundational source-weighted theorem should be an expansion

\[
I_\chi(N)=c_\chi\,a_{\lambda,k}(N)+o(a_{\lambda,k}(N)),
\qquad
a_{\lambda,k}(N)=N^{-\lambda}(\log N)^k,
\]

with \(c_\chi\ge 0\), including \(c_\chi=0\).

Then derive `HasLeadingTerm`/equivalence when \(c_\chi>0\).

This matters because localization functions vanish on many faces. Requiring every localized chart to have positive coefficient would make ordinary partitions awkward or unusable.

There is also an important assembly rule:

> Select the extremal pair among all relevant geometric active pairs, and require positivity of the coefficient sum at that pair.

You cannot simply discard zero-coefficient charts and select the next positive pair. A zero coefficient gives `o` at the chart’s geometric scale; that error need not be negligible at the next, smaller scale. Continuous amplitudes can vanish at rates that introduce intervening asymptotic behavior.

## 3. Positivity

The weighted coefficient positivity theorem should say:

* the face integrand is nonnegative;
* it is positive on a set of positive **natural face measure**.

“`χ > 0` on part of the face” is sufficient only with the corresponding positivity/nonvanishing of the other face-density factors.

For your centred boxes, a practical corollary is:

> If `χ y₀ > 0`, `F ∘ φ` and `p ∘ φ` are positive near `y₀`, then the existing open-feet argument gives positive coefficient.

This uses continuity of `χ`, followed by the same avoidance of residual/Jacobian hyperplanes as CCLXXI. It does not require `χ` to be positive throughout the box.

## 4. Both remainder theorems

Yes: land both.

* Generic: `HasLeadingTerm.add_isLittleO`.
* Wrapper: exponential bound implies little-o of every admissible power–log scale.

The generic theorem is the durable interface; exponential decay is one geometric producer.

---

# Q2. What resolution actually supplies

## (i) One-chart localization: correct theorem and obstruction

### The missing indicator

Change of variables gives an integral over `dom`. A source partition gives

\[
\int_{\mathrm{dom}} g_N
=
\sum_k \int_{\mathrm{dom}\cap B_k}\chi_k g_N
+
\int_{\mathrm{dom}}\Bigl(1-\sum_k\chi_k\Bigr)g_N.
\]

It does **not** give integrals over the full \(B_k\), unless you know, for example,

\[
\chi_k=0\quad\text{a.e. on }B_k\setminus\mathrm{dom}.
\]

Absorbing `dom.indicator` into `χ_k` generally destroys continuity.

A one-dimensional example already exposes the problem:

* `φ = id`;
* `dom = [0,1]`;
* `K(x)=x²`;
* divisor point `0`.

The centred box at `0` extends to negative numbers. A continuous cutoff equal to `1` near `0` cannot remove the negative half. The whole-domain coefficient is \(\sqrt{\pi}/2\), not the coefficient of the bilateral box.

### Source partitions themselves are honest

For compact \(Z\) covered by interiors of boxes, continuous subordinate functions certainly exist in Euclidean space.

But two qualifications matter:

1. They partition the source integral **with its original domain restriction**.
2. To obtain an exponential remainder, the sum must equal `1` on an **open neighborhood** of \(Z\), not merely on \(Z\).

The second is easy to arrange by compact thickening or plateau bumps. The first is the real obstruction.

### The useful unconditional theorem

Let `a` be a globally continuous nonnegative source amplitude with

```lean
IsCompact (tsupport a)
tsupport a ⊆ interior C.dom
```

and assume the needed monomial, continuity, and nonnegative-phase hypotheses. Set

\[
Z_a=\operatorname{tsupport}(a)\cap\{K\circ\phi=0\}.
\]

Then one can prove:

* finitely many centred product boxes \(B_k\subseteq\operatorname{interior}(\mathrm{dom})\), satisfying the CCLXX neighborhood conditions;
* nonnegative continuous cutoffs \(\theta_k\), compactly supported in `interior B_k`;
* \(\sum_k\theta_k\le1\);
* \(\sum_k\theta_k=1\) on a neighborhood of \(Z_a\);
* amplitudes \(\chi_k=a\theta_k\);
* the exact decomposition
  \[
  \int_{\mathrm{dom}} a\,g_N
  =
  \sum_k\int_{B_k}\chi_k\,g_N+r(N);
  \]
* an exponential bound on \(r\).

Indeed, the support of \(a(1-\sum\theta_k)\) is compact and disjoint from the zero set.

This is an honest source-localization theorem from the existing interfaces.

### What would recover the unweighted whole chart?

You need additional domain information, such as:

* the chart already is a product domain—then use the existing theorem directly;
* a supplied full-box localization/ownership certificate;
* suitable boundary-compatible product pieces;
* or an original source weight whose support stays inside the chart interior.

The sufficient condition `Z ⊆ interior dom` also works, but is very restrictive for compact monomial-chart domains and positive-dimensional divisors. Do not make it the advertised general resolution theorem.

Thus replace proposed unit 4 by a **source-localized explicit coefficient theorem**, not an unconditional whole-chart-image upgrade.

## (ii) Across charts

### (ii-a) Supplied target partition

High value, already substantially implemented.

But `SubordinatePartition` alone still does not solve arbitrary-domain localization. Its coefficient theorem needs:

* the existing product packages; or
* additional source-localization compatibility for each weighted chart term.

Also, measurability and the partition identity do not imply continuity of its pullbacks. Retain that hypothesis explicitly.

### (ii-b) A.e.-disjoint images

Yes, prove it. This is an excellent small theorem.

For measurable images, pairwise null intersections, and suitable integrability:

\[
\int_{\bigcup_i A_i}g
=
\sum_i\int_{A_i}g.
\]

Apply chartwise change of variables and use **singleton packages with weight `1`**.

This avoids proving that the full-cover counting weight satisfies the `ProductMonomialChartVar.weight_eq` field. Pointwise it generally does not, even in examples where it is `1` a.e.

Again, a.e.-disjointness solves overlap, not the compact-domain/product-box issue.

### (ii-c) A compatible resolved manifold

Mathematically correct; poor value for this next programme.

An adequate structure would need substantially more than transition maps:

* an upstairs space with suitable manifold/topological assumptions;
* compatible coordinate representations of a global resolution map;
* local normal-crossing/monomial data;
* compactness or properness sufficient for finite localization;
* an upstairs density/integration construction;
* a precise exceptional-locus and multiplicity-one statement;
* proof of the global integral identity.

Mathlib’s manifold and partition-of-unity infrastructure helps with the topology and local smooth constructions. I would **not** plan around an existing turnkey theorem:

> proper smooth map, diffeomorphism off a null exceptional locus ⇒ global Jacobian change of variables on manifolds.

Even defining the upstairs integral in the required coordinate-independent form can become a separate project.

A useful intermediate abstraction is a **finite compatible-source integration certificate**: supply the global-to-local integral identity, without first formalizing an entire resolved manifold. Your `SourceDecomposition` is precisely the scalar version.

### Ranking

1. **Certified source-amplitude assembly:** broadest immediate payoff.
2. **A.e.-disjoint assembly:** inexpensive, concrete, and regression-friendly.
3. **Target partition reuse:** excellent when suitable partitions are supplied; already largely done.
4. **Global compatible resolution:** separate foundational programme.

### What the paper needs

For the leading expectation asymptotic, the mathematical need is a valid decomposition near the zero locus whose local amplitudes have the required regularity, together with control away from that locus.

A compatible resolution with an upstairs partition is a standard way to obtain it. A.e.-disjoint source/product cells are another sufficient way, not something your `PartialResolution` promises.

Therefore:

> The explicit-coefficient theorem for the original target integral is not obtained from the exposed Hironaka interface alone by this programme.

This is a statement about the insufficiency of the proposed derivation/interfaces, not a claim that analytic geometry cannot prove the theorem by a more substantial additional argument.

## (iii) Intrinsic coefficient

Yes, with one correction to the displayed formula:

\[
c=\sum_{\substack{(i,k)\\\text{pair}_{i,k}=(\lambda_*,k_*)}}c_{i,k}.
\]

Non-tied boxes contribute zero **at the assembled scale**, not their own local leading coefficients.

For two positive leading-term certificates of the **same scalar integral**:

1. pair uniqueness identifies \((\lambda,k)\);
2. uniqueness of the normalized limit identifies \(c\).

If `HasLeadingTerm.pair_unique` only identifies the pair, add the coefficient-uniqueness corollary explicitly.

This gives precisely the desired independence from boxes, cutoffs, and chart indexing. It does not give independence from the target region: an arbitrary small ball and the resolution neighborhood are not the same integral.

---

# Q3. Recommended seven-unit programme

The following order keeps the reusable analytic work ahead of geometry. Each file should have the stated narrow deliverable; in particular, do not hide a global-manifold construction in one unit.

## Unit 1 — `LeadingTermNegligible`

**Main statements**

```lean
HasLeadingTerm.add_isLittleO
HasLeadingTerm.congr_eventually
HasExponentialBound.isLittleO_powerLog
HasLeadingTerm.add_exponential
```

Also the elementary estimate:

\[
\left|\int_S g(x)e^{-NK(x)}\,dx\right|
\le e^{-\kappa N}\int_S|g(x)|\,dx,
\quad N\ge0,
\]

assuming integrability and `K ≥ κ` a.e. on `S`.

**Keep separate:** compactness is one producer of `κ`; it is not needed by the integral estimate.

**Status:** unconditional analysis.

---

## Unit 2 — `SourceAmplitudeLeadingTerm`

**Main statement**

For a singleton product package and continuous nonnegative source amplitude:

```lean
sourceBoxIntegral χ ... =
  sourceProductCoeff χ ... * powerLog ... + o(powerLog ...)
```

together with:

```lean
sourceProductCoeff_nonneg
sourceProductCoeff_one
sourceProductCoeff_pos_of_face
sourceBoxIntegral_isEquivalent_of_coeff_pos
```

Add the centred-box corollary from `χ y₀ > 0`.

**Implementation scope:** lift the existing arbitrary-amplitude cell theorem through a source-weighted piece bridge. Do not copy the entire chart theorem or alter `ProductMonomialChartVar`.

**Status:** honest theorem; zero-coefficient expansion is essential.

---

## Unit 3 — `SourceDecompositionAssembly`

Introduce the exact certificate and prove the finite assembly theorem.

**Main statement**

If:

* each active chart has the source-weighted expansion at its geometric pair;
* inactive terms are negligible;
* the remainder is negligible at the extremal scale;
* the tied coefficient sum is positive;

then

```lean
HasLeadingTerm (targetIntegral Rg F K p)
  extremalLam extremalDeg tiedSourceCoeff
```

and hence equivalence.

Provide the exponential-remainder wrapper.

**Important:** positivity is required at the extremal pair selected before discarding zero coefficients.

**Status:** unconditional theorem consuming a supplied decomposition certificate.

---

## Unit 4 — `CompactSourceLocalization`

This is the corrected geometry unit.

**Main statement**

For `a` continuous, nonnegative, compactly supported in `interior dom`, there exist finitely many CCLXX product boxes and continuous localized amplitudes such that

```lean
sourceIntegral C a F K p N =
  (∑ k, sourceBoxIntegral (boxChart k) (χ k) F K p N) + rem N
```

for `N ≥ 0`, and `HasExponentialBound rem`.

Include:

* compactness of the supported zero locus;
* finite box cover;
* plateau partition with sum `1` near that locus;
* no-leakage support lemma;
* compact phase-gap argument.

A short corollary applies Unit 3 when the extremal tied coefficient is positive.

**Status:** honest theorem under the interior-support hypothesis.

**Not included:** unweighted localization of arbitrary `dom`.

---

## Unit 5 — `AEDisjointSourceAssembly`

**Main statements**

```lean
integral_iUnion_eq_sum_of_pairwise_null_inter
```

and a resolution-specific certificate producer:

* measurable finite images;
* pairwise null intersections;
* chartwise change of variables;
* each chart already a product package, or supplied valid local decompositions.

Conclude an exact or exponentially accurate `SourceDecomposition`.

Also add transfer from a union of chart images to `Rg` when their symmetric difference is null.

**Status:** honest theorem; a.e.-disjointness and any required domain-localization data are supplied.

---

## Unit 6 — `CertifiedResolutionExplicitCoefficient`

This is the user-facing conditional theorem.

**Main statement**

For an analytic nonnegative phase and a resolution neighborhood supplied by Hironaka, **if** a valid finite source decomposition with source-weighted product packages is supplied, and the extremal coefficient sum is positive, then

\[
\int_{Rg}Fp\,e^{-NK}
\sim
c\,N^{-\lambda_*}(\log N)^{k_*},
\]

with explicit tied-face sum `c`.

Include:

* uniqueness of the full leading certificate;
* independence from certified decompositions;
* the ratio/expectation corollary where numerator and denominator have compatible expansions and the denominator coefficient is positive.

For a numerator coefficient that may vanish, use the zero-compatible expansion rather than demanding a positive `HasLeadingTerm`.

**Status:** conditional resolution theorem. Do not advertise it as a consequence of `Q_all` alone.

**Region warning:** it is a small-ball theorem only when the certificate is for that ball. A compact neighborhood returned by `Q_all` is not automatically a ball.

---

## Unit 7 — `BlowupWedgeAssemblyRegression`

Use `Rg = [-1,1]²` and the two maps

\[
\phi_1(s,t)=(s,st),\qquad
\phi_2(s,t)=(st,t),
\]

both on `[-1,1]²`.

Their images are

\[
A_1=\{|b|\le |a|,\ |a|\le1\},\qquad
A_2=\{|a|\le |b|,\ |b|\le1\}.
\]

They cover the square, and their intersection lies on the two diagonals. Hence they are a.e. disjoint.

For \(K(a,b)=a^2+b^2\),

\[
K\circ\phi_1=s^2(1+t^2),\quad |\det D\phi_1|=|s|,
\]
\[
K\circ\phi_2=t^2(1+s^2),\quad |\det D\phi_2|=|t|.
\]

Thus both pairs are `(1, 0)`, and each coefficient is

\[
\int_{-1}^{1}\frac{dt}{1+t^2}=\frac{\pi}{2}.
\]

Conclude

\[
\int_{[-1,1]^2}e^{-N(a^2+b^2)}\,da\,db
\sim \pi N^{-1}.
\]

This is a genuinely useful nonidentity-chart regression.

Two corrections to the proposed description:

* With these clipped parameter squares, the wedge images overlap only on a null boundary—not on an open wedge.
* Do not use the full-cover counting weight pointwise. At the exceptional origin and shared boundaries it differs from `1`. Use Unit 5 and singleton packages.

This regression does not need Unit 4’s interior-support hypothesis: its chart domains already are valid product domains.

### Scope relative to the paper

The under-served point worth absorbing is the **zero-compatible numerator expansion and expectation quotient**. It is directly relevant to expectation asymptotics and uses the new amplitude flexibility.

Keep subleading terms out of scope. No new global-manifold formalization is needed for these seven units.

---

# Q4. Mathlib dependencies and cautions

I cannot verify the current checkout here. The names below distinguish reliable starting points from identifiers to grep before committing statements.

## 1. Compact source partitions

Start with:

* `Mathlib.Topology.PartitionOfUnity`;
* `PartitionOfUnity`;
* `BumpCovering`;
* `BumpCovering.toPartitionOfUnity`;
* `exists_isSubordinate` / `IsSubordinate`;
* your candidate `exists_continuous_sum_one_of_isOpen_isCompact`.

**Grep these:** I would not promise their exact namespace, signature, or availability in your Mathlib revision.

Also inspect the Urysohn-lemma API, including the identifier family around:

```lean
exists_continuous_zero_one_of_isClosed
```

Be precise about support:

> For localization and the compact phase-gap proof, prefer  
> `tsupport χ ⊆ O`, often with compact `tsupport χ`,  
> rather than merely `Function.support χ ⊆ O`.

### Lower-risk Euclidean implementation

For Unit 4, I would consider avoiding the general partition API entirely.

Choose finitely many continuous plateau bumps \(b_k\) such that:

* \(0\le b_k\le1\);
* each has compact support inside a box interior;
* their `=1` neighborhoods cover the compact supported zero locus.

Set

\[
B=\sum_k b_k,\qquad
\theta_k=\frac{b_k}{\max(1,B)}.
\]

Then:

* the denominator is everywhere positive;
* \(0\le\sum_k\theta_k\le1\);
* the sum is `1` on an open neighborhood of the supported zero locus;
* support subordination is preserved.

In Euclidean space, elementary distance-based plateau bumps plus

```lean
IsCompact.elim_finite_subcover
```

may be more predictable than adapting a locally finite partition construction. This is also a clean way to guarantee the neighborhood version, not just equality on the compact set.

## 2. Change of variables off the exceptional set

Your proposed strategy is correct, but it has **two null-set steps**, not one.

Let \(D'=\mathrm{dom}\setminus E\).

1. Apply change of variables on `D'`, where injectivity holds.
2. Remove `E` from the source integral using `volume E = 0`.
3. Remove `φ '' E` from the target integral using **`volume (φ '' E) = 0`**.

The last assertion does not follow from source nullity for an arbitrary continuous map. Here it follows from the `C¹` hypothesis: the map is locally Lipschitz near the compact domain, and locally Lipschitz maps between equal-dimensional Euclidean spaces preserve null sets.

Use the existing chartwise COV theorem whenever possible; this argument should already be encapsulated there.

Relevant starting points:

```lean
integral_image_eq_integral_abs_det_fderiv_smul
```

and the API families for:

* `ContDiffOn` ⇒ differentiability on an open neighborhood;
* differentiability ⇒ `HasFDerivWithinAt` after restriction;
* local Lipschitz regularity of `C¹` maps;
* null images under Lipschitz maps;
* set-integral congruence under a.e.-equal domain indicators.

Grep the Lipschitz null-image names rather than assuming an exact identifier.

Also do not justify image measurability by “continuous image of a measurable set.” That implication is not generally valid as stated. Use the hypotheses of the existing COV theorem, compact-image facts, or the completed-measure/a.e. comparison with the compact image.

The nonvanishing Jacobian is part of your chart interface, but the injective COV theorem may not itself require it once its other hypotheses are established.

## 3. Compact phase gap

The standard route is indeed:

```lean
IsCompact.exists_isMinOn
```

with continuity and nonemptiness.

For a compact support set `S`, assume:

* `ContinuousOn (K ∘ φ) S`;
* `0 ≤ K (φ y)` on `S`;
* `K (φ y) ≠ 0` on `S`.

A minimizer gives `κ > 0` and the lower bound.

Handle `S = ∅` separately; the remainder is then zero.

The important geometric input is not “positive distance from the divisor” by itself. It is:

> the remainder amplitude has compact support disjoint from the phase-zero set.

That is exactly what the neighborhood partition supplies.

---

## Recommended commitment

Land Units 1–3 first. They provide a complete, honest theorem:

> **A certified finite source decomposition has an explicit positive leading coefficient.**

Then land the interior-supported localization theorem and a.e.-disjoint producer. Finish with the conditional resolution corollary and the blow-up-square regression.

Do **not** claim either of these yet:

* arbitrary compact monomial chart ⇒ explicit whole-image coefficient by centred-box localization;
* `Q_all` alone ⇒ the required regular source decomposition.

Keeping those gaps explicit is what makes this programme a real extension of #84 rather than a restatement of the same overlap obstruction upstairs.
