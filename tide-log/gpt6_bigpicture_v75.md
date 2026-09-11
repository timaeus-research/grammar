## Recommendation

**Take (D′), but as a conditional adapted-density theorem, not as a theorem about the present measurable cover weights.** Separate three tasks:

1. a prescribed-product-domain, uniform Mellin theorem;
2. an exact adapted decomposition of each chart–stratum density;
3. the already-landed finite-sum assembly.

The second task is a genuine geometric hypothesis unless an adapted-partition construction is proved. Neither `PartialResolution` nor CCXXIII currently supplies it.

There are also two corrections to the diagnosis:

- Bounded measurable weights need not have a leading-term limit at all.
- The leading coefficient generally sees a **critical face**, not just the trace on the full stratum \(S_I\). Noncritical normal variables remain integrated in the coefficient.

These distinctions should appear explicitly in the next interface.

---

# 1. What is—and is not—available

## 1.1 Option (A) is essentially already done

Given your addendum, yes: if CCVIII applies to the same compact resolved set and that set agrees a.e. with the union of chart images, transporting its Θ statement across that a.e. equality adds no substantive asymptotics.

A useful short corollary could identify the exact CCXXIV integral with the CCVIII integral. But this is an API consolidation, not a new theorem of the paper.

There is an amplitude qualification: positivity of \(F\) alone is insufficient when `p : TubeWeight d` is arbitrary. A bounded measurable prior can vanish near the relevant zeros, or introduce irregular concentration. Reuse exactly CCVIII’s positivity and regularity hypotheses on the effective amplitude; do not replace them by merely `F > 0`.

Likewise, an existential CCV region cannot automatically be put inside an arbitrary prescribed piece. Compactness of `dom` does not give it interior near a divisor point.

## 1.2 Bounded measurable weights can destroy the limit

The obstruction is stronger than “the coefficient is noncanonical.”

For a one-dimensional model, take
\[
K(x)=x^2,\qquad \phi(x)=x,\qquad F=p=1.
\]
Choose radii \(r_j\downarrow0\) with \(r_{j+1}/r_j\to0\), and the compact set
\[
E=\{0\}\cup\bigcup_m
\{x:r_{2m+1}\le |x|\le r_{2m}\}.
\]
Then
\[
N^{1/2}\int_E e^{-Nx^2}\,dx
\]
has subsequences tending to \(\sqrt{\pi}\) and to \(0\): choose the Gaussian scale well inside alternating occupied and empty annuli.

This example has an analytic phase and amplitude and an arbitrary compact integration domain of precisely the problematic kind.

It also illustrates the cover-weight issue without changing the global integral. Add a second identity chart covering a full interval. The normalized indicator weight of the shell chart is \(1/2\) on its image, so its contribution still oscillates. The full-interval chart compensates, and the sum has the usual Gaussian leading term.

Thus:

> A global exact leading term does not imply exact leading terms for an arbitrary measurable chart decomposition.

Monotone approximation does not fix this. An approximation error small in ordinary \(L^1\) need not be small after division by \(N^{-\lambda}\log^kN\). One needs approximation in the asymptotic concentration norm, or a suitable trace theorem.

## 1.3 Disjoint images do not solve the domain problem

Per-chart injectivity does not imply cross-chart disjointness.

Measurable disjointification is available set-theoretically, but generally replaces one irregular indicator by another. Even a single chart with an arbitrary compact domain can exhibit the preceding failure.

The supplied `IsMonomialChart` fields say only
```lean
IsOpen W
dom ⊆ W
```
together with analyticity and monomial identities. They contain no box or polydisc property for `dom`. I would not infer such a property from the displayed interface, regardless of how a particular resolution construction chooses intermediate charts.

Shrinking preserves monomiality. It does **not** prove that:

- the original arbitrary compact domain has an exact finite product tiling;
- overlap multiplicities become normal-fibre constant;
- the resulting pieces still give the original integral.

An adapted cover may be constructed on a suitable resolved manifold with additional geometric work. It is not a consequence of “shrink each chart.”

## 1.4 The fibre formula does not regularize the measure

CCXXIII and CCXXIV provide an exact identity. Moving
\[
1_{\mathrm{dom}}\,\rho\,e^{-NK}\,p\,|\det D\phi|
\]
into `fibreMeasure` does not remove its normal-direction irregularity.

In the one-dimensional counterexample, the tangential base is a point. There is therefore no tangential uniformity issue to fix: the zeroth normal moment itself has no normalized limit.

So unrestricted (D) fails for the same reason as (B).

---

# 2. Assessing the adapted-fibre diagnosis

The diagnosis is substantially right, with three qualifications.

### First: impose the hypothesis on all nonsmooth amplitude factors

Even if `1_dom * (ρ ∘ φ)` is fibre-constant, arbitrary `p : TubeWeight d` can recreate the counterexample.

A clean theorem should require either:

- \(p\circ\phi\) to belong to the regular normal-amplitude class; or
- the whole nonsmooth factor, including \(p\circ\phi\), to have an adapted factorization.

For example, on an orthant product cell,
\[
1_{\mathrm{piece}}1_{\mathrm{dom}}(\rho\circ\phi)(p\circ\phi)
=
1_B(z)1_Q(n)\,\beta(z)\,a(z,n)
\quad\text{a.e.},
\]
where \(\beta\) is measurable and \(a\) has the normal regularity required by the Mellin theorem.

Fibre constancy is the special case \(a=1\).

### Second: fibre constancy is sufficient, not necessary

Continuous or suitably trace-regular normal weights can also have exact coefficients. A coefficient, when the normalized limit exists, is canonical **for that integral**. It need not be invariant under changing the chart allocation.

The real distinction is not “canonical versus noncanonical coefficient”; it is:

- existence of a suitable asymptotic trace;
- dependence on the chosen allocation;
- invariance of the total after summation.

### Third: the relevant face may be larger than \(S_I\)

On a positive orthant, write a normal model as
\[
K(z,n)=u(z,n)\prod_{j\in I}n_j^{e_j},\qquad
d\mu=A(z,n)\prod_{j\in I}n_j^{h_j}\,dz\,dn,
\]
with \(u>0\). Put
\[
\lambda=\min_{j\in I}\frac{h_j+1}{e_j},\qquad
J=\left\{j\in I:\frac{h_j+1}{e_j}=\lambda\right\},
\qquad k=|J|-1.
\]

The leading coefficient normally restricts the regular factors to \(n_J=0\), then integrates the remaining normal variables \(n_{I\setminus J}\). It is not generally obtained by evaluating every normal variable at zero.

For instance, for \(K(x,y)=x^2y^4\) and Lebesgue density, the critical variable is \(y\). The leading coefficient involves an integral of
\[
A(x,0)|x|^{-1/2},
\]
not merely \(A(0,0)\).

This matters for the claimed face functional and for moment tensors.

---

# 3. Ranking the routes

| Route | Assessment |
|---|---|
| **(D′): adapted product densities + uniform prescribed-domain Mellin theorem + exact assembly** | First choice for exact conditional progress; closest to the adapted-fibre mechanism in the paper. |
| **(A): reuse CCVIII/CCIX** | Already available, modulo integral-identification glue and matching amplitude hypotheses. |
| **Trace-regular extension of (B)/(D)** | Mathematically valuable later; needs a genuine asymptotic trace/approximation theorem. Bounded measurability is insufficient. |
| **(C): disjoint images** | Not implied by the displayed resolution API and not sufficient without domain/amplitude regularity. |
| **Unrestricted (B)/(D)** | False as a universal certificate theorem. |

For “a few units,” distinguish two claims:

- The **conditional integration and assembly interface** is a few units.
- A **verified prescribed-box uniform Mellin theorem with an explicit face coefficient** is the substantive analytic work. I would not promise that the named population Mellin declarations already contain it without checking their domain, parameter, and domination hypotheses.

And even after that, this proves the leading-order part of `thm:expectation_expansion`, not its full expansion.

---

# 4. Proposed module contracts

The following names are proposed declarations, not claims about existing Mathlib APIs.

## Module 1 — `AdaptedPieceDensity.lean`

### Purpose

Represent exactly what replaces the irregular density on a prescribed piece.

Separate the static density from \(e^{-NK}\). The certificate should not depend on \(N\).

A schematic local structure is:

```lean
structure AdaptedProductDensity ... where
  base : Set Tangent
  measurableSet_base : MeasurableSet base
  normalBox : Set Normal
  beta : Tangent → ℝ
  beta_measurable : Measurable beta
  amplitude : Tangent → Normal → ℝ
  -- regularity and integrability fields supplied separately
  density_ae :
    originalStaticDensity ∘ split
      =ᵐ[volume]
    fun zn =>
      base.indicator
        (fun z => normalBox.indicator
          (fun n => beta z * amplitude z n) zn.2) zn.1
```

In actual Lean, use a less cumbersome product-indicator expression and make the restricted measures explicit.

For the first geometric specialization:

```lean
adaptedProductDensity_of_fibreConstant
```

assume, on the ambient size piece, an a.e. equality
\[
1_{\mathrm{dom}}(\rho\circ\phi)=\beta\circ\operatorname{planeFoot}.
\]
Then require the pulled-back prior to be regular, or incorporate it in the adapted static factor.

Important features:

- A.e. equality is enough; pointwise values assigned on a measure-zero face are not a legitimate trace.
- `base` may be an arbitrary measurable subset of a compact controlled tangential neighborhood. It need not have analytic boundary.
- Do not require the signed observable \(F\) to be nonnegative.
- Keep the geometric allocation factor nonnegative when coefficient positivity will later be needed.

Reuse:

- `planeSplit`, `stratumSplit`, and the size-piece geometry;
- measure-preserving/Jacobian-one splitting already landed;
- the exact `pieceIntegral` definition.

A useful endpoint is:

```lean
pieceIntegral_eq_integral_adaptedProduct
```

for \(N\ge0\), proved from the a.e. static-density identity and integrability.

---

## Module 2 — `UniformProductMellinLeading.lean`

### Purpose

Prove asymptotics on a **prescribed** product box, not an existential CCV region.

A good first analytic theorem uses a compact parameter set \(T\), a fixed positive orthant box
\[
Q=\prod_{j<r}(0,b_j),\qquad b_j>0,
\]
and
\[
L_N(z)=\int_Q
A(z,n)\prod_jn_j^{h_j}
\exp\!\left(-Nu(z,n)\prod_jn_j^{e_j}\right)\,dn.
\]

Require:

- \(r>0\), \(e_j>0\);
- regularity on a neighborhood of \(T\times\overline Q\) sufficient for the existing Mellin argument;
- \(u\ge u_{\min}>0\) there;
- appropriate uniform bounds for \(A,u\) and the derivatives actually used.

A first version may assume joint analyticity. Later, weaken tangential regularity: there is no need to demand analyticity of \(\beta(z)\).

Proposed output:

```lean
uniformProductMellin_hasLeadingKernel
```

providing:

1. a coefficient function `faceCoeff z`;
2. pointwise, or uniform, convergence
   \[
   L_N(z)/\operatorname{powLogScale}(\lambda,k,N)
   \longrightarrow \operatorname{faceCoeff}(z);
   \]
3. an eventual normalized absolute bound, uniform on \(T\).

The third item is essential for integration.

### Explicit coefficient target

For the displayed positive-orthant normalization, the expected coefficient is
\[
\frac{\Gamma(\lambda)}
{k!\prod_{j\in J}e_j}
\int_{\prod_{\ell\notin J}(0,b_\ell)}
 A(z,0_J,t)\,u(z,0_J,t)^{-\lambda}
 \prod_{\ell\notin J}t_\ell^{h_\ell-\lambda e_\ell}\,dt.
\]
Here all exponents in the remaining product are \(>-1\). Orthants are then summed with their actual amplitudes and positive phase units.

This formula should be matched against the library’s Mellin normalization before becoming a definition. In particular, distinguish actual phase exponents \(e_j\) from notation \(e_j=2k_j\).

Reuse or refactor:

- `MellinMoment`;
- `CoeffFamily`;
- `dataBoxCoeff_population_leading_b`;
- the analytic-unit upgrades.

**Do not use `local_leading_term` as if it supplied this theorem.** Its existential region and positive scalar amplitude conclusion omit the prescribed-domain and parameter-uniform content needed here.

A practical proof strategy is to extract the local box calculation beneath CCV, rather than strengthen CCV’s public existential statement by wishful application.

---

## Module 3 — `IntegratedMellinLeading.lean`

### Purpose

Turn fibrewise asymptotics into a base-integrated certificate.

First prove a generic dominated-convergence theorem:

```lean
hasLeadingTerm_integral_of_dominated_kernel
```

with hypotheses of the form:

- \(L_N(z)/s(N)\to\ell(z)\) a.e. on \(B\);
- eventual measurability and integrability;
- for all sufficiently large \(N\),
  \[
  |L_N(z)/s(N)|\le G(z)
  \quad\text{a.e.};
  \]
- `IntegrableOn (fun z => |beta z| * G z) B`.

Conclusion:
\[
\operatorname{HasLeadingTerm}
\left(N\mapsto\int_B\beta(z)L_N(z)\,dz\right)
\left(\int_B\beta(z)\ell(z)\,dz\right)\lambda k.
\]

Be precise about the quantifier order on the bound: an eventual range of \(N\) with an a.e. bound for each such \(N\) is the useful integration hypothesis.

Then specialize Module 2:

```lean
hasLeadingTerm_adaptedProductIntegral
```

This is the promised exact result with a merely measurable tangential weight.

This module is relatively routine. Module 2 is where the nontrivial asymptotics live.

---

## Module 4 — `FiniteAdaptedPieceAtlas.lean`

### Purpose

Encode the finite localization needed for a whole chart–stratum piece.

The atlas should contain finitely many product cells, each with:

- a controlled monomial model;
- an adapted static density;
- a local exponent pair;
- an exact density identity, or an explicitly negligible remainder.

The key field must be an **a.e. weighted identity**, not just a covering assertion:
\[
1_{\mathrm{piece}}\cdot\text{static density}
=
\sum_a \text{transported cell density}_a
\quad\text{a.e.}
\]

A finite cover alone double-counts overlaps. Positive-measure overlaps must be handled by exact tiling or allocation.

Proposed declarations:

```lean
structure FiniteAdaptedPieceAtlas ...
pieceIntegral_eq_sum_atlasIntegrals
faceCoeff_sum_of_exact_base_decomposition
```

### Role of CXCIV

Yes: use `AnalyticCoreDecomposition` and its exact-tiling infrastructure **where its actual hypotheses establish this identity and keep each tile inside a controlled normal model**.

Do not assume that an arbitrary compact `dom` meets those hypotheses. Exact tiling does not manufacture normal traces for irregular restrictions.

Similarly, `gCoeff` and `first_nonzero` can organize coefficient additivity and subsequent cancellation analysis only after the relevant expansion/representation hypotheses have been supplied.

### A necessary collar warning

Shrinking a normal box is not automatically harmless.

If a removed normal coordinate is noncritical, its outer collar can contribute at exactly the same leading scale. A finite localization must either:

- retain the full noncritical-normal face integral; or
- decompose the collars into additional cells and include their coefficients.

Only a region bounded away from **every** phase divisor is automatically exponentially negligible.

Thus a tangential cover by CCV-sized neighborhoods is useful, but it does not by itself identify an integral over the original normal box.

---

## Module 5 — `AdaptedPieceLeadingTerm.lean`

### Purpose

Produce the missing nonempty-piece certificates.

```lean
hasLeadingTerm_pieceIntegral_of_adaptedAtlas
```

takes a `FiniteAdaptedPieceAtlas` and the Module 2 hypotheses on each cell, then:

1. obtains local certificates using Module 3;
2. uses exact additivity from Module 4;
3. applies `hasLeadingTerm_sum_of_extremal`.

There are two reasonable outputs:

- an extremal pair computed from the active cells;
- a certificate at a nominated chart–stratum pair, after proving every cell pair is dominated by it.

The second allows coefficient zero. It is often the better assembly API.

For the usual piece pair, use
\[
\lambda_{i,I}=\min_{j\in I}\frac{h_{i,j}+1}{e_{i,j}},
\qquad
k_{i,I}=\#\operatorname{argmin}-1,
\]
provided the atlas establishes the relevant monomial model. Cells in which some coordinates are bounded away from zero may have faster pairs.

For signed \(F\), all these statements remain valid with signed coefficients. Do not conclude positivity or equivalence to a nonzero leading term.

---

## Module 6 — `ResolvedAdaptedLeadingTerm.lean`

### Purpose

Finish the global conditional theorem with minimal new analysis.

```lean
hasLeadingTerm_boltzmannIntegral_of_adaptedAtlases
```

should invoke:

- Module 5 for every nonempty \((i,I)\);
- CCXXVI’s `hasLeadingTerm_boltzmannIntegral_of_monomial`;
- the existing extremal-pair ordering.

The coefficient is exactly the sum of tied piece coefficients already specified by CCXXV.

Add separate corollaries:

```lean
boltzmannIntegral_isEquivalent_of_adaptedAtlases_of_coeff_ne_zero
resolvedLeadingCoeff_pos_of_positive_extremal_cell
resolvedLeadingPair_eq_identifiedPair
```

The last one needs a nonvanishing argument or matching Θ information. A zero-coefficient `HasLeadingTerm` does not identify the first nonzero exponent.

For positivity, require nonnegative contributions and positive **face-measure** contribution on at least one extremal cell. Positivity at one point, with no positive-measure support condition, is insufficient for an arbitrary measurable base.

---

# 5. The role of \(\varepsilon\)

Treat \(\varepsilon>0\) as fixed before taking \(N\to\infty\).

The adapted-atlas hypotheses must certify that this particular \(\varepsilon\) is compatible with:

- chart neighborhoods;
- unit lower bounds;
- normal boxes or their exact refinements;
- the Mellin uniformity estimates.

There is no automatic certificate for every positive \(\varepsilon\).

If finite localization produces several admissible normal radii, taking their minimum is permissible only after accounting for the removed collars.

Individual piece coefficients can depend on \(\varepsilon\). Once the global identity and certificates hold at a common scale, the **total** coefficient is independent of admissible choices of \(\varepsilon\), by uniqueness of the normalized limit. This is a useful later corollary:

```lean
resolvedLeadingCoeff_eq_of_two_adapted_decompositions
```

It also proves independence from different valid adapted allocations, without claiming invariance of individual allocations.

---

# 6. What upgrades the current results to exact coefficients?

A sufficient conditional package is:

1. exact finite adapted product-density decompositions;
2. regular normal amplitudes, including the prior;
3. positive nonvanishing phase units on controlled product neighborhoods;
4. the uniform prescribed-box Mellin theorem;
5. integrable domination over the tangential bases.

This yields an **exact normalized limit**, not merely Θ or a coefficient inequality.

Neither of the following alone suffices:

- a.e.-disjoint chart images;
- analytic or smooth chart weights with an unchanged arbitrary domain indicator.

An analytic partition of unity also deserves careful phrasing. In the real-analytic category, ordinary subordinate compactly supported partitions are generally unavailable. Prefer:

> Assume an exact adapted allocation whose tangential weights are measurable or smooth and whose normal dependence belongs to the permitted regular class.

If the paper’s adapted-partition lemma gives normal-fibre constancy, formalize that precise property and the geometric setting in which it is constructed. Do not silently identify it with the normalized indicator cover.

The resulting conditional theorem is axiom-clean: the unresolved geometry is an explicit hypothesis. It should be named and documented as conditional, rather than packaged as if `PartialResolution` constructed the required atlas.

---

# 7. What programme should follow?

My ranking is:

### 1. Moment-tensor asymptotics

This most directly advances `thm:expectation_expansion`. Module 2 should be designed to handle monomial insertions:
\[
n^\alpha \prod_j n_j^{h_j}.
\]
On an orthant this shifts \(h_j\) to \(h_j+\alpha_j\), changes the critical set when appropriate, and exposes the Mellin scaling needed for `M_{I,r}(n)`.

For full tensors, also track orthant signs, symmetry cancellations, uniform bounds, and summation remainders. Exact contraction identities alone do not justify exchanging an infinite normal series with a normalized asymptotic limit.

### 2. Coordinate-free leading coefficient and face functional

The local explicit face formula belongs in the present programme. Its global coordinate-free identification should follow closely.

First prove invariance through equality of integrals and uniqueness of leading limits. Then identify that invariant with the paper’s geometric face functional. This is safer than proving chart-transition invariance directly before the analytic coefficient is under control.

### 3. Statistical transfer to §4

This has high paper-level value but is a separate frontier: empirical perturbations, probabilistic uniformity, random normalizers, and interchange of stochastic and asymptotic operations need their own hypotheses.

Population identification of \((\lambda,m)\) does not by itself transfer that pair to empirical/posterior objects.

---

## Bottom line

Do not attempt to discharge the existing nonempty-piece certificates for arbitrary compact domains and normalized measurable cover weights: **they are not universally true**.

The next honest milestone is:

> **A prescribed-product, uniform Mellin theorem for adapted static densities; an exact finite adapted-atlas interface; and the global conditional leading coefficient obtained through CCXXVI.**

CXCIV is the right assembly tool when its exact-tiling hypotheses apply. It is not a substitute for the missing adapted geometry, and CCV’s existential region is not a certificate for a prescribed chart–stratum piece.
