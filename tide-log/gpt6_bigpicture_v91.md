## 1. The honest target needs two corrections

Daniel is right: a leading measure is not an identification of arbitrary Taylor-tree coefficients. But there is also a problem with the proposed stronger target:

> **In general, higher coefficients are distributions supported on the zero set, but they need not be finite-measure strata integrals of only conormal derivatives. Tangential finite-part distributions can occur at intersections of strata.**

This obstruction already occurs for an exact monomial phase, with no unit and no geometric ambiguity.

There are therefore three distinct deliverables:

1. **Available now, conditionally on analytic core certificates:** a full expansion whose coefficients are explicit chart-base integrals of Taylor-tree functionals.
2. **A substantive but chart-local extension:** prove that those functionals extend to finite-order distributions, explicitly represented using normal derivatives and **tangential finite-part distributions**.
3. **Not supplied by the current geometry:** an intrinsic resolved-space formulation, with compatible normal bundles, densities, moment sections, and coordinate-independent strata.

Moreover, the unqualified finite-measure/conormal-only formulation in the question is generally too strong, not merely missing a Lean interface.

### A second correction: the cutoff remainder

The supplied definition proves
\[
O\!\left(N^{-L}(1+\log N)^D\right),
\]
not \(O(N^{-L})\) for every strict cutoff \(\mu<L\). If a nonzero \(N^{-L}\log N\) term exists, the latter assertion is false.

Use one of these formulations:

* the existing `CutoffExpansion`;
* \(O(N^{-L})\) for cutoffs \(L\) outside the candidate spectrum;
* include the terms at exponent \(L\), then obtain \(O(N^{-L})\) by applying the expansion at a slightly larger cutoff.

This should be settled in the theorem statement, not hidden in prose.

---

## 2. Why finite measures paired only with conormal derivatives are insufficient

Consider the completely certified model
\[
Z_N(f)=\int_0^1\!\int_0^1 e^{-Nx^2y^2}f(x,y)\,dx\,dy.
\]
Write \(a=\sqrt\pi/2\). Its leading logarithmic coefficient is
\[
C_{1/2,1}(f)=\frac a2 f(0,0).
\]
The log-free coefficient at the same exponent contains
\[
a\int_0^1\frac{f(x,0)-f(0,0)}x\,dx
+
a\int_0^1\frac{f(0,y)-f(0,0)}y\,dy,
\]
as well as a constant multiple of \(f(0,0)\).

These are finite-part distributions along the axes. They are not integration against finite signed measures there.

There is a useful stronger diagnostic. Suppose a representation used finite measures on the two axes and the origin, paired with conormal derivatives of order at most \(r\). Test it on the polynomials
\[
f_m(x,y)=\bigl(1-(1-x)^m\bigr)^{r+1}.
\]
They satisfy:

* \(0\le f_m\le1\) on the square;
* all \(y\)-derivatives vanish;
* all \(x\)-derivatives through order \(r\) vanish at \(x=0\);
* but
  \[
  \int_0^1 f_m(x,0)\,\frac{dx}{x}\longrightarrow\infty.
  \]

Thus the proposed finite-measure/conormal-only pairing would remain bounded, while the coefficient does not. These tests are polynomials, so restricting to analytic observables does not remove the obstruction.

Integration by parts can rewrite the displayed finite part using an integrable logarithmic weight paired with a **tangential derivative**. That yields a finite-measure derivative representation, but not the claimed conormal-only representation.

Consequently:

> `tanCoeff` is already a strata integral in a legitimate chart-coordinate sense. It is not yet—and cannot generally become—a finite sum of finite-measure integrals of bounded-order conormal jets without regularization or additional tangential derivatives.

Its dependence on infinitely many corner Taylor coefficients is consistent with this: those coefficients reconstruct a function along a face, on which a finite-part functional acts.

---

## 3. The strongest theorem directly accessible from the present expansion interface

I would first prove a theorem named, schematically,

```lean
certifiedCore_analyticCoefficientExpansion
```

Its hypotheses must be stronger than “a.e.-disjoint monomial chart images.”

### Geometric and analytic hypotheses

Fix the original weight \(\varphi\), independently of the observable \(F\). Supply:

1. A certified change-of-variables cover identifying the original integral with the chart/core integral.
2. A finite exact core decomposition and a tail with positive phase gap.
3. Exact core normal forms accepted by the population Taylor tree.
4. Fixed amplitude data, including the transported Jacobian and weight.
5. An admissible class \(\mathcal A\) of observables for which
   \[
   \eta_{a,F}(z,u)=A_a(z,u)\,F(\psi_a(z,u))
   \]
   has the required normal holomorphic extension and integrable, uniform-in-base majorants.
6. Tail integrability for each observable.

Here “analytic near the zero set” is the intended source of admissibility, **not a replacement for item 5**. One needs the radius and domination certificates on the actual boxes. Outside the zero-set neighbourhood, weighted integrability suffices if the contribution has a uniform phase gap.

The interface also does not make analyticity of all unit/Jacobian factors automatic: `IsMonomialChart` records the units as continuous. Their stronger regularity must be obtained by separate division lemmas or supplied.

### Conclusion

There are fixed \(Q>0,D\), a candidate spectrum \(\Lambda\subseteq Q^{-1}\mathbb N\), and linear functionals
\[
C_{\mu,j}:\mathcal A\to\mathbb R
\]
such that, for every admissible \(F\),
\[
\operatorname{CutoffExpansion}(Q,D,Z_F,C(F)),
\]
with
\[
C_{\mu,j}(F)
 =
 \sum_a \int_{B_a}
   \operatorname{dataBoxCoeff}_{a,\mu,j}
       \bigl[c_u(A_a(z,u)F(\psi_a(z,u)))\bigr]
 \,d\nu_a(z).
\]

The formula must use the **physical-\(N\)** coefficient convention already incorporated in `tanCoeff`: box rescaling mixes logarithmic degrees and introduces powers of \(b\). Raw `familySpectralCoeff` cannot simply be substituted without those conversion factors.

Also prove:

* vanishing off \(\Lambda\) and above the declared logarithmic degree;
* continuity on the admitted weighted Taylor-data space;
* independence of certificates, on their common admissible observable class;
* zero-set germ locality on that class.

This is a genuine full-expansion theorem identifying **every coefficient**. But, at this stage, call its coefficients **analytic coefficient functionals**, not distributions.

### What is not a consequence

Continuity on weighted \(\ell^1\) Taylor data does **not** imply
\[
|C_{\mu,j}(F)|
 \le A\max_{|\alpha|\le r}\sup_H|\partial^\alpha F|,
\tag{*}
\]
for some compact \(H\) and finite \(r\).

Estimate (*)—or an explicit finite-order distributional construction—is the missing analytic bridge. Nor does the fibre contraction identity supply it: that identity has no coefficientwise asymptotic estimates and no justification for exchanging its infinite contraction sum with asymptotic coefficient extraction.

---

## 4. The corrected distribution theorem

The appropriate next target is:

> Under the same exact-core and admissibility certificates, construct compactly supported finite-order distributions \(T_{\mu,j}\) on the original Euclidean space, supported in the zero set, whose action on admissible analytic observables equals the explicit `gCoeff`. The original analytic-observable integral has the corresponding full cutoff expansion.

This does **not** assert a smooth-observable expansion merely because its coefficient distributions exist. Extending the remainder theorem to \(C^\infty\) observables requires a separate finite-smoothness remainder argument.

### Honest chart-level representation

Use a finite chart-indexed sum
\[
T_{\mu,j}(F)
 =
 \sum_a\sum_{I,\alpha}
 \int_{B_a}
 \mathcal R_{a,I,\alpha,\mu,j,z}
 \left[
   \left.\partial_{u_I}^{\alpha}
      (A_a\,F\circ\psi_a)\right|_{u_I=0}
 \right]d\nu_a(z).
\tag{1}
\]

Here:

* \(I\ne\varnothing\) identifies a zero face;
* \(\alpha\) has bounded order;
* \(\mathcal R\) acts in the remaining face coordinates;
* \(\mathcal R\) is an ordinary integral when integrable, and otherwise an explicitly Taylor-subtracted finite-part functional.

Leibniz expansion separates derivatives of \(A_a\) from those of \(F\circ\psi_a\). Thus the dependence on the observable is explicit.

A good Lean representation is:

* a finite index of chart-face terms;
* face parameter spaces and maps to \(W\);
* bounded-order derivative evaluation maps;
* continuous linear finite-part functionals on face test functions;
* integrable base dependence;
* the resulting continuous linear functional on ambient smooth tests.

If using Mathlib’s distribution/test-function API is inconvenient, a local finite-order functional structure with linearity and bounds (*) is sufficient initially. Do not call a bare map on analytic functions a distribution.

### Where the finite-part construction comes from

For a deterministic exact monomial box, the relevant one-dimensional factors are
\[
\mathcal A_i(s)[f]
 =\int_0^b t^{h_i-2k_i s}f(t)\,dt.
\]
Taylor subtraction continues these factors across their poles. At
\[
\mu=\frac{h_i+m+1}{2k_i},
\]
the residue is a multiple of \(f^{(m)}(0)\); the regular Laurent coefficients are Taylor-subtracted integrals, with logarithmic weights.

Tensor products of these Laurent expansions give:

* normal derivatives on coordinates contributing residues;
* finite-part functionals on the remaining coordinates;
* finite-order bounds;
* support on a union of zero faces.

Comparing these explicit Laurent coefficient formulas with the population Taylor-tree coefficients is the essential new theorem. One can implement the Taylor-subtracted algebra directly; a general meromorphic-distribution theory is unnecessary.

An explicit order bound should be extracted from the subtraction depths. A safe theorem can initially state a computable `coeffOrder h k μ`; it need not claim an optimal order.

### Why not push everything down to measures on \(W\)?

Because \(D_\perp^r(F\circ\pi)\) is not a field on \(W\). Two points in different chart-faces may map to the same \(w\), with different normal directions and different derivative evaluation maps.

Keep the derivative pairing upstairs in the **disjoint union of chart-face parameter spaces**, then push the resulting functional down:
\[
T(F)=\widetilde T(F\circ\psi).
\]

A finite-order ambient derivative-of-measures representation is another possibility, after establishing finite-order continuity. It is noncanonical and is not a conormal moment-tensor representation.

---

## 5. Handling the analytic unit

### Recommended route: local exact removal, with an explicit assembly certificate

Use the existing `exists_localNormalForm` near a point of a divisor. On the relevant hyperplane, the rescaling fixes the point, and its derivative is invertible.

For a compact subset of that hyperplane, compactness gives a finite collection of such local normal forms. It does **not** automatically give:

* one globally injective rescaling on a whole original chart;
* a product-box image;
* an exact analytic core decomposition;
* analytic localization weights.

The coordinate rescaling leaves the other coordinates unchanged. Locally, tangential coordinates on the chosen face therefore need not change. Under its inverse \(S\), the density becomes
\[
A(S(z))\,|\det DS(z)|,
\]
with the monomial Jacobian factor refactored as appropriate. Any subsequent tangential reparameterization also changes the base measure by its change-of-variables rule.

Even a uniform collar diffeomorphism would not by itself make the image of the original core a rectangular box. Domain transport is a real part of the certificate.

The particular danger is subdivision: smooth partitions of unity exist, but generally destroy analyticity; analytic partitions subordinate to arbitrary local covers are unavailable.

Thus the near-term route is:

> **Local unit removal plus supplied exact analytic core transport**, not “compactness globalizes unit removal.”

A later smooth-amplitude monomial theorem would make smooth localization available and substantially simplify this assembly problem.

### Dressed trees are a separate possible development

A variable unit can also be handled by regularized Mellin factors involving \(u^{-s}\), or by a new dressed phase calculus. This may avoid the domain distortion of exact removal. It still requires uniform estimates and coefficient identification; naive expansion of the exponential perturbation is not justified throughout the integration region.

### The existing `cξ` slot does not handle it

The slot represents
\[
-\beta N u^{2k}+\beta\sqrt N\,u^k\xi(u).
\]
A unit perturbation contributes
\[
-N(U(u)-\beta)u^{2k}.
\]
Encoding that in `ξ` would require
\[
\xi_N(u)=-\frac{\sqrt N}{\beta}(U(u)-\beta)u^k,
\]
which depends on \(N\). That is outside the fixed-data theorem and its bounds.

**Do not feed the unit into this phase slot.**

---

## 6. Canonicity and cancellations

There are three different uniqueness claims.

### Coefficient values

For a fixed observable, normalize both expansions onto a common lattice, pad logarithmic degrees by zero, and use first-nonzero uniqueness. This identifies the total coefficients.

It does not identify individual chart or stratum contributions. Those may cancel.

### Functionals on the analytic test class

Applying that argument to every common admissible observable identifies the total coefficient functionals on that class.

Calling this “canonical” is correct, provided the class is specified. If two certificates admit different observables, the immediate assertion is equality on their intersection.

### Distributions

Once finite-order distributional extensions exist, equality on a sufficiently determining analytic class identifies them as distributions.

For compactly supported distributions, all ambient polynomials are a determining class. Thus admitting polynomials, proving coefficient agreement on them, and constructing compactly supported finite-order extensions is one clean route to distributional canonicity. Alternatively use analytic approximation with the required finite-order estimates.

Continuity merely in the weighted analytic norm is not enough.

Even when the resulting distribution is canonical:

* its chart-face decomposition is not;
* its derivative-of-measures representation is not;
* its finite-part subtraction conventions are not individually canonical;
* its conormal splitting is not canonical.

Only their assembled action is forced by uniqueness.

---

## 7. Ordered unit plan

These are **scope budgets**, not a claim that the missing analytic work is already a collection of wrappers. In particular, units 5–7 are research gates. If their coefficient comparison does not close, stop at unit 4 rather than adding a certificate that simply assumes the desired conclusion.

| Unit | Statement and tools | Budget / gate |
|---|---|---|
| **1. `PopulationSpectralCoeffLinear`** | For `cξ = 0`, prove amplitude linearity of the physical-box coefficient, then of `tanCoeff` and `gCoeff`. Use the population coefficient series, Cauchy-product linearity, absolute summability, and integral linearity. Package fixed-coefficient continuous linear maps on the existing data spaces. | 200–300 lines. **First unit.** Gate: linearity must concern the observable with fixed weight and phase. |
| **2. `CutoffCoefficientUnique`** | Prove uniqueness after lattice refinement and degree padding; derive coefficient equality from an exponentially small difference. Use first-nonzero/flatness and exponential-versus-power-log estimates. | 200–300. Require positive lattice denominators and explicit off-lattice zero conventions. |
| **3. `AnalyticObservableCoreData`** | Define an admissible observable subspace and its linear map into `JointData`: \(F\mapsto c(A\,F\circ\psi)\). Record the exact majorants needed by existing integration and remainder theorems. | 250–350. Gate: weighted analyticity, not just analyticity of \(F\). |
| **4. `CertifiedCoreAnalyticExpansion`** | Assemble the theorem in §3, using `cutoffExpansion_of_hasAnalyticCoreDecomposition`. Prove chart-sum coefficient formula, continuity, common-class canonicity, and germ locality when the difference has phase-separated support. | 250–350. **First complete deliverable.** No distribution claim yet. |
| **5. `EulerFinitePartFunctional`** | Define one-dimensional Taylor-subtracted integrals with log weights. Prove finite-order seminorm bounds, subtraction-depth compatibility, and evaluation on monomials/power series. Use Taylor remainder estimates, integrability of \(t^a|\log t|^q\), and dominated interchange. | 300–400. Gate: actual \(C^r\) bounds, independent of analytic radius. |
| **6. `MonomialFaceCoefficientFunctional`** | Tensorize unit 5 and form the finite Laurent-coefficient algebra at each candidate exponent. Prove a finite-order bound and zero-face support. Record a computable derivative-order bound. | 300–400. Gate: include regular Laurent factors—residues alone miss the finite parts. |
| **7. `PopulationCoeff_eq_faceFinitePart`** | Identify unit 6 with the physical population Taylor-tree coefficient, first on monomials and then on admissible Taylor series. Track the \(b,\beta,\log b\) conversion explicitly. | 300–400. **Central identification gate.** Restrict initially to deterministic population phase. |
| **8. `IntegratedChartCoefficientDistribution`** | Multiply by the fixed amplitude, pull back ambient tests, integrate over the base, and sum charts. Prove finite-order bounds using compact-chart derivative bounds and integrable base majorants; prove support in the image of zero faces. | 300–400. Gate: uniform/integrable distribution seminorm constants must be supplied or derived. |
| **9. `CertifiedCoreDistributionExpansion`** | Combine units 4, 7, 8. Analytic observables have the full expansion with coefficients given by canonical compactly supported distributions and formula (1). Prove representation independence using a determining test class. | 200–300. Does **not** claim a smooth-test remainder theorem. |
| **10. `LocalNormalFormCoreTransport`** | Prove change-of-variables compatibility for a supplied local-normal-form core transport, including the transformed amplitude and coefficient equality by uniqueness. | 250–350. Leaves finite exact analytic tiling as a certificate; does not manufacture it from `PartialResolution`. |

Unit 10 can be moved earlier operationally. It is placed last to emphasize that the coefficient-distribution analysis can and should first be completed on exact monomial cores.

### Hypotheses remaining at the end

Even after all ten units:

* a.e.-disjointness, or a correct multiplicity/localization replacement;
* exact core measure transport and suitable product geometry;
* tail phase gap;
* exact unit removal compatible with those cores, or a separately proved dressed-unit theorem;
* analytic-observable Taylor-radius and domination conditions;
* uniform integrable bounds needed for base-integrated distributions.

None follows merely from the listed `PartialResolution` interface.

---

## 8. What remains genuinely intrinsic

The current interface has no common resolved space or transition maps. It therefore cannot identify chart-indexed normal data as sections of a globally defined \(\operatorname{Sym}^r NS_I\), nor glue their densities and normal splittings.

Even with a common resolved space, higher normal Taylor coefficients require the appropriate splitting/tubular data or an invariant jet formulation. Fibrewise normal Taylor machinery should not silently be promoted to canonical bundle-valued derivatives.

The honest substitute is formula (1), on chart-face parameter spaces, together with canonicity of its total pushed-forward distribution.

Finally, the exact contraction series and the finite-cutoff spectral expansion must remain distinct: actual fibre moments need not themselves be finite power–log sums. Their **asymptotic truncations** may be.

**Recommendation:** finish unit 4 immediately, then make unit 7 the next flagship theorem. That moves from “the leading coefficient is a measure” to “every population coefficient has an explicit finite-order, zero-supported distributional formula.” Do not promise the narrower finite-measure/conormal-only formula: normal-crossing finite parts already show why that is not the general theorem.
