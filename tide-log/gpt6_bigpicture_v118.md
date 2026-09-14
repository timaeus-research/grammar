## Executive verdict

**The smooth engine appears complete as a conditional asymptotic theorem. It is not yet the paper’s analytic–semianalytic existence theorem.** The principal remaining issues are geometric: producing the atlas, rectifying its domain, and normalising its phase units. They are not deficiencies of the smooth-amplitude Taylor engine.

I would **close U1–U6c after the pending regressions and scope documentation**. Do not reopen it to construct a jet field or accommodate arbitrary units inside the exponential.

This is an audit of the supplied declarations and mathematical interfaces, not a repository-level verification of `1f35998`.

## 1. Audit of the landed statements

### 1.1 `hu_tan` is a genuine input restriction

The usual normal-crossing form
\[
K\circ\phi(y)=u(y)\prod_i y_i^{2k_i}
\]
does **not** imply that \(u\) is independent of the active coordinates.

There is a standard **local** way to remove a positive unit. At a point where an active coordinate \(y_j\) vanishes, set
\[
x_j=y_j u(y)^{1/(2k_j)},\qquad x_i=y_i\quad(i\ne j).
\]
Then the phase becomes exactly \(\prod_i x_i^{2k_i}\). At \(y_j=0\), the determinant of this coordinate change is \(u^{1/(2k_j)}>0\), so the inverse function theorem gives a local diffeomorphism.

But this is not a free refinement in the current interface:

* On a whole supplied box, the coordinate change need not be injective.
* Its image need not be a box.
* The chart, Jacobian unit, weights, selected domains, and transport proof all change.
* Away from the zero locus, one should normally use the exponentially small tail rather than force this construction.
* Refining to local normalised boxes requires another cover/partition argument.

Thus:

> `hu_tan` is restrictive for a supplied atlas, although positive units can ordinarily be eliminated locally in a suitably rebuilt resolution atlas.

That distinction belongs in the documentation.

**There is no cheap amplitude workaround.** Writing
\[
F_N(y)=F(y)e^{-N(u(y)-\beta)y^{2k}}
\]
makes the amplitude depend on \(N\). Its derivatives introduce powers of \(N\), and the fixed-amplitude or compact-parameter derivative bounds used by the engine no longer apply. Expanding that exponential can be made into another asymptotic method, but it requires new remainder estimates and coefficient bookkeeping.

**Recommendation:** normalise units geometrically in a future atlas constructor; do not modify the completed facewise engine.

### 1.2 The a.e. presentation fields are appropriate

Let
\[
m=\nu\otimes(\mathrm{vol}|_{\mathrm{box}}),\qquad
w(z)=\operatorname{ofReal}(y^h\rho(z)).
\]
The essential observation is
\[
m.\mathrm{withDensity}(w)\ll m.
\]
Consequently, the a.e. phase and amplitude identities transfer to the weighted source measure and can be used with the map identity.

The obligations worth checking in the actual transport proof are:

1. `mono h` is nonnegative on the active box.
2. The density is measurable.
3. On the a.e. set where `ρ ≥ 0`, conversion through `toNNReal`/`ENNReal` recovers the real density `mono h * ρ`.
4. Integrability is transported from the target, or otherwise established, before using Bochner integral identities.
5. For the asymptotic argument, \(N\ge0\) eventually; then phase nonnegativity gives the usual domination by the integrable observable.

There is no inherent null-set mismatch in the declarations. In fact, requiring the identities a.e. for the **unweighted** source measure is stronger than merely requiring them a.e. for the weighted source.

### 1.3 `commonQ` is valid but deliberately coarse

For each chart \(I\),
\[
Q_I=2\prod_i k_{I,i}>0.
\]
Since \(Q_I\mid\prod_I Q_I\), its lattice embeds in the common lattice. Thus your `commonQ` proves exactly the advertised rational-lattice conclusion.

An `lcm` would reduce the denominator but add little mathematical value.

The following refinement is valid and relatively cheap, assuming the chart coefficient support lemmas are available:

```lean
theorem coeff_support_chartwise
    (hc : A.coeff μ q ≠ 0) :
    ∃ I,
      (∃ m : ℕ, μ = (m : ℝ) / Qamb (A.chart I).k) ∧
      q ≤ dim I - 1
```

A nonzero finite sum has a nonzero summand. This gives the union-of-chart-lattices statement, and even retains each chart’s degree bound.

However, **that union is presentation-dependent**. It is a useful upper bound on intrinsic support, not itself an intrinsic spectrum. I would not make this a new milestone.

### 1.4 Different lattices do not threaten uniqueness

Passing both expansions to the product lattice and the maximum degree bound is sound. A nonzero difference has a least exponent, and at that exponent a largest nonzero logarithmic degree. Such a leading power–log term cannot satisfy the required little-o estimate.

The important interface distinction is:

* `SmoothExpansionCertificate`, with positive denominator and coefficient support, supports equality at **every** `(μ,q)`.
* Bare `HasSmoothCoordFreeExpansion` does not constrain coefficients outside the spectrum that its sums inspect.
* Consequently, a bare `CutoffExpansion` uniqueness theorem must either restrict its conclusion to the indexed spectrum or require support of the competing coefficient function.

Your certificate addresses this correctly. Check that the abbreviated description of `smoothCoeff_unique` does not promise off-spectrum uniqueness without such a hypothesis.

### 1.5 Two explicit checks, and one missing case

**Check the logarithm convention.** Your rescaling formula has `(-log β)^(j-q)`. This is correct for scales
\[
N^{-\mu}(-\log N)^q,
\]
or equivalently \(N^{-\mu}(\log(1/N))^q\). For scales \(N^{-\mu}(\log N)^q\), the sign must instead be positive. The definition of `q.scale` was not supplied, so this is a convention check, not an allegation of an error.

**Do not confuse active dimension zero with zero phase.** When `d = 0`,
\[
\operatorname{mono}(\cdots)=1,
\]
so the core phase is \(\beta(s)>0\), and the contribution is exponentially small. Saturating `d - 1` to zero is harmless: the coefficients should all vanish.

**A phase identically zero on a positive-measure component is not represented by these positive-unit monomial cores.** Its contribution is constant in \(N\), with coefficient
\[
c_{0,0}=\int \mathrm{obs}\,d\mu.
\]
If the paper’s hypotheses do not exclude this situation, it requires a separate zero-phase summand or a preliminary case split. In particular, the pending `d = 0` regression does not automatically cover it.

## 2. Distance to the paper’s theorem

Here is the remaining chain of implications, with relative Lean costs.

| Gap | Required result | Cost |
|---|---|---|
| Resolution and domain rectification | Analytic/semianalytic hypotheses produce finitely many suitable resolved chart domains, including the inequalities defining \(W\) | Very large unless already exported by `hironaka` |
| Exact weighted transport | A finite smooth partition on the resolved space, chartwise change of variables, and null-set removal produce the measure identity | Large |
| Unit normalisation | Local coordinate absorption, refined boxes, transformed Jacobian units, and compatible transport | Medium–large |
| Neighbourhood chart smoothness | Replace global chart-data smoothness by smoothness near the relevant closed boxes | Small–medium, once the geometry is fixed |
| Zero-phase components | Split off a constant contribution, or state the nondegeneracy hypothesis excluding them | Small |
| Final theorem packaging | Construct the inputs from paper hypotheses and invoke the certificate | Small once everything above exists |

### 2.1 The missing constructor is not merely a partition on chart images

The clean construction generally takes place **on the resolution space**, not on the images of singular charts in \(W\).

Suppose \(\pi:\widetilde W\to W\) is the resolution map and \(\theta_i\) is a smooth partition subordinate to resolved coordinate charts \(\psi_i\). Set
\[
\phi_i=\pi\circ\psi_i,\qquad \omega_i=\theta_i\circ\psi_i.
\]
Away from an exceptional/null set, the resolution is a change of variables, and
\[
\sum_i(\phi_i)_*
  \bigl(\omega_i|\det D\phi_i|\,dy\bigr)
=\mathrm{vol}|_W
\]
follows from the partition identity and chartwise change of variables.

A partition subordinate to **chart images in \(W\)** is not a general substitute:

* those images need not be open chart neighbourhoods;
* \(\phi_i^{-1}\) may not exist globally;
* singular images need not support the required smooth inverse-based constructions;
* multiplicities must be accounted for if the map is not one-to-one a.e.

Under appropriate a.e. injectivity hypotheses, your suggested “weights pulled back from a partition summing to one plus change of variables” argument is correct. Those hypotheses are precisely part of what the constructor must prove.

A useful future intermediate theorem would be schematically:

```lean
theorem weighted_transport_of_chartwise_changeOfVariables
    (hpartition : /* weights sum to one on resolved space a.e. */)
    (hchart_cov : /* chartwise integral or measure identities */)
    (hresolution_cov : /* resolution transports Jacobian volume to volume on W */) :
    /* exact finite-sum weighted pushforward identity */
```

Separate this measure-theoretic theorem from the analytic resolution existence theorem.

### 2.2 Boundary and exceptional sets are manageable, but not automatic

For full-dimensional semianalytic pieces, frontier contributions can be discarded after proving the relevant nullity theorem. Lower-dimensional pieces have zero ambient volume. Likewise, the exceptional locus and its image require appropriate null-set results.

But merely resolving \(K\) does not necessarily turn the pullback of \(W\) into your selected orthants. **The defining inequalities of \(W\) must also be rectified**, or treated by an equivalent domain-resolution result.

That is a substantive geometric assumption hidden by saying only “local chart form”.

### 2.3 Global smoothness is mostly an interface issue

If the chart data are smooth on a neighbourhood of a compact closed box, cutoffs and extension can usually produce global representatives agreeing on a neighbourhood of the working box. This also preserves derivative identities there.

Do not extend every field independently and assume the structure still works:

* the extended Jacobian data must remain compatible with the extended chart on the working region;
* phase identities must remain valid there;
* global `hu_tan` needs a tangentially constructed extension, not an arbitrary extension of the unit.

Compared with transport and unit normalisation, this is a convenience wrapper, not the principal blocker.

### 2.4 What I would do next—if the unconditional theorem becomes a new project

Start with the **resolution-space-to-weighted-transport bridge**, with explicit domain-rectification and normalised-phase hypotheses. It will expose whether the existing `hironaka` outputs actually supply the required geometry.

Then implement unit normalisation within that construction. Do not invest first in broader global-to-neighbourhood wrappers: they will not bridge the main gap.

## 3. The coefficient functional

The scalar linear functional is the right final form for this programme.

Linearity and presentation independence are already substantial. They do **not** yet establish:

* continuity in a test-function topology;
* support on \(K^{-1}(0)\);
* finite order;
* dependence on a specified jet bundle;
* an intrinsic decomposition among individual strata.

Also, coefficients need not depend on a finite jet at a single point. They can involve integrals along positive-dimensional faces or strata.

If pursued later, a precise and sensible first target would be the following. Fix the geometry and prior, and let `coeffOf f μ q` denote the intrinsic coefficient for observable `f`. Define
```lean
def zeroSet := {x | x ∈ W ∧ K x = 0}
```
Then prove:

```lean
theorem coeff_eq_of_equal_finiteJets (μ : ℝ) (q : ℕ) :
    ∃ R : ℕ,
      ∀ f g,
        ContDiff ℝ ∞ f →
        ContDiff ℝ ∞ g →
        /* required integrability hypotheses */ →
        (∀ x ∈ zeroSet, ∀ r ≤ R,
          iteratedFDeriv ℝ r f x =
          iteratedFDeriv ℝ r g x) →
        coeffOf f μ q = coeffOf g μ q
```

The quantifier order matters: `R` must be independent of `f` and `g`. This is dependence on **ambient jets along the whole zero set**, not merely tangential derivatives along strata.

A stronger distributional formulation would add an estimate by a finite \(C^R\) seminorm. That would establish continuity and finite order, and would be a better foundation for a genuine “jet functional” than linearity alone.

**Recommendation:** record this target, but do not implement it now. It is not needed to justify the scalar expansion claim.

## 4. Suggested paper-mirror paragraph

> The Lean development proves a smooth-amplitude power–log expansion conditional on a finite weighted normal-crossing presentation with exact measure transport. In the implemented atlas producer, charts use symmetric boxes and selected orthants, the chart data are smooth, and positive phase units are independent of the active normal-crossing coordinates; the prior and observable may instead be smooth on a neighbourhood of the closed integration domain. The resulting expansion has a little-o remainder at every real cutoff order, rational exponents in a common lattice, and a uniform finite logarithmic-degree bound. Its scalar coefficients are uniquely determined by the integral, independent of the admissible presentation, linear in the observable, and compatible with the analytic coefficients when both constructions apply. No stratum-adapted independence condition is imposed on the weights or other amplitude factors, as witnessed by a smooth overlap regression whose weight genuinely varies in an active coordinate. Construction of the required smooth weighted atlas from the analytic–semianalytic hypotheses of the paper, including domain rectification and normalisation of general phase units, is not formalised by this result. The development also does not assert an intrinsic jet field or finite-order jet dependence of the coefficients.

Once the pending regressions land, add them to the regression sentence with their exact tested scope.

## 5. Stopping decision

**Close the smooth programme now.**

Before closure:

1. Finish the two pending regressions.
2. Check and document the logarithm convention.
3. State explicitly that active dimension zero means positive phase, not zero phase.
4. Record the zero-phase-component case alongside atlas existence, domain rectification, and unit normalisation.
5. Label the headline result **conditional on `SmoothSheetInputs`**, not “the analytic–semianalytic theorem”.

I would not require another numbered analytic unit. The union-support refinement and a constant-function certificate are inexpensive conveniences, but neither changes the main scope of the result.

The next substantial project should have a separate name and acceptance criterion: **constructing a smooth weighted normalised atlas from resolution data**. Keeping that boundary explicit is more valuable than extending an already finished amplitude engine.
