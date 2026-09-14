## Executive answer

**Proceed with Q1-α, but treat normal constancy as an explicit atlas hypothesis—not as a consequence of SNC or of Watanabe’s chart clause.** Prove it first for a genuinely overlapping single-blow-up atlas. That is a useful extension of the present producer without changing its analytic engine or §4.

There are two important corrections to the proposed alternatives:

1. **Own-chart normal constancy does not generally survive normalisation.** Indeed, for prescribed incompatible chart projections, a subordinate partition with that property need not exist. Compatible controlled tubes solve a related *smooth* problem, but do not automatically give constancy in the analytic coordinates used by your producer.
2. **A smooth amplitude is not determined, even to a fixed asymptotic order, by finitely many jets at the deepest corner.** For a product phase, boundary faces contribute at leading order. A smooth replacement must retain functions along those faces, their transverse jets, and suitable remainder estimates. It is not simply “truncate the existing infinite normal-order sum.”

A general smooth resolution proof remains available mathematically. Its Lean cost is a new normal-asymptotics engine, with an additional analytic-data interface if you want to preserve §4.

---

# 1. Q1: precisely what can be constructed?

## 1.1 Own-chart admissibility is the correct certificate requirement

You are right about the assembly interface. It does **not** require overlapping pieces to use the same normal foliation.

For each piece \(i\), it is enough that its weighted amplitude be admissible in **its own** core presentations, and that the weighted pushforwards sum to the target measure. Schematically,
\[
\mu=\sum_i(\Phi_i)_*(\chi_i\,\mu_i)+\mu_{\rm tail}.
\]

Thus a common system of normal projections is a **sufficient construction device**, not a logical requirement of the assembled certificate.

But the following two assertions are very different:

* Each \(\chi_i\) is pulled back through its own projection.
* Such \(\chi_i\) can be chosen subordinate to the cover and summing to one.

The second is a substantive compatibility problem.

## 1.2 Normalisation genuinely fails

Let \(p_i\) be the coordinate projection of chart \(i\), and start with
\[
a_i=f_i\circ p_i.
\]
Then
\[
\chi_i=\frac{a_i}{\sum_j a_j}
\]
is constant along \(p_i\)-fibres only if the denominator has the requisite constancy there, wherever \(a_i\ne0\). There is no general reason for this.

This is not merely a defect of that particular construction.

**Local obstruction.** Take a collar of a smooth divisor, with coordinates \((s,t)\), divisor \(t=0\), and two chart projections
\[
p_1(s,t)=s,\qquad p_2(s,t)=s+t.
\]
On a two-chart overlap, own-chart constancy and partition unity require
\[
f(s)+g(s+t)=1.
\]
Differentiation in \(t\) forces \(g'=0\), and then \(f'=0\), on the relevant overlap. Such weights cannot perform a nonconstant transition across it.

This gives a global counterexample by taking a circular divisor covered by two overlapping arcs, each having an exclusive region. Subordination forces a transition from weight \(1\) to weight \(0\), while the displayed equation forbids it. Both charts can retain the phase \(t^2\). If desired, replace \(s+t\) by \(s+t^2\); the same obstruction holds for \(t>0\), even with reflection symmetry in the normal variable.

**Conclusion:** a normally constant partition subordinate to an arbitrary prescribed analytic SNC atlas is false in general.

## 1.3 What controlled tubes do—and do not—provide

There are standard smooth controlled-tube constructions for appropriate stratified spaces, and compatible collar constructions for manifolds with corners. With suitably adapted covers, these support partitions pulled back through compatible projections.

That gives a clean **smooth geometric sufficient condition**:

> Supply compatible collar projections, an adapted cover, and partitions on the strata compatible with those projections; extend inductively through the collars.

For SNC geometry, working on the real oriented blow-up and using its corner structure is a natural framework.

However:

* “Controlled” identities between projections must be the identities actually needed by the partition construction.
* Being constant along a controlled projection does **not** imply being constant along a prescribed analytic chart’s coordinate fibres.
* Straightening smooth collars by smooth coordinate changes can destroy the normal analyticity of the density and observable, even when the divisor remains coordinate-shaped.

So a controlled-tube theorem alone is **not** an adapter into your current holomorphic-packet producer. You also need compatibility with its analytic core coordinates, or a separate argument that the resulting weighted amplitudes satisfy its analytic requirements.

## 1.4 Watanabe’s clause supplies no such compatibility

The local monomial/even chart statement identifies divisor components locally with coordinate hyperplanes. It does not canonically identify normal coordinates or normal projections.

An overlap may preserve the divisor and the monomial phase while changing a tangential coordinate by
\[
s'=s+u,\quad\text{or}\quad s'=s+u^2.
\]
Consequently, normal constancy in one chart need not transfer to another.

Thus:

* Properness helps obtain finite covers over compact sets.
* The chart clause supplies local monomialisation and local analytic units.
* Neither supplies a normally constant partition for the resulting prescribed charts.

This does **not** prove that no better choice of charts could work. It does rule out claiming that the desired partition follows immediately from Watanabe’s triple.

## 1.5 Single blow-ups versus composites

### Single blow-up: a concrete construction

For a blow-up with dominant-coordinate charts, the exceptional-direction map is common to the charts. On chart \(\beta\),
\[
z_\beta=t,\qquad z_\gamma=t\,y_\gamma.
\]
Functions of projective direction are independent of \(t\) in every chart. A smooth partition on projective direction space subordinate to enlarged dominant-coordinate charts therefore gives the required tangential weights.

One explicit construction uses
\[
a_\beta([z])
 =\prod_{\gamma\ne\beta}
   \eta\!\left(\frac{z_\gamma^2}{z_\beta^2}\right),
\]
extended by zero where \(z_\beta=0\), with \(\eta\) equal to \(1\) on \([0,1]\) and zero before the boundary of the enlarged chart. Then set
\[
\chi_\beta=\frac{a_\beta}{\sum_\gamma a_\gamma}.
\]
A maximal-coordinate index has \(a_\beta=1\), so the denominator is positive. The extension is smooth because the numerator vanishes in a neighbourhood of the chart boundary.

Here normalisation is safe because every numerator factors through the **same direction map**.

If strict-transform coordinate hyperplanes also belong to the phase divisor, verify more: the weights must be constant near their normal zero sets too. Plateau cutoffs can provide this locally—small direction coordinates cease to affect all surviving factors—but this is an additional stratum-adaptation lemma, not automatic from radial independence.

### Coordinate-centre composites: plausible, but not automatic

A later blow-up can turn a previously tangential coordinate into a normal coordinate. A weight acceptable before that blow-up can then become normal-dependent after pullback.

Accordingly, “dominant-coordinate walls are tangential” is not by itself an induction proof.

A feasible theorem should specify:

* admissible centres relative to the existing divisor;
* the particular chart refinement;
* which old weights remain constant in the new normal directions;
* how plateau regions are chosen at new crossings;
* the resulting dependence statement for every actual core.

This is a promising **restricted construction programme**, especially for explicitly combinatorial coordinate-centre atlases. It is not presently justified for arbitrary composites merely by their SNC output.

### Status summary

| Claim | Status |
|---|---|
| Weighted assembly from admissible per-core weights | Direct extension of your existing results |
| Normally constant partition for an arbitrary prescribed SNC analytic atlas | False in general |
| Smooth controlled partitions for suitably adapted geometric data | Standard smooth-geometric route |
| Those partitions are admissible in the existing analytic coordinates | Additional compatibility required |
| Single dominant-coordinate blow-up construction | Concrete and provable |
| General coordinate-centre composite construction in the required interface | Separate theorem to develop |
| General consequence of Watanabe’s triple alone | Not supplied by the stated hypotheses |

The remaining existence questions should be called **unproved programme obligations**, not automatically “open problems in mathematics.”

---

# 2. What Q1-α should actually require

Do not encode only “constant near the divisor.” Encode what the producer consumes.

A `StratumAdaptedPartition` should provide, at minimum:

1. Nonnegative measurable weights, with support/subordination data.
2. A finite partition identity on the relevant resolved domain.
3. For **each produced core**, a continuous base weight \(w_{i,c}\) and
   \[
   \chi_i(\Phi_{i,c}(s,v))=w_{i,c}(s)
   \quad\text{a.e. on its entire core box}.
   \]
4. A certified gap for whatever is excluded from those core boxes.
5. The integrability/transport hypotheses needed by weighted measure assembly.

Smoothness of the weights is not necessary for the present engine; continuity of the base weights is the operative assumption.

The “entire core box” qualification matters. A collar identity becomes sufficient only after shrinking/repartitioning cores and proving that the discarded region really has a phase gap. Merely being outside a neighbourhood of one divisor component does not establish a gap: another component may still have zero phase.

With compactness and a neighbourhood of the **whole zero set**, a positive gap on the complement is the familiar compactness argument.

---

# 3. Q2: what a smooth engine really needs

## 3.1 Correct the finite-jet claim

Consider
\[
I(n)=\int_0^1\!\int_0^1
       f(x)e^{-n x^2y^2}\,dy\,dx,
\]
where \(f\) is smooth and supported in \([a,b]\subset(0,1)\). Every jet of this amplitude at \((0,0)\) vanishes, but
\[
I(n)=\frac{\sqrt\pi}{2\sqrt n}
       \int_a^b\frac{f(x)}x\,dx
       +O(e^{-c n}).
\]

Therefore even the leading coefficient is not determined by finitely many—or all—jets at the deepest corner.

What is true is:

> At a fixed order, smooth monomial asymptotics can be obtained from finite transverse jets along the relevant faces, retaining their tangential dependence, together with controlled remainders.

At intersections, a face-subtraction/Mellin construction also needs compatible subtraction terms; lower-log coefficients can involve finite-part expressions. A multivariate estimate \(R_N=O(\lVert v\rVert^N)\) at the origin is not enough: \(\lVert v\rVert\) can stay bounded away from zero while the product phase tends to zero.

Water-filling collars may organise the required estimates, but the asserted “large \(N\) implies beyond \(n^{-A}\)” still needs a proof with:

* the correct facewise remainder;
* control as tangential variables approach other faces;
* integrable uniform bounds.

This is precisely where the existing infinite analytic series can encode information that a finite corner jet cannot.

## 3.2 The scalar all-orders theorem survives

For compactly localised smooth amplitudes and exact monomial phases, standard Mellin/Taylor-subtraction methods recover all-orders power-log expansions. Analyticity of the amplitude is not necessary for that conclusion.

A suitable smooth certificate can recover:

* the scalar coordinate-free asymptotic expansion;
* candidate exponents and logarithmic powers from the monomial data;
* leading asymptotics;
* RLCT/multiplicity readout under the usual positivity/nonvanishing assumptions.

Two qualifications:

**Log degree.** “Codimension minus one” is generally a bound or a maximal-resonance statement, not an unconditional equality. The pole order is controlled by the number of simultaneously resonant normal factors. Coefficients may vanish; signed observables may cancel leading terms. The existing boundary regression remains a regression, not a universal equality theorem.

**Canonicity.** Uniqueness of the asymptotic scale identifies the **total scalar coefficient** \(c_{\alpha,j}\) across certificates and across truncation orders. It does not by itself make every allocation of that coefficient to individual strata canonical. Partitions and finite-part conventions can redistribute contributions.

Thus `expansionCoefficient_eq_of_certificates` has a clear smooth analogue if its conclusion is equality of the total expansion coefficients. A stronger stratumwise statement needs its own invariance theorem.

## 3.3 “One certificate for all orders” is not lost logically

You can package a smooth certificate as one object containing
\[
\forall A,\quad \text{finite-order data and remainder estimates}.
\]
Alternatively, start with one smooth amplitude and derive these certificates at every order.

Consistency of scalar coefficients follows from asymptotic uniqueness. There is no mathematical need to choose unrelated coefficients separately at every order.

What you lose is the **present compact analytic witness** and its existing proof path: one \(C(K,\ell^1)\) datum, exact series evaluation, absolutely summable convolutions, and the particular infinite normal-order pairing.

The J-min jet functional also requires care. Its scalar coefficient functional can survive as a linear functional of the observable, but generally not as a finite jet at the deepest stratum. For analytic observables it may admit a rebuilt analytic representation; for smooth observables, flat-at-the-corner functions can still contribute through adjacent faces.

---

# 4. §4 and weight-in-measure

## 4.1 Moving the weight does preserve analytic input data

Yes: if only \(\chi\) is smooth, one can keep the prior/observable analytic series as the datum and regard \(\chi\) as part of the reference measure.

But this requires a changed core interface. Under the current fields, it is not a harmless definitional rewrite: `chartMeasure`, `transport`, `amplitude_eq`, and the per-core expansion theorem jointly encode the old split.

The new moments are
\[
M_{\gamma,\chi}(n,s)
 =\int_{(0,b]^d}
   \chi(s,v)v^{\gamma+h}
   e^{-n\beta\prod_i v_i^{2k_i}}\,dv.
\]
The monomial phase remains exact, but these are no longer the existing unweighted monomial moments. Arbitrary \(\chi\) destroys the reduction to the current scalar Mellin/Gamma calculations.

Boundedness of \(\chi\) may still justify exchanging an absolutely convergent analytic series with the **original integral**. It does not automatically justify exchanging it with the **asymptotic expansion**, uniformly in coefficient index and base point.

You need new weighted-moment estimates or a smooth-amplitude theorem, including bounds on the resulting coefficient operators.

## 4.2 §4 survives as infrastructure, not automatically as an application

The abstract \(\ell^1\)-valued Gaussian-limit theorems and the analytic observable/prior data do not become false because localisation is smooth. They remain available.

What must be rebuilt is the map from that random datum to the asymptotic coefficients:

* Are the new coefficient operators continuous in the topology used by the CLT?
* Are the required smooth-weighted remainder estimates uniform on the relevant random/tight sets?
* Do the insertion identities commute with those operators?

Finite normal differentiation is not bounded on bare coefficient \(\ell^1\) without appropriate weighting or a radius margin. Your \(b'>b\) analytic packets are therefore valuable: Cauchy estimates can supply precisely the stronger bounds needed. But those bounds must be proved.

The algebraic identities behind log insertions remain meaningful, and Mellin differentiation is still available. The existing ladder implementation tied to the current coefficient map does not transfer merely by moving \(\chi\) into the measure.

## 4.3 The proposed tangential-plus-tail split is exactly Q1 again

A decomposition
\[
\chi(s,v)=\chi^{\rm tan}(s)+r(s,v),
\qquad \operatorname{supp}r\subset\{K\ge\delta\},
\]
would indeed solve the issue with the current engine.

The additive form is preferable to dividing by \(\chi^{\rm tan}\), which may vanish.

But an arbitrary smooth partition does not admit this decomposition. It says exactly that \(\chi\) is base-only wherever the phase is small—the substantive Q1 requirement.

---

# 5. Honest loss statements

**D1 — smooth all-orders certificate.** The deterministic scalar all-orders expansion survives, including its unique total coefficients and leading invariants under appropriate nonvanishing hypotheses. The replacement must use facewise transverse jets and remainder control, not merely finite deepest-corner jets. You lose the current exact analytic datum and its infinite-series coefficient proof. Existing analytic stratum-pairing formulas and §4 applications require new adapters; individual stratum allocations are not automatically canonical.

**D2 — smooth weight in the measure.** You can preserve analytic \(C(K,\ell^1)\) input data and much of the abstract §4 infrastructure. You lose the current closed-form monomial-moment engine and must prove smooth-weighted asymptotics plus continuity and uniformity of the coefficient operators. This is a promising interface for protecting §4, but not a cheaper substitute for smooth asymptotic analysis.

**D3 — stratum-adapted weights.** Nothing essential is lost downstream: base multiplication preserves the present analytic datum, certificates, infinite pairings, and §4 interface. The cost is geometric scope: the producer applies only to atlases carrying the certified adaptation property. Neither SNC nor Watanabe’s local chart clause alone discharges that property.

---

# 6. Recommended programme

## Ranking

1. **Q1-α: weighted-atlas producer with an explicit adaptation hypothesis.**
2. **A bounded Q1-β project:** single blow-up first, then a precisely specified coordinate-centre composite class. Treat Q1-γ as a separate, substantially stronger existence obligation.
3. **D1 smooth asymptotic kernel, designed with a D2 analytic-data interface**, if the geometric programme fails or proves too restrictive.
4. **D2 as a standalone “move the weight” shortcut:** do not pursue it under that description; it does not discharge the new estimates.

## Units for the top choice

1. **Core base-weight adapter:** scale `c`, `x`, and the relevant certificate data once by a nonnegative continuous base weight; preserve the existing series and expansion witnesses.
2. **Weighted transport algebra:** pushforward/`withDensity` identities and finite-sum assembly, with no disjointness assumption.
3. **Adapted-partition structure:** per-core base-factorisation, partition identity, support, and gap obligations.
4. **Weighted domain-atlas producer:** reuse the existing holomorphic packets and per-core theorem.
5. **Tail bookkeeping:** prove that all omitted transition regions belong to one certified phase-gap remainder.
6. **Regression and compatibility theorem:** disjoint atlases embed as the old special case.

## First regression

Use an enlarged dominant-coordinate cover of a single blow-up, with genuinely overlapping interiors and the homogeneous direction weights above. Verify explicitly:

* positive-measure overlap;
* nonconstant smooth tangential weights;
* partition identity after normalisation;
* base-only dependence on every produced core;
* all extra divisor-component plateau conditions, if the phase includes strict transforms;
* weighted pushforward equality and the unchanged expansion output.

Do not let a merely radial check stand in for the full per-stratum check.

## Stopping rule

After that regression, attempt one nontrivial two-stage coordinate-centre composite. Stop broadening the geometric claim unless you can state and prove an induction invariant that preserves **the exact base-factorisation equations used by the cores**.

If the construction requires smoothly changing normal coordinates, or only produces controlled constancy unrelated to the analytic chart projections, count that as failure of the current-engine route—not as a nearly completed proof.

## Suggested non-claim wording

> We construct certificates from weighted domain-sector atlases equipped with an explicit per-core stratum-adapted partition. We verify this hypothesis for the stated blow-up models. We do not claim that arbitrary SNC resolutions or Watanabe modifications automatically supply such partitions, nor do we yet admit general normally varying smooth localisation weights into the analytic normal-series engine.

That is a useful, axiom-clean next landing without hiding either the geometric obstruction or the cost of the smooth fallback.
