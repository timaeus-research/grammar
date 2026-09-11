**Yes: the weighted-coordinate repair is mathematically sound.** The extra weights change the leading coefficient, not the exponent pair. The main qualifications concern which integral the pair belongs to, and what “all divisor points” means—not the local weighted calculation.

Also, I retract the earlier claim about availability of the finite cover: the source-neighbourhood argument you describe supplies exactly the missing ingredient.

## 1. Weighted tangential coordinates

Write the local integral schematically as
\[
\int_A\int_{[0,b]^r}
 a(v,x)\,w(v)\,x^{h_N}
 \exp\!\left[-N\beta(v,x)x^{e_N}\right]\,dx\,dv,
\qquad
w(v)=\prod_i|v_i|^{hT_i},
\]
where \(a,\beta>0\), and all components of \(e_N\) are positive.

Then
\[
\lambda=\min_j\frac{h_{N,j}+1}{e_{N,j}},
\qquad
m=\#\left\{j:\frac{h_{N,j}+1}{e_{N,j}}=\lambda\right\}
\]
are unchanged. The tangential weight is independent of both \(N\) and the normal variables, so it multiplies the face coefficient rather than introducing a Mellin pole.

### Positivity in (d)

After extracting the leading normal term, the coefficient has the form
\[
c=\int_A w(v)L(v)\,dv
\]
(up to the orthant sum and your explicit positive scaling constants), with \(L(v)>0\) under your positive-unit and \(F>0\) assumptions.

On a genuine tangential box:

* \(w\ge0\);
* its zero set is a finite union of coordinate hyperplanes;
* \(w>0\) almost everywhere;
* the box has positive measure.

Thus \(c>0\). In particular, **the fact that \(w(0)=0\) does not make the leading coefficient vanish**: the coefficient integrates over the tangential directions rather than evaluating them at the base point.

The remaining normal powers are integrable because, for each nonminimiser,
\[
h_{N,j}-e_{N,j}\lambda>-1.
\]
Nothing new occurs there.

Your Banach-data implementation is also appropriate: multiplying the datum by the bounded continuous scalar \(w(v)\) preserves the required uniform normal-analytic control. It need not preserve analyticity in \(v\), but that is harmless **provided the analytic-core theorem only requires continuity/integrability in the tangential parameter**, as your description suggests.

Handle the zero-dimensional tangential case separately or by the standard empty-product/zero-dimensional-volume conventions.

### Almost-everywhere injectivity

Under the regularity you state, there is no mathematical obstacle.

Let \(B\subset\mathbb R^d\) be the closed box, \(H\) the finite union of exceptional hyperplanes, and \(\Psi\) be \(C^1\) on an open neighbourhood of \(B\). Then:

1. \(B\cap H\) is null.
2. \(\Psi(B\cap H)\) is null: locally Lipschitz maps between equal-dimensional Euclidean spaces preserve null sets.
3. Apply injective change of variables on \(B\setminus H\).
4. Restore the omitted source and target sets.

You do **not** need
\[
\Psi(B\setminus H)=\Psi(B)\setminus\Psi(B\cap H).
\]
Exceptional points may share images with good points. The discrepancy is contained in the null set \(\Psi(B\cap H)\), which suffices.

Be sure that \(\Psi\) really is \(C^1\) across the closed-box faces; a positive-root substitution at zero would require a separate argument. A smooth strip-normalisation diffeomorphism, as described here, is fine.

### A potentially substantial Lean saving

**Do not automatically downgrade every image to `NullMeasurableSet`.** For your specific exceptional sets, ordinary Borel measurability can survive:

* \(\Psi(B)\) is compact;
* \(\Psi(B\cap H)\) is compact;
* \(B\setminus H\) is \(\sigma\)-compact, for example using compact subsets bounded away from \(H\);
* consequently, \(\Psi(B\setminus H)\) is \(\sigma\)-compact and hence Borel.

Thus an `injOn_off_hyperplanes` or `injOn_off_closed_null` interface may avoid a broad `toMeasurable` refactor. For more general Borel pieces, injectivity plus the standard Borel measurable-image theorem is another route.

I would investigate this before implementing (a) in its most general form.

## 2. The support hypothesis is not implied by the listed chart axioms

There is a very simple counterexample:
\[
\phi(x,y)=(x,y^3),\qquad K(X,Y)=X^2.
\]
Then
\[
K\circ\phi=x^2,\qquad \det D\phi=3y^2.
\]
So
\[
e=(2,0),\qquad h=(0,2).
\]

Moreover:

* \(K\ge0\);
* \(K(\phi(0,0))=0\);
* the phase and Jacobian units are positive analytic units;
* \(\phi\) is even globally injective.

Yet \(h_2>0\) and \(e_2=0\). Compact rectangles and their images give the corresponding compact-domain picture.

So **even strengthening the chart’s injectivity would not discharge the condition**. This is genuinely missing divisor-support information, not a consequence of positivity.

### What readout information would suffice?

A sufficient geometric statement is, on an open chart neighbourhood,
\[
\{\det D\phi=0\}\subseteq\{K\circ\phi=0\}.
\]
For a coordinate hyperplane passing through the relevant point, choose a nearby generic point on that hyperplane with all other coordinates nonzero. The monomial identities then imply
\[
h_j>0\Longrightarrow e_j>0
\]
for that coordinate.

The open-neighbourhood qualification matters: containment only at the divisor point itself says nothing, since the phase already vanishes there.

I cannot certify what `IsQChart` or `PartialResolution.E` exposes without their actual declarations. The precise things to search for are:

* Jacobian nonvanishing over \(\{K\ne0\}\);
* a local-diffeomorphism statement over the nonzero-phase locus;
* a factorisation through blowups together with the “centres lie over the phase zero set” invariant;
* or explicit support containment as above.

A named exceptional set, without the relevant containment and Jacobian statements, is insufficient. If those invariants have been erased by the readout, you cannot recover them merely from the monomial identities.

**Recommendation:** use the weighted theorem as the general result. If the support invariant later becomes accessible, derive the strictly-positive-tangential-unit case as a convenient specialisation.

## 3. Next paper target: uniqueness, then identification—but localise carefully

My priority order would be:

1. **Canonical exponent pair for a fixed integral**, using your existing uniqueness theorem.
2. **Identification with `laplaceTheta`**, after aligning its region/germ and conventions.
3. **Empirical transfer**, if it addresses the paper’s main remaining claim.
4. Full power–log expansion later, unless the paper actually needs its coefficients.

### (ii): What uniqueness immediately gives

If two constructions prove
\[
Z_\Omega(N)=\Theta\!\left(N^{-\lambda}(\log N)^{m-1}\right)
\]
for the **same** \(Z_\Omega\), their pairs agree. This gives:

* independence from the finite subcover;
* independence from auxiliary boxes and strip choices;
* independence from the resolution, whenever both constructions concern that same integral.

This is a short, high-value result.

### “All divisor points” requires an additional comparison

Independence from a finite subcover does **not by itself** prove equality with the minimum over every divisor point of the original resolution.

To include another point \(p\), you need its local contribution to be visible to \(Z_\Omega\), for example
\[
Z_p(N)\le C\,Z_\Omega(N).
\]
Then comparison of rates yields
\[
\lambda_*\le\lambda_p,
\qquad
\lambda_*=\lambda_p\Longrightarrow m_*\ge m_p.
\]
Together with an attaining point from the finite family, this gives the all-points formula for the appropriate collection of points.

A divisor point whose image lies outside \(\Omega\) has no such automatic comparison. Even a point mapping to \(\partial\Omega\) needs care: intersecting its chart image with \(\Omega\) might remove its leading contribution.

The safe formulation is therefore:

> The pair is the extremal pair over all divisor-point pieces admissible for, or suitably comparable with, the chosen integration region.

A stronger formulation over an entire resolved compact set needs a theorem establishing that comparison.

### (iii): Region exponent versus germ RLCT

This is the most important terminology checkpoint.

“Some compact neighbourhood \(\Omega\) of \(w\) has pair \((\lambda_*,m_*)\)” is not yet the assertion that this is **the germ RLCT at \(w\)**.

For example,
\[
K(x)=x^2(x-a)^4,\qquad a\ne0,\qquad w=0.
\]
A sufficiently small neighbourhood of \(0\) has pair \((1/2,1)\); a region also containing \(a\) has pair \((1/4,1)\). Accordingly, the minimum over all divisor points above a larger \(N\) need not equal the germ invariant at \(w\).

For the `laplaceTheta` identification, check:

* Is its integral over exactly the same region?
* If it is germ-local, have sufficiently small neighbourhoods been shown to have the same pair?
* Does \(\theta_H\) denote the logarithmic exponent or the pole multiplicity?
* Are phase exponents recorded as \(e_j\) or \(2k_j\)?

If both theorems already control the same integral, uniqueness should make the identification very cheap. If not, **the localisation/comparison bridge is the next mathematical theorem**, not mere bookkeeping.

### (iv): Statistical transfer

This is likely more paper-relevant than a full deterministic expansion. But it needs genuinely additional hypotheses controlling the empirical phase—not just the deterministic resolution pair.

Also separate:

* an \(O_p(1)\) remainder in free energy;
* an \(O(1)\) remainder after expectation;
* the annealed quantity \(-\log \mathbb E Z_n\).

The first does not imply the second without integrability control, and the third is a different object.

## 4. What in §1 is overclaimed?

**The three landed mathematical results, as qualified by their stated hypotheses, sound properly scoped.** In particular:

* finite overlapping pieces suffice for the positive-integrand \(\Theta\) argument;
* the exponential off-union remainder is the right estimate;
* taking \(-\log\) gives the displayed \(O(1)\) free-energy remainder.

My blunt qualifications are:

1. **Currently conditional:** CCVII still depends on the Jacobian-support hypothesis until the weighted extension or a support theorem lands.
2. **A selected finite-family formula is not yet an all-divisor-points formula.**
3. **A neighbourhood-integral exponent is not automatically the germ RLCT at \(w\).**
4. **A \(\Theta\) formula is not a global leading equivalent or a full expansion.** Your route D correctly claims only the former.
5. **“Unconditional through `Q_all`” should mean “without the extra support condition,”** not without the analytic, positivity, resolution-existence, and localisation hypotheses.

The local analytic gap is now well identified and repairable. I would implement weighted tangential amplitudes while retaining Borel image measurability where possible, then immediately prove fixed-integral canonicity and audit the precise localisation needed for the `laplaceTheta` identification.
