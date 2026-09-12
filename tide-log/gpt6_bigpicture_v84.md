**I would land the local explicit-coefficient constructor first, and keep global coefficient identification as a separate programme.** There are two important corrections to Q1:

1. Restricting the phase support to \(J_0\) is correct, but restricting the Jacobian support to \(J_0\) is generally **not**.
2. A continuous target-space partition subordinate to resolution-chart images need not exist—even for perfectly good blow-up charts. This is a genuine geometric obstruction, not merely a missing Mathlib partition-of-unity lemma.

The `hact` removal is a cheap, useful independent unit.

## Q1. The localisation constructor

### (a) Restrict the phase support; initially leave the Jacobian exponents alone

Yes:
\[
J_0=\{j:e_j\ne0,\ (y_0)_j=0\}
\]
is nonempty at a divisor point, but need not equal `supp e`.

Set
\[
e'_j=\begin{cases}e_j&j\in J_0,\\0&j\notin J_0,\end{cases}
\qquad
u'(y)=u(y)\prod_{j\notin J_0}y_j^{e_j}.
\]
On
\[
W'=W\cap\{y:\forall j\in\operatorname{supp}(e)\setminus J_0,\ y_j\ne0\},
\]
this gives a continuous nonvanishing unit and the required phase identity.

**But your proposed \(h'=h|_{J_0}\) can fail.** There may be a coordinate with
\[
e_j=0,\qquad h_j>0,\qquad (y_0)_j=0.
\]
Its Jacobian factor cannot be absorbed into a nonvanishing unit near \(y_0\). Your proposed \(W'\) does not exclude these zeros, and excluding them would remove \(y_0\).

The simplest constructor should therefore use:

```text
new phase exponents := e restricted to J₀
new phase unit      := u × removed phase factors
Jacobian exponents  := h
Jacobian unit       := v
```

Then `injOn` is inherited immediately by shrinking \(W\); no changed Jacobian nonzero-locus needs proving.

A useful general lemma is indeed worth landing, but I would separate it into:

* **phase restriction:** truncate `e` when the removed factors are nonzero, leaving `h` unchanged;
* **Jacobian restriction:** truncate `h` when its removed factors are nonzero.

If you want both centred, the safe retained Jacobian set is
\[
H_0=\{j:h_j\ne0,\ (y_0)_j=0\},
\]
not necessarily \(J_0\). Tangential Jacobian monomials are legitimate and must remain available.

### (b) The box need only lie in the monomial neighbourhood—not in the old compact domain

An arbitrary compact `dom` need not contain any box around \(y_0\). Thus:

> `y₀ ∈ dom` is insufficient for constructing a product box contained in `dom`.

For the **local constructor**, make a **new chart using the same map on its open monomial neighbourhood**. Do not describe it as a domain restriction of the old `ResolutionChart` unless you additionally assume \(y_0\in\operatorname{interior}(\mathrm{dom})\).

Take a tangential rectangle
\[
T=\{x:x_j=0\ (j\in J_0),\quad
             |x_j-(y_0)_j|\le\delta\ (j\notin J_0)\}.
\]
Then choose \(\delta,b>0\) so that
\[
B=\operatorname{productDom}(J_0,T,b)\subset W'.
\]
This is just a closed rectangle around \(y_0\), expressed in the package’s coordinates. No translation is necessary: the \(J_0\)-coordinates of \(y_0\) already vanish.

For the exceptional set, use the monomial certificate directly:
\[
E_B=B\cap\{y:\operatorname{monomialEval}(y,h)=0\}.
\]
It is a finite union of coordinate-hyperplane sections, hence closed and null; injectivity and Jacobian nonvanishing off it follow from `IsMonomialChart`. This avoids relying on the old exceptional set outside the old domain.

**Keep the distinction explicit:**

* `localProductChart`: new box inside \(W'\);
* `restrictedProductChart`: additionally supplied proof \(B\subseteq\mathrm{dom}\).

Only the latter participates automatically in the original partial resolution’s coverage statements.

Also, any parity/positive-unit result needs nonnegativity of \(K\circ\phi\) on a suitable open neighbourhood—not merely on an arbitrary compact `dom`. Under the analytic/nonnegative local hypotheses of your existing centred-chart theorem, shrink to obtain that hypothesis. The symmetric normal directions then force the retained phase exponents to be even and the phase unit positive.

### (c) Do not make finite a.e.-disjoint image boxes the next promised theorem

Neither \(\alpha\) nor \(\beta\) follows cheaply from the supplied resolution interface.

A concrete obstruction to \(\beta\) is the blow-up chart
\[
\phi(s,t)=(s,st),\qquad K(a,b)=a^2+b^2.
\]
Then
\[
K\circ\phi=s^2(1+t^2),\qquad \det D\phi=s.
\]
This satisfies the relevant monomial and off-exceptional injectivity properties. But the image of a small box around \((0,0)\) is a wedge:
\[
|b|\le\delta |a|.
\]
Its image contains the divisor point \(0\), but does **not** contain a target neighbourhood of \(0\).

Consequently, a continuous target function supported in that wedge must vanish at \(0\). A finite collection of such wedges can cover a target neighbourhood while none individually contains a neighbourhood of \(0\). A continuous subordinate partition with sum one there is then impossible.

Thus the right condition for applying the usual topological partition theorem is not merely
\[
C\subseteq\bigcup_p A_p,
\]
but an appropriate **relative interior cover**:
\[
C\subseteq\bigcup_p\operatorname{int}_{U}(A_p).
\]
Resolution images do not generally provide this.

For \(\alpha\), essential disjointness would indeed give the clean theorem
\[
\int_U f=\sum_p\int_{A_p}f,
\]
with constant one-chart amplitudes. But constructing such a finite decomposition by product-chart images is the hard part. Arbitrary chart transitions and clipping by the target region do not preserve product boxes. Even a fixed disk in an identity chart is not a finite union of axis-aligned boxes modulo null sets.

**Recommendation:**

* Keep CCLXV as the target-partition assembly theorem **when its partition is supplied**.
* Prove an a.e.-disjoint assembly theorem when essential disjointness is supplied, if useful.
* Do not yet promise a constructor producing either certificate from `PartialResolution.IsMonomial`.

The standard general-resolution route is instead a **partition on the resolved space**, subordinate to source coordinate neighbourhoods, followed by change of variables. That permits smooth source amplitudes with compact support inside coordinate boxes. But it needs additional structure: a common resolved space, compatible charts, and a global map with the appropriate a.e. multiplicity/change-of-variables theorem. The displayed `PartialResolution` interface does not expose that structure.

This would also suggest a future assembly interface accepting **source amplitudes plus an exact integral-decomposition certificate**, rather than requiring every local amplitude to be the pullback of a target partition function.

### (d) Negligible complements: yes, but state the separation hypothesis correctly

Add the generic lemma:

```text
HasLeadingTerm.add_isLittleO
```

where the little-o is relative to the leading scale.

Also useful is a wrapper taking
\[
|R_N|\le C e^{-\kappa N},\qquad \kappa>0.
\]

However, compactness alone does not give a gap on “the complement of closed divisor boxes.” That complement need not be compact, and zeros on box boundaries may be approached from outside.

A convenient sufficient hypothesis is:

> The retained region contains a relative neighbourhood of the entire zero set in the compact integration region.

Then the closure of the remainder is compact and disjoint from the zero set, yielding \(K\ge\kappa>0\).

### (e) Positivity: correct conclusion, with two qualifications

A full tangential rectangle has positive measure in its **tangential coordinate measure**, including the zero-dimensional case. Its ambient \(d\)-dimensional measure is irrelevant.

But:

1. With `h` retained, a tangential Jacobian monomial may vanish at \(y_0\).
2. The dominant face freezes the **ratio-minimising coordinates**, not necessarily all of \(J_0\).

Neither prevents positivity. If \(Fp\) is continuous and positive at \(\phi(y_0)\), it stays positive nearby. Choose tangential coordinates away from the finitely many Jacobian hyperplanes, and residual active coordinates nonzero and small. This gives a positive-measure portion of the dominant face on which the residual integrand is positive.

For weighted assembly, positivity of a tied chart’s partition amplitude remains a separate obligation. Unweighted positivity at \(y_0\) does not establish positivity of \(p\psi_i\) there.

## Q2. The first coefficient theorem should be local

I agree strongly with your proposed minimal version, with one simplification:

**You do not need the target point to have a unique preimage in the whole resolution.** For the integral over this one chart image, the chart’s own off-exceptional injectivity suffices.

The theorem should say, schematically:

> Given a monomial chart, a divisor point \(y_0\), local nonnegativity of the phase, and a continuous amplitude positive at \(\phi(y_0)\), there is a centred product box \(B\) around \(y_0\) such that
> \[
> \int_{\phi(B)}Fp\,e^{-NK}
> \sim c_B N^{-\lambda}(\log N)^{m-1},
> \]
> where \(c_B>0\) is the existing variable-unit residual expression instantiated with the constructed chart.

This upgrades the local theorem without solving global localisation.

### A useful mathematical specification of the coefficient

Write \(A=J_0\), \(a_j=e'_j>0\), and
\[
\lambda=\min_{j\in A}\frac{h_j+1}{a_j},
\qquad
D=\left\{j\in A:\frac{h_j+1}{a_j}=\lambda\right\},
\qquad m=|D|.
\]
Let \(t\) denote tangential coordinates and \(z\) the active residual coordinates \(A\setminus D\). Define the amplitude with active Jacobian powers removed:
\[
H(y)=(Fp)(\phi(y))\,|v(y)|
       \prod_{j\notin A}|y_j|^{h_j}.
\]
For the symmetric box, the coefficient has the form
\[
\boxed{
c_B=
\frac{2^m\Gamma(\lambda)}
     {(m-1)!\prod_{j\in D}a_j}
\int_{T_{\mathrm{coord}}}
\int_{[-b,b]^{A\setminus D}}
H(t,z,0_D)\,
u'(t,z,0_D)^{-\lambda}
\prod_{j\in A\setminus D}|z_j|^{h_j-a_j\lambda}
\,dz\,dt .
}
\]
Here \(T_{\mathrm{coord}}\) is the coordinate rectangle parametrising \(T\), not \(T\) with ambient volume. The empty-dimensional integrals have their usual value-one convention.

I would initially expose this through your existing certified residual formula, rather than re-prove the displayed normalisation independently.

**Important scope distinction:** this identifies the coefficient for \(\phi(B)\). Pair equality with CCIX’s small-ball pair does **not** identify the small-ball coefficient. Coefficients depend on the region, and equality of pairs plus Θ-comparison contains no information sufficient to recover them.

## Q3. Remove `hact` using zero certificates

**Yes.** If the variable no-active theorem gives coefficient zero at every admissible pair, no exponential estimate is needed for this assembly result.

Let
\[
I_{\mathrm{act}}=\{i:\operatorname{supp}(e_i)\ne\varnothing\}.
\]
Then:

1. Assume `I_act.Nonempty` for the polynomial leading-term branch.
2. Define the extremal pair using active charts only.
3. Assemble active charts at that pair.
4. Give each inactive chart its zero certificate **at that same pair**.
5. Add all the certificates.

Keep a separate all-inactive conclusion: coefficient zero at every pair, not an arbitrarily selected positive leading coefficient.

Based on the APIs you describe, the empty-stratum argument is the right implementation route. I cannot verify the exact existing exports or whether the variable copy is literally ten lines, but mathematically there is no additional exponential-analysis obligation.

## Q4. Ranked next five units

### 1. `VariableNoActiveAssembly`

* Variable no-active zero certificate.
* Active-only extremal index set.
* `hact`-free partition leading-term theorem.
* Positivity/equivalence/posterior wrappers with an active tied-chart witness.

This is the cheapest substantial completion of CCLXV.

### 2. `MonomialChartRestrictFactors`

* Phase-support restriction.
* Separate Jacobian-support restriction.
* Divisor-point specialisation producing `supp e' = J₀`.
* Retain `h` by default.
* Reuse or expose the existing local parity/positive-unit result.

This is broadly reusable algebraic infrastructure.

### 3. `MonomialChartProductBox`

Construct the one-chart `ProductMonomialChartVar` on a box inside \(W'\), with:

* compact, nonempty tangential rectangle;
* positive widths;
* canonical monomial exceptional set;
* one-chart weight \(r=1\);
* optional refinement asserting containment in the old domain.

This is the actual missing constructor.

### 4. `LocalExplicitResidualCoefficient`

Instantiate CCLXVII for that constructor:

* explicit coefficient;
* positivity;
* pair agreement with `CentredChartData`;
* optionally a local posterior ratio.

This is the main mathematical payoff and a clean stopping point.

### 5. `PartitionAssemblyRegression`

Use two overlapping **identity-chart interval boxes**, with continuous ramps whose supports lie inside the respective chart images, and a phase such as \(K(x)=x^2\). Choose the ramps so both charts have positive weight at the dominant point.

Check:

* masked partition construction;
* the two weighted coefficients;
* their sum equals the unpartitioned coefficient;
* the posterior limit or free-energy constant.

This exercises the genuine partition theorem without pretending to solve the blow-up-image obstruction.

I would put `HasLeadingTerm.add_isLittleO` into a small generic consequences unit when convenient, but defer the global geometric decomposition programme until its additional input is explicitly chosen.

**Bottom line:** you now have enough asymptotics. The next local step is mostly chart construction, and it should succeed. The global step is not “find the right partition-of-unity theorem”; it is “supply a decomposition geometry compatible with resolution images or move the partition upstairs.”
