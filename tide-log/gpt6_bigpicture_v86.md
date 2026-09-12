## Q1 — the regression is sound

The geometry and the coefficient are correct. I would proceed with this regression, with three implementation cautions:

1. distinguish **exact set identities** from identities only needed a.e.;
2. check that the package constructor accepts `ε ≤ b`, rather than imposing `ε < b`;
3. compute the actual finite piece sum before simplifying it to the displayed factor `2`.

### Geometry

For the two maps,
\[
\phi_0(s,t)=(s,st),\qquad \phi_1(s,t)=(st,t),
\]
the images of `dom = [-1,1]²` are exactly
\[
A_0=\{(a,b): |a|\le1,\ |b|\le |a|\},\qquad
A_1=\{(a,b): |b|\le1,\ |a|\le |b|\}.
\]

Thus their union is the square, and their intersection is contained in—and in fact equals the portion of—the two diagonals inside the square.

In the image-surjectivity argument, split off the zero pivot **before division**. For example, if `|b| ≤ |a|` and `a = 0`, then `b = 0`, and `(0,0)` is an explicit preimage. Otherwise use `(a,b/a)`.

Your exceptional sets
\[
E_\beta=\mathrm{dom}\cap\{y_\beta=0\}
\]
are right. Both map to the origin, and the supplied injectivity lemma gives the required injectivity off them. If `ResolutionChart` asks for regularity or an inverse away from the exceptional image beyond injectivity, the inverse formulas are just the corresponding quotient maps.

For disjointness, kernels of
\[
(a,b)\mapsto a-b,\qquad (a,b)\mapsto a+b
\]
are a good route. Establish once that each kernel is proper, using a coordinate basis vector; then apply the Haar-null proper-subspace result.

### Monomial data

Your identities are exactly
\[
K(\phi_\beta(y))=y_\beta^2(1+y_{\mathrm{rev}\,\beta}^2),\qquad
|\det D\phi_\beta(y)|=|y_\beta|.
\]
Thus
\[
e_\beta=2,\quad h_\beta=1,\quad
\lambda=\frac{h_\beta+1}{e_\beta}=1,\quad k=0.
\]

There is only one positive phase exponent. Make sure the minimum is taken over that active set: the tangential coordinate with `e = 0` must not enter a raw quotient-based minimum.

`W = univ` is legitimate for this hand-built monomial-chart proof: the phase unit is globally positive, the Jacobian unit is constant, and the polynomial chart is analytic. No inverse analyticity across the pivot hyperplane is being asserted.

### Dominant face and coefficient

Under the definitions you describe, the dominant face is precisely the tangential interval:
\[
\{z:\mathrm{Fin}\ 1\to\mathbb R: |z_0|\le1\}.
\]
The omitted-coordinate part of the foot condition is vacuous because `D = I = {β}`. The remaining facts are:

- the foot belongs to the chart domain;
- `G = p = v = 1` there;
- the tangential Jacobian monomial is the empty product;
- the tangential interval has positive volume.

So the positivity hypothesis is not merely nonempty-foot positivity: you really have a positive-measure family of positive feet.

The coefficient calculation is
\[
2\cdot\frac{\Gamma(1)}{0!}\cdot\frac12
 \int_{-1}^{1}\frac{dt}{1+t^2}
=\frac{\pi}{2}.
\]
The first factor `2` accounts for the two signs of the pivot coordinate. I would let `productCoeffV_extremal_eq_sum_minimal` expose its actual indexing and simplify that finite sum, rather than inserting this factor ahead of the package calculation.

Both charts are active at `(1,0)`, so the assembled coefficient is indeed `π`.

### Is `ε = b = 1` safe?

**Mathematically, yes.** Strictness of `|yβ| < ε` creates no problem:

- the near-divisor piece contains `|yβ| < 1`;
- the divisor-free piece contains the remaining `|yβ| = 1` faces;
- those faces are null;
- the foot has pivot coordinate zero, hence satisfies the strict near-divisor inequality.

In fact, the divisor-free source integral is identically zero here, not merely exponentially small.

There is one API-level qualification: if an existing constructor explicitly requires `ε < b`, do not weaken a large API just for this example. Use `ε = 1/2`; the dominant coefficient is unchanged, and the divisor-free region then has the elementary phase gap `K ∘ φ ≥ 1/4`. The general cutoff-dependent factors in the leading coefficient should simplify away because the logarithmic degree is zero.

**Recommendation:** use `ε = 1` if the public hypotheses allow it. Otherwise use `1/2` and keep the regression moving.

The final theorem should be obtained through the assembled certificate, with the Gaussian factorisation only as an external numerical check. That tests the machinery you actually want tested.

---

## Q2 — ranking

My ranking is:

1. **A: derived certificates for boundary-compatible product domains;**
2. **C: an honest statistical-transfer layer, with its hypotheses made explicit;**
3. **B: coefficient locality and an isolated-zero small-ball corollary;**
4. **D: one exactly solvable subleading-kernel theorem, not general subleading asymptotics;**
5. **E: a theorem-to-hypothesis audit, then stop rather than add another broad programme.**

I would land A, take the inexpensive locality results from B when convenient, and make C the next substantive mathematical decision.

### 1. A — valuable, but get the blow-up boxes exactly right

This is a worthwhile closure of the named gap for a genuine class of resolutions. It changes the conclusion from

> supplied resolution-compatible product packages imply an explicit coefficient

to

> concrete monomial-chart data on these specified domains produce the certificate and hence the explicit coefficient.

That is a meaningful theorem, even though it does not solve arbitrary compact chart domains.

#### The radius qualification

For the standard blow-up of the origin, the source domain producing the target cube `[-ρ,ρ]^d` is
\[
|y_\beta|\le\rho,\qquad |y_\gamma|\le1\quad(\gamma\ne\beta),
\]
not generally `[-ρ,ρ]^d` in source coordinates.

Its image is
\[
A_\beta=
\{x: |x_\beta|\le\rho,\ |x_\gamma|\le|x_\beta|\ \forall\gamma\}.
\]
These wedges cover the target cube. For distinct pivots,
\[
A_\beta\cap A_\gamma
\subseteq\{x_\beta=x_\gamma\}\cup\{x_\beta=-x_\gamma\},
\]
so they are a.e. disjoint.

For a coordinate-centre blow-up indexed by `B`, the comparisons are among the coordinates in `range B`; coordinates outside the centre retain their ordinary target bounds.

Thus: **yes, the standard wedge charts are a.e. disjoint**, provided `blowUpChartBox` has these intended bounds. Check its definition rather than infer the bounds from its name.

There is also a package issue: if the existing builder only handles equal-radius source boxes, these anisotropic boxes need either a rectangular-box builder or an affine rescaling to a unit box. Rescaling is harmless, but its Jacobian factor must enter the coefficient.

Finally, “one blow-up monomialises” should mean the identities and positivity hold on the **whole stipulated blow-up boxes**, not just in a neighbourhood of one point on the exceptional divisor.

#### A four-unit programme

1. Whole-box source certificates, without localization or shrinking.
2. Boundary-compatible finite product assemblies, including a convenient target a.e.-disjointness criterion.
3. Blow-up-box image formulas, exact coverage, and a.e. disjointness.
4. “One blow-up suffices” explicit-coefficient and posterior theorems, with the quadratic phase in dimension `d` as the regression.

For `K = ∑ xᵢ²`, this should recover
\[
\lambda=d/2,\qquad k=0,\qquad c=\pi^{d/2}
\]
for unit density and amplitude on a positive-radius cube.

### First unit of A: the statement

I would call it something like **`WholeBoxSourceCertificate`**. The following is a specification, not a claim about existing Lean identifiers.

> **Whole-box certificate theorem.**  
> Let `C` be a resolution chart whose domain is exactly a specified closed product box `Q`. Suppose the chart carries monomial data on an open neighbourhood of `Q`, and the specified box satisfies the hypotheses of the box-package construction. Let `G` be a continuous source amplitude on `Q`, with the integrability/sign hypotheses required by the source theory.  
> Then the monomial data canonically produce a product package `P_Q` and a one-chart `SourceDecomposition` for
> \[
> Z_Q(N)=\int_Q G(y)\,|\det D\Phi(y)|\,p(\Phi(y))
>                  e^{-N K(\Phi(y))}\,dy,
> \]
> whose remainder is identically zero. Its coefficient is
> `P_Q.sourceCoeff G lam₀ k₀`, and it satisfies the existing zero-compatible leading-term theorem. Under the existing positive dominant-face hypothesis, that coefficient is positive.

The important design constraints are:

- **no product package as an input;**
- **no compactly supported extension of `G` as an input;**
- **no shrinking the specified box;**
- the domain equality is literal, or a separate explicitly proved a.e. equality;
- the certificate constructor should work before imposing the extra positivity needed for equivalence.

This is not an application of `exists_sourceLocalization` to `G · 1_Q`. That extension is generally discontinuous at the boundary. It is a direct application of the box-package construction to the integral over `Q`.

If the existing builder only guarantees packages after choosing a sufficiently small radius, retain that admissibility hypothesis explicitly. Do not turn “there exists a smaller good box” into a theorem about the originally supplied box.

### 2. C — population and empirical coefficients are not automatically the same

This is the most important remaining interpretation issue.

A uniform law of large numbers for empirical loss is **not enough** to transfer the population coefficient ratio. The exponent multiplies the empirical error by `n`, and on the relevant shrinking neighbourhoods the empirical fluctuation can survive at order one.

Indeed, the deterministic ratio can fail even in an elementary analytic Gaussian model.

Take observations in `ℝ²`, true mean zero, and model mean
\[
m(a,b)=(a,ab),\qquad (a,b)\in[-1,1]^2.
\]
With identity covariance,
\[
K(a,b)=\frac12a^2(1+b^2).
\]
For a uniform prior, the population limiting distribution of `b` has density proportional to
\[
(1+b^2)^{-1/2}.
\]
But writing \(Z_n=\sqrt n\,\overline X_n\), the empirical limiting weight, after integrating out the shrinking `a` coordinate, is proportional to
\[
\frac1{\sqrt{1+b^2}}
\exp\!\left(\frac{(Z_{n,1}+bZ_{n,2})^2}{2(1+b^2)}\right).
\]
Here `Z_n` has a nondegenerate Gaussian distribution for every `n`. General observables of `b` therefore do not converge in probability to their population coefficient ratio.

So the companion material must identify **what cancels or what concentrates**; a generic Gaussian approximation alone does not provide the desired transfer.

#### Honest minimal transfer theorem

Let `μₙ` be the population posterior and let the empirical posterior have unnormalised density ratio
\[
R_n(\omega,w)=e^{-n(\widehat K_n(\omega,w)-K(w))}
\]
relative to `μₙ`. Assume there exist positive random scalars `Aₙ` such that
\[
\delta_n
=\int\left|R_n/A_n-1\right|\,d\mu_n
\longrightarrow0
\]
in probability, or almost surely.

Then, for bounded measurable `φ`,
\[
\left|\widehat\mu_n(\phi)-\mu_n(\phi)\right|
\le
\frac{2\|\phi\|_\infty\delta_n}{1-\delta_n}
\quad\text{when }\delta_n<1.
\]
Consequently the certified population limit transfers in the same mode.

This is a clean first abstract unit, but the hypothesis is substantial—not a disguised consequence of an ordinary ULLN.

A more directly useful statistical theorem may instead be:

> If the empirical posterior concentrates near `K⁻¹(0)`, and `φ` is continuous and constant there with value `φ₀`, then its expectation tends to `φ₀`.

That can follow from uniform loss convergence, a compact phase gap, and prior mass near minimizers. Where the population coefficient theorem applies, its ratio is also `φ₀`.

A reasonable C programme is: abstract perturbation transfer; concentration near minimizers; constant-on-minimizers observables; then the exact Gaussian companion result supported by its hypotheses. I cannot determine which final specialization is already available without seeing those companion statements.

### 3. B — prove locality, not unconditional small-ball invariance

“Coefficient of the region `N`” is the correct general final form. But there is an inexpensive and useful locality theorem:

> If two compact integration regions differ only on a set where `K ≥ κ > 0`, and the amplitude is integrable there, their integrals differ exponentially. Therefore any positive leading coefficients and pairs agree.

This immediately gives **small-ball radius independence around an isolated zero**, provided the balls lie inside a compact neighbourhood containing no other zeros. Their symmetric difference is an annular region with a positive phase gap.

For
\[
K(x)=\sum_{i=1}^d x_i^{2k_i},
\]
a small Euclidean ball can therefore be compared with an inner box. For continuous amplitude `f` with `f(0)>0`,
\[
\int_{\overline B(0,r)} f(x)e^{-NK(x)}\,dx
\sim
f(0)\prod_i\frac{\Gamma(1/(2k_i))}{k_i}\,
N^{-\sum_i1/(2k_i)}.
\]
No new ball-resolution certificate is necessary.

But radius independence fails with a positive-dimensional zero set. For example, on a Euclidean disk in `ℝ²`,
\[
K(x,y)=x^2
\quad\Longrightarrow\quad
\int_{\overline B(0,r)}e^{-Nx^2}\,dx\,dy
\sim 2r\sqrt\pi\,N^{-1/2}.
\]

A three-unit B programme—exponentially negligible symmetric differences, coefficient locality, isolated-zero/separable-ball regression—would be well justified.

### 4. D — start with the exact constant-unit kernel

The proposed second logarithmic term is not available for arbitrary continuous amplitudes. Continuity permits convergence to the face value slower than `1/log N`, producing corrections larger than the requested second term.

The clean first step is the all-minimal **constant-unit, constant-amplitude rectangular kernel**. If there are `m ≥ 2` active variables, all with
\[
(h_i+1)/e_i=\lambda,
\]
then the product substitution reduces the kernel to
\[
\int_0^B t^{\lambda-1}
       \bigl(\log(B/t)\bigr)^{m-1}e^{-Nu t}\,dt,
\qquad B=\prod_i b_i^{e_i},
\]
up to the explicit Jacobian/sign factor.

This yields an entire polynomial in `log N`, multiplied by `N^{-λ}`, with coefficients involving derivatives of `Γ`, and an exponentially small tail. In particular, the ratio of the second coefficient to the first is
\[
(m-1)\left(\log(uB)-\frac{\Gamma'(\lambda)}{\Gamma(\lambda)}\right).
\]

Two terminology cautions:

- this is the **next logarithmic coefficient at the same pole**, not the next pole;
- for `m = 1`, there is no second logarithmic coefficient of this kind.

Only after that regression should you consider variable units and amplitudes, with an explicit quantitative regularity hypothesis.

### 5. E — audit the semantic boundary

I would not infer an underserved theorem from the number of mirror dots. The valuable audit is whether each §3–§4 claim visibly distinguishes:

- population from empirical posterior;
- intrinsic pair from region-dependent coefficient;
- existence of a resolution from production of a compatible certificate;
- normalized coefficient functionals from ordinary pointwise evaluation.

The empirical/population distinction is the highest-risk one. Otherwise, after A and a carefully scoped C, **stopping is a respectable outcome**.

---

## Q3 — Lean/Mathlib specifics

I cannot inspect your pinned Mathlib revision here, so the following distinguishes the mathematical route from names/signatures I would verify.

### Transport from `Fin 1 → ℝ`

`MeasureTheory.volume_preserving_funUnique` is the right candidate. Check its direction and arguments with `#check`.

The robust target is the measure-preserving equivalence
\[
e:(\mathrm{Fin}\ 1\to\mathbb R)\simeq^m\mathbb R,\qquad e(z)=z(0),
\]
whose inverse sends `t` to the constant function.

Prove the set identity
\[
\{z:|z(0)|\le1\}=e^{-1}([-1,1]).
\]
Then use set-integral transport.

`MeasurePreserving.setIntegral_preimage_emb` is a plausible API entry, but **I would verify its exact name and hypotheses**. If awkward, rewrite the set integral using an indicator and use whole-integral transport through the measure-preserving equivalence. That avoids wrestling with the embedding-oriented set-integral interface.

### Arctangent integral

- `integral_inv_one_add_sq`: the right candidate; verify namespace and whether its integrand is written using division or inverse.
- `Real.arctan_one`: expected standard name.
- `Real.arctan_neg`: expected standard name.

The desired interval calculation is
\[
\int_{-1}^{1}(1+x^2)^{-1}\,dx
=\arctan(1)-\arctan(-1)=\pi/2.
\]

You still need the bridge from the `Icc` set integral to the interval integral. Endpoints are null for volume. Use the interval-integral conversion available in your revision rather than forcing the antiderivative theorem onto a set integral.

### Haar-null diagonals

`Measure.addHaar_submodule` is the candidate you mention; **verify its exact properness/finite-dimensionality hypotheses and namespace**.

For the usual finite pi type, `volume` should have the additive Haar instance. Test directly:
```lean
example :
    MeasureTheory.IsAddHaarMeasure
      (volume : Measure (Fin 2 → ℝ)) := by
  infer_instance
```
Namespace qualification may need adjustment.

Represent each diagonal as the kernel of a continuous linear map, then use its underlying linear submodule. The non-top proof should be a tiny coordinate computation. This is preferable to a general theorem about arbitrary null polynomial zero sets.

### Analytic coordinate maps

The expected route is the analytic API for continuous linear maps:

- `ContinuousLinearMap.analyticAt`;
- `ContinuousLinearMap.analyticOnNhd`;

with `ContinuousLinearMap.proj j`.

**Check the exact namespace/signature in your revision.** Analyticity of the blow-up coordinates then follows by multiplication and finite-pi assembly. Your suggested `AnalyticOnNhd.pi`/`.mul` route is appropriate.

Do not try to derive analyticity merely from `contDiff_blowUpChart`: smoothness alone is not enough.

### Finsupp support

`Finsupp.support_single_ne_zero` is the expected lemma. Verify argument order, and make the value type explicit: the nonzero proof is for the natural-number exponent `1` or `2`, not for a real coefficient.

Often the simplest proof is just:
```lean
simp
```
after unfolding `e` or `h`. I would try that before manually invoking the support lemma.

---

**Bottom line:** finish the square regression as planned; `ε = 1` is mathematically clean. Then make the next theorem genuinely derive a whole-box certificate without shrinking the box or introducing a discontinuous cutoff. The next major conceptual guardrail is that empirical posterior limits need not equal population coefficient ratios.
