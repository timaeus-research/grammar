## Recommendation

**Make the next programme a stochastic quotient calculus for the full retained expansion, with a first nontrivial posterior correction as its flagship application.**

The key distinction is:

> At polynomial accuracy, the natural posterior expansion is generally **a quotient of power–log sums**, or equivalently a power expansion with **rational functions of \(\log n\)** as coefficients—not a finite power–log sum.

That is a substantive theorem programme, not merely packaging. You already have almost all its analytic and probabilistic inputs.

I am treating the reported declarations as available; the Lean names I propose below are **new declarations**, not claims about existing Mathlib APIs.

---

# 1. Ranked programmes

## 1. Full posterior quotient expansion, then the first correction law

Write \(L_n=\log n\), and let the retained numerator and denominator sums be
\[
P_n=\sum_{\mu<U,q}A_{\mu,q,n}n^{-\mu}L_n^q,\qquad
Q_n=\sum_{\mu<U,q}B_{\mu,q,n}n^{-\mu}L_n^q.
\]
Suppose the common leading scale is
\[
s_n=n^{-\lambda}L_n^{m-1},
\]
and the normalized denominator has a strictly positive limiting law.

The headline should be:

\[
\boxed{
\frac{N_n}{D_n}-\frac{P_n}{Q_n}
=
O_P\!\left(n^{-(U-\lambda)}L_n^{d-m}\right)
}
\]
when the evidence remainders are
\[
O_P\!\left(n^{-U}L_n^{d-1}\right).
\]
Consequently, for every \(a<U-\lambda\),
\[
n^a\left(\frac{N_n}{D_n}-\frac{P_n}{Q_n}\right)\longrightarrow_P0.
\]

Here \(d-1\) can be replaced by the actual logarithmic remainder exponent your atlas theorem supplies. Bounded observables give an especially clean proof.

**Second headline:** for \(m\ge2\), a first inverse-logarithmic posterior correction:
\[
L_n\left(
\frac{N_n}{D_n}-\frac{A_{0,n}}{B_{0,n}}
\right)
\Rightarrow
\frac{A_1B_0-A_0B_1}{B_0^2},
\]
where
\[
A_{j,n}=A_{\lambda,m-1-j,n},\qquad
B_{j,n}=B_{\lambda,m-1-j,n},
\]
and the four variables on the right have their already-available joint Gaussian-functional law.

Crucially, the centering is the **prelimit** ratio \(A_{0,n}/B_{0,n}\), not the limiting posterior random variable.

### Why not a finite power–log expansion?

Already
\[
\frac{a_0L+a_1}{b_0L+b_1}
\]
has a generally infinite expansion in \(L^{-1}\). A finite truncation leaves an inverse-logarithmic error, which is not \(o(n^{-a})\) for any \(a>0\).

The right all-polynomial-accuracy object retains that rational logarithmic block exactly. Exceptional cases—\(m=1\), exact cancellation, or special denominator structure—can admit simpler expansions.

---

## 2. A conditional geometric constructor for the chart kernel package

The headline should **not** initially be

> analytic \(K\) + relative finite variance implies `AnalyticChartKernel`.

That hides an integrability hypothesis.

Instead prove a theorem of the form:

> A resolved analytic log-density-ratio map with values in \(L^6\), together with the relative finite variance inequality and the resolved monomial form of \(K\), produces the analytic \(L^6\) quotient kernel and the chart regularity package.

The central conditional divisibility statement is roughly:
\[
F(u)\in L^6,\qquad
\|F(u)\|_{L^2}\le C|u^k|
\quad\Longrightarrow\quad
F(u)=u^k a(u),
\]
with \(a\) analytic into \(L^6\), on a suitably shrunk neighbourhood.

This is plausible because \(L^6\hookrightarrow L^2\) is continuous and injective on a probability space: the \(L^2\) inequality forces the forbidden Taylor coefficients to vanish, and injectivity makes them vanish in \(L^6\) too. Then one performs analytic monomial division.

**The important qualification:** this uses analytic \(L^6\)-valued \(F\) before division. Relative finite variance supplies \(L^2\) information; it does not manufacture sixth moments.

This programme would remove a major interface assumption without pretending to solve an integrability upgrade that is unavailable in general.

---

## 3. An explicit first subleading coefficient—but with the correct face structure

Start with a theorem identifying the \(q=m-2\) coefficient with the corresponding Taylor-tree/Mellin expression. Its value is interpretability: it makes the first posterior correction above an explicit Gaussian functional.

I would stage it as:

1. smooth-field formula;
2. continuity of the explicit expression on the required jet space;
3. equality with `cubeCoeffGenOnClosedJets` by density and uniqueness of continuous extension.

**Do not promise that this coefficient depends only on a finite jet on the deepest leading face.** Lower logarithmic coefficients can contain finite-part integrals along larger faces.

For example, in
\[
\int_{[0,1]^2}\eta(x,y)e^{-t x^2y^2}\,dx\,dy,
\]
the leading pair is \((1/2,2)\). A weight supported away from \(x=0\), but meeting \(y=0\), has all jets zero at the deepest corner and can nevertheless contribute a nonzero \(t^{-1/2}\) term. That contribution involves an edge integral with an \(x^{-1}\)-type residue weight.

Thus the paper’s formula should be formalised as a sum over the actual Taylor-tree strata and Mellin functionals—not paraphrased as “a local polynomial at the leading intersection.”

I would do the first subleading log before the next exponent: it directly feeds programme 1 and involves less lattice bookkeeping.

---

## 4. Atlas invariance through **frozen-field uniqueness**

There is real content here, but it requires a stronger formulation than uniqueness of stochastic expansions.

The useful headline is:

> For two atlases describing the same deterministically deformed evidence integral, and a fixed compatible fluctuation field, the aggregated power–log coefficients agree after embedding both supports in a common index set.

Prove ordinary uniqueness of finite power–log asymptotic expansions with coefficients independent of the asymptotic parameter. Apply it with the field frozen. Then pass to compatible Gaussian fields and their laws.

This gives a credible route to intrinsic aggregated coefficient functionals and hence intrinsic support.

By contrast, the evidence sequence and a triangular-array stochastic expansion alone do **not** determine all coefficient limit laws. For example,
\[
Z_n=C_{0,n}+n^{-\delta}C_{1,n}
\]
also equals
\[
\bigl(C_{0,n}+n^{-\delta}H\bigr)
+n^{-\delta}\bigl(C_{1,n}-H\bigr).
\]
The leading coefficient limit is unchanged; the subleading coefficient limit can change arbitrarily.

So the proposed “trivially intrinsic, as a limit” argument works for the uncentered leading normalization, but not automatically for the entire coefficient vector.

---

## 5. Remainder coherence and sharper cutoff bounds

You already have the substance of an arbitrarily deep **stochastic expansion**, conditional on the regularity and tail hypotheses needed at that depth.

A useful theorem would package:

* compatibility of coefficients across cutoffs;
* consistency of truncation;
* the exact \(O_P(n^{-U}L_n^{d-1})\) remainder;
* consequences at every strictly smaller polynomial rate.

But this is lower-value than the programmes above unless it yields a genuinely sharper exponent, a smaller logarithmic loss, or quantitative probability bounds.

Tracking constants alone is not enough to obtain concentration or Berry–Esseen estimates. Those require quantitative empirical-process input beyond weak convergence and tightness.

---

# 2. Concrete Lean plan for programme 1

## Stage A: a reusable quotient perturbation theorem

Keep this independent of charts, jets, and Gaussian limits.

### Data model

A schematic structure could contain:

```lean
structure QuotientApproxData (Ω : Type*) where
  numerator denominator : ℕ → Ω → ℝ
  numeratorApprox denominatorApprox : ℕ → Ω → ℝ
  leadingScale errorScale : ℕ → ℝ
  obsBound : ℝ
```

Put probabilistic hypotheses in theorem arguments or a companion structure:

* measurability of the four arrays;
* eventual positivity of `leadingScale`;
* numerator and denominator approximation errors are \(O_P(\texttt{errorScale})\);
* `denominatorApprox / leadingScale` converges in distribution to \(B\);
* \(B>0\) almost surely;
* almost surely, for each \(n\),
  \[
  D_n\ne0,\qquad |N_n/D_n|\le M.
  \]

For the generic non-observable version, replace the bounded-ratio hypothesis by tightness of \(N_n/D_n\). The bounded version is the easiest first theorem and is exactly suited to your application.

Suggested declarations:

```lean
quotient_sub_quotient_eq_on
abs_quotient_sub_quotient_le_on
quotientApprox_error_isBoundedInProbability
quotientApprox_error_tendstoInMeasure
```

### Deterministic identity

On \(D\ne0\), \(Q\ne0\),
\[
\frac ND-\frac PQ
=
\frac{(N-P)-(N/D)(D-Q)}{Q}.
\]
Therefore
\[
\left|\frac ND-\frac PQ\right|
\le
\frac{|N-P|+M|D-Q|}{|Q|}.
\]

This formulation avoids separately proving tightness of the approximate numerator.

### Probabilistic engine

Use strict positivity of \(B\) and convergence in distribution to show
\[
s_n/Q_n=O_P(1),
\qquad
\mathbb P(Q_n=0)\to0.
\]
Then multiply the scaled error bounds by this tight reciprocal.

**Important:** strict positivity of the limit does not give a deterministic lower bound on it. The proof must choose a small \(\delta>0\) with
\[
\mathbb P(B\le\delta)
\]
small, and then transfer the estimate to \(Q_n/s_n\).

Also, it does not give eventual almost-sure positivity of \(Q_n\).

### Existing machinery

The main carriers should be the machinery already used for:

* `tendstoInDistribution_div`;
* the tight-times-null argument in `LeadingLaw`;
* `tendstoInDistribution_posteriorMean_leading`.

For Mathlib searches, I would search the concepts `TendstoInDistribution`, `TendstoInMeasure`, tightness, and boundedness in probability rather than assume a particular exported name. The nonprobabilistic layer should need only ordinary field algebra and absolute-value inequalities.

---

## Stage B: paired aggregated evidence expansions

The landed results sound sufficient mathematically, but check that the interface supplies one joint coefficient vector for **both** weights:
\[
w_\alpha,\qquad w_\alpha(\mathrm{obs}\circ g_\alpha).
\]

A natural new declaration is:

```lean
evidence_expansion_commonLattice_pair
```

It should return:

1. one common lattice;
2. one retained index set;
3. both approximation remainders;
4. joint convergence of the paired aggregated coefficient vector;
5. identification of its leading denominator component.

Do not reconstruct the joint law from two marginal convergence statements. Use `jointChartCoeffLaw_pair`, or the general finite-family coefficient law followed by the linear aggregation map.

If pairing is already fully subsumed by a finite observable family, generalise immediately to
```lean
obs : ι → Parameter → ℝ
```
with finite `ι` and the constant observable included. Then the posterior result gives a **joint law of finitely many posterior expectations** for essentially the same cost.

---

## Stage C: the full quotient-of-series theorem

Suggested headline:

```lean
posteriorMean_sub_retainedQuotient_isBoundedInProbability
```

Conclusion:
\[
\frac{
\operatorname{post}_n(\mathrm{obs})-P_n/Q_n
}{
n^{-(U-\lambda)}L_n^{d-m}
}
=O_P(1).
\]

Then:

```lean
tendstoInMeasure_pow_mul_posteriorMean_sub_retainedQuotient
```

with hypothesis
\[
a<U-\lambda.
\]

Equivalently, using your existing “every rate below cutoff” interface, choose an evidence rate \(A\) satisfying
\[
a+\lambda<A<U
\]
and absorb the logarithmic factor using the strict polynomial gap.

### Hypotheses to expose

* the existing atlas and tail packages;
* the joint jet CLT at the required order;
* the actual regularity bound \(R\) sufficient for this \(U\);
* a global box-leading pair \((\lambda,m)\);
* strict positivity on at least one leading chart as required by `boxFaceLimit_pos`;
* bounded measurable observable with the existing smooth pullback hypotheses.

Do not hide the required-order condition behind an unqualified “all \(U\).”

### Carriers

* `evidence_expansion_commonLattice`;
* `evidence_expansion_obs`;
* paired coefficient law and aggregation;
* `empCoeffRect_leading_eq_boxFaceLimit`;
* `boxFaceLimit_pos`;
* the leading spectral isolation argument behind `absSpectralSum_eq_leading`.

---

## Stage D: first inverse-log correction

Define the four aggregated coefficients explicitly:
```lean
A0 n := numeratorCoeff n λ (m - 1)
A1 n := numeratorCoeff n λ (m - 2)
B0 n := denominatorCoeff n λ (m - 1)
B1 n := denominatorCoeff n λ (m - 2)
```
with `2 ≤ m` to avoid misleading natural-number subtraction.

First prove:
\[
N_n/s_n=A_{0,n}+L_n^{-1}A_{1,n}+o_P(L_n^{-1}),
\]
\[
D_n/s_n=B_{0,n}+L_n^{-1}B_{1,n}+o_P(L_n^{-1}).
\]

For this, choose \(U>\lambda\). The finite common lattice gives a positive gap to every retained exponent above \(\lambda\); powers of \(n\) then dominate all the finitely many log powers. Lower log powers at \(\lambda\) are handled directly.

Then prove the stronger approximation:
\[
L_n\left(\operatorname{post}_n-\frac{A_{0,n}}{B_{0,n}}\right)
-
\frac{A_{1,n}B_{0,n}-A_{0,n}B_{1,n}}{B_{0,n}^2}
\longrightarrow_P0.
\]

Suggested declarations:

```lean
posteriorMean_firstLogCorrection_tendstoInMeasure
tendstoInDistribution_posteriorMean_firstLogCorrection
```

The second follows from the paired joint coefficient law, division away from the almost-sure zero set of the limiting denominator, and Slutsky.

**Do not require this limiting correction to be nonzero.** The theorem remains useful when cancellations make it degenerate.

---

## Stage E: optional all-order rational-log block calculus

This is worthwhile after the first correction, not before it.

On the common lattice, set \(x=n^{-1/Q}\). After factoring \(n^{-\lambda}\), group by exponent:
\[
P(x,L)=\sum_jx^jP_j(L),\qquad
Q(x,L)=\sum_jx^jQ_j(L).
\]
Retain \(Q_0(L)\) exactly and define recursively
\[
R_0(L)=\frac{P_0(L)}{Q_0(L)},\qquad
R_j(L)=\frac{P_j(L)-\sum_{i=1}^jQ_i(L)R_{j-i}(L)}{Q_0(L)}.
\]

For Lean, a finite recurrence on evaluated real-valued blocks may be easier than introducing a full formal-series fraction field. `Polynomial.eval` is useful if you want a symbolic logarithmic layer.

The theorem then gives a finite expansion in \(x\), whose coefficients are rational functions of \(L\) and the empirical coefficient vector. This is the clean algebraic answer to item (a).

---

# 3. Corrections and qualifications to the landed-results description

## A. Joint coefficient laws are not a coupling to fixed limiting coefficients

You can say:

> The empirical expansion coefficients converge jointly to Gaussian-functional coefficients.

You generally cannot replace the empirical coefficients inside the expansion by those limiting random variables and retain an in-probability remainder. Weak convergence supplies neither a common coupling nor a convergence rate.

This matters especially for posterior corrections.

## B. Posterior polynomial rates lose the leading evidence exponent

An absolute evidence cutoff \(U\) yields posterior rates below \(U-\lambda\), not below \(U\). The logarithmic normalization changes too.

## C. Continuous extension is an identification gap, not a mathematical ambiguity

`cubeCoeffGenOnClosedJets` is not “only some continuous extension” if realizable smooth jets are dense in the declared closed jet space. It is the **unique continuous extension** of the canonical coefficient functional.

What remains missing is an explicit formula or interpretation—not canonicity.

## D. Aggregation is necessary, but does not alone prove atlas invariance

Your caution about individual chart support is correct. However, even aggregated triangular-array coefficient laws are not intrinsic merely because an evidence expansion exists. The gauge example above is the obstruction.

Frozen-field coefficient uniqueness is the more substantial and defensible theorem.

## E. Separate ordinary resolution output from the analytic probability package

The following are different gaps:

* constructing/refining compact product-sector charts;
* ensuring box images lie in \(K_0\);
* constructing smooth weights;
* obtaining the precise monomial exponent convention;
* analytic \(L^6\) division;
* selecting simultaneous kernel representatives and verifying every derivative datum.

In particular, resolution does not automatically force every coordinate exponent \(k_i\) to be positive. Coordinates transverse to no relevant divisor can have exponent zero. If the grammar interface requires `0 < k α i`, you need either an active-coordinate decomposition or a theorem that integrates/parameters out inactive coordinates—not just a citation to resolution.

## F. “Genuine asymptotic expansion” needs the stochastic qualification

What you have is already a genuine and strong **triangular-array stochastic expansion**. It is not a classical expansion with fixed random coefficients, and the cutoff estimate remains \(O_P\), not automatically \(o_P\).

I would preserve that distinction rather than treat the current rate theorem as somehow provisional.

---

**Bottom line:** land the quotient-of-retained-series theorem and the first inverse-log posterior correction next. They exploit almost every major theorem already built, add a genuinely new posterior asymptotics layer, and force the right mathematical answer to the logarithmic inversion issue. In parallel, scope the conditional \(L^6\)-analytic division constructor: that is the highest-value foundational follow-up.