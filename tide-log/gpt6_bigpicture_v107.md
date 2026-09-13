## Decision

**Accept Ranks 1 and 2, and the first half of Rank 3, at their stated conditional scope.** Authorise:

1. **One normal-location model test**, using the two-sign, finite-angular-resolution representation of the one-dimensional regular model.
2. **Rank 5 only after a short call-site audit** establishes that the Taylor-law-to-`GaussianField` instantiation is missing.
3. A final claim-ledger and wording pass, then stop.

This closes the **bounded formalisation programme**, not the general model-level expected-error theorem. In particular, one conjugate model does not discharge the actual-observable certificates for arbitrary resolved singular models.

My acceptance below is based on the supplied statements and code, not an independent build or repository search.

---

## 1. Acceptance and wording of the landed work

### Rank 1: accepted

The division is now correct:

- distributional convergence and uniform moments are **inputs**;
- expectation transfer for continuous polynomially bounded observables is **proved**;
- the finite-resolution self-normalised quartet requires **no raw-evidence temperature threshold**;
- identification with actual statistical observables is **not inferred**.

Two small wording changes:

1. In the TeX, change
   > “the four Bayes combinations … converge to …”

   to
   > “the **expectations of** the four Bayes combinations … converge to …”.

   The present sentence can be read as random-variable convergence to constants.

2. Say explicitly that \(F(G)\), and the finite-\(n\) compositions, are integrable. This matters because the result is an expectation theorem, not merely a statement using Lean’s totalised integral.

`UniformMoments` is a convenient sufficient interface. There is no need now to weaken it: the proof already shows that a polynomial growth exponent \(k\) only needs the corresponding \(2k\)-moment bound.

### Rank 2: accepted

`expected_quartet_of_L1_transfer` is the right endpoint. Its substantive statistical hypothesis is precisely

\[
\mathbb E|B_{n,j}-\mathcal Q_j(g_n)|\longrightarrow0.
\]

Do not describe this module as proving model-level observable transfer. It proves **expectation transfer from supplied observable-transfer certificates**.

The existing distinction between \(o_{L^1}(1)\) and \(o_P(1)\) is important and should remain.

### Rank 3, first half: accepted

The centred bound is the right primary theorem:

\[
|R|\le \frac16\sup_{0\le t\le1}
       \Pi_t|X-\Pi_tX|^3.
\]

**The raw-third-moment corollary is not required.** Under the corresponding integrability assumptions,

\[
\Pi_t|X-\Pi_tX|^3\le 8\Pi_t|X|^3
\]

is a useful optional convenience, but it adds no necessary capability for the chosen model test. Add it only if it shortens that proof appreciably.

Three precision points:

- Retain the hypothesis that \([0,1]\) lies in the **interior** of the exponential-integrability set. Exponential integrability merely at the endpoints is not the landed hypothesis.
- `tendsto_mul_integral_abs_remainder` is an **envelope theorem**, not a theorem constructing or proving measurability of a supremum over \(t\). Its documentation should foreground measurable, integrable \(S_n\) satisfying the pointwise bound. A supremum is one possible envelope once its regularity is justified.
- The probabilistic reading of the moment ratios as moments of \(\Pi_t\) is mathematically correct. Keep the ledger clear about whether an actual tilted-measure constructor and its integral formula have been formalised, or whether the formal declarations use the displayed normalised ratios.

No reworking of the Taylor proof is requested.

---

## 2. Controlled model test: choose normal location

### Model and scope

Choose **(a)**, with the narrowest clean specification:

\[
X_i\stackrel{\mathrm{iid}}{\sim}N(0,1),\qquad
p(x\mid w)=N(w,1),\qquad
\pi=N(0,a^{-1}),\quad a>0,
\]
and fixed inverse temperature \(\beta>0\).

The excess loss is

\[
f(x,w)=\frac{(x-w)^2-x^2}{2}
      =\frac{w^2}{2}-xw.
\]

Use the tempered posterior based on \(X_1,\ldots,X_n\). Define

\[
d_n=a+\beta n,\qquad
v_n=d_n^{-1},\qquad
m_n=\frac{\beta\sum_{i=1}^nX_i}{d_n}.
\]

Then \(\Pi_n=N(m_n,v_n)\).

This is finite resolution in the relevant sense: **two angular signs, with the radial integral retained**. It is not a finite-support posterior. Neither the divisor model nor an abstract Gaussian-quartet parameter model is preferable here: the former introduces unnecessary geometry, while the latter risks testing only another surrogate rather than an actual posterior predictive loss.

### The tilt and the reusable bound

For prediction, \(X=-f(x,\cdot)\). Thus

\[
\Pi_{n,t,x}(dw)\propto e^{-tf(x,w)}\Pi_n(dw),
\]

and completion of the square gives

\[
v_{n,t}=(d_n+t)^{-1},\qquad
m_{n,t,x}=\frac{d_nm_n+tx}{d_n+t}.
\]

In particular,

\[
m_{n,t,x}-x=\frac{d_n}{d_n+t}(m_n-x).
\]

If \(W=m_{n,t,x}+\sqrt{v_{n,t}}Z\), \(Z\sim N(0,1)\), then

\[
f(x,W)-\Pi_{n,t,x}f(x,\cdot)
=(m_{n,t,x}-x)\sqrt{v_{n,t}}Z
+\frac{v_{n,t}}2(Z^2-1).
\]

That identity is the useful reusable calculation. It yields, for a universal finite constant \(C\), uniformly over \(t\in[0,1]\),

\[
\Pi_{n,t,x}|f-\Pi_{n,t,x}f|^3
\le
S_n(D_n,x)
:=
C\left[
d_n^{-3/2}(|m_n|^3+|x|^3)+d_n^{-3}
\right].
\]

**Prove an upper bound, not an exact absolute-third-moment formula.** Gaussian moments through order six suffice. The exact absolute moment of this quadratic polynomial is unnecessary.

Also prove the exponential-integrability-neighbourhood condition. Here it follows from positivity of \(d_n+t\); there is an open interval containing \([0,1]\) on which the Gaussian quadratic integral is finite.

### Target theorem

The primary target should package **both generalisation and training certificates**:

\[
n\,\mathbb E_{D_n}\mathbb E_{X_*}S_n(D_n,X_*)\to0,
\]

where \(X_*\sim N(0,1)\) is independent of \(D_n\), and

\[
n\,\mathbb E_{D_n}
 \left[\frac1n\sum_{i=1}^n S_n(D_n,X_i)\right]\to0.
\]

Consequently, writing
\[
R_n(D_n,x)=
\operatorname{predictiveRemainder}(-f(x,\cdot),\Pi_n),
\]
prove

\[
n\,\mathbb E_{D_n}\mathbb E_{X_*}|R_n(D_n,X_*)|\to0,
\]
and
\[
n\,\mathbb E_{D_n}
 \left[\frac1n\sum_{i=1}^n|R_n(D_n,X_i)|\right]\to0.
\]

A schematic declaration name is:

```lean
normalLocation_predictive_remainder_L1
```

Its hypotheses should be only:

- \(a>0\), \(\beta>0\);
- a measurable i.i.d. standard-normal training sequence;
- an independent standard-normal fresh point, if the fresh-point version uses a common sample space;
- the explicit definitions of the loss and tempered posterior.

Posterior identification, moment bounds, remainder measurability and integrability should be **conclusions or internal lemmas**, not unexplained certificate hypotheses at the final model theorem.

Work with \(n\ge1\), or index sample size by \(n+1\). Do not let the \(n=0\) convention dominate the proof.

### Which expectation over \(x\)?

**Both, separately.**

- Generalisation: integrate \(x\) against the population law, independently of the training data.
- Training: take the empirical average over the very sample defining the posterior.

A fresh-point certificate does **not** automatically imply the training certificate. In this model, however, the same pathwise envelope proves both. No independence between \(m_n\) and \(X_i\) is needed to integrate the separated bound \(|m_n|^3+|X_i|^3\).

Also, “\(O(n^{-3/2})\) for fixed \(x\)” is not the endpoint. The proof needs the random-data and \(x\)-integrated envelope.

### Reusable declarations

First inspect the exact existing signatures. Reuse, rather than restate:

- `EffectiveTemperature.sum_normalLocation`;
- `normalLocation_standard_form`;
- `neg_zetaEmp_normalLocation`;
- `variance_phase_normalLocation`.

The proposed new declarations are, schematically:

1. `normalLocation_posterior_eq_gaussian`
2. `normalLocation_tilt_eq_gaussian`
3. `normalLocation_mem_interior_integrableExpSet`
4. `normalLocation_centred_loss_eq`
5. `normalLocation_tiltAbsThird_le`
6. `normalLocation_predictive_remainder_L1`

A small Gaussian quadratic-polynomial moment bound is reusable. A generic conjugate-family framework is not authorised.

### Feeding `expected_quartet_of_L1_transfer`

Use the endpoint’s order, which is **Gibbs generalisation, Gibbs training, Bayes generalisation, Bayes training**:

\[
\begin{aligned}
B_{n,0}&=n\,\mathbb E_x\Pi_n[f(x,w)],\\
B_{n,1}&=n\,\frac1n\sum_i\Pi_n[f(X_i,w)],\\
B_{n,2}&=n\,\mathbb E_x[-\log\Pi_n(e^{-f(x,w)})],\\
B_{n,3}&=n\,\frac1n\sum_i[-\log\Pi_n(e^{-f(X_i,w)})].
\end{aligned}
\]

These are excess errors relative to \(w=0\); the baseline subtraction must be explicit.

Let \(Z_n=n^{-1/2}\sum_iX_i\). The expected two-sign quartet identification, under the usual \(w=\pm\sqrt{2r}\) radial convention, is

\[
\lambda=\tfrac12,\qquad
g_n=(\sqrt2Z_n,-\sqrt2Z_n),\qquad
b=
\begin{pmatrix}2&-2\\-2&2\end{pmatrix},
\]
with equal positive sign weights. **Verify this normalisation against the actual quartet definitions before coding the adapter.**

The corresponding combinations should simplify to

\[
\left(
\frac{\beta^{-1}+Z_n^2}{2},\
\frac{\beta^{-1}-Z_n^2}{2},\
\frac{Z_n^2}{2},\
-\frac{Z_n^2}{2}
\right).
\]

The \(L^1\) proof has three distinct ingredients:

1. **Gibbs transfer**, from the exact posterior formulas:
   \[
   G_g=\frac{m_n^2+v_n}{2},\qquad
   G_t=\frac{m_n^2+v_n}{2}-m_n\bar X_n.
   \]

2. **Variance-correction transfer**, using
   \[
   \operatorname{Var}_{\Pi_n}(f(x,w))
   =v_n(m_n-x)^2+\frac{v_n^2}{2}.
   \]
   Both its population and empirical averages, multiplied by \(n\), converge in \(L^1\) to \(1/\beta\). The training case also uses \(L^1\) convergence of the empirical second moment.

3. **Predictive remainder transfer**, from the two certificates above and the integral/finite-sum triangle inequalities.

Thus the remainder certificate is **one component**, not the whole actual-observable transfer.

For this test, \(Z_n\) is already exactly standard normal for every \(n\ge1\). Therefore the phase law and uniform moments can be discharged directly from Gaussian facts; the general sub-Gaussian-to-uniform-moments bridge remains unnecessary.

After verifying the quartet identification, target a thin corollary:

```lean
normalLocation_expected_quartet
```

with \(\lambda=\nu=1/2\), yielding

\[
\left(
\frac{1+\beta^{-1}}2,\
\frac{\beta^{-1}-1}2,\
\frac12,\
-\frac12
\right).
\]

### Gate and stopping rule

**Gate:** establish the exact posterior, tilt, and two-sign normalisation on paper and in a short signature sheet. Confirm that the existing Gaussian API can support the needed moments and integrals without a new probability infrastructure project.

**Stop after:** the two remainder certificates and the thin actual-quartet instantiation, provided the latter remains this elementary normal-location calculation.

If the quartet adapter exposes a substantive mismatch, stop with the model remainder theorem and document the missing identification. Do not redefine the actual \(B_{n,j}\) to make the endpoint tautological.

No divisor model, general singular posterior, non-Gaussian data, multidimensional extension, or continuum-resolution limit in this rank.

---

## 3. Rank 5: Taylor law to compact Gaussian field

### What the supplied constructor list establishes

It establishes that generic constructors exist. It does **not** establish that one has been applied to the Taylor-data limit law.

I cannot certify either presence or absence of that instantiation from the excerpts. The audit should search:

- call sites of `ofIsGaussian` and `ofIsGaussianCertificates`;
- occurrences of the concrete Taylor-limit-law declaration in compact-base modules;
- any bounded coefficient-synthesis/evaluation map and its law-identification theorem.

**Do not rebuild a CLT or a tail theorem.** G0 has settled that part.

### Target if missing

Let \(L\) be the constructed law on the relevant \(\ell^1\) coefficient space. Build a bounded linear synthesis map

\[
T:\ell^1(I)\longrightarrow C(K,\mathbb R),
\qquad
T(a)(x)=\sum_{r\in I}a_r\phi_r(x).
\]

Then instantiate the existing constructor to obtain, schematically,

```lean
GaussianField.ofL1TaylorLimit
```

on the coefficient probability space, with field \(T\) and covariance equal to the certified kernel.

Equivalently, first form \(L.map\,T\) on \(C(K)\) and use the identity random field. **Only one representation is necessary.** In particular, constructing a separate pushforward measure is not mandatory if `GaussianField` can use \(\Omega=\ell^1(I)\), \(P=L\), \(G=T\).

### What continuity requires

A clean sufficient condition is

\[
\phi_r\in C(K),\qquad
\sup_r\|\phi_r\|_\infty\le M<\infty.
\]

Then

\[
\|T(a)\|_\infty\le M\|a\|_1,
\]

so the defining series converges uniformly and \(T\) is bounded linear.

Important distinctions:

- Continuity of every \(\phi_r\), even on compact \(K\), does **not** give a bound uniform in \(r\).
- Pointwise summability alone does **not** prove continuity of the summed field.
- If the coefficient certificate uses weights, those weights must be reflected in the \(\ell^1\) norm or absorbed into the basis functions before asserting this bound.

### Gaussian and covariance obligations

The adapter must consume or derive:

1. measurability of \(T\), supplied by continuity under the appropriate Borel structures;
2. Gaussianity of every finite evaluation vector;
3. zero means and the specified covariance kernel, as required by the chosen constructor.

**Individual Gaussian coordinate marginals are not enough for item 2.** Check that the coordinate certificate supplies joint finite-dimensional Gaussian laws, or Gaussianity of all finite linear combinations. From those, truncation and the \(\ell^1\)-continuous synthesis map give the required Gaussian evaluation laws.

For mean/covariance identification, use the existing tail/moment consequences to justify limiting integrals. For example, \(\mathbb E_L\|a\|_1^2<\infty\), together with bounded \(T\), supplies a straightforward domination route. Do not silently interchange infinite covariance sums.

The target should expose the actual certified chart/basis compatibility, not replace it by an unrelated covariance kernel.

**Rank-5 stopping point:** one adapter, a field-map simp lemma, the needed covariance identification, and one existing compact-base consumer instantiated with it. No new compactness, Fernique or CLT framework.

---

## 4. Closure of the note programme

### What can be declared closed

After the controlled test and Rank 5 if missing, the agreed stopping-point programme is closed if the ledger records:

- the coordinate-to-limit-law construction and its tail bound;
- finite-resolution quartet expectation transfer;
- the conditional actual-observable expectation endpoint;
- the predictive Taylor theorem;
- one actual-model discharge, with fresh and training expectations distinguished;
- the compact-field adapter where needed.

Use wording such as:

> The formalisation programme is complete at the stated interface boundary. General expected-error conclusions remain conditional on model-to-chart identification and actual-observable \(L^1\) transfer certificates; these certificates have been discharged in the specified normal-location test only.

### Explicit non-claims to retain

Unless independently established elsewhere and cited precisely:

- no general discharge of actual scaled normalised observable transfer;
- no general predictive-remainder certificate for resolved singular models;
- no replacement of \(L^1\) transfer by bare convergence in probability;
- no formal general sub-Gaussian-to-`UniformMoments` bridge;
- no finite-resolution-to-continuum expected-quartet passage;
- no automatic model-to-chart coefficient identification;
- no inference of comparison or statistical transport merely from resolution existence;
- no removal of raw-evidence or closure-endpoint temperature/moment conditions by the self-normalised theorem;
- no unconditional strict inequality \(\beta_{\mathrm{eff}}<\beta\).

After the model test, replace “its discharge in a statistical model is not formalised” by “its general discharge is not formalised; the specified normal-location case is formalised.”

### Final wording pass

Check every headline, proposition dot, interface row and concluding paragraph against:

1. **Constructed versus consumed:** especially the limit law, chart data, covariance and remainder certificates.
2. **Mode of convergence:** distribution, probability, \(L^1\), or convergence of expectations.
3. **Scope:** fixed finite resolution versus compact base versus a resolution limit.
4. **Observable identity:** actual excess error versus a quartet surrogate; \(n\)-scaling and the four-entry order.
5. **Expectation space:** training data, independent test point, empirical average, posterior or tilt.
6. **Analytic side conditions:** integrability, measurability, positive normalisers, exponential-integrability neighbourhoods.
7. **Parameters:** all positivity conditions and every threshold retained at the interface where it is used.
8. **Formal coverage:** no dot over a model discharge, supremum-measurability assertion, or adapter instantiation that remains only an explanation.
9. **Earlier repairs:** preserve the extended-integral annealed identity, the definition of \(Q(g)\), “at most 1”, and the conditional strictness language.
10. **Dependency audit:** build the final endpoints and check their axiom reports under the library’s established axiom-clean criterion.

The strategic point is to finish with a **closed, accurately delimited chain of interfaces and one genuine statistical test**, not to turn that test into an implicit claim of a general singular-learning theorem.
