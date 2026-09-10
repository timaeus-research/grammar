## Executive decision

**(A)** There are two worthwhile paper-facing units available now: the sampling-model identification of \(N=n\), with a sign audit, and the tangential/normal box bookkeeping. A positive-gap remainder lemma is also available, but **it does not construct the missing analytic localisation**. I would not launch another resolution-to-standard-form campaign before the analytic-unit interface arrives.

**(B)** Make the companion note principally about **Gaussian averaging and self-normalised Gaussian posterior identities**, not a purported convergent diagrammatic calculus.

The right flagship result is your candidate (4):

> For a finite positive spatial measure and a centred Gaussian vector, the Schwinger–Dyson and Gaussian-IBP identities hold, and all the normalised quantities involved are integrable for every \(\beta>0\).

This is accessible without Isserlis or Malliavin calculus. Its continuum extension is also accessible by discretisation under explicit compactness, continuity, and Gaussian random-element hypotheses.

Three corrections are particularly important:

1. **The divisor variance \(2\) needs \(K=\phi^2\), not merely \(\phi\to0\).**
2. **Bilocal finiteness depends on the sign of the covariance, not \(|b|\).** Absolute convergence of the cross-pairing series does depend on \(|b|\).
3. **Leading posterior ratios are generally random, already at order \(1\).** Averaging the numerator and denominator separately does not remove that randomness.

I am assessing the interfaces supplied in the question, not reporting an independent checkout or verification of the repository.

---

# A. What can be done now?

## A1. Sampling-model bridge, including \(N=n\) and the phase sign

This is a genuine remaining interface theorem, independent of resolution units and complexification.

Suppose
\[
f(x,u)=\phi(u)a(x,u),\qquad
\mathbb E a(X,u)=\phi(u),
\]
and, for \(n>0\), define
\[
\zeta_n(u)=n^{-1/2}\sum_{i=1}^n
       \bigl(a(X_i,u)-\mathbb E a(X,u)\bigr).
\]
Then, identically for every dataset,
\[
K_n(u)=\frac1n\sum_i f(X_i,u)
      =\phi(u)^2+\frac{\phi(u)}{\sqrt n}\zeta_n(u),
\]
and
\[
e^{-\beta\sum_i f(X_i,u)}
=e^{-\beta n\phi(u)^2-\beta\sqrt n\,\phi(u)\zeta_n(u)}.
\]

Thus the standard integral with **positive** fluctuation term uses
\[
\xi_n=-\zeta_n,\qquad N=n.
\]

On the interfaces you supplied, the note’s \(\xi_n\) and grammar’s `dataPhase_sampleDatum` have opposite signs **if their \(a\)'s denote the same likelihood-ratio coefficient**. Audit this explicitly. A centred Gaussian limit has the same law under simultaneous global negation, but this does not repair a finite-sample identity.

**Non-claim:** this identifies the asymptotic scale in this sampling construction. It does not establish an unconditional equality between two independently introduced parameters called \(N\) and \(n\).

## A2. Tangential/normal weighted-box decomposition

Do the Astra #55 bookkeeping unit: coordinate permutation/reindexing, product measures, monomial weights, face restriction, and the compatibility of the existing `TanCertificate` interface with that decomposition.

This is low-risk and actually closes a stated paper-facing gap.

## A3. Positive-gap remainder, if not already subsumed

For compact \(W\), continuous \(K\ge0\), and an open \(U\supseteq K^{-1}(0)\), compactness gives
\[
K\ge\delta>0\quad\text{on }W\setminus U.
\]
For integrable \(g\),
\[
\left|\int_{W\setminus U}g\,e^{-\beta NK}\right|
\le e^{-\beta N\delta}\int_{W\setminus U}|g|.
\]

For the empirical standard exponent and \(\|\xi\|_\infty\le R\),
\[
-\beta NK+\beta\sqrt{NK}\,\xi
\le-\frac{\beta NK}{2}+\frac{\beta R^2}{2},
\]
hence a uniform exponentially small remainder.

**Crucial limitation:** analytic charts in a `ResolutionCover` do not themselves supply an exact analytic decomposition of the integral over \(U\). Nor does this lemma manufacture analytic partition functions. In particular, nontrivial compactly supported analytic cutoffs are not available on connected analytic charts.

Call this a **positive-gap remainder theorem conditional on a chosen core**, not “the analytic-core decomposition theorem”.

Real analyticity alone also does not supply Hypothesis I’s joint holomorphic extension and uniform Cauchy envelope. Particular real-variable consequences can be proved under explicit derivative/envelope hypotheses, but they should not be advertised as discharging complexification.

---

# B. Mathematical corrections and exact targets

Throughout, use one normalisation:
\[
S_\mu(a)
=\operatorname{fluctuation}(\beta,\mu,a)
=\int_0^\infty y^{\mu-1}e^{-\beta y+\beta a\sqrt y}\,dy,
\qquad \beta,\mu>0.
\]

Write \(T=\sqrt y\) when discussing the radial posterior. Then
\[
S_\mu(a)=2J_{2\mu}(a),
\qquad
S_\mu(0)=\frac{\Gamma(\mu)}{\beta^\mu}.
\]

The note’s earlier half-line quadratic integral is \(J_{2\mu}=S_\mu/2\). Ratios are unchanged; raw \(q\)-point functions acquire a factor \(2^q\).

## B1. Variance normalisation: true with the missing hypothesis

The robust theorem is slightly more general than the proposed one.

Assume
\[
\mathbb E e^{-\phi a_\phi}=1,\qquad
\mathbb E[\phi a_\phi]=\phi^2 h_\phi.
\]
For \(\phi\ne0\), Taylor’s theorem gives
\[
\boxed{
\left|\mathbb E[a_\phi^2]-2h_\phi\right|
\le
\frac{|\phi|}{3}
\mathbb E\!\left[|a_\phi|^3e^{|\phi a_\phi|}\right].
}
\]
Indeed,
\[
|e^{-z}-1+z-z^2/2|\le |z|^3e^{|z|}/6.
\]

Consequently, a uniform bound on the displayed third-moment envelope implies
\[
\mathbb E[a_\phi^2]=2h_\phi+O(|\phi|).
\]

At a divisor point \(u_0\), assume additionally:

- \(u_0\) is approached by points with \(\phi(u)\ne0\);
- \(a_u\to a_{u_0}\) in \(L^2\);
- \(h_u\to h_{u_0}\).

Then
\[
\mathbb E[a_{u_0}^2]=2h_{u_0}.
\]
The corresponding first-moment continuity gives \(\mathbb E a_{u_0}=0\).

Therefore, in the **normalised standard form**
\[
K(u)=\phi(u)^2,
\]
the covariance diagonal on the divisor is exactly \(2\).

But the statement with arbitrary \(K=\mathbb E f\) and merely \(\phi\to0\) is false. For example, with \(Z\sim N(0,1)\),
\[
a_\phi=\sigma Z+\frac{\phi\sigma^2}{2}
\]
satisfies \(\mathbb E e^{-\phi a_\phi}=1\), while
\[
\mathbb E[a_\phi^2]\longrightarrow \sigma^2.
\]

Two further qualifications:

- Pointwise real analyticity does not establish the needed integrable envelopes or \(L^2\)-continuity.
- For \(f=\log q-\log p\), the identity \(\mathbb E_qe^{-f}=1\) needs the relevant support/absolute-continuity condition. Otherwise the integral only sees the support of \(q\).

I would prove this elementary theorem directly rather than make the Lean statement depend on an unchecked attribution to a particular numbered theorem in Watanabe.

## B2. \(Q=0,1,2\): exact closed forms

Let \((Y,X_1,X_2)\) be jointly centred Gaussian and put
\[
c=\mathbb E Y^2,\quad
d_i=\mathbb E[X_iY],\quad
e=\mathbb E[X_1X_2],\quad
\delta=1-\frac{\beta c}{2}.
\]
Assume \(\delta>0\). Then all the following are absolutely integrable:
\[
\boxed{\mathbb E S_\mu(Y)=\frac{\Gamma(\mu)}{(\beta\delta)^\mu},}
\]
\[
\boxed{
\mathbb E[X_1S_\mu(Y)]
=\frac{\beta d_1\Gamma(\mu+\tfrac12)}
       {(\beta\delta)^{\mu+1/2}},
}
\]
\[
\boxed{
\mathbb E[X_1X_2S_\mu(Y)]
=
\frac{e\Gamma(\mu)}{(\beta\delta)^\mu}
+
\frac{\beta^2d_1d_2\Gamma(\mu+1)}
     {(\beta\delta)^{\mu+1}}.
}
\]

In particular,
\[
\mathbb E[X_1S_{\lambda+1/2}(Y)]
=
\frac{d_1\Gamma(\lambda+1)}
     {\beta^\lambda\delta^{\lambda+1}},
\]
and
\[
\mathbb E[X_1X_2S_{\lambda+1}(Y)]
=
\frac{e\Gamma(\lambda+1)}
     {\beta^{\lambda+1}\delta^{\lambda+1}}
+
\frac{d_1d_2\Gamma(\lambda+2)}
     {\beta^\lambda\delta^{\lambda+2}}.
\]

**The note’s `eq:Q1_expansion` is correct in its earlier half-normalisation**, with \(c=2\) and \(\beta<1\). It needs multiplication by \(2\) when converted to `fluctuation`.

No Isserlis theorem is necessary. Two routes are available:

- Gaussian regression, splitting out \(c=0\);
- the tilted Gaussian identities
  \[
  \mathbb E[X_i e^{\theta Y}]
  =\theta d_i e^{c\theta^2/2},
  \]
  \[
  \mathbb E[X_1X_2e^{\theta Y}]
  =(e+\theta^2d_1d_2)e^{c\theta^2/2}.
  \]

The second route avoids division by \(c\). Alternatively, use the finite-dimensional Stein theorem developed below.

For \(Q=0\), reuse the existing ENNReal dichotomy. Do not state an ordinary real integral equals \(+\infty\): Lean’s nonintegrable Bochner integral is not an extended expectation.

## B3. Bilocal integral, series, and the actual thresholds

Let \((X,Y)\) be centred Gaussian with covariance data \(c,c',b\). Define
\[
A=\beta(1-\beta c/2),\qquad
B=\beta(1-\beta c'/2),\qquad
H=\beta^2b.
\]

Tonelli and the joint MGF give the extended-valued identity
\[
\boxed{
\mathbb E_+[S_\lambda(X)S_\lambda(Y)]
=
\int_0^\infty\!\!\int_0^\infty
t^{\lambda-1}s^{\lambda-1}
e^{-At-Bs+H\sqrt{ts}}\,dt\,ds.
}
\]

### Finiteness is an orthant question, not positive-definiteness on all of \(\mathbb R^2\)

For the equal indices requested here, the exact classification is:
\[
\boxed{
A>0,\ B>0,\quad
\begin{cases}
H<2\sqrt{AB},&\text{finite},\\
H=2\sqrt{AB},&\text{finite iff }\lambda<1/4,\\
H>2\sqrt{AB},&\text{infinite}.
\end{cases}
}
\]
If \(A\le0\) or \(B\le0\), the equal-index integral is infinite.

In particular, negative \(b\) helps integrability. Replacing \(b\) by \(|b|\) gives a sufficient strict condition, not the exact finiteness criterion.

For \(c=c'=2\):

- \(b\le0\): finite exactly when \(0<\beta<1\);
- \(b>0\): finite for
  \[
  \beta<\frac1{1+b/2},
  \]
  infinite above it, and finite at equality iff \(\lambda<1/4\).

At \(b=2\), the critical value is \(\beta=1/2\), **but equality is not always divergent**.

To see the endpoint, set \(t=x^2,s=y^2\). At criticality, the exponent vanishes along an interior ray. Integration in the transverse Gaussian direction leaves a tail proportional to
\[
\int^\infty R^{4\lambda-2}\,dR,
\]
which converges precisely for \(\lambda<1/4\).

### Cross-pairing series

When
\[
A,B>0,\qquad |H|<2\sqrt{AB},
\]
absolute interchange gives
\[
\boxed{
\mathbb E[S_\lambda(X)S_\lambda(Y)]
=
\sum_{r=0}^\infty
\frac{H^r}{r!}
\frac{\Gamma(\lambda+r/2)^2}
     {A^{\lambda+r/2}B^{\lambda+r/2}}.
}
\]

For \(c=c'=2\), this becomes
\[
\frac1{\beta^{2\lambda}}
\sum_{r=0}^\infty
\frac{\Gamma(\lambda+r/2)^2}{r!}
(\beta b)^r(1-\beta)^{-(2\lambda+r)}.
\]

Thus `eq:bilocal_resummed` has the correct coefficients in the old half-normalisation. Its main defect is the missing domain qualification, not an incorrect resummation coefficient.

At the absolute-convergence boundary, the series is absolutely convergent iff \(\lambda<1/4\). At the negative boundary it also has a conditionally convergent range \(1/4\le\lambda<3/4\). Do not make that signed boundary analysis a prerequisite for the first Lean theorem.

For negative \(b\), the integral can remain finite well outside the series’ radius of convergence.

### Connected integral and the alleged scaling discrepancy

In unscaled `fluctuation` variables, with \(c=c'=2\),
\[
\operatorname{Cov}(S_\lambda(X),S_\lambda(Y))
=
\iint t^{\lambda-1}s^{\lambda-1}
e^{-\beta(1-\beta)(t+s)}
\bigl(e^{\beta^2b\sqrt{ts}}-1\bigr)\,dt\,ds,
\]
under sufficient integrability.

After rescaling \(t,s\) by \(\beta\), this is
\[
\frac1{\beta^{2\lambda}}
\iint t^{\lambda-1}s^{\lambda-1}
e^{-(1-\beta)(t+s)}
\bigl(e^{\beta b\sqrt{ts}}-1\bigr)\,dt\,ds.
\]

The note’s displayed integral with prefactor \(1/(4\beta^{2\lambda})\) is therefore **correct for its old half-normalisation and rescaled integration variables**. Label the change of variables; do not “correct” it into a different formula without adjusting the prefactor.

### \(p\)-th moments

For \(Y\sim N(0,c)\), \(c>0\), and integer \(p\ge1\):
\[
\mathbb E[S_\lambda(Y)^p]<\infty
\quad\text{if }\beta cp<2,
\]
and it is infinite if \(\beta cp>2\).

At equality,
\[
\boxed{
\mathbb E[S_\lambda(Y)^p]<\infty
\iff
\lambda<\frac{p-1}{2p}.
}
\]

This follows from
\[
S_\lambda(a)\sim
2\sqrt{\frac\pi\beta}
\left(\frac a2\right)^{2\lambda-1}
e^{\beta a^2/4}
\qquad(a\to+\infty).
\]

So \(\beta<1/p\) for \(c=2\) is the correct **strict subcritical domain**, not a complete iff statement including its boundary. Nor is \(1/p\) automatically the exact threshold for every spatially integrated \(D(G)\).

## B4. Self-normalisation: elementary bounds suffice

Define
\[
R_1(a)=\frac{S_{\lambda+1/2}(a)}{S_\lambda(a)},\qquad
R_2(a)=\frac{S_{\lambda+1}(a)}{S_\lambda(a)}.
\]
Positivity, posterior Cauchy–Schwarz, and the existing Weber identity give
\[
R_1(a)^2\le R_2(a),\qquad
R_2(a)=\frac\lambda\beta+\frac a2R_1(a).
\]

Writing \(a_+=\max(a,0)\), one obtains, without asymptotic analysis,
\[
\boxed{
0<R_2(a)\le \frac{2\lambda}{\beta}+\frac{a_+^2}{4},
\qquad
0<R_1(a)\le
\sqrt{\frac{2\lambda}{\beta}+\frac{a_+^2}{4}}.
}
\]

These are enough for the quartet and interpolation.

There is also a useful polynomial lower bound. For \(R\ge0\),
\[
S_\lambda(-R)
\ge \frac{e^{-2\beta}}{\lambda}(1+R)^{-2\lambda},
\]
by restricting the integral to \(0<y<(1+R)^{-2}\).

If a positive spatial measure has mass \(M>0\), then
\[
D(g)\ge
M\frac{e^{-2\beta}}{\lambda}(1+\|g\|_\infty)^{-2\lambda}.
\]
Together with the existing Gaussian upper bound, this gives
\[
|\log D(g)|\le C(1+\|g\|_\infty^2).
\]

Consequences:

- quartet quantities need only suitable polynomial moments of the field norm;
- negative moments of \(D\) follow from polynomial moments of that norm;
- no Borell–TIS estimate is needed here;
- no limiting argument \(\beta\uparrow1\) is needed.

## B5. Finite-dimensional quartet: the flagship theorem

Let \(m>0\), \(\rho_i>0\), and \(G\) be centred Gaussian with PSD covariance \(b\), with \(b_{ii}=c\). Define \(D,M_1,M_2,H_G,V\) as in the question, with
\[
H_G=\langle GT\rangle_G.
\]

Then, for every \(\beta,\lambda>0\),

1. \(D(g)>0\) for every \(g\);
2. pointwise,
   \[
   M_2(g)=\lambda/\beta+H_g/2;
   \]
3. \(V(g)\ge0\);
4. all quantities below are integrable;
5.
   \[
   \boxed{\mathbb E H_G=\beta\mathbb E V(G);}
   \]
6. defining \(\nu=\tfrac12\mathbb E H_G\),
   \[
   \boxed{
   \nu\ge0,\qquad
   \mathbb E V=2\nu/\beta,\qquad
   \mathbb E M_2=\lambda/\beta+\nu.
   }
   \]

For positivity, factor \(b_{ij}=\langle h_i,h_j\rangle\). Under the marked posterior on \((i,T)\),
\[
V(g)
=
\mathbb E_{\pi_g}\|Th_i\|^2
-\left\|\mathbb E_{\pi_g}[Th_i]\right\|^2.
\]
In particular,
\[
0\le V(g)\le cM_2(g).
\]

For IBP, set
\[
F_i(g)=\frac{\rho_iS_{\lambda+1/2}(g_i)}{D(g)}.
\]
Then
\[
\partial_jF_i
=
\beta\delta_{ij}
\frac{\rho_iS_{\lambda+1}(g_i)}{D(g)}
-\beta F_iF_j.
\]
Apply
\[
\mathbb E[G_iF_i(G)]
=\sum_jb_{ij}\mathbb E[\partial_jF_i(G)]
\]
and sum over \(i\).

The bounds above make \(F_i\) and its first derivatives polynomially bounded. This avoids proving elaborate sharp asymptotics.

**Non-claim:** these are Gaussian-limit posterior identities. Identifying this \(\nu\) with the statistical singular fluctuation, and deriving the four expected finite-sample error expansions, still requires the appropriate posterior transfer and predictive Taylor-remainder/UI theorems.

---

# C. Ranked Lean programme: ten units maximum

The ranking below keeps the central theorem early. Units 2–3 are its only genuinely new Gaussian infrastructure.

## 1. Normalisation adapters and deterministic self-normalisation

**Deliverables**

- \(S_\mu=2J_{2\mu}\);
- strict positivity of \(S_\mu\);
- \(R_1^2\le R_2\);
- the explicit polynomial bounds above;
- positive finite-mixture bounds;
- polynomial lower bound for \(D\), and quadratic bound for \(|\log D|\).

**Inputs:** existing `fluctuation_integrableOn`, `fluctuation_le_gaussian`, Weber recurrence, posterior laws, Cauchy–Schwarz for integrals.

**Trap:** prove integrability and denominator positivity before quotient manipulations. Keep signed Taylor-leaf coefficients separate from positive posterior weights.

## 2. Scalar Gaussian Stein identity

First prove a deliberately strong, usable interface:

For \(Z\sim N(0,1)\), \(F\in C^1(\mathbb R)\), and polynomial bounds on \(F,F'\),
\[
\mathbb E[ZF(Z)]=\mathbb E[F'(Z)].
\]

Then obtain the arbitrary-variance version, treating zero variance separately.

**Inputs:** `gaussianReal`, its density, real differentiation, interval integration by parts, Gaussian moments.

**Proof strategy:** integrate on \([-R,R]\), prove the boundary term tends to zero, pass to the limit.

**Trap:** the note’s assumption \(\mathbb E|ZF'(Z)|<\infty\) is not the right standalone theorem interface. Use explicit regularity and integrability/boundary hypotheses, or polynomial growth.

## 3. Finite-dimensional Stein, including degenerate laws

Prove first for
\[
G=AZ,\qquad Z\text{ a finite vector of independent standard Gaussians}.
\]
Then
\[
\mathbb E[G_iF(G)]
=\sum_j(AA^\mathsf T)_{ij}\mathbb E[\partial_jF(G)].
\]

Package a covariance-law adapter for arbitrary centred finite-dimensional Gaussian laws.

**Inputs:** `stdGaussian`, `multivariateGaussian`, `charFun_multivariateGaussian`, `covariance_eval_multivariateGaussian`, product integration and the chain rule.

**Trap:** do not assume invertible covariance. A PSD square-root/law-identification adapter is the correct route. If that adapter is unexpectedly expensive, retain the explicit \(AZ\) theorem first; do not insert nondegeneracy into the mathematical headline.

## 4. Finite-dimensional self-normalised Gaussian quartet

Formalise B5, including \(V\ge0\), integrability for every \(\beta>0\), and the three boxed expected identities.

Add the elementary algebra assembling the four coefficients **conditional on** the statistical reductions:
\[
\frac\lambda\beta\pm\nu,\qquad
\frac{\lambda-\nu}{\beta}\pm\nu.
\]

**Inputs:** units 1–3, existing fluctuation derivatives.

**Non-claim:** no theorem yet about the actual expected Bayes errors merely from this finite Gaussian calculation.

## 5. Divisor variance from likelihood normalisation

Prove the explicit Taylor-remainder inequality in B1, followed by:

- uniform-envelope \(O(|\phi|)\) corollary;
- \(L^2\)-continuous extension to divisor points;
- \(K=\phi^2\Rightarrow c=2\);
- \(K=\phi^2h\Rightarrow c=2h\).

**Inputs:** elementary exponential Taylor estimates, integrals, \(L^2\)/`MemLp` continuity.

**Trap:** formulate the theorem without analyticity first. Analytic sampling models provide a separate adapter supplying the envelopes.

## 6. Gaussian insertion formulas \(Q=0,1,2\)

Formalise B2 in the \(\delta>0\) domain.

Reuse `headline_gaussian_dichotomy` for \(Q=0\); do not reproduce its proof as a Wick expansion.

For \(Q=1,2\), use regression or tilted MGF identities. The polynomial-growth Stein interface of unit 3 does **not directly apply** to \(S_\mu\), which grows exponentially. Either:

- prove the needed integrable-growth extension of Stein; or
- use cutoffs with subcritical domination; or
- use regression/MGF directly.

**Trap:** this growth distinction matters. Do not silently apply the normalised-quotient Stein theorem to an unnormalised fluctuation function.

## 7. Bilocal MGF integral and the absolutely convergent series

First deliver:

- the ENNReal double-integral identity;
- finiteness for \(A,B>0\) and \(H<2\sqrt{AB}\);
- the series in the strict absolute domain \(|H|<2\sqrt{AB}\);
- the connected integral there;
- divergence in the strictly supercritical positive-cross-term region.

**Inputs:** joint Gaussian MGF, Tonelli/Fubini, exponential series, Gamma integrals.

**Bound the unit:** critical-boundary classification and the complete \(p\)-moment endpoint theorem may remain mathematically proved but not Lean-formalised in this campaign. They are not needed by the quartet.

**Trap:** distinguish signed series convergence from integrability of the positive original integrand.

## 8. Finite-dimensional covariance interpolation

Let
\[
D_s(g)=\sum_i\rho_iS_\lambda(\sqrt s\,g_i),
\]
and let \(V_s(g)\) be the B5 variance expression evaluated at \(\sqrt s\,g\), using the original covariance \(b\).

Prove
\[
L(s)=\mathbb E\log D_s(G)
\]
is continuous on \([0,1]\), differentiable on \((0,1)\), and
\[
\boxed{L'(s)=\frac{\beta^2}{2}\mathbb E[V_s(G)].}
\]
Then
\[
\boxed{
\mathbb E\log D(G)
=
\log\!\left(\sum_i\rho_iS_\lambda(0)\right)
+\frac{\beta^2}{2}\int_0^1\mathbb E[V_s(G)]\,ds.
}
\]

Also obtain monotonicity and
\[
\mathbb E\log D(G)\ge\log D(0).
\]

**Trap:** the pathwise derivative contains \(1/\sqrt s\). Prove the identity on \(s>0\), then use continuity and uniform polynomial bounds at \(s=0\). Do not assert pathwise differentiability there.

## 9. Compact-base continuum transfer by discretisation

Assume:

- \(K\) is compact metrizable;
- \(\rho\) is a finite positive Borel measure with positive mass;
- \(G\) is a measurable \(C(K,\mathbb R)\)-valued centred Gaussian random element;
- the covariance kernel \(b\) is continuous, with \(b(w,w)=c\).

Approximate \(\rho\) by finite positive atomic measures. Prove pathwise convergence of \(D,M_2,H,V,\log D\), and then convergence of expectations using bounds depending only on \(\|G\|_\infty\).

Transfer units 4 and 8.

**Inputs:** `ContinuousMap`, finite-measure integration, `IsGaussian`/`HasGaussianLaw`, `IsGaussianProcess`, Fernique’s `exists_integrable_exp_sq`.

**Trap:** continuous sample paths plus finite-dimensional Gaussianity must be connected to a measurable Gaussian random element in \(C(K)\). Supply that adapter or explicitly assume the random-element law. Do not silently invoke Banach-space Fernique from an unbundled process hypothesis.

This unit avoids Malliavin calculus entirely.

## 10. Dataset-facing theorem and an explicit averaging obstruction

Prove the exact annealed identity for likelihood ratios:
\[
Z_n(\beta)=\int\prod_{i=1}^n e^{-\beta f(X_i,u)}\,\pi(du),
\]
so, by independence and Tonelli,
\[
\boxed{
\mathbb E_+ Z_n(\beta)
=
\int\bigl(\mathbb E e^{-\beta f(X,u)}\bigr)^n\,\pi(du).
}
\]

Under \(\mathbb E e^{-f(X,u)}=1\),
\[
\boxed{\mathbb E Z_n(1)=\pi(W).}
\]

This is an especially valuable corrective theorem: the typical \(n^{-\lambda}(\log n)^{r-1}\) scale does not describe the raw annealed evidence at \(\beta=1\).

Also package the Gaussian-limit coefficient calculation:
\[
\mathbb E D(G)
=
\frac{\Gamma(\lambda)}
     {[\beta(1-\beta)]^\lambda}\rho(K),
\qquad 0<\beta<1,
\]
and its ENNReal divergence for \(\beta\ge1\), assuming divisor variance \(2\).

For actual finite-sample expectation asymptotics, require an explicit UI/moment hypothesis on the **scaled empirical quantities**. Use the existing stochastic expansion and posterior transfer under that hypothesis.

**Stop here.** No general Isserlis campaign, Malliavin calculus, diagram enumeration, or Edgeworth expansion belongs inside these ten units.

---

# D. Concrete editing plan for `averaging_dataset.tex`

## D1. Restructure the main text

Suggested structure:

1. **Scope and normalisation**
   - Define `fluctuation` once.
   - Separate exact finite-sample identities, Gaussian-limit theorems, and conditional asymptotic consequences.
   - State explicitly that convergence in distribution does not imply convergence of expectations.

2. **Sampling phase and resolved covariance**
   - Fix the sign convention.
   - State the standard-form hypotheses.
   - Prove the variance-normalisation lemma with explicit envelopes and extension assumptions.

3. **Raw Gaussian averages**
   - \(Q=0,1,2\) formulas.
   - Bilocal MGF integral.
   - Strict convergence domains and a clearly marked boundary proposition.
   - Corrected floor-rises examples.

4. **Self-normalised finite Gaussian posteriors**
   - Positivity and polynomial bounds.
   - Schwinger–Dyson.
   - Scalar and finite-dimensional Stein.
   - Quartet identities.

5. **Expected log evidence by interpolation**
   - Finite-dimensional theorem for all \(\beta>0\).
   - Optional compact-base extension once unit 9 lands.

6. **Relation to grammar’s stochastic theorems**
   - Evidence-weighted Gaussian face mixture.
   - What existing weak/stable convergence proves.
   - What additional UI and predictive expansion assumptions are needed for expected error formulas.
   - Exact annealed identity at \(\beta=1\).

7. **Discussion**
   - Short diagrammatic interpretation.
   - Relation to Watanabe.
   - Explicitly deferred higher-order questions.

Every Lean remark should distinguish:

- already formalised;
- newly formalised;
- conditional adapter;
- mathematically established but not formalised;
- heuristic/deferred.

Do not label the whole note “formalised” merely because its principal Gaussian identities are.

## D2. Correct these equations and paragraphs in place

### Normalisation and coefficients

Replace
\[
s_m^{(\mu)}
=\frac{\beta^{m/2-\mu}\Gamma(\mu+m/2)}{2m!}
\]
by
\[
s_m^{(\mu)}
=\frac{\beta^{m/2-\mu}\Gamma(\mu+m/2)}{m!}.
\]

Remove the factors \(1/2\) from one-point raw formulas and \(1/4\) from two-point raw formulas when adopting `fluctuation`.

The radial identity in the quartet section is currently misindexed. Use
\[
S_\mu(a)=2\int_0^\infty T^{2\mu-1}e^{-\beta T^2+\beta aT}\,dT,
\]
so
\[
\int_0^\infty T^{2\mu}e^{-\beta T^2+\beta aT}\,dT
=\tfrac12S_{\mu+1/2}(a),
\]
and
\[
\int_0^\infty T^{2\mu+1}e^{-\beta T^2+\beta aT}\,dT
=\tfrac12S_{\mu+1}(a).
\]

### Floor-rises bilocal example

The displayed \(r=1\) coefficient \(\pi b/[4(1-\beta)^2]\) is wrong even in the old normalisation.

Since \(\Gamma(1)^2=1\), it is
\[
\frac{b}{4(1-\beta)^2}
\]
in the old convention, and
\[
\boxed{\frac{b}{(1-\beta)^2}}
\]
in `fluctuation`.

### Geometric overview

For a monomial product standard form, the leading chart exponent is
\[
\lambda=\min_{i:k_i>0}\frac{h_i+1}{2k_i},
\]
with multiplicity determined by the number of minimisers—not the sum stated in the overview.

The normal-crossings divisor is generally a union of smooth components, not itself one smooth object.

### Fisher-information remark

Keep the one-dimensional regular example.

Delete the asserted multidimensional formula
\[
a(x,0)=-\sum_i s_i(x)/\sqrt{I_{ii}/2}.
\]
A multidimensional regular quadratic KL is not reduced to that scalar monomial coefficient by the stated argument. A blow-up introduces directional variables; the resolved coefficient depends on those directions.

### Gaussian jets

Replace “analyticity ensures the required integrability” with an explicit hypothesis or reference to grammar’s analytic coefficient envelope.

Derivatives are jointly Gaussian when obtained as appropriate limits of Gaussian linear functionals. For the existing \(\ell^1\) Gaussian Taylor data, bounded linear coefficient/evaluation maps may be a cleaner route than constructing random derivatives by difference quotients.

### Spatial covariance

Delete “as \(w,w'\) separate, \(b\) decays”. There is no spatial decay theorem in the stated assumptions; the covariance can be constant, oscillatory, or negative.

## D3. Audit the Taylor-tree vertex formula rather than replacing one shift by another

The \(+Q/2\) shift is **not automatically wrong**. It is the shift produced by \(Q\) differentiations of the fluctuation source, or by \(Q\) factors of the radial variable \(T\).

But monomial insertions also modify the underlying Mellin exponent.

For example, in one normal coordinate,
\[
n^{Q/2}\int
u^{h+\gamma+kQ}
e^{-\beta nu^{2k}+\beta\sqrt n\,u^ka}\,du
\]
has scale
\[
n^{-\mu}S_{\mu+Q/2}(a),
\qquad
\mu=\frac{h+\gamma+1}{2k},
\]
up to deterministic factors.

Thus:

- \(Q/2\) tracks source insertions;
- \(\gamma/(2k)\) tracks the monomial insertion;
- both can appear;
- logarithmic terms require the `fluctMoment` functions, not just bare \(S_\mu\).

For multiple coordinates, the shifted floor/minimiser calculation is not generally a naive sum of coordinate shifts.

Replace the universal displayed \(P_\ell\) formula by a **schematic formula**, then state a precise leaf-interface proposition extracted from `thm:TaylorTree`. Do not assert that every leaf is one positive-weight product times one \(S\)-function.

Remove the assertions that every \(S_\lambda\) is a vacuum and that equal asymptotic exponents identify the same irreducible Weyl representation. Those require separate representation-theoretic statements and are not consequences of the displayed ladder identities.

## D4. Replace the claimed leading-order triviality

This section contains a substantive false conclusion.

The leading posterior observable is generally
\[
\boxed{
\frac{\int \rho(w)\phi(w)S_\lambda(G_w)\,dw}
     {\int \rho(w)S_\lambda(G_w)\,dw},
}
\]
which is random and depends on the covariance structure.

Even though
\[
\mathbb E S_\lambda(G_w)
\]
is independent of \(w\) when the variance is constant, it does not follow that
\[
\mathbb E\frac{N(G)}{D(G)}
=\frac{\mathbb E N(G)}{\mathbb E D(G)}.
\]

This is exactly the distinction already represented by grammar’s evidence-weighted face-mixture theorem.

Accordingly:

- replace “leading ratio is the population ratio” by the Gaussian evidence-weighted mixture;
- remove the claim that normalisation first matters at relative order \(1/n\);
- explain that an observable such as \(K\) itself carries a \(1/n\) scale, while the limiting spatial posterior weights can already fluctuate at order \(1\);
- remove the displayed covariance “expansion” of the random ratio: it is neither an exact identity nor a justified asymptotic expansion.

A genuinely constant spatial phase is a special case where a common fluctuation factor cancels. Do not generalise that special case.

## D5. Move corrected formal diagrammatics to an appendix

Create:

> **Appendix A. Heuristic diagrammatics (deferred)**

Move there:

- general Isserlis pairing enumeration;
- geometric denominator expansions;
- higher-loop and higher-cumulant claims;
- “\(1/n\) is loop order” assertions;
- irreducible-module interpretations not independently proved;
- the proposed arbitrary-order computation recipe;
- the diagrammatic phase-transition narrative.

However, **moving a false equation to an appendix is not enough**.

The logarithm expansion is
\[
\mathbb E\log D
=
\log\bar D+
\sum_{p\ge2}\frac{(-1)^{p+1}}p\,\mathbb E[\delta^p]
\]
when justified, not the stated sum of cumulants. For example,
\[
\mathbb E[\delta^4]=\kappa_4+3\kappa_2^2.
\]

Also:

- at \(\beta\ge1\) in the normalised divisor model, \(\bar D=\infty\), so this \(\delta\) is not defined;
- covariance interpolation is not term-for-term the same expansion around \(\bar D\);
- its Taylor coefficients are not simply the cumulants of \(\delta\).

Keep only a corrected formal discussion, with no convergence or asymptotic-order claim.

## D6. Replace the Malliavin sketch, rather than formalising it

Keep the marked-space representation: it is useful and correct in `fluctuation` normalisation.

Replace the claimed infinite-dimensional calculation by the finite-dimensional theorem and, later, its discretisation extension.

Specific errors to remove:

- an isonormal process \(W\) is generally not an \(H\)-valued random vector, so
  \[
  \langle W,\nabla\log D\rangle_H
  \]
  is not automatically meaningful;
- the directional-gradient display duplicates \(\rho\), which is already in the marked measure;
- the claimed factorisation of the marked second moment is unjustified;
- the correct trace bound is simply
  \[
  \operatorname{Tr}\operatorname{Cov}_{\pi}(V,V)
  \le \mathbb E_\pi\|V\|^2
  =c\,\mathbb E_\pi[y]
  \]
  for constant covariance diagonal;
- the \(W\)-Hessian of \(\log D_s\) carries a factor \(s\):
  \[
  \nabla_W^2\log D_s
  =\beta^2s\,\operatorname{Cov}_{\pi_s}(V,V).
  \]

The interpolation identity itself survives unchanged in the rigorous finite-dimensional formulation.

## D7. Correct the finite-\(n\) and criticality discussion

Delete claims that a finite empirical average is automatically sub-Gaussian or has all exponential moments. Neither follows from analyticity in the parameter.

Distinguish:

- pathwise finiteness of \(Z_n\);
- finiteness of its dataset moments;
- finiteness of moments of the Gaussian limit.

At \(\beta=1\), the exact likelihood-normalisation identity
\[
\mathbb E Z_n(1)=\pi(W)
\]
is a much sharper explanation of the annealed/quenched distinction than “divergent factors cancel”.

For the quartet’s Gaussian-limit quantities, no Borel summation or analytic continuation to \(\beta=1\) is required.

## D8. Phase-transition section: keep algebra, defer interpretation

The log-sum identity and the conditional asymptotic formula for \(\Delta F_n\) are useful.

Correct the following:

- \(n^{-(\lambda_2-\lambda_1)}\) is polynomially, not exponentially, small in \(n\);
- equal \(\lambda\) but unequal multiplicities still gives deterministic \(\log\log n\) selection;
- \(\mathbb E[\log D_1-\log D_2]\) depends only on the two marginal laws. Cross-covariance does **not** enter that expectation through cross-cumulants;
- cross-covariance matters for the variance of the difference, phase-selection probabilities, and \(\mathbb E\log(D_1+D_2)\);
- large correlation alone does not prove a “soft” transition or closeness to the population ratio;
- the asserted inclusion between normal bundles of different strata is not supplied by the stated incidence relation.

Keep the corrected elementary algebra as discussion or a short appendix. Move the “resonance”, wall-crossing diagnostics, and universal phase-sharpness claims to explicitly speculative discussion.

---

## Final recommendation

The companion note can become substantially rigorous **now**, without waiting for analytic units:

- **Main theorem:** self-normalised Gaussian quartet, all \(\beta>0\).
- **Second theorem:** finite-dimensional expected-log interpolation.
- **Supporting theorems:** variance normalisation with envelopes; \(Q\le2\) insertion formulas; bilocal MGF and carefully restricted series.
- **Bridge to grammar:** existing random face-mixture and stochastic-expansion results, with explicit UI hypotheses for averaged asymptotics.
- **Strong corrective theorem:** exact annealed evidence at \(\beta=1\).

That is a coherent ten-unit programme. Stop before general Wick combinatorics or infinite-dimensional differential calculus; neither is needed for the note’s most valuable rigorous content.
