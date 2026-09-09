## Recommendation

**Rank: (d) → (b) → (c) → joint limit → (e).** Use six units, with polynomial-observable/Wasserstein work split into two. **Defer (a); drop (f) from this stretch.**

The best next headline is: **the perturbed posterior has the correct limiting energy mean and variance—not merely the correct weak limit.** Then turn the deterministic phase family into a usable random-phase theorem.

All statements below assume the existing positivity/integrability hypotheses, in particular \(\beta,\lambda>0\). No resolution, geometric bridge, or empirical-process theorem is needed.

## 1. Perturbed energy moments, including mean and variance — (d)

**Target.** For measurable phases satisfying
\[
\sup_u|\xi_N(u)-a|\le \varepsilon_N,\qquad \varepsilon_N\to0,
\]
prove, for every integer \(r\ge0\),
\[
\mathbb E_{\xi_N}[(NK)^r]\longrightarrow
m_r(a):=\frac{J_{\lambda+r}(a)}{J_\lambda(a)}.
\]
Consequently,
\[
\mathbb E_{\xi_N}[NK]\to\mu(a),\qquad
\operatorname{Var}_{\xi_N}(NK)\to v(a).
\]

**Shortest proof route: positive-observable sandwich, not truncation.** Whenever \(|\xi-a|\le\delta\), positivity of the tilt statistic gives, for \(h\ge0\),
\[
\frac{\mathcal Z_N(a-\delta)}{\mathcal Z_N(a+\delta)}
 \mathbb E_{a-\delta}[h]
\le \mathbb E_\xi[h]\le
\frac{\mathcal Z_N(a+\delta)}{\mathcal Z_N(a-\delta)}
 \mathbb E_{a+\delta}[h].
\]
Instantiate with \(h=(NK)^r\), take \(N\to\infty\), then \(\delta\downarrow0\).

**Inputs.** Existing constant-phase moment asymptotics, partition-function asymptotics, continuity of the moment ratios. Establish perturbed integrability by the same domination before using real-valued integrals.

**Trap.** An \(\varepsilon_N\)-dependent application of a fixed-phase asymptotic is not automatically justified. The fixed-\(\delta\), double-limit proof avoids that issue.

**Author payoff:** posterior energy estimators now survive vanishing spatial phase error.

## 2. Polynomial observables and Wasserstein convergence — finish #42 unit 5

**Target.** Under Unit 1’s assumptions, for every continuous \(f:[0,\infty)\to\mathbb R\) satisfying
\[
|f(y)|\le C(1+y^r),
\]
prove
\[
\int f\,d\operatorname{phaseEnergyLaw}_N(\xi_N)
\longrightarrow \int f\,d\rho_a.
\]
Then, for every finite \(p\ge1\),
\[
W_p\!\left(\operatorname{phaseEnergyLaw}_N(\xi_N),\rho_a\right)\to0.
\]

**Inputs.** LXVIII weak convergence and Unit 1 with an integer moment order strictly larger than \(r\), respectively \(p\). Package the reusable lemma “weak convergence + bounded higher moments ⇒ convergence against continuous polynomial-growth observables.”

**Traps and bounds.**
- Weak convergence does **not** cover arbitrary measurable polynomially bounded observables.
- A bounded \(p\)-th moment alone does not supply uniform integrability of the \(p\)-th powers.
- State Wasserstein convergence on the actual energy space, or transport explicitly through its inclusion into \(\mathbb R\).

**Lean scope cap.** If Mathlib’s available transport interface makes \(W_p\) disproportionately expensive, ship the polynomial-observable theorem and the precise moment/tail conditions first. Do not let a new transport library consume the stretch.

## 3. Locally uniform convergence and moving deterministic phases — (b)

Let \(K_N(a)\) denote the constant-phase energy law and \(K(a)=\rho_a\).

**Targets.** For every compact \(C\subset\mathbb R\) and bounded continuous \(f\),
\[
\sup_{a\in C}
\left|\int f\,dK_N(a)-\int f\,dK(a)\right|\to0.
\]
Also:
\[
a_N\to a\quad\Longrightarrow\quad K_N(a_N)\Rightarrow K(a).
\]
Add locally uniform convergence of every fixed moment, hence the corresponding compact-uniform polynomial-observable result.

**Proof route.** Use compact-uniform Laplace convergence and continuity of \(a\mapsto\rho_a\). A compactness/subsequence contradiction promotes moving-phase convergence to uniform convergence for each test function. Compact-uniform moment bounds come from the existing two-term numerator/denominator data and a positive minimum for \(A\).

**Useful strengthening for Unit 5.** For bounded jointly continuous \(F(a,y)\), prove locally uniform convergence of
\[
a\mapsto\int F(a,y)\,K_N(a,dy)
\]
to the analogous limiting function. Uniform energy tightness on compact phase sets supplies the needed truncation.

**Non-claim.** This is not uniform convergence over all bounded measurable observables, nor uniformity over unbounded phase sets. A weak metric is an optional packaging theorem, not the core deliverable.

## 4. Random-phase mixture laws — (c)

**Targets.**
1. Construct measurable probability kernels \(K_N\) and \(K\).
2. For arbitrary probability laws \(\eta_N\Rightarrow\eta\) on phase space,
\[
\eta_N\mathbin{\mathrm{bind}}K_N
\Rightarrow
\eta\mathbin{\mathrm{bind}}K.
\]

**Inputs.** Joint measurability of the unnormalised densities, measurable parameter integrals, positive normalisers, and pushforward measurability. Then use `integral_bind` and the existing random-phase transform theorem/LXV:
\[
\int T_N(a,t)\,\eta_N(da)\to
\int T(a,t)\,\eta(da).
\]
The bound \(0\le T_N\le1\) handles phase tails through tightness.

**Why worth a unit:** yes. This is a paper-facing distribution theorem, not merely infrastructure. It replaces informal “condition on the random phase” arguments with an explicit limiting energy distribution.

**Critical non-claim.** This mixture describes the stipulated conditional kernel. It does not establish that an empirical phase and the actual posterior have that conditional law. Nor does it identify evidence-reweighted chart mixing with exogenous mixing by \(\eta\).

## 5. Joint phase–energy limit — replace the temperature direction

**Target.** Define
\[
Q_N(da,dy)=\eta_N(da)K_N(a,dy),\qquad
Q(da,dy)=\eta(da)\rho_a(dy).
\]
Prove
\[
Q_N\Rightarrow Q.
\]
In particular, for bounded continuous \(h\) and \(t\ge0\),
\[
\int h(a)e^{-ty}\,dQ_N
\to
\int h(a)T(a,t)\,\eta(da).
\]

**Inputs.** Unit 3’s jointly continuous test-function result, Unit 4’s kernel construction, and tightness of \(\eta_N\). Prove convergence directly against bounded continuous functions on the product; no new multivariate Laplace-continuity theorem is necessary.

**Optional bounded extension.** Under an explicit condition
\[
\sup_N\int m_{N,q}(a)\,\eta_N(da)<\infty
\]
for some integer \(q>r\), extend to continuous joint observables bounded by \(C(1+y^r)\).

**Traps.**
- The limit is generally **not** an independent product.
- Weak convergence of phase laws alone does not justify convergence of mixed energy means or variances. Rare large phases can spoil moment convergence.

## 6. Full stochastic ordering of the limiting family — (e)

**Target.** For \(a<b\),
\[
\rho_a\le_{\mathrm{st}}\rho_b:
\qquad
\int g\,d\rho_a\le\int g\,d\rho_b
\]
for every bounded measurable increasing \(g\). Prove strict inequality when \(g\) is not \(\rho_a\)-almost everywhere constant.

Give the particularly usable corollary
\[
\rho_b((t,\infty))>\rho_a((t,\infty))
\qquad(t>0).
\]

**Inputs.** The likelihood ratio
\[
\frac{d\rho_b}{d\rho_a}(y)
=\frac{J_\lambda(a)}{J_\lambda(b)}
 e^{\beta(b-a)\sqrt y}
\]
and a two-copy covariance identity. Full support on \((0,\infty)\) supplies strictness.

**Trap.** The likelihood ratio is unbounded: prove its integrability and the relevant product integrability explicitly. This ordering concerns the common-\(\lambda,\beta\) constant-phase family, not arbitrary spatial perturbations or changing chart mixtures.

## Cuts and spatial-phase warning

**(a): defer, but correct the proposed obstruction.** Constancy along the face is not necessary. What is missing is a **joint energy–face asymptotic theorem**. If its baseline limit factorises as \(\rho_a(dy)\bar\eta(dv)\), a bounded face phase produces a candidate joint density proportional to
\[
y^{\lambda-1}e^{-\beta y+\beta(a+\varepsilon\zeta(v))\sqrt y}\,dy\,\bar\eta(dv).
\]
Its energy marginal is an **evidence-weighted** mixture, with face weights proportional to \(J_\lambda(a+\varepsilon\zeta(v))\). Existing energy convergence alone does not establish this. Respect the spatial-limit deferral rather than disguise the missing joint theorem as Taylor calculus.

**(f): drop for now.** Useful, but less valuable than joint/random-phase energy laws. Also, \(\partial_\beta\mu=-v\) holds at fixed \(c=\beta a\), whereas at fixed \(a\),
\[
\partial_\beta\mu=-v+a\,\operatorname{Cov}(Y,\sqrt Y).
\]
No blanket fixed-\(a\) monotonicity should be claimed.

**Stop after six units.** This gives a coherent new layer: **energy moments → polynomial observables → moving phases → random mixtures → joint laws → stochastic comparison.**
