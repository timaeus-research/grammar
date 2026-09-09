## Recommendation

**Lead with assembly, then a genuinely cheaper spatial-phase stability theorem.** Follow with the structural properties of the limiting family. Do not spend this stretch on kernels or joint-limit packaging.

I would bound the programme at **five units**, ranked below. All statements remain at the normal-form/chart level unless an assembly identity is explicitly supplied.

### 1. First assembled posterior energy law — keep (a)

This is the clearest next author-facing theorem.

Let \(b_N=N^{-\mu_*}(\log N)^{m_*-1}\). For finitely many dominant charts, let \(U_{N,I}\) be their **unnormalised energy measures**, with
\[
U_{N,I}(\mathbb R)/b_N\longrightarrow A_I>0,
\qquad
\frac{U_{N,I}}{U_{N,I}(\mathbb R)}
\Rightarrow \rho_{a_I},
\]
where every limiting law has shape \(\mu_*\) and temperature \(\beta\). Given an assembled nonnegative measure \(U_N\) with negligible residual, prove
\[
\frac{U_N}{U_N(\mathbb R)}
\Rightarrow
\sum_I\frac{A_I}{A_*}\rho_{a_I},
\qquad A_*=\sum_I A_I.
\]

**Minimal external interface:** instead of constructing signed residual measures, require, for every \(t\ge0\),
\[
\frac{\int e^{-ty}\,dU_N-\sum_I\int e^{-ty}\,dU_{N,I}}{b_N}\to0,
\]
together with support in \([0,\infty)\). The \(t=0\) instance gives the denominator asymptotic. A nonnegative residual of mass \(o(b_N)\) is a convenient sufficient condition.

Then use LXIV. In particular, at zero phase,
\[
\frac{U_N}{U_N(\mathbb R)}
\Rightarrow \operatorname{Gamma}(\mu_*,\text{rate }\beta).
\]

**Traps/non-claims.**
- Different phases generally give a **mixture**, not one effective-phase law.
- Negligible residual mass does not control residual moments.
- Lower-order charts may be discarded only after establishing their mass is \(o(b_N)\).
- Chart-specific phases must belong to the supplied assembly; this does not construct a global perturbation realising arbitrary \(a_I\).
- No resolution or original-space posterior claim is smuggled in.

### 2. Vanishing spatial-phase perturbations — replace (g) by a bounded-oscillation theorem

There is a route requiring **no parameter-uniform higher-\(p\) tail estimate**.

On the same chart, write the posterior density as proportional to
\[
\eta(x)\exp\{-\beta NK(x)+\beta\sqrt{NK(x)}\,\xi_N(x)\},
\]
with \(\eta\ge0\). Let \(P_N^{\xi_N}\) denote this posterior and \(P_N^a\) its constant-phase version. Assume measurability and
\[
|\xi_N(x)-a|\le\varepsilon_N
\quad\text{a.e. on the weighted support},\qquad \varepsilon_N\to0.
\]

First prove the finite-\(N\) bound, using
\(d_{\rm TV}(P,Q)=\sup_E|P(E)-Q(E)|\):
\[
d_{\rm TV}(P_N^\xi,P_N^a)
\le
\frac{\mathcal Z_N(a+\varepsilon)-\mathcal Z_N(a)}
     {\mathcal Z_N(a-\varepsilon)}
\quad\text{if }|\xi-a|\le\varepsilon.
\]

It follows by viewing \(P_N^\xi\) as the normalised tilt
\(h=e^{\beta(\xi-a)\sqrt{NK}}\) of \(P_N^a\), and bounding
\[
|h-1|\le e^{\beta\varepsilon\sqrt{NK}}-1.
\]

For each fixed \(\varepsilon>0\), the constant-phase asymptotics yield
\[
\limsup_N d_{\rm TV}(P_N^\xi,P_N^a)
\le
\frac{A(a+\varepsilon)-A(a)}{A(a-\varepsilon)}.
\]
Continuity and positivity of \(A\) therefore give
\[
d_{\rm TV}(P_N^{\xi_N},P_N^a)\to0,
\qquad
(NK)_\#P_N^{\xi_N}\Rightarrow\rho_a.
\]

This also gives an \(O(\varepsilon)\) **asymptotic stability bound** for fixed small perturbations.

**Inputs:** existing constant-phase asymptotics, positivity, continuity of \(A\); bounded measurable phase perturbations. A fixed-\(\varepsilon\), then \(\varepsilon\downarrow0\), argument avoids moving-parameter estimates.

**Non-claims:** no limit formula for a fixed nonconstant phase; no weighted-\(\ell^1\) Lipschitz theorem; no next-log stability without rates. Continuity of the Programme S coefficient alone does **not** imply Lipschitz continuity. Total variation controls bounded observables, not energy moments automatically.

### 3. Exponential-family structure and strict phase ordering — keep the strongest part of (b)

For \(\lambda,\beta>0\), establish the differentiation identity
\[
\frac{d}{da}\mathbb E_{\rho_a}[f(Y)]
=
\beta\,\operatorname{Cov}_{\rho_a}(f(Y),\sqrt Y)
\]
first for bounded \(f\), then for the polynomial observables needed below.

Targets:
\[
\partial_a\log J_\lambda(a)=\beta\,\mathbb E_{\rho_a}\sqrt Y,
\]
\[
\partial_a^2\log J_\lambda(a)
=\beta^2\operatorname{Var}_{\rho_a}(\sqrt Y)>0,
\]
and, decisively,
\[
\mu'(a)
=\beta\,\operatorname{Cov}_{\rho_a}(Y,\sqrt Y)>0.
\]

So **yes: the limiting mean energy strictly increases with phase, for every real phase**.

A useful stronger statement is stochastic ordering:
\[
a<b,\ f\text{ bounded increasing}
\quad\Longrightarrow\quad
\mathbb E_{\rho_a}f\le\mathbb E_{\rho_b}f.
\]
Prove it from the increasing likelihood ratio
\[
\frac{d\rho_b}{d\rho_a}(y)
=\frac{J_\lambda(a)}{J_\lambda(b)}
 e^{\beta(b-a)\sqrt y}.
\]
The independent-copy covariance identity supplies a clean positivity proof.

**Inputs:** differentiation under the integral using compact-phase domination; polynomial integrability of the Gaussian-in-\(\sqrt y\) tail.

**Trap:** positivity of \(\ell''\) alone does not prove \(\mu'>0\) when \(a<0\). Use covariance, not sign manipulation of the closed form.

### 4. Thermodynamic closed forms and Laplace consistency — finish (b)

With \(\ell=\log A_\beta\), prove
\[
\mu(a)=\frac{\lambda+(a/2)\ell'(a)}{\beta},
\]
\[
v(a)=
\frac{\lambda+(3a/4)\ell'(a)+(a^2/4)\ell''(a)}
{\beta^2}.
\]
Identify these with the existing \(c_1\) and posterior variance limits.

Extend the limiting transform naturally to \(t>-\beta\):
\[
T(a,t)=
\frac{\int_0^\infty y^{\lambda-1}
 e^{-(\beta+t)y+\beta a\sqrt y}\,dy}{J_\lambda(a)}.
\]
Then establish
\[
-\partial_tT(a,0)=\mu(a),\qquad
\partial_t^2\log T(a,0)=v(a)>0.
\]

At \(a=0\), record the calibration
\[
\mu(0)=\lambda/\beta,\qquad v(0)=\lambda/\beta^2.
\]

**Inputs:** the \(J\)-recurrence and derivative infrastructure from unit 3. Since \(A=HJ_\lambda/2\), phase derivatives of \(\log A\) and \(\log J_\lambda\) agree when \(H>0\).

**Non-claim:** do not obtain these by differentiating the convergence \(T_N\to T\). Differentiate the limiting integral directly. Using \(t>-\beta\) also removes the one-sided derivative nuisance at zero.

### 5. Upgrade constant-phase weak convergence to Wasserstein convergence — replacement (h)

LXI–LXIV already contain the substantive hypotheses. Let \(\nu_N\) be the posterior law of \(NK\) at fixed phase. Prove, for every finite \(p\ge1\),
\[
W_p(\nu_N,\rho_a)\longrightarrow0.
\]

Choose an integer \(q>p\). LXII gives
\[
\sup_N\int y^q\,d\nu_N<\infty
\]
after discarding finitely many terms, hence
\[
\sup_N\int_{y>R}y^p\,d\nu_N
\le R^{p-q}\sup_N\int y^q\,d\nu_N\to0.
\]
Combine this with weak convergence and the standard Wasserstein criterion.

If the Wasserstein API would dominate the work, stop at the still-useful theorem:
\[
\int f\,d\nu_N\to\int f\,d\rho_a
\]
for every continuous \(f\) of polynomial growth.

**Non-claims:** random-phase expectation convergence still needs appropriate integrability. Nor does assembly inherit this upgrade without moment-weighted residual control.

## Cuts and scope

- **(a): keep, first.**
- **(b): keep, split into structural ordering and explicit formulas.**
- **(c): include only as a short corollary**, not a work unit: continuous mapping gives the square-root law with density
  \[
  s\mapsto M_\beta(2\lambda;a)^{-1}s^{2\lambda-1}e^{-\beta s^2+\beta as}.
  \]
- **(d): defer.** Large positive-phase asymptotics deserve a separate concentration/Laplace-method programme.
- **(e), (f): drop this stretch.** Useful packaging, but not the requested mathematical advance.
- **(g): defer in full generality; replace by unit 2.**

The resulting headline is substantial: **assembled energy laws, robustness to vanishing spatial perturbations, strict phase ordering, and polynomial-observable convergence**—without reopening any deferred geometric bridge.
