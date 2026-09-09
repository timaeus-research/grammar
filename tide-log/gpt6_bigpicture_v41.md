## Recommendation

Prioritise **the actual posterior law of \(NK\)**, with the joint moving-phase theorem and free energy as inexpensive companion results. Keep the spatially varying phase deferred.

**Important correction to (a):** changing temperature at fixed \(a\) changes both the energy and phase terms. Thus
\[
\frac{\mathcal Z_{\beta+t}(N;a)}{\mathcal Z_\beta(N;a)}
\]
is **not** the posterior Laplace transform of \(NK\).

Write \(r=(\beta+t)/\beta\). For the posterior defined by the \(\beta\)-integrand, the correct identity is
\[
T_N(a,t):=\mathbb E_{\beta,N,a}[e^{-tNK}]
=\frac{\mathcal Z_{\beta+t}(N;a/r)}{\mathcal Z_\beta(N;a)}
=\frac{\mathcal Z_\beta(rN;a/\sqrt r)}{\mathcal Z_\beta(N;a)}.
\]
Consequently,
\[
T(a,t)=r^{-\lambda}\frac{A(a/\sqrt r)}{A(a)}.
\]
The fixed-phase temperature ratio in (a) is a valid different theorem, but its derivative does not recover the energy mean.

Here is a ranked, **eight-unit cap**.

---

### 1. Correct phase-aware tilting and temperature rescaling

Prove both exact identities, explicitly distinguished:

\[
\mathcal Z_{\beta+t}(N;a)
=\mathcal Z_\beta(rN;a\sqrt r),
\]
\[
\int e^{-tNK}\,dP_{\beta,N,a}
=\frac{\mathcal Z_\beta(rN;a/\sqrt r)}
       {\mathcal Z_\beta(N;a)}.
\]

**Inputs:** a nonnegative integrand defining a finite posterior, positive normaliser, and the exact energy/phase integrand identity. For an original-space posterior, the standard-form identity remains external.

**Traps:** require \(\beta>0\), \(r>0\); use \(t\ge0\) for probability-law work. Check whether \(N\) is real-valued in the rescaling interface: silently replacing \(rN\) by an integer is not an exact identity.

This unit prevents a substantive misstatement in the paper.

### 2. Compact-uniform, two-term posterior Laplace asymptotics

Set \(b=a/\sqrt r\), \(p=m-1\). Prove
\[
T_N(a,t)\to T(a,t),
\]
and the stronger refinement
\[
L\bigl(T_N(a,t)-T(a,t)\bigr)\to S(a,t),
\]
where
\[
S(a,t)=r^{-\lambda}
\left[
\frac{B(b)+p\log r\,A(b)}{A(a)}
-\frac{A(b)B(a)}{A(a)^2}
\right].
\]

Target uniformity on
\[
|a|\le R,\qquad 0\le t\le T,
\]
assuming \(A>0\) on the denominator phase compact.

**Inputs:** `constPhase_twoTerm_uniform`, continuity of \(A,B\), and a positive compact lower bound for \(A\).

**Traps:** the numerator remainder must be uniform at **both** the shifted phase \(b\) and shifted scale \(rN\). The \(p\log r\) term comes from \((L+\log r)^p\); it must not disappear. This is finite two-term division, not the prohibited all-orders programme.

For finitely many \(t_i\), also export the moving-phase vector limit
\[
\bigl(T_N(X_N,t_i),\,L(T_N(X_N,t_i)-T(X_N,t_i))\bigr)_i
\Rightarrow
\bigl(T(X,t_i),S(X,t_i)\bigr)_i.
\]

### 3. Construct and identify the limiting energy law

Under the positive-half-line monomial convention, define
\[
\rho_a(dy)=
\frac{y^{\lambda-1}e^{-\beta y+\beta a\sqrt y}}
{\displaystyle\int_0^\infty u^{\lambda-1}e^{-\beta u+\beta a\sqrt u}\,du}
\,dy,\qquad y>0,
\]
with \(\lambda>0\).

Prove finiteness, positivity, normalisation, and
\[
\int e^{-ty}\,\rho_a(dy)=T(a,t).
\]

Match the normalising integral to the repository’s **actual \(J\)-definition**, including its change-of-variable constants. Do not infer those constants from the subscript \(J_{2\lambda}\).

At \(a=0\), identify the Gamma law of shape \(\lambda\), rate \(\beta\). For nonzero \(a\), present \(\rho_a\) as the square-root exponential tilt of that law.

**Inputs:** face factorisation \(A(a)=J_{2\lambda}(a)H\); \(H\) cancels.

**Non-claim:** signed monomial sectors or differently phased assembled charts require their actual limiting mixture, not this density automatically.

### 4. Phase-dressed moment hierarchy and variance

Define leading energy-moment coefficients by
\[
M_0=A,\qquad
M_{q+1}=\frac{(\lambda+q)M_q+(a/2)M_q'}{\beta}.
\]
Prove, for each fixed \(q\in\mathbb N\),
\[
\mathbb E_{\beta,N,a}[(NK)^q]\to \frac{M_q(a)}{A(a)}
=\int y^q\,\rho_a(dy).
\]

Export compact-uniform convergence for each fixed \(q\), then the corresponding fixed/moving random-phase statistics.

For \(\ell=\log A\), the useful closed forms are
\[
\mu(a)=\frac{\lambda+(a/2)\ell'(a)}{\beta},
\]
\[
v(a)=\frac{\lambda+\frac{3a}{4}\ell'(a)
+\frac{a^2}{4}\ell''(a)}{\beta^2}.
\]

Also prove the consistency checks
\[
-\partial_tT(a,0)=c_1(a),\qquad
\partial_t^2\log T(a,0)=v(a).
\]

**Inputs:** iterated coefficient transport, repeated coefficient differentiability, and the existing moment integrals.

**Trap:** none of these may come from differentiating an \(N\)-asymptotic expansion. Differentiate the exact limiting integral or coefficient formula. Uniformity in \(q\) is not requested.

### 5. Weak convergence of the posterior energy law

Prove the headline theorem
\[
(NK)_*P_{\beta,N,a}\Rightarrow\rho_a.
\]
Also prove the deterministic moving-phase version for every \(a_N\to a\).

Avoid building a general Laplace-transform continuity library. A bounded specialised lemma suffices:

> Probability measures on \([0,\infty)\), uniformly tight, whose Laplace transforms converge at every nonnegative integer to those of a specified probability measure, converge weakly to that measure.

Use \(u=e^{-y}\), polynomial approximation on \([0,1]\), and a tail cutoff. Unit 4 supplies tightness through the first moment; unit 2 supplies transform convergence.

**Traps:** \(u=0\) corresponds to escaped mass at infinity; it cannot simply be ignored when applying \(-\log\). The original-space version still requires the external posterior/assembled-integral identification and appropriate residual control.

This is preferable to a detour through characteristic functions and an unformalised Gamma characteristic function.

### 6. Random-phase posterior mixture limit

When a posterior probability kernel is available, let \(Y_N\), conditionally on \(X_N=a\), have the posterior law of \(NK\). Prove
\[
X_N\Rightarrow X
\quad\Longrightarrow\quad
Y_N\Rightarrow \int\rho_a\,\operatorname{Law}(X)(da).
\]

**Inputs:** measurable posterior kernels, positivity of \(A\), compact-uniform transform convergence, and compact-uniform first-moment bounds.

Phase tightness plus local moment bounds gives energy-law tightness without requiring a global phase moment bound.

**Important distinction:** for \(t\ge0\), posterior Laplace transforms lie in \([0,1]\). Their expectations therefore converge without the extra UI hypothesis needed for energy means.

**Non-claim:** this does not establish
\(\mathbb E[Q_N(X_N)]\to\mathbb E[c_1(X)]\).
Nor does it assert joint convergence with \(X_N\); leave that stronger kernel theorem outside this unit.

### 7. Close the existing joint-statistics gap

Using one continuous mapping of the existing statistics vector, prove
\[
\left(Q_N(X_N),
L(Q_N(X_N)-c_1(X_N))\right)
\Rightarrow
\left(c_1(X),c_2(X)\right).
\]

**Inputs:** exactly LX’s hypotheses and denominator control.

**Traps:** two marginal convergence statements do not establish the joint theorem. Preserve the common statistics vector. The centring remains \(c_1(X_N)\), not \(c_1(X)\).

This is cheap enough to land early while the law work proceeds.

### 8. Constant-phase and moving-phase free energy

For \(F_N(a)=-\log\mathcal Z_N[\eta;a]\), prove compact-uniformly
\[
F_N(a)=\lambda L-p\log L-\log A(a)
-\frac{B(a)}{A(a)L}+o(L^{-1}).
\]
Then
\[
L\!\left(F_N(X_N)-\lambda L+p\log L+\log A(X_N)\right)
\Rightarrow-\frac{B(X)}{A(X)}.
\]

**Inputs:** `neg_log_twoTerm`, uniform two-term remainder, compact positive lower bounds.

State the interpretation precisely:
\[
-\log A(a)=-\log J_{2\lambda}(a)-\log H.
\]
The phase also enters the \(1/L\) correction through \(B/A\).

---

## Cuts and priority

**Keep:** corrected **(a)**, **(b)**, **(d)**, then **(c)**. Add **(h)** as the main payoff: an identified posterior weak limit.

**Drop this round:**

- **(e), zeros localisation:** useful abstraction, but unnecessary under the positive-face hypothesis. Do not claim global positivity handles charts lacking that witness.
- **(f), spatially varying phase:** still deferred; its parameter-uniform higher-\(p\) tail is genuinely new analytic work.
- **(g), energy expectations:** local-uniform asymptotics do not control phase tails. The suggested global linear bound is generally implausible: the limiting tilted law has mean of quadratic order as \(a\to+\infty\). Positivity of \(J\) also gives no positive lower bound over the whole real line. A generic “UI implies expectation convergence” corollary is fine, but not a headline unit.

**Hard stop:** eight units; no resolution bridge, no general transform library, no all-orders division.
