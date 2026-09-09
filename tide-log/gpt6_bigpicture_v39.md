## Recommendation: 11 units, with one bounded §4 pilot

**Prioritise stochastic second-order asymptotics, then the population energy hierarchy.** Close the boundary-positivity issue without importing geometry. Keep nonzero-phase work to a two-unit, constant-phase pilot.

The crucial correction to candidate (i): **convergence in distribution of the data does not justify centring at the limiting random quotient at the `log N` scale.** The natural theorem centres at the leading quotient evaluated on the *current* data.

Throughout, write \(L=\log N\), with \(N\to\infty\), and assume \(\beta>0\). All assembly, chart and normal-form data remain external.

---

## 1. Stochastic second-order quotient — **GO, highest priority; 3 units**

### Unit 1: Locally uniform two-term remainder

For fixed exponent/log degree \((\lambda,s)\), put
\[
X_N(d)=\frac{Z_N(d)}{N^{-\lambda}L^s},\qquad
A(d)=C_{\lambda,s}(d),\quad B(d)=C_{\lambda,s-1}(d),
\]
with \(B=0\) when \(s=0\).

Target, on the admissible support locus \(S\):
\[
\sup_{\substack{d\in S\\\|d\|\le R}}
\left|L\bigl(X_N(d)-A(d)\bigr)-B(d)\right|\longrightarrow0.
\]

Prove the analogous statement for the observable integral.

**Inputs:** a common admissible chart family, common cutoff strictly beyond \(\lambda\), and bounded-set quantitative cutoff estimates. On \(S\), coefficients at smaller exponents and at larger log degrees at exponent \(\lambda\) vanish.

**Trap:** pointwise coefficient continuity and pointwise cutoff asymptotics do **not** imply this uniform statement. Extract the envelope from the existing quantitative estimates. Include any assembly residual at the scale
\[
E_N=o\!\left(N^{-\lambda}L^{s-1}\right).
\]
For \(s=0\), this means \(o(N^{-\lambda}/L)\), not merely \(o(N^{-\lambda})\).

### Unit 2: Random-data two-term expansion

For random admissible data \(D_N\) whose norms are bounded in probability:
\[
L\bigl(X_N(D_N)-A(D_N)\bigr)-B(D_N)
   \xrightarrow{\mathbb P}0.
\]

Allow \(D_N\in S\) almost surely, or with probability tending to one. Derive norm tightness from data convergence in distribution where the existing interfaces permit it.

**Inputs:** Unit 1 and corresponding probabilistic control of external residuals.

**Do not claim:** convergence in distribution of the data alone preserves a selected pair. The predecessor vanishings must hold for the approximating data, not just for their limit.

### Unit 3: Randomly centred quotient

Let
\[
(A_N,B_N,A'_N,B'_N)\Rightarrow(A,B,A',B'),
\qquad \mathbb P(A\ne0)=1,
\]
and assume both two-term remainders are \(o_{\mathbb P}(1/L)\). Then
\[
L\left(
\frac{Z'_N}{Z_N}N^{\lambda'-\lambda}L^{s-s'}
-\frac{A'_N}{A_N}
\right)
\Rightarrow
\frac{AB'-A'B}{A^2}.
\]

Also obtain joint convergence with the coefficient vector.

**Division trap:** denominators need only be nonzero with probability tending to one; use totalised division consistently and show exceptional events disappear.

**Do not claim:** the same result centred at \(A'/A\) under weak convergence alone. That requires a common-space coupling and, for example,
\[
L\left(A'_N/A_N-A'/A\right)\xrightarrow{\mathbb P}0.
\]
A deterministic centring is valid when the current leading quotient is identically that constant.

---

## 2. Population energy hierarchy — **GO; 3 units**

This gives more mathematical return than an isolated third-order energy calculation.

### Unit 4: Iterated coefficient transport and moment correction

For every fixed \(r\in\mathbb N\), prove
\[
C_{K^r}(\mu+r,j)
=\beta^{-r}
\left[\prod_{q=0}^{r-1}(\mu+q-\partial_L)P_\mu(L)\right]_j,
\]
where \(P_\mu(L)=\sum_j C(\mu,j)L^j\).

After finite assembly with selected pair \((\lambda,s)\), \(A\ne0\), conclude
\[
N^r\frac{\mathcal Z_{K^r}}{\mathcal Z}
\longrightarrow \frac{(\lambda)_r}{\beta^r},
\]
and
\[
L\left(
N^r\frac{\mathcal Z_{K^r}}{\mathcal Z}
-\frac{(\lambda)_r}{\beta^r}
\right)
\longrightarrow
-\frac{s}{\beta^r}\,\partial_\lambda(\lambda)_r.
\]

Here \((\lambda)_r=\lambda(\lambda+1)\cdots(\lambda+r-1)\); its derivative is simply a polynomial derivative.

**Inputs:** zero noise, common fixed chart data, and the two-term residual scale for each inserted moment:
\[
E_r=o\!\left(N^{-(\lambda+r)}L^{s-1}\right).
\]

**Trap:** do not prove this by differentiating an asymptotic equivalence. Iterate the exact coefficient transport.

### Unit 5: Variance, including its first correction

Under nonnegative posterior weights, define
\[
V_N=N^2\frac{\mathcal Z_{K^2}}{\mathcal Z}
-\left(N\frac{\mathcal Z_K}{\mathcal Z}\right)^2.
\]
Prove
\[
V_N\to\frac{\lambda}{\beta^2},
\qquad
L\left(V_N-\frac{\lambda}{\beta^2}\right)
\to-\frac{s}{\beta^2}.
\]

**Inputs:** Unit 4 for \(r=1,2\), eventual positive denominator.

**Do not call this** the learning-theoretic “singular fluctuation.” It is the posterior variance of \(NK\); that terminology otherwise risks conflating distinct invariants.

### Unit 6: Gamma Laplace-transform limit

For the actual nonnegative population integral, with \(N\)-independent amplitude,
\[
\mathbb E_{N,\beta}[e^{-tNK}]
=\frac{\mathcal Z_{\beta+t}(N)}{\mathcal Z_\beta(N)}
\longrightarrow
\left(\frac{\beta}{\beta+t}\right)^\lambda
\qquad(t\ge0).
\]

Use the exact rescaling
\[
\mathcal Z_{\beta+t}(N)
=\mathcal Z_\beta\!\left(\frac{\beta+t}{\beta}N\right),
\]
rather than developing new parameter-uniform asymptotics.

**Inputs:** \(\lambda>0\), positive leading coefficient, and an exact integral family with the stated rescaling. An arbitrary externally supplied residual need not respect that identity.

**Do not claim:** weak convergence to Gamma merely from moment convergence. The Laplace-transform theorem is already a useful endpoint; add weak convergence only if the required probability theorem is already available. Arbitrary cumulant infrastructure is outside this allocation.

---

## 3. Nonnegative weights and principal-face witnesses — **GO; 2 units**

### Unit 7: Replace global strict positivity by a face witness

For a principal-face functional represented by integration against a positive density, prove:

* nonnegative amplitude restriction implies a nonnegative face coefficient;
* a continuous nonnegative restriction that is positive at one relative-interior point has strictly positive face coefficient.

Handle the zero-dimensional face separately: its functional is evaluation.

**Inputs:** supplied face parametrisation and density, positivity/local integrability of that density, and a witness on the relevant principal face.

**Trap:** positivity somewhere in the ambient chart is insufficient. The restriction to the principal face can vanish identically while the amplitude is positive elsewhere.

### Unit 8: Assembled noncancellation from compatible witnesses

For charts contributing to a common global leading pair \(p_*\), prove:
\[
A_i\ge0\ \text{for all contributors},\qquad
A_{i_0}>0
\quad\Longrightarrow\quad
A_*=\sum_i A_i>0.
\]

Add a convenient witness corollary for amplitudes \(w_i\rho_i\): supplied compatible principal-face points, \(w_i\ge0\), \(\rho_i>0\) there, and a positive sum of their weight evaluations imply a positive assembled coefficient.

**External:** compatibility of those points and any partition-of-unity identity. Do not construct them.

**Do not claim:** an arbitrary partition of unity guarantees positivity at the dominant face. Its positive chart might have a different candidate pair, or the relevant restrictions might all vanish. If all dominant face coefficients vanish, selection must run again.

---

## 4. Constant nonzero phase pilot — **GO narrowly; full (ii) NO-GO this stretch; 2 units**

### Unit 9: Phase-dressed moment recurrence

Define explicitly
\[
J_{\nu,i}(a)=
\int_0^\infty t^{\nu-1}(-\log t)^i
 e^{-\beta t^2+\beta at}\,dt.
\]
For \(\nu>0\), prove
\[
2\beta J_{\nu+2,i}
=\nu J_{\nu,i}+\beta aJ_{\nu+1,i}
-iJ_{\nu,i-1},
\]
omitting the final term when \(i=0\), together with
\[
\partial_aJ_{\nu,i}=\beta J_{\nu+1,i}.
\]

**Inputs:** only \(\beta>0,\nu>0\); boundary terms and differentiation under the integral are proved using Gaussian domination.

This is a deliberately bounded kernel theorem, not a claim to cover every `kernelS` polynomial factor.

### Unit 10: Constant-phase energy correction

For \(\xi(u)\equiv a\), establish coefficient transport
\[
C_K(\mu+1,j;a)
=\frac{\mu C(\mu,j;a)-(j+1)C(\mu,j+1;a)
+\frac a2\,\partial_aC(\mu,j;a)}{\beta}.
\]

For two-term coefficients \(A(a),B(a)\), with \(A(a)\ne0\), deduce
\[
N\frac{Z_K}{Z}\to
\frac{\lambda}{\beta}
+\frac{a}{2\beta}\frac{A'(a)}{A(a)},
\]
and
\[
L\left(
N\frac{Z_K}{Z}
-\frac{\lambda}{\beta}
-\frac{aA'(a)}{2\beta A(a)}
\right)
\to
-\frac{s}{\beta}
+\frac{a}{2\beta}
\frac{A(a)B'(a)-A'(a)B(a)}{A(a)^2}.
\]

**Inputs:** constant-phase chart data and two-term residuals for both integrals. Prove coefficient differentiation from the moment representation, not from differentiated remainders.

**Do not claim:** this handles spatially varying \(\xi\). That requires phase-scaling differentiation of the full coefficient functional, including the Taylor-tree contributions. If that extra machinery becomes necessary even for this pilot, stop at Unit 9 rather than enlarge the programme.

---

## 5. Free energy with its first inverse-log correction — **GO; 1 unit**

### Unit 11: A paper-facing logarithm theorem

From
\[
Z=N^{-\lambda}L^s\left(A+\frac BL+o(L^{-1})\right),
\qquad A>0,
\]
prove eventual positivity and
\[
-\log Z
=\lambda L-s\log L-\log A-\frac{B}{AL}+o(L^{-1}).
\]

Instantiate for chart and assembled population expansions.

**External:** only the established expansion and positivity.

**Do not integrate in \(\beta\):** direct logarithm continuity and the first-order expansion of \(\log(1+x)\) suffice. No WBIC claim, particularly no moving-temperature regime such as \(\beta_N\asymp1/\log N\).

---

## Explicit cuts

* **(i): GO**, with current-data centring and a proved locally uniform second-order remainder.
* **(ii): defer the general empirical theorem.** Only the two-unit constant-phase pilot is GO.
* **(iii): GO** for all fixed moments, variance correction and Laplace-transform limit. Defer general cumulant infrastructure.
* **(iv): DROP this stretch.** Fixed third-order division is legitimate, but lower value than the above.
* **(v): KEEP free energy; DROP new \(\beta\)-derivative/WBIC development.**
* **(vi): DROP.** Existing signed-box machinery makes this a corollary backlog. Also, odd \(h_i\) alone does not force cancellation for arbitrary amplitudes: one needs the relevant evenness or vanishing-face argument.
* **(vii): DROP.** Local monomial-order bookkeeping is not a coordinate-free theorem; chart compatibility and divisorial interpretation remain external.
* **All-orders inverse-log division remains NO-GO.**

This programme adds a genuine stochastic second-order theorem, a population Gamma-energy hierarchy, and a practical positivity bridge—without reopening resolution or mistaking local chart algebra for coordinate-free geometry.
