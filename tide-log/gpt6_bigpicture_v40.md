## Recommendation

**Prioritise (a) and (b), strengthen them to a moving-random-phase next-log theorem, then do (f).** This gives a coherent new result: not merely stochastic convergence of energy, but its first logarithmic correction under a random constant phase.

I would **defer (c), drop (d) from this sprint, and drop (e) as a standalone headline**. Six bounded units follow. Order below includes prerequisites.

Throughout, write
\[
L=\log N,\qquad Q_N(a)=N\,\frac{\mathcal Z_N[K\eta;a]}{\mathcal Z_N[\eta;a]},
\]
and use coefficients in the **\(N^{-\lambda}L^j\) convention**, not the \(\sqrt N\) convention. Assume \(\beta>0,\lambda>0\), and let \(U\) be the parameter domain on which the constant-phase expansion is actually available.

### 1. Constant-phase nonvanishing and regularity

Package the LVI face formula as
\[
A(a)=H\,J_{2\lambda}(a),
\]
where \(H\) is the phase-independent face factor, including all normalising constants.

**Targets**
- \(J_{2\lambda}(a)>0\) for real \(a\).
- Under a positive face witness, \(H>0\), hence \(A(a)>0\).
- \(A\) is continuously differentiable on \(U\).
- On each compact \(C\subset U\), \(A\) is bounded away from zero.

For an assembled expansion, factor out the common moment only after checking that all leading contributors have the same \(\lambda\) and that their normalisations have been reconciled.

**Inputs:** LVI, moment domination, LI positivity. No new geometry.

**Payoff:** division hypotheses become structural rather than repeatedly assumed. Indeed, for this fixed-amplitude constant-phase family, \(H\neq0\) already gives global nonvanishing wherever the formula holds; positivity is stronger than necessary.

**Trap:** positivity of individual moments does not prevent cancellation in a signed assembled face factor.

### 2. Constant-phase two-term data, including multiplicity one

Prove for \(m\ge2\):
\[
\mathcal Z_N[\eta;a]
=N^{-\lambda}L^{m-1}
\left(A(a)+\frac{B(a)}L+o(L^{-1})\right),
\]
and independently
\[
\mathcal Z_N[K\eta;a]
=N^{-\lambda-1}L^{m-1}
\left(E(a)+\frac{D(a)}L+o(L^{-1})\right).
\]

First obtain pointwise statements. Then strengthen the remainders to be uniform on compact subsets of \(U\), using the existing norm-ball isolated-remainder estimates.

**Multiplicity one:** define \(B=0\), but prove the genuinely stronger remainder
\[
\mathcal Z_N[\eta;a]=N^{-\lambda}\bigl(A(a)+o(L^{-1})\bigr),
\]
and similarly for the energy numerator with \(D=0\).

**Inputs:** constant-phase Taylor tree, arbitrary-log-weight isolated remainders, coefficient identifications.

**Traps**
- An \(o(1)\) normalised remainder is insufficient.
- Polynomial uniqueness identifies coefficients; it does not improve a remainder.
- Compact-uniformity must cover the actual Taylor-tree remainder, not merely the isolated piece.
- Convert all powers of \(2\) from \(\log\sqrt N\) before naming \(B\).

This is the main feasibility gate. If compact-uniformity becomes expensive, retain the pointwise theorem and proceed to unit 4.

### 3. Deterministic constant-phase next-log energy

Use coefficient transport—not differentiation of the asymptotic expansion—to prove
\[
E=\frac{\lambda A+(a/2)A'}{\beta},
\qquad
D=\frac{\lambda B-(m-1)A+(a/2)B'}{\beta}.
\]

Then establish
\[
L\bigl(Q_N(a)-c_1(a)\bigr)\longrightarrow c_2(a),
\]
where
\[
c_1(a)=\frac{\lambda}{\beta}
+\frac{a}{2\beta}\frac{A'(a)}{A(a)},
\]
and
\[
\boxed{
c_2(a)=-\frac{m-1}{\beta}
+\frac{a}{2\beta}\left(\frac BA\right)'(a)
}.
\]

Prove the equivalent algebraic form first:
\[
c_2=\frac{DA-EB}{A^2}.
\]

**Inputs:** unit 2, LVI coefficient differentiation, `quotient_second_order`.

**Checks**
- At \(a=0\), recover \(-(m-1)/\beta\).
- For \(m=1\), recover \(c_2=0\), using the strengthened remainder.
- State the theorem on \(A(a)\neq0\); discharge this using unit 1 where possible.

**Non-claim:** no all-orders inverse-log division. No derivative of an \(o(\cdot)\) term is being taken.

### 4. Fixed random constant phase: almost-sure, hence distributional, limits

Let \(X:\Omega\to U\) be measurable, with \(A(X)\neq0\) almost surely. Target
\[
Q_N(X)\longrightarrow c_1(X)\quad\text{a.s.},
\]
and
\[
L\bigl(Q_N(X)-c_1(X)\bigr)\longrightarrow c_2(X)
\quad\text{a.s.}
\]
Consequently both converge in distribution.

**Important simplification:** for a single random variable \(X\), pointwise deterministic convergence composes directly. You do **not** need compact-uniform asymptotics or the leading-quotient-in-distribution machinery.

**Inputs:** measurable parameterised integrals/quotients and measurable coefficient functions. No CLT and no moment assumption on \(X\).

Under the positive face witness, the nonvanishing condition is automatic. A Gaussian \(X\) is an immediate specialisation **only if \(U=\mathbb R\), or the expansion is otherwise established on its almost-sure range**.

**Non-claim:** these results do not imply convergence of expectations over \(X\). That requires uniform integrability.

### 5. Moving random phase: the stronger stochastic headline

Assume \(X_N\Rightarrow X\), with values in \(U\). Using compact-uniform versions of units 2–3, prove
\[
Q_N(X_N)\Rightarrow c_1(X),
\]
and, more importantly,
\[
\boxed{
L\bigl(Q_N(X_N)-c_1(X_N)\bigr)\Rightarrow c_2(X)
}.
\]

An attractive final packaging is the joint limit
\[
\left(Q_N(X_N),
L(Q_N(X_N)-c_1(X_N))\right)
\Rightarrow
\left(c_1(X),c_2(X)\right).
\]

**Inputs:** \(X_N\Rightarrow X\) supplied externally; continuity of \(c_1,c_2\); tightness/localisation. In the globally positive case, compact denominator bounds come from unit 1.

If zeros of \(A\) are allowed, localise inside \(U\cap\{A\neq0\}\), requiring \(A(X)\neq0\) almost surely. Do not assume a global lower bound.

**Critical centring trap:** the next-log theorem centres at **\(c_1(X_N)\)**. Replacing this by \(c_1(X)\), even on a common probability space, requires additional coupling and rate information.

This is my preferred replacement for spending a unit on routine mixed-multiplicity bookkeeping.

### 6. Assembled Laplace limit with explicit residual control

For the zero-phase population model, set \(r=(\beta+t)/\beta\), \(t\ge0\). Prove
\[
\frac{\mathcal Z_{\beta+t}(N)}{\mathcal Z_\beta(N)}
\longrightarrow r^{-\lambda}.
\]

Give two entry points:

1. **Exact full rescaling:**  
   \(\mathcal Z_{\beta+t}(N)=\mathcal Z_\beta(rN)\).

2. **Chart rescaling plus negligible residuals:**  
   the assembled chart sums rescale exactly, while
   \[
   R_\beta(N)=o(N^{-\lambda}L^{m-1}),\qquad
   R_{\beta+t}(N)=o(N^{-\lambda}L^{m-1}).
   \]

Exact rescaling of the residual itself is sufficient, but **not necessary**; negligibility at both temperatures suffices.

With a genuine normalised posterior measure, identify this ratio as
\[
\mathbb E_{\Pi_{N,\beta}}[e^{-tNK}].
\]

**Inputs:** the assembly identity and residual hypotheses remain explicit external inputs.

**Traps:** temperature-dependent amplitudes can break rescaling; fixed-\(\beta\) residual control alone does not control \(\beta+t\); the leading assembled coefficient must be nonzero.

**Non-claim:** this is not yet weak convergence to Gamma.

## Cuts and boundaries

- **(a): keep, highest priority.**
- **(b): keep and strengthen through units 4–5.**
- **(c): defer.** A first derivative at zero is worthwhile, but merely identifying the \(p=1\) term is not a derivative theorem: the higher-\(p\) tail needs a parameter-uniform estimate. It opens a separate functional-analytic branch.
- **(d): drop from this sprint.** Reopen only after locating a usable Mathlib Laplace-continuity theorem for nonnegative laws. Do not turn this into a probability-library project.
- **(e): drop as a headline.** Accept only as a genuinely small corollary of the existing four-statistics interface.
- **(f): keep, last.**

**Stopping rule:** units 1–4 already constitute a complete new deterministic-and-stochastic result. Unit 5 is the best extension; unit 6 is independent. None requires reopening the deferred geometric bridge.
