**Prioritise (a), then (d), then (c).** The existing coefficient machinery appears sufficient for an analytic spatial-phase two-term theorem: the key shortcut is to identify its leading coefficient **by uniqueness of the already-proved continuous-phase limit**, not by repeating LVI’s coefficient calculation. The genuinely new calculation is the second coefficient.

Two corrections to the programme:

- The limiting energy and face location are **generally dependent**, not independent.
- Analytic-phase next-log asymptotics will **not automatically upgrade all of LXXII–LXXVI**: continuous observables and arbitrary uniformly converging phase sequences need stronger hypotheses for rates.

Here is a bounded seven-unit plan.

## 1. Extract the analytic spatial two-term theorem

Assume `cξ`, `cη` satisfy the actual Taylor-tree hypotheses and represent the functions in LXXII. For \(m\ge2\), target
\[
\frac{\mathcal Z_N[\eta;\xi]}{N^{-\lambda}L^{m-1}}
 =F(\xi,\eta)+\frac{B(\xi,\eta)}L+o(L^{-1}).
\]

**Route:**

1. Apply the general-family `TaylorTreeConclusion`.
2. Use the isolated-remainder lemmas to retain \((\lambda,m-1)\) and \((\lambda,m-2)\).
3. Divide by the leading scale.
4. Compare with `spatialPhase_tendsto` to identify the leading coefficient with \(F\).

Thus, **in the expansion’s own normalization**,
\[
B(\xi,\eta)
=\texttt{familySpectralCoeff}(\ldots,c_\xi,c_\eta,\lambda,m-2).
\]

**Assessment of reachability:** yes, on the interfaces described. No new resolution or CLT input is needed. Check that the remainder really is
\(o(N^{-\lambda}L^{m-2})\), and that multiplicity bounds eliminate higher log powers at \(\lambda\). A merely leading-order remainder is insufficient.

For \(m=1\), do not interpret a coefficient indexed by \(-1\). A sufficiently strong spectral-gap remainder instead gives the displayed scaled difference tending to zero.

## 2. Identify \(B\) by a finite-part integral

This is the substantive new theorem.

Here are explicit formulas in the normalization
\[
K(u)=\prod_i u_i^{2k_i},\qquad L=\log N,
\]
with any common chart prefactor multiplying both leading and second coefficients.

Write \(I=J^c\), \(v\in(0,1]^I\), \(w(v)=\prod_{i\in I}v_i^{h_i-2k_i\lambda}\), and
\[
\kappa=\prod_{i\in J}(2k_i)^{-1}.
\]
Let \(e_i(t,v)\) have coordinate \(i\) equal to \(t\), the other \(J\)-coordinates zero, and \(I\)-coordinates \(v\). Put
\[
H(u)=\eta(u)J_\lambda(\xi(u)),\qquad
\dot J_\lambda(a)=
\left.\partial_\nu J_\nu(a)\right|_{\nu=\lambda}.
\]

Then
\[
F=\frac{\kappa}{(m-1)!}\int w(v)H(0_J,v)\,dv,
\]
and the correct second coefficient is
\[
\boxed{
\begin{aligned}
B=\frac{\kappa}{(m-2)!}\Bigg[
&\int w(v)\eta(0_J,v)
 \left(
 2\sum_{\ell\in I}k_\ell\log v_\ell\,
 J_\lambda(\xi(0_J,v))
 -\dot J_\lambda(\xi(0_J,v))
 \right)\,dv\\
&+\sum_{i\in J}2k_i
 \int w(v)\int_0^1
 \frac{H(e_i(t,v))-H(0_J,v)}{t}\,dt\,dv
\Bigg].
\end{aligned}}
\]

A derivation uses the Mellin expression
\[
\mathcal H(z)=
\int u^{h-2kz}\eta(u)J_z(\xi(u))\,du.
\]
If its principal part is
\(A_m(\lambda-z)^{-m}+A_{m-1}(\lambda-z)^{-(m-1)}\),
then \(F=A_m/(m-1)!\) and \(B=A_{m-1}/(m-2)!\).

**Implementation choice:** prove the corresponding coefficient identity within the Taylor-tree framework; do not build a general Mellin-inversion library just for this calculation.

**Trap:** \(B\) is not generally determined by a finite transverse jet. The one-coordinate integrals can depend on the entire analytic restriction to those larger strata. Analyticity makes the subtracted integrals integrable.

## 3. Obtain next-log posterior moments and quotients

For an admissible observable \(g\), define the unnormalised numerator coefficients \(A_{r,g},B_{r,g}\). Their formulas are those above with \(J_z(\xi)\) replaced by
\[
g\,J_{z+r}(\xi).
\]
Subject to the requisite moment and Taylor-tree hypotheses,
\[
L\left(
E_{Q_N^\xi}[(NK)^r g(u)]-\frac{A_{r,g}}{A_{0,1}}
\right)
\longrightarrow
\frac{B_{r,g}A_{0,1}-A_{r,g}B_{0,1}}{A_{0,1}^2}.
\]

In particular, define unambiguously
\[
c_2(\xi)=
\lim_N L\left(E_{Q_N^\xi}[NK]-\mu_\xi\right)
=
\frac{B_{1,1}A_{0,1}-A_{1,1}B_{0,1}}{A_{0,1}^2}.
\]

Also obtain evidence-ratio and energy-Laplace corrections by the same two-term quotient lemma.

**Sanity check:** for zero phase, the standard monomial normalization gives
\[
\mu_0=\lambda/\beta,\qquad c_2(0)=-(m-1)/\beta.
\]

**Non-claim:** this is two-term division only, not the prohibited all-orders programme.

## 4. Separate face and transverse phase effects

Let \(\bar\xi=\xi\circ P_J\), keeping \(\eta\) fixed. Then the first line of the formula for \(B\) cancels, giving
\[
\begin{aligned}
B(\xi,\eta)-B(\bar\xi,\eta)
=\frac{\kappa}{(m-2)!}\sum_{i\in J}2k_i
\int w(v)\int_0^1
\frac{\eta(e_i(t,v))}{t}
\big[
J_\lambda(\xi(e_i(t,v)))
-J_\lambda(\xi(0_J,v))
\big]\,dt\,dv .
\end{aligned}
\]

Deliver three clean consequences:

- Equal face restrictions need **not** imply equal next-log coefficients.
- Equality of the phase restrictions on every stratum \(P_{J\setminus\{i\}}\) **does** imply equality of \(B\).
- With nonnegative amplitude, a nonnegative transverse phase increment gives a nonnegative evidence correction; suitable strict positivity makes it strict.

An example \(\xi=\bar\xi+a u_i\), \(a>0\), demonstrates genuine \(1/L\) transverse sensitivity when \(m\ge2\).

**Trap:** unrestricted continuous observables need not admit this rate; their subtracted \(dt/t\) integrals may diverge. Likewise, uniform phase convergence without a rate does not preserve a second-order coefficient. A perturbation theorem needs appropriate quantitative control, typically including \(o(1/L)\) phase error.

## 5. Complete joint weak convergence—and state dependence correctly

Target
\[
(NK,u)_\#Q_N^\xi\Rightarrow \widetilde Q^\xi,
\]
where \(\widetilde Q^\xi\) is the pushforward of `spatialJointLaw` under
\[
(y,u)\mapsto(y,P_Ju).
\]

Use the established limits for
\[
e^{-ty}g(u),\qquad t\ge0,\quad g\in C(\overline B),
\]
plus energy tightness and compactness of location. A determining-class or subsequential-identification argument suffices.

**State-space trap:** \((0,1]^d\) does not contain the limiting face. Use \((0,\infty)\times[0,1]^d\), or an equivalent explicit compact location space.

The conditional energy law is
\[
\mathcal L(Y\mid V=v)=\rho_{\xi(v)}.
\]
Hence independence holds when \(\xi\) is constant almost everywhere under the limiting face law. Conversely, identifiability of this exponential family gives the same condition as necessary.

That characterization is more valuable than a false general independence claim.

## 6. Random fields: first prove finite-observable convergence

Before `Measure.bind` or random probability measures, target
\[
(X_N,T_N(X_N))\Rightarrow(X,T(X))
\]
for a finite vector \(T_N\) of normalised evidence and bounded posterior observables, conditional on the **external**
\[
X_N\Rightarrow X\quad\text{in }C([0,1]^d).
\]

Internal work:

- continuity/measurability of the finite-\(N\) maps;
- continuity of their face-limit maps;
- convergence uniformly on compact sets of phases, obtained from phase stability and finite nets;
- an extended continuous-mapping argument.

Posterior means can follow after proving the stronger uniform moment bounds they require.

**Non-claims:** no empirical-process CLT is proved; a continuous-field CLT alone supplies neither analytic sample paths nor next-log stochastic asymptotics. Defer the full random-measure packaging.

## 7. Assembly only if needed; report after the new theorem block

Generalise chart assembly once chartwise two-term expansions are available. At next order, charts with the same \(\lambda\) but multiplicity \(m-1\) contribute alongside the \(B\)-terms of multiplicity-\(m\) charts. Omitting them gives the wrong global correction. Charts with larger \(\lambda\) are negligible provided the required remainder control holds.

Keep resolution and partition construction external.

I would **not** allocate a theorem unit to a PDF now. After units 1–4, a short consolidated theorem sheet is worthwhile—but the highest-value next deliverable is the explicit spatial \(B\), its quotient correction, and the transverse-sensitivity theorem.
