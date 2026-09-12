## Verdict

**Programme C is mathematically sound at the scope indicated, and it is a good stopping point.** It establishes useful conditional transfers without pretending that a uniform LLN identifies empirical leading coefficients.

I would nevertheless amend the mirror paragraph. The main issues are:

1. the missing positive-sublevel-mass hypothesis;
2. “on the support” versus the supplied global uniform bound;
3. concentration on *every neighbourhood* requires an additional separation argument, not just the measurable concentration theorem;
4. the final reference to an underived field CLT needs to distinguish this module from the substantial certified empirical-process results already in the library.

I would **not commission programme D**, nor another substantial theorem programme, on the evidence supplied.

This is a statement-level audit, not a verification of the implementation. In particular, the C1 declaration itself was not supplied, and a title index cannot establish that a proposed adapter is absent.

## 1. Audit of the statements

### A. Empirical concentration: correct, with important scope boundaries

The estimates have the right signs and constants. In particular,
\[
\hat K\ge K-e,\qquad \hat K\le K+e
\]
give
\[
\int_{\{K\ge\kappa\}}e^{-n\hat K}\,d\pi
 \le \pi(W)e^{-n(\kappa-e)}
\]
and
\[
\hat Z_n\ge \pi\{K<a\}e^{-n(a+e)}.
\]
Their quotient gives exactly the displayed \(\kappa-a-2e\).

The following hypotheses deserve explicit visibility.

- **Positive mass arbitrarily close to the minimum is essential.**
  ```lean
  hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a}
  ```
  says that the prior sees arbitrarily small values of \(K\). With the other assumptions, it expresses essential infimum zero. It does **not** follow merely from \(K\ge0\), existence of a zero, or a nonzero finite prior.

- **The uniform bound is global in \(w\).** Both `he` and `hunif` quantify over all of `W`, not merely over the prior support or almost everywhere under \(\pi\). This is stronger than the integral arguments intrinsically require. It is an acceptable interface, but the mirror should describe the actual interface.

- **No \(n\|\hat K_n-K\|_\infty\to0\) assumption is needed for concentration.** Ordinary uniform convergence suffices: for each fixed \(\kappa>0\), eventually choose an error small relative to \(\kappa\). This is exactly the useful distinction from fine posterior perturbation.

- **The empirical phases need not be nonnegative.** The hypotheses provide a uniform lower bound, which is enough for finite-prior integrability. This is a legitimate generalisation.

#### Sublevels versus neighbourhoods

`tendsto_gibbsMass_ge` proves concentration in every fixed positive sublevel:
\[
\hat\mu_n\{K\ge\kappa\}\longrightarrow0.
\]

For concentration on every open neighbourhood \(U\) of the zero set, one additionally needs
\[
\inf_{S\setminus U}K>0
\]
on a set \(S\) carrying the prior. Compactness of \(S\), continuity of \(K\) there, and \(U\supseteq S\cap\{K=0\}\) supply this.

Without such a condition, small positive values can occur arbitrarily far from the zero set. Thus the measurable concentration theorem alone does not establish the mirror’s neighbourhood claim.

### B. The probabilistic versions are carefully weaker than a full random-kernel construction

`ae_tendsto_gibbsMass_ge` is a **pathwise theorem**: for almost every sample, apply the deterministic result. It does not require joint measurability in \((\omega,w)\).

`tendsto_measure_gibbsMass_ge` is an **event-measure transfer**. It assumes convergence of the measures of uniform-error events and concludes convergence of the measures of posterior-tail events.

Notably:

- `P` need not be a probability measure;
- measurability of those events is not explicitly assumed;
- Lean measures can be evaluated on arbitrary sets, using their outer-measure extension.

The statement is therefore honestly more general than a conventional measurable-random-variable convergence-in-probability theorem. Calling it the “in-probability version” is reasonable in the intended probability setting, but it should not be advertised as having constructed a measurable empirical posterior from slice measurability alone.

### C. Normaliser transfer is precisely an order-\(n\) result

The sandwich and logarithmic bound are correct:
\[
|\log\hat Z_n-\log Z_n|\le ne.
\]
Under uniform convergence,
\[
\frac{\log\hat Z_n-\log Z_n}{n}\to0.
\]

This does **not** transfer:

- the power–log leading pair;
- a leading coefficient;
- the constant term in the free energy.

An \(o(1)\) phase error can still produce an \(o(n)\) logarithmic-normaliser error much larger than \(\log n\). The current theorem is appropriately limited.

`[NeZero π]` is important here because these are statements about genuine positive normalisers, not Lean’s totalised `Real.log 0`.

### D. Constant-on-minimisers consistency and coefficient consistency

These statements are correct and useful.

`exists_sublevel_of_eq_on_zeroSet` is the right compactness lemma: continuity and constancy on the zero set make \(\phi\) uniformly close to \(\phi_0\) on sufficiently small sublevels.

The expectation theorem then follows from boundedness on compact \(S\) and concentration. It does **not** identify a limiting posterior distribution along the zero set. It only identifies observables that cannot distinguish its points.

The coefficient conclusion is exactly:
\[
a_nZ_n[1]\to c_1>0,\qquad
a_nZ_n[\phi]\to c_\phi
\quad\Longrightarrow\quad
c_\phi=\phi_0c_1.
\]
It does not construct either certificate. Moreover, \(c_\phi\) may be zero. Thus “certificates at a common scale” is safer language than “the same nonzero leading term.”

The condition on \(\phi\) is only on \(S\cap\{K=0\}\), appropriately ignoring prior-null regions outside \(S\).

### E. Gibbs joint ratio: correct, but an algebraic specialisation rather than a new ratio theorem

The essential assumptions are right:

- **joint**, not marginal, convergence;
- a common scaling;
- an almost surely nonzero limiting denominator.

`ha : ∀ i, a i ≠ 0` is slightly stronger than necessary: eventual nonvanishing would suffice. This is harmless and not worth a separate development.

No positivity of \(L_1\) is asserted. That is appropriate because the scaling may be negative.

One important semantic distinction: `tendstoInDistribution_expectation` does **not** itself assume that every source integral defines a genuine Gibbs probability distribution. It requires neither finite/nonzero \(\pi\) nor integrability of every Gibbs weight. As an identity involving Lean’s integrals and totalised division, it remains valid.

Consequently, when describing it as a theorem about actual Gibbs posteriors, retain the surrounding conditions ensuring
\[
0<Z_n[1]<\infty
\]
and integrability of the observable numerator.

The bounded-observable expectation corollary supplies the necessary uniform-integrability mechanism correctly. The degenerate-ratio-law consequence also has exactly the right scope: uniqueness of the distributional limit forces the ratio law to be a point mass.

**Naming:** the Lean names are accurate. The headline “THE JOINT RATIO THEOREM” could suggest novelty relative to `QuotientInDistribution`. “Joint-ratio transfer for empirical Gibbs expectations” would describe the contribution more precisely.

### F. A totalised-integral caveat, especially for C1

`abs_numerator_le` does not assume measurability of \(\phi\). This can still be a correct Lean theorem: a nonintegrable Bochner integrand has integral zero. It should not be interpreted as constructing an ordinary expectation for an arbitrary nonmeasurable observable.

For C1, whose declaration is absent, verify that the mirror retains the requisite measurability/integrability assumptions. In ordinary mathematical language,
\[
\int|R/A-1|\,d\mu<1
\]
is an integrable discrepancy assumption. In Lean, a bare inequality about a totalised real integral does not establish integrability. Presumably C1 handles this; the supplied material does not allow that check.

## 2. Mirror amendments

I would make these targeted changes rather than rewrite the remark.

### Concentration clause

Replace the opening of (b) by something like:

> If \(\pi\) is finite, \(K\ge0\) and \(\hat K\) are measurable, \(|\hat K-K|\le e\) everywhere, and \(\pi\{K<a\}>0\), then the empirical posterior mass of \(\{K\ge\kappa\}\) is at most … . If every positive sublevel of \(K\) has positive prior mass, a hypothesised uniform LLN therefore gives concentration in every fixed positive sublevel. On a compact set carrying the prior, with \(K\) continuous, this implies concentration on every open neighbourhood of the zero set within that set.

This fixes all three substantive omissions without changing the mathematics.

### Perturbation clause

Change:

> “it is not a consequence of a law of large numbers”

to:

> “it is not implied by a uniform LLN alone.”

And change “the empirical coefficient differs” to “the empirical coefficient **can differ**.” The fluctuation-based explanation is reasonable, but it is not a universal consequence of the abstract perturbation theorem.

### Final sentences

Use:

> Whenever the relevant expectations exist and \(\mathbb E L_1\ne0\), the expectation of the ratio, the ratio of expectations, and the population coefficient ratio need not agree. The Gibbs transfer theorem takes the joint numerator–normaliser limit as an input; it does not derive that limit from a statistical model. Earlier certified empirical-process and assembly results provide such inputs under their own hypotheses. Uniform convergence of the empirical phase is likewise an input to the concentration results above.

This matters because CXVI–CXVIII, CLXII–CLXIII, and related units already contain substantial field-limit machinery. Also, a field CLT and convergence of the scaled evidence pair are related but not identical statements: the latter additionally needs the integral/asymptotic and assembly bridges.

## 3. Programme D: do not commission it

**I do not think another one or two units are justified for the paper.**

You already have:

- unconditional exact-monomial box expansions;
- explicit leading coefficients and residual-face formulas;
- second-order logarithmic expansions;
- concrete equal- and unequal-exponent regressions;
- normal moments and coefficient ratios.

An exact constant-unit kernel formula would be a useful analytic regression, but it would not remove a remaining headline hypothesis or establish a missing paper conclusion.

There is also a scope trap in the proposed title. A finite-box kernel is generally **not exactly a finite power–log polynomial**. Even
\[
\int_0^1 e^{-Nx}\,dx=\frac{1-e^{-N}}N
\]
retains an exponential boundary term. A correct exact formula uses incomplete Gamma/log-moment integrals, or a power–log expression **plus an explicitly retained tail**. Establishing that identity is respectable, but its marginal value here is low.

Keep D as an optional maintenance/regression task, not a completion requirement.

## 4. Remaining high-value theorems and closure

**I cannot identify a genuinely high-value missing theorem from this index and these statements. My recommendation is to close the formalisation at this point.**

The two apparent directions do not justify another programme:

- **A certified-sample-to-actual-Gibbs endpoint.** If an existing common-sample joint assembly result already produces exactly the scaled numerator and normaliser required here, composing it with CCLXXXIX could make a useful user-facing theorem. Its statement would conclude the Gibbs ratio law and, for bounded observables, convergence of dataset expectations from the existing sample/chart certificate package. The proof would be existing joint assembly, integral identification, then `tendstoInDistribution_expectation` and `tendsto_integral_expectation`. Budget: roughly **one short adapter unit**, only if all those interfaces already align. But the index contains several closely related endpoints; absence is not established, and this is packaging rather than a new major theorem.

- **An unconditional empirical theorem from broad paper-level assumptions.** This would require deriving the relevant analytic sampling certificates, resolved empirical-process control, and joint assembly compatibility—not merely adding another continuous-mapping wrapper. That is a separate research programme, not a one- or two-unit finishing task.

I would therefore spend the remaining effort on the mirror corrections, an exported-signature audit of the headline theorems, and a clear release map separating unconditional geometry/population results from certificate-dependent empirical results. **There is no mathematical need to reach CCLXXXX.**
