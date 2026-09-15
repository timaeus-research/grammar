## Verdict

**Ranks 3–5a form a coherent, paper-worthy conditional empirical asymptotics theorem.** They do not yet prove empirical asymptotics for a specified statistical model, nor convergence of annealed expectations. The mirror mostly respects that distinction.

My principal recommendations are:

1. Add the measurability assumption on the empirical partition function to the paper statement.
2. Qualify the claim that the divisor variance is \(2\): this is the standard **realizable likelihood normalization**, not a universal singular-learning identity.
3. Treat varying variance as the natural next local extension.
4. Do not make a functional CLT or annealed convergence a prerequisite for closing the current paper-facing programme.

This is a mathematical audit of the supplied statements, not a source-level verification of commit `58765f6`.

## (a) Audit of the three statements

### 1. `tendstoUniformlyOn_tupleZ`

The architecture is correct:

- fixed-field convergence;
- Lipschitz estimates uniform over bounded sets of fields, eventually in \(N\);
- compact sets are bounded and admit finite \(\varepsilon\)-nets;
- the limit inherits the same Lipschitz estimate on each such bounded set.

The constant \(e^{M^2}\) in the exponential estimate is valid. In particular,
\[
\sigma M\le \frac{\sigma^2}{4}+M^2,
\qquad
\sup_{\sigma\ge0}\sigma e^{-\sigma^2/4}
=\sqrt{2/e}<1.
\]
There is no need to optimize that constant for rank 3.

The use of the zero-field integral at \(N/2\) is also right. Its normalization remains bounded because the scale ratio at \(N/2\) and \(N\) converges to a finite constant. Positivity of the normalizing scale is needed only eventually; small \(N\), including \(0\) and \(1\), is irrelevant.

The branch-tuple construction is particularly sound: clamping gives an extension without requiring an extension theorem, preserves the values relevant to the integrals, and permits a clean sup-norm estimate.

**Important semantic qualification:** `ChartLeading` supplies a permissible normalization, not necessarily a sharp one. If \(\lambda\) is strictly below every chart ratio, or \(m\) is larger than the actual maximal multiplicity, the limit can be zero. Even at sharp geometric exponents, a signed insertion can cancel. Consequently, the paper should state **normalized convergence**, not automatically
\[
Z_n\sim T(G)s_n
\]
with a nonzero coefficient.

### 2. `tendstoInDistribution_empZ_div`

This is the correct extended continuous-mapping argument followed by a negligible-tail Slutsky step. The hypotheses account for three genuinely different issues:

1. joint weak convergence of the chart fields;
2. compact-uniform deterministic asymptotics;
3. probabilistic control of the field on the tail complement.

The third does not follow just from convergence of the branch tuple: that tuple need not control the field on the tail.

#### (i) Measurability of `empZ`

**It is entirely acceptable as a hypothesis.** A measurable-space structure on `RootField` is not required when the theorem assumes measurability of the actual observables it uses.

Moreover, measurability of the tuple alone does **not** generally imply measurability of `empZ`: the latter also sees the tail.

I would retain the present theorem and add a convenience result later:

> Under suitable joint measurability of  
> \((\omega,Q)\mapsto(\xi_n(\omega)).\psi(Q)\), and the deterministic measurable/integrable data, the map \(\omega\mapsto\operatorname{empZ}(\xi_n(\omega),n)\) is measurable or a.e. measurable.

One must distinguish joint measurability from merely having a measurable section in \(Q\) for each \(\omega\).

**The mirror currently needs a correction:** its displayed assumptions mention measurable tuples but omit the separate `hZm` assumption. Add “assume also that the empirical partition functions are a.e. measurable,” unless an earlier blanket assumption already supplies this.

#### (ii) Tightness

Yes: in the stated setting, the explicit tightness hypothesis is mathematically redundant.

Each \(C(K_p,\mathbb R)\), for compact metric \(K_p\), is a separable Banach space. The finite product \(E\) is therefore Polish. A weakly convergent sequence of Borel probability measures on a Polish space is uniformly tight, including its finitely many initial terms.

The general rank-4 transfer theorem should keep its explicit tightness hypothesis: its ambient space is more general. For the specialized branch-tuple theorem, a Polish-space corollary can remove it.

Is proving this worth doing? **Yes as reusable probability infrastructure, but not as a blocker.** First check whether Mathlib already has the result under a differently packaged formulation. If not, prove it generally rather than inside the empirical development. Until then, write:

> “…with uniformly tight laws; this hypothesis is redundant mathematically in the present Polish space but is retained explicitly in the formal theorem.”

#### (iii) \(M_n\ge0\), \(M_n=O_p(1)\)

The formulation is right, with two qualifications.

- The displayed tail condition is **asymptotic boundedness in probability**, which is exactly what is needed. Uniform control of every \(n\) is unnecessary.
- Calling \(M_n\) a “random variable” ordinarily includes measurability. Your formal lemma appears not to require it, because measures of arbitrary sets can support an outer-probability formulation.

For the paper, the clean choice is simply to assume that \(M_n\) are measurable nonnegative random variables satisfying
\[
|\psi_n(Q)|\le M_n\quad\text{for every }Q,
\qquad M_n=O_p(1).
\]
This is a slightly more conventional specialization of the formal result. Otherwise explicitly say “bounded in outer probability.”

### 3. `integral_tupleLimit_gaussian`

The expectation calculation is correct. It uses:

- joint measurability of evaluation;
- Gaussian exponential moments;
- integrability of the deterministic residue weight;
- absolute-integrability/Fubini arguments for the signed amplitude.

No independence is required. Indeed, **joint Gaussianity is not required either**: Gaussian one-point marginals suffice for this expectation identity.

The common variance assumption is substantially stronger than necessary in two ways:

1. only points on the **active leading faces** affect \(T\);
2. their variances need not agree.

Thus the natural extension is exactly the one you propose. Write
\[
\rho_p=\nu_p\otimes
\left(\mathrm{vol}\!\restriction (0,b_p]^{J_p^c}\right),
\]
and let \(a_p(z)\) include the amplitude, residue weight, and face constant. For active pieces, suppose
\[
G_p(z)\sim N(0,v_p(z)),\qquad
0\le v_p(z)\le 2-\varepsilon.
\]
Then
\[
\mathbb E T(G)
=
\Gamma(\lambda)
\sum_{p\ \mathrm{active}}
\int a_p(z)\,
       (1-v_p(z)/2)^{-\lambda}\,d\rho_p(z).
\]

Require the variance profiles to be measurable, or obtain that measurability from a suitable covariance-kernel hypothesis. A uniform gap makes absolute integrability immediate from \(a_p\in L^1\).

The more general hypothesis is
\[
\int |a_p(z)|(1-v_p(z)/2)^{-\lambda}\,d\rho_p(z)<\infty,
\]
with \(v_p<2\) a.e. on the relevant weighted faces. **Implement the uniform-gap version first.**

For actual statistical limits, constant variance is natural in some realizable normalizations, but not in general misspecified models. Conversely, variation away from the divisor is irrelevant if the active face variance is constant.

## (b) The factor, tempering, and the critical case

Your scalar normalization gives
\[
S_\lambda(a)=\int_0^\infty
t^{\lambda-1}e^{-t+a\sqrt t}\,dt.
\]
If \(X\sim N(0,v)\), Tonelli yields
\[
\mathbb E S_\lambda(X)
=
\int_0^\infty t^{\lambda-1}e^{-(1-v/2)t}\,dt
=
\Gamma(\lambda)(1-v/2)^{-\lambda},
\]
provided \(\lambda>0\) and \(v<2\).

For \(v\ge2\), that expectation is infinite.

### Temperature bookkeeping

For the tempered kernel
\[
e^{-\beta t+\beta a\sqrt t},
\]
the corresponding expectation is
\[
\Gamma(\lambda)
\bigl[\beta(1-\beta v/2)\bigr]^{-\lambda},
\qquad \beta v<2.
\]
Relative to its zero-field value \(\Gamma(\lambda)\beta^{-\lambda}\), the multiplier is
\[
(1-\beta v/2)^{-\lambda}.
\]

Thus, when the underlying normalized variance is \(v=2\), the finite-mean threshold is \(\beta<1\). Equivalently, after absorbing temperature into the phase scale and field, the effective variance is \(\beta v\).

### Is the natural divisor variance \(2\)?

**In the standard realizable likelihood setting, under the usual regularity and continuous-extension assumptions: yes. Not universally.**

With log likelihood ratio \(f(x,u)\), \(K(u)=\mathbb E f(x,u)\), and normalized fluctuation based on \(f/\sqrt K\),
\[
v(u)=\frac{\operatorname{Var}(f(x,u))}{K(u)}.
\]
Realizability gives the local identity
\[
\mathbb E f^2=2K+o(K)
\]
as the model approaches the true distribution. Consequently the continuous normalized variance on the zero divisor is \(2\).

In a misspecified setting, the analogous variance/curvature ratio need not equal \(2\), and may vary by direction. A covariance kernel by itself does not settle which case applies.

### What follows about finite-sample expectations?

The current results imply only:

- \(Z_n^{\mathrm{emp}}/s_n\Rightarrow T(G)\);
- under the variance gap, \(T(G)\in L^1\) and its expectation has the stated value.

They do **not** imply
\[
\mathbb E[Z_n^{\mathrm{emp}}/s_n]\longrightarrow\mathbb E T(G).
\]
That needs uniform integrability, or another argument directly controlling expectations.

The critical case illustrates why the distinction matters. In the realizable, common-support likelihood-ratio setting at \(\beta=1\),
\[
\mathbb E\exp\!\left(-\sum_{i=1}^n
\log\frac{q(X_i)}{p(X_i,u)}\right)=1.
\]
Hence, for a nonnegative insertion,
\[
\mathbb E Z_n^{\mathrm{emp}}[F]=\int F\,d\mu_U.
\]
Its normalized expectation therefore diverges when that integral is positive and \(s_n\to0\). Rare samples dominate the annealed quantity.

Likewise, if the leading face weights are nonnegative and nontrivial and their variance is \(2\), Tonelli gives \(\mathbb E T(G)=+\infty\). For **signed** insertions, do not assert this without qualification: cancellations can change the conclusion, and integrability must be analyzed separately.

## (c) Honest status of the functional CLT

At present the statistical input is an **external, substantive hypothesis**. Chartwise scalar CLTs, or even convergence of every finite collection of evaluations, are not by themselves a functional CLT.

A direct Lean proof would need:

1. construction and measurability of the empirical branch tuple as an \(E\)-valued random element;
2. joint finite-dimensional convergence, including cross-chart covariances;
3. tightness/asymptotic equicontinuity in the sup norm;
4. identification of a continuous limiting random field;
5. separate control of the global root-field bound needed for the tail.

A Kolmogorov–Chentsov route is possible if sufficiently strong **uniform-in-\(n\)** increment moment estimates are available. A compact parameter set and pointwise CLTs alone are not enough.

The analytic-certificate route may be a better fit for this repository. If the chart fields admit a common coefficient representation with:

- a CLT in the appropriate weighted \(\ell^1\) coefficient space;
- a continuous reconstruction map into the finite product of \(C(K_p)\);
- certified summability and uniform remainder control;

then the continuous mapping theorem can deliver the functional CLT. Existing `L1SeqCLT` could make that route considerably more economical than developing general empirical-process tightness.

The key audit question is whether the existing certificate controls the **joint random coefficient sequence in the norm required for uniform reconstruction**. Analyticity of each sample path alone is not sufficient.

I would rank this as the largest statistical extension, below paper closure and the local expectation refinements.

## (d) Recommended next work

Sizes below are architectural estimates, not repository-level task estimates.

| Priority | Work | Size / recommendation |
|---|---|---|
| 1 | Freeze the present scope and finish paper-facing statements | **Small.** Do now. Include `hZm`, conditional statistical input, and the nonzero-limit qualification. |
| 2 | Varying-variance expectation on active faces | **Small–medium**, plausibly a few modules. Best immediate mathematical extension. |
| 3 | Polish tightness corollary and measurability convenience theorem | **Small–medium**, depending on existing Mathlib support. Improve usability without changing the core result. |
| 4 | Geometric/exponent bridge and stratum identification | **Medium to large.** Prioritize if needed to identify the theorem with the paper’s invariant formulation. |
| 5 | Conditional annealed theorem from UI | **Small** abstractly; **medium** for a useful exponential-envelope criterion. Optional for this paper. |
| 6 | Model-derived functional CLT and tail tightness | **Large to very large.** A separate statistical programme unless the analytic certificate nearly closes it already. |

Two cautions about this ordering:

### The `ChartLeading ↔ IsExtremalData` bridge

Do not target an unqualified equivalence if `IsExtremalData` asserts actual extremality. `ChartLeading` permits strictly subleading choices and overlarge multiplicities.

A sharp bridge needs attainment conditions identifying:

- \(\lambda\) with the minimum chart ratio;
- \(m\) with the maximal multiplicity among charts attaining that minimum.

Even sharp geometric data do not prevent cancellation for a particular signed \(F\).

### The annealed/UI criterion

A useful sufficient hypothesis is stronger than \(M_n=O_p(1)\). For \(0<a<1\),
\[
-t+M\sqrt t\le -at+\frac{M^2}{4(1-a)}.
\]
Together with an eventually bounded normalized deterministic positive envelope, this suggests a sufficient \(L^p\) condition
\[
\sup_{n\ge n_0}
\mathbb E\exp\!\left(
\frac{pM_n^2}{4(1-a)}
\right)<\infty
\quad\text{for some }p>1.
\]
That gives UI of the normalized partition functions.

State the required coefficient explicitly: “uniform exponential moments of \(M_n^2\)” without specifying their strength is insufficient. Such a global supremum criterion can also be much stronger than the facewise condition \(v<2\). Its failure would not disprove annealed convergence.

## Suggested paper theorem

> **Conditional empirical leading asymptotics.** Fix a finite resolved chart transport, an insertion \(F\), and exponents \(\lambda>0\), \(m\ge1\) satisfying `ChartLeading`. Let \(\psi_n\) be bounded root fields whose continuous branch tuples \(\widehat\psi_n\) are measurable random elements of \(E=\prod_p C(K_p,\mathbb R)\), and assume that the empirical partition functions are a.e. measurable. Suppose \(\widehat\psi_n\Rightarrow G\) jointly in \(E\), with uniformly tight laws, and that measurable nonnegative bounds \(M_n\ge\sup_U|\psi_n|\) satisfy \(M_n=O_p(1)\). Then
> \[
> \frac{Z_n^{\mathrm{emp}}[F;\psi_n]}
> {n^{-\lambda}(\log n)^{m-1}}
> \Rightarrow T(G),
> \]
> where \(T\) is the continuous resolved leading-face functional. If every one-point marginal of \(G\) is \(N(0,v)\) for a common \(v<2\), then \(T(G)\) is integrable and
> \[
> \mathbb E T(G)=(1-v/2)^{-\lambda}T(0).
> \]
> No independence of field values is assumed. The theorem neither establishes the functional convergence from a statistical model nor asserts convergence of finite-sample expectations; the latter requires additional uniform-integrability control.

**Bottom line:** close ranks 3–5a as a successful conditional empirical theorem. Add varying variance if it remains local. Do not let the genuinely larger functional-CLT problem turn this completed analytic/probabilistic transfer result into an indefinitely unfinished programme.