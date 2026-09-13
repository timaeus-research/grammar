## Decision

**Accept the model test and Rank 5 as reported. Close the companion-note programme without the thin quartet or the kernel double-series identification.**

The only required changes are small wording clarifications, not additional Lean results. This is a review of the supplied signatures and passages, not an independent audit of checkout `a19cc7e`.

The stopping boundary is mathematically sound:

- The normal-location test **discharges the predictive-remainder input**, including its training version.
- Rank 5 **constructs the missing Gaussian-law/synthesis adapter** from the ℓ¹ CLT.
- Neither result supplies the remaining model-specific expected-error transfers.

## 1. Model test and Rank 5: acceptance and wording

### Model test — accepted

The proof has the intended shape: posterior identification, control of tilted centred third moments, measurable remainder, and an integrable envelope whose expectation has the required rate. Keeping \(C_3,C_6\) symbolic is entirely appropriate.

The marginal-law hypothesis is a strength, not a defect. In particular, the training result genuinely permits the evaluation point to be one of the observations used in the posterior.

Two wording refinements:

1. **Identify the data-law regime explicitly.** The model family is \(N(w,1)\), but the displayed expectation certificates concern standard-normal marginal data, i.e. the \(w=0\) marginal regime.
2. **Do not let “the normal-location case is formalised” suggest that the entire expected quartet is formalised.**

Replace the trailing paragraph after the general remainder proposition with:

> The general discharge of this predictive-remainder input in a statistical model is not formalised. The following proposition discharges it in the normal-location model with fixed positive prior precision and inverse temperature, for both an additional evaluation point and the empirical training average. It does not supply the other expected-error transfers.

In the new proposition, I suggest:

> Fix \(a>0\) and \(\beta>0\). Suppose the observations \(X_i\) and an additional evaluation point \(X^*\) are defined on a common probability space and each has law \(N(0,1)\). No independence assumptions are imposed.

The rest of the quoted proposition is correctly scoped. Calling \(X^*\) an **additional evaluation point** avoids giving “test point” an implicit independence meaning.

### Rank 5 — accepted

This is a substantive completion of the adapter, not merely another abstract constructor:

- The ℓ¹ CLT supplies a limit law.
- That law is proved Gaussian as a Banach-space measure.
- The continuous synthesis map transports it to \(C(K)\).
- The field constructor is actually instantiated.
- The existing compact-base identity becomes available under its other hypotheses.

Defining the kernel from the field is the right mode here. The `rfl` covariance certificate is not a weakness: the substantive work lies in constructing the Gaussian law and synthesis map and establishing the kernel’s regularity.

There is one proof-description correction. The bound
\[
|L(T_Fa)|\leq \|L\|\|a\|_1
\]
alone explains first-moment domination, but second moments need its square. Replace the relevant sentence by:

> Finite truncations are Gaussian. Along a covering exhaustion, \(L\circ T_{F_k}\to L\) pointwise; the bounds \(\|L\|\|a\|_1\) and \(\|L\|^2\|a\|_1^2\), together with the square-integrability supplied by summable coordinate \(L^2\) norms, permit passage of first and second moments. Characteristic functions pass by bounded convergence, giving the Gaussian Banach law.

Also make centring explicit:

> The limit is centred: every continuous linear functional has mean zero.

**Kernel terminology caveat:** for a general square-integrable measure, `synthesisKernel` defines a **second-moment kernel**. It is a covariance kernel in the centred setting used by `ofL1TaylorLimit`. Your quoted paragraph concerns that centred setting and is correct; retain that qualification in any standalone API description.

## 2. Thin quartet: choose (b)

**Close with the remainder theorem. Do not make `normalLocation_expected_quartet` a closure requirement.**

The two-sign normalisation does pass a short mathematical sanity check. This is useful to record internally, but it is not the missing formal adapter.

For \(n\geq1\), put
\[
u=\sqrt n\,w,\qquad Z_n=\frac1{\sqrt n}\sum_{i<n}X_i,\qquad t=u^2/2.
\]
Then
\[
\sum_{i<n}f(X_i,w)=t-Z_nu,
\]
and the two branches \(u=\pm\sqrt{2t}\) give
\[
\lambda=\tfrac12,\qquad
g_n=(\sqrt2 Z_n,-\sqrt2 Z_n),\qquad
\rho=(\tfrac12,\tfrac12).
\]
Any common strictly positive weight gives the same ratios. The branch Jacobian is proportional to \(t^{-1/2}\).

For the reference integrals defining the quartet, the corresponding \(u\)-law is
\[
N(Z,\beta^{-1}).
\]
Consequently, with
\[
b=\begin{pmatrix}2&-2\\-2&2\end{pmatrix},\qquad c=2,
\]
the normalisations are
\[
M_2=\frac{Z^2+\beta^{-1}}2,\qquad H=Z^2,\qquad
Q=Z^2,\qquad V=\beta^{-1}.
\]
Thus
\[
\operatorname{bayesCombination}
=
\left(
\frac{Z^2+\beta^{-1}}2,\,
\frac{\beta^{-1}-Z^2}2,\,
\frac{Z^2}2,\,
-\frac{Z^2}2
\right).
\]
For \(Z\sim N(0,1)\), its expectation is `bayesValue` with \(\lambda=\tfrac12\) and scalar Bayes parameter \(\nu=\tfrac12\).

**But this is the reference quartet, not an exact finite-\(n\) posterior identification.** The actual prior contributes
\[
e^{-at/n},
\]
so the finite-\(n\) rate is \(\beta+a/n\), while the linear coefficient remains \(\beta g_n\). Relating the actual errors and variance correction to the reference quartet still requires the model-specific calculations and \(L^1\) transfers.

Moreover, standard-normal marginal laws alone do **not** give \(Z_n\Rightarrow N(0,1)\). A conventional iid quartet theorem would introduce assumptions absent from—and unnecessary for—the remainder theorem.

Suggested exact non-claim:

> The normal-location result verifies only the predictive-remainder transfer. The two-sign identification with the fluctuation-function quartet, the Gibbs and variance-correction \(L^1\) transfers, and a model-level expected-quartet theorem are not formalised.

A future complete thin instantiation looks like **roughly 2–4 units**, depending on the existing finite-dimensional error API and change-of-variables lemmas. That is a planning estimate, not a one-unit closure task.

## 3. Kernel identification: stop at field covariance

**Not worth adding as a closure unit.**

The double-series theorem would improve coefficient-level interpretation, but it unlocks none of the stated compact-base conclusions: those already operate on the constructed field and its continuous PSD covariance kernel.

If later undertaken, distinguish the two statements:

- For a general square-integrable law:
  \[
  C(y,z)=\sum_{r,s}\mathbb E[a_ra_s]\phi_r(y)\phi_s(z).
  \]
- For the centred law:
  \[
  C(y,z)=\sum_{r,s}\operatorname{Cov}(a_r,a_s)\phi_r(y)\phi_s(z).
  \]

The summable coordinate \(L^2\) bounds provide the natural absolute-summability argument. Nevertheless, the double-sum/integral interchange and its API can consume time disproportionate to the conceptual content.

**Optional estimate:** 1–2 units, not a guaranteed single unit. Keep it deferred until a downstream result needs coefficient covariances.

Your present non-formalisation sentence is appropriate.

## 4. Closure checklist and final ledger wording

Applying the constructed/consumed, convergence, sampling, and parameter checks:

| Item | Final ledger wording |
|---|---|
| **Normal-location construction** | Constructs the tempered Gaussian posterior and proves a measurable predictive-remainder bound for the excess loss \(f(x,w)=w^2/2-xw\). |
| **Remainder convergence** | For fixed \(a>0,\beta>0\), proves \(n\mathbb E|R_n(X^*)|\to0\) and \(n\mathbb E[(1/n)\sum_{i<n}|R_n(X_i)|]\to0\). These are absolute-moment certificates, not merely convergence of signed expectations. |
| **Sampling assumptions** | Requires only standard-normal marginal laws on a common probability space; independence is not used. The training evaluation points may be the observations forming the posterior. |
| **Expected-error interface** | Consumes model-specific Gibbs, variance-correction, and predictive-remainder \(L^1\) transfers. Only the predictive-remainder transfer is supplied here for normal location. A raw-core limit supplies none of these transfers by itself. |
| **ℓ¹ CLT law** | Constructs a centred Gaussian limit law for the library’s centred empirical sums under the stated independence, identical-distribution, measurability, and summable coordinate \(L^2\) hypotheses. Convergence is in distribution. |
| **Synthesis and field** | Given a uniformly bounded continuous basis on the stated compact metric base, constructs a bounded linear synthesis map and a centred Gaussian field under the ℓ¹ limit law. Its kernel is defined by field second moments and hence is its covariance kernel. |
| **Compact-base identity** | Instantiates the existing Gaussian-field interface; the compact-base identity applies under its remaining parameter and measure hypotheses. |
| **Not supplied** | No Gaussian law constructed from a prescribed kernel alone; no coefficient-covariance double-series identification; no instantiation with the statistical model’s chart data; no normal-location expected-quartet theorem. |

Additional parameter guardrails:

- The remainder rate is for **fixed** positive \(a,\beta\), not a uniform result over varying temperatures or prior precisions.
- Measurability is asserted in \((m,x)\) **for fixed variance**.
- The synthesis result consumes the uniform basis bound; it does not establish that bound for arbitrary chart data.
- The ℓ¹ CLT is not an \(L^1\) coupling theorem, and the Gaussian-field adapter does not convert weak convergence into expected-error convergence.

The quoted interface-table changes are acceptable. I would use the explicit three-transfer wording above in preference to “all three inputs,” which otherwise requires readers to recover the antecedent.

### Exact closing sentence

> This closes the companion-note programme at the stated conditional interfaces, with the normal-location predictive-remainder input and the bounded-basis ℓ¹ Gaussian-field construction supplied; no model-level expected quartet or general discharge of the statistical-model inputs is claimed.

## Ranked remaining units

1. **Required: wording and ledger pass only — less than one unit.** Apply the centring/second-moment clarification, explicitly delimit the normal-location remainder claim, and retain the fixed-parameter and sampling qualifications. Keep both documents aligned to the audited pin.
2. **No required Lean units.**
3. **Deferred, only on downstream demand:** thin normal-location quartet, approximately 2–4 units.
4. **Deferred, only on downstream demand:** coefficient-covariance kernel series, approximately 1–2 units.

**Programme status: accepted for closure after the wording pass.**
