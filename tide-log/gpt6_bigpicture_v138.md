## Executive verdict

The proposed direction is valuable, but three corrections are essential:

1. **A stratum coefficient is not automatically a leading asymptotic.** E1’s normalised integral generally diverges if lower exponents contribute. The population graded-stratum theorem identifies a coefficient, not necessarily the limit of the whole integral.
2. **Convergence of the field only on \(Z_0\) is insufficient.** One also needs control of its oscillation towards \(Z_0\) on the shrinking integration region. Convergence in \(C\) on a compact neighbourhood is a clean sufficient hypothesis.
3. **The signed-monomial convention matters.** Watanabe’s \(u^k\xi(u)\) need not equal \(\sqrt K\,\xi(u)\). On a signed resolution, the answer may require a sum over normal-side branches, not \(S_\mu\) of a single field on the underlying stratum.

After these corrections, the **leading, zero-order empirical theorem should be stated without analyticity**. The analytic Taylor-data theorem should remain the theorem for full expansions and ordered remainders.

My principal formalisation recommendation is to insert a **marked radial-limit theorem** between the population engine and the empirical theory. It can reuse the population leading theorem and avoid rebuilding the entire face calculation.

---

## 1. Normalisations and conventions

Use
\[
S_{\mu,\beta}(a)
 :=\int_0^\infty t^{\mu-1}e^{-\beta t+\beta a\sqrt t}\,dt,
 \qquad \mu,\beta>0.
\]
Then
\[
S_{\mu,\beta}(0)=\Gamma(\mu)\beta^{-\mu},
\qquad
\partial_a^pS_{\mu,\beta}(a)
 =\beta^pS_{\mu+p/2,\beta}(a).
\]

Keep the population measure \(\nu^\mu_c\) normalised at temperature \(1\):
\[
\nu^\mu_c=\frac{\Gamma(\mu)}{(c-1)!}\,\mathcal R^\mu_c.
\]
For a genuinely scalar nonnegative-root field, the empirical measure is therefore
\[
\boxed{
\nu^\mu_{c,\beta}(\xi)
 =\frac{S_{\mu,\beta}(\xi)}{\Gamma(\mu)}\,\nu^\mu_c
 =\frac{S_{\mu,\beta}(\xi)}{(c-1)!}\,\mathcal R^\mu_c .
}
\]
In particular,
\[
\nu^\mu_{c,\beta}(0)=\beta^{-\mu}\nu^\mu_c.
\]

There is no additional \(\beta^{-\mu}\) outside \(S_{\mu,\beta}\).

### The signed-monomial issue

In a signed chart,
\[
u^k\xi(u)=|u^k|\bigl(\operatorname{sgn}(u^k)\xi(u)\bigr).
\]
The effective nonnegative-root field is thus
\[
\widehat\xi=\operatorname{sgn}(u^k)\xi.
\]
It need not extend continuously across the divisor on the ordinary resolution manifold. It does extend branchwise in the usual normal-crossing setting.

A decisive regression is \(K(x)=x^2\) on a two-sided neighbourhood, with constant signed field \(a\):
\[
\sqrt N\int \phi(x)e^{-Nx^2+\sqrt Nxa}\,dx
 \longrightarrow \sqrt\pi\,\phi(0)e^{a^2/4}.
\]
The two normal sides contribute
\[
\frac{\phi(0)}2
 \bigl(S_{1/2,1}(a)+S_{1/2,1}(-a)\bigr),
\]
not \(\phi(0)S_{1/2,1}(a)\).

For a global statement, either:

* work on nonnegative orthants with compatible branch data; or
* use a normal-side/oriented resolution \(\widehat U\), with projection \(p\), a lifted residue measure \(\widehat\nu\), and a continuous effective field \(\widehat\xi\).

Then the intrinsic measure on \(U\) is
\[
\boxed{
\nu_{\beta}(\widehat\xi)
 =p_*\!\left(
    \frac{S_{\mu,\beta}(\widehat\xi)}{\Gamma(\mu)}
    \widehat\nu
   \right),\qquad p_*\widehat\nu=\nu .
}
\]
It is still absolutely continuous with respect to \(\nu\), but its density can be a weighted average over branches. It need not be \(S_{\mu,\beta}\) of one scalar field on \(U\).

This convention should be settled before global assembly.

---

## 2. Audit of E1–E6

### E1 — Correct for a leading stratum, not as stated for arbitrary \((\mu,c)\)

The proposed constant is correct at \(\beta=1\), subject to the branch convention. But the hypotheses do not exclude contributions
\[
N^{-\lambda}(\log N)^q,\qquad \lambda<\mu.
\]
Vanishing near \(D_{c+1}\) does not exclude these: they may arise on shallower strata.

Thus distinguish:

* **Coefficient theorem:** identifies the graded coefficient indexed by \((\mu,c-1)\).
* **Leading-limit theorem:** identifies the normalised whole integral after proving that no asymptotically larger terms contribute.

For the latter, require that \((\mu,c)\) is the leading pair on the support under consideration. A convenient chartwise sufficient condition is:

* every active exceptional ratio is at least \(\mu\);
* the maximum number of simultaneously active \(\mu\)-resonant divisors is \(c\);
* the top contribution is zero order;
* compact-support/local-finiteness hypotheses give finite relevant measures.

The global extremal pair is the natural first application. A merely continuous field should **not** be advertised as giving arbitrary higher coefficients after subtraction.

Under this leading-pair hypothesis, your limit is right:
\[
N^\mu(\log N)^{-(c-1)}
 \int F e^{-\beta NK+\beta\sqrt{NK}\xi}\,d\mu_U
 \longrightarrow
 \frac1{(c-1)!}\int_S F S_{\mu,\beta}(\xi)\,d\mathcal R^\mu_c.
\]

#### Corners and the hyperbola ends

Yes, the result survives for \(c\ge2\). The ends are lower-order at the top logarithmic scale. But the suggested \(N^{-\varepsilon}\) argument needs correction:

* the region where some \(u_j>N^{-\varepsilon}\) generally occupies an \(O(\varepsilon)\) fraction of the logarithmic simplex;
* it is not an \(O(1)\)-width boundary layer.

A cleaner proof fixes \(\delta>0\):

1. On \(u_j\le\delta\) for all resonant \(j\), freeze the field using its modulus of continuity.
2. A region with some resonant \(u_j>\delta\) loses one logarithmic degree, with constants depending on \(\delta\).
3. Send \(N\to\infty\), then \(\delta\downarrow0\).

For \(c=1\), treat the complement directly rather than interpreting a negative logarithmic degree.

#### Continuity assumptions

Continuity on a compact closed chart is enough; no Hölder hypothesis is needed for convergence. More precisely, what matters is a uniform approach to the face trace:
\[
\sup_{\operatorname{dist}(x,S)\le\delta}
 |\xi(x)-\xi(\text{corresponding face point})|\to0,
\]
on the relevant local pieces.

**Continuity of the restriction to \(Z_0\) alone says nothing about this approach.**

Uniformity on bounded equicontinuous families on compact chart neighbourhoods is appropriate. A Hölder modulus is useful for an explicit rate, but does not by itself make the logarithmic boundary error disappear.

**Verdict:** promote the corrected *leading* version; do not state E1 at arbitrary indices.

---

### E2 — Correct

For \(\|\xi\|_\infty,\|\zeta\|_\infty\le M\),
\[
|L_{\beta,F}(\xi)-L_{\beta,F}(\zeta)|
 \le
 \frac{\sup_{|a|\le M}\beta S_{\mu+1/2,\beta}(a)}
      {\Gamma(\mu)}
 \left(\int |F|\,d\nu^\mu_c\right)
 \|\xi-\zeta\|_{\infty,S}.
\]
The coefficient depends only on the face trace, or on the branchwise face trace in the signed setting.

One can strengthen this to local Lipschitz continuity of the finite empirical measures in total variation:
\[
\|\nu_\beta(\xi)-\nu_\beta(\zeta)\|_{\mathrm{TV}}
 \le C_M\,\nu(U)\|\xi-\zeta\|_\infty .
\]

**Verdict:** a small, useful next theorem. Keep it separate from the much harder asymptotic theorem.

---

### E3 — The limit is right, but \(C(Z_0)\)-convergence alone is not enough

Here is a deterministic counterexample. On a half-chart take \(K(u)=u^2\) and
\[
\xi_n(u)=h(\sqrt n\,u),\qquad h(0)=0,
\]
with \(h\) bounded, continuous and nonzero. Every restriction \(\xi_n|_{Z_0}\) is identically zero, but after \(v=\sqrt n\,u\),
\[
\sqrt n\,Z_n^0
 \longrightarrow A(0)\int_0^\infty e^{-\beta v^2+\beta v h(v)}\,dv,
\]
which is generally not the zero-field limit.

A clean sufficient assumption is
\[
\xi_n\Rightarrow G\quad\text{in }C(B),
\]
where \(B\) is a compact neighbourhood containing the relevant support near the zero fibre. Tightness in \(C(B)\) supplies boundedness and equicontinuity in probability.

A weaker formulation is possible:

1. \(\xi_n|_{Z_0}\Rightarrow G\) in \(C(Z_0)\);
2. stochastic equicontinuity **towards** \(Z_0\), for example
   \[
   \lim_{\delta\downarrow0}\limsup_n
   \Pr\!\left[
    \sup_{\substack{z\in Z_0,\ x\in B\\d(x,z)<\delta}}
       |\xi_n(x)-\xi_n(z)|>\varepsilon
   \right]=0;
   \]
3. the envelope/tail bounds needed outside that neighbourhood.

Under these hypotheses, the proposed joint finite-observable convergence follows from uniform-on-compacts asymptotics and the extended continuous mapping theorem.

For the far region, the existing bound is exactly the right tool:
\[
e^{-\beta n\varepsilon/2+\beta M_n^2/2},
\qquad M_n=\|\psi_n\|_\infty.
\]
If \(M_n=O_p(1)\), this is negligible at every polynomial-logarithmic scale. No exponential moment of \(M_n\) is needed for this **in-probability** assertion.

For posterior ratios, require the denominator to have the **same leading pair**, finite positive limiting mass, and the relevant joint convergence. Admissibility of \(1\) under the current vanishing-near-deeper-strata theorem is one sufficient route, not an intrinsic requirement of the eventual posterior theorem.

Do not claim that Watanabe’s hypotheses automatically provide the exact topology without checking the particular empirical-process theorem being invoked. The point is that **the leading theorem needs a continuous-field CLT plus transverse tightness, not analytic Taylor-data convergence**.

**Verdict:** this should be a headline paper theorem after correcting the topology and branch convention.

---

### E4 — Correct first moment; variance requires a bilocal integrability criterion

For a centred Gaussian face field with variance \(v(P)\),
\[
\mathbb E S_{\mu,\beta}(G(P))
 =
 \Gamma(\mu)
 \left[\beta\left(1-\frac{\beta v(P)}2\right)\right]^{-\mu},
\]
provided \(\beta v(P)<2\). At or above \(2\), it is infinite.

Consequently, for a nonnegative observable,
\[
\mathbb E L_{\beta,F}
 =
 \int F(P)
 \left[\beta\left(1-\frac{\beta v(P)}2\right)\right]^{-\mu}
 \,d\nu^\mu_c(P),
\]
as an extended-valued identity, with the branchwise version understood if necessary.

Two qualifications:

* Pointwise \(\beta v<2\) does not alone guarantee a finite integral on a noncompact stratum or without a uniform margin.
* Uniform integrability is needed to pass from convergence in distribution of the normalised finite-\(n\) integrals to convergence of their expectations. It is **not** needed merely to compute the expectation of the limiting coefficient.

Calling this a “covariance-modified residue” is acceptable if explained, but the **first moment uses only the variance function**. The full covariance enters second moments.

#### Exact second-moment condition

Write
\[
\rho(dP)=\frac{F(P)}{(c-1)!}\mathcal R^\mu_c(dP),
\qquad F\ge0,
\]
so \(L=\int S_{\mu,\beta}(G(P))\,\rho(dP)\). Define
\[
H(P,Q)=\mathbb E[
 S_{\mu,\beta}(G(P))S_{\mu,\beta}(G(Q))].
\]
Then
\[
\boxed{\mathbb E L^2<\infty
\iff \iint H(P,Q)\,\rho(dP)\rho(dQ)<\infty.}
\]

Assume the marginal first moments are finite and put
\[
a=\beta-\frac{\beta^2v(P)}2,\quad
b=\beta-\frac{\beta^2v(Q)}2,\quad
d=\beta^2\operatorname{Cov}(G(P),G(Q)).
\]
Then
\[
H(P,Q)=
\int_0^\infty\!\!\int_0^\infty
t^{\mu-1}s^{\mu-1}e^{-at-bs+d\sqrt{ts}}\,dt\,ds.
\]
Since \(a,b>0\):

* \(d<2\sqrt{ab}\): finite;
* \(d>2\sqrt{ab}\): infinite;
* \(d=2\sqrt{ab}\): finite exactly when \(\mu<1/4\).

The critical exponent follows after \(t=r^2,s=z^2\): along the null ray the radial integrand has order \(r^{4\mu-2}\).

In particular,
\[
\mathbb E S_{\mu,\beta}(G(P))^2<\infty
\]
if \(\beta v(P)<1\), and at \(\beta v(P)=1\) exactly if \(\mu<1/4\).

A convenient global sufficient condition is
\[
\sup_{\operatorname{supp}\rho}\beta v<1.
\]
Also, \(\beta v\le1\) everywhere and \(\mu<1/4\) gives a uniform second-moment bound.

But **pointwise infinite second moments on a measure-zero diagonal do not automatically make the integrated coefficient’s variance infinite**. At criticality, integrability near the diagonal matters. “Finite iff \(\mu<1/4\) at perfect correlation” describes the critical bilocal kernel, not a universal criterion for every integrated field.

For signed \(F\), the absolute-value kernel criterion is sufficient; cancellation means it need not be necessary.

**Verdict:** state both the exact kernel criterion and a simple uniform-variance sufficient condition.

---

### E5 — A good later theorem, with a narrower claim

For a fixed graded face coefficient, finite transverse regularity should suffice. Formally, differentiating the frozen radial integrand gives
\[
\partial_J^\alpha
 \left[A(u,w)e^{\beta\sqrt t\,\xi(u,w)}\right]_{u_J=0}.
\]
This is a finite polynomial in transverse jets of \(A,\xi\), multiplied by
\[
e^{\beta\sqrt t\,\xi(0,w)}t^{p/2}.
\]
Radial integration produces derivatives
\[
\partial_a^pS_{\mu,\beta}
 =\beta^pS_{\mu+p/2,\beta}.
\]

Thus a joint finite-jet statement is plausible and worth stating for the **fixed graded coefficient**. However:

* it concerns the coefficient, not necessarily an un-subtracted normalised integral;
* the requisite order is the intrinsic order already established in the population theorem, locally \(|\alpha|\) at the relevant integral resonances;
* the amplitude/density jets participate too;
* defining the coefficient from finite jets and proving a uniform asymptotic remainder are different tasks;
* lower logarithmic coefficients can retain information along larger faces or require finite-part constructions, so do not extend the exact-stratum locality claim indiscriminately to all \(q\).

Convergence of the relevant jet fields suffices for convergence of the resulting coefficient functional. To obtain finite-\(n\) asymptotics, also prove the required uniform Taylor-remainder control.

The weighted-\(\ell^1\) analytic-data theorem is a strong formal surrogate for the analytic theorem, but it is **not itself a formalisation of the finite-\(C^k\) weakening**.

**Verdict:** prove a finite-jet coefficient identity before attempting a full \(C^k\) asymptotic engine. Defer both until the leading global theorem is complete.

---

### E6 — Feasible, but insert a reusable radial bridge

Your sequence is broadly right. I would replace “redo the one-face theorem with a fluctuation factor” by the following first attempt.

#### Marked radial limit

Suppose the population leading theorem gives, for suitable test functions \(F\),
\[
a_N\int F e^{-NK}\,d\mu_U\to\int F\,d\nu,
\qquad
a_N=N^\mu(\log N)^{-(c-1)}.
\]
Rescaling \(N\) gives, for every \(s>0\),
\[
a_N\int F e^{-sNK}\,d\mu_U
 \to s^{-\mu}\int F\,d\nu.
\]

This suggests the marked limit
\[
\boxed{
a_N\, (P,NK(P))_*(e^{-NK(P)}\,d\mu_U)
 \Rightarrow
 \nu(dP)\otimes
 \frac{t^{\mu-1}e^{-t}}{\Gamma(\mu)}\,dt .
}
\]
This is weak convergence of finite measures after suitable compact localisation. The spatial component of the limit is carried by the leading stratum.

The empirical integrand is obtained by testing against
\[
F(P)e^{(1-\beta)t+\beta\sqrt t\,\xi(P)}.
\]
This test is unbounded, but the bound
\[
e^{-\beta t+\beta M\sqrt t}
 \le e^{\beta M^2/2}e^{-\beta t/2}
\]
and population estimates at a smaller temperature provide tail control. A slightly smaller temperature supplies decaying tail bounds.

Advantages:

* reuses the population theorem;
* separates radial Gamma asymptotics from field continuity;
* makes the \(S_{\mu,\beta}/\Gamma(\mu)\) factor automatic;
* makes uniformity on compact subsets of \(C(B)\) natural;
* can be proved chartwise or globally, depending on the available measure infrastructure.

The costs are Laplace-transform determination and tightness. If these are awkward in Mathlib, prove a compact-radial-test version using approximation by exponentials, or fall back to the fixed-\(\delta\) face sandwich proof.

**Verdict:** pursue the marked bridge first, with a short feasibility spike; retain the direct face proof as fallback.

---

## 3. Recommended paper-level statements

I recommend four statements, clearly separating leading asymptotics from full expansions.

### Theorem A — Continuous-field leading residue theorem

Fix \(\beta>0\), a compact localisation, and a leading pair \((\mu,c)\) for which the population leading functional is a finite positive zero-order measure \(\nu^\mu_c\). Assume no larger asymptotic terms contribute on this localisation.

Let \(\xi\) be continuous on a compact neighbourhood of the relevant zero fibre. Then
\[
N^\mu(\log N)^{-(c-1)}Z_N^0[F;\xi]
 \longrightarrow
 \int F\,\frac{S_{\mu,\beta}(\xi)}{\Gamma(\mu)}\,d\nu^\mu_c.
\]
Convergence is uniform on compact subsets of the continuous-field space, and more generally on bounded equicontinuous families.

The coefficient depends only on the stratum trace and is locally Lipschitz in that trace. For signed monomial standardisations, use the branchwise pushforward formulation.

This theorem needs no analyticity.

### Theorem B — Empirical leading law and posterior law

Under Theorem A’s geometric hypotheses, assume:

* continuous-field convergence in distribution on a compact neighbourhood, or trace convergence plus transverse stochastic equicontinuity;
* an \(O_p(1)\) far-region field envelope;
* the needed compact localisation/tail assumptions.

Then the normalised empirical integrals converge jointly for finitely many observables to the corresponding random residue integrals.

If numerator and denominator share this leading normalisation and the denominator’s limiting random mass is finite and strictly positive almost surely, posterior expectations converge in distribution to the ratio of random residue integrals.

### Theorem C — Annealed residue and second moments

For a centred Gaussian limiting field, the expected limiting measure has density
\[
\left[\beta\left(1-\frac{\beta v}2\right)\right]^{-\mu}
\]
with respect to the temperature-one population measure, interpreted branchwise and with its exact integrability condition.

Under uniform integrability, the same expression gives the limit of normalised empirical means.

State the bilocal-kernel criterion for second moments, with \(\sup\beta v<1\) as an easy sufficient condition.

### Theorem D — Analytic full expansion; finite-jet locality of graded terms

Retain the paper’s analytic-data full expansion and ordered normalised remainder theorem.

Add a separate finite-jet locality proposition for fixed graded stratum coefficients, initially under the analytic hypotheses. Present extension to finite regularity only when the corresponding remainder theorem has actually been proved.

This avoids weakening the hypotheses of the entire expansion based only on a leading-term argument.

---

## 4. Ranked formalisation programme

The estimates below are rough **new Lean LOC**, assuming reuse of existing interfaces; measure/topology API gaps could substantially increase them.

| Rank | Task | Estimated size | Rationale |
|---|---|---:|---|
| 0 | Fix leading-pair and signed/root interfaces; add regressions | 300–800 | Prevents proving the wrong global statement |
| 1 | F1 + E2: fluctuation bounds, weighted measure, locality, Lipschitz continuity | 300–900 | Mostly reuse; establishes the target object |
| 2 | Marked radial limit and continuous-field leading theorem | 1,500–4,000 | Main new theorem; try population reuse first |
| 3 | F3: chart/piece assembly and branchwise pushforward identity | 800–2,500 | Actual bridge to the resolved residue picture |
| 4 | F4: varying-field distributional transfer, joint observables, ratios, far phase | 500–1,500 | Existing probabilistic machinery should do most work |
| 5 | F5: Gaussian mean measure and UI transfer | 400–1,200 | First moment largely available already |
| 6 | Bilocal variance criterion and useful corollaries | 500–1,500 | Important, but not on the leading-law critical path |
| 7 | Fixed-index joint finite-jet coefficient theorem | 1,500–4,000 | Smaller and cleaner than a full finite-regularity engine |
| 8 | Uniform \(C^k\) asymptotics / higher-logarithmic extension | 3,000–8,000+ | Substantially more bookkeeping and remainder analysis |

### A small parallel analytic bridge is worthwhile

Before or alongside rank 2, prove a **compatibility lemma**:

> In a zero-order leading chart, the existing analytic Taylor-tree coefficient equals the explicit \(S_{\mu,\beta}\)-weighted face integral.

Estimated size: roughly **500–1,500 LOC**, depending on how directly the leading term can be extracted.

This is valuable for:

* validating factorials, \(\beta\)-powers and branch signs;
* connecting the existing Lean theorem to the paper’s geometric language;
* regression-testing the new smooth theorem.

But I would **not** make global analytic-data assembly the main next programme. It risks substantial chart-transition and data-space bookkeeping while retaining stronger hypotheses than the leading SLT object needs.

### Minimum regression suite

Include:

1. \(K=x^2\), one-sided and two-sided, constant field.
2. \(K=x^2y^2\), constant field, with explicit normal-side conventions.
3. A continuous field whose trace is fixed but whose finite-\(n\) boundary layer changes the limit.
4. A localisation with a lower exponent, showing why arbitrary graded coefficients are not raw normalised limits.
5. Constant Gaussian face variance, checking the effective-temperature formula.

**Bottom line:** first formalise the **leading empirical measure with continuous fields**, including transverse tightness and normal-side data. Use a radial Gamma-limit bridge to leverage POPULATION. Then obtain the empirical law and annealed law using the already-developed probability machinery. Keep full analytic expansions and finite-jet extensions as separate, later layers.