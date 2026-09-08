## Recommendation

**Open a new programme: “§4.3 stochastic Taylor tree and conditional integration/assembly.” Start with A1–A2, not with the whole resolution application.**

The new instruction changes the priority from #32: it asks to continue formalising **the paper**, rather than to complete the most attractive adjacent consequence of the existing library. General-dimensional coefficient convergence and ordered stochastic remainders are directly parts of `thm:strataempiricalexpansion`; posterior weak convergence for the concrete normal-crossing model is not the best response to that emphasis.

Keep Headlines I–XXXIII frozen. The next programme should have its own scope, gates, and release statement:

> In every positive normal dimension, the canonical Taylor-tree coefficients are continuous functions of weighted-summable phase and amplitude data. Under joint convergence in distribution of those data, finite coefficient vectors and ordered normalised remainders converge in distribution. Subsequently, extend this result to tangential integration and finite chart assembly under explicit uniformity and decomposition hypotheses.

That is a substantial advance on a remaining paper theorem, without pretending to derive the paper’s statistical or geometric hypotheses.

The estimates below are **planning estimates in the previous implementation-unit sense**, based on the supplied inventory, not a fresh inspection of the repository.

---

## 1. Ranking and programme boundaries

| Priority | Work package | Estimated units | Gate / stopping condition |
|---|---|---:|---|
| **1** | **A1–A2: stochastic Taylor tree, one chart, arbitrary positive dimension** | **11–18**, including statement audit and review | By unit 3, a credible quantitative proof must handle perturbations of **the constant phase as well as the other coefficients**. Final gate: ordered remainder convergence for the original family integral, not merely a formal series. |
| **2** | **A3: integration over tangential parameters and finite chart assembly** | **8–14 additional** | Prove an integrated remainder bound from an explicit integrable majorant. Do not obtain “uniformity over a stratum” from pointwise asymptotics. |
| **3** | **A4: posterior division** | **2–3 scouting; then 8–16 if the expansion language is settled** | Resolve the inverse-logarithm issue before implementing an all-orders quotient theorem. A general leading quotient is a smaller, earlier deliverable. |
| **4** | **B: corrected, conditional population expansion** | **2–4 statement-audit units; 4–8 for a scalar corollary reusing A3** | Author agreement on the replacement statement. This estimate excludes coordinate-free geometry and construction of a resolution atlas. |
| **5** | **D: boundary/Δ tail and non-box domains** | **2–3 reconnaissance; provisional 8–20 for a narrowly specified lemma** | Identify the exact domain and a valid phase-separation or boundary argument. Promote this package if it becomes a demonstrated prerequisite for chart assembly. |
| **6** | **C: posterior weak convergence / second example** | Re-estimate separately | Useful, but not the default response to this instruction. A small example may serve as a regression test, not become the programme. |

### Recommended authorisation envelope

Authorise **A1–A2 first, capped at 18 units**, with the first hard review after unit 3. Treat A3 as the next gated tranche. Do not commit now to “full §4.3 in 40 units”: the empirical-process topology, integration hypotheses, and quotient expansion language remain genuine statement-level questions.

The principal deliverable after the first tranche should be advertised as:

> **The single-chart stochastic Taylor-tree conclusion in every positive dimension, conditional on joint weak convergence of weighted Taylor data.**

Not “Hypothesis I implies `thm:strataempiricalexpansion`.”

---

## 2. A1: the right coefficient-space theorem

### Use a genuine Banach space, with `CoeffFamily` as its analytic interface

For fixed \(d>0\) and \(b>0\), put
\[
E_b=\left\{c:\mathbb N^d\to\mathbb R:
   \|c\|_b:=\sum_\gamma |c_\gamma|b^{|\gamma|}<\infty\right\}.
\]

Implement this through the isometry
\[
c\longmapsto \bigl(\gamma\mapsto b^{|\gamma|}c_\gamma\bigr)
\]
to ordinary real \(\ell^1(\mathbb N^d)\).

**Reuse/generalise the existing weighted-\(\ell^1_\rho\) probability infrastructure.** Do not build a competing probability-space structure on the raw `CoeffFamily d` function type. Add a bridge from the Banach-space element to the existing summable-family theorems.

A useful public data space is
\[
X_b=E_b\times E_b,
\]
for phase and amplitude, with a standard product norm. Finite collections of amplitudes can be added later; they are particularly useful for numerator/denominator joint convergence.

### Which radius?

**Use the box radius \(b\) in the primary theorem.** That is the norm controlled by the Taylor-tree remainder estimate and sufficient for the integral and coefficient system.

A stronger norm at \(r>b\) is an optional input interface:

* the inclusion \(E_r\to E_b\) is continuous;
* holomorphic data on a larger polydisc provide elements of \(E_b\);
* probability theory can then be carried out entirely in \(E_b\).

Do not require extra analytic radius for the abstract stochastic transfer when weighted summability at \(b\) already suffices.

### Public theorem: continuity. Quantitative engine: Lipschitz on bounded balls

For each fixed \(\mu>0\), \(0\le j<d\), fixed normal-crossing data, and fixed box, prove an estimate of the form
\[
|A^b_{\mu,j}(x)-A^b_{\mu,j}(y)|
 \le K_{\mu,j,R}\,\|x-y\|,
 \qquad \|x\|,\|y\|\le R.
\]

Here \(A^b\) must mean the **actual coefficient of**
\(N^{-\mu}(\log N)^j\), including the box rescaling and binomial log conversion. Avoid silently switching between the rescaled unit-box coefficients and the paper-facing box coefficients.

Then export:

1. Lipschitzness on every bounded ball;
2. continuity on \(X_b\);
3. continuity of every finite vector of canonical coefficients;
4. measurability as an immediate corollary.

For the paper-facing replacement of `prop:convergence`, **continuity is the main statement**. The ballwise Lipschitz theorem is the stronger reusable estimate.

### The decisive missing perturbation: \(a=\xi(0)\)

The existing stability result with a fixed constant phase is not yet A1.

Split a perturbation into:

* amplitude perturbation;
* perturbation of the constant-free phase \(J\);
* perturbation of \(a=c_\xi(0)\).

For the third piece, use the phase derivative/moment shift or directly
\[
|e^{\beta a\sqrt t}-e^{\beta a'\sqrt t}|
 \le \beta |a-a'|\sqrt t\,
       e^{\beta\max(a,a')\sqrt t}.
\]
The existing log-moment majorants then control the difference, with the extra half-shift of the moment exponent. On a ball, \(|a|,|a'|\), the phase masses, and amplitude masses are bounded.

The desired outcome is one constant depending on \(R\), not a coefficientwise constant with uncontrolled dependence on the two inputs.

**Gate A:** establish this estimate for the canonical series and pass it to the existing canonical coefficient. Do not introduce a new existential coefficient choice.

---

## 3. A2: probability model and ordered remainders

### State weak convergence at the data-space level

Let
\[
X_n=(c_{\xi_n},c_{\eta_n}),\qquad X=(c_G,c_\eta)
\]
be measurable \(X_b\)-valued random elements, and assume
\[
\mathcal L(X_n)\Rightarrow\mathcal L(X).
\]

The limit amplitude may also be random. Deterministic amplitude is a convenient specialisation.

The abstract transfer theorem does **not** need Gaussianity. A paper-facing corollary may additionally identify the limiting phase as the coefficient data of a Gaussian process. That identification is an external hypothesis until an empirical-process theorem supplies it.

Use the repository’s existing probability-law/CMT interface. At the mathematical level, convergence in the weak topology of `ProbabilityMeasure X_b` is the right object. The various `tendsto_iff_forall_integral_tendsto` characterisations are fallback proof tools, not a reason to redo the d=2 infrastructure.

The exact Mathlib API should be checked against the pin before putting declaration names in the plan.

### Coefficient vectors

For any finite list of indices \(F\),
\[
\bigl(A^b_{\mu,j}(X_n)\bigr)_{(\mu,j)\in F}
\Rightarrow
\bigl(A^b_{\mu,j}(X)\bigr)_{(\mu,j)\in F}.
\]

Prove this as **joint finite-dimensional convergence**, not only marginal convergence. The joint result is what later division and assembly need.

### The stronger and more useful remainder theorem

Order terms by increasing exponent and, at a fixed exponent, decreasing log degree. For target \((\mu,j)\), define
\[
R_n^{\mu,j}
=
\frac{
 Z(N_n;X_n)
 -
 \sum_{(\nu,q)\prec(\mu,j)}
 A^b_{\nu,q}(X_n)N_n^{-\nu}(\log N_n)^q
}{
 N_n^{-\mu}(\log N_n)^j
}.
\]

First prove
\[
R_n^{\mu,j}-A^b_{\mu,j}(X_n)\longrightarrow 0
\quad\text{in probability}.
\]
Then conclude
\[
R_n^{\mu,j}\Rightarrow A^b_{\mu,j}(X).
\]

This separates the analytic estimate from continuous mapping and Slutsky, and supports joint versions.

### How to obtain the small remainder

Choose a spectral cutoff \(L>\mu\). The Taylor-tree remainder gives
\[
C_L(X_n)\,
N_n^{-(L-\mu)}
\frac{(1+\log N_n)^{d-1}}{(\log N_n)^j}.
\]

On each fixed data ball, \(C_L\) has a deterministic bound. The remaining terms below \(L\) form a finite sum:

* same exponent, lower log degree: killed by inverse powers of \(\log N_n\);
* larger exponent: killed by a negative power of \(N_n\).

Their coefficients are bounded in probability by continuous mapping.

For \(C_L(X_n)\), it is enough to use **boundedness in probability of the scalar norms**. Do not argue that closed bounded balls in infinite-dimensional \(\ell^1\) are compact. They are not. Weak convergence of the data implies weak convergence of their norms and hence the scalar boundedness needed here.

Also establish measurability of \(Z(N;\cdot)\). For each fixed \(N>0\), continuity of the family integral is a natural route via the evaluation bound and dominated convergence on a data ball.

**Gate B:** prove the ordered remainder statement at a target with nontrivial log ordering. A theorem only at the largest log degree is not yet the paper’s ordered assertion.

---

## 4. A3: supply `lemma:AsymInt`, but expose its hypotheses

Yes: the two dangling references are excellent paper-facing targets. They should become **explicit named replacement lemmas**, with topology and domination hypotheses stated.

### First version of `AsymInt`: deterministic dominated integration

Suppose \(v\) ranges over a finite measure space and
\[
\left|Z_N(v)-\sum_{\mu<L,j}
 A_{\mu,j}(v)N^{-\mu}(\log N)^j\right|
\le H_L(v)N^{-L}(1+\log N)^{d-1},
\]
where \(H_L\) is integrable and the coefficient functions are integrable.

Then
\[
\int Z_N(v)\,d\nu(v)
=
\sum_{\mu<L,j}
 \left(\int A_{\mu,j}(v)\,d\nu(v)\right)
 N^{-\mu}(\log N)^j
+
O\!\left(N^{-L}(1+\log N)^{d-1}\right).
\]

This is the correct general lemma. Compact support alone is not a substitute for the majorant.

### Concrete tangential interface

For a compact parameter space \(K\), a finite measure \(\nu\), and continuous data
\[
v\mapsto X(v)\in X_b,
\]
the sup norm supplies a uniform bound. Thus the coefficient-integration map
\[
X\longmapsto
\left(\int_K A_{\mu,j}(X(v))\,d\nu(v)\right)_{(\mu,j)\in F}
\]
is continuous on \(C(K,X_b)\), and ballwise Lipschitz when the coefficient maps are.

For random tangential fields, a clean sufficient assumption is
\[
X_n\Rightarrow X
\quad\text{in }C(K,X_b).
\]

**Pointwise convergence in distribution for each \(v\) is not sufficient.** It gives neither the needed joint structure nor uniform remainder control.

### Then finite chart assembly

Use a finite product of these chart-data spaces, with joint convergence. If charts have different normal dimensions or exponent lattices, collect coefficients over their finite union and insert zeros where appropriate.

The chart decomposition must include either:

* an exact integral identity; or
* an error proved negligible at the requested normalised scales.

An externally assumed “decomposition” without a quantified residual is not enough for an all-orders stochastic expansion.

A particularly important audit concerns cutoffs: smooth partitions of unity generally do **not** preserve holomorphic normal-coordinate amplitudes. A3 must explicitly assume the relevant normal coefficient-family representation, or later supply a different smooth-amplitude extension. Do not hide this issue in the word “adapted.”

**Gate C:** one compact tangential-parameter theorem, with the integrated coefficient and integrated remainder both identified. Only then add finite assembly.

---

## 5. A4: do not rush “division of asymptotic series”

A leading quotient theorem is straightforward once numerator and denominator are treated jointly and the limiting leading denominator is nonzero almost surely.

An all-orders expansion is more delicate.

### The inverse-logarithm issue

For example,
\[
\frac1{\log N+a}
=
\frac1{\log N}
-\frac a{(\log N)^2}
+\frac{a^2}{(\log N)^3}-\cdots.
\]

There are infinitely many logarithmic orders at the **same power of \(N\)** before any positive-power correction is reached. Thus a generic pair of discrete index sets \(\mathcal S,\mathcal Q\) does not by itself specify a usable asymptotic summation convention. A finite spectral-cutoff sum, as used in the Taylor tree, does not automatically survive division.

Before implementing A4:

1. inspect the exact statement and formal status of `lemma:division`;
2. choose either a nested power/log expansion convention, or rational functions of \(\log N\) at each \(N\)-power;
3. state precisely what a finite truncation means and what remainder it controls.

Coefficient recursion can then be formalised, but a formal recursive series is not yet an asymptotic theorem for the original quotient.

### Positivity issue

Positivity of each sample’s leading denominator is not sufficient on its own. The stochastic division theorem needs a limit coefficient that is nonzero almost surely, or an equivalent lower-tail condition. On that open set, finite quotient coefficients are continuous functions of the **joint** numerator/denominator coefficient vector.

**Gate D:** approve the expansion language and denominator hypotheses before starting the all-orders implementation.

---

## 6. The missing labels and the §3 rewrite

### What to tell the authors

Supply a short dependency/errata note:

> The proof of `thm:strataempiricalexpansion` cites `prop:convergence` and `lemma:AsymInt`, but these labels have no statements in the supplied source. The formalisation supplies precise sufficient versions: coefficient continuity in the weighted-\(\ell^1\) topology, and integration of expansions under an integrable remainder majorant. These fill explicit proof obligations; they do not establish that Hypothesis I supplies their hypotheses.

Use descriptive Lean names, for example:

* `continuous_taylorTree_coeff`;
* `taylorTree_coeff_lipschitzOn_ball`;
* `integral_taylorTree_expansion`.

Add paper labels only in coordination with the authors. In particular, do not call the first theorem continuity on \(C^\omega([0,b]^d)\) without specifying that space’s topology and a continuous bridge into \(E_b\).

### Why B should wait for a statement audit

The red warning is substantive. At least these distinctions need repair before formalising the displayed §3 theorem:

* candidate exponents versus genuinely nonzero leading terms;
* signed-observable cancellation after integration over a stratum;
* face-supported leading functionals versus a corner restriction in mixed-ratio cases;
* coordinate-free higher normal derivatives and any splitting/jet hypotheses needed to define them;
* dependence of a per-stratum decomposition on localisation choices.

In particular,
\[
D_\perp^l(\phi\circ\pi)|_{S_I}\not\equiv0
\]
does not by itself prevent the resulting signed leading coefficient from integrating to zero. Nor does \(l_i=0\) for every component generally imply that the observable is nonzero on their intersection.

A good later B deliverable is a **scalar, conditional population expansion obtained by \(\xi=0\)** from A3. Do not attach the entire existing `thm:expectation_expansion` label to that corollary.

---

## 7. Explicit non-claims for the new programme

The first release should list these prominently:

1. **No derivation from Hypothesis I or relative finite variance.** Resolution, empirical-process convergence, and the standard-form likelihood identity remain external inputs.
2. **No assertion that real analyticity yields an origin-centred polydisc of radius larger than the chart box.** Local real analyticity is not that hypothesis.
3. **No automatic common radius for random empirical phases.** The primary assumption is measurable \(E_b\)-valued data and convergence there for a fixed \(b\). A sample-dependent holomorphic radius alone does not provide this.
4. **No automatic Gaussian Banach-valued limit.** Gaussianity and identification with the paper’s \(G\) require separate input.
5. **No global geometric stratum theorem.** Compact parameter integration and finite chart assembly are conditional analytic constructions.
6. **No support nonvanishing or cancellation-free leading exponent claim.**
7. **No full posterior expansion until division semantics are settled.**
8. **No silent scale conversion.** Use Taylor-tree \(N=\) paper sample size here; translate older normal-block conventions explicitly.

For a holomorphic random-field interface, a useful sufficient route is a **fixed** \(b<r<R\), a measurable random function in a suitable sup-norm holomorphic-function space, and a continuous coefficient-extraction map into \(E_b\). Cauchy estimates give a bound proportional to
\[
(1-b/r)^{-d}
\]
times the sup norm on the radius-\(r\) polydisc. This proves measurability by continuity. It does not manufacture the required function-space convergence from pointwise empirical-process convergence.

---

## 8. First three units: start here

### Unit 1 — statement lock and Banach-space bridge

* Open the programme ledger and proposed Headline XXXIV.
* Inspect the existing weighted-\(\ell^1_\rho\), CMT, and random-transfer infrastructure.
* Implement the arbitrary-dimensional rescaling bridge \(E_b\leftrightarrow\ell^1(\mathbb N^d)\).
* State the canonical paper-facing coefficient map, including box log conversion.
* Prove continuity of constant evaluation and the basic mass/norm bounds.

**Deliverable:** a checked data-space interface and exact A1/A2 theorem signatures. No new probability infrastructure unless the existing one genuinely cannot be generalised.

### Unit 2 — varying-constant-phase estimate

Prove the quantitative coefficient estimate for changing \(a=\xi(0)\), using the moment majorant and half-shift. Combine it on paper—and preferably in Lean—with the existing \(J\)- and amplitude-perturbation estimates.

**Deliverable:** an estimate uniform on a data ball for an arbitrary fixed valid coefficient index.

### Unit 3 — close the continuity gate and test the stochastic bound

* Export ballwise Lipschitzness/continuity for the canonical box coefficient.
* Export continuity of finite coefficient vectors.
* Prove, or reduce to existing scalar lemmas, that the cutoff remainder normalised at a target \((\mu,j)\) tends uniformly to zero on each fixed data ball when \(L>\mu\).
* Audit measurability of the fixed-\(N\) integral map.

### Stop criterion

**Stop and reassess after unit 3** if the result still:

* fixes \(\xi(0)\);
* applies only to polynomial truncations rather than canonical family coefficients;
* introduces coefficient choices unrelated to the frozen Taylor-tree coefficients; or
* requires an unstated common analytic radius or unproved uniformity hypothesis.

An ordinary missing Mathlib convenience lemma is not a mathematical stop signal. Discovering that the proposed public statement needs stronger, unacknowledged hypotheses is.

---

**Bottom line:** choose **A1–A2 now**, then **A3**, with A4 behind a statement gate. This most directly turns the completed deterministic Taylor tree into progress on the paper’s remaining §4.3 statements, while also giving the authors precise replacements for two missing proof dependencies.
