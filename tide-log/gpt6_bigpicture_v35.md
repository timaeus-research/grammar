## Recommendation

**Freeze A1–A3 now as a complete, independently releasable result. GO on a separately bounded A4-L tranche for the leading quotient only. NO-GO on an all-orders posterior expansion.**

The statement gate for A4-L can be passed mathematically. The remaining uncertainty is the Lean probability interface, not the division argument itself. Do not make the A1–A3 release depend on resolving that interface.

I am relying on the supplied theorem summaries and reviews here; I have not inspected the repository or verified which Mathlib APIs exist at this pin.

---

## 1. A4-L: scope, budget, and stop criteria

A4-L should deliver exactly two layers:

1. **A generic quotient-in-distribution theorem**, assuming joint convergence of normalised numerator and denominator and an almost surely nonzero limiting denominator.
2. **An assembled leading-target corollary**, obtaining those hypotheses from the Programme S coefficient and remainder machinery.

This would materially improve the present posterior headline: arbitrary positive normal dimensions, tangential integration, finite chart assembly, and random limiting coefficient ratios. It would remain a **leading-order, conditional theorem**, not a formalisation of the displayed full expansion.

### Budget

**Expected: 7–10 units; hard cap: 12.** Reviews after units **3 and 8**, with a final statement review before release.

| Units | Deliverable |
|---|---|
| 1–2 | Lock the two statements; inspect the weak-convergence/test-function APIs; establish a concrete proof route for division |
| 3–4 | Prove the generic joint-law quotient theorem |
| 5–6 | Joint numerator/denominator assembly and leading-target bridge |
| 7–8 | Paper-facing headline; zero-denominator and common-scale interfaces |
| 9–10 | Documentation, regression examples, review corrections |
| 11–12 | Contingency only |

The unused allowance under the earlier caps is not an obligation to spend it.

### Stop criteria

- **After unit 2:** if neither an existing a.s.-continuous mapping theorem nor an accessible bounded-continuous-test-function route is available, pause implementation and freeze at A3.
- **By unit 4:** the generic scalar quotient theorem should be proved. Otherwise stop and reassess; do not turn A4 into an open-ended weak-convergence infrastructure programme.
- Stop if the proposed headline silently requires deriving joint data convergence, leading-index identification, positivity, or the chart decomposition from the paper’s hypotheses.
- Stop any attempt to introduce all-orders division, random leading indices, or inverse-logarithmic series into this tranche.
- Do **not** replace `P(B = 0) = 0` by a fixed lower bound `|B| ≥ c > 0` merely to obtain a globally continuous map. That would be a useful auxiliary theorem, but not the agreed statement.

If A4 stops, retain any useful generic lemmas, but release Programme S as XXXIV–XXXVII with the existing posterior scope unchanged.

---

## 2. Exact statement gate

### 2.1 Generic normalised-integral theorem

Let \(U_\ell,V_\ell\) be measurable real random variables on the source probability space, and let \((A,B)\) be a measurable real pair on the limiting probability space. The two spaces need not be the same.

Let \(a_\ell\) be a deterministic real sequence, eventually nonzero. Assume
\[
\left(\frac{U_\ell}{a_\ell},\frac{V_\ell}{a_\ell}\right)
\Rightarrow (A,B),
\qquad
\mathbb P(B=0)=0.
\]
Then
\[
\frac{U_\ell}{V_\ell}\Rightarrow \frac AB.
\]

This requires:

- **joint** convergence, not convergence of the two marginals;
- no independence;
- no positivity of \(A\) or \(B\);
- no moment or uniform-integrability hypothesis;
- no deterministic lower bound on \(|B|\).

A still smaller reusable core is simply
\[
(Y_\ell,W_\ell)\Rightarrow(A,B),\quad \mathbb P(B=0)=0
\quad\Longrightarrow\quad
Y_\ell/W_\ell\Rightarrow A/B.
\]
The scale cancellation is then a separate elementary corollary.

### Zero denominators

Use Lean’s total real division in the generic theorem. State explicitly that:

- the chosen value of \(A/B\) on \(\{B=0\}\) is irrelevant to its law;
- the hypotheses imply
  \[
  \mathbb P(V_\ell=0)\longrightarrow0;
  \]
- changing the source quotient arbitrarily, measurably, on \(\{V_\ell=0\}\) does not change the limiting law.

They do **not** imply that \(V_\ell\neq0\) eventually almost surely.

For an actual posterior interpretation, finite-sample positivity/nonvanishing of the partition function belongs in a separate application hypothesis or bridge. The probabilistic quotient theorem should not be burdened with it.

### 2.2 A workable proof without an a.s.-continuous CMT

I would not assume the needed Mathlib theorem exists. But there is a short, concrete workaround that does not require constructing a general a.s.-continuous mapping theorem.

For \(\delta>0\), define
\[
T_\delta(a,b)=\frac{ab}{\max(b^2,\delta^2)}.
\]
This map is globally continuous and agrees with \(a/b\) whenever \(|b|\ge\delta\).

For a bounded continuous test function \(f:\mathbb R\to\mathbb R\),
\[
\left|\mathbb E f(Y_\ell/W_\ell)
-\mathbb E f(T_\delta(Y_\ell,W_\ell))\right|
\le 2\|f\|_\infty\,\mathbb P(|W_\ell|<\delta).
\]
Portmanteau gives
\[
\limsup_\ell\mathbb P(|W_\ell|<\delta)
\le \mathbb P(|B|\le\delta),
\]
and the latter tends to zero as \(\delta\downarrow0\), because \(\mathbb P(B=0)=0\). Apply global continuous mapping at fixed \(\delta\), then let \(\delta\downarrow0\). The same comparison handles the limiting quotient.

**No truncation of the numerator is needed:** boundedness of the test function controls the error on the bad-denominator event.

Thus the API probe should look for the existing weak-convergence integral characterisation and portmanteau interfaces, not only for an a.s.-continuous CMT.

---

## 3. The assembled leading-target theorem

Choose a **deterministic target**
\[
\tau=(\mu_0,j_0),\qquad
\mu_0\in Q^{-1}\mathbb N,\quad j_0\le D,
\]
on a common lattice and degree covering numerator and denominator. Put
\[
a_\ell=N_\ell^{-\mu_0}(\log N_\ell)^{j_0}.
\]
Since \(N_\ell\to\infty\), this is eventually positive.

Use a single jointly convergent datum \(X_\ell\Rightarrow X\) carrying both amplitude families. Write
\[
A(x)=C^\phi_{\mu_0,j_0}(x),\qquad
B(x)=C^1_{\mu_0,j_0}(x),
\]
and let \(P^\phi_\ell,P^1_\ell\) be their assembled predecessor sums.

The best mathematical interface is:
\[
\frac{P^\phi_\ell}{a_\ell}\to0,\qquad
\frac{P^1_\ell}{a_\ell}\to0
\quad\text{in probability},
\]
together with the normalised external-residual hypotheses and
\[
\mathbb P(B(X)=0)=0.
\]
Then the assembled approximation statements give
\[
\left(\frac{Z^0_\ell[\phi]}{a_\ell},
      \frac{Z^0_\ell[1]}{a_\ell}\right)
\Rightarrow (A(X),B(X)),
\]
and hence
\[
\boxed{\quad
\frac{Z^0_\ell[\phi]}{Z^0_\ell[1]}
\Rightarrow
\frac{C^\phi_{\mu_0,j_0}(X)}
     {C^1_{\mu_0,j_0}(X)}.
\quad}
\]

### The convenient “all predecessors vanish” corollary

A sufficient, easily audited condition is that, for **each source index \(\ell\)** and each predecessor \((\nu,q)\prec\tau\),
\[
C^\phi_{\nu,q}(X_\ell)=0,\qquad
C^1_{\nu,q}(X_\ell)=0
\quad\text{almost surely}.
\]
There are finitely many predecessors at the target, so these imply the required predecessor sums vanish almost surely.

A deterministic identity of the coefficient functions on an admissible data set is stronger and often convenient, but should not be required by the generic statement.

**Crucial warning:** vanishing of predecessor coefficients only at the limiting datum \(X\) is insufficient. Their small source values may be multiplied by diverging scale ratios. One needs exact source vanishing or sufficiently fast normalised negligibility.

### What “leading target” means here

The denominator coefficient is nonzero almost surely, so the target is genuinely leading for the denominator in the asserted probabilistic sense.

The numerator coefficient may vanish, even identically. That is harmless: the theorem then permits a zero limiting posterior ratio. Do not require a nonzero numerator coefficient merely to call this a leading-scale result.

Randomly selected leading indices are outside A4-L.

### Joint data: avoid a new analytic data-space programme

The simplest implementation is a product of the numerator and denominator chart-data spaces, with the two projection maps. Joint weak convergence is an explicit hypothesis.

For paper-facing common-phase data, explain how the two projections share the phase. That compatibility can be encoded by a common underlying datum or by a support condition. It is not needed for the generic quotient lemma.

Do not infer joint convergence from separate applications of XXXVII. Instead:

1. obtain joint coefficient convergence by continuous mapping;
2. prove each normalised approximation error tends to zero in probability;
3. combine those two errors into a vector;
4. apply vector Slutsky.

No independence is involved.

### Different leading scales

A useful optional corollary is
\[
\left(U_\ell/a^\phi_\ell,\;V_\ell/a^1_\ell\right)
\Rightarrow(A,B)
\quad\Longrightarrow\quad
\frac{a^1_\ell}{a^\phi_\ell}\frac{U_\ell}{V_\ell}
\Rightarrow A/B.
\]
That is the correct leading assertion for different numerator and denominator indices. It is **not** automatically an unscaled quotient limit.

The common empirical exponential factor may be cancelled separately once its nonvanishing is established.

---

## 4. Do not attempt the all-orders quotient expansion

The absent `lemma:division` is now a major statement-level gap, not a small omitted algebra lemma.

Even
\[
\frac1{1+1/\log N}
=\sum_{m\ge0}(-1)^m(\log N)^{-m}
\]
illustrates the problem. A finite truncation leaves an inverse-logarithmic error, which is larger than \(N^{-\varepsilon}\) for every fixed \(\varepsilon>0\).

Consequently, reaching a later polynomial order may require resolving an **infinite inverse-logarithmic block** first. The present finite-predecessor machinery does not directly support that ordering.

An all-orders statement needs decisions about:

- the precise asymptotic series class;
- whether coefficients at each \(N\)-power are formal Laurent series in \(1/\log N\), functions, or something else;
- the truncation and remainder semantics;
- admissible leading-index shifts;
- nonvanishing and continuity domains for recursive coefficients.

The paper’s product notation \(\mathcal S\times\mathcal Q\), with “discrete index sets,” does not settle these questions.

Also, \(\mathcal S\subset\mathbb Q_{\ge0}\) is not a consequence of arbitrary scalar division: it needs a numerator-versus-denominator leading-order condition. Bounded observables may supply relevant constraints, but that is additional mathematics.

**A4-L should neither formalise `lemma:division` nor claim to validate the full displayed expansion.**

---

## 5. Paper notes and A3 additions

I would organise the notes into three categories: **missing statements**, **corrections/conventions**, and **formal scope qualifications**. This prevents stronger sufficient Lean hypotheses from being confused with errors in the paper.

### Missing statements

Add:

- **`lemma:division` has no statement despite repeated citations.** A leading quotient theorem repairs only the leading-law argument, not the all-orders claim.
- `prop:convergence` and `lemma:AsymInt` have explicit formal substitutes, with their actual topology and domination hypotheses recorded.

### Corrections and conventions

Retain your existing items, and add:

1. **Common lattice and degree.** Finite assembly uses refinement and zero padding. Coefficients off a local lattice or above a local log degree must vanish.
2. **One cutoff across charts.** A global target need not be an admissible local target in every chart. Assembly is justified by expanding every chart through one common cutoff, not by applying an inapplicable local target theorem.
3. **Joint randomness.** Finite chart assembly—and especially posterior division—requires joint convergence of the relevant data.
4. **Index translation.** State \(j=m-1\) wherever the paper’s log multiplicity is connected to the Lean index.
5. **Leading coefficient positivity.** Positivity at each finite sample does not by itself imply a nonzero limiting coefficient. For example, positive deterministic \(B_\ell=1/\ell\) converges to zero. The quoted positivity result must apply to the coefficient evaluated at the limiting datum, with its admissibility assumptions verified.

For the partition weights, say that the formalisation **absorbs \(\rho_I\) into the amplitude**. Whether the source contains an actual omission or merely an unstated convention should be described accordingly.

For the exponential residual, record both \(\varepsilon>0\) and \(N_\ell\to\infty\), and preserve the mode of convergence: this is negligibility **in probability**, not an almost-sure or deterministic uniform estimate.

### Scope qualifications

A3 proves a conditional assembly theorem with:

- finite charts;
- the declared tangential data and measure assumptions;
- externally supplied decomposition;
- externally supplied joint data convergence;
- normalised residual control.

It does not construct the resolution, partition of unity, or decomposition from the original statistical model.

---

## 6. Beyond §4.3

### Population specialisation

**Do not open a 2–4-unit programme under the name `thm:expectation_expansion` before the authors rewrite it.**

There is a cheap, legitimate deterministic corollary:

- constant data;
- \(\xi=0\);
- deterministic amplitudes;
- the deterministic integrated/assembled cutoff theorem;
- an external deterministic decomposition and suitable residual control, if a global integral is claimed.

That gives a **conditional deterministic normal-form integral expansion**. It is not automatically the obsolete §3 population theorem, particularly if that theorem concerns a posterior ratio or a different setup.

My scheduling recommendation:

- postpone it until A4-L is completed or stopped;
- authorise **at most two units** if the authors want this precise auxiliary theorem;
- do not stretch to four units without an agreed rewritten statement.

Use the deterministic A3 machinery directly, rather than routing the argument through degenerate probability laws.

### Other inexpensive extensions

From the machinery described here, the strongest low-cost candidates are:

- finitely many observables jointly, with one denominator, after A4-L;
- the different-scale quotient corollary;
- constant-data deterministic specialisations;
- convenient sufficient conditions for zero predecessor sums.

The first is particularly useful:
\[
\bigl(Z[\phi_1]/Z[1],\ldots,Z[\phi_r]/Z[1]\bigr)
\Rightarrow
\bigl(A_1/B,\ldots,A_r/B\bigr).
\]

I would not speculate about other items from #33 without their statements. In particular, positivity, Gaussian identification, derivation from Hypothesis I, and full division are not now “cheap.”

---

## 7. Hand-off report and release non-claims

### What to emphasise

The central achievement is not merely an increase in normal dimension:

> **Programme S supplies a continuous-coefficient, finite-cutoff stochastic Taylor-tree interface, stable under tangential integration and finite chart assembly, conditional on joint data convergence and an external global decomposition.**

The report should contain:

1. **Exact release pin and build status**, distinguishing reviewed commits from any later A4 work.
2. **Dependency ladder:** canonical coefficient continuity → uniform cutoff bounds → ordered remainders → stochastic convergence → tangential integration → finite assembly.
3. **Headline-to-paper mapping**, marking substitutes and partial results rather than silently identifying them with the source claims.
4. **A compact hypothesis table** for XXXV, XXXVI, XXXVII/XXXVII′, and A4-L if completed.
5. **Paper repair ledger**, separated as above.
6. **A4 disposition:** completed leading quotient, or explicitly deferred.

The four PASS reviews are good release evidence, but they should accompany—not replace—the scope table.

### Final release non-claims

For the A1–A3 release:

- No derivation of weighted-\(\ell^1\) or tangential-data convergence from Hypothesis I.
- No identification of the limiting data as Gaussian.
- No identification of the weighted-\(\ell^1\) topology with an unspecified \(C^\omega\) topology.
- No derivation of a common analytic radius for random phases; fixed chart radii and appropriate data membership are hypotheses.
- No construction of the resolution, finite chart system, partition of unity, or external global decomposition.
- No claim for zero normal dimension, infinite chart assemblies, or more general tangential settings than those stated.
- No minimality claim for compactness, finite-measure, or continuity assumptions.
- No upgrade from norm-boundedness in probability to compact tightness.
- No almost-sure expansion, moment convergence, or expectation convergence from weak convergence alone.
- No automatic identification or nonvanishing of the globally leading coefficient; chart cancellations remain possible.
- Sample sizes are deterministic and tend to infinity; quotient-scale identities use the stated eventual thresholds.
- No full posterior expansion and no formalised all-orders division lemma.
- No formalisation of the obsolete §3 population theorem.

If A4-L is completed, add:

- Posterior convergence is conditional on **joint** normalised convergence and almost-sure nonvanishing of the limiting denominator.
- Common-target applications require source predecessor vanishing or normalised negligibility.
- Finite-sample posterior well-definedness and positivity are separate application facts.
- No random leading-index theorem.
- No claim that convergence in law of a posterior expectation implies convergence of its expectation over datasets.

**Bottom line:** bank XXXIV–XXXVII now. Spend a bounded tranche on the genuinely useful leading quotient theorem, with `P(B = 0) = 0` intact. Leave the full posterior series—and the obsolete population theorem—behind explicit author-facing statement gates.
