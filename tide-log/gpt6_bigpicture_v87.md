## Recommendation

Make **C’s main result the joint empirical posterior-ratio theorem**
\[
\widehat\mu_n(\varphi)\ \Rightarrow\ \frac{L_\varphi}{L_1},
\qquad L_1>0\ \text{a.s.},
\]
with both coefficients evaluated at the **same Gaussian limit**.

Alongside it, land the inexpensive perturbation lemma and a compact concentration/constant-on-minimisers package. Do **not** make a new uniform empirical-process development a prerequisite. Your existing field CLT may already supply the needed *in-probability* uniform control on certified boxes.

Do a short semantic audit first, and another after C. D is optional refinement after that.

---

# Q1. The honest minimal C

## (a) C1: correct—and the general bound can be sharpened

Let \(\mu\) be a probability measure, \(R\ge0\) a.e. and integrable, \(A>0\), and put
\[
r=R/A,\qquad
\delta=\int |r-1|\,d\mu<1,\qquad
m=\int r\,d\mu.
\]
Then
\[
|m-1|\le\delta,\qquad 0<1-\delta\le m\le1+\delta.
\]
For a bounded measurable real observable, define
\[
\widehat\mu(\varphi)=\frac{\int\varphi R\,d\mu}{\int R\,d\mu}.
\]
Your proposed estimate is valid:
\[
|\widehat\mu(\varphi)-\mu(\varphi)|
\le \frac{2\|\varphi\|_\infty\delta}{1-\delta}.
\]

For implementation, an explicit a.e. bound \(|\varphi|\le M\) is more convenient than an essential-supremum norm.

### Centring

The useful identity is
\[
\widehat\mu(\varphi)-\mu(\varphi)
=\frac1m\int(\varphi-\mu(\varphi))(r-1)\,d\mu.
\]
Consequently,
\[
|\widehat\mu(\varphi)-\mu(\varphi)|
\le \frac{\|\varphi-\mu(\varphi)\|_\infty\delta}{1-\delta}.
\]
Thus, if \(\mu(\varphi)=0\), your proposed one-factor bound is exactly right.

### A sharper universal bound

In fact,
\[
d_{\rm TV}(\widehat\mu,\mu)\le\delta,
\]
using \(d_{\rm TV}=\sup_E|\widehat\mu(E)-\mu(E)|\). Hence
\[
\boxed{|\widehat\mu(\varphi)-\mu(\varphi)|\le2M\delta.}
\]
More generally, if \(a\le\varphi\le b\) a.e., the bound is \((b-a)\delta\).

A short proof: write
\[
a_+=\int(r-1)_+\,d\mu,\qquad b_-=\int(1-r)_+\,d\mu,
\]
so \(m=1+a_+-b_-\), \(\delta=a_++b_-\). If \(m\le1\), normalization can only increase the overlap with \(\mu\), giving TV \(\le b_-\). If \(m\ge1\), the overlap gives TV \(\le a_+/m\). Both are at most \(\delta\).

The constant \(2\) in \(2M\delta\) is sharp: take \(R=0\) on a set of probability \(\delta\), \(R=1\) elsewhere, and \(\varphi=-M\) on that set, \(+M\) elsewhere.

**Engineering recommendation:** land your elementary denominator-bound version first; add the sharp version only if the positive-part or TV infrastructure makes it cheap. Neither result establishes that the empirical \(R_n\) actually satisfies the hypothesis—that remains the essential guardrail.

Also, use a different name for this scalar than the empirical normalization \(A_n=n^\lambda/(\log n)^{m-1}\).

---

## (b) C2: the population certificate suffices, but is stronger than necessary

Your conclusion is correct. The cleanest underlying theorem needs neither compactness nor a population asymptotic certificate.

Let \(\pi\) be a finite nonzero prior on the domain \(S\), and assume:

1. \(K\ge0\) is measurable;
2. every positive sublevel has positive prior mass:
   \[
   \pi\{K<a\}>0\qquad(a>0);
   \]
3. the empirical phases are measurable and admit errors \(\varepsilon_n(\omega)\) with
   \[
   |\widehat K_n(\omega,w)-K(w)|\le\varepsilon_n(\omega)
   \]
   on \(S\), or \(\pi\)-a.e. there;
4. \(\varepsilon_n\to0\), pathwise on the event under consideration.

For \(0<a<\kappa\),
\[
\begin{aligned}
\int_{\{K\ge\kappa\}}e^{-n\widehat K_n}\,d\pi
&\le \pi(S)e^{-n(\kappa-\varepsilon_n)},\\
\widehat Z_n
&\ge \pi\{K<a\}\,e^{-n(a+\varepsilon_n)}.
\end{aligned}
\]
Therefore
\[
\boxed{
\widehat\mu_n\{K\ge\kappa\}
\le
\frac{\pi(S)}{\pi\{K<a\}}
e^{-n(\kappa-a-2\varepsilon_n)}.
}
\]
For example, take \(a=\kappa/4\) and eventually \(\varepsilon_n\le\kappa/8\). This yields an \(e^{-n\kappa/2}\) bound with a fixed prefactor.

This fixes the issue in the proposed denominator argument: **use a smaller sublevel for the denominator than the threshold defining the tail.**

### Certificate-facing corollary

Your alternative is excellent as a library-facing corollary:
\[
\widehat Z_n\ge e^{-n\varepsilon_n}Z_n,
\qquad
\widehat\mu_n\{K\ge\kappa\}
\le \frac{\pi(S)e^{-n\kappa+2n\varepsilon_n}}{Z_n}.
\]
It suffices that
\[
\frac{\log Z_n}{n}\to0.
\]
Every positive polynomial/logarithmic leading certificate supplies this, including
\[
Z_n\sim c\,n^{-\lambda}(\log n)^{m-1},\qquad c>0.
\]
No rate stronger than \(\varepsilon_n=o(1)\) is needed.

I would expose:

* an elementary **sublevel-mass theorem**;
* a **subexponential-normalizer theorem** or corollary;
* the derived **population-certificate corollary**.

### ULLN hypotheses

Uniform convergence is an entirely acceptable hypothesis. Do not describe “bounded i.i.d. losses on a compact parameter space” alone as sufficient: compactness and boundedness do not give a ULLN without control of the function class.

A clean sufficient special case is bounded i.i.d. losses with a common deterministic Lipschitz constant in the parameter on a compact metric space. Finite nets plus scalar laws of large numbers then work. That is a separate programme, not part of minimal C.

### Your empirical layer may already give the weaker mode needed

In your displayed chart identity, with \(\beta\) kept outside the phase,
\[
\widehat K_n=\phi^2-n^{-1/2}\phi\,\xi_n.
\]
Thus on a box where \(\phi\) is bounded,
\[
\|\widehat K_n-K\|_\infty
\le n^{-1/2}\|\phi\|_\infty\|\xi_n\|_\infty.
\]
If coefficient evaluation into bounded functions on the box is continuous, the \(\ell^1\) CLT gives
\[
\|\xi_n\|_\infty=O_{\mathbb P}(1),
\]
and hence uniform loss convergence **in probability**.

The same deterministic concentration estimate then gives concentration in probability. This is potentially a much cheaper empirical specialization than an a.s. ULLN.

Two cautions:

* a CLT/tightness statement does not itself give a.s. uniform convergence;
* box control proves concentration for the box model; extending it to the full posterior still needs coverage or control of the omitted region.

---

## (c) C3: yes, with compactness located correctly

Use a compact parameter domain or compact prior support \(S\), with \(K,\varphi\) continuous there, and assume
\[
\varphi=\varphi_0\quad\text{on }S\cap K^{-1}(0).
\]
Compactness gives
\[
\forall\epsilon>0,\ \exists\kappa>0,\quad
w\in S,\ K(w)<\kappa
\Longrightarrow |\varphi(w)-\varphi_0|<\epsilon.
\]
The proof is particularly clean through the compact “bad set”
\[
\{w\in S:|\varphi(w)-\varphi_0|\ge\epsilon\},
\]
on which \(K\) has a strictly positive minimum.

Then
\[
|\widehat\mu_n(\varphi)-\varphi_0|
\le\epsilon+B\,\widehat\mu_n\{K\ge\kappa\},
\]
where \(B\) bounds \(|\varphi-\varphi_0|\) on \(S\).

Thus the conclusion inherits C2’s mode:

* a.s. uniform loss convergence gives a.s. observable convergence;
* uniform loss convergence in probability gives observable convergence in probability.

The truly minimal observable assumption is the displayed small-sublevel property plus boundedness. Compactness and continuity are its convenient geometric specialization.

---

## (d) Coefficient consistency: true, and easiest through uniqueness of limits

The correct statement is:

> Suppose the population posterior concentrates on \(K^{-1}(0)\) in the preceding sense. Let \(\varphi\) be bounded and continuous on the compact support, constant there on the zero set with value \(\varphi_0\). If, for the **same normalization** \(a_n\),
> \[
> a_nZ_n[1]\to c_1>0,\qquad a_nZ_n[\varphi]\to c_\varphi,
> \]
> then
> \[
> \boxed{c_\varphi=\varphi_0c_1.}
> \]

Indeed,
\[
Z_n[\varphi]/Z_n[1]\to\varphi_0
\quad\text{and}\quad
Z_n[\varphi]/Z_n[1]\to c_\varphi/c_1.
\]

This route requires **no new coefficient-linearity API**, no certificate for \(|\varphi-\varphi_0|\), and no chart-by-chart argument.

In particular, a continuous observable vanishing on the **entire relevant zero set** has zero coefficient at the denominator’s leading scale. Positive-dimensional zero sets do not invalidate that assertion. Your correction to the \(x^2\) example is exactly right. Such an observable can still have a nonzero coefficient at a *smaller asymptotic scale*.

### Important boundary qualification

If \(Rg\) is not closed, “constant on \(K^{-1}(0)\cap Rg\)” can be insufficient. Boundary zeros in the closure of the prior support can dominate the integral. State the hypothesis on the compact support/closure used for concentration, or use the small-sublevel property directly.

**Worth a unit?** Worth a theorem family in the C2/C3 unit; probably not a separate unit unless packaging the Var/source certificate adapters is substantial.

---

## (e) C4: the joint ratio theorem is the right empirical counterpart

Yes. State the abstract result as follows.

Let \(a_n>0\) eventually and suppose
\[
\bigl(a_nZ_n[\varphi_1],\ldots,a_nZ_n[\varphi_q],a_nZ_n[1]\bigr)
\Rightarrow
(L_{\varphi_1},\ldots,L_{\varphi_q},L_1),
\]
with \(L_1>0\) a.s. and valid finite-sample denominators. Then
\[
\boxed{
\bigl(\widehat\mu_n(\varphi_1),\ldots,\widehat\mu_n(\varphi_q)\bigr)
\Rightarrow
\left(\frac{L_{\varphi_1}}{L_1},\ldots,\frac{L_{\varphi_q}}{L_1}\right).
}
\]

The proof is the continuous mapping theorem for division, continuous wherever the last coordinate is nonzero. Separate marginal convergence is not sufficient.

### Connection to the existing layer

The intended assembly is:

1. apply the field CLT once;
2. map the field to the **vector** of coefficient functionals;
3. control each normalized remainder in probability;
4. use finite-dimensional/vector Slutsky;
5. divide.

Explicit checks:

* continuity, or Gaussian-a.s. continuity, of the coefficient vector;
* strict positivity and finiteness of \(L_1\);
* signed-observable support for numerator certificates;
* common normalization and common underlying Gaussian field.

If the existing numerator theorem only accepts nonnegative amplitudes, bounded observables can sometimes be shifted by a constant and recovered by subtraction.

### A useful expectation corollary

For \(|\varphi|\le M\), the finite-sample posterior expectations are bounded by \(M\). Thus convergence in distribution also gives
\[
\mathbb E[\widehat\mu_n(\varphi)]
\longrightarrow
\mathbb E[L_\varphi/L_1].
\]
No separate denominator inverse-moment estimate is needed for this bounded-observable conclusion.

Keep all three quantities distinct:
\[
\mathbb E[L_\varphi/L_1],
\qquad
\frac{\mathbb E L_\varphi}{\mathbb E L_1},
\qquad
\frac{c_\varphi}{c_1}.
\]
They need not coincide; the middle expression might not even be defined.

The annealed identity and tilted Gaussian moments do **not** replace this theorem. They address different operations of averaging and normalization.

**Priority:** this is C’s highest-value headline. C2/C3 are cheaper and complementary, and establish exactly the deterministic special cases that survive empirical fluctuation.

---

# Q2. Order and stopping point

Recommended order:

1. **E, short initial pass.** Add the four distinctions you listed, plus annealed versus expected normalized posterior.
2. **C1.** Small, reusable, explicitly conditional.
3. **C2/C3 plus coefficient consistency.** One compact package, with a.s. and in-probability wrappers around a pathwise estimate.
4. **Joint empirical ratio theorem and its field-CLT specialization.** The substantive empirical endpoint.
5. **E, final pass.** Update the mirror to reflect the new empirical theorem and its actual mode of convergence.
6. **D, optional.**

D is mathematically worthwhile as an exact next-order benchmark, but less urgent than making the empirical semantics and joint ratio theorem precise. Its second coefficient is sensitive to the exact kernel, scaling convention, and cutoff; avoid presenting it as a universal next-order resolution coefficient.

**Recommended stopping point:** after the joint ratio specialization and final audit. Defer both a general ULLN development and D unless they serve a concrete next theorem.

If joint assembly proves unexpectedly expensive, a sound interim endpoint is C1–C3 with the **abstract** joint ratio theorem landed and its missing specialization premises explicitly recorded.

---

# Q3. Lean/Mathlib design

## Avoid real suprema in the core ULLN hypothesis

Prefer
```lean
∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop,
  ∀ w ∈ S, |Khat n ω w - K w| ≤ ε
```
over a real-valued `iSup`.

Why:

* real `iSup`/`sSup` requires boundedness bookkeeping;
* compactness alone does not bound an arbitrary empirical phase;
* a supremum over an uncountable parameter space introduces measurability issues when used as a random variable;
* the proof only uses eventual uniform inequalities.

Even better for the reusable pathwise estimate: accept an explicit error bound \(e\), then specialize to a sequence \(\varepsilon_n\). For convergence in probability, a **measurable scalar error envelope** is especially convenient.

If the phase already lives in a continuous-map or bounded-continuous-function space, its norm is a natural alternative: boundedness and norm measurability then come from the function-space setup.

## C1 implementation

Useful design choices:

* use `IsProbabilityMeasure μ`;
* take `0 ≤ R` a.e., `Integrable R μ`, and an explicit \(A>0\);
* take `AEStronglyMeasurable φ μ` and an a.e. bound \(\|\varphi\|\le M\);
* prove weighted integrability before manipulating integrals;
* prove denominator positivity explicitly—Lean’s totalized division will not enforce it.

The elementary bound is friendly to the Bochner integral and can be stated for Banach-valued observables. Keep the scalar real version first if that avoids API overhead.

Your listed integral lemmas are in the right area, but `integral_mono` applications generally require the relevant integrability obligations. An explicit bound often makes `Integrable.mono'`-style arguments useful. Exact signatures should be checked locally.

## C2 implementation

Separate three layers:

1. **Deterministic inequality** with fixed \(n,\kappa,a,e\).
2. **Pathwise asymptotic theorem** using eventual bounds.
3. **Probability wrapper** for a.s. or in-probability convergence.

This keeps product measurability and probability topology out of the exponential-integral proof.

Additional obligations to budget for:

* finite prior measure and positive small-sublevel mass;
* integrability and strict positivity of each empirical normalizer;
* measurability of parameterized integrals for the probabilistic wrappers;
* compact-gap existence for C3;
* the joint/vector convergence API and the a.s.-continuous mapping theorem at the random denominator for C4.

The potentially substantial missing bridge is **joint coefficient/remainder assembly**, not the posterior concentration inequality. Given the layer you described, that is where I would spend the new formalisation effort.
