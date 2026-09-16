**The proposed identity is right for the admissible deformation fields supplied by the bridge.** The main corrections are:

1. **Boundedness of \(H\) alone is not the right hypothesis.** Use the resolved standard form \(H\circ g_\alpha=u^{k_\alpha}\zeta_\alpha\), with the required regularity and bounds on \(\zeta_\alpha\).
2. The summands on the RHS are intrinsic population coefficients; **their sum becomes a frozen coefficient system only after the convergence and identification theorem**.
3. The Gaussian limit gives an **analytic functional of a Gaussian field**, not automatically its Wiener-chaos decomposition.

I would pursue the real Mellin-moment route, preceded by a weight-shift/depth-stabilization lemma.

## 1. Correctness and convergence of \((★)\)

### Exponent bookkeeping

Your bookkeeping is correct:
\[
N^{p/2}
\left[
C^{\rm pop}_{\mu+p/2,q}[\varphi H^p]\,
N^{-(\mu+p/2)}(\log N)^q
\right]
=
C^{\rm pop}_{\mu+p/2,q}[\varphi H^p]\,
N^{-\mu}(\log N)^q.
\]
There is no extra log mixing: multiplication by \(N^{p/2}\) shifts the exponent and leaves \(q\) unchanged.

Thus the intended statement is
\[
\boxed{
C_{\mu,q}[H,\varphi]
=
\sum_{p=0}^{\infty}\frac1{p!}
C^{\rm pop}_{\mu+p/2,q}[\varphi H^p].
}
\]

The equality of evidence functions obtained by expanding the exponential is useful motivation, but **does not itself justify coefficient matching**. That is precisely what the chartwise theorem must establish.

### The essential hypothesis is resolved divisibility

Bounded \(H\) is insufficient for the general claim. For example, with
\[
K(x)=x^2,\qquad H(x)=1,\qquad x\in[0,1],
\]
the frozen evidence has an \(e^{\sqrt N}\) factor and does not have the proposed power-log expansion.

Your bridge gives something much stronger:
\[
H\circ g_\alpha=u^{k_\alpha}\zeta_\alpha,
\qquad K\circ g_\alpha=u^{2k_\alpha}.
\]
For a finite atlas with bounded \(\zeta_\alpha\), this implies, on the relevant supports,
\[
|H|\le B\sqrt K.
\]
Consequently,
\[
-NK+\sqrt N|H|
\le -NK+B\sqrt{NK}
\le -\tfrac12 NK+\tfrac12B^2.
\]
This is the structural estimate behind the coefficient-level exponential expansion.

For the smooth engine, add the regularity needed for its face derivatives and integrations. A good theorem hypothesis is therefore **admissibility in a compatible standard-form atlas**, not merely boundedness of the global field.

### What growth must be controlled?

For a fixed \((\mu,q)\), the useful target is a bound of the form
\[
\left|C^{\rm pop}_{\mu+p/2,q}[\varphi H^p]\right|
\le
A\,B^p(1+p)^M\Gamma(p/2+a),
\tag{1}
\]
with \(a>0\) and constants independent of \(p\). Finitely many exceptional small \(p\) can be treated separately.

Here:

- \(B\) depends on bounds for the resolved deformation fields;
- \(M\) comes from finitely many spatial derivatives;
- the Gamma growth comes from the shifted moment;
- logarithmic moments can be absorbed into a slightly larger Gamma bound.

Then division by \(p!\) gives absolute convergence. Your “roughly \(p!^{-1/2}\)” intuition is correct, up to exponential and polynomial factors.

**The nontrivial part is obtaining a fixed derivative order as \(p\) varies.** One should not estimate the population coefficients as arbitrary coefficients at an exponent tending to infinity. Their observables have the special vanishing factor \(u^{kp}\), which cancels that apparent increase in required order.

### Intrinsicness and lattices

All summands are intrinsic once the population coefficient systems for \(\varphi H^p\) exist in the permitted observable class. Absolute convergence then makes the RHS an intrinsic number.

But phrase the logical status carefully:

> The RHS is an absolutely convergent series of intrinsic population coefficients, and the theorem identifies this series with the intrinsic frozen coefficient.

Before that theorem, the RHS is not yet known to be an `IsFrozenCoeff` system.

Also arrange a **common exponent lattice stable under addition of \(1/2\)**. Refining denominator \(Q\) to \(2Q\) is a safe choice. Prove lattice-refinement invariance once and avoid carrying parity side conditions through the main theorem.

## 2. Recommended proof route

### Recommendation: moment expansion, with a structural lemma first

I rank the routes:

1. **Real Mellin-moment expansion plus weight-shift/stabilization.**
2. Uniform cutoff expansions, if the required uniform remainder estimate is already nearly available.
3. Taylor tree plus recentering.

The first route attacks a single coefficient directly. Route (i) asks for substantially more: control of a whole infinite family of remainders. Route (ii) introduces recentering bookkeeping without removing the fundamental interchange estimates.

You can accurately describe the recommended route as **avoiding complex Mellin transforms and Laurent operators**. It still uses the engine’s existing real Mellin moments.

### The moment majorant

In the standard normalization where \(\tau=\sqrt s\),
\[
\sum_{p\ge0}\frac{\tau^p|\zeta|^p}{p!}
=e^{\sqrt s|\zeta|}.
\]
After finitely many spatial derivatives, the corresponding absolute sum is bounded by
\[
C(1+\sqrt s)^M e^{B\sqrt s}.
\]
Combined with the moment kernel, the majorant has the shape
\[
C\,s^{a-1}(1+|\log s|)^q
(1+\sqrt s)^M e^{-s+B\sqrt s}.
\tag{2}
\]

At infinity this is straightforward because
\[
-s+B\sqrt s\le -s/2+B^2/2.
\]

**Do not omit the endpoint \(s=0\).** The \(e^{-s}\) decay says nothing there. Use the actual admissible moment exponents and the engine’s existing logarithmic-moment integrability results.

For Lean, proving integrability of the absolute sum and using a sum/integral interchange theorem may be cheaper than first proving the explicit Gamma estimate (1). That avoids needing Stirling-type asymptotics.

### The central structural lemma: absorb the monomial into the weight

You need the coefficient-level counterpart of
\[
u^h\,\eta(u)(u^k\zeta(u))^p
=
u^{h+pk}\,\eta(u)\zeta(u)^p.
\tag{3}
\]

This is important for both identification and estimates. It separates:

- the \(p\)-dependent monomial vanishing, handled by the weight;
- the amplitude \(\eta\zeta^p\), handled by a fixed-order product-rule estimate.

Schematically, the singular coordinate candidate exponents obey
\[
\frac{h_i+pk_i+1+r_i}{2k_i}
=
\frac p2+\frac{h_i+1+r_i}{2k_i}.
\]
Thus the population target \(\mu+p/2\), after shifting the weight by \(pk\), has the same relative cutoff geometry as the empirical target \(\mu\).

This is the reason a uniform depth statement should exist.

### The depth trap is real

Do **not** initially assert \((★★)\) for arbitrary `empCoeffAtDepth` values at the same depth. A raw finite-depth expression need not behave well under the shift.

Instead:

1. prove the weight-shift identity;
2. prove that a suitable depth condition is preserved under
   \[
   (h,\mu)\mapsto(h+pk,\mu+p/2);
   \]
3. establish the moment identity at stabilized depths;
4. descend to canonical `empCoeffRect`.

If the existing sufficient bound for \(L_0\) depends crudely on the absolute size of \(\mu\), it may falsely force depth to grow with \(p\). In that case, add a sharper **relative-cutoff lemma** rather than trying to dominate derivatives of unbounded order.

### Face integrals and derivatives

The remaining interchanges should be separated:

- finite sums over faces and derivative indices: algebraic;
- the infinite \(p\)-sum with a Mellin integral: absolute-integrability theorem;
- the infinite \(p\)-sum with `faceCoeffInt`: a uniform-on-the-face majorant;
- spatial differentiation with the exponential series: locally uniform convergence of the required derivative series.

For a fixed derivative order \(r\), derivatives of \(\zeta^p\) contribute falling-factorial factors bounded by a polynomial in \(p\). A robust bound uses \(B=1+\|\zeta\|_{C^r}\), avoiding awkward \(B^{p-r}\) and zero-norm cases.

The ladder then identifies each term. **The ladder alone does not prove the whole cube-coefficient identity**: the monomial weight shift and stabilized face bookkeeping are the other half.

## 3. How to describe the result to the authors

Relative to the future-work remark as you describe it, this is a direct answer to that programme. I would say:

> Under the standard-form admissibility hypotheses, the intrinsic frozen empirical coefficient functional is the absolutely convergent exponential generating series of intrinsic population coefficient functionals evaluated on powers of the global deformation field:
> \[
> C_{\mu,q}[H,\varphi]
> =
> \sum_{p\ge0}\frac1{p!}
> C^{\rm pop}_{\mu+p/2,q}[\varphi H^p].
> \]
> For the empirical model, take \(H=H_n=\sqrt n(K-K_n)\). The identity is independent of the compatible resolution atlas and requires no choice of normal splitting.

I would use **“all-orders generating-series identity”** rather than unqualified “closed form.”

The exponential expansion itself is elementary. The substantive contribution is:

- identification of the shifted population coefficient;
- absolute convergence at coefficient level;
- resolution/atlas independence;
- applicability to the global empirical field;
- formal verification of the interchanges and stabilization.

I cannot certify broader literature novelty from the remark alone.

## 4. The stochastic consequence

The right first statement is
\[
H_n\Rightarrow G
\quad\Longrightarrow\quad
\bigl(C_{\mu_j,q_j}[H_n,\varphi_j]\bigr)_{j=1}^m
\Rightarrow
\bigl(C_{\mu_j,q_j}[G,\varphi_j]\bigr)_{j=1}^m,
\]
where, pathwise,
\[
C_{\mu,q}[G,\varphi]
=
\sum_{p\ge0}\frac1{p!}
C^{\rm pop}_{\mu+p/2,q}[\varphi G^p].
\]

### Which topology?

Use a topology controlling the finitely many **resolved quotient-field jets**
\[
\zeta_\alpha=(H\circ g_\alpha)/u^{k_\alpha}
\]
needed by the selected coefficients, including their values along the relevant faces.

Two cautions:

1. The required control is not generally just a finite jet at each chart origin. Face integrals can depend on functions along positive-dimensional faces.
2. Uniform control of \(H\) itself does not control these quotient fields near the divisor.

The useful analytic theorem is that the coefficient series converges **uniformly on bounded sets of an appropriate quotient-field \(C^L\) space**. Its terms are continuous homogeneous polynomials there, hence its sum is continuous.

Then use the continuous mapping theorem. This is cleaner than interchanging \(n\to\infty\) with the infinite \(p\)-sum probabilistically.

So:

- if the available chartwise joint jet law is a functional law in this sufficiently strong topology, with joint compatibility, it should suffice;
- if it is only finite-dimensional convergence of evaluations, additional tightness/control is needed.

### Not yet a Wiener-chaos decomposition

The expression in ordinary powers \(G^p\) is a **Gaussian power-series representation**, not a homogeneous Wiener-chaos expansion. Ordinary powers contain lower-order chaos components through contractions.

A genuine chaos decomposition requires Wick ordering and regrouping. It also requires the relevant integrability, typically \(L^2\), which is not automatic. Moment functions can grow like \(e^{cG^2}\), and Gaussian inputs do not guarantee square integrability for arbitrary covariance.

Thus I would initially claim:

> The limiting coefficient is a continuous analytic functional of the Gaussian deformation field, with an intrinsic population-coefficient power-series representation.

Keep Wiener chaos as a separate theorem.

## 5. Suggested staged Lean plan

The following are schematic statements, not claims about exact existing signatures.

### C1. Coefficient infrastructure

Prove:

- refinement to a common half-shift-stable lattice;
- zero-field population specialization;
- monomial absorption (3);
- stabilization compatible with \((h,\mu)\mapsto(h+pk,\mu+p/2)\).

```lean
-- Schematic
theorem popCoeffRect_monomial_absorb :
  popCoeffRect (η * monomial (p • k) * ζ ^ p) h k b ρ q
    =
  popCoeffRect (η * ζ ^ p) (h + p • k) k b ρ q
```

The exact weight convention may alter the displayed arguments.

### C2. Analytic series lemmas

First prove the reusable moment theorem:

```lean
theorem mellinMom_exp_series
    (hadm : MomentSeriesAdmissible ...) :
  mellinMom (fun τ => η * Real.exp (τ * ζ)) μ ℓ
    =
  ∑' p : ℕ,
    (1 / (p.factorial : ℝ)) *
      mellinMom (fun τ => η * τ ^ p * ζ ^ p) μ ℓ
```

Pair it with an absolute-summability statement. Lift this through the finite derivative and face operations, retaining estimates uniform on bounded admissible jet sets.

### C3. Canonical cube identity

Prove summability separately from equality:

```lean
theorem summable_popCoeffRect_shifted
    (hadm : RectDeformationAdmissible ...) :
  Summable (fun p : ℕ =>
    (1 / (p.factorial : ℝ)) *
      empCoeffRect
        (η * (monomial k * ζ) ^ p) 0 h k b
        (μ + (p : ℝ) / 2) q)
```

```lean
theorem empCoeffRect_eq_tsum_popCoeffRect
    (hadm : RectDeformationAdmissible ...) :
  empCoeffRect η ζ h k b μ q
    =
  ∑' p : ℕ,
    (1 / (p.factorial : ℝ)) *
      empCoeffRect
        (η * (monomial k * ζ) ^ p) 0 h k b
        (μ + (p : ℝ) / 2) q
```

Keep depth parameters out of this public theorem.

### D. Aggregate and identify intrinsically

For a finite compatible atlas:

1. apply C3 chartwise;
2. commute the finite chart sum with `tsum`;
3. use compatibility on unit-weight supports to identify the population observable as \(\varphi H^p\);
4. identify zero-field aggregated coefficients with population intrinsic coefficients;
5. identify the empirical aggregated coefficients with the intrinsic frozen system.

At the API level, a relational theorem fits your current design:

```lean
-- Schematic
theorem frozenCoeff_eq_tsum_population
    (hH : AdmissibleResolvedDeformation ...)
    (hc : IsFrozenCoeff νχ K H obs Q c)
    (hd : ∀ p, IsFrozenCoeff νχ K 0
      (fun x => obs x * H x ^ p) Q (d p)) :
  Summable (fun p => invFactorial p * d p (μ + p / 2) q)
    ∧
  c μ q = ∑' p, invFactorial p * d p (μ + p / 2) q
```

Insert the lattice and index admissibility hypotheses explicitly. This formulation avoids introducing choice-defined coefficient functions prematurely.

Your landed uniqueness and atlas-realization theorems should make this stage mostly transport rather than analysis.

### E. Empirical and stochastic wrappers

First specialize pathwise to \(H_n(\omega)\), combining the deterministic theorem with `ae_isFrozenCoeff_leadCoeff`. This gives the a.s. generating-series identity without any CLT work.

Then add, separately:

1. local uniform summability on quotient-jet bounded sets;
2. continuity of each selected coefficient map;
3. joint convergence by the continuous mapping theorem;
4. optional \(L^2\)/Wick-chaos results under additional hypotheses.

**Bottom line:** proceed with \((★★)\). The decisive preliminary task is proving that monomial absorption makes the shifted population coefficient a **fixed-relative-depth** problem. Once that is established, the exponential-series majorant should make the moment route substantially cleaner than uniform asymptotic remainders or recentering the Taylor tree.