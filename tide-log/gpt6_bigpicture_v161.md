**Verdict:** close the probabilistic integrability gap, but do not reopen the theorem-level deliverables. For the envelope, investigate **monomial/ Mellin-shift cancellation before estimating the growing depths**. That is the potentially decisive simplification.

## A. `hint`: A2 first; a cheaper A1 next; A3 optional

### 1. A2 is worth one packaging layer

Prove the deterministic power-jet estimate, then derive `hint` from:

* a.e. smoothness of the sample field;
* strong measurability of its jet map;
* all finite moments of the relevant jet norms.

Schematically, writing \(J_R\) for the cube jet,
\[
\|J_R(\eta Y^r)\|
 \le C_{\eta,R}(r+1)^R\|J_RY\|^r.
\]
Using \(Y=\mathrm{mono}\,k\cdot\zeta\) directly makes this easiest. A crude reduction to \(J_R\zeta\) introduces an additional \(A_{k,R}^r\); a sharper monomial-specific estimate on the unit cube can avoid that exponential loss.

**Important qualification:** “one moment hypothesis” means a predicate quantifying over all required \(R,r\), not one finite-order `MemLp` assumption. And moments alone do **not** establish `habs`.

### 2. A1 does not need a derivative CLT or Riesz

There is a simpler route from the existing Gaussian **value process**, provided the smooth limit field is genuinely a lift of that process.

1. Interior derivative evaluations are limits of finite differences of value evaluations.
2. Consequently, every finite collection of derivative evaluations is jointly Gaussian: every linear combination is a limit in probability of Gaussian variables.
3. Boundary derivative evaluations follow by continuity from interior points.
4. Approximate the identity on each
   \(C(K,\mathrm{ContinuousMultilinearMap})\)
   by finite-rank partition-of-unity interpolation operators. The multilinear target is finite-dimensional here.
5. For every strong-dual functional \(L\), \(L(T_nJ)\to L(J)\), and each \(L(T_nJ)\) is Gaussian. Closure of Gaussian laws under convergence in distribution finishes.

This bypasses both jet-level CLT and dual representation. Countably many coordinate evaluations also provide the jet-map measurability argument in these separable spaces.

Your holonomy theorem suggests an alternative **Gaussian lifting through an injective continuous linear map on the closed jet-range subspace**. That is mathematically valid with the appropriate standard-Borel/separability machinery, but not necessarily the shortest Lean route. **Do not infer a continuous inverse or norm bounds from holonomy alone.**

Once `IsGaussian` of each jet law lands, Fernique supplies all finite moments and discharges the A2 wrapper.

**Ranking:** A2 → this value-process-based A1 → A3.

### 3. A3 is a separate asymptotic result

Useful, but not a replacement for the limit Wick theorem. The correct route is:

\[
J_n\Rightarrow J,\qquad F(J_n)\ \text{uniformly integrable}
\quad\Longrightarrow\quad
\mathbb E F(J_n)\to\mathbb E F(J),
\]
with continuity, or a.e. continuity, of the relevant coefficient functional established.

Finite-\(n\) moments are not enough: you need **uniform-in-\(n\)** bounds. Joint convergence of finitely many jet functionals is also not automatically convergence of the full nonlinear coefficient. Skip unless finite-sample expectation convergence is a requested output.

## B. Envelope: first cancel the apparent depth growth

I would **not** start by tracking \(K_1(p_r)\).

The Wick summand contains the special amplitude
\[
\eta\,(\mathrm{mono}\,k)^r\zeta^r
\]
and the specially shifted index \(\mu+r/2\). These shifts match.

At the uncompleted local Mellin-transform level, the structural identity is
\[
Z_{\eta(\mathrm{mono}\,k)^r\zeta^r}(s)
   =Z_{\eta\zeta^r}(s-r/2),
\]
because the kernel contributes \(u^{-2ks}\). Thus the geometric pole at \(\mu+r/2\) becomes a pole at the **fixed** index \(\mu\). This should allow fixed-depth control of \(\eta\zeta^r\), rather than depth growing with \(r\).

### The concrete engine target

Prove a **monomial-shift identity for the uncompleted Mellin/polar coefficients**, then recover the completed coefficient by multiplying by \(\Gamma(s)\).

The \(r\)-growth should then be carried by:

* `mellinMom_pow_mul_exp_zero` for the shifted Gamma moment;
* its logarithmic-moment/parameter-derivative companions for higher poles.

Schematically, the coefficient becomes a finite combination of
\[
\Gamma^{(\ell)}(\mu+r/2)
 \times
 \{\text{fixed-index local polar coefficients of }\eta\zeta^r\}.
\]
The number of relevant derivatives is bounded by the pole order. Gamma derivatives introduce only polynomial/logarithmic losses beyond Gamma growth.

That is the route to a bound of the form
\[
|C_r|
 \le C\,A^r(r+1)^N\Gamma(c+r/2)\|J_R\zeta\|^r,
\]
with **fixed \(R\)** for the requested coefficient.

This is a proposed engine lemma, not something the reported depth estimate already proves. Check it first against the existing polar-coefficient identification, including signs, factorials and cutoff conventions.

### What to leave as a hypothesis

Until that shift lemma and its quantitative consequence land, keep `habs`.

Even after A1, **Fernique alone does not give the envelope**: its exponential-square constant may be too small. For the displayed bound, a convenient sufficient condition is
\[
\mathbb E e^{\delta\|J_R\zeta\|^2}<\infty,
\qquad \delta>A^2/4.
\]
The strict margin absorbs polynomial factors.

Document \(W<2\) as the **scalar absolute-series threshold**, not an iff criterion for the general coefficient envelope: coefficients can cancel or vanish, and jet-norm majorants generally lose sharpness.

## C. Optional (α)

**One module only if inexpensive; otherwise skip.**

For numerator blocks \(A_j\), denominator blocks \(B_j\), the standard unreduced representation is
\[
R_j=\frac{N_j}{B_0^{j+1}},
\]
with
\[
N_0=A_0,\qquad
N_j=A_jB_0^j-\sum_{i=1}^j B_iN_{j-i}B_0^{i-1}.
\]
Prove polynomiality and this identity wherever \(B_0\ne0\). No gcd normalization, no new asymptotics. It is presentation infrastructure, not a remaining analytic gap.

## D. Audit and priorities

Nothing reported is inherently vacuous or inconsistent.

* **A(a):** marginal Gaussian laws really are sufficient with the integrable-jet/holonomy argument; joint jet Gaussianity is needed only to derive `hint`, not for the landed averaging theorem.
* **Strip package:** correct that `hE0` uses boundedness of \(\Xi\), obtained from standardized boundedness **plus** the upper bound on \(K\).
* **Strip nonemptiness:** retaining \(\int K^{-\sigma}<\infty\) is legitimate. A nonempty positive strip still requires some \(\sigma>0\) satisfying it; positivity and boundedness of \(K\) alone do not supply that.
* **Measurability:** make sure it is explicit in every probabilistic wrapper; pathwise smoothness alone is not the Bochner measurability proof.

**Priority order:**  
1. A2 moment-to-`hint` wrapper.  
2. Gaussian jet law from Gaussian values and finite differences.  
3. Fixed-index monomial-shift lemma; only then quantitative envelope work.  
4. Optional (α), if cheap.  
5. Skip derivative CLT/Riesz and finite-\(n\) asymptotic Wick for this closure cycle.