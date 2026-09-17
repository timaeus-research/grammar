## 1. Decision: write up now

**Ranking for the paper’s narrative:**
\[
\boxed{\text{VIII}>\text{IX}>\text{VII}>\text{IV}>\text{III}.}
\]

| Rank | Candidate | Assessment |
|---|---|---|
| 1 | **VIII: mirror §10.5** | The landed theorems already support a coherent account of posterior expectations. This is now the highest-value addition. |
| 2 | **IX: a nontrivial exact check** | A two-site exchangeability theorem gives both an exact identity and a sign. It explains what averaging the quotient does. |
| 3 | **VII: differential interpolation** | A useful completion of the interpolation picture, but not necessary once the exact integral identity is available. |
| 4 | **IV: higher fixed-sample cumulants** | A genuine algebraic extension, but variance already demonstrates the mechanism. |
| 5 | **III: convergent source expansion** | Attractive analytic closure, but it adds less to the central question than the results already landed. |

**ONE next: VIII.** Stop the current theorem programme at **DLX**, rather than making either all-order cumulants or second-order interpolation a prerequisite for presenting it.

There is one essential qualification:

* **Closed:** fixed-sample quotient/variance expansions, and the compact Gaussian posterior’s Stein, response, replica, and exact interpolation calculus.
* **Not closed:** an identification theorem saying that the averaged empirical posterior mean converges to that compact Gaussian posterior expectation.

The missing identification in VI is not a minor technical omission. Thus §10.5 can present two rigorous parts, but must not silently identify their limiting objects.

In particular, distinguish
\[
\mathbb E\langle f\rangle_G
=
\frac{\rho(f)}{\rho(K)}
+\int_0^1\mathbb E H_f(\sqrt{s}G)\,ds
\]
from the additional, currently unavailable assertion
\[
\lim_n\mathbb E\!\left[\frac{Z_n[f]}{Z_n[1]}\right]
=
\mathbb E\langle f\rangle_G.
\]

For a **fixed bounded observable**, uniform integrability of genuine posterior means is automatic from
\[
\left|\frac{Z_n[f]}{Z_n[1]}\right|\leq \|f\|_\infty.
\]
Once convergence in law to the *identified* compact posterior mean exists, convergence of expectations follows without inverse-evidence estimates. This does not apply automatically to rescaled errors, retained quotients, or unbounded observables.

---

## 2. IX has a worthwhile answer: two-site minority enhancement

Take two sites with normalized base masses \(p,1-p\), where \(0<p<1\). Write their positive posterior weights as \(U,V\), so that the posterior mass of the first site is
\[
Q_p=\frac{pU}{pU+(1-p)V}.
\]

Assume only that **\((U,V)\) is exchangeable**. Then:

\[
\boxed{
\mathbb E Q_p-p
=
\frac{p(1-p)(1-2p)}{2}\,
\mathbb E\!\left[
\frac{(U-V)^2}
{(pU+(1-p)V)((1-p)U+pV)}
\right].
}
\]

No moments of \(U\) or \(V\) are needed: the relevant ratios are bounded when \(p\in(0,1)\).

Consequently,
\[
\boxed{
\begin{aligned}
0<p\leq\tfrac12&\implies p\leq\mathbb E Q_p\leq\tfrac12,\\
\tfrac12\leq p<1&\implies \tfrac12\leq\mathbb E Q_p\leq p.
\end{aligned}}
\]

Thus exchangeable random weights move the **averaged posterior mass toward equal allocation**, not necessarily toward the original base mass.

If \(p\neq\tfrac12\) and \(\mathbb P(U\neq V)>0\), the displacement from \(p\) is strict.

### Application to your Gaussian posterior

Let
\[
U=S_\lambda(G_1),\qquad V=S_\lambda(G_2),
\]
using the same positive weight function at both sites. If the centered Gaussian pair satisfies
\[
\mathcal C_{11}=\mathcal C_{22},
\]
then \((G_1,G_2)\), hence \((U,V)\), is exchangeable. The displayed identity applies directly.

For strictness, it suffices that \(S_\lambda\) is injective and
\[
\mathcal C_{11}-\mathcal C_{12}>0.
\]
Indeed, \(G_1-G_2\) then has positive variance. Under the usual positive-temperature weight, strict monotonicity of \(S_\lambda\) supplies injectivity.

This is a useful sanity anchor because it gives:

* **An exact closed value:** if \(p=\tfrac12\), then \(\mathbb E Q_p=\tfrac12\), even with nontrivial disorder.
* **A nontrivial sign:** a minority site gains expected posterior mass; a majority site loses it.
* **A counterexample to positive-observable monotonicity:** choose the indicator of a majority site. The averaged posterior expectation decreases, even for a covariance matrix with strictly positive entries.
* **A check on interpolation:** its integrated response must equal the displayed exchangeability expression.

For general unequal masses, I would not promise an elementary formula involving only the Gaussian covariance parameters and the parameters of \(S_\lambda\). The exact sign and bounded expectation identity are already informative.

### Lean-typable statements

These statements deliberately use ordinary positive random weights, so they do not depend on the repo-specific arguments of `compactAvg`.

```lean
namespace Grammar

def twoSitePosteriorMass (p u v : ℝ) : ℝ :=
  p * u / (p * u + (1 - p) * v)

theorem twoSitePosteriorMass_symm_sub
    (p u v : ℝ)
    (hp : 0 < p) (hp₁ : p < 1)
    (hu : 0 < u) (hv : 0 < v) :
    (twoSitePosteriorMass p u v +
        twoSitePosteriorMass p v u) / 2 - p =
      (p * (1 - p) * (1 - 2 * p) / 2) *
        ((u - v) ^ 2 /
          ((p * u + (1 - p) * v) *
           ((1 - p) * u + p * v))) := by
  sorry

theorem integral_twoSitePosteriorMass_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (U V : Ω → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hpos : ∀ᵐ ω ∂μ, 0 < U ω ∧ 0 < V ω)
    (hexch :
      MeasureTheory.Measure.map (fun ω => (U ω, V ω)) μ =
      MeasureTheory.Measure.map (fun ω => (V ω, U ω)) μ)
    (p : ℝ) (hp : 0 < p) (hp₁ : p < 1) :
    (∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ) - p =
      (p * (1 - p) * (1 - 2 * p) / 2) *
        ∫ ω,
          (U ω - V ω) ^ 2 /
            ((p * U ω + (1 - p) * V ω) *
             ((1 - p) * U ω + p * V ω)) ∂μ := by
  sorry

end Grammar
```

The especially compact narrative corollary is
\[
\mathbb E Q_p\in
[\min(p,\tfrac12),\max(p,\tfrac12)].
\]

**This is the one extra mathematical result I would choose if an additional theorem is wanted. Stop at the exchangeability identity and its Gaussian specialization.**

---

## 3. VII: valid, but the endpoint identity alone is insufficient

The appropriate addition is the **first derivative identity**, not second-order interpolation.

Set
\[
A(s)=\mathbb E\langle f\rangle_{\sqrt{s}G},
\qquad
R(s)=\mathbb E H_f(\sqrt{s}G),
\]
where \(H_f\) uses the **original covariance \(\mathcal C\)**.

The desired statement is
\[
s\in(0,1)\implies \operatorname{HasDerivAt}(A,R(s),s).
\]

A reusable Lean statement isolating the final analytic step is:

```lean
theorem hasDerivAt_of_interpolation_primitive
    (A R : ℝ → ℝ)
    (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      A t = A 0 + ∫ u in (0 : ℝ)..t, R u)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt A (R s) s := by
  sorry
```

The missing mathematical input is the primitive identity **for every upper endpoint**, not merely at \(1\). Applying the landed interpolation theorem to the scaled field provides it once covariance scaling is recorded correctly: the response for covariance \(s\mathcal C\) is \(s\) times the response for \(\mathcal C\).

Five replicas are a plausible representation of the next response, but that is a fresh layer of differentiation and domination—not a necessary closure condition.

---

## 4. Corrections and naming cautions before the write-up

### A. The main conceptual distinction

Use **“compact Gaussian posterior expectation”** for the averaged object currently identified. Do not call it **“the leading empirical posterior expectation”** without the VI identification theorem.

Also distinguish throughout:
\[
\mathbb E[Z[f]/Z[1]]
\quad\text{from}\quad
\mathbb E Z[f]/\mathbb E Z[1].
\]

### B. Half and first moments

The notation
\[
\langle\phi\rangle^{1/2}
\]
is genuinely misleading: readers will interpret it as a square root.

Prefer
\[
\langle\phi\sqrt t\rangle_{\mu_g},
\qquad
\langle\phi t\rangle_{\mu_g},
\]
or explicitly indexed notation such as \(\langle\phi\rangle_{g;1/2}\).

`compactHalfAvg` and `compactFirstMoment` are not averages under separately normalized tilted laws. They are joint-posterior weighted integrals. Names such as

* `compactSqrtTimeMoment`,
* `compactTimeMoment`

would describe the mathematics more directly.

### C. `gibbsJoint`

The name is sound. Say:

> A probability measure on \(K\times\mathbb R\), concentrated on \(K\times(0,\infty)\).

Avoid saying its **topological support is contained in** \(K\times(0,\infty)\): \(t=0\) may belong to the topological support even though it has zero mass.

### D. “Banach-form Stein”

This is accurate if qualified as:

> Stein’s identity for the compact-posterior observable, expressed using its Fréchet derivative.

DLX does not, merely by proving this instance, establish Stein’s identity for every admissible Fréchet-differentiable functional on \(C(K,\mathbb R)\).

### E. Source expansion terminology

The moment-generating function
\[
z\mapsto\langle e^{zf}\rangle_g
\]
is entire for bounded \(f\). Its logarithm is **not generally entire**. Candidate III should say:

> The analytic logarithm on a uniform zero-free disk about zero.

Also, \(\Psi=\mathbb E\log\langle e^{\varepsilon f}\rangle_G\) is the **quenched** source. Its coefficients are expected conditional cumulants, not cumulants of the disorder-averaged posterior law.

### F. Response and covariance

Describe \(H_f\) as a **signed covariance-interpolation response**. Positive semidefiniteness—or even pointwise positivity—of the kernel does not make it nonnegative for \(f\geq0\). The two-site theorem above makes that failure explicit.

**Bottom line:** DLX closes the compact Gaussian calculus. Write-up is now the priority; the best optional final theorem is two-site exchangeable-weight balancing, not another all-orders extension.