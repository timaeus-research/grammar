## 1. Fidelity check

**On the supplied statements, all three targets are met.** I have not inspected the pinned source or its Mathlib dependency; the checks below are mathematical/API-design checks, not a build audit.

### (a) Depth-five recursion: the coefficients are correct

Write \(s=\sqrt{2\pi}\), \(P_4=A_4\ell^3+B_4\ell^2+C_4\ell+D_4\). The moment part of the step is
\[
\frac2s\left(R_0P_4+2JP_4'+2J_2P_4''+\frac43J_3P_4'''\right).
\]
Consequently,
\[
D_5=\frac{D_4+2C_4R_0+8B_4J+24A_4J_2}{s},
\]
and
\[
E_5=\frac2s\left(Q_4+D_4R_0+2C_4J+4B_4J_2+8A_4J_3\right).
\]
In particular, **all four coefficients you singled out are right**. The flat-part and shift identities also agree with this recursion.

DCLIV’s advertised improvement is sound. Its description should say that sharper rates are **not supplied by the current residual bound**, rather than ruling out alternative arguments exploiting cancellation.

### (b) Mellin jet: correct, with \(0\le k\le L-1\)

The principal-pole polynomial is
\[
P_L(\ell)=2^{-(L-1)/2}\pi^{-L/2}
 \sum_{k=0}^{L-1}g_k\frac{\ell^{L-1-k}}{(L-1-k)!},
\]
with exactly your
\[
g_k=[u^k]\Gamma(\tfrac12-u)\Gamma(1+u)^L2^{(L-1)u}.
\]
The residue algebra is correct; an asymptotic theorem additionally requires the contour/remainder justification.

A convenient normalized jet is
\[
\frac{\Gamma(\tfrac12-u)\Gamma(1+u)^L2^{(L-1)u}}{\sqrt\pi}
=
\exp\left(
a_Lu+\sum_{r\ge2}
\frac{2^r-1+L(-1)^r}{r}\zeta(r)u^r
\right),
\]
where
\[
a_L=(L+1)\log2-(L-1)\gamma.
\]

For depth five set \(a=6\log2-4\gamma\). Through degree four, the exponent is
\[
au+\frac{2\pi^2}{3}u^2+\frac{2\zeta(3)}3u^3+5\zeta(4)u^4.
\]
Thus
\[
\boxed{D_5=\frac1{4\pi^2}
 \left(\frac{a^3}{6}+\frac{2\pi^2a}{3}+\frac{2\zeta(3)}3\right)}
\]
and
\[
\boxed{
E_5=\frac{g_4}{4\pi^{5/2}}
=\frac1{4\pi^2}
 \left(\frac{a^4}{24}+\frac{\pi^2a^2}{3}
       +\frac{2a\zeta(3)}3+25\zeta(4)\right).
}
\]
Equivalently,
\[
E_5=\frac{a^4}{96\pi^2}+\frac{a^2}{12}
       +\frac{a\zeta(3)}{6\pi^2}+\frac{5\pi^2}{72}.
\]

These remain **derivation-level identifications of the integral-defined constants**, not consequences already formalized by DCLVI.

### (c) Unconditional `toReal` equality: yes, with the stated measurability

For a measurable nonnegative real integrand:

* finite lintegral implies Bochner integrability and the usual equality;
* infinite lintegral implies nonintegrability, hence Lean’s real integral is zero, matching `ENNReal.toReal ⊤`.

Thus the unconditional identity is legitimate. Pointwise finiteness of `prodDensity` supports identifying the real integrand with the ENNReal integrand’s `toReal`; it does **not** itself establish fibre integrability.

Also, a finite-valued **real** closed-form equality alone would not establish finiteness of the ENNReal density: the earlier ENNReal closed-form theorem supplies that distinction.

## 2. The all-depth engine

### The right invariant

H1 is a good invariant. There is no need to store the limit separately: it follows from the rate. The residual is defined from \(P\), and \(Q\) should ordinarily be defined from that residual—not supplied independently.

Your conservative exponent update
\[
m'=\max(m+1,\deg P)
\]
is valid given the indicated coarse estimates. **But the \(m+1\) loss is avoidable.**

For \(r=\sqrt N\), use the quadratic Gaussian bound
\[
|\gamma(v/r)-\gamma(0)|\le C\min(v^2/r^2,1).
\]
If \(|q(v)|\le K(1+\log v)^m/v^2\) for \(v>1\), then
\[
\begin{aligned}
\left|\int_0^\infty(\gamma(v/r)-\gamma(0))q(v)\,dv\right|
&\le \frac C{r^2}\int_0^r v^2|q(v)|\,dv
   +C\int_r^\infty|q(v)|\,dv\\
&\le C'\frac{(1+\log r)^m}{r}.
\end{aligned}
\]
The bounded inner residual handles \(v<1\). **The logarithmic exponent is preserved.**

There is an equally useful combined-cutoff estimate. With \(a=N^{-1/2}\),
\[
\int_0^a\frac{h(x)}xP(\ell+2\log x)\,dx
=
\int_0^1\frac{h(ay)}yP(2\log y)\,dy.
\]
Since \(|h(ay)|\le C a^2y^2\),
\[
\left|\int_0^a\frac{h(x)}xP(\ell+2\log x)\,dx\right|
\le \frac{C_P}{N}.
\]
This avoids every growing cutoff coefficient.

**Recommended invariant:** a fixed \(m\), preserved by the step. Your current \(m=1\) input can therefore propagate indefinitely. This does not yet give the sharper \(N^{-1}\)-scale remainder.

### Lean-facing representation

Use **`Polynomial ℝ` externally**, finite coefficient sums internally. `Fin n → ℝ` introduces unnecessary dimension transports at every step.

Schematic interface:

```lean
def polyResidual (L : ℕ) (P : Polynomial ℝ) (v : ℝ) : ℝ :=
  gaussLaplaceL L (v ^ 2) -
    if 1 < v then P.eval (2 * Real.log v) / v else 0

def polyResidualIntegral (L : ℕ) (P : Polynomial ℝ) : ℝ :=
  ∫ v in Set.Ioi 0, polyResidual L P v

def HasPolyRate (L : ℕ) (P : Polynomial ℝ) (m : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
    |Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N)| ≤
      K * (1 + Real.log N) ^ m / Real.sqrt N
```

Define a zero-constant primitive explicitly by coefficients if the pinned polynomial API lacks a convenient antiderivative:
\[
\operatorname{prim}(P)=\sum_k
 \operatorname{monomial}(k+1)\bigl(P_k/(k+1)\bigr).
\]
Then
\[
\operatorname{stepPoly}(P,Q)=
s^{-1}\operatorname{prim}(P)+
\frac2s\sum_{j=0}^{\deg P}
 \frac{2^jJ_j}{j!}\,(\operatorname{derivative}^{[j]}P)
+\operatorname{C}(2Q/s).
\]

Target:

```lean
theorem HasPolyRate.step
    (hL : 1 ≤ L) (h : HasPolyRate L P m) :
    HasPolyRate (L + 1)
      (stepPoly P (polyResidualIntegral L P)) m
```

Adjust `hL` to the existing scalar recursion’s domain.

For differentiation, avoid manually differentiating polynomial compositions. Put
`R := P.comp (C ℓ + C 2 * X)` and compose the polynomial evaluation derivative with `Real.hasDerivAt_log hx`. The expected API ingredients are `Polynomial.hasDerivAt`, `HasDerivAt.comp`, and `Polynomial.eval_comp`; **verify exact names/arguments on the pin**. The resulting derivative is
\[
R'(\log x)/x=2P'(\ell+2\log x)/x.
\]

### Cost and cheaper deliverable

* **Depth-five linear-log rate:** roughly **1–2 focused days**, using the quadratic residual split and combined cutoff. It gives \(m=1\), not merely \(m=2\).
* **Reusable quantitative residual lemma plus cutoff lemma:** **2–3 days**.
* **Clean all-depth engine, generic moments, polynomial algebra, and instantiated regression tests:** **4–7 days**, not an honest one-day promise.

The main risk is generic integration/algebra infrastructure, not the analytic argument. I would prove the two quantitative lemmas first and use depth five as their acceptance test.

## 3. Other candidates

### Important correction: the fixed-\(\lambda\) naive-Bayes density is not generally normalized

The supplied closed form already disproves mass \(1\) at every fixed \(\lambda\). At \(\lambda_1=\lambda_2=\tfrac12\),
\[
M_+=M_-=\tfrac14,\qquad V=\tfrac1{16},
\]
and each sign interval has mass
\[
2\int_0^{1/4}\log^2\!\left(\frac{1/4}{\mu}\right)d\mu=1.
\]
Thus the two intervals alone have total mass **2**.

The pushforward density is a **joint density in \((\lambda,\mu)\)**; fixing \(\lambda\) does not automatically produce a normalized conditional density.

Assuming the expected support theorem, its marginal mass is
\[
m(\lambda)=
2M_+\left(\log\frac V{M_+^2}+2\right)
+
2M_-\left(\log\frac V{M_-^2}+2\right).
\]
The conditional density is \(\rho(\lambda,\mu)/m(\lambda)\).

### Ranked candidates

| Candidate | Assessment |
|---|---|
| **NB a.e. fibre finiteness/integrability and marginal mass** | Best inexpensive measure-theoretic deliverable; about **½–1 day** if the joint mass theorem is ready |
| **NB every interior fibre integrable, with explicit mass** | **1–2 days** if support and ENNReal closed forms are available |
| **\(J_2,J_3\)–Gamma-derivative bridge** | Good next analytic deliverable; **2–4 days** with reusable differentiated-Gamma integral infrastructure |
| Cone \(c_3\) | Cannot responsibly call day-sized without the exact remainder input; coefficient calculation alone is not the theorem |
| Blow-up \(N^{-3/2}\log N\) coefficient | Lower priority: requires another justified remainder order |
| Exact \(\Gamma'''(1)\), \(\Gamma''''(1)\) via zeta | Infrastructure-dependent; **not safely day-sized** without an existing local log-Gamma/polygamma expansion |

Tonelli gives **a.e.** fibre finiteness from finite joint mass. It does not upgrade that to every interior \(\lambda\).

### Top interface 1: NB finiteness first, real integrability second

Prove ENNReal finiteness before stating the real-integral theorem; otherwise `toReal ⊤ = 0` can hide the missing analytic content.

```lean
theorem nbFibreDensity_lintegral_ne_top
    (h₁ : l₁ ∈ Set.Ioo (0 : ℝ) 1)
    (h₂ : l₂ ∈ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ z : ℝ, nbFibreDensity l₁ l₂ z) ≠ ⊤

theorem integrable_nbFixedDensity
    (h₁ : l₁ ∈ Set.Ioo (0 : ℝ) 1)
    (h₂ : l₂ ∈ Set.Ioo (0 : ℝ) 1) :
    Integrable (fun z : ℝ => nbFixedDensity ((l₁, l₂), z))

theorem integral_nbFixedDensity_eq_marginal
    (h₁ : l₁ ∈ Set.Ioo (0 : ℝ) 1)
    (h₂ : l₂ ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ z : ℝ, nbFixedDensity ((l₁, l₂), z)) =
      nbMeanMarginal (l₁, l₂)
```

Also prove `nbFibreDensity … z ≠ ⊤` for a.e. `z`; this makes the conversion from the genuine ENNReal density explicit.

### Top interface 2: general cutoff moments, without zeta evaluation

Let
\[
I_k=\int_0^\infty
 (e^{-u}-1_{(0,1]}(u))\frac{\log^k u}{u}\,du.
\]
Integration by parts gives
\[
\boxed{I_k=\frac{\Gamma^{(k+1)}(1)}{k+1}.}
\]
For your Gaussian cutoff convention,
\[
\boxed{
J_k=
\frac{1}{2^{k+1}(k+1)}
\sum_{r=0}^{k+1}\binom{k+1}{r}
(\log2)^{k+1-r}\Gamma^{(r)}(1).
}
\]
Here \(J_0=R_0\) and \(\Gamma^{(0)}(1)=1\).

I would stage the implementation:

1. Define Gamma log-moments
   \[
   G_r=\int_0^\infty e^{-u}\log^r u\,du.
   \]
2. Prove integrability and `I_k = G_(k+1)/(k+1)` by integration by parts.
3. Prove the displayed \(J_k\) formula with \(G_r\).
4. Separately identify `G_r = iteratedDeriv r Real.Gamma 1`.

This separates elementary improper-integral estimates from differentiation under the integral. Neither Bohr–Mollerup nor the mere existence of zeta-sum lemmas supplies the missing higher-derivative bridge.

**My next-round choice:** depth-five linear-log rate plus NB marginal/fibre integrability. Then build the all-depth engine around the quadratic residual estimate—without baking an unnecessary logarithmic loss into its invariant.