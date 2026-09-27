## 1. Fidelity check

**The supplied statements match the intended results**, with one documentation correction. This is an audit of the supplied interfaces and calculations, not an independent repository build.

### Gaussian logarithmic moment

The cutoff bookkeeping is correct:
\[
\begin{aligned}
J&=\frac14\left[\ell(\ell-\gamma)
+\frac12\left(\gamma^2+\frac{\pi^2}{6}\right)-\frac12\ell^2\right]\\
&=\frac{(\ell-\gamma)^2}{8}+\frac{\pi^2}{48}
=\frac{R_0^2}{2}+\frac{\pi^2}{48},
\qquad \ell=\log2.
\end{aligned}
\]

Moving the cutoff from \(1\) to \(1/2\) **adds** the interval contribution. That contribution is positive for \(1/u\), but negative for \(\log u/u\). Both signs in the supplied statements are right.

**Correction:** the DCXXXVIII headline’s consequence uses
\[
((\log2-\gamma)R_0+2J)/\pi.
\]
It should use the coefficient in your DCXXXI definition:
\[
\boxed{C_3=((3\log2-\gamma)R_0+2J)/\pi+(2/s)Q.}
\]
This matters for the claimed final closed form.

### Cone derivative and normalization

Writing \(D_0=\int w_{0,a}\), the normalized law is \(N(a,1)\), so
\[
G=-\frac{Q_1D_0-P_0M_1}{D_0^2}
=-\operatorname{Cov}_a(T_+,|T|).
\]
The mixed spellings of \(w_{0,a}\) do not change this.

The normalization is exactly right. With \(\delta=N^{-1/2}\),
\[
E_N=\tfrac12+\delta\int F_\delta\gamma,\qquad
N\left(E_N-\tfrac12-\frac{\delta}{\sqrt\pi}\right)
=\frac1\delta\int(F_\delta-F_0)\gamma.
\]
Thus the pointwise \(O(\delta^2K)\) remainder gives the stated \(C_2/\sqrt N\) bound.

### Envelope and \(268e^4\)

The envelope follows from
\[
|\text{remainder}|
\le \delta^2\left(
\frac{|G|M_1}{D_\delta}
+\frac{M_3}{D_\delta}
+\frac{P_0}{D_0}\frac{M_2}{D_\delta}\right),
\]
using \(P_0/D_0\le |a|+1\). Your bounds give precisely
\[
\frac{e^{|a|}}{c_0}
\left[6s(a^2+1)(|a|+1)+4s|a|^3+16\right].
\]

The numerical domination constant is also safe. Put \(r=|a|\). Since \(s\le3\), the bracket is at most
\[
30r^3+18r^2+18r+34.
\]
Use
\[
r\le r^2/16+4,\qquad
r^k e^{-3r^2/16}\le
\begin{cases}
1&k=1,\\2&k=2,\\6&k=3.
\end{cases}
\]
Then
\[
(30r^3+18r^2+18r+34)e^{r-r^2/4}
\le e^4(180+36+18+34)=268e^4.
\]
No missing Gaussian normalization or exponential factor is apparent.

The numerical nonzero next coefficient is **evidence of sharpness**, not yet a formal sharpness theorem.

---

## 2. Next three targets, ranked

My ranking is:

1. **Cone symmetry and exact second coefficient**, using one-dimensional Gaussian integration by parts.
2. **The pole-subtracted Mellin-to-\(Q\) bridge**, independently of evaluating the Mellin transform.
3. **The regularized Gamma jet giving the proposed finite part.**

These separate an analytic limit theorem from special-function algebra. The full exact-\(Q\) package should not be advertised as one day.

### Target 1: cone exactness—avoid correlated polar coordinates entirely

Define
\[
m(a)=E|a+G|,\qquad
b(a)=2\int_0^a\gamma(t)\,dt.
\]
Then
\[
b'=2\gamma,\quad |b|\le1,\quad b(\pm\infty)=\pm1,
\qquad m(a)=a\,b(a)+2\gamma(a).
\]

First prove the pointwise reflection identity
\[
\boxed{G(a)+G(-a)=-(a^2+1-m(a)^2).}
\]
Indeed, the reflected positive-part moments add to \(E_aT^2=a^2+1\), and the reflected positive-part means add to \(m(a)\). This is cleaner than formalizing an odd covariance term separately.

Suggested interfaces:
```lean
noncomputable def coneAbsMean (a : ℝ) : ℝ :=
  (∫ t, |t| * coneTilt 0 a t) / ∫ t, coneTilt 0 a t

theorem coneCorrectionDeriv_add_neg (a : ℝ) :
    coneCorrectionDeriv a + coneCorrectionDeriv (-a) =
      -(a ^ 2 + 1 - coneAbsMean a ^ 2)

theorem coneSecondCoeff_eq_symmetric :
    coneSecondCoeff =
      -(1 / 2 : ℝ) *
        ∫ a, (a ^ 2 + 1 - coneAbsMean a ^ 2) * gaussDensity a
```

**The exact moment needs only three scalar identities.** Write
\[
B=\int b^2\gamma,\quad I=\int a b\gamma^2,\quad H=\int\gamma^3.
\]
Then:
\[
B=\frac13,\qquad I=H,\qquad
\int a^2b^2\gamma=B+4I.
\]
Their proofs are respectively:

* integrate \((b^3)'=6b^2\gamma\);
* integrate \((\gamma^2)'=-2a\gamma^2\);
* integrate \(\gamma'=-a\gamma\).

Consequently,
\[
\int m^2\gamma=B+8I+4H=\frac13+12H.
\]
The ordinary Gaussian integral gives
\[
H=\frac1{2\pi\sqrt3},\qquad
\boxed{\int m^2\gamma=\frac13+\frac{2\sqrt3}{\pi}.}
\]
Hence \(c_2=-1+\frac12\int m^2\gamma=-5/6+\sqrt3/\pi\).

```lean
theorem integral_coneAbsMean_sq :
    ∫ a, coneAbsMean a ^ 2 * gaussDensity a =
      1 / 3 + 2 * Real.sqrt 3 / Real.pi

theorem coneSecondCoeff_eq :
    coneSecondCoeff = -(5 / 6 : ℝ) + Real.sqrt 3 / Real.pi
```

**Scope:** symmetry is comfortably day-sized. The full exact result is a plausible day if truncated Gaussian moments and improper integration-by-parts infrastructure are already available; otherwise split those two milestones. Prove IBP on finite intervals, then discharge boundary terms using \(|b|\le1\) and Gaussian decay.

This is substantially less infrastructure than polar coordinates, Price’s theorem, or Sheppard’s formula.

### Target 2: the Mellin residual bridge

Let
\[
M(z)=\int_0^\infty v^{z-1}Z_2(v^2)\,dv,\qquad
q(v)=Z_2(v^2)-1_{v>1}\frac{2\log v+c}{sv}.
\]

The useful decomposition is:

```lean
-- Proposed names/interfaces; use the existing q definition.
theorem depthThree_mellin_pole_integral
    {z : ℝ} (hz : z < 1) :
    (∫ v in Ioi (1 : ℝ),
      v ^ (z - 1) * ((2 * Real.log v + c) / (s * v))) =
      2 / (s * (1 - z) ^ 2) + c / (s * (1 - z))

theorem depthThree_mellin_sub_poles
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthThreeMellin z -
        (2 / (s * (1 - z) ^ 2) + c / (s * (1 - z))) =
      ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * q v

theorem tendsto_depthThree_mellin_sub_poles :
    Tendsto
      (fun z => depthThreeMellin z -
        (2 / (s * (1 - z) ^ 2) + c / (s * (1 - z))))
      (𝓝[<] (1 : ℝ)) (𝓝 depthThreeQint)
```

Prove **integrability of both summands before splitting their integrals**.

For dominated convergence, restrict eventually to \(1/2\le z<1\):

* \(0<v\le1\): \(q=Z_2(v^2)\le1\), so the integrand is bounded by \(v^{-1/2}\);
* \(v>1\): \(v^{z-1}\le1\), so the existing integrable bound on \(|q|\) suffices.

You do not actually need the full strength of the outer decay estimate here—only its integrable envelope.

**Scope:** this is an honest day-sized unit and reusable finite-part infrastructure.

### Target 3: regularize before taking the Gamma jet

Do **not** Taylor-expand the singular \(\Gamma(\varepsilon/2)\) directly. Set
\[
B(\varepsilon)=
2^{\varepsilon/2}
\frac{\Gamma(1/2-\varepsilon/2)}{\sqrt\pi}
\Gamma(1+\varepsilon/2)^2.
\]
The proposed Mellin expression becomes
\[
M(1-\varepsilon)=\frac{2}{s\varepsilon^2}B(\varepsilon).
\]

The regular jet is
\[
B(0)=1,\qquad B'(0)=c/2,\qquad
B''(0)=c^2/4+5\pi^2/24.
\]
Therefore
\[
\frac{B(\varepsilon)-1-(c/2)\varepsilon}{\varepsilon^2}
\longrightarrow \frac{c^2}{8}+\frac{5\pi^2}{48}.
\]

Lean-facing core:
```lean
theorem tendsto_depthThreeGammaFactor_second :
    Tendsto
      (fun ε =>
        (depthThreeGammaFactor ε - 1 - (c / 2) * ε) / ε ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c ^ 2 / 8 + 5 * Real.pi ^ 2 / 48))
```

Use DCVIII and `GammaSecondDerivOne`; establish enough local differentiability to justify the second-order Peano remainder. Two isolated derivative values alone are not the Taylor theorem.

The resulting special-function finite part is
\[
\boxed{\frac{c^2+5\pi^2/6}{4s}.}
\]

**Scope:** a reasonable day with the existing complex derivative adapters. Prefer whichever real/complex formulation minimizes new coercion infrastructure.

### The remaining exact-\(Q\) stage: Mellin evaluation

Your transform formula is correct:
\[
M(z)=\frac{2^{-1-z/2}}{\pi}
\Gamma(z/2)\Gamma((1-z)/2)^2,\qquad 0<z<1.
\]

Clean decomposition:

1. Scalar reduction \(Z_2(v^2)=\int(1+v^2g^2)^{-1/2}\gamma(g)\,dg\).
2. Beta integral, for \(g\ne0\):
   \[
   \int_0^\infty\frac{v^{z-1}}{\sqrt{1+g^2v^2}}\,dv
   =|g|^{-z}\frac{\Gamma(z/2)\Gamma((1-z)/2)}{2\sqrt\pi}.
   \]
3. Negative Gaussian absolute moment:
   \[
   \int |g|^{-z}\gamma(g)\,dg
   =2^{-z/2}\Gamma((1-z)/2)/\sqrt\pi.
   \]
4. Nonnegative Tonelli, followed by finiteness/integrability.
5. Combine the transform, residual bridge, and regularized jet.

Treat \(g=0\) **a.e.**, not as an ordinary scalar substitution case. This stage is day-sized only if the needed improper Beta integral is readily available.

Finally, substitution of exact \(J,Q\) gives
\[
C_3=\frac{(4\log2-2\gamma)^2+\pi^2}{4\pi}.
\]

### Other candidates

| Candidate | Assessment |
|---|---|
| NB generic power/log face certificate | Honest day-sized library target: integrability on \((0,1)\) for \(x^\alpha|\log x|^k\), \(\alpha>-1\), then finite products by Tonelli. Does **not** itself establish face exponent inequalities or joint measurability. |
| Blow-up \(\alpha_1\) | Potentially day-sized if the local expansion and remainder machinery already exist. Separate the residue coefficient from its Laplace normalization. |
| `FourTermData` propagation | Plausibly day-sized **once its new moment data are supplied**. It gives four leading coefficients, not every constant term at arbitrary depth. |
| \(\int h\log^2x/x\), \(\Gamma'''(1)\) | Not a cheap repetition: duplication relates third derivatives at \(1/2\) and \(1\), but does not independently supply the new \(\zeta(3)\) datum. |
| All constant terms for \(L\ge4\) | Not day-sized. Arbitrarily deep constants require progressively higher jet/moment data; exact \(Q\) alone does not supply them. |
| NB KL-versus-surrogate remainder | Not honestly day-sized without an already quantified local remainder and a uniform integrable envelope. |

---

## 3. Convention hazards worth pinning explicitly

* **Cutoff endpoints:** changing open/closed endpoints preserves integrals, not pointwise identities. Keep the exact `Ioc` conventions in the splitting lemmas.
* **Kernel orientation:** for \(v<1\), `logKernel v u` is negative. With the next weight,
  \[
  \int \mathrm{logKernel}(v,u)\log^2u\,du=\tfrac13\log^3v,
  \]
  whereas the absolute integral is \(\tfrac13|\log v|^3\). Do not copy the previous nonnegativity argument.
* **Tilt normalization:** add a simp lemma:
  ```lean
  @[simp] theorem coneTilt_zero (a t : ℝ) :
      coneTilt 0 a t = Real.exp (-t ^ 2 / 2 + a * t)
  ```
  Normalize this spelling before algebra involving \(M_1,Q_1,D_0\).
* **Two Gaussian normalizations:** \(D_0=s e^{a^2/2}\) normalizes the tilted \(t\)-law; `gaussDensity a` normalizes the outer \(a\)-average. Neither factor may be silently omitted.
* **Constant names:** reserve \(c=3\log2-\gamma\), distinguish it from \(2R_0=\log2-\gamma\), and fix the headline discrepancy now.
* **Exactness boundary:** keep “integral-defined with rate,” “closed form proved,” and “numerically observed next coefficient” separate in the note.