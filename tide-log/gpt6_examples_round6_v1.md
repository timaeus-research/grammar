## 1. Fidelity: endorsed, with one remaining analytic qualification

Based on the supplied statements, **DCX–DCXIII meet the round-5 specifications**. I have not independently checked the repository.

### Gaussian remainder

The constants are consistent. The three error contributions are
\[
\varepsilon,\qquad
\varepsilon(\log(1/\varepsilon)+1),\qquad
\varepsilon,
\]
so their sum is precisely \(\varepsilon(\log(1/\varepsilon)+3)\). Substituting \(\varepsilon=1/(2N)\) and dividing by \(\sqrt{2\pi N}\) gives the stated bound, valid for \(N\geq \tfrac12\). In particular, it implies the advertised asymptotic remainder.

This is stronger than the requested two-term asymptotic: the explicit bound should remain the primary interface.

### Domination adapter

The four-piece bound has the right structure. For each **fixed** \(0<r<\tfrac12\), it admits a coarser bound of the suggested form
\[
B_\lambda\leq C_r W_\lambda
 (1+M_\lambda^{-2r})(1+|\log M_\lambda|^4).
\]
For example, a sufficiently generous choice is
\[
W=(1+|\phi_0|+L)(1+\ell^2+|c|+|b|),
\]
assuming \(L\geq0\). The cutoff terms require at most cubic growth in \(|\log M|\); degree four is harmless slack. The \(4/\delta^2\) factor is absorbed into \(C_r\), not into a new face singularity.

**What is still needed:** integrability of \(B\) and joint measurability do not, by themselves, discharge every hypothesis of `averaged_naiveBayes_polar`. One must also establish:

- integrability of the polar coefficients;
- integrability of the remainder values;
- identification of the actual model transform with the averaged fibre transform, including any required Fubini/change-of-variables justification.

A useful strengthening is to replace remainder integrability at every point by **integrability at one basepoint**. On the convex ball,
\[
\|H_\lambda(s)\|
 \leq \|H_\lambda(\tfrac12)\|+rB_\lambda.
\]
Thus basepoint integrability plus derivative domination suffices. A direct bound for \(H_\lambda(\tfrac12)\) should also fit the coarse envelope above.

Finally, the theorem identifies a principal part; claiming an **actual order-three pole** additionally requires nonvanishing of \(\int\phi_\lambda(0)\,d\nu\).

---

## 2. Ranked round-6 targets

### 1. Blow-up Laplace expansion by exact Gaussian scaling

**Highest value-per-effort, provided the model-identification lemma is available.** Do not start with a general Mellin-transfer theorem.

A concrete model matching DCX is the unnormalised integral
\[
B(N)=\int_{\mathbb R^2}
 e^{-(x^2+y^2)/2}\,e^{-2Nx^2y^2}\,dx\,dy.
\]
Its zeta function is exactly
\[
\int_{\mathbb R^2}(2x^2y^2)^w e^{-(x^2+y^2)/2}\,dx\,dy
 =2^{3w+1}\Gamma(w+\tfrac12)^2.
\]
With the DCVII normalisation,
\[
B(N)=2\pi\,\mathrm{gaussLaplace2}(4N).
\]

**Proposed interfaces**—new names, not checked Lean code:
```lean
theorem blowupLaplace_eq_gauss {N : ℝ} (hN : 0 ≤ N) :
    blowupLaplace N = 2 * Real.pi * gaussLaplace2 (4 * N)

theorem blowupLaplace_two_term_bound {N : ℝ} (hN : 1 / 8 ≤ N) :
    |blowupLaplace N -
      Real.sqrt (Real.pi / 2) / Real.sqrt N *
        (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant)| ≤
    Real.sqrt (Real.pi / 2) / Real.sqrt N *
      ((Real.log (8 * N) + 3) / (8 * N))
```
Then obtain the `IsBigO` corollary immediately.

**Route:** Gaussian-density normalisation/Fubini → exact scaling → DCXII at \(4N\) → logarithm and square-root algebra.

**Important scope boundary:** the zeta closed form does not itself establish that this is the note’s original geometric integral. Name the original model, prior, and measure explicitly and prove their identification. If that requires substantial chart assembly, the honest one-day deliverable is the explicitly defined model above—not “global blow-up assembly completed.”

As a consistency check, formal coefficient transfer gives
\[
\Gamma(\tfrac12)A_2\log N+
\Gamma(\tfrac12)A_1-\Gamma'(\tfrac12)A_2
=\sqrt{\pi/2}\,[\log N+5\log2-\gamma].
\]
Local Laurent data alone are not an asymptotic-transfer theorem.

### 2. A face-integrability certificate, plus a basepoint adapter

**Honest day-sized target:** a reusable certificate that discharges DCXIII’s analytic hypotheses. **Not yet an honest promise:** verification for the actual naive Bayes envelope, whose formula and face coordinates are absent from the supplied material.

First expose the coarse bound:
```lean
theorem logSqDomBound_le_envelope
    (hr : 0 < r) (hr1 : r < 1 / 2)
    (hM0 : 0 < M) (hM1 : M ≤ 1) (hL : 0 ≤ L) :
    logSqDomBound ℓ c b M L φ₀ r ≤
      envelopeConst r *
        ((1 + |φ₀| + L) * (1 + ℓ^2 + |c| + |b|)) *
        (1 + M ^ (-2 * r)) * (1 + |Real.log M|^4)
```
Then a measurable-majorant corollary:
```lean
theorem integrable_logSqDomBound_of_envelope
    -- measurability, admissible r and M, L ≥ 0
    (hEnv : Integrable (fun l =>
      W l * (1 + M l ^ (-2 * r)) *
        (1 + |Real.log (M l)|^4)) ν)
    -- pointwise domination of the coefficient factor by W
    : Integrable (fun l =>
        logSqDomBound (ℓ l) (c l) (b l) (M l)
          (L l) (φ l 0) r) ν
```

The face lemma should use **a lower bound on \(M\)**:
\[
M(d)\geq \kappa d^\beta,\quad 0<M\leq1,\qquad
W(d)\lesssim d^{-\eta}(1+|\log d|^k).
\]
Against a density bounded by \(C d^{a-1}\), the resulting majorant is
\[
C' d^{a-1-\eta-2r\beta}(1+|\log d|^{k+4}),
\]
integrable when
\[
\boxed{\eta+2r\beta<a.}
\]
Here \(\eta\) must account for **all growth in \(W\)**, not just the Lipschitz constant \(L\).

For corners with product majorants, impose this inequality **coordinatewise**. Also verify bounded tangential factors, Jacobians, and one common positive radius \(r\) across the finite face cover. An upper bound on \(M\) is the wrong direction for negative moments.

For measurability: jointly measurable \((\lambda,t)\mapsto\phi_\lambda(t)\), together with measurable \(\ell,c,b,M\), makes the variable-cutoff integrands measurable. Parameter-integral measurability then gives measurability of \(\lambda\mapsto H_\lambda(s)\), under the applicable measure hypotheses. This is distinct from an integrability/Fubini assertion.

**Do not invent the actual face table:** determining which faces and which \((\beta,\eta,a)\) requires the actual \(M_\pm\), prior density, and fibre-coordinate formulas.

### 3. All-depth Gaussian conditional reduction and leading polar coefficient

**Day-sized:** the exact reduction and leading zeta coefficient.  
**Not reliably day-sized:** the all-depth Laplace asymptotic with an explicit remainder.

Define, with \(\nu_d\) the law of \(d\) independent standard Gaussians,
\[
Z_d(N)=\int \exp\!\left(-\frac N2\Bigl(\prod_{i<d}w_i\Bigr)^2\right)d\nu_d.
\]
Then:
```lean
theorem gaussLaplace_succ_eq_conditional
    (d : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplace (d + 1) N =
      ∫ w : Fin d → ℝ,
        1 / Real.sqrt (1 + N * (∏ i, w i)^2) ∂stdGaussianPi d
```
**Route:** split the last coordinate, apply the existing one-dimensional Gaussian integral, and use boundedness by \(1\) for integrability. No Bessel functions are involved.

For this normalisation,
\[
\zeta_L(w)=
 2^{(L-1)w}\pi^{-L/2}\Gamma(w+\tfrac12)^L,
\]
so regularisation by \(\Gamma(1+t)^L\) gives
\[
\lim_{t\to0}t^L\zeta_L(-\tfrac12+t)
 =2^{-(L-1)/2}\pi^{-L/2}.
\]
Expose this as a `Tendsto` theorem, or as the value at zero of a named regularised function.

The corresponding **candidate Laplace leading term** is
\[
\boxed{
\frac{(\log N)^{L-1}}
 {(L-1)!(2\pi)^{(L-1)/2}\sqrt N}
}.
\]
Thus the \(L=2\) normalisation does **not** carry unchanged to higher depth.

To prove that asymptotic, rather than merely its polar prediction, one needs an additional transfer argument or a quantitative induction on the product distribution. The conditional identity is an excellent interface, but does not itself supply the logarithmic expansion.

### Remaining candidates

- **Cone averaged posterior:** potentially one day if the exact \(\xi\)-dependent integrand and a uniform integrable majorant are already isolated. Not enough information here to certify that.
- **Rank-one beyond alignment:** an orthogonal-change-of-coordinates lemma can be day-sized with existing Gaussian invariance infrastructure. The Morse–Bott/orientation passage is a larger target.
- **\(H_3\)/\(\zeta(3)\): defer.** A third derivative of reflection at \(1/2\) gives cancellation, not the missing value. One needs additional input such as
  \(\psi''(1)=-2\zeta(3)\), then duplication yields
  \(\psi''(1/2)=-14\zeta(3)\). Reflection alone cannot close this.

---

## 3. Convention hazards

1. **Two meanings of \(w\).** In DCX, \(w\) is the complex zeta variable; in `gaussJ`, it is a positive real integration variable. The substitution \(v=w^2\) is correct:
   \[
   \frac{e^{-v}\,dv}{\sqrt{v(v+\varepsilon)}}
   =\frac{2e^{-w^2}}{\sqrt{w^2+\varepsilon}}\,dw.
   \]

2. **Population versus Mellin signs.** If the transforms are related by \(w=-s\), then
   \[
   (w+\lambda)^{-k}=(-1)^k(s-\lambda)^{-k}.
   \]
   Preserve the distinction between \(A\)-coefficients and the signed \(C\)-coefficients. Any energy rescaling contributes additional factors.

3. **The radius and \(\delta\) are correct.** The even-remainder integrability margin becomes
   \[
   1-2\delta-2r=\tfrac12-r>0.
   \]
   Constants deteriorate near either endpoint of the allowed radius range. Fix \(r\) before averaging; a fibre-dependent radius is not the current interface.

4. **Endpoint indicators are harmless only measure-theoretically.** `(0,1]` and `(0,1)` differ on a null set for Lebesgue integration. They are not pointwise interchangeable in `integral_exp_kernel`. Use an a.e. congruence, not a pointwise rewrite.

5. **Keep normalisations visible.** Probability Gaussian measure versus unnormalised Gaussian volume is exactly the factor \(2\pi\) in the blow-up shortcut. It changes every coefficient.

**Recommended round-6 scope:** scaled blow-up expansion; face-envelope/basepoint certificate; all-depth exact Gaussian reduction and leading polar coefficient. These advance the note without presenting geometric verification or analytic transfer as already proved.