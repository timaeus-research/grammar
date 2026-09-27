## 1. Fidelity and the DCIX interface

**At the level of the supplied statements, DCVII–DCIX match the advertised claims.** This is not an independent source/code audit.

- **DCVII:** correct normalisation and conditional Gaussian reduction. It proves an exact representation, **not yet** the two-term asymptotic.
- **DCVIII:** correct half-Gamma second derivative and hence the explicit depth-three flat-prior polynomial. Reflection supplies the missing second derivative; it does not supply the third.
- **DCIX:** the averaged polar coefficients are justified **under the stated analytic domination hypothesis**. This is not yet an unconditional result for the naive Bayes model.

### Keep DCIX’s interface; add a geometric adapter

Domination of the continuation remainder \(H_\lambda\) is the right **abstract averaging interface**. Do not replace it. Add a theorem deriving its hypotheses from fibre amplitudes and cutoffs, along the DCIV route.

The important subtlety is that **logarithmic integrability of \(M_\pm\) alone generally does not suffice**. Continuing across \(s=\tfrac12\) introduces
\[
M^{1-2s},
\]
so domination on a complex neighbourhood needs a small **negative moment of \(M\)**.

For example, consider fibres built from
\[
\int_0^{M_\lambda}t^{-2s}a_\lambda(t)
          \log^2(t/M_\lambda)\,dt,
\qquad 0<M_\lambda\le1,
\]
with measurable amplitude families satisfying
\[
|a_\lambda(0)|\le W_\lambda,\qquad
|a_\lambda(t)-a_\lambda(0)|\le W_\lambda t.
\]
After subtracting the explicit polar part, a convenient sufficient majorant on
\(\lvert s-\tfrac12\rvert<r<\tfrac12\) is
\[
W_\lambda(1+M_\lambda^{-2r})
              (1+|\log M_\lambda|^4)\in L^1(\nu).
\]
The fourth logarithmic power accommodates a derivative of the regularised log² term. Lower-log terms can be included with their coefficients absorbed into the weight.

**Actual naive Bayes verification needs:**

1. Measurability of \(M_\pm\), amplitudes, and their remainder families.
2. Uniform-in-fibre amplitude/Lipschitz bounds, allowing an integrable base-dependent weight.
3. Negative-moment estimates at every boundary face and corner.
4. A separate treatment of any positive-measure set where \(M=0\); a null boundary can simply be excluded a.e.

Locally, if
\[
M\asymp d^\beta,\qquad W\lesssim d^{-\eta},
\qquad d\nu\lesssim d^{a-1}\,dd,
\]
the sufficient condition is
\[
2r\beta+\eta<a.
\]
At corners, check the analogous condition in each boundary coordinate.

**Recommendation:** allow DCIX’s averaging theorem on an arbitrary open neighbourhood of \(\tfrac12\), rather than requiring the entire half-plane \(\Re s<1\). The polar conclusion needs only a small neighbourhood; demanding domination throughout the half-plane creates unnecessary geometric work.

---

## 2. Ranked next targets

The following Lean statements are schematic interfaces, not assertions about existing identifier names.

### 1. Blow-up Laurent coefficients and their convention bridge

**Highest value/effort: a genuinely new explicit consequence of the existing closed zeta formula.**

Put \(t=w+\tfrac12\). Avoid differentiating Gamma at its pole: regularise first,
\[
t^2\zeta(-\tfrac12+t)
   =2^{-1/2}e^{3t\log2}\Gamma(1+t)^2.
\]
The right side is analytic at zero. Its value and first derivative give both coefficients immediately.

```lean
def blowupZetaReg (t : ℂ) :=
  Complex.exp ((3 * t - 1 / 2) * Real.log 2) *
    Complex.Gamma (1 + t) ^ 2

theorem blowupZetaReg_hasDerivAt_zero :
    HasDerivAt blowupZetaReg
      (((3 * Real.log 2 - 2 * Real.eulerMascheroniConstant) /
        Real.sqrt 2 : ℝ) : ℂ) 0 := ...

theorem blowupZeta_laurent :
    (fun t : ℂ =>
      blowupZeta (-1 / 2 + t) -
        a / t^2 - b / t)
      =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := ...
```

Route: Gamma recurrence on a punctured neighbourhood, `hasDerivAt_Gamma_one`, then analytic Taylor divisibility by \(t^2\). No \(\Gamma''(\tfrac12)\) is needed.

Bundle candidate **(e)** here:
\[
C_{\alpha,k}=(-1)^k A_{\alpha,k}
\]
when \(A\) denotes the Laurent coefficients of the positive-moment zeta and \(C\) those of its negative-moment counterpart. In particular \(A_{\alpha,1}=-C_{\alpha,1}\). That bridge is useful but not a standalone day-sized target.

### 2. Depth-two Gaussian asymptotic via the renormalised exponential integral

**Best direct completion of an outstanding headline.** The Euler-constant identity is cleanly obtainable by integration by parts; no new special function is needed.

First prove
\[
\int_0^\infty
 \frac{e^{-v}-\mathbf1_{(0,1)}(v)}v\,dv=-\gamma.
\]
Use the Mellin-derivative machinery already exercised in DCVIII to obtain
\[
\int_0^\infty e^{-v}\log v\,dv=\Gamma'(1)=-\gamma.
\]
Integrate by parts on finite intervals, splitting at \(1\), and pass to the endpoints. The cancellation is
\[
e^{-\delta}\log\delta+\int_\delta^\infty\frac{e^{-v}}v\,dv
=
(e^{-\delta}-1)\log\delta
+\int_\delta^1\frac{e^{-v}-1}v\,dv
+\int_1^\infty\frac{e^{-v}}v\,dv.
\]

Then define
\[
J(\varepsilon)=\int_0^\infty\frac{e^{-v}}{\sqrt{v(v+\varepsilon)}}\,dv.
\]
The elementary comparison term is
\[
\int_0^1\frac{dv}{\sqrt{v(v+\varepsilon)}}
 =2\log\frac{1+\sqrt{1+\varepsilon}}{\sqrt\varepsilon}.
\]
For the remaining kernel difference, split at \(\varepsilon\) and \(1\). This gives
\[
J(\varepsilon)=\log(1/\varepsilon)+\log4-\gamma
                 +O(\varepsilon|\log\varepsilon|).
\]

Lean-facing endpoint:

```lean
theorem J_two_term :
    (fun ε => J ε - (Real.log (1 / ε) + Real.log 4 - γ))
      =O[𝓝[>] 0] (fun ε => ε * |Real.log ε|) := ...

theorem gaussLaplace2_two_term :
    (fun N =>
      gaussLaplace2 N -
        (Real.log N + 3 * Real.log 2 - γ) /
          Real.sqrt (2 * Real.pi * N))
      =O[atTop] (fun N => N ^ (-(3 / 2 : ℝ)) * Real.log N) := ...
```

The exact substitution is
\[
Z_N=\frac{J(1/(2N))}{\sqrt{2\pi N}},\qquad N>0.
\]

**Scheduling:** the renormalised-integral identity is a safe day-sized landing. The full quantitative \(J\)-estimate is the stretch target; do not promise both if interval-integral estimates consume the day.

### 3. A shrinking-cutoff domination adapter for DCIX

Prove the sufficient criterion above, together with a power-face integrability corollary:

```lean
-- Schematic: H is the explicit regularised log² fibre integral.
theorem logSq_remainder_deriv_dominated
    (hr : 0 < r ∧ r < 1 / 2)
    (hmajorant :
      Integrable (fun λ =>
        W λ * (1 + (M λ) ^ (-2 * r)) *
          (1 + |Real.log (M λ)| ^ 4)) ν)
    ... :
    ∃ bound, Integrable bound ν ∧
      ∀ᵐ λ ∂ν, ∀ s ∈ Metric.ball (1 / 2) r,
        ‖deriv (H λ) s‖ ≤ bound λ := ...
```

This is a reusable geometric-to-analytic bridge, not another averaging theorem. Actual verification for \(M_\pm\) should be a subsequent corollary once their facewise formulas are in hand.

**Other candidates:** cone tail estimates are likely cheap, but converting them into the note’s exact expansion needs the precise tail argument and prefactors; a posterior mean additionally needs numerator/denominator control. Generalising the rank-one tilt beyond alignment is worthwhile linear algebra, but does not by itself close the Morse–Bott or orientation gap. Neither presently outranks the three above.

---

## 3. Exact blow-up Laurent data and normalisations

For the **displayed, unrescaled** zeta
\[
\zeta(w)=2^{3w+1}\Gamma(w+\tfrac12)^2,
\]
write \(t=w+\tfrac12\). Then
\[
\boxed{
\zeta(-\tfrac12+t)
=
\frac{1}{\sqrt2\,t^2}
+\frac{3\log2-2\gamma}{\sqrt2\,t}
+O(1).
}
\]

Thus, in the positive-moment Laurent convention
\[
\zeta(w)=\frac{A_{1/2,2}}{(w+\tfrac12)^2}
        +\frac{A_{1/2,1}}{w+\tfrac12}+O(1),
\]
the coefficients are
\[
\boxed{
A_{1/2,2}=\frac1{\sqrt2},\qquad
A_{1/2,1}=\frac{3\log2-2\gamma}{\sqrt2}.
}
\]
Using only the half-point digamma value, the latter is equivalently
\[
\boxed{
A_{1/2,1}
=\frac{7\log2+
       2\,\Gamma'(\tfrac12)/\Gamma(\tfrac12)}{\sqrt2}.
}
\]
The Gamma-at-one route is shorter in Lean.

To prevent convention drift, record all three related objects:

| Object | Double/log coefficient | Simple/constant coefficient |
|---|---:|---:|
| Positive-moment zeta \(\zeta(w)\), at \(w=-\tfrac12\) | \(1/\sqrt2\) | \((3\log2-2\gamma)/\sqrt2\) |
| Negative-moment zeta \(\zeta(-s)\), at \(s=\tfrac12\) | \(1/\sqrt2\) | \((2\gamma-3\log2)/\sqrt2\) |
| Corresponding Laplace polynomial multiplying \(N^{-1/2}\) | \(\sqrt{\pi/2}\) | \(\sqrt{\pi/2}(5\log2-\gamma)\) |

The final row follows from integrating
\[
x^{-1/2}\bigl[a\log(1/x)+b\bigr]
\]
against \(e^{-Nx}\): the constant is \(\sqrt\pi\,b-a\Gamma'(\tfrac12)\). **Its asymptotic validity still requires the transfer/remainder theorem**; Laurent algebra alone does not formalise that passage.

Any Gaussian-prior normalising factor absent from the displayed zeta multiplies every coefficient above.