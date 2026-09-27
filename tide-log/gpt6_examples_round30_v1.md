## 1. Fidelity check

**DCLXXXVI is mathematically consistent with the supplied statements.**

- The kernel coefficient `3/4` is correct: it is the quadratic coefficient in \(2(1+x)^{-1/2}\).
- Below \(\delta=\sqrt\varepsilon\),
  \[
  \int_0^\delta(u^3+\varepsilon u/2)\,du=\varepsilon^2/2.
  \]
- Above \(\delta\),
  \[
  \frac38\varepsilon^2\int_\delta^1\frac{du}{u}
  =\frac3{16}\varepsilon^2\log(1/\varepsilon).
  \]
- The outer constant is \((3/4)\int_1^\infty u^{-5}du=3/16\). The elementary \(\varepsilon^2/4\) bound is valid.
- The linear-coefficient identity is correct, using \(\int_1^\infty u^{-3}du=1/2\).
- For by-parts, \(v=-1/(2u^2)\) and \(a=e^{-u^4/2}\) give
  \[
  -v(1-a)'=u a.
  \]
  The product \(-(1-a)/(2u^2)\) tends to zero at both endpoints: \(O(u^2)\) at zero and \(O(u^{-2})\) at infinity.

Small numerical correction: \(-0.203\) is **below** \(-3/16=-0.1875\), not above. This does not affect the coefficient prediction.

## 2. Second half: two explicit remainder theorems

Write
\[
a(u)=e^{-u^4/2},\quad a_\varepsilon(u)=a(u)e^{-\varepsilon u^2/2},
\quad A=\frac12\sqrt{\pi/2},\quad \ell=\log(1/\varepsilon).
\]
All bounds below hold for \(0<\varepsilon\le1\).

### A. Moving amplitude: existing kernel lemma suffices

Recommended public statement:
\[
\boxed{\left|J_{a_\varepsilon}(\varepsilon)-J_a(\varepsilon)
       +A\varepsilon-\frac14\varepsilon^2\ell\right|
       \le2\varepsilon^2.}
\]

Introduce the genuinely integrable auxiliary integral
\[
I(\varepsilon)=\int_0^\infty\frac{u^2a(u)}{\sqrt{u^2+\varepsilon}}\,du.
\]

**First isolate the exponential Taylor remainder.** For \(x\ge0\),
\[
0\le e^{-x}-1+x\le x^2/2.
\]
Consequently,
\[
0\le J_{a_\varepsilon}-J_a+\varepsilon I(\varepsilon)
\le\frac{\varepsilon^2}{4}\int_0^\infty u^3a(u)\,du
=\frac{\varepsilon^2}{8}.
\]
The new moment is particularly easy:
\[
\int_0^\infty u^3e^{-u^4/2}\,du=\frac12.
\]

**Then prove**
\[
\boxed{\left|I(\varepsilon)-A+\frac{\varepsilon}{4}\ell\right|
       \le\varepsilon.}
\]

Use the three intervals \((0,\delta],(\delta,1],(1,\infty)\), where \(\delta=\sqrt\varepsilon\).

| Interval | Subtraction and bound |
|---|---|
| \((0,\delta]\) | \(\left|u^2a(1/\sqrt{u^2+\varepsilon}-1/u)\right|\le u\); integral \(\le\varepsilon/2\). |
| \((\delta,1]\) | Add \(\varepsilon/(2u)\). The resulting absolute value is at most \(\frac38\varepsilon^2u^{-3}+\frac14\varepsilon u^3\); integral \(\le\varepsilon/4\). |
| \((1,\infty)\) | Bound by \(\varepsilon a/(2u)\); integral \(\le\varepsilon/4\), since \(a/u\le u^3a\). |

The exact extracted integral is
\[
-\frac{\varepsilon}{2}\int_\delta^1\frac{du}{u}
=-\frac{\varepsilon}{4}\ell.
\]

Thus the moving theorem actually admits constant \(9/8\); **publish `2` unless sharper bookkeeping is useful**.

Lean-facing intermediate targets:
```lean
integral_cube_mul_exp_neg_quartic
movingJ_taylor_remainder
movingMoment_log_remainder
movingJ_sub_frozen
```
Crucially, never introduce \(\int_0^\infty a(u)/u\,du\) as a separate term.

### B. Frozen refinement: one new algebraic kernel lemma

Recommended statement:
\[
\boxed{\left|J_a(\varepsilon)
 -\left(\log(4/\varepsilon)+R_\infty+A\varepsilon\right)
 +\frac3{16}\varepsilon^2\ell\right|\le2\varepsilon^2.}
\]

Let
\[
r=\frac2{\sqrt{u^2+\varepsilon}}-\frac2u+\frac{\varepsilon}{u^3}.
\]
The required extension is
\[
\boxed{0\le\frac34\frac{\varepsilon^2}{u^5}-r
       \le\frac58\frac{\varepsilon^3}{u^7}.}
\]

**No analytic Taylor machinery is necessary.** Put \(s=\sqrt{u^2+\varepsilon}\). The gap equals
\[
\frac{(s-u)^3(3s^2+9su+8u^2)}{4su^5}.
\]
For its upper bound, the remaining polynomial inequality factors as
\[
5s(s+u)^3-2u^2(3s^2+9su+8u^2)
=(s-u)(5s^3+20s^2u+29su^2+16u^3)\ge0.
\]
This fits DCLXXXVI’s `field_simp`/`ring`/positivity architecture.

Also prove the global amplitude estimate
\[
0\le a-1+u^4/2\le u^8/8.
\]

On \((\delta,1]\), subtract the singular model **pointwise**:
\[
\left|(a-1)r+\frac38\frac{\varepsilon^2}{u}\right|
\le \frac3{32}\varepsilon^2u^3
   +\frac5{16}\varepsilon^3u^{-3}.
\]
Its integral is at most
\[
\left(\frac3{128}+\frac5{32}\right)\varepsilon^2
=\frac{23}{128}\varepsilon^2.
\]
Meanwhile,
\[
-\frac38\varepsilon^2\int_\delta^1\frac{du}{u}
=-\frac3{16}\varepsilon^2\ell.
\]

Reuse the existing bounds elsewhere:

- inner \((0,\delta]\): \(\varepsilon^2/2\);
- outer \((1,\infty)\): \(3\varepsilon^2/16\);
- elementary remainder: \(\varepsilon^2/4\).

Total: \(143\varepsilon^2/128<2\varepsilon^2\).

**Cutoffs:** exactly \(\sqrt\varepsilon\) and \(1\), with no new scale.

### C. Size and execution order

- **Moving amplitude:** one focused unit; existing kernel estimate plus one quartic moment and the three-way split.
- **Frozen logarithmic refinement:** one substantial unit; algebraic third-order gap plus a refinement of the existing inner-integral proof.
- **Evidence wrapper:** small follow-up, or append to the second unit if the real-power conversion infrastructure is ready.

I would execute **moving first**, then frozen. Neither requires an all-orders asymptotic framework.

## 3. Final evidence theorem

Adding the two public bounds gives
\[
\left|J_{a_\varepsilon}(\varepsilon)
-\log(4/\varepsilon)-R_\infty
-\frac1{16}\varepsilon^2\log(1/\varepsilon)\right|
\le4\varepsilon^2.
\]

Hence, for real \(N\ge1\),
\[
\boxed{
\left|Z_N-
\sqrt{\frac\pi2}\frac{\log N+5\log2-\gamma}{\sqrt N}
-\frac{\sqrt{2\pi}}{32}\frac{\log N}{N\sqrt N}
\right|
\le\frac{4\sqrt{2\pi}}{N\sqrt N}.
}
\]

**Lean recommendation:** state the denominator as `N * Real.sqrt N`, rather than `N ^ (3 / 2 : ℝ)`. First prove the wrapper for `N = m ^ 4`, `1 ≤ m`; obtain the general theorem via \(m=\sqrt{\sqrt N}\).

### The moving renormalization constant

It is worth recording the cheap companion:
\[
\boxed{
0\le R_{a_\varepsilon}-R_\infty+A\varepsilon
\le\varepsilon^2/8.
}
\]
Indeed,
\[
R_{a_\varepsilon}-R_\infty
=2\int_0^\infty\frac{a_\varepsilon-a}{u}\,du.
\]

Thus its linear coefficient is **negative**, namely \(-A\).

One correction to the proposed interpretation: this linear term contributes at order \(N^{-1}\) in the evidence and participates in the cancellation. It is the **quadratic** renormalization term that contributes to the \(N^{-3/2}\) constant. In fact its coefficient is \(1/8\), but identifying that limit is unnecessary for the requested logarithmic theorem. Do not add a separate renormalization correction after proving the direct moving-\(J\) theorem—it is already included.

## 4. Ranking and convention checklist

**Ranking:** finish the blow-up second half; then cone general-prior corner; then localised exact-phase replacement.

The blow-up work now has explicit constants, fixed cutoffs, and direct reuse of DCLXXXVI. The cone theorem is attractive but likely needs more fresh prior-localization and density regularity infrastructure. The exact-phase inequality is elementary once formulated, but choosing and controlling the uniform localization away from \(V=0\) is the substantive task.

Keep these identities explicit in wrapper lemmas:
\[
\varepsilon=m^{-2}=N^{-1/2},\qquad
\log(1/\varepsilon)=2\log m=\tfrac12\log N,
\]
\[
\log(4/\varepsilon)+R_\infty
=\tfrac12(\log N+5\log2-\gamma).
\]

The coefficient chain is
\[
-\frac3{16}+\frac14=\frac1{16},
\qquad
\frac1{16}\log(1/\varepsilon)=\frac1{32}\log N.
\]
And throughout, \(a_\varepsilon\le a\), so both \(J_{a_\varepsilon}-J_a\) and \(R_{a_\varepsilon}-R_\infty\) are nonpositive.