## 1. Fidelity check

**DCXLIX–DCLI match the stated round-15 targets**, based on the supplied signatures. This is a mathematical/interface check, not an independent checkout of `c2cc041`.

### (a) Mellin transfer

The cutoff, sign and indexing are correct:
\[
\int_1^\infty v^{z-2}(\log v)^k\,dv
=\int_0^\infty e^{-(1-z)t}t^k\,dt
=\frac{k!}{(1-z)^{k+1}},\qquad z<1.
\]
Thus the principal part is **subtracted**, with positive coefficients in powers of \(1-z\). If rewritten using \(z-1\), alternating signs appear.

`Fin (d + 1)` correctly covers degrees \(0,\ldots,d\). The value at \(v=1\) is immaterial to integration, but the strict cutoff is consistent throughout.

One wording boundary: DCXLIX proves a **real one-sided finite-part limit**. By itself it does not prove complex meromorphic continuation.

### (b) Gaussian second log moment

The half-line factor is \(1/(4\sqrt2)\); doubling gives
\[
m_2=\frac1{2\sqrt2}
 \left[(\log2)^2\Gamma(\tfrac12)
 +2\log2\,\Gamma'(\tfrac12)+\Gamma''(\tfrac12)\right].
\]
Since \(1/(2\sqrt2)=\sqrt2/4\), the bookkeeping is correct. Substituting
\[
\psi(\tfrac12)=-\gamma-2\log2,\qquad
\psi'(\tfrac12)=\frac{\pi^2}{2}
\]
gives exactly
\[
m_2=\sqrt{2\pi}\left[\frac{(\gamma+\log2)^2}{4}+\frac{\pi^2}{8}\right].
\]

### (c) Independent derivation of \(D_4\)

Write \(s=\sqrt{2\pi}\), \(\ell=\log N\), \(a=N^{-1/2}\), and
\[
P_3(u)=A_3u^2+B_3u+C_3.
\]
The recursion and residual split give
\[
\sqrt N Z_4(N)
=2\int_0^\infty\gamma(v/\sqrt N)q_3(v)\,dv
+\frac2s\left[
 \int_a^1\frac{P_3(\ell+2\log x)}x\,dx
 +\int_a^\infty\frac{h(x)P_3(\ell+2\log x)}x\,dx
\right].
\]

For the flat part, put \(u=\ell+2\log x\). The endpoints become \(0,\ell\), hence
\[
\int_a^1\frac{P_3(\ell+2\log x)}x\,dx
=\frac12\int_0^\ell P_3(u)\,du
=\frac{A_3\ell^3}{6}+\frac{B_3\ell^2}{4}+\frac{C_3\ell}{2}.
\]

The shifted polynomial is
\[
P_3(\ell+2y)=c_0+c_1y+c_2y^2,
\]
with exactly
\[
c_0=A_3\ell^2+B_3\ell+C_3,\quad
c_1=4A_3\ell+2B_3,\quad c_2=4A_3.
\]

Replacing the cutoff moments by their full moments therefore gives
\[
\begin{aligned}
A_4&=\frac{A_3}{3s},\\
B_4&=\frac{B_3}{2s}+\frac{2A_3R_0}{s},\\
C_4&=\frac{C_3}{s}+\frac{2B_3R_0+8A_3J}{s},\\
D_4&=\frac2s\left[Q_3+C_3R_0+2B_3J+4A_3J_2\right].
\end{aligned}
\]
Thus **`depthFourConst` is the correct constant**. The coefficient matching in the exact remainder identity is also the right consistency check.

The supplied cutoff bound is sufficient: all discarded terms are bounded by constants times
\[
a\ell^2,\quad a\ell,\quad a,
\]
which vanish. No sharper cutoff estimate is required for DCLI.

### (d) Mellin-jet prediction

With the normalization consistent with \(A_3=1/(4\pi)\), the prediction is
\[
D_4^{\rm jet}
=\frac1{2^{3/2}\pi^2}
 [\varepsilon^3]\,
 \Gamma(\tfrac12-\varepsilon)\,2^{3\varepsilon}
 \Gamma(1+\varepsilon)^4.
\]
Set \(b=5\log2-3\gamma\). Then
\[
\log\frac{\Gamma(\tfrac12-\varepsilon)2^{3\varepsilon}
                 \Gamma(1+\varepsilon)^4}{\sqrt\pi}
=b\varepsilon+\frac{7\pi^2}{12}\varepsilon^2
+\zeta(3)\varepsilon^3+O(\varepsilon^4).
\]
Consequently
\[
\boxed{
D_4^{\rm jet}
=\frac{b^3/6+(7\pi^2/12)b+\zeta(3)}
       {(2\pi)^{3/2}}
}
\]
and numerically
\[
\boxed{D_4^{\rm jet}\approx0.7654005.}
\]
This agrees with `0.76540`.

The relevant third derivative at the half-integer is
\[
\Gamma'''(\tfrac12)
=\sqrt\pi\left[
-(\gamma+2\log2)^3
-\frac{3\pi^2}{2}(\gamma+2\log2)-14\zeta(3)
\right].
\]
**The numerical agreement does not yet identify the integral-defined Lean constant with this closed form.**

## 2. Next targets

My ranking is:

| Rank | Target | Assessment |
|---|---|---|
| 1 | Depth-four quantitative remainder | Best mathematical payoff; a conservative rate is day-sized |
| 2 | Naive-Bayes joint measurability from the fixed-domain representation | Day-sized **if joint measurability of the kernel is already available** |
| 3 | A.e.-measurable Mellin-transfer interface | Low-risk, reusable, genuinely day-sized |

### 1. Depth-four rate

The safe immediate target is
\[
\sqrt N Z_4-P_4(\log N)
=O\!\left(\frac{(1+\log N)^2}{\sqrt N}\right).
\]

A Lean-facing statement requiring no new asymptotic notation is:

```lean
theorem gaussLaplaceL_four_constant_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
      |Real.sqrt N * gaussLaplaceL 4 N
        - gaussCoeffA 0 * (Real.log N)^3
        - gaussCoeffB 0 * (Real.log N)^2
        - thirdCoeff 0 * Real.log N
        - depthFourConst|
      ≤ K * (1 + Real.log N)^2 / Real.sqrt N
```

**Route:** retain `sqrt_mul_gaussLaplaceL_four_sub_eq`, and replace the DCT conclusion by a quantitative split at \(R=\sqrt N\).

On \(v\le R\), use
\[
|\gamma(v/R)-\gamma(0)|\le\frac{v^2}{2sN};
\]
on \(v>R\), use \(1/s\). The outer residual bound yields
\[
\frac1N\int_1^R(1+2\log v)\,dv
+\int_R^\infty\frac{1+2\log v}{v^2}\,dv
=O\!\left(\frac{1+\log N}{\sqrt N}\right).
\]
The inner interval contributes \(O(N^{-1})\), using \(Z_3(v^2)\le1\). The existing cutoff estimates contribute \(O((1+\ell)^2/\sqrt N)\).

**A stronger bound is also available:**
\[
O\!\left(\frac{1+\log N}{\sqrt N}\right).
\]
For this, combine the three cutoff errors **before** estimating them:
\[
-\frac2s\int_0^a \frac{h(x)}xP_3(\ell+2\log x)\,dx.
\]
Using \(|h(x)|\le x^2/2\) and \(x=ay\), its absolute value is at most
\[
\frac{a^2}{s}\int_0^1y\,|P_3(2\log y)|\,dy=O(N^{-1}).
\]
So the squared-log rate is honest but not the strongest consequence of the available bounds. I would ship it first, with the combined-cutoff lemma as the natural strengthening.

### 2. Naive-Bayes joint measurability

The useful abstraction is measurability of a parameterized fixed-domain integral—not a bespoke fibre theorem.

For the actual parameter space `Λ`, a representative interface is:

```lean
-- Ambient namespace: Grammar; usual Borel assumptions on Λ.
theorem measurable_nb_fixedDomainIntegral
    {h : Λ → ℝ → ℝ → ℝ}
    (hh : Measurable
      (fun p : (Λ × ℝ) × ℝ =>
        h p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2))))) :
    Measurable
      (fun p : Λ × ℝ =>
        ∫ t in Set.Ioo (0 : ℝ) 1,
          (t * (1 - t))⁻¹ *
            h p.1 t (p.2 / (t * (1 - t))))
```

Use measurable arithmetic and Mathlib’s measurable parameter-integral theorem over the fixed restricted measure.

Two boundaries:

* A separately measurable family \(h_t\) is **not** enough; prove joint measurability of the displayed composed kernel.
* Measurability of the totalized Bochner integral does not establish that it is the intended finite density. Carry fibre integrability separately when transferring `eq:nb_rho_integral`.

No KL-versus-surrogate remainder should be bundled into this target.

### 3. A.e.-measurable Mellin transfer

Prefer measurability on the relevant restricted measure:

```lean
theorem tendsto_mellin_sub_logPolynomial_ae
    {d : ℕ} (p : Fin (d + 1) → ℝ)
    {q : ℝ → ℝ} {a : ℝ}
    (ha : a < 1)
    (hq : AEStronglyMeasurable q
      (volume.restrict (Set.Ioi (0 : ℝ))))
    (hsmall : IntegrableOn
      (fun v => v ^ (a - 1) * q v) (Set.Ioc 0 1))
    (hlarge : IntegrableOn q (Set.Ioi 1)) :
    Tendsto
      (fun z : ℝ =>
        (∫ v in Set.Ioi (0 : ℝ),
          v ^ (z - 1) * (q v + mellinLogTail p v)) -
        ∑ k : Fin (d + 1),
          p k * ((k : ℕ).factorial : ℝ) /
            (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ v in Set.Ioi (0 : ℝ), q v))
```

**Route:** choose a measurable representative on `volume.restrict (Ioi 0)`, transfer the two integrability hypotheses by a.e. equality, apply DCXLIX, and transport all integrals back. Preserve the existing measurable version as a convenience wrapper.

### Other candidates

**All-depth recursion:** valuable, but not yet an honest single-day target. Also, a fixed `FourTermData` cannot encode every depth’s **constant**: at depth five the constant is already the fifth coefficient.

The correct eventual abstraction is a full polynomial \(P_L\), together with a quantitative residual certificate. With
\[
H_j=\int_0^\infty h(x)\frac{\log^j x}{x}\,dx,
\]
the polynomial step is
\[
P_{L+1}(\ell)
=\frac1s\int_0^\ell P_L(u)\,du
+\frac2s\sum_{j=0}^{\deg P_L}
 \frac{2^j}{j!}P_L^{(j)}(\ell)H_j
+\frac2sQ_L.
\]
A four-term engine is appropriate for the **top four coefficients**, not all-depth constant terms. First extract the quantitative residual convolution lemma from the depth-four rate proof.

**Exact \(J_2\):** the kernel identity and factor \(1/3\) are correct. If
\[
K_j=\int_0^\infty
 (e^{-u}-1_{(0,1]}(u))\frac{\log^j u}{u}\,du,
\]
then \(K_j=\Gamma^{(j+1)}(1)/(j+1)\). After \(u=x^2/2\), including the cutoff shift,
\[
J_2=\frac18\left[
(\log2)^2\Gamma'(1)+\log2\,\Gamma''(1)
+\frac{\Gamma'''(1)}3+\frac{(\log2)^3}3
\right].
\]
Hence analytically
\[
\boxed{
J_2=\frac{(\log2-\gamma)^3+
 \frac{\pi^2}{2}(\log2-\gamma)-2\zeta(3)}{24}.
}
\]
The kernel reduction is plausibly day-sized. The special-value theorem is not something I would promise without checking the pinned Mathlib: analyticity of `Complex.Gamma` alone does not supply \(\psi''(1)=-2\zeta(3)\). Keep the integral definition public.

**Cone \(c_3\):** day-sized only if the required twice-differentiable scalar representation and integral differentiation bounds already exist. The factor \(1/2\) belongs to the quadratic Taylor coefficient of the chosen desingularized function; it cannot safely be attached to an unspecified existing `c₂` function.

**Polish:** the `thirdCoeffClosed` corollary is an excellent tiny task: copy the existing asymptotic theorem’s statement, replace the target coefficient, and `simpa only [the coefficient equality]`. Cube-set and a.e.-domination adapters are also day-sized when they require only restriction/transport, not new boundary estimates.

## 3. Convention hazards

* **`depthThreeJet`:** document that this means the entire polynomial for depth three. Its constant is \(C_3\); `thirdCoeffClosed` means the *third asymptotic coefficient at arbitrary depth*. Those coincide only at depth three.

* **`gaussJlog2`:** good parallel naming. State explicitly that this is a second log moment, **not** `(gaussJlog)^2`, and that its \(\zeta(3)\) evaluation is not yet formalized.

* **`depthFourQ`:** indexed by its consuming recursion, while the function being residualized is \(Z_3\). Keep the existing name, but add a source-depth alias such as `depthThreeJetResidual`; use \(q_3\) in mathematical documentation.

* **`depthFourTail` versus `mellinLogTail`:** add a bridge
  \[
  \texttt{depthFourTail}
  =\texttt{mellinLogTail}\,[C_3,\,2B_3,\,4A_3].
  \]
  The factors \(2,4\) are essential because the jet is evaluated at \(2\log v\). This avoids duplicated indicator algebra and makes DCXLIX directly reusable.

* **`if` versus `indicator`:** no mathematical discrepancy. Supply one canonical equality lemma and standard zero/outer-value lemmas; avoid repeatedly unfolding both representations.

**Bottom line:** round 15 is faithful, and the Mellin jet predicts \(D_4\approx0.7654005\). The strongest next move is a quantitative depth-four remainder, followed by fixed-domain measurability and the a.e. Mellin interface—not an immediate all-depth constant engine.