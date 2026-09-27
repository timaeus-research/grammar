## 1. Fidelity check

**All four targets match the supplied specifications.** This is a check of the statements and mathematics, not an independent build or inspection of `examples_slop.tex`.

- **DCXXVIII:** the quartic-defect interface is the right reusable abstraction. With \(B=\tfrac12\), `ampJ_two_term_quartic` gives \(4.5\varepsilon\), rounded to \(5\varepsilon\). Adding the whole-integral comparison \(2/m^2\), and using
  \[
  \varepsilon=m^{-(2k-2)}\le m^{-2}\qquad(k\ge2,\ m\ge1),
  \]
  gives **7**. Crucially, no logarithm is reintroduced through separate renormalised constants.

- **DCXXIX–DCXXX:** the direct denominator estimate is entirely sufficient—and simpler than proving tilt monotonicity. Completing the square and applying
  \[
  |t|\le |a|+|t-a|
  \]
  gives exactly the stated lower bound, uniformly for \(0\le\delta\le1\).

  Yes:
  \[
  \int \frac{\texttt{coneNumSq}\ N\ a}{\texttt{coneDen}\ N\ a}\,\gamma(a)\,da
  \]
  is the note’s \(E_\xi[E[u_1^2\mid\xi]]\), **provided \(a\) is its standard-normal scalar field coordinate**. The two `_eq` theorems identify the ratio with the four-dimensional posterior. No ratio-of-averages substitution occurs.

  I would add a small exported wrapper restating `cone_averaged_correction` directly with the two four-dimensional integrals. This is presentation closure, not new analysis.

- **DCXXXI:** the \(1/v\) in the subtraction is essential:
  \[
  Z_2(v^2)\sim\frac{2\log v+c}{sv},\qquad
  c=3\log2-\gamma,\quad s=\sqrt{2\pi}.
  \]
  The residual constant is correct:
  \[
  D_3=\frac{cR_0+2J}{\pi}+\frac2sQ,\qquad
  R_0=\frac{\log2-\gamma}{2}.
  \]
  Substituting the proposed exact values gives
  \[
  D_3
  =\frac{(c+2R_0)^2+\pi^2}{4\pi}
  =\frac{(4\log2-2\gamma)^2+\pi^2}{4\pi}.
  \]
  Thus the integral-defined theorem and the Mellin value agree, including every factor of two.

## 2. Recommended next three targets

My ranking is:

| Rank | Target | Assessment |
|---|---|---|
| 1 | Blow-up observable numerators \(X_N,Y_N\) | Two concrete note claims; elementary DCT; genuinely day-sized |
| 2 | Cone averaged \(O(N^{-1})\) remainder | Reuses the new denominator bound almost verbatim; genuinely day-sized |
| 3 | Three-term propagation, retaining `gaussJlog` | High leverage at all depths; day-sized if it follows the existing `TwoTermData` proof |

The exact \(J\) evaluation is the best substitute for target 3 if a convenient Gamma duplication identity is found immediately.

### Target 1: blow-up observable numerators

Here the model is the quartic \(k=2\) model, with the **raw** Gaussian weight. Write \(s=\sqrt{2\pi}\). Integrating out \(y\) gives
\[
X_N=s\int_{\mathbb R}
 \frac{x^2e^{-Nx^4/2-x^2/2}}{\sqrt{1+Nx^2}}\,dx,
\]
\[
Y_N=s\int_{\mathbb R}
 \frac{e^{-Nx^4/2-x^2/2}}{(1+Nx^2)^{3/2}}\,dx.
\]

The useful scaled identities are
\[
NX_N=s\int_{\mathbb R}
 \frac{u^2e^{-u^4/2-u^2/(2\sqrt N)}}
      {\sqrt{u^2+N^{-1/2}}}\,du,
\]
and
\[
\sqrt N\,Y_N=s\int_{\mathbb R}
 \frac{e^{-(t^4+t^2)/(2N)}}{(1+t^2)^{3/2}}\,dt.
\]

For DCT:

- first integrand is bounded by \(|u|e^{-u^4/2}\);
- second is bounded by \((1+t^2)^{-3/2}\);
- their limiting integrals are \(\sqrt{\pi/2}\) and \(2\), respectively.

For the second integral, use the primitive \(t/\sqrt{1+t^2}\).

Suggested interfaces, with names illustrative:

```lean
theorem blowupX_eq_oneDim {N : ℝ} (hN : 0 < N) : ...
theorem blowupY_eq_oneDim {N : ℝ} (hN : 0 < N) : ...

theorem tendsto_mul_blowupX :
    Tendsto (fun N : ℝ => N * blowupX N) atTop (𝓝 Real.pi)

theorem tendsto_sqrt_mul_blowupY :
    Tendsto (fun N : ℝ => Real.sqrt N * blowupY N) atTop
      (𝓝 (2 * Real.sqrt (2 * Real.pi)))
```

Prove the scaled identities separately from the limits. Avoid differentiating the partition-function expansion: its remainder does not automatically differentiate.

### Target 2: cone averaged \(O(N^{-1})\)

Let \(F_\delta(a)=\texttt{coneScaledCorrection}\ \delta\ a\). The elementary inequality
\[
0\le1-e^{-\delta|t|}\le\delta|t|
\]
already yields the required quantitative continuity.

Put \(b=2/s\). Gaussian moment bounds give
\[
F_0(a)\le |a|+b,\qquad
E_{0,a}|t|\le |a|+b,\qquad
E_{0,a}t^2=a^2+1.
\]
Using the existing denominator lower bound,
\[
|F_\delta(a)-F_0(a)|
\le \delta\,B(a),\qquad 0\le\delta\le1,
\]
where one convenient envelope is
\[
B(a)=\frac{s}{c_0}e^{|a|}
 \left[a^2+1+(|a|+2/s)^2\right].
\]
Its product with `gaussDensity` is integrable by the same Gaussian-tail argument already used.

Suggested interfaces:

```lean
noncomputable def coneCorrectionLipEnvelope (a : ℝ) : ℝ := ...

theorem coneScaledCorrection_sub_zero_le
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    |coneScaledCorrection δ a - coneScaledCorrection 0 a| ≤
      δ * coneCorrectionLipEnvelope a

theorem integrable_coneCorrectionLipEnvelope :
    Integrable (fun a =>
      coneCorrectionLipEnvelope a * gaussDensity a)

theorem cone_averaged_remainder :
    (fun N : ℝ =>
      (∫ a, coneNumSq N a / coneDen N a * gaussDensity a) -
        1 / 2 - 1 / (Real.sqrt Real.pi * Real.sqrt N))
      =O[atTop] (fun N => 1 / N)
```

An explicit bound for \(N\ge1\), with constant
\[
C=\int B(a)\gamma(a)\,da,
\]
is just as accessible.

**Do not make the exact second coefficient part of this day’s target.** At fixed \(a\),
\[
F'_0(a)=-\operatorname{Cov}_{N(a,1)}(t_+,|t|).
\]
Consequently, the expected averaged expansion is
\[
E_a[\text{posterior ratio}]
=\frac12+\frac1{\sqrt{\pi N}}
-\left(\frac56-\frac{\sqrt3}{\pi}\right)\frac1N+o(N^{-1}).
\]
Evaluating that coefficient introduces a correlated absolute-Gaussian moment; the \(O(N^{-1})\) result does not need it.

### Target 3: three-term propagation with integral-defined \(J\)

Your recurrence is correct. In the convention
\[
\sqrt N\,Z_L(N)
=A_L\ell^{L-1}+B_L\ell^{L-2}+C_L\ell^{L-3}
+o(\ell^{L-3}),
\]
it is
\[
\begin{aligned}
A_{L+1}&=\frac{A_L}{sL},\\
B_{L+1}&=\frac{B_L/(L-1)+2A_LR_0}{s},\\
C_{L+1}&=\frac{C_L/(L-2)+2B_LR_0+4(L-1)A_LJ}{s}.
\end{aligned}
\]

A Lean-facing asymptotic predicate could expose:

```lean
-- Schematic: include the engine's existing measurability/local bounds.
def HasThreeTerm (F : ℝ → ℝ) (L : ℕ) (A B C : ℝ) : Prop :=
  (fun N =>
    Real.sqrt N * F N -
      (A * (Real.log N) ^ (L - 1) +
       B * (Real.log N) ^ (L - 2) +
       C * (Real.log N) ^ (L - 3)))
    =o[atTop] (fun N => (Real.log N) ^ (L - 3))
```

Then export a propagation theorem for \(L\ge3\), using real-valued denominator casts explicitly.

The seed is already available:
\[
A_3=\frac1{4\pi},\qquad
B_3=\frac{2\log2-\gamma}{\pi},\qquad
C_3=\texttt{depthThreeConst}.
\]

**Proof route:** repeat the existing cutoff decomposition. The constant part of the Gaussian integrates the polynomial exactly; the first two renormalised moments contribute \(R_0,J\). Integrate the input little-\(o\) remainder using an epsilon/tail split, not DCT alone. Bounded-scale contributions are \(O(1)\), hence negligible against the output’s \(\ell^{L-2}\).

The hidden effort is integrability of the required absolute log moments of `gaussH`. Check that infrastructure before committing to the one-day estimate.

## 3. Exact \(J\), exact \(Q\), and the other candidates

### Exact \(J\): Gamma data at \(1\), not just at \(1/2\)

With the existing cutoff convention,
\[
H(z)=\int_0^\infty h(x)x^{z-1}\,dx
=\frac{2^{z/2}\Gamma(1+z/2)-1}{z}.
\]
If \(f(z)=2^{z/2}\Gamma(1+z/2)\), then
\[
R_0=f'(0),\qquad J=\frac12f''(0).
\]
Thus the needed identity is
\[
\Gamma''(1)=\gamma^2+\frac{\pi^2}{6}.
\]

The clean routes are:

1. **Duplication, if readily available.** Twice logarithmically differentiating at \(1/2\) gives
   \[
   \psi'(1/2)+\psi'(1)=4\psi'(1),
   \]
   hence \(\psi'(1)=\pi^2/6\). I cannot certify the theorem name on this pin; grep `Gamma_mul_Gamma_add_half` and nearby duplication results.

2. **Regularised reflection, without duplication:**
   \[
   \Gamma(1+z)\Gamma(1-z)=\frac{\pi z}{\sin(\pi z)}.
   \]
   Extend the right side at zero. Its quadratic coefficient is \(\pi^2/6\), so
   \[
   2\Gamma''(1)-2\Gamma'(1)^2=\pi^2/3.
   \]
   This needs a removable-singularity/Taylor lemma for the sine quotient, not raw reflection “at \(1\)”.

Then prove differentiation under the renormalised integral, or directly a second-order expansion of \(f\), obtaining:

```lean
theorem gaussJlog_eq :
    gaussJlog =
      ((Real.log 2 - Real.eulerMascheroniConstant) / 2) ^ 2 / 2 +
        Real.pi ^ 2 / 48
```

The proposed Gaussian \(\log^2x\,dx\) integral uses Gamma data at \(1/2\), but it is **not the same moment** as the renormalised \(\log x\,dx/x\) integral. It does not by itself avoid the missing identity at \(1\).

### Exact \(Q\): not fundamentally a new two-dimensional identity

For \(0<z<1\),
\[
\int_0^\infty v^{z-1}Z_2(v^2)\,dv
=\frac{2^{-z/2-1}}{\pi}
 \Gamma(z/2)\Gamma((1-z)/2)^2.
\]
Put \(w=1-z\). Its expansion is
\[
\frac{2}{sw^2}+\frac{c}{sw}
+\frac{c^2+5\pi^2/6}{4s}+O(w).
\]

Subtracting the Mellin transform of the cutoff tail leaves
\[
\int_0^\infty v^{-w}q(v)\,dv\longrightarrow Q.
\]
The existing inner boundedness and outer \(v^{-2}\) bound justify this limit.

So \(Q\) reduces to **Beta/Gamma Mellin factorisation plus the same second-order Gamma data**, not an irreducible 2D calculation. Nevertheless, factorisation, pole subtraction, and expansion together are probably more than a day unless the Beta integral is already packaged.

### Naive Bayes face certification

The supplied APIs now make an **abstract face certificate** straightforward, but still do not specify the actual \(M_\pm(\lambda)\), coordinate measure, or fibre-family formulas.

For a one-face patch \(d\in(0,1]\), assume
\[
d\nu\le C_\nu d^{a-1}\,dd,\quad
M(d)\ge\kappa d^\beta,\quad M(d)\le1,\quad
W(d)\le C_Wd^{-\eta},
\]
with \(0<\kappa\le1\), \(\beta,\eta\ge0\). Then
\[
W(1+M^{-2r})(1+|\log M|^4)
\le C\,d^{-\eta-2r\beta}(1+|\log d|^4).
\]
Hence the existing envelope is integrable when
\[
a-\eta-2r\beta>0.
\]

This discharges `hB` through `integrable_logSqDomBound_of_envelope`; one must still discharge `hint0` and `hmeas` for the basepoint adapter.

**Important ambiguity:** neither face parameters `a`, `b` nor actual \(M_\pm\) are defined in the supplied signatures. If “\(a=0,b=2\)” means \(a=0,\beta=2\) in the face-power convention above, the condition becomes \(\eta+4r<0\), which is impossible for nonnegative \(\eta\). It cannot certify that patch. If these are model coordinates instead, their formulas are needed. The `b` argument of `logSqDomBound` is an odd-amplitude coefficient, not automatically a cutoff exponent.

The generic power/log integrability certificate is day-sized; the actual model closure is not yet specified.

### Rank-one Morse–Bott passage

A reduced theorem is plausible **given** a tubular-coordinate integral, Jacobian convergence, a uniform Gaussian majorant in scaled normal coordinates, and a negligible off-tube contribution. The existing normal integral then evaluates the limit.

Constructing those hypotheses for the actual model is the substantive Morse–Bott passage. I would not classify that full passage as a day-sized consequence of the normal-integral theorem.

## 4. Convention hazards to record

1. **`coneTilt δ a` takes \(\delta=N^{-1/2}\), not \(N\).** This comes from \(t=\sqrt N\,v\). Its tilt is \(at\), with no remaining \(\sqrt N\).

2. **Use \(N>0\) for substitutions; \(N\ge1\) for uniform envelopes.** Lean’s totalised division and square root do not encode the intended scaling at nonpositive \(N\).

3. **`depthThreeQ` subtracts only on `Ioi 1`.** The endpoint is measure-zero, but pointwise identities must preserve the stated membership condition. Never drop the \(1/v\).

4. **`gaussJlog` is the full renormalised moment.** \(J_a\) is its cutoff approximation. Keep the definition and sign of `gaussH` explicit when proving the Gamma formula.

5. **Cone evidence uses a raw Gaussian on \(\mathbb R^4\); the field average uses a normalised Gaussian on \(\mathbb R\).** Normalising the four-dimensional prior multiplies numerator and denominator by the same \((2\pi)^{-2}\), so the posterior ratio is unchanged. It does change separate evidence identities.

6. **Average of ratios remains the invariant interface.** In particular, the fact that averaging the likelihood over \(a\) returns the prior mass does not evaluate the averaged posterior.