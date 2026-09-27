**DCLXXI is mathematically faithful on the supplied statements.** Route B gives the desired identification without needing either duplication or a ζ(3) theorem. I have not inspected the pinned repository/Mathlib, so API availability below is distinguished from proposed interfaces.

## 1. Fidelity

### (a) Leibniz coefficients: correct

Here \(A(0)=C(0)=1\). Writing \(D=C^3\),
\[
D'(0)=3c_1,\quad
D''(0)=6c_1^2+3c_2,\quad
D'''(0)=6c_1^3+18c_1c_2+3c_3.
\]
Substitution into
\[
(ABD)'''=A'''BD+3A''(B'D+BD')
 +3A'(B''D+2B'D'+BD'')
 +A(B'''D+3B''D'+3B'D''+BD''')
\]
gives exactly your 14 terms.

The \(c_j=C^{(j)}(0)\) in this calculation are **derivative values**, not the jet coefficients also denoted \(c_j\).

### (b) Cubic expression and real-part extraction: correct

Substitute
\[
b_0=\sqrt\pi,\quad b_1=\sqrt\pi\,p,\quad
b_2=\sqrt\pi(p^2+\pi^2/2),\quad b_3=-\Gamma'''(1/2),
\]
\[
C'(0)=-\gamma,\quad C''(0)=q,\quad C'''(0)=\Gamma'''(1).
\]
This reproduces every term of the `depthThreeJetCubic` docstring, including the signs of both third derivatives.

For real \(a,b\),
\[
(\uparrow a+\uparrow b\,\Gamma'''(1)-\Gamma'''(1/2)).\mathrm{re}
 =a+b\,\texttt{gammaThirdOne}-\texttt{gammaThirdHalf}.
\]
Thus your specially arranged \(a\) reduces to \(6\sqrt\pi\,c_3\). **No theorem asserting that the complex third derivatives are real is required.**

### (c) Pole matching: correct

For \(P_3(x)=A_3x^2+B_3x+C_3\), your pole convention gives
\[
\frac{A_3}{u^3}+\frac{B_3}{2u^2}+\frac{C_3}{2u}.
\]
Hence
\[
A_3=\frac1{4\pi},\qquad B_3=\frac{c_1}{2\pi},
\qquad C_3=\frac{c_2}{2\pi}.
\]

## 2. Ranked next targets

### 1. **(a) One-symbol reduction by duplication — strongest next-day target**

Set \(G_1=\texttt{gammaThirdOne}\), \(G_{1/2}=\texttt{gammaThirdHalf}\). The exact relation is
\[
\boxed{
G_{1/2}
=\sqrt\pi\left[
7G_1+7\gamma^3+\frac72\gamma\pi^2
-p^3-\frac32p\pi^2
\right],\qquad p=\gamma+2\log2.
}
\]

For the direct product-rule proof, with \(k=2\log2\), \(q=\gamma^2+\pi^2/6\), the unsimplified identity is
\[
G_{1/2}-3\sqrt\pi\,\gamma(p^2+\pi^2/2)
-3\sqrt\pi\,p q+\sqrt\pi\,G_1
=
\sqrt\pi[-k^3-6k^2\gamma-12kq+8G_1].
\]
This is particularly suitable for `ring` after substitution.

Proposed API:
```lean
noncomputable def gammaLogThirdOne : ℝ :=
  gammaThirdOne + Real.eulerMascheroniConstant ^ 3 +
    Real.eulerMascheroniConstant * Real.pi ^ 2 / 2

theorem gammaThirdHalf_eq_gammaThirdOne : ...
theorem depthThreeJetCubic_eq_logThird :
    depthThreeJetCubic =
      depthThreeJetLinear ^ 3 / 6 +
      depthThreeJetLinear * Real.pi ^ 2 / 2 -
      (2 / 3 : ℝ) * gammaLogThirdOne
```
Then obtain both residual-mass corollaries by rewriting.

**One-day assessment: credible**, given DCXXXVIII’s existing chain. Reuse its complex duplication setup, add the third-order `HasDerivAt` layer, identify derivatives locally on \(\Re z>0\), and take real parts only at the end. Avoid introducing a general polygamma API for this target.

### 2. **(c) Log-moment identification — valuable, but budget conditionally**

The desired bridge is
```lean
theorem gammaOneLogMoment_three :
    gammaOneLogMoment 3 = gammaThirdOne
```
assuming the moment uses the unnormalised weight \(e^{-u}(\log u)^3\).

I cannot certify an iterated Gamma-integral derivative theorem at this pin. Check the actual signatures/source of the named first-order theorem before estimating. **Analyticity alone does not identify derivatives with weighted integrals.**

A reusable proposed interface is
\[
F_m(s)=\int_0^\infty e^{-u}u^{s-1}(\log u)^m\,du,
\]
```lean
theorem hasDerivAt_gammaLogIntegral
    (m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (gammaLogIntegral m)
      (gammaLogIntegral (m + 1) s) s
```
For this milestone, restrict to a neighbourhood of \(1\) and \(m\le2\); a general theorem is optional. A common dominating envelope can use
\[
e^{-u}(1+|\log u|^4)
\begin{cases}
u^{-1/2},&0<u\le1,\\
u^{1/2},&u\ge1.
\end{cases}
\]
The work is integrability and uniform domination, not algebra.

**Estimate:** one day if the existing proof already exposes reusable log-weight bounds; otherwise several days. With (a), this genuinely closes \(D_4\) modulo the single symbol \(\lambda_3\).

### 3. **(d) General coefficient packaging — good bounded target, with a bridge caveat**

Define
\[
h_0=1,\qquad
h_n=\frac1n\sum_{j=1}^{n}j\,b_jh_{n-j}.
\]
Your ζ-formula
\[
b_n=\frac{2^n-1+L(-1)^n}{n}\zeta(n)
\]
is for **\(n\ge2\)**; supply \(b_1\) separately from the normalisation of \(H_L\). Do not instantiate it at ζ(1).

The clean conditional interface is:
```lean
-- Schematic: hypotheses assert the appropriate jet and Mellin normalisation.
theorem enginePoly_coeff_eq_of_jet
    ... (hk : k < L) :
    (enginePoly L).coeff k =
      2 * C L * h (L - 1 - k) / (k.factorial : ℝ)
```
Also package the finite part as \(Q_L=C_Lh_L\) when the order-\(L\) jet is available.

**Important:** finite-part matching does not by itself prove that the recursively defined ζ-coefficients are the actual Gamma jet. Either:
- use actual analytic jet coefficients and prove the matching theorem; or
- use the ζ-recurrence and make the log-Gamma-series bridge an explicit hypothesis.

That is useful “closed form modulo the log-Gamma series”; omitting the bridge would overstate the result. A finite recursive implementation avoids unnecessary `PowerSeries` infrastructure.

### 4. **(e) Naive-Bayes ratio — independent alternative, specification needed**

Potentially a good day-sized application if the two evidence asymptotics already exist. Target the **ratio theorem with nonzero leading denominator**, then derive posterior odds. State explicitly whether prior odds are included.

### 5–6. **(f) Cone \(c_3\), then (g) blow-up \(N^{-3/2}\log N\)**

This ordering is provisional: their definitions and existing remainder estimates are not supplied. For either, specify the coefficient through a residual limit and prove an asymptotic with a remainder smaller than the claimed term. For (g), one must also rule out or subtract all intervening terms. I would not call either a certified one-day target from these labels alone.

### 7. **(b) ζ(3) identification — high payoff, not a default day-sized task**

The needed analytic statement is
\[
(\log\Gamma)'''(1)=-2\sum_{n=1}^{\infty}n^{-3}=-2\zeta(3),
\]
followed by
\[
G_1=(\log\Gamma)'''(1)-\gamma^3-\gamma\pi^2/2.
\]

I cannot say which components the pin lacks without inspection. Audit for:
1. a differentiated log-Gamma/digamma series;
2. locally uniform convergence permitting two further differentiations;
3. the natural-number series identification with ζ(3).

A Weierstrass-product or `GammaSeq` route also needs **derivative-convergence justification**; pointwise convergence is insufficient. If that infrastructure is absent, budget a multi-day mini-project, potentially longer—not one more product-rule lemma.

## 3. Convention hazards

- **Real-part symbols:** retain their explicit definitions. Complex identities may be projected to real parts without proving imaginary parts vanish.
- **Normalisation:** `cubicH 0 = √π`, whereas `gammaJetH 0 = 1`. State prominently that \(c_3=\texttt{gammaJetH}'''(0)/6\).
- **Pole sum:** `Fin (natDegree + 1)` includes the constant coefficient. The change \(z=1-2u\) supplies the crucial \(2^{k+1}\) denominator.
- **Direction:** \(u\to0^+\) corresponds to \(z\to1^-\); preserve this in the finite-part comparison.
- **Domain binders:** the displayed `hasDerivAt_cubicH` statements suppress hypotheses. Ensure the public documentation shows the strip \(-1<\Re w<1/2\); unrestricted differentiability would be false.
- **Claim boundary:** DCLXXI formally closes the two-symbol Gamma-jet formula. Label the ζ-form as an external derivation/numerical check until its bridge is formalised.

**Recommendation:** do duplication next; then the log-moment bridge. Together they consolidate \(D_4\) without making ζ(3) infrastructure the critical path.