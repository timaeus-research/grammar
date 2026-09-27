## 1. Fidelity: approved, with two qualifications

On the supplied statements—not an independent checkout/build—DCLXXXIII–DCLXXXIV faithfully close route B.

- **Isolated zeros:** the correct input is frequent equality in the **punctured** neighbourhood `𝓝[≠] 0`. The points `↑(1/(m+3))` are nonzero, tend to zero, and satisfy the real-series identity. Ordinary neighbourhood frequency alone would not exclude equality only at zero. Your implementation addresses precisely this issue. The resulting *eventual equality* is all the jet argument needs; equality on the whole half-ball is unnecessary.
- **Derivative majorant:** for \(k=n+1\ge1\),
  \[
  \left|\frac{(-1)^{j+1}j!}{(k+z)^{j+1}}\right|
  \le \frac{j!2^{j+1}}{k^{j+1}}
  \le \frac{j!2^{j+1}}{k^2}\qquad(j\ge1).
  \]
  Keeping order zero separate is essential.
- **`cpow` adapter:** first normalize the exponent to `((j + 1 : ℕ) : ℂ)`, then use `Complex.cpow_natCast`. This is an exact natural-power identity, not a branch argument.
- **Reality:** `psiOneCoeff_im` and the signed ζ-bridge prove the asserted reality of ζ(3), ζ(5). In fact they give a useful optional generalization: ζ(k) is real for every natural \(k\ge2\).

### Re-deriving \(Q_5\)

Write \(\zeta_k=(\operatorname{riemannZeta}k).re\). The centered logarithmic jet feeding \(h_{5,5}\) has coefficients
\[
\ell_2=\frac{2\pi^2}{3},\qquad
\ell_3=-\frac{\lambda_3}{3},\qquad
\ell_4=\frac{5\lambda_4}{6},\qquad
\ell_5=-\frac{13\lambda_5}{60}.
\]
Consequently,
\[
h_{5,5}
=\frac{a^5}{120}+\frac{a^3\ell_2}{6}
+\frac{a^2\ell_3}{2}
+a\left(\ell_4+\frac{\ell_2^2}{2}\right)
+\ell_2\ell_3+\ell_5.
\]
Substitution gives
\[
\ell_3=\frac23\zeta_3,\quad
\ell_4=\frac{\pi^4}{18},\quad
\ell_5=\frac{26}{5}\zeta_5,
\]
and hence
\[
\boxed{
Q_5=\frac1{8\pi^2}
\left[
\frac{a^5}{120}+\frac{\pi^2a^3}{9}
+\frac{a^2\zeta_3}{3}
+\frac{5a\pi^4}{18}
+\frac{4\pi^2\zeta_3}{9}
+\frac{26}{5}\zeta_5
\right].}
\]

The \(a\pi^4\) coefficient is
\[
\frac1{18}+\frac29=\frac5{18},
\]
with the second contribution coming from \(\ell_2^2/2\).

**Your described slip is not distinguishable as written:** `5aπ⁴/18` and `5π⁴a/18` are identical, and both are correct here.

The other four forms pass the same checks:

- \(Q_3\): cubic exponential coefficient with quadratic log coefficient \(\pi^2/2\) and cubic log coefficient \(4\zeta_3/3\).
- \(D_4\): the stated denominator is correct:
  \[
  \frac{b^3/6+7\pi^2b/12+\zeta_3}{(2\pi)^{3/2}}
  =\frac{2b^3+7\pi^2b+12\zeta_3}{24\pi\sqrt{2\pi}}.
  \]
- \(D_5\): \(h_{5,3}=a^3/6+a\ell_2+\ell_3\).
- \(E_5\): \(h_{5,4}=a^4/24+a^2\ell_2/2+a\ell_3+\ell_4+\ell_2^2/2\).

## 2. §2 post-closure

### (b) Depressed polynomial: do it, but as a small corollary

For \(L\ge2\), expose the vanishing coefficient of degree \(L-2\) **in the centered variable**. If `depthLogDerivCoeff_zero` already expresses the zero linear logarithmic jet, the exponential recurrence at index one proves this immediately.

This deserves a public theorem and perhaps a reader-facing formula—not another substantial workstream. Keep the original and centered polynomial variables visibly distinct.

### (a) Flat prior: worthwhile, and not fundamentally a Mellin computation

Use the existing volume identity, substitute \(y=N t^2/2\), and expand a finite power. With \(m=L-1\),
\[
Q_m(X)=\frac1{\sqrt\pi}
\sum_{j=0}^{m}\binom mj X^{m-j}(-1)^j\Gamma^{(j)}(1/2).
\]
This gives exactly the normalization in your question.

The tail is especially friendly. Put \(A=N/2\), \(X=\log A\); then
\[
|X-\log y|^m=\log^m(y/A)\le ((y-A)/A)^m
\quad(y\ge A).
\]
Thus, at each fixed depth, the omitted tail is actually
\[
O_L\!\left(N^{-L}e^{-N/2}\right),
\]
stronger than the displayed remainder.

**Day-sized qualification:** evaluated \(\Gamma^{(j)}(1/2)\) jets do not by themselves provide
\[
\int_0^\infty e^{-y}y^{-1/2}\log^j y\,dy=\Gamma^{(j)}(1/2).
\]
If the all-order log-moment identity and integrability are public already, yes: a day-sized substitution/binomial/tail module. Otherwise budget a separate all-order moment module. Do not reopen the complex Mellin machinery.

### (c) Observable rates: meaningful, but mind the depth factor

For the Gaussian prior and fixed \(L\ge2\), the leading rate should be
\[
\mathbb E_N[w_1^2]\sim\frac{2(L-1)}{\log N},
\]
not \(2/\log N\) at every depth. At the polynomial level the ratio is
\[
\frac{2P_L'(\log N)}{P_L(\log N)}.
\]

Use a weighted-integral identity or weighted pole expansion. **Do not differentiate an asymptotic remainder without derivative control.**

**Recommendation:** add (b), take (a) if the moment API is ready, then move beyond §2.

## 3. Post-§2 ranking

### 1. **(vi) Blow-up frozen quartic correction**

Best next unit: concrete consumer, existing one-dimensional infrastructure, no new geometric change of variables.

Define, explicitly or through the existing `ampJ`,
\[
J_\infty(\varepsilon)
=\int_{0}^{\infty}
\frac{2e^{-u^4/2}}{\sqrt{u^2+\varepsilon}}\,du,
\qquad R_\infty=\frac{\log2-\gamma_E}{2}.
\]

**Exact target interface**—new names below, adapted to the existing definitions:

```lean
theorem quarticJ_linear_remainder :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        |quarticJ ε
          - (Real.log (4 / ε) + quarticRenorm
              + (Real.sqrt (Real.pi / 2) / 2) * ε)|
          ≤ C * ε ^ 2 * (Real.log (1 / ε) + 1)
```

Here `quarticRenorm` is identified with \((\log2-\gamma_E)/2\) by the existing theorem.

**Proof route:** integrate by parts:
\[
J_\infty(\varepsilon)
=4\int_0^\infty u^3e^{-u^4/2}
       \operatorname{arsinh}(u/\sqrt\varepsilon)\,du.
\]
Subtract
\[
\log(2u/\sqrt\varepsilon)+\frac{\varepsilon}{4u^2}.
\]
Split at \(u=\sqrt\varepsilon\). On the outer region use a quadratic remainder in \(\varepsilon/u^2\); on the inner region use direct bounds. The linear coefficient is
\[
\int_0^\infty u e^{-u^4/2}\,du
=\frac12\sqrt{\frac\pi2}.
\]
A logarithmic expression for `arsinh` can avoid introducing a new special-function API.

**Important sequencing correction:** this \(O(\varepsilon^2\log(1/\varepsilon))\) theorem alone cannot identify the eventual logarithmic coefficient. The next refinement needed is
\[
J_\infty(\varepsilon)
=\log(4/\varepsilon)+R_\infty
+\frac12\sqrt{\frac\pi2}\varepsilon
-\frac3{16}\varepsilon^2\log(1/\varepsilon)
+O(\varepsilon^2).
\]

For the moving amplitude \(e^{-u^4/2}e^{-\varepsilon u^2/2}\):

- its linear contribution cancels the frozen linear term;
- its logarithmic contribution is \(+\frac14\varepsilon^2\log(1/\varepsilon)\);
- the net coefficient is \(1/16\).

Since \(\varepsilon=N^{-1/2}\), multiplication by \(\sqrt{2\pi}N^{-1/2}\) gives precisely
\[
\boxed{\frac{\sqrt{2\pi}}{32}N^{-3/2}\log N.}
\]

### 2. **(v) General-prior cone vertex**

High mathematical value, but separate geometry from Laplace transfer.

A clean sufficient hypothesis is \(F\in C_c^2(\mathbb R^4)\); optimize regularity later. With the note’s normalization of the cone map, the minimal useful density statement is
\[
\lim_{t\downarrow0}
\frac{\rho_F(t)+\rho_F(-t)-2\rho_F(0)}t
=-4\pi^2F(0).
\]
This avoids requiring a canonical full decomposition \(A_F(t)+|t|B_F(t)\), while encoding \(B_F(0)=-2\pi^2F(0)\).

The transfer consumer is
\[
\lim_{N\to\infty}
N\left[
Z_N[F]-\sqrt{2\pi}\rho_F(0)N^{-1/2}
\right]
=-4\pi^2F(0).
\]

Bipolar coordinates and circle averages smooth in squared radii are the right route. But the general Leray identity and the corner calculation should be separate interfaces; together they are not automatically one day-sized unit.

### 3. **(vii) Naive Bayes exact-phase replacement**

First prove a **localized, uniform replacement theorem away from \(V=0\)**, not another surrogate coefficient.

Useful hypotheses in transverse radius \(r\):
\[
K,K_0\ge cr^2,\qquad |K-K_0|\le Cr^3,
\]
together with a density error of order \(r\) relative to an integrable logarithmic envelope. The elementary bound
\[
|e^{-NK}-e^{-NK_0}|
\le N|K-K_0|e^{-cNr^2}
\]
then gives \(O(N^{-2}(1+\log^2N))\) in three transverse dimensions.

First establish these hypotheses for the actual KL phase and density on a compact mean-parameter set with \(V\ge v_0>0\). Boundary integration is a later theorem. The `log V` term is useful bookkeeping inside the surrogate; it is not the missing exact-phase bridge.

### 4. **(viii) Rank-one beyond leading order**

Prefer a regular, nonzero-truth first correction before zero truth, provided the reduced integral already has a uniform local expansion and tail bound. Zero truth changes the singular geometry and is a separate project, not a routine next coefficient.

### 5. **(ix) Quotient-jet tool**

Only with a consumer. A good one is the next Gaussian observable correction from \(2P_L'/P_L\), or a rank-one posterior numerator/denominator pair.

For a first correction, the formula
\[
(b/a)_1=b_1/a_0-b_0a_1/a_0^2
\]
may suffice; do not build an arbitrary-order analytic quotient API merely to prove it.

## 4. Convention checklist

1. **Real ζ:** keep public real formulas as `(riemannZeta k).re`, or introduce an explicitly defined real wrapper. Taking `.re` is not itself a proof of reality.
2. **Natural exponents:** normalize casts before `Complex.cpow_natCast`; avoid general `cpow_add` rewrites here.
3. **Jet normalization:** distinguish
   \[
   \psiOneCoeff(j)=\psi^{(j)}(1)/j!
   \]
   from derivatives themselves. For \(r\ge2\),
   \[
   \lambda_r=(-1)^r(r-1)!\zeta(r).
   \]
4. **Sign:** the series coefficients use \((-1)^{j+1}\), yielding \(+\zeta_2,-\zeta_3,+\zeta_4,-\zeta_5\).
5. **External factors:** retain the \(D_4\) square-root normalization until the last rewrite. Its algebraic numerator is not the complete coefficient.