## 1. Fidelity check

**On the supplied summaries, the five rows support the note’s claims**, with three qualifications worth making explicit:

- **DXCIX:** the polar dictionaries match the stated convention: coefficients multiply powers of \(s-\mu\). The full-interval factor of two and the mixed-density opposite signs are correct. These are identities of functionals on the stated Lipschitz-at-zero test class; no larger test-function framework should be implied without a bridge.
- **DC:** this proves the smooth tie formula **conditional on a supplied decomposition**, now with continuous profiles. It does not yet prove the decomposition for arbitrary smooth \(\eta\). Also retain the sign distinction between the negative simple-pole coefficient \(C_{\frac12,1}\) and any positively signed \(A_{\frac12,1}\) in the paper.
- **DCI–DCIII:** together they genuinely identify the expansion with the model integral, not merely with a one-dimensional surrogate.

Thus **“eq. (dln_flat) is a theorem for the model at every positive depth” is honest**, provided the equation means:
\[
L\ge1,\quad N>0,\qquad
Z_N=\frac{\sqrt2}{(L-1)!\sqrt N}P_{L-1}(\log N-\log2)-R_{L-1}(N)
\]
with the displayed integral definitions of \(H_j\) and the stated exponential bound. Unevaluated, explicitly defined constants are perfectly legitimate theorem coefficients. A bounded exponential remainder is stronger than an unspecified algebraic asymptotic remainder; it need not itself be expanded.

Two editorial cautions:

1. This \(Z_N\) uses **Lebesgue measure on the box**. A probability-normalized uniform prior contributes \(2^{-L}\).
2. Do not silently upgrade the definitions of all \(H_j\) to formalized identities \(H_j=\Gamma^{(j)}(\tfrac12)\).

## 2. Next three day-sized targets

The statements below are schematic Lean interfaces, not claims about existing API names.

### 1 — Hadamard decomposition and arbitrary-amplitude tie formula

**Highest value-per-effort:** it removes a hypothesis from a central theorem using genuinely new analysis.

First prove a reusable \(C^2\) decomposition:

```lean
theorem exists_continuous_wallDecomposition
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ 2 η) :
    ∃ g₁ g₂ : ℝ → ℝ, ∃ ρ : (Fin 2 → ℝ) → ℝ,
      Continuous g₁ ∧ Continuous g₂ ∧ Continuous ρ ∧
      η = tieAmp (η 0) g₁ g₂ ρ
```

Then feed the witnesses to `chartPolarCoeff_tieAmp_half'`, under the existing smoothness hypothesis on \(\eta\). Prefer also defining **canonical** profiles, so the resulting coefficient theorem does not merely expose existential witnesses.

**Route:** two pathwise FTCs, continuity under integration over a compact square, then the existing tie theorem. No new meromorphic-continuation machinery.

### 2 — The log² polar dictionary, including cutoff and odd term

This directly advances (d), without claiming to solve the \(\lambda\)-dependent model.

For fixed \(V,M>0\), write \(\ell=\log\sqrt V\), and define
\[
F_\varphi(s)=
\int_{-M}^{M}
\varphi(t)\bigl(2\log^2(\sqrt V/|t|)-c+b\,\operatorname{sgn}t\bigr)
|t|^{-2s}\,dt .
\]
Endpoint values at \(t=0\) are immaterial. For continuous \(\varphi\), Lipschitz at zero, prove strip agreement with a continuation and:

```lean
-- z := s - (1/2 : ℂ)
-- Fcont - (-φ(0)/z^3 + 2*ℓ*φ(0)/z^2
--                       + (c - 2*ℓ^2)*φ(0)/z)
-- is holomorphic near 1/2, hence O(1).
```

In particular,
\[
C_{\frac12,3}=-\delta_0,\qquad
C_{\frac12,2}=2\ell\,\delta_0,\qquad
C_{\frac12,1}=(c-2\ell^2)\delta_0.
\]

The odd term contributes no pole: after symmetrization its amplitude is
\(b(\varphi(t)-\varphi(-t))=O(t)\). The cutoff \(M\) changes only a holomorphic term.

**Route:** differentiate the existing log Mellin identity once more:
\[
\int_0^1t^{-2s}\log^2(1/t)\,dt=\frac{2}{(1-2s)^3}.
\]
Use power majorants for the logarithms, the existing Mellin differentiation theorem, symmetrization, and principal-part uniqueness.

**Scope guard:** this is a fixed-fibre theorem. Passing to the actual \((\lambda,\mu)\) density still requires control as \(M(\lambda)\) varies or vanishes.

### 3 — Gaussian-product zeta identity and exact leading pole

Choose a **normalized standard Gaussian prior**, and formalize the product moment rather than promising the entire Gaussian-prior asymptotic.

```lean
theorem gaussianProductZeta_eq
    (L : ℕ) (s : ℂ) (hs : s.re < 1 / 2) :
    gaussianProductZeta L s =
      (((2 : ℂ) ^ (-s)) *
        Complex.Gamma (1 / 2 - s) /
        (Real.sqrt Real.pi : ℂ)) ^ L
```

The definition should mean
\[
\zeta_L(s)=\mathbb E\!\left[|\textstyle\prod_i W_i|^{-2s}\right],
\qquad W_i\sim N(0,1).
\]

For \(L\ge1\), also prove a holomorphic renormalization near \(\tfrac12\):
\[
(s-\tfrac12)^L\zeta_L(s)
\longrightarrow (-1)^L(2\pi)^{-L/2}.
\]

**Route:** one-dimensional complex Gaussian moment by \(x=w^2/2\), absolute integrability from \(\Re s<\tfrac12\), product Fubini, then the Gamma functional equation. This is moderately riskier than the first two targets: the complex Gamma-integral bridge is the likely cost centre.

**Leave as derivations:** (c), (e), (f), (g), (h), and the full asymptotic part of (b). Trigamma is a special-function infrastructure project; averaged normalized posteriors require a genuinely different domination argument; chart assembly and nonlinear/Morse–Bott passages need geometric or uniform remainder estimates absent from the current inventory. They should not be disguised as corollaries of local integral evaluations.

## 3. Cheapest route for Hadamard

**Use the integral representation, not a generic Taylor theorem.**

Let \(e_0,e_1\) be the coordinate vectors. Define
\[
\begin{aligned}
g_1(u)&=\int_0^1 D\eta(tu,0)[e_0]\,dt,\\
g_2(v)&=\int_0^1 D\eta(0,rv)[e_1]\,dr,\\
\rho(u,v)&=\int_0^1\int_0^1
D^2\eta(tu,rv)[e_0,e_1]\,dr\,dt.
\end{aligned}
\]
Choose the order of the iterated derivative to match the two FTC applications; no mixed-partial interchange is needed.

Apply FTC along paths parameterized by \([0,1]\). This gives, including when either coordinate is zero,
\[
\eta(u,v)-\eta(u,0)-\eta(0,v)+\eta(0,0)=uv\,\rho(u,v).
\]

Advantages in Lean:

- no division or separate axis limits;
- no variable integration domains;
- negative coordinates work automatically;
- continuity follows directly from continuity of \(D^2\eta\) and compact parameter integration;
- away from the axes, the quotient formula is just algebra.

Use `fderiv`/iterated `fderiv` and coordinate evaluation, rather than introducing a partial-derivative abstraction first. Apply the existing continuous-parametric-integral tool twice.

**Estimate:** roughly **250–500 lines** for definitions, continuity, and the decomposition, depending on the derivative-evaluation API friction; the arbitrary-smooth tie corollary should then be short. A plausible focused day, not a guaranteed tiny patch. A Taylor remainder theorem usually introduces unnecessary bookkeeping for cancelling the pure-axis terms.

## 4. Gaussian Mellin route: yes, but separate three claims

### Exact transform

Yes:
\[
\mathbb E|W_1\cdots W_L|^{-2s}
=
\left(\frac{2^{-s}\Gamma(\frac12-s)}{\sqrt\pi}\right)^L,
\qquad \Re s<\tfrac12.
\]
For the actual phase \(K=(\prod W_i)^2/2\),
\[
\zeta_K(s)=2^s\zeta_L(s).
\]
That factor matters for every constant.

### Local polar extraction

This is particularly clean without polygamma. Put \(\varepsilon=\tfrac12-s\) and use
\[
\Gamma(\varepsilon)^L=\varepsilon^{-L}\Gamma(1+\varepsilon)^L.
\]
Everything after \(\varepsilon^{-L}\) is holomorphic. The principal part is therefore a finite Taylor jet of a holomorphic function.

**The cleanest genuinely new next theorem is the exact transform plus its nonzero order-\(L\) leading pole.** Higher coefficients can initially remain derivatives of the regularized factor.

### Partition-function asymptotics

This is **not** supplied by local polar extraction alone: one still needs Mellin inversion and contour estimates, or a suitable Tauberian/asymptotic transfer theorem.

Also, **do not reuse the flat-prior polynomial \(P_m\)**. The Gaussian polynomial has different higher cumulants. The relevant regularized Mellin kernel is
\[
H_L(\varepsilon)=
2^{(1-L)(1/2-\varepsilon)}\pi^{-L/2}
\Gamma(\tfrac12-\varepsilon)\Gamma(1+\varepsilon)^L.
\]
Its logarithmic linear coefficient is exactly
\[
\kappa_L=(L+1)\log2-(L-1)\gamma,
\]
but its logarithmic quadratic coefficient is
\[
\frac{\pi^2(L+3)}{12}.
\]
Consequently, at \(L=3\), the centered monic Gaussian polynomial is
\[
X^2+\pi^2,
\]
whereas the centered monic flat polynomial is \(X^2+\pi^2/2\).

So the proposed shift \(\kappa_L\) is right, but a shifted copy of the already-defined flat \(P_{L-1}\) is not. Give the Gaussian family a distinct name and define it by the finite jet of \(H_L\); leave the asymptotic-transfer claim separate until proved.