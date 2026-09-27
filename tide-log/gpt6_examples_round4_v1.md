## 1. Fidelity and normalisation

Based on the supplied theorem summaries, **DCIV–DCVI match the stated scope well**:

- **DCIV:** the fixed-fibre polar dictionary is correct. “The odd term and cutoff are holomorphic” should retain the domain qualifier **\(\Re s<1\)** and the fixed-cutoff hypothesis.
- **DCV:** closes the arbitrary-smooth-amplitude gap. It does not yet identify or assemble the geometric blow-up charts.
- **DCVI:** establishes the Gaussian zeta identity and leading singularity, not the Laplace asymptotics. Say “order-\(L\) pole” for **\(L\ge1\)**; \(L=0\) is regular.

### Phase normalisation and the positive asymptotic coefficient

With the **normalised standard Gaussian prior** and \(T=\prod_i W_i\),
\[
K=T^2/2,\qquad
\zeta_K(s)=\mathbb E K^{-s}
=2^s\zeta_L(s).
\]
Thus the leading coefficient at \(s=\tfrac12\), expressed in powers of \(s-\tfrac12\), is
\[
a_{-L}
=2^{1/2}\left(-\frac1{\sqrt{2\pi}}\right)^L.
\]

For
\[
Z_N=\mathbb E e^{-NK},
\]
the Mellin integrand is \(\Gamma(s)\zeta_K(s)N^{-s}\). **Conditional on a justified contour transfer**, its contribution at \(s=\tfrac12\) is minus the residue. Consequently,
\[
[N^{-1/2}(\log N)^{L-1}]\,Z_N
=\frac{(-1)^L\Gamma(\tfrac12)a_{-L}}{(L-1)!}
=\boxed{\frac1{(L-1)!(2\pi)^{(L-1)/2}}.
\]
The signs therefore agree exactly. The two signs come from the expansion of \(N^{-s}\) and the minus-residue convention for shifting this Mellin contour rightward.

The same calculation gives the centring
\[
\boxed{\kappa_L=(L+1)\log 2-(L-1)\gamma}.
\]
Indeed, with \(r=s-\tfrac12\),
\[
\Gamma(s)\zeta_K(s)
=\Gamma(\tfrac12)a_{-L}r^{-L}
\left(1+\big((L-1)\gamma-(L+1)\log2\big)r+O(r^2)\right).
\]

**Important normalisation correction:** at depth two,
\[
Z_N=\frac{\log N+3\log2-\gamma}{\sqrt{2\pi N}}
+O(N^{-3/2}\log N)
\]
for the **probability-normalised** prior. Your proposed expression with an additional \(2\pi\) is correct for the **unnormalised** two-dimensional Gaussian integral.

## 2. Next three day-sized targets

These are proposed statements, not claims about existing API names.

### 1. Gaussian depth-two exact reduction — best immediate value/effort

Define `gaussLaplace2 N` using the normalised Gaussian prior. Prove, for \(N>0\),
\[
\boxed{
Z_N=\frac1{\sqrt{2\pi}}\int_{\mathbb R}
\frac{e^{-y^2/2}}{\sqrt{1+Ny^2}}\,dy
}
\]
and, if the substitution budget permits,
\[
\boxed{
Z_N=\frac1{\sqrt{2\pi N}}\int_0^\infty
\frac{e^{-v}}{\sqrt{v(v+1/(2N))}}\,dv.
}
\]

Schematic Lean target:
```lean
theorem gaussLaplace2_eq_integral
    {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ y : ℝ,
          Real.exp (-y^2 / 2) / Real.sqrt (1 + N*y^2)
```

**Route:** dominate the joint integrand by the Gaussian density; use Fubini; evaluate the conditional Gaussian integral with quadratic coefficient \(1+Ny^2>0\). This needs no product-density theorem, Bessel theory, or Mellin inversion.

**Day boundary:** land the exact reduction and integrability witnesses. Treat the constant-term asymptotic as a follow-up, not part of the acceptance criterion.

### 2. \(H_2=\Gamma''(\tfrac12)\) and its explicit value

Target
\[
\boxed{
\Gamma''(\tfrac12)
=\sqrt\pi\left((\gamma+2\log2)^2+\frac{\pi^2}{2}\right).
}
\]

A useful first Lean statement avoids Euler-constant API details:
```lean
theorem gamma_second_deriv_half :
    deriv (deriv Complex.Gamma) (1 / 2 : ℂ) =
      Complex.Gamma (1 / 2 : ℂ) *
        ((deriv Complex.Gamma (1 / 2 : ℂ) /
            Complex.Gamma (1 / 2 : ℂ))^2
          + (Real.pi : ℂ)^2 / 2)
```

**Route:** differentiate the reflection identity
\[
\Gamma(z)\Gamma(1-z)=\frac{\pi}{\sin\pi z}
\]
twice near \(z=\tfrac12\). At that point,
\[
2\Gamma\Gamma''-2(\Gamma')^2=\pi^3.
\]
Use \(\Gamma(\tfrac12)=\sqrt\pi\) and the existing first-derivative value.

This is a **local derivative calculation**, not a trigamma development. If the note defines \(H_2\) by a log-squared Gamma integral, identifying that integral with \(\Gamma''\) remains a separate differentiation-under-the-integral lemma.

**Payoff:** removes (f), and supplies the missing constant behind the Gaussian quadratic coefficient \(\pi^2(L+3)/12\). It still does not prove asymptotic transfer.

### 3. An averaged log²-fibre theorem with an explicit domination hypothesis

Do **not** begin with the full naive-Bayes geometry. Package the analytic interface needed to integrate DCIV over \(\lambda\).

Write the fixed-fibre continuation as
\[
F_\lambda(s)=2\phi_\lambda(0)\,
 \mathrm{logSqRat}(\ell_\lambda,c_\lambda,s)+H_\lambda(s).
\]
Prove that integration over \(\lambda\) commutes with this decomposition and that
\[
\bar H(s)=\int H_\lambda(s)\,d\nu(\lambda)
\]
is holomorphic near \(\tfrac12\), under joint measurability and compact-uniform integrable domination.

Schematic core statement:
```lean
theorem differentiableOn_integral_logSqHolo
    -- measurable family;
    -- each H λ holomorphic on U;
    -- integrable domination locally uniformly in s ∈ U
    :
    DifferentiableOn ℂ (fun s => ∫ λ, H λ s ∂ν) U
```

The resulting coefficients are explicitly
\[
\bar C_3=-\int\phi_\lambda(0)\,d\nu,\quad
\bar C_2=2\int\ell_\lambda\phi_\lambda(0)\,d\nu,\quad
\bar C_1=\int(c_\lambda-2\ell_\lambda^2)\phi_\lambda(0)\,d\nu.
\]

**Concrete envelope to aim for:** choose \(0<\varepsilon<\tfrac12\), control the amplitudes uniformly in a suitable \(C^1\) norm, and assume integrability of
\[
B(\lambda)\,M(\lambda)^{-2\varepsilon}
\bigl(1+|\log M(\lambda)|^3\bigr),
\]
where \(B\) includes the amplitude norms and \(1+\ell^2+|c|+|b|\). This supports continuation to \(\Re s<\tfrac12+\varepsilon\).

**Day boundary:** the abstract integration theorem and coefficient formula. Verifying the envelope for the actual \(M(\lambda)\), including boundary faces, is a separate geometric target. This separation prevents accidentally promoting the full model to a theorem.

I would defer general Mellin inversion, noncompact Morse–Bott, and posterior domination: each introduces substantially more infrastructure.

## 3. Depth two without Bessel functions

**Yes: there is an excellent Bessel-free exact integral representation. No: the zeta’s Gamma-product form does not eliminate the inverse-transform problem.**

Conditioning on one Gaussian gives the first reduction above. Substituting \(y=\sinh u/\sqrt N\) yields
\[
Z_N=\sqrt{\frac2{\pi N}}
\int_0^\infty e^{-\sinh^2u/(2N)}\,du.
\]
Equivalently, if one *chooses* to name the standard Bessel integral,
\[
\boxed{
Z_N=\frac{e^{1/(4N)}}{\sqrt{2\pi N}}\,
K_0\!\left(\frac1{4N}\right).
}
\]
This is the classical special-function closed form; there is no standard finite Gamma-only simplification.

For Lean, the most useful representation is instead
\[
J(\epsilon)=\int_0^\infty\frac{e^{-v}}{\sqrt{v(v+\epsilon)}}\,dv,
\qquad
Z_N=\frac{J(1/(2N))}{\sqrt{2\pi N}}.
\]

A direct proof of the two-term expansion can use
\[
J(\epsilon)=
\underbrace{\int_0^1\frac{dv}{\sqrt{v(v+\epsilon)}}}
_{\,2\operatorname{arsinh}(1/\sqrt\epsilon)}
+
\int_0^\infty
\frac{e^{-v}-\mathbf1_{(0,1)}(v)}
     {\sqrt{v(v+\epsilon)}}\,dv.
\]
The first term is \(\log(4/\epsilon)+O(\epsilon)\); the second is
\[
-\gamma+O\!\left(\epsilon\log(1/\epsilon)\right).
\]
Splitting at \(v=\epsilon\) and \(v=1\) gives elementary bounds for the latter error. Hence
\[
J(\epsilon)=\log(4/\epsilon)-\gamma
+O\!\left(\epsilon\log(1/\epsilon)\right),
\]
which proves the depth-two expansion without Bessel or inversion infrastructure.

For comparison, the Mellin–Barnes formula is
\[
Z_N=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
\Gamma(s)\frac{2^{-s}\Gamma(\tfrac12-s)^2}{\pi}
N^{-s}\,ds,\qquad 0<c<\tfrac12.
\]
That is mathematically useful but **formally more expensive here**.

**Recommendation:** formalise the exact conditional-Gaussian reduction now; pursue the direct \(J(\epsilon)\) expansion next. Leave the all-depth pole-to-asymptotic transfer labelled a derivation until an actual converse mechanism is implemented.