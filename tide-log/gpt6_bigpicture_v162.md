## Verdict

**For a fixed sample, this is formal division. For the sample average, the useful extra structure is the normalized Gibbs measure and its quenched source function—not a Wick expansion of an inverse partition function.**

I would land a small source/cumulant algebra unit, then a **specialized compact-posterior Stein/interpolation theorem**. I would not make general Banach-space Stein or a divergence theorem prerequisites.

Three corrections to your assessment matter:

1. “Connected coefficients” means **connected in the source variables**. It does not, by itself, give a new expansion in \(N\), or a canonical graph expansion.
2. \(\mathbb E D=\infty\) does **not** imply bad inverse moments or divergent averaged posterior coefficients. In this model, inverse moments of \(D\) are particularly well behaved.
3. Gaussian covariance interpolation of a **posterior expectation** generally involves **three replicas**, not merely a two-replica covariance. The two-replica expression is natural for the quenched log partition function.

---

## 1. What is correct, and what should change

### Fixed sample: yes, but distinguish the two formal variables

For positive evidence and bounded smooth \(f\),
\[
\left.\partial_\varepsilon\log Z_N[\eta e^{\varepsilon f}]\right|_{\varepsilon=0}
 =\frac{Z_N[\eta f]}{Z_N[\eta]},
\]
and
\[
\left.\partial_\varepsilon^2\log Z_N[\eta e^{\varepsilon f}]\right|_{\varepsilon=0}
 =\frac{Z_N[\eta f^2]}{Z_N[\eta]}
  -\left(\frac{Z_N[\eta f]}{Z_N[\eta]}\right)^2.
\]

The best formal source object is actually
\[
\log\frac{Z_N[\eta e^{\varepsilon f}]}{Z_N[\eta]}.
\]
Its constant source coefficient is zero. This avoids choosing a formal logarithm of the leading evidence coefficient.

For finite source order, there is no need to prove an expansion uniform in \(\varepsilon\), or differentiate an asymptotic remainder. Use the finite jet
\[
\sum_{r=0}^{R}\frac{\varepsilon^r}{r!}Z_N[\eta f^r],
\]
and apply `emp_cutoffExpansion` separately to its finitely many entries.

**One coefficient-ring caveat:** after extracting the leading power of \(N\), the leading coefficient can still be a polynomial in \(\log N\). Its inverse need not be polynomial. Thus formal division naturally takes place over a field such as
\[
K=\mathbb R(\ell),\qquad \ell=\log N,
\]
or in the already-established quotient-block representation. Do not advertise the quotient as another polynomial-log `CutoffExpansion` without the corresponding closure theorem.

### Averaging: the proposed obstruction is not the right one

These distinctions should be explicit:

- A formal inverse in the **\(N\)-asymptotic parameter** is legitimate whenever its leading block is invertible.
- A geometric expansion around the **zero-noise denominator** requires additional convergence control. A Gaussian field is unbounded, so the usual geometric-series condition is not generally available globally.
- Wick’s rule evaluates Gaussian polynomial moments. It does not automatically justify integrating a series of nonlinear normalized quantities.

However, the divergence of \(\mathbb E D\) is not a divergence theorem for \(\mathbb E D^{-1}\).

Indeed, let
\[
D_\beta(g)=\int_K\int_0^\infty
t^{\lambda-1}e^{-\beta t+\beta g(x)\sqrt t}\,dt\,d\rho(x),
\]
with \(\beta,\lambda>0\) and \(0<\rho(K)<\infty\). Writing \(M=\|g\|_\infty\), integration over \(0<t<(1+M)^{-2}\) gives
\[
D_\beta(g)\ge
\frac{e^{-2\beta}\rho(K)}{\lambda}(1+M)^{-2\lambda}.
\]
Consequently,
\[
D_\beta(g)^{-1}\le
\frac{\lambda e^{2\beta}}{\rho(K)}(1+\|g\|_\infty)^{2\lambda}.
\]

Thus, under the usual measurable continuous Gaussian-field hypotheses, Fernique gives **all finite inverse moments of \(D_\beta(G)\)**. No small-variance threshold is needed.

This makes a much better sanity theorem than (D).

### Limit Gibbs measure: yes, but retain the radial variable

Use the joint probability measure
\[
\mu_g(dx\,dt)
 =D_\beta(g)^{-1}
 t^{\lambda-1}e^{-\beta t+\beta g(x)\sqrt t}\,d\rho(x)\,dt
\]
on \(K\times(0,\infty)\).

Its \(K\)-marginal has the \(S_\lambda\)-weights you describe. Keeping \(t\) makes derivatives and replicas precise: the tilt observable is simply
\[
T_h(x,t)=\sqrt t\,h(x).
\]

One geometric qualification: identifying the limiting observable with \(f|_K\) requires that the leading inserted coefficient is represented by multiplying the same base measure by that function. This is not automatic for observables whose leading contribution involves normal vanishing orders or normal jets.

---

## 2. Ranking

| Rank | Unit | Decision |
|---|---|---|
| **1** | **(A), finite source jets and formal cumulants** | Highest value per effort. Small deterministic closure of the existing quotient theory. |
| **2** | **Alternative: anchored quenched source function** | Clean exact formulation of averaged posterior cumulants; bounded \(f\) needs no evidence moment threshold. |
| **3** | **(B), specialized to compact posterior observables** | Main new Gaussian mathematics. Prove directional derivatives, Stein, then replica interpolation. |
| **4** | **Alternative: inverse-evidence and normalized radial-moment bounds** | Useful supporting estimates; directly explain why normalization is benign. |
| **5** | **(C), beyond-leading averaged transfer** | Valuable only with explicit rate and uniform-integrability hypotheses. Not a consequence of Gaussian weak convergence. |
| **6** | **General Banach-space version of (B)** | Correct, but more infrastructure than the posterior application needs. |
| **7** | **(D), divergence of unnormalized evidence moments** | Optional diagnostic, not an obstruction theorem for posterior averaging. |

The already-landed bounded-observable leading transfer needs no new unit.

---

## 3. Top unit: exact formal source statement

Let \(k\) be a characteristic-zero field, \(R=k[[x]]\), and let
\[
Z\in R[[\varepsilon]],\qquad B=[\varepsilon^0]Z\in R^\times.
\]
Define
\[
U=B^{-1}Z,\qquad L=\log U.
\]
Here \(U(0)=1\), so the formal logarithm is canonical.

The core theorem is
\[
\boxed{\quad
\partial_\varepsilon L=Z^{-1}\partial_\varepsilon Z.
\quad}
\]

The formal logarithm needs no analytic logarithm. For any commutative \(\mathbb Q\)-algebra \(R\), define its coefficients by the finite formula
\[
[\varepsilon^r]\log U
 =
 \sum_{j=1}^{r}\frac{(-1)^{j+1}}{j}
 [\varepsilon^r](U-1)^j,
 \qquad [\varepsilon^0]U=1.
\]
This definition is directly Lean-typable using `PowerSeries`, finite sums, and rational scalar multiplication.

The useful exported specialization is:

> **Formal posterior cumulants.**  
> Let \(A,B,C\in k[[x]]\), with \(B_0\ne0\), and let
> \[
> Z=B+\varepsilon A+\frac{\varepsilon^2}{2}C+O(\varepsilon^3).
> \]
> Then
> \[
> [\varepsilon]\log(B^{-1}Z)=B^{-1}A,
> \]
> \[
> 2[\varepsilon^2]\log(B^{-1}Z)
>   =B^{-1}C-(B^{-1}A)^2.
> \]

Writing `qA := quotientBlocks A B` and `qC := quotientBlocks C B`, the coefficient-level second statement is exactly
\[
\boxed{
\kappa_2(n)
 =qC(n)-\sum_{i=0}^{n}qA(i)qA(n-i).
}
\]
The first is \(\kappa_1(n)=qA(n)\).

For all source orders, put
\[
m_r=B^{-1}Z_r,\qquad
Z=\sum_{r\ge0}Z_r\frac{\varepsilon^r}{r!},
\qquad m_0=1.
\]
Then the cumulants are characterized by
\[
\boxed{
\kappa_{r+1}
 =
 m_{r+1}
 -\sum_{i=0}^{r-1}
   \binom ri\,\kappa_{i+1}m_{r-i}.
}
\]
Products here are Cauchy products in \(x\). This recurrence is an especially convenient API over `ℕ → k`.

### Proof dependencies

- `quotientBlocks_zero/succ`: identify the coefficients of \(B^{-1}A\) with the existing quotient.
- Formal power-series multiplication and derivative: prove \(U L'=U'\), coefficientwise if necessary.
- `emp_cutoffExpansion`: instantiate \(Z_r\) with the expansion for \(\eta f^r\).
- `empCoeff_unique`: identify linear combinations of coefficient families when forming finite source jets.
- Existing all-orders quotient bridge: transfer the first and second cumulant identities back to posterior mean and variance asymptotics.

This adds conceptual organization, not a second analytic quotient engine.

---

## 4. The better exact averaged object: an anchored quenched source

For bounded \(f\), define
\[
\Psi(\varepsilon)
 =
 \mathbb E\log
 \frac{D_\beta(G;\rho e^{\varepsilon f})}
      {D_\beta(G;\rho)}
 =
 \mathbb E\log\langle e^{\varepsilon f}\rangle_G.
\]

The anchoring is important: it avoids requiring separate integrability of either log evidence.

If \(\|f\|_\infty\le M\), then pointwise
\[
\left|\log\langle e^{\varepsilon f}\rangle_G\right|
 \le |\varepsilon|M.
\]
Consequently,
\[
\boxed{\Psi'(0)=\mathbb E\langle f\rangle_G,}
\]
\[
\boxed{
\Psi''(0)
 =\mathbb E\bigl[\langle f^2\rangle_G-\langle f\rangle_G^2\bigr].
}
\]
More generally,
\[
\Psi^{(r)}(0)=\mathbb E\,\kappa_r^{\mu_G}(f).
\]

These are **averages of conditional cumulants**, not cumulants under the sample-averaged Gibbs measure.

There is even a genuinely convergent source expansion. For \(M>0\), the elementary bound
\[
|\langle e^{zf}\rangle_G-1|\le e^{|z|M}-1
\]
gives a uniform logarithmic expansion on every closed disk strictly inside
\[
|z|<\frac{\log 2}{M}.
\]
Hence
\[
\Psi(\varepsilon)
 =\sum_{r\ge1}\frac{\varepsilon^r}{r!}
   \mathbb E\,\kappa_r^{\mu_G}(f)
\]
there.

**This is a convergent expansion in the source, not in covariance or \(N^{-1/Q}\).** That distinction should appear prominently in the notes.

The reciprocal Laplace identity
\[
D^{-1}=\int_0^\infty e^{-uD}\,du
\]
is exact but inferior here: expanding \(e^{-uD}\) invokes positive evidence moments and usually destroys the useful domination. Replica limits such as \(D^{-1}=\lim_{r\to0}D^{r-1}\) add an analytic-continuation problem rather than solving one.

---

## 5. The precise compact-posterior Stein theorem

Assume:

- \(K\) is compact metric;
- \(\rho\) is a finite positive Borel measure with \(\rho(K)>0\);
- \(\beta,\lambda>0\);
- \(\mathcal C\) is continuous and positive semidefinite;
- \(G:\Omega\to C(K,\mathbb R)\) is measurable, centered Gaussian, with covariance \(\mathcal C\);
- \(f\in C(K,\mathbb R)\).

Write \(F_f(g)=\langle f\rangle_g\), with \(f(x,t)=f(x)\).

### Derivative theorem

Use a **Fréchet derivative on `C(K, ℝ)` with the sup norm**:
\[
DF_f(g):C(K,\mathbb R)\to_L\mathbb R.
\]
Its formula is
\[
\boxed{
DF_f(g)[h]
 =
 \beta\left(
 \langle f\sqrt t\,h(x)\rangle_g
 -
 \langle f\rangle_g\langle\sqrt t\,h(x)\rangle_g
 \right).
}
\]

In Lean, the derivative witness has type
```lean
F' : C(K, ℝ) → (C(K, ℝ) →L[ℝ] ℝ)
```
and the differentiability statement is
```lean
∀ g, HasFDerivAt F_f (F' g) g
```

A directional derivative only along \(\mathcal C(x,\cdot)\) would suffice for one Stein identity. The Fréchet formula is nevertheless the better specialized API: it also supports interpolation and higher derivatives.

### Stein theorem: use replicas, not a delta observable

For \(x_0\in K\), let
\[
c_{x_0}(x)=\mathcal C(x_0,x)\in C(K,\mathbb R).
\]
Then
\[
\boxed{
\mathbb E[G(x_0)F_f(G)]
 =\mathbb E[DF_f(G)[c_{x_0}]].
}
\]

Equivalently, with two conditionally independent replicas,
\[
\boxed{
\mathbb E[G(x_0)\langle f\rangle_G]
 =
 \beta\,\mathbb E\left\langle
 f(x_1)\left(
 \sqrt{t_1}\mathcal C(x_0,x_1)
 -
 \sqrt{t_2}\mathcal C(x_0,x_2)
 \right)
 \right\rangle_G^{\otimes2}.
}
\]

This avoids the ambiguous notation \(T_{x'}\), which would otherwise hide a delta distribution or a Radon–Nikodym convention.

A useful energy corollary is
\[
\boxed{
\mathbb E\langle \sqrt t\,G(x)\rangle_G
 =
 \beta\,\mathbb E\left[
 \langle t\,\mathcal C(x,x)\rangle_G
 -
 \left\langle
 \sqrt{t_1t_2}\mathcal C(x_1,x_2)
 \right\rangle_G^{\otimes2}
 \right].
}
\]
Its proof applies Stein to the weighted posterior densities; it is not obtained by treating the field-dependent observable \(G(x)\) as fixed during differentiation.

### Passing from atoms to the compact base

For this specialized theorem, the existing quantisation route is sufficient:

1. Take \(\rho_n=(q_n)_*\rho\) from `exists_quantisation_seq`.
2. Apply `gaussianVector_stein` to the joint Gaussian vector consisting of \(G(x_0)\) and the finitely many atom values.
3. Identify its derivative with the finite-atom posterior covariance.
4. Use `tendsto_compactD_map` and the analogous numerator convergence for \(f\), kernel sections, and radial insertions.
5. Pass through expectation using polynomial bounds in \(1+\|G\|_\infty\).

The relevant domination is for **normalized radial moments**, for example
\[
\langle t^p\rangle_g
 \le C_p(1+\|g\|_\infty)^{2p},
\]
with constants depending on the fixed parameters. Such bounds imply polynomial bounds for the derivative and replica expressions. Fernique, or the already-assumed exponential jet moment when working in that setting, supplies integrability.

Do **not** dominate the ratios by independently bounding the numerator exponentially and the denominator below polynomially. That can unnecessarily reintroduce the unnormalized-evidence threshold.

### If you nevertheless want general Banach Stein

A clean statement uses:

```lean
F  : C(K, ℝ) → ℝ
F' : C(K, ℝ) → (C(K, ℝ) →L[ℝ] ℝ)
hF : ∀ g, HasFDerivAt F (F' g) g
hF' : Continuous F'
```

together with polynomial bounds on `|F g|` and `‖F' g‖`. The conclusion is
```lean
∫ ω, G ω x * F (G ω) ∂P
  = ∫ ω, F' (G ω) (kernelSection C x) ∂P
```

Finite-atom quadrature alone does not approximate an arbitrary functional on `C(K, ℝ)`. Use finite-rank **continuous interpolation operators**
\[
P_ng=\sum_i\psi_{n,i}\,g(x_{n,i}),
\]
where \(\psi_{n,i}\) form a partition of unity. Then
\[
\|P_n\|\le1,\qquad P_ng\to g,
\]
and finite-dimensional Stein gives
\[
\mathbb E[G(x)F(P_nG)]
 =
 \mathbb E[DF(P_nG)[P_nc_x]].
\]
Continuous \(F'\), polynomial bounds, and dominated convergence finish the proof.

That extra approximation infrastructure is why I rank the general theorem below the specialized one.

---

## 6. Covariance interpolation: the exact diagrammatic formula

Define
\[
A(s)=\mathbb E\langle f\rangle_{\sqrt sG},
\qquad
R_{ab}=\sqrt{t_at_b}\,\mathcal C(x_a,x_b).
\]
Then, for \(s>0\),
\[
\boxed{
A'(s)=\frac{\beta^2}{2}\,
\mathbb E\left\langle
f(x_1)\bigl(R_{11}-2R_{12}-R_{22}+2R_{23}\bigr)
\right\rangle_{\sqrt sG}^{\otimes3}.
}
\]

Thus
\[
\boxed{
A(1)=A(0)+\frac{\beta^2}{2}\int_0^1
\mathbb E\left\langle
f(x_1)\bigl(R_{11}-2R_{12}-R_{22}+2R_{23}\bigr)
\right\rangle_{\sqrt sG}^{\otimes3}\,ds.
}
\]

Here \(A(0)=\rho(f)/\rho(K)\). The coefficients \(1,-2,-1,2\) come from differentiating a normalized expectation twice. In particular, **three replicas really occur**.

This is the appropriate “one covariance line” theorem. Your existing `integral_log_compactD_eq` is its free-energy counterpart, where differentiating the logarithm gives the simpler two-replica structure.

Iterating interpolation produces finite-order expansions with exact integral remainders. That is a rigorous diagrammatic calculus: covariance contractions supply lines, and normalization supplies connected/replica subtractions.

But:

> Smooth interpolation to every finite order does not imply convergence of the infinite covariance Taylor series.

Moreover, covariance amplitude \(s\) is not the asymptotic parameter \(N^{-1/Q}\). Unless the model introduces a small-noise scaling, these diagrams describe the random leading Gibbs object and its perturbations, not automatically the subleading \(N\)-expansion.

---

## 7. What is actually needed beyond leading order in the sample average

The relevant theorem is an **averaging-of-remainders theorem**, not another quotient theorem.

Schematically, suppose the existing fixed-sample expansion gives
\[
R_N=\sum_{j=0}^{m}a_{N,j}\,Q_j(G_N)+r_N.
\]
To average at a desired scale \(b_N\), require
\[
b_N\,\mathbb E|r_N|\longrightarrow0,
\]
and sufficient rate information for
\[
\mathbb E Q_j(G_N)-\mathbb E Q_j(G).
\]

Convergence in distribution of \(G_N\) only handles the leading limit, with uniform integrability where needed. It supplies no prescribed \(N^{-1/2}\) rate. Corrections can receive contributions from both:

1. the geometric/evidence expansion;
2. the correction to the law of \(G_N\), typically Edgeworth-type data.

Nor is \(N^{-1/2}\) universally the first correction: the exponent lattice and logarithmic quotient structure decide that.

So (C) should not be presented as a small extension of `tendsto_integral_expectation`.

---

## 8. What to say about the threshold

For a single Gaussian value of variance \(v\), Tonelli gives
\[
\mathbb E S_\lambda(\beta;G)
 =
 \int_0^\infty
 t^{\lambda-1}e^{-(\beta-\beta^2v/2)t}\,dt.
\]
It is finite exactly when
\[
\beta v<2.
\]
At \(\beta=1\), this is your variance threshold \(v<2\).

For a compact base, integrate this extended-valued expression against \(\rho\). A positive-\(\rho\)-measure supercritical set forces divergence; a single supercritical point need not.

The correct conclusion is:

> Unnormalized evidence averaging can fail while normalized posterior expectations and all inverse evidence moments remain finite.

That is a useful distinction—not a proof that averaged quotient expansions are impossible.

---

## 9. Short literature list

- **Quenched free energy and thermal/replica cumulants:** the standard language for \(\mathbb E\log Z\) and its source derivatives.
- **Gaussian integration by parts and replica identities in spin glasses:** Talagrand, *Mean Field Models for Spin Glasses*; Panchenko, *The Sherrington–Kirkpatrick Model*.
- **Gaussian covariance interpolation / smart path:** Guerra–Toninelli, “The thermodynamic limit in mean field spin glass models” (2002), and the above books. “Guerra interpolation” is appropriate when emphasizing the spin-glass comparison method, rather than every Gaussian interpolation identity.
- **Gaussian covariance differentiation:** **Price’s theorem** is the direct classical name for differentiation of Gaussian expectations with respect to covariance.
- **Singular-learning posterior identities:** Watanabe, “Equations of States in Singular Statistical Estimation” (2010).
- **Classical ratio asymptotics:** Tierney–Kadane, “Accurate Approximations for Posterior Moments and Marginal Densities” (1986).

“Schwinger–Dyson” is a useful analogy, but “Gaussian IBP, replica identities, and covariance interpolation” is the more precise primary description here.