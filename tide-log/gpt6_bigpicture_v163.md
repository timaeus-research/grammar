## Decision

**Do (I) next, stopping at the compact-base integrated identity.** Prove the finite-atom derivative as the implementation lemma; do not simultaneously build a joint-Gibbs-measure API, general Banach-space Stein theorem, or general covariance interpolation theorem.

My ranking for the paper’s narrative is:

| Rank | Candidate | Assessment |
|---|---|---|
| **1** | **I** | The next genuinely new identity for an averaged posterior expectation. It makes the replica calculus do work beyond rewriting Stein. |
| **2** | **II** | Best presentation payoff, but not a new result and not quite free in Lean. Build it after the moment identity it will package. |
| **3** | **V** | Clean and reusable, especially for posterior-functional calculus. Not needed for the quantisation route to (I). |
| **4** | **VI** | Potentially excellent, but only after checking for joint convergence and uniform integrability. Moves to second place if these are already available. |
| **5** | **IV** | Predictable extension, but it advances the fixed-sample expansion story rather than averaged Gibbs expectations. |
| **6** | **III** | Attractive, but analytic identification and uniform interchange are a substantial new front. “Formal cumulants exist” is much cheaper than this theorem. |

The reason to prefer (I) despite its size: **(II) and (V) primarily re-express the landed identity; (I) computes the change in the averaged posterior mean caused by the Gaussian field.**

---

## 1. Candidate (I): the formulas are correct

Write, on finite atoms,
\[
D(g)=\sum_j\rho_jS_\lambda(g_j),\qquad
F(g)=\frac{\sum_j\rho_j f_jS_\lambda(g_j)}{D(g)},
\]
and
\[
W_j(g)=\frac{\rho_jS_{\lambda+1/2}(g_j)}{D(g)},\qquad
R_j(g)=\frac{\rho_jS_{\lambda+1}(g_j)}{D(g)}.
\]

Under your convention \(S_\nu'=\beta S_{\nu+1/2}\),
\[
\partial_iW_j
=\beta\delta_{ij}R_j-\beta W_iW_j.
\]
Consequently,
\[
\boxed{
\partial_i\partial_jF
=\beta^2\left[
\delta_{ij}R_j(f_j-F)
-W_iW_j(f_j-F)
-W_iW_j(f_i-F)
\right].
}
\]

This includes diagonal and off-diagonal cases without an omitted term.

For a **centred** Gaussian vector with covariance \(b\), put
\[
A(s)=\mathbb E F(\sqrt{s}\,G).
\]
For \(s>0\),
\[
A'(s)=\frac12\mathbb E\sum_{i,j}b_{ij}
  \partial_i\partial_jF(\sqrt{s}G).
\]
Using symmetry of \(b\), your proposed contraction follows:
\[
\boxed{
A'(s)=\frac{\beta^2}{2}\mathbb E\left[
\sum_jb_{jj}R_j(f_j-F)
-2\sum_{i,j}b_{ij}W_iW_j(f_j-F)
\right]_{\sqrt{s}G}.
}
\]

There is no residual \(s^{-1/2}\) in the final expression.

### Implementation recommendation

Do **not** make a full second-Fréchet-derivative theorem the prerequisite. The coordinate identity
\[
\partial_i\bigl(W_j(f_j-F)\bigr)
\]
is enough for the finite-dimensional Stein step and should fit the existing `PolyBoundedPi` infrastructure.

---

## 2. The compact-base endpoint

Fix the usual hypotheses: compact metric base, finite nonzero positive \(\rho\), \(\lambda,\beta>0\), continuous real \(f\), and the landed centred Gaussian-field assumptions.

Define only these additional moment quantities:
\[
T_g(\phi)
:=\frac{\int_K\phi(x)S_{\lambda+1}(g(x))\,d\rho(x)}{D(g)},
\]
and
\[
B_g(h)
:=\frac{
 \int_K\int_K h(x,y)
 S_{\lambda+1/2}(g(x))S_{\lambda+1/2}(g(y))
 \,d\rho(y)\,d\rho(x)}
 {D(g)^2}.
\]

Thus \(T_g(\phi)=\langle\phi t\rangle_g\). The bilocal API should accept a general continuous \(h:K\times K\to\mathbb R\), unless existing `compactQ`/`bilocalC` already provide that generality.

Set
\[
F_g=\langle f\rangle_g,\qquad c_\Delta(x)=\mathcal C(x,x),
\qquad h_f(x,y)=\mathcal C(x,y)f(x).
\]
Define the response functional
\[
\boxed{
H_f(g)=\frac{\beta^2}{2}\left[
T_g(fc_\Delta)-F_gT_g(c_\Delta)
-2\bigl(B_g(h_f)-F_gB_g(\mathcal C)\bigr)
\right].
}
\]

The paper-facing theorem should be
\[
\boxed{
\mathbb E\langle f\rangle_G-\frac{\int_Kf\,d\rho}{\rho(K)}
=
\int_0^1\mathbb E H_f(\sqrt{s}G)\,ds.
}
\]

**Present this as the principal theorem, not merely the derivative identity.** It directly compares the averaged posterior mean with its zero-field base mean. The derivative is the mechanism.

### Lean target shape

Here is a literal, small path wrapper; `F` and `H` below are the fixed-\(\rho,\lambda,\beta,f,\mathcal C\) functionals above.

```lean
def gaussianScaleAverage
    {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
    (P : Measure Ω) (G : Ω → C(K, ℝ))
    (F : C(K, ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, F (Real.sqrt s • G ω) ∂P
```

The derivative conclusion has type:

```lean
∀ s : ℝ, 0 < s →
  HasDerivAt
    (gaussianScaleAverage P G F)
    (gaussianScaleAverage P G H s)
    s
```

The compact theorem’s conclusion has type:

```lean
gaussianScaleAverage P G F 1
    - (∫ x, f x ∂ρ) / (ρ Set.univ).toReal
  =
    ∫ s in (0 : ℝ)..1,
      gaussianScaleAverage P G H s
```

These are interface sketches, not claims about existing repo identifiers. Put the established positivity, field, and continuity hypotheses in the theorem binders.

### The key domination is cheaper than inverse-moment machinery

Let \(M=\|f\|_\infty\), \(C_*=\|\mathcal C\|_\infty\). Positivity and Cauchy–Schwarz for the normalised radial integrals give
\[
|H_f(g)|
\le 3\beta^2MC_*\langle t\rangle_g
\le
3\beta^2MC_*
\left(\frac{2\lambda}{\beta}+\frac{\|g\|^2}{4}\right).
\]

Indeed:

* the centred \(T\)-term costs at most \(2MC_*\langle t\rangle_g\);
* the centred bilocal term costs at most
  \(2MC_*\langle\sqrt t\rangle_g^2
  \le2MC_*\langle t\rangle_g\);
* its coefficient is \(2\).

Therefore, uniformly for \(s\in[0,1]\),
\[
|H_f(\sqrt{s}G)|
\le
3\beta^2MC_*
\left(\frac{2\lambda}{\beta}+\frac{\|G\|^2}{4}\right).
\]

**This uses exactly the field’s landed second-moment hypothesis.** Use it for the compact quantisation limit rather than carrying high inverse-evidence moments through that proof.

### Endpoint handling

Do not differentiate \(\sqrt{s}\) at zero.

1. Prove the finite derivative for \(s>0\).
2. Integrate on \([\delta,1]\).
3. Pass \(\delta\downarrow0\), using continuity of \(A\) and the uniform response bound.
4. Pass finite bases to the compact base.

A compact derivative theorem is then a reasonable later corollary once continuity of the averaged response is packaged. It need not be part of this sprint.

---

## 3. Can the landed Stein identity avoid second derivatives?

**Not in its currently specialised form.**

The chain rule gives
\[
\frac d{ds}F(\sqrt{s}G)
=
\frac{\beta}{2\sqrt{s}}
\sum_jG_j\,W_j(\sqrt{s}G)
       \bigl(f_j-F(\sqrt{s}G)\bigr).
\]
Stein must therefore be applied to
\[
g\longmapsto W_j(g)(f_j-F(g)),
\]
not just to \(g\longmapsto F(g)\).

Your landed `integral_eval_mul_compactAvg` handles a deterministic observable \(f\). It does not permit a field-dependent posterior weight to be inserted into \(f\). Moving such a factor outside the Gaussian expectation would be invalid.

So the useful simplification is:

> Use general finite-dimensional Stein on the explicit first-derivative expression; avoid constructing a Hessian object.

This is still the second-derivative calculation mathematically, but a substantially smaller Lean interface.

Differentiating the existing log-evidence interpolation in a source parameter is an elegant paper derivation. In Lean it introduces a new interchange of source differentiation and the interpolation integral, so I would not select it as the implementation route without an already-uniform source-parameter API.

---

## 4. Joint Gibbs measures: the clean formulation, but not the dependency

For Lean, prefer a measure on **`K × ℝ` supported on positive \(t\)** over a measure on `K × Set.Ioi (0 : ℝ)`.

Let \(q_\lambda(u,t)\) denote the exact radial density used to define \(S_\lambda(u)\). In the usual convention,
\[
q_\lambda(u,t)=t^{\lambda-1}e^{-\beta t+\beta u\sqrt t}
\quad(t>0).
\]
Use the landed convention verbatim, including any normalising constant.

Define
\[
\mu_g
=
\left(\rho\otimes(\mathrm{volume}|_{(0,\infty)})\right)
.\mathrm{withDensity}
\left((x,t)\mapsto
 \operatorname{ofReal}\frac{q_\lambda(g(x),t)}{D(g)}
\right).
\]

The Lean constructor shape is:

```lean
(ρ.prod (volume.restrict (Set.Ioi (0 : ℝ)))).withDensity
  (fun z => ENNReal.ofReal (radialDensity (g z.1) z.2 / D g))
```

This avoids positive-subtype coercions throughout the replica formulas.

### Minimal useful API

Prove, in this order:

1. `IsProbabilityMeasure (jointGibbs ... g)`;
2. observable reduction:
   \[
   \int\phi(x)\,d\mu_g=\langle\phi\rangle_g;
   \]
3. half-moment reduction:
   \[
   \int\phi(x)\sqrt t\,d\mu_g=\langle\phi\rangle_g^{1/2};
   \]
4. first-moment reduction:
   \[
   \int\phi(x)t\,d\mu_g=T_g(\phi);
   \]
5. product reduction:
   \[
   \int h(x_1,x_2)\sqrt{t_1}\sqrt{t_2}\,
       d(\mu_g\otimes\mu_g)=B_g(h).
   \]

Do **not** initially construct a probability kernel \(g\mapsto\mu_g\), samples from that kernel, or a general replica hierarchy. Fixed-\(g\) measures and reduction lemmas suffice.

It is not essentially free: density measurability, total mass, signed-integral reductions, and product-integrability certificates remain real work. For (I), **stay with the \(S_\nu\) moments internally** and build this interpretation afterwards.

### Why (I) really is three-replica calculus

With three independent replicas under \(\mu_g^{\otimes3}\),
\[
\boxed{
H_f(g)=\frac{\beta^2}{2}
\mathbb E_{\mu_g^{\otimes3}}
\left[
(f(x_1)-f(x_2))
\left(
t_1\mathcal C(x_1,x_1)
-2\sqrt{t_1}\sqrt{t_3}\mathcal C(x_1,x_3)
\right)
\right].
}
\]

This is the clean narrative formula. Prove the moment version first; later prove this equality by the five reduction lemmas.

---

## 5. Candidate (VI): a cheap bridge exists, conditionally

The landed convergence of averaged bounded posterior means does **not** imply convergence after multiplying by an unbounded field evaluation.

A sufficient package is:
\[
(X_N,Y_N)\Rightarrow(X,Y),\qquad
|Y_N|\le M,
\]
together with uniform integrability of \(X_N\). Then \(X_NY_N\) is uniformly integrable and
\[
\mathbb E[X_NY_N]\longrightarrow\mathbb E[XY].
\]

A uniform \(L^p\) bound on \(X_N\), for any \(p>1\), is a convenient sufficient condition.

For your intended application:
\[
X_N=G_N(x_0),\qquad Y_N=E_N[f],\qquad
(X,Y)=(G(x_0),\langle f\rangle_G).
\]
Stein then identifies the limiting expectation.

One particularly cheap route would be:

* \(G_N\Rightarrow G\) in \(C(K,\mathbb R)\);
* \(E_N[f]-F(G_N)\to0\) in probability;
* \(|E_N[f]|,|F(G_N)|\le M\);
* \(\sup_N\mathbb E|G_N(x_0)|^2<\infty\).

Boundedness makes the posterior approximation error tend to zero in \(L^2\); Cauchy–Schwarz removes its product with \(G_N(x_0)\). Joint convergence for \((G_N(x_0),F(G_N))\) comes from continuity.

**This is not averaging asymptotic remainders in disguise.** It is a leading-order convergence-plus-uniform-integrability theorem. But if only `tendsto_integral_expectation` is available, the missing joint convergence is substantive.

I would do a short inventory before starting (I), not open a new empirical proof campaign.

---

## 6. Citation and naming audit

Nothing listed looks mathematically inconsistent. These distinctions should be explicit in the notes.

### A. Half-moment brackets are not a new normalised posterior

Neither
\[
\sum_jW_j=\langle\sqrt t\rangle_g
\quad\text{nor}\quad
\sum_jR_j=\langle t\rangle_g
\]
is generally \(1\).

Call these **radial-moment-weighted posterior integrals**, not posterior expectations under a shifted-\(\lambda\) Gibbs measure. Their denominator remains \(D_\lambda\).

Names such as `compactHalfMoment` and `compactFirstRadialMoment` are less ambiguous than names suggesting probability averages.

### B. Quenched second derivative is an expected conditional variance

\[
\Psi''(0)=\mathbb E\,\mathrm{Var}_{\mu_G}(f).
\]
It is neither
\(\mathrm{Var}_G(\langle f\rangle_G)\)
nor the variance under the annealed mixture. Likewise, future \(\mathbb E\kappa_r^{\mu_G}(f)\) are not cumulants of that mixture.

### C. The empirical big-O theorem is pathwise

State prominently:

> Fixed sample; implicit constants may depend on that sample and on truncation order.

Do not cite it as an annealed expansion without separate domination of its remainders.

### D. “Banach Stein” must retain its scope

Candidate (V) would prove, for this posterior functional,
\[
DF(g)[h]
=\beta\left(
\langle fh\rangle_g^{1/2}
-F_g\langle h\rangle_g^{1/2}
\right).
\]
The landed identity then becomes
\[
\mathbb E[G(x_0)F(G)]
=\mathbb E[DF(G)[\mathcal C(x_0,\cdot)]].
\]

That is a Banach-form statement **for posterior averages**, not yet a general Gaussian integration-by-parts theorem for arbitrary Fréchet-differentiable functionals.

### E. Record centring and factorial conventions

* `GaussianField` here is centred; say so when presenting Stein.
* Keep source derivatives \(\kappa_r\) distinct from ordinary source-series coefficients \(\kappa_r/r!\).
* For (III), the stated radius requires \(M>0\); \(M=0\) is the trivial entire case.

---

**Recommended stopping point:** one compact theorem expressing the averaged posterior-mean shift as an integral of `compactMeanResponse`, backed by finite coordinate Stein and a quadratic domination lemma. That is a coherent new paper result—and gives (II) something genuinely useful to package.