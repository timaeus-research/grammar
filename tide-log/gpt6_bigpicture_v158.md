## Recommendation

I would separate **new mathematical interfaces** from **completion of the existing stochastic interface**.

**Priority ranking:** **1 → 3 → 6 → 2 → 5 → 4**.

- **1** supplies a genuinely useful intrinsic characterization of *all* coefficients.
- **3** completes a central application without requiring new analysis.
- **6** distinguishes distributional conclusions from expectation-level conclusions, and gives useful new formulas and counterexamples.
- **2** is valuable, but needs careful normalization: lower-order pieces are not individually intrinsic.
- **5** is a small, worthwhile infrastructure patch; do it opportunistically before anything that needs it.
- **4** should stop at continuous descent, if needed. A new global functional CLT is not justified by the current goals.

The Lean declarations below are **schematic interfaces**, not claims about existing identifiers or exact Mathlib argument order.

---

# 1. Fluctuation zeta: use complex Mellin regularization

**Yes: your proposed statement is the right one. Use complex \(s\).** Real-variable Laurent data would save little and leave you with a less useful theorem.

## The main object

For a finite cutoff polynomial
\[
P_U(N)=\sum_{\mu<U}\sum_q c_{\mu,q}N^{-\mu}(\log N)^q,
\]
define
\[
R_U(N)=E(N)-\mathbf1_{[1,\infty)}(N)P_U(N),
\qquad
M_U(s)=\operatorname{mellin}(R_U)(s).
\]

The principal theorem should package:

1. Mellin convergence of \(R_U\) on \(0<\Re s<U\);
2. complex differentiability there;
3. agreement with the original transform wherever all unsubtracted terms converge;
4. compatibility between different cutoffs.

A useful shape is:

```lean
theorem cutoffExpansion_mellin_regularization
    (hsmall : IsBigO (nhdsWithin 0 (Ioi 0)) E (fun _ => 1))
    (hexp : HasCutoffExpansion E c Q U D)
    (hmeas : AEStronglyMeasurable E ...) :
    MellinRegularizationSpec E c Q U
```

Here `MellinRegularizationSpec` should contain the concrete formulas, rather than an abstract assertion of continuation.

On the initial strip,
\[
\operatorname{mellin}E(s)
 =
 M_U(s)+
 \sum_{\mu<U,q}c_{\mu,q}\frac{q!}{(\mu-s)^{q+1}}.
\]

A remainder \(O(N^{-U}(\log N)^D)\) is sufficient: at every point with \(\Re s<U\), absorb the logarithm into an arbitrarily small positive power. Do not require an unnecessarily stronger \(O(N^{-U})\) remainder.

### The elementary Mellin lemma

Prove once:
\[
\int_1^\infty N^{s-\mu-1}(\log N)^q\,dN
=\frac{q!}{(\mu-s)^{q+1}},
\qquad \Re s<\mu.
\]

The substitution \(N=e^x\) reduces this to a complex Laplace–Gamma integral. This is the only special-function computation needed for the principal-parts interface.

## Cutoff compatibility is important

For \(U<V\),
\[
M_U(s)
=
M_V(s)+\sum_{U\leq\mu<V,q}
 c_{\mu,q}\frac{q!}{(\mu-s)^{q+1}},
\qquad 0<\Re s<U.
\]

Consequently,
\[
F_U(s):=M_U(s)+\sum_{\mu<U,q}
c_{\mu,q}\frac{q!}{(\mu-s)^{q+1}}
\]
and \(F_V\) agree on their common pole-free domain.

This gives a coherent continuation to the right half-plane as \(U\to\infty\), without a meromorphic-function object. It does **not** claim continuation across \(\Re s=0\).

## Principal-parts uniqueness

This is a worthwhile addition to `IsFrozenCoeff.unique`, but it is a different uniqueness theorem:

> A function represented near \(\mu\) by a holomorphic remainder plus a finite principal part has uniquely determined principal-part coefficients.

Prove it by multiplying by the maximal pole power, taking a limit, and descending in pole order. No identity theorem or meromorphic API is necessary.

With the convention using \((s-\mu)^{-j}\),
\[
[(s-\mu)^{-(q+1)}]F
=(-1)^{q+1}q!\,c_{\mu,q}.
\]

It then follows that the highest nonzero logarithmic order at \(\mu\) is exactly one less than the pole order. This is the clean intrinsic “lower-log-order” statement available immediately.

## Fubini identity: a separate theorem

Define, for \(\Re s>0\),
\[
S_s(a)=\int_0^\infty t^{s-1}e^{-t+a\sqrt t}\,dt.
\]

For real \(H\), nonnegative \(K\), and \(\sigma=\Re s\), the appropriate absolute-integrability hypothesis is
\[
\int_W |\phi|K^{-\sigma}
 S_\sigma(H/\sqrt K)\,d\nu_\chi<\infty,
\]
together with \(K>0\) a.e. on the relevant support. Then
\[
\operatorname{mellin}E(s)
=
\int_W \phi K^{-s}S_s(H/\sqrt K)\,d\nu_\chi.
\]

**Do not infer this absolute Fubini hypothesis merely from a cutoff expansion of a signed observable.** Use a positive dominating observable/evidence estimate.

### Do not attempt

- A general meromorphic-continuation library.
- Continuation across \(s=0\).
- A real-only replacement based on elaborate `iteratedDeriv` bookkeeping.
- Fubini from cancellation-based asymptotics of \(E_\phi\).

---

# 2. Lower logarithmic orders: intrinsic principal parts, noncanonical conormal summands

The key distinction is:

> The coefficient is intrinsic. A decomposition of that coefficient into finite-part integrals and index derivatives generally is not.

A coordinate change changes finite parts by terms supported on deeper strata. Those changes cancel against changes in the other summands.

## The correct general formula

Fix \(\mu\). Suppose a normalized conormal presentation gives, locally in \(s\),
\[
Z(s)=H(s)+\sum_{j=1}^{c}\frac{B_j(s)}{(\mu-s)^j},
\]
with \(H,B_j\) holomorphic near \(\mu\). Then
\[
\boxed{
c_{\mu,q}
=
\frac1{q!}
\sum_{j=q+1}^{c}
\frac{(-1)^{j-q-1}}{(j-q-1)!}
B_j^{(j-q-1)}(\mu).
}
\]

In particular,
\[
c_{\mu,c-1}=\frac{B_c(\mu)}{(c-1)!},
\]
and
\[
\boxed{
c_{\mu,c-2}
=
\frac{B_{c-1}(\mu)-B_c'(\mu)}{(c-2)!}.
}
\]

This is the sharp “two-term” statement. The second term differentiates the **whole deepest-stratum numerator family**, not automatically just \(S_s\). Whether the remaining geometric factors are independent of \(s\) depends on the chosen conormal normalization.

### Nested resonances

Your proposed \(\Phi_{J,\alpha}\) need not be holomorphic at \(\mu\): its tangential integral can have further poles. Therefore:

- first regularize tangentially and account for deeper resonances;
- then collect a holomorphic-numerator presentation;
- only then apply the displayed derivative formula.

Simply taking derivatives of an unnormalized `FP Φ` risks double counting deeper faces.

## What to say about \(\mathcal T^U_{\mu,q}\) and \(\mathcal I_{c+1}\)

I would not assert an exact ideal-factorization theorem without inspecting the paper’s precise definitions and normalization. The information in the question does not determine those conventions.

The mathematically safe target is:

> Under the conormal presentation and its stated depth-\(c\) truncation/vanishing hypothesis, identify \(B_c\) and \(B_{c-1}\), and prove that  
> \((B_{c-1}(\mu)-B_c'(\mu))/(c-2)!\) equals the already-defined intrinsic coefficient.

In particular, **do not infer that the lower coefficient descends through the same quotient as the top residue pairing**. The derivative and finite-part contribution are exactly what can retain additional normal information.

Likewise, vanishing of \(B_c(\mu)\) does not imply vanishing of \(B_c'(\mu)\). A hypothesis killing the deepest contribution must kill the relevant family/jet, not only its value at \(\mu\).

## Explicit two-dimensional anchor

Assume \(k_1,k_2>0\), \(\mu>0\), and enough smoothness. Put
\[
A_s(x,y)=\eta(x,y)S_s(\zeta(x,y)),
\qquad
\alpha_i=2k_i\mu-h_i-1.
\]

Direction \(i\) is resonant if \(\alpha_i\in\mathbb N\). For a resonant direction define
\[
D_i f=\frac{\partial_i^{\alpha_i}f|_{x_i=0}}{\alpha_i!}.
\]

Let \(\operatorname{FP}_i^\mu\) denote the constant term at \(s=\mu\) of
\[
f\longmapsto\int_0^1 x_i^{h_i-2k_i s}f(x_i)\,dx_i,
\]
with \(f\) held fixed when extracting that constant term.

For a resonant direction, explicitly,
\[
\operatorname{FP}_i^\mu f
=
\int_0^1
\frac{f(x)-\sum_{a=0}^{\alpha_i}f^{(a)}(0)x^a/a!}
{x^{\alpha_i+1}}\,dx
+
\sum_{a=0}^{\alpha_i-1}
\frac{f^{(a)}(0)/a!}{a-\alpha_i}.
\]

If both directions resonate, then
\[
\boxed{
c_{\mu,1}=\frac{D_1D_2A_\mu}{4k_1k_2},
}
\]
and
\[
\boxed{
c_{\mu,0}
=
\frac{D_1\operatorname{FP}_2^\mu A_\mu}{2k_1}
+
\frac{\operatorname{FP}_1^\mu D_2 A_\mu}{2k_2}
-
\frac{D_1D_2(\partial_s A_s|_{s=\mu})}{4k_1k_2}.
}
\]

Here
\[
\partial_s A_s|_\mu
=
\eta\int_0^\infty
t^{\mu-1}\log t\,e^{-t+\zeta\sqrt t}\,dt,
\]
so it is the negative of the corresponding first `mellinMom` log moment.

If only direction 1 resonates,
\[
c_{\mu,0}=\frac{D_1\operatorname{FP}_2^\mu A_\mu}{2k_1},
\qquad c_{\mu,1}=0,
\]
where the nonresonant finite part means the regularized value of the tangential family at \(\mu\). Exchange indices for the other case. If neither resonates, both coefficients vanish.

As a sign check, for \(h=(0,0)\), \(k=(1,1)\), \(\eta=1\), \(\zeta=0\), \(\mu=1/2\),
\[
c_{\mu,1}=\Gamma(\mu)/4,\qquad
c_{\mu,0}=-\Gamma'(\mu)/4.
\]

### Worth proving

First prove the two-dimensional formula using your existing regularized face integrals. Then prove the holomorphic-numerator coefficient-extraction lemma. Only afterward package a global conormal theorem.

### Do not attempt

A canonical global “subleading residue measure.” The finite-part object is not generally a measure, and its separate summands depend on regularization choices.

---

# 3. Posterior quotients: rational-log blocks first

The right stopping point is **the general finite rational-log block theorem**, plus arbitrary finite inverse-log expansion of each block.

## Algebraic object

After factoring \(N^{-\lambda}\), put
\[
x=N^{-1/Q},\qquad L=\log N.
\]
Write the retained series as
\[
A(x,L)=\sum_i A_i(L)x^i,\qquad
B(x,L)=\sum_i B_i(L)x^i,
\]
where the \(A_i,B_i\) are polynomials.

The economical coefficient field is
\[
\mathbb R(L),
\]
implemented by `RatFunc ℝ`, with power series in \(x\) only if useful.

You do **not** initially need
`PowerSeries (LaurentSeries ℝ)`. That object is mathematically appropriate, but formal infinite-series evaluation is unnecessary work.

Define rational blocks recursively:
\[
R_0=A_0/B_0,
\qquad
R_j=\frac{A_j-\sum_{i=1}^j B_iR_{j-i}}{B_0}.
\]

Then prove the finite congruence
\[
B\sum_{j<J}R_jx^j-A\equiv0\pmod{x^J}.
\]

```lean
theorem quotientBlocks_mul_congr
    (hB₀ : B 0 ≠ 0) :
    TruncEq J
      (mulBlocks B (quotientBlocks A B))
      A
```

## Inverse logarithms within a block

At \(z=1/L=0\), every rational block has a Laurent expansion with finite principal part. If
\[
B_0(L)=L^{m-1}(b_0+b_1/L+\cdots),\qquad b_0\ne0,
\]
finite division in \(z\) gives any prescribed depth.

For the leading quotient block, if numerator and denominator both have degree at most \(m-1\),
\[
R_0(L)
=
\frac{a_0}{b_0}
+
\frac{a_1b_0-a_0b_1}{b_0^2L}
+O(L^{-2}).
\]

The general recurrence is just as useful as another named low-order correction theorem.

## The main trap: two incompatible error scales

A fixed inverse-log truncation of the leading block has error
\[
O((\log N)^{-J-1}),
\]
which dominates **every** \(N^{-\delta}\), \(\delta>0\).

Therefore you cannot:

1. replace every rational block by a fixed finite inverse-log expansion; and
2. retain the original polynomial-in-\(N^{-1/Q}\) remainder rate.

The correct interface provides two conclusions:

- **power accuracy:** retain rational-log blocks exactly;
- **log accuracy:** expand a specified block to arbitrary finite inverse-log depth, with its separate logarithmic error.

A genuine transseries statement should express this blockwise hierarchy, not flatten it into one erroneous remainder estimate.

## Probabilistic transfer

For a fixed finite cutoff, require:

- joint tightness/convergence of retained numerator and denominator coefficients;
- \(b_{0,n}\Rightarrow b_0\) with \(\mathbb P(b_0=0)=0\);
- the already-established expansion remainders.

Then inverse denominator factors are tight. No deterministic positive lower bound on \(b_0\) is needed.

This supports a reusable transfer theorem producing \(O_p\) or \(o_p\) errors at the corresponding deterministic scale. Tightness alone gives \(O_p\), not automatically \(o_p\).

### Do not attempt

- Division through ratios of Mellin transforms: Mellin transformation does not turn pointwise quotients into quotients.
- Hahn-series machinery.
- Evaluation of arbitrary formal Laurent series.
- Inferring an all-orders numerical approximation from fixed-depth inverse-log truncations.

---

# 4. The Gaussian field downstairs: continuous descent, not another CLT

There is a cheaper option between (a) and (b).

## Start with the existing joint chart law

Let \(G^\alpha\) be the jointly defined limiting chart root fields and form
\[
Y^\alpha=u^{k_\alpha}G^\alpha.
\]

The finite-\(n\) weighted chart fields satisfy:

1. overlap consistency on the resolution;
2. equality at pairs of resolution points with the same image downstairs.

These are **closed conditions** in a product of spaces with continuous evaluation maps. Hence they pass to a joint weak limit.

This requires genuinely joint convergence across the relevant charts. Marginal chart convergence is insufficient.

## Glue, then descend

Suppose the relevant compact resolution domain \(U\) maps properly and surjectively to a compact Hausdorff parameter domain \(W\). Then
\[
g^*:C(W)\longrightarrow C(U)
\]
is an isometric embedding whose image is exactly the closed subspace of fiber-constant functions.

Thus a fiber-constant \(C(U)\)-valued random limit descends through a continuous inverse on that closed subspace.

A useful theorem is:

```lean
theorem gaussianLimit_descends_of_fiberCompatible
    (hg : ContinuousSurjectiveQuotientMap g)
    (hcompat : ∀ᵐ ω, FiberConstant g (GU ω))
    (hGauss : IsGaussianRandomElement GU) :
    ∃ G : Ω → C(W, ℝ),
      Measurable G ∧
      IsGaussianRandomElement G ∧
      (∀ᵐ ω, GU ω = (G ω).comp g)
```

The exact Gaussian predicate may initially be finite-dimensional: every finite vector of evaluations is centered Gaussian.

No new functional CLT is needed if the chart topology already contains continuous fields.

## Important limitation

Overlap compatibility alone gives a field on the resolution. It does **not** imply descent: distinct exceptional points in one fiber need not lie in a common chart overlap.

Also, continuous descent does not give \(C^R\) regularity downstairs.

## Minimal residue-reweighting theorem

You do not need descent at all to prove the pathwise residue formula. On the resolution,
\[
\frac{S_\mu(G^\alpha)}{\Gamma(\mu)}
=
\mathbb E_{T\sim\Gamma(\mu,1)}
     e^{G^\alpha\sqrt T}.
\]

Here the expectation is over an auxiliary \(T\), with the Gaussian field held fixed.

This distinction matters:

- \(\mathbb E_T e^{G^\alpha\sqrt T}\) is a **random residue weight**;
- \(\mathbb E_{G,T} e^{G^\alpha\sqrt T}\) is an **annealed weight**, requiring the moment hypotheses in item 6.

Moreover, \(G/\sqrt K\) need not descend continuously across \(K=0\), even when \(G\) does. The exceptional divisor retains directional root-field data.

### Recommendation

Keep chart/resolution root fields as the primary object. Add continuous downstairs descent only when a theorem actually needs it. Do not construct a global \(C^R\) CLT.

---

# 5. Joint law of the truncation vector: mechanical, for fixed \(R\)

Yes. The correct generalization is a finite-product continuous mapping theorem:

```lean
theorem jointLaw_of_continuous_closedJetFunctionals
    [Fintype ι]
    (hZ : TendstoInDistribution Zₙ G)
    (F : ι → ClosedJets → ℝ)
    (hF : ∀ i, Continuous (F i)) :
    TendstoInDistribution
      (fun n ω i => F i (Zₙ n ω))
      (fun ω i => F i (G ω))
```

Instantiate one coordinate with the full coefficient functional and the others with `genTermOnClosedJets`.

### Traps

1. **Fixed \(R\), not \(R_n\to\infty\).** Increasing dimension needs a sequence-space topology or a converging-together argument.
2. Every functional must act on the **same ambient jet space**. Different queries may require different derivative depths; lift everything to their common maximum.
3. The full coefficient functional must actually be continuous. Uniform convergence on jet balls is enough, using local boundedness of convergent sequences.
4. Joint convergence cannot be reconstructed from marginal convergence.

The variable-truncation result follows separately from your truncation-in-probability theorem plus the joint law, using a converging-together lemma.

---

# 6. Moments: prove an integrable-envelope interface, then a subcritical Gaussian corollary

There are three logically separate statements:

1. limit coefficient integrability;
2. exchange of expectation and the generating series;
3. moment convergence from finite \(n\).

Only the first two are addressed by Gaussian limit estimates. The third additionally needs uniform integrability of the finite-\(n\) coefficients.

## Minimal robust theorem

For a fixed finite family of coefficient queries, prove an envelope controlling both the coefficient and the **sum of absolute generating terms**.

A usable analytic bound has the form
\[
|C(G)|+\sum_r |a_r(G)|
\leq
C(1+\|G\|_{C^r})^M
 \exp\!\left((1/4+\varepsilon)\|G\|_{C^0}^2\right),
\]
with the right-hand side adjusted to the actual derivative seminorms in your implementation.

The most immediately reusable probabilistic hypothesis is simply integrability of that envelope. Then:

```lean
theorem integral_frozenCoeff_eq_tsum_of_integrableEnvelope
    (hgen : ∀ᵐ ω, HasSum (genTerm G ω) (coeff G ω))
    (hdom : ∀ᵐ ω, ∑' r, ‖genTerm G ω r‖ ≤ D ω)
    (hD : Integrable D) :
    Integrable (coeff G) ∧
    (∫ ω, coeff G ω) = ∑' r, ∫ ω, genTerm G ω r
```

This deliberately avoids deriving integrability from the existing jet-ball tail bound: its random constant \(C_B\) need not be integrable.

## A sharper covariance condition

For smooth Gaussian root fields on finitely many compact charts, a natural sufficient condition is
\[
\boxed{\sup_{\alpha,u}\operatorname{Var}(G^\alpha(u))\leq 2-\delta}
\]
for some \(\delta>0\), together with:

- enough almost-sure spatial regularity for the coefficient formula;
- jointly Gaussian derivative evaluations;
- uniform bounds on the variances of the finitely many derivatives used.

This is sharper than requiring a strong exponential moment of the entire \(C^r\)-norm.

### Route

Express finite parts by Taylor-remainder integrals. Spatial derivatives of \(e^{\sqrt tG}\) are polynomials in Gaussian derivative jets times \(e^{\sqrt tG}\). Gaussian tilting, or Hölder with a little variance slack, gives
\[
\mathbb E\!\left[
 |P(\text{jets},\sqrt t)|e^{\sqrt tG(u)}
\right]
\leq C(1+t)^M e^{a t},
\qquad a<1.
\]

The remaining \(e^{-t}\) yields integrability, including the finitely many \(\log t\) factors. The same route with \(e^{\sqrt t|G|}\) controls the absolute generating series.

This requires opening the finite-part formula enough to expose a **bounded finite-order integral representation**. Pointwise variance control alone is not a black-box Fernique theorem for arbitrary jet-norm functionals.

For the empirical process,
\[
\operatorname{Var}(G^\alpha)
=
\left(\frac{\operatorname{Var}(f(X,w))}{K(w)}\right)\circ g_\alpha
\]
away from the divisor. Thus your proposed covariance ratio is exactly the right subcritical quantity, provided its resolved extension and required derivative covariance bounds are available.

## Wick formula

Under the absolute-summability hypotheses,
\[
\mathbb E C_{\mu,q}[G,\phi]
=
\sum_r\frac1{r!}
 \mathbb E C^{\rm pop}_{\mu+r/2,q}[\phi G^r].
\]

If the population coefficient functional can also be interchanged with expectation, and \(V(w)=\operatorname{Var}(G(w))\), then centered Gaussian Wick moments give
\[
\boxed{
\mathbb E C_{\mu,q}[G,\phi]
=
\sum_{j\geq0}
\frac1{2^j j!}
C^{\rm pop}_{\mu+j,q}[\phi V^j].
}
\]

This can be stated chartwise without first constructing a global field.

At top log order the particularly clean corollary is the residue-density replacement
\[
\mathbb E_G\frac{S_\mu(G(u))}{\Gamma(\mu)}
=
\left(1-\frac{v(u)}2\right)^{-\mu}.
\]

## Counterexample: formulate it in extended nonnegative integrals

For \(Z\sim N(0,v)\), \(\mu>0\),
\[
\mathbb E S_\mu(Z)
=
\begin{cases}
\Gamma(\mu)(1-v/2)^{-\mu},&v<2,\\
+\infty,&v\geq2.
\end{cases}
\]

Tonelli proves this directly:
\[
\mathbb E S_\mu(Z)
=
\int_0^\infty t^{\mu-1}e^{-(1-v/2)t}\,dt.
\]

For \(\mu=1/2\),
\[
S_{1/2}(Z)=2\int_0^\infty e^{-t^2+tZ}\,dt.
\]

**Lean trap:** a nonintegrable real-valued Bochner integral does not denote \(+\infty\). State:

- the `lintegral` is `∞`;
- consequently `¬ Integrable ...`.

Do not state that a real expectation “equals infinity.”

### Do not attempt

- Moment convergence from convergence in law alone.
- A necessary-and-sufficient covariance criterion for arbitrary signed lower coefficients.
- A global Banach-space Fernique theorem merely to prove these finite-order coefficient estimates.

---

# First three concrete statements

Following the mathematical priority ranking, I would commission these:

### 1. Mellin regularization with cutoff compatibility

```lean
theorem hasCutoffExpansion_mellinRegularization :
  HasCutoffExpansion E c Q U D →
  BoundedNearZero E →
  MellinRegularizationSpec E c Q U
```

Include differentiability on the open strip and the finite rational principal-part identity. Add cutoff compatibility immediately afterward.

### 2. Finite rational-log quotient recursion

```lean
theorem quotientBlocks_spec
    (hB₀ : B 0 ≠ 0) :
    ∀ J, TruncEq J
      (mulBlocks B (quotientBlocks A B))
      A
```

Then attach deterministic evaluation estimates and the existing probabilistic denominator machinery. Preserve rational blocks for power-rate accuracy.

### 3. Expectation–generating-series interchange under an integrable envelope

```lean
theorem integral_coeff_eq_tsum_integral_genTerm
    (hgen : ...)
    (habs : Integrable (fun ω => ∑' r, ‖genTerm ω r‖)) :
    Integrable coeff ∧
    integral coeff = ∑' r, integral (genTerm · r)
```

Follow this with the scalar Gaussian \(v=2\) threshold theorem, then the chartwise subcritical covariance criterion.

**Small parallel patch:** generalize the closed-jet continuous mapping theorem in item 5 now. It should not become a separate research project, and it will simplify nearly every subsequent joint-law statement.