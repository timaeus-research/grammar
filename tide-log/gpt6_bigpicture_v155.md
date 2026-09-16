## Recommendation

Use **(b) as the all-orders mathematical formulation, (c) as its intrinsic specification and first Lean interface**. Treat (a) as a later, choice-dependent description of the resulting functional—not as its definition.

There is a useful intermediate formulation that makes (b) quite concrete:

> **The empirical coefficients are the Laurent coefficients of a population local-zeta distribution evaluated on a holomorphic family of amplitudes determined by the standardised field.**

This both explains the lower logarithmic orders and gives a route from your existing population residue/finite-part machinery to the empirical fluctuation tree.

Two qualifications are fundamental:

1. The globally defined deformation in the exponential is
   \[
   H_n:=\sqrt n(K-K_n),
   \]
   whereas the standardised field is \(\psi_n=H_n/\sqrt K\), initially only off \(K^{-1}(0)\).
2. Higher “normal derivatives” are not, without additional choices, canonical sections of the symmetric conormal bundles. The intrinsic object is a **filtered jet object**; symmetric conormal tensors describe its associated graded.

I am treating the reported theorem interfaces as available; the proposed Lean declarations below are design sketches, not claims about existing declaration names.

---

# 1. The intrinsic coefficient object

## 1.1 Start with the scalar functional

For a fixed admissible deformation \(H\), define
\[
Z_H(N;\varphi)
  :=\int_W \varphi\,e^{-NK+\sqrt N H}\,d\nu_\chi.
\]

Your frozen-field uniqueness theorem already specifies intrinsic coefficients
\[
\mathcal C_{\mu,q}[\varphi;H]
\]
through the cutoff expansion of this integral. They are:

- linear in the observable \(\varphi\);
- generally nonlinear in \(H\);
- independent of a compatible atlas, on a common comparison window/lattice;
- dependent on \((\nu_\chi,K,H)\), rather than on the chosen chart representatives.

This is already a genuine global formulation. It is not merely a fallback. What it does **not** yet supply is the requested geometric computation of the functional.

For \(\psi\) defined off the zero set, write
\[
\mathcal T^{\mathrm{emp}}_{\mu,q}[\varphi;\psi]
  :=\mathcal C_{\mu,q}[\varphi;\sqrt K\,\psi],
\]
provided the product has the required interpretation and compatible resolved extensions.

The observable should be an explicit argument. Do not hide it permanently in the measure: linearity and comparison of test observables will matter later.

## 1.2 A concrete all-orders residue formulation

Define, initially for \(\Re s>0\),
\[
B(s,z):=\int_0^\infty t^{s-1}e^{-t+\sqrt t\,z}\,dt.
\]

For bounded real \(z\), this is holomorphic in \(s\) on that half-plane, and
\[
B(s,0)=\Gamma(s).
\]

On an appropriate initial convergence strip, the substitution \(t=NK(w)\) gives
\[
\int_0^\infty N^{s-1}Z_H(N;\varphi)\,dN
=
\int_W \varphi\,K^{-s}B(s,\psi)\,d\nu_\chi,
\qquad H=\sqrt K\,\psi.
\]

Here one needs the usual integrability assumptions and either zero mass on \(K^{-1}(0)\), or a separate treatment of that mass.

Thus introduce the empirical zeta family
\[
\mathscr Z_{\varphi,\psi}(s)
  :=\int_W \varphi\,K^{-s}B(s,\psi)\,d\nu_\chi.
\]

Although this expression is written on \(W\setminus K^{-1}(0)\), its meromorphic continuation can be constructed on a compatible resolution. The field need only have the requisite smooth extensions there, possibly chamberwise.

The coefficient convention is particularly clean in powers of \(\mu-s\):
\[
\mathscr Z_{\varphi,\psi}(s)
 \sim
 \sum_q \frac{q!\,\mathcal T^{\mathrm{emp}}_{\mu,q}[\varphi;\psi]}
                  {(\mu-s)^{q+1}}
 \quad\text{near }s=\mu.
\]

Indeed,
\[
\int_1^\infty N^{s-\mu-1}(\log N)^q\,dN
  =\frac{q!}{(\mu-s)^{q+1}}.
\]

**Check the exact relationship between \(B(\mu,z)\) and grammar’s \(S_\mu(z)\).** It should recover the existing top-order special-function weight, but the gamma factors and sign conventions should be proved rather than inferred from notation.

## 1.3 This explains every lower logarithmic order

Let the **raw population zeta distribution**, without a gamma factor included, have local Laurent expansion
\[
\mathscr R(s)
=
\sum_{j=1}^{c}\frac{R_{\mu,j}}{(\mu-s)^j}
+\text{holomorphic}.
\]

These \(R_{\mu,j}\) are distributional functionals on resolved amplitudes. Evaluating on the \(s\)-dependent amplitude \(\varphi B(s,\psi)\) gives
\[
\boxed{
\mathcal T^{\mathrm{emp}}_{\mu,q}[\varphi;\psi]
=
\frac1{q!}
\sum_{j=q+1}^{c}
\frac{(-1)^{j-q-1}}{(j-q-1)!}
R_{\mu,j}
\!\left[
\varphi\,
\partial_s^{\,j-q-1}B(\mu,\psi)
\right].
}
\]

This formula is schematic only in the sense that your implementation must fix the resolved density, branch bookkeeping, and normalization of the population Laurent operators.

It gives a precise answer to the deeper-strata question:

- At \(q=c-1\), only the highest Laurent operator contributes:
  \[
  \frac1{(c-1)!}R_{\mu,c}[\varphi B(\mu,\psi)].
  \]
  This is the route to the existing weighted stratum measure/formula.
- At lower \(q\), **both lower Laurent operators and higher Laurent operators acting on spectral derivatives of the amplitude contribute**.
- The lower Laurent operators contain the residue/finite-part geometry. Deeper intersections therefore contribute to lower logarithmic powers; they do not belong exclusively to the highest power.

For example, for a double pole,
\[
\mathcal T^{\mathrm{emp}}_{\mu,1}
 =R_{\mu,2}[\varphi B(\mu,\psi)],
\]
while
\[
\mathcal T^{\mathrm{emp}}_{\mu,0}
 =R_{\mu,1}[\varphi B(\mu,\psi)]
  -R_{\mu,2}[\varphi\,\partial_s B(\mu,\psi)].
\]

That second term is important. “Apply the population stratum formula with a replaced amplitude” is sufficient at the top pole, but generally insufficient below it.

### Lean advantage

You need not prove a new Mellin inversion theorem.

Use the already proved frozen-field expansion. For a cutoff \(A>\mu\), its remainder gives a Mellin transform holomorphic on \(\Re s<A\). Comparing principal parts identifies the coefficients.

This requires a real-positive-parameter frozen expansion. If the available interface is only sequential in \(n\), expose the underlying real-parameter result or prove that extension first.

---

# 2. Why I would not start with fluctuation moment tensors

There are three separate difficulties with candidate (a).

## 2.1 Normal Taylor coefficients require a splitting

For a submanifold \(S\), the canonical objects are the filtration by its vanishing ideal and
\[
I_S^r/I_S^{r+1}\cong \operatorname{Sym}^rN^*S.
\]

But an arbitrary function does not canonically determine separate homogeneous normal Taylor components in every degree.

A tubular retraction, connection, or another splitting lets one write those components. Changing the splitting mixes degrees and can introduce tangential derivatives.

Likewise,
\[
J=\psi-\psi|_S
\]
is not a function on a neighbourhood until one chooses how to extend \(\psi|_S\) off \(S\).

Thus the paper’s tensor notation should be understood relative to whatever geometric choices support its normal-fibre construction, unless those choices have separately been shown to disappear.

## 2.2 The proposed tensor variance needs correction

If the factors being contracted are conormal derivatives of both the observable and the field, the moment object needs corresponding **normal**, not additional conormal, slots.

A term involving derivative orders \(r,\ell_1,\dots,\ell_p\) would naturally pair against something of type
\[
\operatorname{Sym}^r NS
\otimes
\operatorname{Sym}^{\ell_1}NS
\otimes\cdots\otimes
\operatorname{Sym}^{\ell_p}NS.
\]

Writing \((D_\perp J)^{\odot p}\) alone also obscures the higher derivative orders appearing in a Faà di Bruno/tree expansion.

## 2.3 Finite parts are not ordinary fibre moments

Below the top logarithmic order, finite-part distributions along the remaining divisor directions enter. A package of ordinary normal-fibre moments will not automatically capture them.

One can develop **renormalised, filtered fluctuation moments**, but that is a substantially larger construction.

**Recommendation:** first establish the intrinsic functional and its residue formula. Then derive a tensor/tree presentation after choosing a normal splitting, with a theorem that its total contraction equals the intrinsic functional. Do not require each individual tensor summand to be invariant.

---

# 3. The global sample field

## 3.1 Prove the identity—but keep both fields

The bridge should establish
\[
H_n\circ g_\alpha=u^{k_\alpha}\xi^\alpha_n
\]
on the whole cube, using the standard-form identity and the finite-sum algebra.

Then, off the divisor,
\[
\xi^\alpha_n
 =\frac{H_n\circ g_\alpha}{u^{k_\alpha}}.
\]

To conclude that this equals \(\psi_n\circ g_\alpha\), you also need
\[
\sqrt{K\circ g_\alpha}=u^{k_\alpha}.
\]

This holds on a nonnegative cube with the stated monomial standard form. On signed charts the formula is instead
\[
\psi_n\circ g_\alpha
 =\operatorname{sgn}(u^{k_\alpha})\,\xi^\alpha_n.
\]

That sign is structural, not cosmetic.

## 3.2 Do not claim descent across the divisor

The smooth chart quotient may extend across a resolved divisor while the standardised field has no continuous extension on the original \(W\).

Different exceptional points lying over the same point of \(W\) can encode different directional limits. Continuity or analyticity on the resolution does not force them to descend.

There are three sensible geometric settings:

1. **Positive/chamber charts:** the current cube presentation.
2. **The oriented real blow-up:** boundary defining functions are nonnegative, and the pulled-back standardised field can be smooth there.
3. **Signed-root data:** local signed square roots and their corresponding quotient fields, with sign transitions; where available, these can be packaged as root-line data.

For the bridge, (1) is enough initially. Do not build (2) or (3) merely to express a theorem you can already state.

## 3.3 What frozen-field invariance actually applies to

For each fixed \(n,\omega\), apply `aggCoeff_atlas_invariant` to
\[
H=H_n(\omega),
\]
not to \(\psi_n(\omega)\).

The exponent is
\[
-NK+\sqrt N\,H_n(\omega).
\]

At \(N=n\), this is the empirical exponent \(-nK_n\). The frozen theorem compares coefficient constructions for that particular field; it does **not** itself prove an asymptotic theorem along the changing sequence \(H_n\).

Your existing empirical remainder theorems supply that diagonal stochastic control.

## 3.4 Is the identity plus invariance enough?

For **pathwise atlas independence of the coefficient values**, essentially yes, after discharging:

- the same measure and observable insertion;
- frozen-field admissibility;
- sign/branch compatibility;
- a common cutoff and lattice;
- any simultaneous almost-sure event needed for the standard-form identities.

For a **random functional**
\[
\omega\longmapsto
\mathcal T^{\mathrm{emp}}_{\mu,q}[\varphi;\psi_n(\omega)],
\]
you additionally need measurability, usually inherited from a chosen chart coefficient formula.

For **modification independence**, not necessarily: you must verify that the frozen invariance interface really compares the two resolved presentations over the same base integral. If it only compares atlases on a fixed resolved object, that extension remains a separate theorem.

Finally, if \(\psi\) is specified only off the divisor, explain why its boundary choices cannot affect the integral and why compatible smooth chart extensions are unique. Nullity of the divisor for the measure and density of the chart complement are the relevant, distinct facts.

---

# 4. The stochastic limit object

## 4.1 The right geometric target

The natural target is a Gaussian random element in a space of **compatible resolved fields with sufficient regularity**. Its finite jets along strata are then derived objects.

For signed-root presentations it is a Gaussian section of the corresponding field bundle. For positive/chamber presentations it is a compatible Gaussian field on those chambers.

It is not generally just a Gaussian section of
\[
\bigoplus_r\operatorname{Sym}^rN^*S.
\]
That direct-sum description presupposes a splitting of the filtered jet object.

For normal crossings, the multi-filtration by divisor ideals is more informative than a single normal degree.

## 4.2 A base-space CLT is not automatically a jet CLT

Convergence in \(C(K)\) does not imply convergence of derivatives, nor continuity of finite-part functionals that require derivative bounds.

Moreover, the process intrinsically defined on \(W\setminus K^{-1}(0)\) need not extend continuously to the singular locus of \(W\). Its natural regular extension may live only on the resolved/chamber space.

The covariance off the zero set can be written intrinsically as
\[
\frac{\operatorname{Cov}(f(X,w),f(X,w'))}
     {\sqrt{K(w)}\sqrt{K(w')}}.
\]
Extending this into a sufficiently regular resolved Gaussian field is additional work, not a consequence of that formula alone.

## 4.3 What to formalise now

State the coordinate-free coefficient theorem **conditionally on the existing joint chart-jet convergence**.

Then prove:

- the deterministic coefficient map is intrinsic;
- it is continuous in the regularity topology used by the chart theorem;
- consequently its limiting law is intrinsic.

You can obtain atlas independence of the limiting coefficient law without constructing a coupled global Gaussian field: the same intrinsic prelimit random vector has at most one limiting distribution.

A later, modest geometric upgrade is to define the **closed compatibility subspace of tuples of chart fields/jets**. If overlap transformations are continuous and the prelimit fields satisfy the compatibility identities, the limit law is supported on that subspace.

That is much cheaper than building Gaussian measures on global Fréchet section spaces, and directly reflects what the bridge currently proves.

Remember: the field/jet limit is Gaussian; the coefficient vector, being a nonlinear function of it, generally is not.

---

# 5. Ranked programmes

## 1. Intrinsic empirical coefficient functional, with all-orders residue identification

**Highest priority.**

Deliver:

1. intrinsic coefficients of \((\nu_\chi,K,H)\), with observable insertion;
2. sample-field identification \(H_n=\sqrt n(K-K_n)\);
3. the holomorphic-amplitude Laurent formula above;
4. agreement with the existing top stratum formula and analytic Taylor-tree coefficients;
5. the existing stochastic expansion restated using these intrinsic coefficients.

This answers the actual coordinate-free question while reusing almost all the landed asymptotic work.

## 2. Compatible resolved jet laws and atlas-independent limiting distributions

Build the compatibility space and a conditional continuous-mapping theorem for a finite retained coefficient vector.

This gives a geometric stochastic theorem without attempting a new global CLT.

## 3. Empirical modification independence

Extend the comparison from compatible atlases to arbitrary admissible resolved presentations of the same base empirical integral.

If the frozen interface already supports this, it is a corollary/package; otherwise it is a meaningful theorem. Keep it distinct from mere atlas invariance.

## 4. Filtered fluctuation jets and a tensor/tree presentation

Introduce normal splittings only here. Derive the contraction formula, include finite-part terms, and prove agreement with Programme 1.

This is the programme closest to the paper’s proposed future empirical geometry, but it has the largest risk of an attractive yet noncanonical definition.

## 5. A global resolved Gaussian-process CLT

Only prioritise this if needed for an application or if the chart-wise stochastic hypotheses become a serious burden. It is not a prerequisite for an intrinsic asymptotic expansion.

---

# 6. Staged Lean plan for Programme 1

## Stage A — Separate raw and standardised fields

Use distinct definitions, for example:

```lean
empiricalDeformation n ω w := sqrt n * (K w - empiricalK n ω w)

standardizedField n ω w :=
  empiricalDeformation n ω w / sqrt (K w)
```

The second definition may use Lean’s total division, but its mathematical API should explicitly restrict to `K w ≠ 0`. Its arbitrary value at zero must not become part of the geometric claim.

Prove schematically:

```lean
empiricalDeformation_comp_chart
  : Hn (g α u) = monomial α u * chartXi α n ω u

chartXi_eq_standardized_off_divisor
  : monomial α u ≠ 0 →
    chartXi α n ω u = standardizedField n ω (g α u)
```

The second theorem needs the nonnegative-root hypothesis. Provide a signed version separately if relevant.

**Carried by:** grey-book standard-form identities and finite-sum algebra.

**Trap:** reconcile all sign conventions, including `sampleExt`, before connecting the analytic theorem.

## Stage B — A lightweight intrinsic coefficient interface

Avoid starting with a quotient of all atlases.

Define coefficients using one admissible presentation; prove a presentation-independence theorem; expose an abstract specification if useful.

A hypothesis structure should record, or reuse existing structures for:

- base measure and energy;
- deformation \(H\);
- an admissible rectangular presentation;
- quotient-field compatibility;
- the regularity required by the coefficient engine;
- cutoff/lattice comparison data.

Do not require a continuous scalar \(\psi\) on all of \(W\).

Prove:

```lean
intrinsicCoeff_eq_aggCoeff
intrinsicCoeff_presentation_independent
intrinsicCoeff_add_observable
intrinsicCoeff_smul_observable
```

For signed observables, use the inserted-integral interface or linearity; do not silently treat a signed insertion as a positive measure.

**Carried by:** `Bridge/FrozenField`, cutoff uniqueness, existing observable insertion.

## Stage C — Establish the Mellin principal-part interface

First prove the numerical identity
\[
\int_1^\infty N^{s-\mu-1}(\log N)^q\,dN
 =q!(\mu-s)^{-q-1}.
\]

Then prove a general lemma:

> A finite cutoff expansion with remainder \(O(N^{-A})\) identifies the principal parts of its Mellin transform in \(\Re s<A\).

Your little-\(o\) remainder supplies this \(O\)-bound. Choose a cutoff strictly above every pole being identified.

Separately establish the transform kernel \(B(s,z)\), its parameter derivatives, and the Fubini/substitution identity on an initial strip.

**Traps:**

- real versus complex logarithm conventions;
- Laurent signs;
- behavior near \(N=0\);
- uniform domination for parameter derivatives;
- positive mass on the zero set;
- continuous versus discrete asymptotic parameter.

Keep this analytic infrastructure independent of grammar’s chart combinatorics.

## Stage D — Lift population Laurent operators to amplitude families

The required population interface is not merely “coefficients exist for each fixed amplitude.” It should support a holomorphic family of smooth amplitudes, with enough locally uniform regularity to evaluate Laurent operators and differentiate in the spectral parameter.

If grammar does not currently expose that interface, build it from its explicit residue/finite-part formulas rather than assuming pointwise expansions imply it.

Prove an abstract Laurent-product lemma, then instantiate it with
\[
a_s=\varphi B(s,\psi).
\]

This produces the boxed formula in §1.3.

**Carried by:** population residue and renormalised-strata results, after the necessary amplitude-family packaging.

## Stage E — Identify all existing empirical presentations

Prove the triangle:
\[
\text{intrinsic Laurent coefficient}
=
\text{aggregated canonical coefficient}
=
\text{aggregated analytic Taylor-tree coefficient}.
\]

The first equality uses the frozen expansion and Mellin principal parts. The second uses `empCoeffRect_eq_boxCoeff` / `empCoeffRect_eq_taylorSeries`.

At top order, identify the Laurent expression with `empStratumSum` and `empiricalStratumMeasure`, under their actual support/depth hypotheses.

**Trap:** do not advertise a stratum measure at every exponent unless the existing theorem really provides one there. A higher derivative residue is generally a distribution, not a measure.

## Stage F — Transport the stochastic theorems

Restate `evidence_expansion_obs_taylor` and the sequential remainder theorem using intrinsic coefficient variables.

No new probability theorem should be needed at this stage: prove equality of the random coefficient vectors, then transport convergence and distributions.

Use one common probability-one event when compatibility is only almost sure.

---

# 7. What is new relative to the paper?

I would distinguish the following in communication with the authors.

### Formalisation or intrinsic repackaging of existing principles

- The standard-form field identity.
- Atlas independence obtained from uniqueness of asymptotic coefficients.
- Recasting already proved chart-wise convergence in terms of equal intrinsic random variables.
- The population residue/finite-part geometry already stated in the paper.

These can be substantial formal work without being new mathematical claims.

### Explicit empirical coefficient identification

The landed Taylor-tree identification appears to formalise the paper’s stated empirical theorem and displayed coefficient formula, under your explicit analytic hypotheses. It should not be described simply as solving a problem the paper left open.

### A genuine extension beyond the paper’s stated coordinate-free results

Subject to checking the paper’s precise scope, these should be flagged:

- an **all-orders coordinate-free empirical residue/finite-part theorem**;
- a systematic formula expressing empirical coefficients through population Laurent operators and the field-dependent amplitude \(B(s,\psi)\);
- a coordinate-free filtered fluctuation-tree interpretation, including lower logarithmic orders;
- a resolved geometric Gaussian-field/jet theorem, if actually constructed beyond conditional chart-wise convergence.

The Mellin-amplitude mechanism is standard in spirit. The potentially new result is its rigorous application here, with all orders, strata, analytic tree identification, and stochastic consequences—not the Mellin substitution itself.

---

# 8. Main corrections to the framing

1. **The frozen global field is \(H_n\), not \(\psi_n\).**
2. **The standardised process need not descend continuously across the base singular locus.**
3. **The identity with the chart field needs a root/sign convention.**
4. **Normal Taylor components are associated-graded data, not a canonical splitting for arbitrary functions.**
5. **Lower empirical log powers require spectral derivatives of the amplitude as well as lower population finite-part operators.**
6. **A top-order stratum measure should not be extrapolated to all coefficients.** General coefficients are distributional functionals.
7. **A \(C(K)\) CLT alone does not furnish the jets used by the coefficient maps.**
8. **Pathwise frozen invariance does not provide diagonal stochastic remainder control.** Your landed stochastic theorems do.
9. **Atlas independence and modification independence should remain separately named claims.**

The best next milestone is therefore:

> **For every retained \((\mu,q)\), construct an intrinsic empirical coefficient functional, identify it with a finite combination of population Laurent operators applied to \(\varphi\,\partial_s^\ell B(\mu,\psi)\), and prove that the sample’s explicit Taylor-tree coefficients compute it.**

That is coordinate-free, genuinely all-orders, compatible with the existing formal architecture, and much less fragile than beginning with moment tensor bundles.