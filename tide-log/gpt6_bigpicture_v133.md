## Verdict: CLOSE, with wording corrections

The signatures close the programme **in the adopted measure-theoretic sense (3B)**: construction, representation, concentration, uniqueness, transport independence, residue normalization, and the extremal insertion limit are all present.

I would make four paper-level corrections:

1. State **\(c\ge1\)** and, for the residue normalization, **\(\mu>0\)**.
2. Qualify “intrinsic” as **for the fixed resolved geometry and prior, independent of the auxiliary transport data**.
3. Describe the logarithmic residue as the **density-residue convention defined by the displayed face integrals**, not an independently developed residue calculus.
4. Distinguish the normalized-limit coefficient from a **nonzero leading asymptotic**, and distinguish \(\nu\) from the normalized residue measure \(\mathscr R\).

No further substantive unit is necessary for closure.

## (a) What the measure statements establish

### Construction and Radon property

`stratumMeasure`, its regularity instance, and `integral_stratumMeasure` supply the intended Riesz representation on
\[
X=U\setminus D_{c+1}.
\]
Together with `integral_stratumMeasure_test`, this is precisely the representation of the positive extension of the smooth coefficient functional.

The estimate `abs_T_le` supplies fixed-support continuity. Strictly speaking, the extension exists and is unique because of **that estimate together with fixed-support smooth approximation**. Your paragraph should mention both, rather than attributing the extension to the estimate alone.

### Concentration on the exact stratum

`stratumMeasure_compl_exactStratum` is exactly the right statement for
\[
\nu^\mu_c(X\setminus S^\mu_c)=0.
\]

“**Carried by the exact stratum**” is excellent wording. It does not imply that every point of the exact stratum belongs to the topological support.

Moreover, because \(S^\mu_c\subset X\) and it is relatively closed in \(X\), you may also say
\[
\operatorname{supp}_X\nu^\mu_c\subset S^\mu_c.
\]
Writing \(\overline{S^\mu_c}^{\,X}\) is correct but unnecessary: that closure is \(S^\mu_c\) itself.

The ambient space matters. This does **not** establish an ambient-\(U\) support statement excluding accumulation at \(D_{c+1}\). Nor does it assert any finite or Radon extension across that set.

### Representation on \(\mathcal I_{c+1}\)

Yes:
`coeff_withF_eq_integral_stratumMeasure` represents the functional on all smooth observables **vanishing on a neighbourhood of \(D_{c+1}\)**. There is no compact-support-in-\(X\) assumption.

Be explicit that this is the definition of \(\mathcal I_{c+1}\) being used. Vanishing merely *on* \(D_{c+1}\), or vanishing there to a prescribed finite order, would be different hypotheses.

Your integrability argument is sound:
\[
G|_X=(G\chi)|_X\quad \nu^\mu_c\text{-a.e.},
\]
where \(G\chi\) is smooth and compactly supported in \(X\). Consequently \(G|_X\) is integrable.

There is nevertheless a useful formal-interface distinction:

> An equality involving Lean’s Bochner integral does not, by itself, assert integrability.

I recommend adding an explicit `Integrable` lemma as a small API completion, using exactly your cutoff argument. This is **not a missing mathematical unit or a closure blocker**. In the paper, “\(F\) is integrable and satisfies …” is justified by the construction you describe.

The same observation applies to the residue-measure integral formulas.

### Uniqueness

`eq_stratumMeasure_of_tests` is a genuine uniqueness statement: among the regular measures in its hypothesis, agreement on ambient smooth compactly supported tests in \(X\) determines the measure.

The key facts are exactly those in your proof notes:

- arbitrary \(C_c(X)\) functions admit fixed-support smooth approximation;
- compact supports have finite measure;
- uniform approximation therefore gives convergence of integrals;
- regular measures are determined by these \(C_c\) integrals.

For reader-facing wording, “**the unique positive Radon measure with these smooth-test integrals**” is particularly clear. “Unique regular Borel measure” is also faithful when understood with the local-finiteness convention supplied by the formal regularity framework.

### Independence

`stratumMeasure_eq_of_transports` proves independence of \(Y\), with \(\Xi\) fixed.

It does not state independence of:

- the modification;
- the resolved ambient space;
- a change of resolution via pushforward;
- arbitrary alternative geometric constructions.

Thus “intrinsic” is fine with its scope specified. The corresponding independence of \(\mathscr R^\mu_c\) is an immediate consequence of its scalar definition.

## (b) The weighted logarithmic residue terminology

For \(\mu>0\), \(c\ge1\), the normalization is positive and the identities give
\[
\mathscr R^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c,
\qquad
\int G\,d\nu^\mu_c
=\frac{\Gamma(\mu)}{(c-1)!}\int G\,d\mathscr R^\mu_c.
\]

`integral_residueMeasure_eq` justifies calling \(\mathscr R^\mu_c\) the residue measure **under the stated density-residue convention**. This is more than an unsupported name: its action on admissible insertions is proved to equal the chartwise bare residue sum, and the measure itself has an intrinsic characterization.

What is not established is an independent logarithmic-density calculus, followed by a theorem identifying its output with \(\mathscr R\). Also, the displayed global chart-sum identity should not be advertised as a separately formalized chart-pushforward measure theorem.

Recommended wording:

> We call \(\mathscr R^\mu_c\) the unsigned, multiplicity-weighted logarithmic residue measure of the twisted prior density. This terminology refers to the proved face-integral formula: extraction of each simple density pole, normalized against \(d\log(u_j^{2k_j})\), contributes the factor \((2k_j)^{-1}\), with the chart and face multiplicities included in the residue sum. This is a positive-measure construction from densities, not the classical alternating-form Poincaré residue; no logarithmic-form residue calculus is asserted.

Keep “pole” in this density sense. In particular, do not imply meromorphicity of the twisted density in the coordinates, or identify it with a meromorphic differential form.

## (c) The extremal insertion theorem and total mass

### What CDLVII says

The statements establish, under their hypotheses,
\[
Z_f(N)=N^{-\lambda}(\log N)^{m-1}
\left(\int f\circ\pi\,d\nu^\lambda_m+o(1)\right).
\]

This is valid even when the integral vanishes. It is an asymptotic equivalence
\[
Z_f(N)\sim
\left(\int f\circ\pi\,d\nu^\lambda_m\right)
N^{-\lambda}(\log N)^{m-1}
\]
only when that integral is nonzero—exactly as required by `partitionObs_isEquivalent_extremal`.

Two qualifications are important:

- `IsExtremalData lam m`, as defined here, consists of **extremal bounds**. It does not itself assert that either bound is attained, that the measure is nonzero, or that \((\lambda,m)\) is the actual leading index.
- At the independently identified RLCT pair \((\lambda^*,m^*)\), you may call this the coefficient at the leading scale. For a particular insertion, cancellation or vanishing can still make that coefficient zero.

Also replace “zero-order condition holds on every stratum” by:

> the zero-order condition holds on each exact \(\lambda^*\)-resonant stratum.

That avoids suggesting every wall on every depth stratum has ratio \(\lambda^*\).

### The Gamma factor in the proposed addition

The integral against \(\nu\) is **not the bare residue integral against \(\mathscr R\)**. Your last sentence should retain the factor:
\[
\int f\circ\pi\,d\nu^{\lambda^*}_{m^*}
=
\frac{\Gamma(\lambda^*)}{(m^*-1)!}
\int f\circ\pi\,d\mathscr R^{\lambda^*}_{m^*}.
\]

### Unit insertion

Correct: the constant unit insertion satisfies the landed neighbourhood-vanishing hypothesis exactly when \(D_{m+1}=\varnothing\).

In that case, the representation applies to \(1\), the measure is finite, and its mass is identified with the unit coefficient. When \(D_{m+1}\ne\varnothing\), these signatures do not make that identification.

### General versus extremal total mass

Your suspicion of infinite mass is valid for the **general** stratum measures. For example, with positive prior near the origin and
\[
K(x,y)=x^2y^2,\qquad \mu=\tfrac12,\quad c=1,
\]
the simple-stratum residue density along an axis behaves like
\[
\frac{dy}{|y|}
\]
near the removed crossing. Its total mass can therefore be infinite.

But this example has leading multiplicity \(2\), not \(1\). Do not transfer the same expectation uncritically to the **extremal leading measure**. At extremal data, remaining nonresonant directions have strictly integrable exponents; finiteness is much more plausible.

There is also a cheap conditional argument. If the earlier extremal theory supplies a finite bound
\[
\limsup_{N\to\infty}
N^\lambda(\log N)^{-(m-1)}Z_1(N)\le C,
\]
then positivity gives, for every compactly supported smooth \(0\le\chi\le1\) in \(X\),
\[
\int\chi\,d\nu^\lambda_m
=\lim N^\lambda(\log N)^{-(m-1)}Z_\chi(N)
\le C.
\]
Cutoffs and inner regularity imply \(\nu^\lambda_m(X)\le C\).

That proves finiteness, **not equality with the unit coefficient**: equality additionally requires ruling out leading mass concentrating toward the removed deeper fibre.

For this closure paragraph, leave total mass unspecified. In particular, do not use `ν.real univ` as a proxy for total mass without first proving finiteness: the real-valued conversion does not faithfully represent infinite mass.

## (d) Recommended final wording

Here is a replacement that keeps the mathematical scope explicit. Attach the corresponding landed references to the claims as in your draft.

> **The stratum measure and the weighted residue (formalised).** Let \(c\ge1\), and assume the zero-order condition on \(S^\mu_c\): every wall through this exact stratum satisfies \(2k_j\mu=h_j+1\). The coefficient functional \(\mathcal T^U_{\mu,c-1}\) determines a positive Radon measure \(\nu^\mu_c\) on \(X=U\setminus D_{c+1}\). It is obtained by applying the Riesz–Markov–Kakutani theorem to the positive extension of the coefficient functional from smooth compactly supported tests to \(C_c(X)\); fixed-support smooth approximation and the cutoff bound \(\lvert\mathcal T^U_{\mu,c-1}[G]\rvert\le\|G\|_\infty\mathcal T^U_{\mu,c-1}[\chi_L]\) give the required extension. The measure is carried by \(S^\mu_c\), which is relatively closed in \(X\), and is uniquely determined among positive Radon measures by its smooth-test integrals. For every smooth \(F\) vanishing on a neighbourhood of \(D_{c+1}\), with no compact-support assumption on \(F\), its restriction to \(X\) is integrable and
> \[
> \mathcal T^U_{\mu,c-1}[F]=\int_X F\,d\nu^\mu_c.
> \]
> In particular, \(C_{\mu,c-1}(f)=\int_X f\circ\pi\,d\nu^\mu_c\) whenever \(f\circ\pi\) satisfies this neighbourhood-vanishing condition. For the fixed resolved geometry and prior, the measure is independent of the auxiliary transport data.
>
> For \(\mu>0\), define
> \[
> \mathscr R^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c.
> \]
> The proved normal-crossings identity identifies its integral against every such \(F\) with the bare sum of simple-face residue integrals of the twisted prior density \((K\circ\pi)^{-\mu}\mu_U\). Each extracted simple density pole contributes \((2k_j)^{-1}\), corresponding to normalization against \(d\log(u_j^{2k_j})\), and the sum retains the chart and face multiplicities. In this precise sense we call \(\mathscr R^\mu_c\) the unsigned, multiplicity-weighted logarithmic residue measure. This is a residue convention for densities yielding a positive measure, not the classical alternating-form Poincaré residue. No logarithmic-form calculus, identification with a Laurent coefficient of a meromorphically continued zeta function, or Radon extension across \(D_{c+1}\) is asserted.
>
> At the RLCT data \((\lambda^*,m^*)\) identified earlier, with \(m^*\ge1\), the zero-order condition holds on the exact \(\lambda^*\)-resonant strata. For every smooth observable \(f\) whose pullback vanishes on a neighbourhood of \(D_{m^*+1}\),
> \[
> N^{\lambda^*}(\log N)^{-(m^*-1)}
> \int \varphi f\,e^{-NK}
> \longrightarrow
> \int_X f\circ\pi\,d\nu^{\lambda^*}_{m^*}
> =
> \frac{\Gamma(\lambda^*)}{(m^*-1)!}
> \int_X f\circ\pi\,d\mathscr R^{\lambda^*}_{m^*}.
> \]
> When this coefficient is nonzero, the corresponding asymptotic equivalence follows; when it is zero, the normalized limit statement remains valid. The result does not identify the unit-insertion coefficient with total mass when the unit insertion fails the neighbourhood-vanishing hypothesis.

### Optional follow-ups, ranked by value/cost

| Rank | Follow-up | Assessment |
|---|---|---|
| 1 | **\(x^2y^2\) regression** | High explanatory value, relatively low cost. Checks crossing multiplicities, Gamma normalization, infinite lower-stratum mass, and the finite leading atomic measure. |
| 2 | **Local positivity / nonzero insertion coefficient** | High value, moderate cost. Turns normalized limits into genuine asymptotic equivalences in useful cases. |
| 3 | **Explicit chart-pushforward measure identity** | High value, higher cost. Makes the geometric density description a direct measure theorem and helps with positivity and finiteness. |
| 4 | **Measure on the subtype \(S^\mu_c\)** | Low cost, modest added content. Mostly repackages the existing concentration theorem. |
| 5 | **Zeta continuation and Laurent-coefficient comparison** | Substantial new programme; high cost, not a closure dependency. |

For positivity, the proposed statement is mathematically sound under the usual local nondegeneracy assumptions: a nonnegative insertion positive at an exact-stratum point where the residual prior amplitude is positive gives a positive local face contribution. Prior positivity must genuinely imply that residual-amplitude positivity in your chart setup. This does not follow merely from “carried by”; it needs a local lower-bound argument. The orthant lower bound is a plausible route, but its applicability and cost depend on its precise signature.

Before those follow-ups, I would add the inexpensive explicit integrability lemma for API clarity.

## (e) Memory/plan wording

Use:

> **Constructed the intrinsic positive Radon measure on \(U\setminus D_{c+1}\), carried by the exact stratum, intrinsic here meaning independent of auxiliary transport data for the fixed resolved geometry and prior. Proved representation for smooth insertions vanishing near the deeper zero fibre, uniqueness from smooth tests, the normalized density-residue chart formula, and the extremal insertion limit; asymptotic equivalence requires a nonzero coefficient. Log-form calculus, zeta continuation, resolution comparison, and extension across the deeper fibre remain outside scope.**

That is faithful to the supplied signatures. **CLOSE.**