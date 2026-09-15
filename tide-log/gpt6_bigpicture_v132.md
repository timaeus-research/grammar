## Recommendation

**Proceed with item 2 by smooth-test extension and Riesz. Adopt (3B), but distinguish the asymptotic measure from the weighted logarithmic residue. Do not claim that this constructs the ordinary Poincaré residue of a log form.**

There are three important corrections to the proposal:

1. **Use \(X:=U\setminus D_{c+1}\) for the construction.** A measure carried by \(S^\mu_c\subset X\) is already the right intrinsic stratum measure. Constructing it first on \(S^\mu_c\) adds unnecessary extension machinery.
2. **The displayed residue density needs the restricted smooth amplitude/unit factors, and any branch multiplicities.** `residueWeight` alone is not the full coordinate density.
3. **The factors \(\prod_{j\in J}(2k_j)^{-1}\) are multiplicity weights, not part of the ordinary Poincaré residue with respect to \(d\log u_j\).** This distinction should be explicit in the definitions and paper.

The original item (3), interpreted as a general log-form calculus, is the wrong near-term target. Interpreted as an intrinsic **weighted logarithmic residue measure**, it is appropriate.

---

## 1. Freeze the hypotheses first

For the main construction, fix:

- \(c\geq 1\);
- the geometric/resolution data and \(\mu\);
- the hypotheses giving **linearity, positivity, and exact-stratum locality for every smooth test function under consideration**;
- \(D_{c+1}\) closed, with \(X=U\setminus D_{c+1}\) locally compact Hausdorff;
- \(S:=S^\mu_c\cap X\) closed in \(X\), and \(S\subset Z_0\cap X\).

Use `ZeroOrder μ c` if it supplies the requisite uniform hypotheses. The point to audit is that the hypothesis must remain valid as the test function varies: a positivity theorem for one fixed `Ξ.F` does not itself provide a positive linear functional on a test-function space.

For the explicit Gamma-normalized statement, use \(\mu>0\), together with the hypotheses of CDLIII. On every simple face, \(2k_j\mu=h_j+1\) already forces \(k_j>0\).

Do **not** use the Laplace-limit description for arbitrary \((\mu,c)\). Include it only under the hypotheses of the existing extremal/leading-index theorem. Otherwise the intrinsic definition uses the coefficient functional, not an unrenormalized Laplace limit.

---

## 2. Item 2: construct on the ambient open space

### 2.1 Smooth tests on \(X\)

Let
\[
T(F):=\mathcal T^U_{\mu,c-1}[\widetilde F],
\qquad F\in C^\infty_c(X),
\]
where \(\widetilde F\) is extension by zero to \(U\).

Compact support in the open subset makes this extension smooth and makes it vanish on a neighborhood of \(D_{c+1}\). Thus CDLIII and the positivity/locality results apply.

Package this as a functional on a **genuine varying-test-function domain**, not merely as a collection of theorems about separately constructed resolved data.

### 2.2 Extend by fixed-support approximation

Your proposed route is standard and sound.

For every compact \(K\subset X\), construct
\[
\chi_K\in C^\infty_c(X),\qquad
\chi_K\geq0,\qquad \chi_K\geq1\text{ on }K.
\]
Positivity gives
\[
|T(F)|\leq T(\chi_K)\,\|F\|_\infty
\quad\text{when }\operatorname{supp}F\subset K.
\]

The approximation lemma should explicitly give **one common compact support**:

> For \(f\in C_c(X,\mathbb R)\), there are a compact \(L\subset X\) and \(F_n\in C^\infty_c(X)\), all supported in \(L\), with \(F_n\to f\) uniformly.

The convex-gluing theorem plus cutoff gives exactly this:

1. choose \(0\leq\eta\leq1\), smooth and compactly supported, with \(\eta=1\) on \(\operatorname{supp}f\);
2. approximate \(f\) uniformly by smooth \(g_n\) on \(X\);
3. set \(F_n=\eta g_n\).

Then \(\eta f=f\), so the uniform error does not increase, and all supports lie in \(\operatorname{supp}\eta\).

Define
\[
\Lambda(f)=\lim_n T(F_n).
\]
Use compact unions to prove independence of choices and linearity. Positivity follows from the same local bound; positive smooth approximants are not necessary.

**Do not try to prove a global sup-norm bound for \(T\).** Local compact-support bounds are sufficient and are compatible with infinite total mass.

### 2.3 Riesz and smooth-test uniqueness

Set
\[
\nu^\mu_c:=\operatorname{RealRMK.rieszMeasure}(\Lambda).
\]

The core theorem is
\[
\boxed{\quad
\mathcal T^U_{\mu,c-1}[\widetilde F]
=\int_X F\,d\nu^\mu_c,
\qquad F\in C^\infty_c(X).
\quad}
\]

Prove a reusable uniqueness lemma:

> Two positive Radon measures on \(X\) agreeing on all smooth compactly supported real tests are equal.

Its proof uses the same fixed-support approximation and finiteness of each measure on the common compact support, followed by continuous-test uniqueness.

This is what turns the construction into a coordinate-independent object, independently of the particular extension implementation.

---

## 3. Support and the choice between \(X\) and \(S\)

### Construct on \(X\); describe it as carried by \(S\)

From locality, a smooth test supported in \(X\setminus S\) has \(T(F)=0\). Smooth cutoffs and regularity then give
\[
\nu^\mu_c(X\setminus S)=0,
\qquad
\operatorname{supp}_X\nu^\mu_c\subset S.
\]

Both formulations are worth exposing. **Do not assert equality of supports** without a nondegeneracy/strict-positivity hypothesis.

Because \(S\) is closed in \(X\), it is Borel and locally compact Hausdorff. Consequently the measure can also be regarded as a Radon measure on \(S\), whose pushforward under \(S\hookrightarrow X\) is \(\nu^\mu_c\). Make this an optional corollary, not the construction.

### The proposed direct-on-\(S\) route contains a false requirement

A general \(f\in C_c(S)\) cannot be the restriction of a smooth ambient function: its restriction would be smooth along a smooth stratum. Thus

> “every \(C_c(S)\) function extends to a smooth \(F\)”

is false.

One could instead extend **smooth** functions on \(S\), then approximate continuous functions there, but that adds a submanifold-extension theorem without improving the final object. Values-only dependence establishes well-definedness on the image of restriction; it does not establish surjectivity.

**Paper-facing choice:** “a positive Radon measure on \(U\setminus D_{c+1}\), carried by the exact stratum.” This also avoids depending on a global smooth-manifold description of that stratum.

---

## 4. Can the representation cover noncompactly supported \(F\)?

**Yes, for smooth \(F\) vanishing on a neighborhood of \(D_{c+1}\), using compactness of \(Z_0\).** This deserves a separate theorem.

Indeed,
\[
K_F:=Z_0\cap\operatorname{supp}_U(F)
\]
is compact and disjoint from \(D_{c+1}\), hence compact in \(X\). Choose \(\chi\in C^\infty_c(X)\) equal to \(1\) on \(K_F\). Then \(F\) and \(\chi F\) agree on \(S\), so locality and concentration give
\[
\mathcal T[F]=\mathcal T[\chi F]
=\int_X\chi F\,d\nu^\mu_c
=\int_XF\,d\nu^\mu_c.
\]
Moreover \(F\) is integrable: its nonzero values on the measure-carrying set occur in \(K_F\), where it is bounded and the measure is finite.

Thus \(F=1\) is allowed when \(D_{c+1}=\varnothing\). In that case the measure is carried by the compact set \(Z_0\), so it has finite total mass.

**But audit the meaning of \(\mathcal I_{c+1}\).** If it means merely vanishing *on* the deeper locus, or vanishing to some finite order, this argument does not apply. Such an extension needs a separate integrability theorem and a suitable approximation/continuity result. The safe initial theorem should spell out **vanishing on a neighborhood**, exactly as CDLIII does.

---

## 5. The coordinate formula: what is actually a residue?

Write a local positive-sector expression schematically as
\[
K\circ\pi=\kappa(u,y)\prod_i u_i^{a_i},
\qquad a_i=2k_i,
\]
\[
d\mu_U=A(u,y)\prod_i u_i^{h_i}\,|du\,dy|.
\]
Here \(\kappa>0\) is the unit; put
\[
B_\mu=A\,\kappa^{-\mu}.
\]

For a simple face \(J\), \(|J|=c\) and \(a_j\mu=h_j+1\), the contribution to \(\nu^\mu_c\) is
\[
\boxed{
\frac{\Gamma(\mu)}{(c-1)!}
\left(\prod_{j\in J}a_j^{-1}\right)
B_\mu(0_J,w,y)
\prod_{i\notin J}w_i^{h_i-a_i\mu}
\,|dw\,dy|.
}
\]

In the actual CDLIII statement, retain the outer parameter integrations, partition/localization factors, units such as \(\beta^{-\mu}\), and pushforwards. They must either appear explicitly or be demonstrably absorbed into \(B_\mu\). Likewise, sum the relevant real sectors/branches according to the existing chart convention.

The immediate theorem should therefore be the **test-integral identity**
\[
\int_XF\,d\nu^\mu_c=\operatorname{residueSum}(F).
\]
That is already a rigorous coordinate representation. An equality with an independently constructed chart-pushforward measure is an additional theorem, not something obtained merely by writing a density.

### Ordinary residue versus multiplicity-weighted residue

Along the simple walls, the twisted density has the local form
\[
B_\mu(u,w,y)
\prod_{j\in J}\frac{|du_j|}{|u_j|}
\prod_{i\notin J}w_i^{h_i-a_i\mu}\,|dw\,dy|.
\]

The unsigned logarithmic density residue with respect to
\(\lvert d\log u_j\rvert\) has coefficient
\[
B_\mu(0_J,w,y)\prod_{i\notin J}w_i^{h_i-a_i\mu}.
\]

It does **not** contain \(\prod a_j^{-1}\). Those factors arise when extracting coefficients against
\[
|d\log(u_j^{a_j})|=a_j\,|d\log u_j|.
\]

So your normalization is natural, but it is a **multiplicity-weighted logarithmic residue determined by \(K\)**. It is not just the ordinary Poincaré residue of the twisted density.

The Gamma/factorial factor is a further Laplace normalization; it is not part of the ordinary residue either.

---

## 6. Ruling on item 3

### (3A): defer the general calculus

A real density is not an alternating differential form. Its residue is unsigned, branch conventions matter, and the twisted density need not have only simple logarithmic poles globally: other exponents may be nonintegral or higher-order.

Accordingly, a general “Poincaré residue for log forms on \(U\)” is both expensive and not exactly the object your coefficient theorem needs.

A restricted calculus of **unsigned logarithmic density residues**, with multiplicity weights and clean simple intersections, would be a sensible later project. It can avoid a full de Rham/log-form development, but it is still new infrastructure.

### (3B): approve, with two named normalizations

Keep
\[
\nu^\mu_c
\]
for the asymptotic coefficient measure. If an independently named residue object is wanted, define
\[
\mathscr R^\mu_c
:=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c,
\qquad \mu>0.
\]
Then
\[
\mathcal T_{\mu,c-1}[F]
=\frac{\Gamma(\mu)}{(c-1)!}\int F\,d\mathscr R^\mu_c,
\]
and \(\mathscr R^\mu_c\) has precisely the multiplicity-weighted face formula without the Gamma/factorial factor.

This is an intrinsic residue **measure**, defined through the coefficient functional and identified by the coordinate theorem.

Be plain about scope: this completes a revised item (3), **not** the original request for an independent general Poincaré-residue operator on densities with poles.

### (3C): defer

The zeta interpretation is mathematically well aligned with \(\mathscr R^\mu_c\): under the requisite continuation and pole-order hypotheses, its test integral is the coefficient of \((s+\mu)^{-c}\). The corresponding Laplace coefficient is multiplied by \(\Gamma(\mu)/(c-1)!\).

But meromorphic continuation is not a shortcut here. Budget it as a separate **L** project, potentially larger if a reusable complex-analytic framework is intended.

### Recommended paper wording

> The coefficient functional determines an intrinsic positive Radon measure on \(U\setminus D_{c+1}\), carried by the exact stratum. In normal-crossings coordinates, this measure is \(\Gamma(\mu)/(c-1)!\) times the multiplicity-weighted logarithmic residue of the twisted prior density, with normalization against \(d\log(u_j^{2k_j})\).

Then distinguish this density-residue terminology from the classical alternating-form construction.

Avoid the unqualified equation
\[
\nu^\mu_c=\frac{\Gamma(\mu)}{(c-1)!}
\operatorname{Res}_{S^\mu_c}[(K\circ\pi)^{-\mu}\mu_U]
\]
unless `Res` has explicitly been defined to mean this weighted, unsigned residue, including the branch convention.

---

## 7. Fixed unit list and costs

These are engineering estimates, not claims about exact existing declaration compatibility.

| Order | Unit | Deliverable | Cost |
|---|---|---|---|
| 1 | **StratumTestFunctional** | Varying smooth-test API; extension by zero; common hypotheses; linearity, positivity, locality | **M** |
| 2 | **SmoothCompactApproximation** | Compactly supported cutoffs and uniform approximation with one common compact support | **M** |
| 3 | **PositiveSmoothExtension** | Local sup-norm bound; unique positive linear extension to `C_c` | **M** |
| 4 | **SmoothTestMeasureUniqueness** | Equality of Radon measures from smooth compact tests | **S–M** |
| 5 | **StratumRadonMeasure** | Riesz definition, regularity/local finiteness, smooth integral representation, uniqueness | **S** after 1–4 |
| 6 | **StratumMeasureSupport** | Closed/Borel exact stratum; concentration and support inclusion | **S–M** |
| 7 | **StratumMeasureLocalization** | Representation and integrability for tests vanishing near the deeper locus, using compact \(Z_0\) | **M** |
| 8 | **StratumMeasureResidueFormula** | `integral_eq_residueSum`; faithful chart-normalization theorem | **S** for the integral theorem; **M** for explicit local measure identities |
| 9 | **IntrinsicWeightedResidue** | \(\mathscr R^\mu_c\), normalization identities, coordinate formula; leading-index limit characterization where available | **S** |
| 10 | **StratumMeasureNaturality** | Transport/chart independence as measure equalities via uniqueness | **S–M**, assuming existing transport results |

Optional, later:

- **Measure directly on the subtype \(S\): S–M.**
- **Explicit chart-pushforward measure and equality with Riesz: M–L.**
- **Restricted logarithmic density-residue calculus: L.**
- **General log-form calculus or zeta continuation: L or larger.**

The extension infrastructure is the main item-2 cost. Do not budget the whole construction as “Riesz: S.”

---

## 8. Why not start with chart pushforwards?

It is a legitimate alternative, but not obviously cheaper with the stated infrastructure.

You would need nonnegative **test-independent** chart weights, measurable parameterized measures/maps, branch bookkeeping, and local finiteness on every compact subset of \(X\). The existing integrability theorem is useful, but it must apply to the dominating cutoff needed for local finiteness. `Measure.bind` also introduces kernel/measurability obligations.

After that, smooth-test uniqueness still needs approximation.

**Use chart pushforwards later as a concrete model of the already intrinsic measure.** Start there only if most of those measure/kernel constructions already exist.

Finally, keep the ambient-space distinction visible: \(\nu^\mu_c\) is Radon on \(X\), but can have infinite mass accumulating toward \(D_{c+1}\). Its pushforward to \(U\) is a measure, yet need not be locally finite or Radon at the omitted locus. That is a feature of the residue geometry, not a defect of the construction.