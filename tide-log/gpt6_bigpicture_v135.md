## Recommendation

**Build P1 now, with the normalized measure \(\mathcal R^\mu_c\) as the primary explicit object.** Derive the corresponding identity for \(\nu^\mu_c\) by multiplying by `residueConst μ c`.

This is the missing structural unit: an actual face-density pushforward measure, proved equal to the existing intrinsic measure. It does **not** require a general density-residue calculus or a new asymptotic engine.

Two corrections are needed first:

1. The proposed collar formula for Definition B is divergent as written.
2. An ordinary, unsigned density residue gives the coefficient **per normal side**. Your existing residue measure sums orthants, so a two-sided wall contributes an additional factor \(2\). Thus the fully two-sided formula has \(2^c/\prod_{j\in J}2k_j\), not merely \(1/\prod_{j\in J}2k_j\).

---

# 1. Check of Definitions A and B

## A. Laplace definition: correct

For the admissible tests and hypotheses already used by the programme,
\[
\int_X F\,d\mathcal R^\mu_c
=
\frac{(c-1)!}{\Gamma(\mu)}
\lim_{N\to\infty}
N^\mu(\log N)^{-(c-1)}
\int_U F e^{-N(K\circ\pi)}\,d\mu_U.
\]

Keep the restrictions on \(F\) explicit: for the measure characterization, smooth compactly supported tests on \(X=U\setminus D_{c+1}\), represented by their admissible extensions to \(U\).

## A′. Truncated negative moment: \(c!\) is correct

The candidate formula is
\[
\boxed{
\int_X F\,d\mathcal R^\mu_c
=
\lim_{\delta\downarrow0}
\frac{c!}{(\log(1/\delta))^c}
\int_{\{K\circ\pi>\delta\}}
F(K\circ\pi)^{-\mu}\,d\mu_U .
}
\]

Here is the constant check on one orthant. Along the \(c\) resonant walls,
\[
|u_j|^{h_j-2k_j\mu}\,d|u_j|
=\frac{d|u_j|}{|u_j|},
\qquad
t_j=2k_j\log(1/|u_j|).
\]
Consequently,
\[
\prod_{j\in J}\frac{d|u_j|}{|u_j|}
=
\left(\prod_{j\in J}\frac1{2k_j}\right)\prod_{j\in J}dt_j.
\]
The cutoff produces, to leading order, a simplex of volume
\[
\frac{(\log(1/\delta))^c}{c!}.
\]
Thus its leading coefficient is exactly \(\mathcal R^\mu_c(F)/c!\).

**Caveats for the artifact:**

- This is a **truncated negative-moment formula**, rather than literally a sublevel-set integral: the region is \(\{K\circ\pi>\delta\}\).
- The constant check is not a formal proof of the general formula. Unless it has been proved separately, label it an expected/equivalent classical characterization, **not a formalized equivalence**.
- State it for compactly supported admissible tests. A global integral without localization can introduce unrelated convergence issues.

## B. Correct the residue definition and collar formula

Let
\[
\omega=\frac{a(f,y)}{|f|}\,|df|\,|dy|
\]
near \(E=\{f=0\}\), where \(a\) extends regularly to \(E\). The ordinary density residue is
\[
\operatorname{res}_E\omega=a(0,y)|dy|.
\]

A coordinate-free shorthand is
\[
\boxed{
\operatorname{res}_E\omega
=
\frac{\left.(|f|\omega)\right|_E}{|df|}.
}
\]
Here the restriction and division mean the normal/tangential density decomposition along \(E\); they are not the ordinary pullback of a top-dimensional density.

Use **\(|f|\omega\)**, not \(f\omega\), for positive densities and signed defining functions.

### The proposed collar formula is wrong

For \(\omega\sim a\,|df|/|f|\),
\[
\int_{\{|f|<\varepsilon\}}g\,\omega
\]
is already infinite for every \(\varepsilon>0\), generally. Dividing by \(2\varepsilon\) does not repair it.

The correct ordinary-residue collar formula is
\[
\int_E g\,\operatorname{res}_E\omega
=
\lim_{\varepsilon\downarrow0}
\frac1{2\varepsilon}
\int_{\{|f|<\varepsilon\}}\widetilde g\,|f|\omega.
\]
Equivalently, with a localized collar and fixed outer radius,
\[
\int_E g\,\operatorname{res}_E\omega
=
\lim_{\varepsilon\downarrow0}
\frac1{2\log(1/\varepsilon)}
\int_{\{\varepsilon<|f|<r\}}\widetilde g\,\omega.
\]

These formulas assume a smooth two-sided coefficient extending through the wall. For a one-sided collar, omit the factor \(2\).

### Invariance and iteration

Under \(f'=af\), with \(a\) nonvanishing,
\[
|f'|\omega=|a|\,|f|\omega,
\qquad
|df'|_E=|a|_E|df|_E,
\]
so the ordinary density residue is invariant.

For a normal-crossing simple-pole density, iteration along distinct walls is symmetric: there is no orientation sign for densities.

### Multiplicities and the factor \(2^c\)

Write \(n_j=2k_j\). The multiplicity-normalized ordinary iterated residue is
\[
\left(\prod_{j\in J}n_j^{-1}\right)\operatorname{res}_{E_J}\omega.
\]

But **your \(\mathcal R\) is the sum of the one-sided contributions**. In a full, two-sided normal-crossing chart with smooth coefficient,
\[
\boxed{
\mathcal R^\mu_c
=
\frac{2^c}{\prod_{j\in J}2k_j}\,
\operatorname{res}_{E_J}\!\left[(K\circ\pi)^{-\mu}\mu_U\right]
}
\]
on the relevant exact stratum, with the usual chart localization and sum over faces.

Your orthant construction already implements this correctly: each orthant contributes \(\prod(2k_j)^{-1}\), and the normal sign choices contribute \(2^c\).

A useful sanity check is \(K(x)=x^{2k}\), \(d\mu=dx\), \(\mu=1/(2k)\). Then
\[
\mathcal R^\mu_1=\frac1k\delta_0,
\]
whereas the ordinary residue of \(|x|^{-1}|dx|\) is \(1\). Dividing only by \(2k\) would give half the correct answer.

**Notation:** `Res^(div K∘π)_S` is reasonable only after explicitly declaring whether `Res` means the ordinary coefficient residue or the **sum-of-normal-sides logarithmic density residue**. I recommend the latter convention for Definition B, and stating it prominently.

---

# 2. The precise P1 object

## 2.1 Freeze the geometry and remove the test insertion

Introduce a baseline context
```lean
Ξ₁ := Ξ.withF (fun _ => 1) contMDiff_const
```
and define all explicit face densities using its amplitude.

Do not merely assume the base measure is independent of `F`. Prove the relevant lemmas:

```lean
withF_geometry_eq
withF_baseMeasure_eq
amp_withF_eq_mul_faceEvaluation
```

The key pointwise lemma should say, schematically,
```lean
((Ξ.withF G hG).amp Y p).amp s v
  =
  (Ξ₁.amp Y p).amp s v * G (Ξ.divPt Y p s v)
```
on the valid chart domain.

Use the baseline base measure
```lean
βp := ((Ξ₁.decomp Y).chart I).ν
```
throughout the new definition. Prove that the base measures in the existing `withF` formula coincide with these, using dependent rewriting where necessary.

**Do not put `prior`, `ω`, or inactive monomial factors into the definition a second time.** The exact existing F-free amplitude and base measure together determine where those factors belong.

## 2.2 Face parameter space

For \(p=\mathrm{en}(I)\) and \(J\in\mathrm{simpleFaces}(p,\mu,c)\), let
\[
W_{p,J}=\{j:\operatorname{Fin}(\mathrm{da}(p))\mid j\notin J\}\to\mathbb R
\]
and
\[
Q_{p,J}=\operatorname{Base}_p\times W_{p,J}.
\]

The reference measure is
\[
q_{p,J}
=
\beta_p\otimes
\bigl(\mathrm{volume}\restriction\mathrm{box}(W_{p,J},a_p)\bigr).
\]

This order matches the existing iterated integral:
\[
\int_s\int_w(\cdots)\,dw\,d\beta_p(s).
\]

Define
\[
z_{p,J}(s,w)=\mathrm{glue}(J,0,w),
\qquad
e_{p,J}(s,w)=\mathrm{divPt}(p,s,z_{p,J}(s,w)),
\]
and the nonnegative density
\[
D_{p,J}(s,w)=
\left(\prod_{j\in J}\frac1{2k^A_{p,j}}\right)
A^0_p(s,z_{p,J}(s,w))
\operatorname{residueWeight}(h^A|_{J^c},k^A|_{J^c},\mu,w).
\]

Then the source measure is
\[
\lambda_{p,J}=q_{p,J}.\mathrm{withDensity}(\operatorname{ofReal}D_{p,J}).
\]

This definition makes the Base integration completely explicit.

## 2.3 Build directly on \(X\)

I recommend **not** first defining a potentially infinite global measure on \(U\) and then transporting its restriction to a subtype.

Instead:

1. Restrict the parameter space to valid face points in the chart.
2. Further restrict to points for which \(e_{p,J}(s,w)\in X\).
3. Push the restricted source measure to \(X\).

Schematically:
```lean
noncomputable def faceResidueMeasure
    (I : Fin (Fintype.card (Ξ₁.X Y).PIdx))
    (J : Finset (Fin ((Ξ₁.X Y).da ((Ξ₁.X Y).en I))))
    (hJ : J ∈ Ξ₁.simpleFaces Y ((Ξ₁.X Y).en I) μ c) :
    Measure (Ξ.stratumOpen c) :=
  Measure.map faceMapToStratumOpen faceSourceMeasureOnOpen
```

Implement `faceSourceMeasureOnOpen` using a measurable subtype/restriction construction, hidden behind helper definitions.

### Important chart-domain issue

An `OpenPartialHomeomorph` is continuous on its source/target, **not automatically globally continuous as a total Lean function**. In particular, do not base the proof on an unrestricted claim
```lean
Continuous (Y.φ i).symm
```

Prove that the relevant face points lie in `(Y.φ i).target`, or use the target subtype. The construction above accommodates this explicitly. The supplied snippets do not themselves establish that membership lemma.

Finally:
```lean
noncomputable def chartResidueMeasure
    (μ : ℝ) (c : ℕ) :
    Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ₁.simpleFaces Y ((Ξ₁.X Y).en I) μ c,
    Ξ.faceResidueMeasure Y I J ‹_›
```
The displayed Lean is a signature design, not a claim that these dependent binders elaborate unchanged.

---

# 3. Recommended headline theorems

The primary theorem should be:

```lean
theorem chartResidueMeasure_eq_residueMeasure
    {μ : ℝ} (hμ : 0 < μ)
    {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c =
      Ξ.residueMeasure Y hc hzero
```

Then:

```lean
theorem stratumMeasure_eq_smul_chartResidueMeasure
    {μ : ℝ} (hμ : 0 < μ)
    {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero =
      ENNReal.ofReal (residueConst μ c) •
        Ξ.chartResidueMeasure Y μ c
```

If `chartResidueMeasure` is constructed using geometric facts requiring `hc` or `hzero`, include them in its arguments. Do not force hypothesis independence at the price of awkward total definitions.

For the actual uniqueness proof, the second theorem is closest to your existing API:

- Set `ν' := ofReal (residueConst μ c) • chartResidueMeasure`.
- Prove regularity.
- Prove its smooth-test formula.
- Apply `eq_stratumMeasure_of_tests`.
- Cancel the positive normalization to obtain the first theorem.

No new uniqueness theorem is necessary.

---

# 4. Local finiteness and regularity: the real proof obligation

Your concern is correct: a face density need not be globally integrable. But removing \(D_{c+1}\) is intended to remove the additional active-wall singularities.

That observation must become a lemma; it is not supplied merely by `J ∈ simpleFaces`.

## Preferred geometric lemma

For every compact \(C\subset X\), prove
\[
\int_{e_{p,J}^{-1}(C)}D_{p,J}\,dq_{p,J}<\infty.
\]

The geometric argument is:

- the selected \(c\) active coordinates vanish;
- an additional vanishing active coordinate would put the image in \(D_{c+1}\);
- on compact subsets of \(X\), the dangerous remaining active coordinates therefore stay away from zero, **provided the weighted chart parameter region has the needed compactness/properness control**;
- the F-free amplitude is bounded on the relevant region;
- inactive coordinates have no negative phase exponent.

The compactness/properness qualification matters. Compactness of \(C\) alone does not make the inverse image under an arbitrary continuous map compact. Audit the chart-box closure, chart-target containment, and support of the chart weights.

If those facts are already available, this is a direct local estimate.

## Alternative: positive cutoff domination

For a compact \(C\subset X\), choose a nonnegative smooth admissible cutoff \(\chi\) with \(\chi\ge1\) on \(C\). Prove
\[
\lambda_{p,J}(e^{-1}(C))
\le
\int \chi(e(q))D_{p,J}(q)\,dq
<\infty.
\]

This can reuse integrability estimates behind the existing face-integral theorem.

**Avoid a circular shortcut:** a Lean equality between real-valued Bochner integrals does not itself establish integrability. Nonintegrable real integrals are totalized. You need an actual `Integrable` lemma or an ENNReal `lintegral < ∞` statement.

My recommendation is to make the following a named infrastructure theorem:
```lean
faceDensity_integrable_mul_test
```
for admissible smooth tests, with a nonnegative-cutoff corollary giving compact finiteness.

After obtaining local finiteness, use the locally compact/second-countable or sigma-compact regularity infrastructure appropriate to `stratumOpen c`. Check the exact mathlib theorem signature in the checkout; do not make the design depend on the guessed spelling of `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.

**Do not infer regularity simply from “continuous pushforward.”** Without the appropriate finiteness/properness hypotheses, that is not a sufficient argument.

---

# 5. Integral bridge

Prove an ENNReal pushforward formula first:
\[
\int_X^{\!\!-} H\,dm_{p,J}
=
\int^{\!\!-}_{q:\,e(q)\in X}
H(e(q))\,\operatorname{ofReal}(D_{p,J}(q))\,dq.
\]

This is the clean measure-object theorem and does not require integrability.

Then prove, for admissible \(G\),
\[
\int_X G\,dm_{p,J}
=
\int_s
\operatorname{dlogResidueInt}
\bigl(k^A,h^A,\mu,a,J,
((\Xi.\mathrm{withF}\ G).\mathrm{amp}\ p).s\bigr)
\,d\beta_p(s).
\]

The restriction to \(X\) disappears on the right because the extended test vanishes on the removed deeper set. Include the chart-domain support argument if the definition also restricted to valid chart parameters.

Proof ingredients:

1. `integral_map` on the valid measurable map;
2. the `withDensity` integral formula;
3. integrability established separately;
4. Fubini for `βp.prod (volume.restrict box)`;
5. the amplitude factorization;
6. unfolding `dlogResidueInt`;
7. finite summation.

This is the bridge that turns the already-existing test formula into the new measure identity.

---

# 6. Scope, canonicity, and extremality

## Canonical where?

The explicit finite sum on \(X\) becomes canonical **after** the equality theorem: it is independent of transport, chart subdivision, orthant enumeration, and auxiliary weights because it equals \(\mathcal R^\mu_c\).

A raw all-face measure on \(U\):

- may fail to be locally finite near \(D_{c+1}\);
- is not identified by the existing test theory on \(X\);
- should not be advertised as a canonical Radon measure on all of \(U\).

There is nevertheless a canonical Borel measure extension of \(\mathcal R^\mu_c\) to \(U\) by inclusion \(X\hookrightarrow U\), assigning zero mass to the complement. It may fail to be locally finite at the deleted set. Distinguish this **extension by zero** from an independently defined raw chart sum; proving they agree is a separate statement.

## Which normalization?

Define the explicit density measure as \(\mathcal R\). This avoids carrying \(\Gamma(\mu)/(c-1)!\) inside every face density and makes the residue interpretation transparent.

State both headline equalities. The \(\nu\)-version aligns with the RMK uniqueness API; the \(\mathcal R\)-version aligns with Definition B.

## Does this need extremality?

**No additional extremal-index hypothesis should be introduced.** Work under the same `hc`, `hzero`, and positivity hypotheses supporting the existing residue theorem.

If the local-finiteness proof unexpectedly needs extremality, first investigate whether a geometric localization or integrability lemma is missing. Do not silently narrow the general theorem.

---

# 7. Unit list and costs

| Unit | Deliverable | Cost |
|---|---|---:|
| 1 | F-free context; invariance of geometry and base measures under `withF`; amplitude factorization | S–M |
| 2 | Face parameter spaces, product reference measures, valid-domain maps to \(X\), measurability | M |
| 3 | Nonnegative face densities and actual `faceResidueMeasure` / finite chart sum | S–M |
| 4 | Local face integrability, compact finiteness, local finiteness and regularity | **M–L** |
| 5 | ENNReal pushforward formula and real smooth-test integral bridge | M |
| 6 | Equality with \(\nu\) and \(\mathcal R\); inherited support and transport independence | S |
| 7, optional | Monomial specialization with \(2^{m_*}/\prod_J2k_j\) | M |

**Overall P1:** M–L if existing face estimates expose the needed integrability and chart-support facts; otherwise L. Unit 4 is the gating audit.

Recommended order:

1. Correct the artifact’s A/B wording immediately.
2. Audit the prerequisites for Unit 4.
3. Implement P1, Units 1–6.
4. Add P2 as the concrete normalization/regression example.
5. Defer P3 and P4.

P2 is a good first theorem only if the general chart-domain/local-finiteness audit reveals genuinely missing infrastructure. It should not replace P1 merely because the scalar monomial formula is already explicit.

---

# 8. Paper/artifact wording

After P1, the justified paper sentence is:

> On \(X=U\setminus D_{c+1}\), the intrinsically defined normalized residue measure is exactly the finite sum of the pushforwards of the multiplicity-normalized simple-face densities in any resolved chart transport. Equivalently, it is the sum over normal sides of the iterated logarithmic density residue of \((K\circ\pi)^{-\mu}\mu_U\); each normal side contributes a factor \((2k_j)^{-1}\) per wall.

For the formalization status, add:

> The measure identity and its chart-independence are formalized; the terminology of iterated density residues describes the explicit local density formula, rather than invoking a separately formalized manifold-level residue calculus.

Replace the current B passage with something like:

> For a simple-pole density \(\omega\), the ordinary residue along \(E=\{f=0\}\) is the tangential density \((|f|\omega)|_E/|df|\), invariant under replacement of \(f\) by a nonvanishing multiple. Its iterates along transverse walls commute. In the normalization used here, contributions are summed over normal sides and divided by the divisor multiplicity \(2k_j\) at each wall. Thus a full two-sided \(c\)-fold crossing contributes \(2^c/\prod_j2k_j\) times the ordinary iterated density residue.

That fixes both the divergent collar formula and the missing side-count normalization, while making P1 precisely the promised structural unit.