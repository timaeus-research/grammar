## Recommendation

The next programme should **turn the scalar-unit hypothesis into a concrete geometric constructor, and then make its leading coefficient genuinely nonzero**. I would not start variable-strip normalisation or an all-orders theorem yet.

There is also one inexpensive gap worth fixing now: **normalised moments can have negative logarithmic degree**, which CCXXXV currently excludes.

A key qualification for G1 is:

> The existing `adaptedProductDensity_of_fibreConstant` does not automatically give a compact base merely because the chart domain is compact. Its displayed base is the entire foot-condition set, without a domain restriction.

That is the principal interface issue to resolve next.

---

# Q1. Ranking and next 3–5 units

## Ranking

| Rank | Item | Assessment |
|---|---|---|
| 1 | **G1: concrete scalar-chart extraction** | Highest immediate value. It replaces a substantial black-box atlas hypothesis by geometric hypotheses that can actually be verified. Feasible for product domains and normal-independent units. |
| 2 | **G6: positive coefficients** | Converts a possibly zero leading-term certificate into the paper’s genuine leading asymptotic. Also enables pair identification and posterior denominators. |
| 3 | **Missing gap: negative-log ratios** | Very cheap, and necessary for ordinary normalised moments—not an exotic extension. |
| 4 | **G3: symmetric moments, then density identification** | Signed orthant bookkeeping is cheap. Identification with `condTubeNormalMeasure` is a separate, more substantial bridge. |
| 5 | **G2: normal-dependent units** | The main remaining geometric generalisation after G1, but still requires honest control of the transformed domain. Do not hide that problem in a “normalisation lemma.” |
| 6 | **G4: all-orders cell expansion** | Important to the full paper statement, but analytic regularity of the *entire amplitude*, allocation, domain and parameter dependence must first be specified. |
| 7 | **G5: statistical transfer** | High eventual value, but not a small continuation of the deterministic cell programme. Population asymptotics alone do not supply the required empirical/probabilistic hypotheses. |

This is an **implementation ranking**, not a ranking of mathematical importance.

## Proposed five units

1. **CCXXXVI `ScalarChartNormalForm`**  
   Normal exponent parity, positive scalar phase, determinant-to-amplitude algebra.

2. **CCXXXVII `CompactProductChartDensity`**  
   Compact-base restriction and an actual product-domain allocation constructor.

3. **CCXXXVIII `SingleChartScalarAtlas`**  
   A direct single-chart theorem, plus the all-strata atlas constructor under explicit product geometry.

4. **CCXXXIX `PositiveScalarCoefficient`**  
   All-minimal positivity first; nonnegative atlas sums and a strict witness; general-face positivity if the existing face-integral API makes it inexpensive.

5. **CCXL `LogRatioAndSymmetricMoments`**  
   Remove the negative-log obstruction at the limit level; add signed orthant moments. Defer the conditional-measure identification unless its density API is already especially convenient.

For a three-unit programme, land the first three. The fourth is what makes the resulting theorem match “positive leading coefficient.”

---

# Q2. Contracts for G1

The following are **proposed contracts**, not claims about declarations already in the repository. I would keep the algebraic extraction, support geometry, and integration bridge separate.

## Unit 1: `ScalarChartNormalForm`

### A. What `even_positive_form_halfExp` actually supplies

The displayed theorem gives a neighbourhood \(W'\) on which

\[
K(y)=\operatorname{reducedUnit}(u,e,y_0)(y)
       \prod_j y_j^{2\,\operatorname{halfExp}(e,y_0)(j)},
\]

with the reduced unit analytic and strictly positive.

Its proof explicitly obtains

\[
y_{0j}=0\quad\Longrightarrow\quad \operatorname{Even}(e_j).
\]

It does **not** supply:

* positivity of every `halfExp`;
* parity of coordinates nonzero at \(y_0\);
* normal-independence of the reduced unit;
* a prescribed product box contained in \(W'\);
* one uniform neighbourhood covering a previously chosen compact base.

In particular, `hk : ∀ j, 0 < k j` requires the additional fact that every selected normal coordinate is an **active divisor coordinate**, meaning \(e_j>0\).

### Proposed parity wrapper

For a finite set \(I\), assume:

* \(W\) open;
* \(y_0\in W\);
* \(K=u\cdot\operatorname{monomialEval}(\,\cdot\,,e)\) on \(W\);
* \(K\ge0\) on \(W\);
* \(u\) continuous at \(y_0\), with \(u(y_0)\ne0\);
* \(y_{0j}=0\) and \(0<e_j\) for every \(j\in I\).

Conclude, after normal-coordinate reindexing,

```lean
∃ k : Fin I.card → ℕ,
  (∀ a, 0 < k a) ∧
  (∀ a, e (normalIndex a) = 2 * k a)
```

Use `even_exponent_of_nonneg` directly for this wrapper. The analytic reduced-unit theorem is stronger than necessary.

**Pitfall:** parity follows from a two-sided open neighbourhood, not merely from nonnegativity on a positive orthant or on the divisor itself.

### B. Scalar phase extraction

Write \(\Psi(z,n)\) for the coordinate split. Assume on the relevant product:

\[
K(\varphi(\Psi(z,n)))
 =
u_T(z)
\left(\prod_{j\notin I}z_{\tau(j)}^{e_j}\right)
\left(\prod_{j\in I}n_{\nu(j)}^{e_j}\right).
\]

Define

\[
q(z)=u_T(z)\prod_{j\notin I}z_{\tau(j)}^{e_j}.
\]

The algebraic contract should conclude

\[
K(\varphi(\Psi(z,n)))=q(z)\prod_a n_a^{2k_a}.
\]

Keep a separate lemma for continuity of \(q\).

### C. Positivity of \(q\)

Do not try to prove this by evaluating at \(n=0\): that only gives \(K=0\).

A clean contract is:

* \(q(z)\ne0\) on the base;
* \(K\ge0\) on the product;
* the normal box contains a point \(n_*\) whose coordinates are all nonzero;
* the scalar phase identity holds there.

Then

\[
0\le K(\varphi(\Psi(z,n_*)))
   =q(z)\underbrace{\prod_a n_{*a}^{2k_a}}_{>0}
\]

implies \(q(z)>0\).

For an \(\varepsilon\)-ball in the `Fin` sup norm, take every coordinate of \(n_*\) to be \(\varepsilon/2\).

To prove \(q(z)\ne0\), use:

* the unit is nonvanishing;
* each tangential coordinate with \(e_j>0\) is nonzero, typically from \(|z_j|\ge\varepsilon\).

Coordinates with \(e_j=0\) need no lower bound.

This formulation also handles the case where the original unit itself is negative and a tangential monomial contributes the compensating sign.

### D. Jacobian/amplitude extraction

If the Jacobian normal form is

\[
|\det D\varphi(\Psi(z,n))|
 =
|v(z,n)|
\prod_{\text{tangential }j}|z_j|^{h_j}
\prod_{\text{normal }a}|n_a|^{h_a},
\]

the scalar amplitude must include the tangential factor:

\[
A(z,n)=
|v(z,n)|
\prod_{\text{tangential }j}|z_j|^{h_j}
\,p(\varphi(\Psi(z,n)))\,F(\varphi(\Psi(z,n))).
\]

Your proposed \(A=|v|pF\) is correct only if the tangential Jacobian monomial has already been absorbed into \(v\), the adapted amplitude, or the base weight.

The resulting contract is exactly the `hamp` needed by CCXXXIII.

**Allocation bookkeeping:** if `Ad.beta` carries allocation, do not multiply allocation into \(A\) again.

### E. Local versus global continuity

CCXXXI and CCXXXIII currently require

```lean
Continuous q
Continuous (Function.uncurry A)
```

on the whole ambient Euclidean spaces.

A Hironaka chart generally gives continuity only on its chart neighbourhood. Thus G1 also needs an explicit policy:

1. initially assume globally continuous representatives agreeing on the relevant compact product; or
2. add a compact-product extension lemma and construct such representatives.

For the second route, continuity on a neighbourhood of

\[
T\times\overline{B_\varepsilon(0)}
\]

is sufficient for real-valued extension from that compact set. Equality is required only on the integration set. Positivity of the extension away from \(T\) is unnecessary.

Do not silently turn `ContinuousOn` into `Continuous`.

---

## Unit 2: `CompactProductChartDensity`

This is the most important geometric interface unit.

### A. The compact-base issue in the existing constructor

The displayed constructor chooses

\[
B_0=\{z:\Psi(z,0)\in\operatorname{footCondition}(D_i,\varepsilon,I)\}.
\]

That set is generally unbounded. A compactly supported `beta` does not make \(B_0\) compact.

Therefore neither of these arguments is valid:

* “`dom` is compact, so `Ad.base` is compact”;
* “allocation vanishes outside `dom`, so `Ad.base` is compact.”

The support and the chosen base are different objects.

### B. Add a compact-base restriction operation

A useful independent contract is:

> Given an adapted product density on base \(B_0\), a measurable compact \(T\subseteq B_0\), and
> \[
> \beta=0\quad\text{a.e. on }B_0\setminus T,
> \]
> construct an adapted product density with base \(T\), the same normal box and amplitude, and the same represented density a.e.

Then prove the corresponding integral identity.

This should be stated in the language of the actual `AdaptedProductDensity` fields, but its mathematical content is support truncation, not a new disintegration theorem.

### C. The proposed tangential projection

Let \(C\) be a compact chart-domain carrier and \(\pi_T\) the tangential projection. Define

\[
T=
\pi_T(C)\cap
\{z:\Psi(z,0)\in\operatorname{footCondition}(D_i,\varepsilon,I)\}.
\]

Then \(T\) is compact provided the foot-condition set is closed. Prove that from its coordinate inequalities; if its implementation includes strict inequalities, use an appropriate closed carrier instead.

Two qualifications matter:

1. If `dom` is open or half-open, its projection need not be compact. Use a compact closure/carrier.
2. This formula proves compactness, **not product reconstruction**.

For a general compact \(C\),

\[
C\cap\operatorname{sizePiece}
\ne \Psi(T\times B_\varepsilon(0))
\]

in general. A disc or sloping boundary already defeats that equality.

Thus projection is the right compactness device, but an independent fibre/product hypothesis remains necessary.

### D. Honest allocation contracts

Offer two constructors.

#### Constructor 1: explicit fibre-constant hypothesis

Retain the displayed `hfc`, and add the compact support/truncation hypothesis needed above.

This is honest and useful, but still conditional.

#### Constructor 2: product-domain allocation

Assume, at least a.e.,

\[
\operatorname{allocation}_i(\Psi(z,n))
 =
\mathbf 1_{\mathrm{dom}}(\Psi(z,n))\,\rho_T(z),
\]

and on the size piece,

\[
\mathbf 1_{\mathrm{dom}}(\Psi(z,n))
 =
\mathbf 1_T(z)\mathbf 1_{B_\varepsilon}(n).
\]

Then use

\[
\beta(z)=\mathbf 1_T(z)\rho_T(z).
\]

For a single chart with allocation weight \(1\), this reduces to \(\beta=\mathbf 1_T\), or to constant \(1\) after restricting the adapted base to \(T\).

**Important:** “one chart, \(\rho\equiv1\)” does not by itself establish fibre constancy. The allocation can still contain the chart-domain indicator. Product geometry is what makes that indicator fibre-constant on the selected size piece.

Use a.e. statements where closed/open box boundaries differ; do not prove false pointwise identities at \(|y_j|=\varepsilon\).

---

## Unit 3: `SingleChartScalarAtlas`

### A. Piece constructor

Combine the preceding units into a theorem with hypotheses:

* nonempty active normal set \(I\);
* an actual product-domain allocation identity;
* a compact tangential carrier and integrable tangential weight;
* scalar phase extracted from the monomial chart;
* Jacobian/amplitude identity;
* continuous representatives on the compact product;
* normal box equal to the required \(\varepsilon\)-ball.

Conclusion:

```lean
FiniteScalarUnitAtlas
  (d - I.card)
  (R.pieceIntegral D ε i I F K p)
```

with a companion formula identifying each cell’s `lam` and `mult`.

Reuse:

* `even_exponent_of_nonneg`;
* `even_positive_form_halfExp` when the positive reduced-unit form is useful;
* `adaptedProductDensity_of_fibreConstant`, followed by base restriction, or a new product constructor;
* `pieceIntegral_eq_symIntegral`;
* `pieceAtlas`;
* `pieceAtlas_cell_lam`;
* `ScalarUnitCell.symAtlas`.

### B. All-strata constructor

For a **single centred product chart**, let \(J\) be the active divisor coordinates and assume the original unit is independent of **all coordinates in \(J\)**.

For a stratum \(I\subseteq J\), the other active coordinates become tangential, and

\[
q_I(z)=u_T(z_{\mathrm{nondiv}})
       \prod_{j\in J\setminus I} z_j^{e_j}.
\]

It is normal-independent for that stratum. On its base, the factors indexed by \(J\setminus I\) are bounded away from zero.

This global normal-independence assumption is stronger than independence for one selected \(I\), but it is exactly what makes the all-strata constructor automatic.

Build the atlas for every nonempty \(I\); reuse CCXXVI for \(I=\varnothing\); then apply the existing per-piece-dimension assembly theorem.

---

# Q3. A cheaper unconditional theorem

**Yes—and there are two versions.**

Here “unconditional” should mean **no unresolved finite-atlas or adapted-density existence hypothesis**, not “no geometric hypotheses.”

## Cheapest: integrate the whole centred product chart directly

Suppose the active divisor set is \(J\ne\varnothing\), the domain is a product

\[
T\times(-b,b)^J,
\]

and

\[
K\circ\varphi=q(z)\prod_{j\in J}n_j^{2k_j},
\qquad
\text{pulled-back weighted density}
 =\beta(z)A(z,n)\prod_{j\in J}|n_j|^{h_j}.
\]

Assume the established compactness, integrability, continuity and positivity conditions.

The **whole chart integral is one symmetric scalar cell**. Apply `symAtlas` directly.

No size-stratum decomposition is needed to prove its leading term. The region being integrated already contains all size strata.

This is the cheapest concrete theorem now available. Its atlas has \(2^{|J|}\) orthant cells, rather than a separate atlas for every size stratum.

## More infrastructurally valuable: certify every size piece

The all-strata constructor above proves that the existing resolved decomposition pipeline applies to this chart. This is slightly more work but tests precisely the interface that remains conditional in the paper theorem.

I would land both:

1. direct product-chart leading term;
2. equality/compatibility with the all-strata assembly.

`coeff_unique` then identifies the resulting coefficients whenever both certificates use the same scale.

### Scope warning

A single chart theorem gives the original Boltzmann integral only if an existing change-of-variables/allocation theorem identifies that original integral with this chart integral. A local chart with an existential region is not automatically a global single-chart cover.

Also, the exponent pair becomes the **actual** leading pair only after proving the coefficient nonzero.

---

# G6: the fourth unit should establish genuine positivity

For the all-minimal case, CCXXXIV gives a particularly clean contract.

Assume:

* all ratios equal `c.lam`;
* \(\beta_w\ge0\) a.e. on the base;
* \(A(z,0)\ge0\) a.e. on the base;
* a positive-measure set on which
  \[
  \beta_w(z)>0,\qquad A(z,0)>0.
  \]

Then `c.coeff > 0`.

All prefactors are positive: \(b>0\), \(q>0\), \(\lambda>0\), \(\Gamma(\lambda)>0\), positive factorial and positive \(k_j\).

Two corrections to the informal G6 formulation:

* Nonnegative \(\beta_w\) plus \(A(z,0)>0\) on a positive-volume set is insufficient: \(\beta_w\) may vanish there.
* Positivity somewhere does not prevent cancellation elsewhere unless the coefficient integrand is nonnegative a.e.

An equivalent formulation is positivity of \(A(z,0)\) on a set of positive \(\beta_w\,dz\)-measure.

For general ratios, the critical face retains the nonminimal normal coordinates. Do not reuse the all-minimal origin formula. Either prove positivity directly from the general face integral, or use a nonnegative lower-comparison cell with the same extremal pair.

At atlas level, prove:

> All tied coefficients are nonnegative, and one tied coefficient is positive  
> \(\Longrightarrow\) the tied sum is positive.

This is the proper positivity theorem for partition functions. Signed observable numerators remain a different story.

---

# Q4. Audit of CCXXXI–CCXXXV

From the displayed statements, I see **no demonstrated mathematical error**. I do see several scope qualifications worth recording explicitly.

## 1. Scalar scaling is correct

Positive time change gives

\[
a^{-\lambda}c,
\]

with no extra leading factor from the logarithm, since
\(\log(aN)/\log N\to1\).

No continuity of \(q\) is needed for the pointwise theorem. Compact-base integration legitimately needs uniform control, supplied here by continuity and positivity on the compact base.

## 2. Symmetric orthant decomposition is correct in form

Reflection preserves the phase because its exponents are even, and absolute density powers introduce no signs.

The orthants overlap only on null coordinate hyperplanes. For arbitrary real \(N\), bounded-box integrability is still plausible from continuity; exponential decay is not needed on a bounded domain.

The `Metric.ball`/cube identification uses the standard sup norm on finite `Pi` spaces. It would not be the same statement for a Euclidean \(\ell^2\) ball.

## 3. CCXXXIII remains a bridge, not an extraction theorem

Its statement honestly assumes:

* an adapted product density;
* compact base;
* integrable base weight;
* the exact normal box;
* scalar phase and amplitude identities.

It does not establish those properties for a general monomial chart. In particular, the displayed fibre-constant constructor does not visibly discharge compactness.

## 4. Coefficient uniqueness is not nonvanishing

`tiedCoeff_eq` proves decomposition independence at the **specified common dominating scale**. It remains valid if both coefficients are zero, or the scale is strictly above the actual leading scale.

Thus it is not, by itself, an atlas-independent identification of the actual leading pair. `pair_unique` correctly requires nonzero coefficients.

## 5. The all-minimal coefficient has a useful simplification

When all ratios equal \(\lambda\),

\[
h_j+1=2k_j\lambda,
\]

so

\[
b^{\sum h_j+r}(b^{2\sum k_j})^{-\lambda}=1,
\qquad r=n+1.
\]

The displayed unsimplified formula is therefore consistent. A simplification lemma would be useful.

For a symmetric cell in the all-minimal case, every reflection has the same origin amplitude. Its coefficient is consequently \(2^r\) times the positive-orthant coefficient. Do not attribute the displayed `c.coeff` formula directly to `c.symIntegral` without that orthant sum.

## 6. The important CCXXXV restriction: negative log powers

`HasLeadingTerm.div` is correct under `k₂ ≤ k₁`, but that hypothesis excludes common moments.

For example, with two normal coordinates, \(h=(0,0)\), \(k=(1,1)\), inserting \(u_1^2\) changes:

* denominator pair: \((\lambda,\text{log degree})=(1/2,1)\);
* numerator pair: \((1/2,0)\).

The normalised moment is of order \(1/\log N\). Your `hdeg` does not cover it.

The cheapest repair is **not necessarily** a new integer-indexed `HasLeadingTerm`. First prove an unrestricted ratio limit using the quotient of existing scales:

\[
\frac{Z_1(N)/Z_2(N)}
     {s_{\lambda_1,k_1}(N)/s_{\lambda_2,k_2}(N)}
\longrightarrow \frac{c_1}{c_2}.
\]

Then expose an integer-log-degree corollary if wanted. This avoids unnecessary subtraction arithmetic in the foundational API.

Finally, signed symmetric moments require the orthant multiplier

\[
\prod_j(-1)^{\sigma_j\alpha_j}.
\]

Their leading coefficients can cancel. A zero signed certificate does not identify the next nonzero term.

---

## Bottom line

The next milestone should be:

> **A concrete product monomial chart with normal-independent unit produces its scalar atlas, with no assumed adapted-density or atlas existence; nonnegative positive-mass data then give a strictly positive leading coefficient.**

That is reachable with the existing analytic kernel machinery. The real remaining work is compact support, product geometry and allocation—not another asymptotic kernel theorem.
