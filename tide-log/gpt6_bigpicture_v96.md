## Executive recommendation

The programme is on track, but there are two important corrections.

1. **The clamped observable is analytic near the origin; the `max`-clamped prior need not be.** The producer is still valid because the coefficient certificate needs an analytic representative of the density on the positive box, not necessarily the Taylor series of the globally truncated prior.
2. **Do not change `CorePresentation.b` to a variable width yet.** On the coordinate model there is a finite, a.e.-disjoint decomposition into *curved, normalised boxes with fixed normal side*. A “water-filling” construction resolves the apparent conflict between normalisation and disjointness.

My recommended next sequence is:

> parameterised diagonal-rescaling producer → water-filling collar → compact-box analytic producer → compatibility-backed geometric interpretation.

The first two should already produce a substantial theorem beyond the deepest-stratum example.

---

# 1. Audit of what landed

This is an audit of the supplied statements and descriptions, not an independent inspection of commit `cfcd013`.

## 1.1 CCCXVI: the refactor is mathematically appropriate

The move from exact-sublevel partitions to

\[
\mu=\sum_I\mu_I+\mu_{\mathrm{tail}},
\qquad K\geq\delta_0>0\quad\mu_{\mathrm{tail}}\text{-a.e.}
\]

is the right primary interface.

In particular:

- the moment representation genuinely needs only the core transport;
- a residual belongs in the **exact** representation;
- the residual disappears from the algebraic-logarithmic asymptotic expansion because it is exponentially small;
- the old adapted-sublevel construction is correctly an adapter, not the definition of the general interface.

Keep the distinction between `Z_eq`, which is true by the definition of `resid`, and `resid_eq`/`resid_bound`, which carry the substantive measure-decomposition content.

## 1.2 CCCXVIII: honest producer, with one headline correction

### The observable clamp is legitimate

For \(r=(b+b')/2\), coordinatewise clamp agrees with the identity on the open sup-norm ball of radius \(r\). Thus the clamped observable:

- agrees with the original series on the integration region;
- agrees with it on a neighbourhood of \(0\);
- has precisely the intended normal jets;
- has the required power-series presentation on a ball larger than the normal box.

This is an entirely legitimate extension device.

It is nevertheless worth exporting an **extension-independence lemma**: two observables with the same analytic germ near \(0\) and the same values on the region give the same certificate-level integral and jets. That makes the role of the extension explicit.

### The prior needs a correction in the prose

The statement

> “Prior and observable … are analytic at \(0\) on the larger ball”

is false for the prior in the stated generality.

For example, a prior series \(f(u)=u_1\) is nonnegative on the positive box, but
\[
\max(f(u),0)=\max(u_1,0)
\]
is not differentiable at \(0\).

What is true is:

- `prior` is globally continuous and nonnegative;
- it agrees with the analytic series on the positive box;
- that series is an analytic extension of its **positive-box restriction**;
- `cc = fϕ` is the density’s analytic representative for the amplitude identity, not necessarily the jet family of the globally defined truncated prior.

That is sufficient for the supplied certificate statements. Do not later silently reinterpret `cc` as `jetFamily prior`.

**Suggested headline edit:**

> “Prior and observable are globally continuous and agree with the series on the region. The observable is analytic on the larger normal ball; the prior restriction has the supplied analytic series representative.”

### The null tail is legitimate

Yes. A zero tail is a valid special case, and its phase-gap condition is correctly vacuous. Here the nontrivial fact is the **exact measure transport and null-boundary argument**, not the gap.

Describe it as a “null-tail coordinate-box producer”, not as evidence that the geometric collar problem has already been solved.

### Scope

The theorem really produces a certificate from series data. That is a substantial advance.

It does not yet produce:

- charts from arbitrary analytic geometry;
- a collar covering several strata;
- density compatibility with a resolved Jacobian;
- an identification of the supplied normal data with genuine geometric normal derivatives.

Your supplied rows mostly respect these boundaries.

## 1.3 CCCXIX: gate 2 passed, but one gate remains

`continuous_datum` is exactly the functional-analytic gate I intended:

\[
x\longmapsto \operatorname{ofFamilies}(b,0,f_x)
\]

is continuous in the **actual weighted \(\ell^1\) datum topology**, not merely coefficientwise.

The uniform majorant is a legitimate input to this theorem. It is not a disguised certificate hypothesis.

There is, however, a separate production step:

> derive a uniform coefficient majorant on a smaller normal radius from analytic geometric data on a compact parameter set.

CCCXIX does not do that step, and should not claim to.

The parenthetical phrase

> “the real form of a uniform analytic extension/bound on a larger normal polydisc”

is acceptable as motivation, but not as an equivalence theorem. A uniformly bounded holomorphic extension yields such a majorant **after shrinking the radius**. The shrink is essential.

### Small API observations

- Consider adding an explicit `M_nonneg` field, or exporting it when `X` is nonempty. The existing definition is mathematically fine, but empty parameter spaces otherwise make positivity of the chosen majorant unavailable.
- Positivity of the radius could be packaged in a separate “usable analytic family” structure. Repeating it in elementary lemmas is not a design error.
- The global condition `CoreNormalMomentPresentation.c_le : ∀ q, ...` is stronger than the integration argument needs. A bound on the supported normal box would suffice. This is a convenience restriction, not a mathematical defect, and bounded extensions can currently work around it.

---

# 2. Unit 3: the parameterised normal-rescaling producer

I would implement this first for a nonempty coordinate subset \(I\), with \(m=|I|\), and only afterwards instantiate it with the collar below.

Let
\[
E=\mathbb R^d,\qquad
S_I=\{w:w_i=0\iff i\in I\},
\]
and choose enumerations of \(I\) and its complement. Write the corresponding coordinate isometry as
\[
P_I:\mathbb R^{d-m}\times\mathbb R^m\longrightarrow E.
\]

A compact base \(B\subset S_I\) is identified with a compact subset \(\bar B\subset\mathbb R^{d-m}\).

## 2.1 The base measure is not arbitrary

For transport to ambient Lebesgue measure, take

\[
\nu_B=(\text{coordinate Lebesgue measure restricted to }\bar B)
\]

transported to the subtype \(B\).

An arbitrary finite `ν_B` does **not** give ambient Lebesgue measure on the image. It gives the corresponding product-pushforward measure.

This distinction should be reflected in two APIs:

1. a general finite-base-measure rescaling producer;
2. its coordinate-Lebesgue transport specialization.

The \(m=d\) case uses zero-dimensional Lebesgue measure, hence a Dirac base. It is not a separate geometric exception.

## 2.2 The map and normalisation

Allow orthant signs \(\sigma_i\in\{-1,1\}\). Let \(\lambda_i:B\to(0,\infty)\) be continuous and set

\[
\Phi(s,v)=s+\sum_{i\in I}\sigma_i\lambda_i(s)v_i e_i.
\]

With
\[
t(s)=\prod_{j\notin I}s_j^{2k_j},
\]
require
\[
t(s)\prod_{i\in I}\lambda_i(s)^{2k_i}=\beta.
\]

Then
\[
K(\Phi(s,v))=\beta\prod_{i\in I}v_i^{2k_i}.
\]

For the generic unit-3 theorem, make this identity a hypothesis about the scaling functions, and provide constructors:

- symmetric splitting;
- one-coordinate absorption;
- the collar-specific splitting of §3.

There is no universally best splitting. **The collar geometry should determine the splitting**, rather than selecting symmetric splitting prematurely.

## 2.3 Density and amplitude

For ordinary prior-weighted Lebesgue measure, \(h_i=0\), and

\[
J(s)=\prod_{i\in I}\lambda_i(s),\qquad
c(s,v)=J(s)\,\varphi(\Phi(s,v))
\]
on the normal box.

Suppose the original normal series are
\[
\varphi\!\left(s+\sum_{i\in I}z_i e_i\right)
 =\sum_\gamma a_\gamma(s)z^\gamma,
\quad
\phi\!\left(s+\sum_{i\in I}z_i e_i\right)
 =\sum_\gamma f_\gamma(s)z^\gamma.
\]

Then the normalised density coefficients are

\[
a^\sharp_\gamma(s)
 =J(s)a_\gamma(s)\prod_i(\sigma_i\lambda_i(s))^{\gamma_i},
\]

the observable coefficients are

\[
f^\sharp_\gamma(s)
 =f_\gamma(s)\prod_i(\sigma_i\lambda_i(s))^{\gamma_i},
\]

and the amplitude coefficients are

\[
g^\sharp_\gamma(s)
 =J(s)(a\star f)_\gamma(s)
       \prod_i(\sigma_i\lambda_i(s))^{\gamma_i}.
\]

**The Jacobian factor \(J(s)\) is missing from the amplitude formula proposed in Q2.**

If the measure has an additional factor \(\prod_i|w_i|^{h_i}\), then the normal Jacobian multiplier is instead

\[
J_h(s)=\prod_{i\in I}\lambda_i(s)^{h_i+1},
\]
with tangential factors \(\prod_{j\notin I}|s_j|^{h_j}\) placed either in the base measure or in the density coefficients.

## 2.4 Exact series hypotheses

A good direct producer hypothesis is:

- `Fprior Fobs : UniformSeriesFamily B m ρ`;
- \(0<\rho\);
- their evaluations agree with the prescribed prior and observable on the centred normal neighbourhood \(|z_i|<\rho\);
- the prior is nonnegative on the intended physical image;
- \(L_i\) bound \(\lambda_i\) on \(B\);
- \(0<b<b'\), with
  \[
  b'L_i<\rho \quad\text{for every }i.
  \]

A common radius is convenient, not mathematically necessary.

Rescaling the majorants gives

\[
M^\sharp_\gamma=M_\gamma\prod_i L_i^{\gamma_i},
\]
and for the density include an upper bound for \(J\).

CCCXIX then supplies continuity of the amplitude datum and uniform bounds. CCCXVII supplies its evaluation and observable jet identities.

For `cBound`, either:

- improve the field to a bound on the supported box; or
- define `c` off that box using a bounded clamped analytic representative.

Only `c`’s values on the chart measure matter. It need not equal `prior ∘ Φ` globally.

By contrast, `obsFibre` is fixed by `D.obs` and `Φ`. Its actual values must agree with the analytic representative on the larger normal ball. Merely knowing observable equality on the positive box is not enough to discharge `HasFPowerSeriesOnBall`.

## 2.5 Transport: use fibrewise linear change of variables first

The simplest proof does **not** differentiate the subtype-valued base or the function \(s\mapsto\lambda(s)\).

For fixed \(s\), use the invertible diagonal linear map
\[
L_s(v)_i=\sigma_i\lambda_i(s)v_i.
\]

Prove

\[
(L_s)_*
 \left(J(s)\,dv\big|_{(0,b]^m}\right)
 =
 dz\big|_{L_s((0,b]^m)}.
\]

Then:

1. integrate this identity over coordinate Lebesgue measure on \(\bar B\);
2. use the coordinate split \(P_I\), whose determinant has absolute value \(1\);
3. insert the prior by `withDensity` naturality;
4. identify the resulting measure with the ambient restriction to the image.

A useful intermediate declaration is schematically:

```lean
theorem map_diagonalBox_withDensity
    (hλ : ∀ i, 0 < λ i) :
    Measure.map (signedDiagonal σ λ)
      ((volume.restrict (piBox m (Ioc 0 b))).withDensity
        (fun _ => ENNReal.ofReal (∏ i, λ i))) =
    volume.restrict
      (signedDiagonal σ λ '' piBox m (Ioc 0 b))
```

Then a parameterised version using `lintegral_prod`.

This needs continuity/measurability of the scaling, not its differentiability.

### Alternative full-dimensional route

On an ambient tangential neighbourhood, extend the scaling and use

\[
F(z,v)=P_I(z,L_zv).
\]

Its derivative is block triangular, so

\[
|\det DF|=\prod_i\lambda_i(z).
\]

Now `map_withDensity_abs_det_fderiv_eq_addHaar` applies to the corresponding full-dimensional measurable subset. This is useful later for tubular charts, but is more work than necessary for unit 3.

**Do not apply the Haar Jacobian theorem directly to `Base × ℝ^m`.** That subtype product is not the ambient vector space appearing in its hypotheses.

## 2.6 Existing machinery to reuse

- **Reuse directly:** coordinate splits, `UniformSeriesFamily`, convolution, clamp evaluation, and the core/moment constructors.
- **Variable-unit results:** use as an independent leading-term comparison theorem. They do not construct an exact monomial-phase `CorePresentation` and do not supply the full expansion.
- **`ProductMonomialChartVar`:** useful input for a later resolution-cover producer, but its continuous units and amplitudes are insufficient for the analytic all-orders producer.
- **`TubularJacobian`:** relevant when replacing the coordinate split with a genuine tubular parametrisation. First add its measure-valued counterpart using the audited Mathlib Jacobian theorem.

---

# 3. Unit 4: a finite normalised collar without changing `b`

Here is the construction I recommend. It gives an exact-sublevel collar modulo null sets, even though its individual images are curved.

For clarity first take
\[
W=[0,a]^d,\qquad a>0,\qquad d>0,
\]
and \(k_i>0\). Put
\[
y_i=w_i^{2k_i},\qquad A_i=a^{2k_i}.
\]

Choose \(\delta>0\) sufficiently small that

\[
\delta^{1/d}<\min_i A_i.
\]

Further smallness for analyticity will be imposed in unit 5.

## 3.1 Bases and widths

For every nonempty \(I\subseteq\{1,\ldots,d\}\), let \(m=|I|\). On the complement coordinates define

\[
t_I(s)=\prod_{j\notin I}s_j^{2k_j},
\qquad
q_I(s)=\left(\frac{\delta}{t_I(s)}\right)^{1/m}.
\]

Define the base

\[
B_I=
\left\{
s\in W:
\begin{array}{l}
s_i=0 \quad(i\in I),\\
s_j>0 \quad(j\notin I),\\
s_j^{2k_j}\ge q_I(s)\quad(j\notin I)
\end{array}
\right\}.
\]

For \(I=\{1,\ldots,d\}\), use the singleton origin and \(t_I=1\).

These bases are compact subsets of the **exact** strata. To prove compactness without divisions at zero, express the complementary inequalities as

\[
\delta\le t_I(s)\bigl(s_j^{2k_j}\bigr)^m.
\]

Together with the compact-box constraints, these are closed conditions and force every complementary coordinate away from zero.

They need not be products of intervals. That is harmless: `CorePresentation` accepts a compact base with an arbitrary finite measure.

For \(i\in I\), put

\[
\ell_{I,i}(s)=q_I(s)^{1/(2k_i)}.
\]

Choose

\[
b_I=\delta^{1/(2\sum_{i\in I}k_i)},
\qquad
\lambda_{I,i}(s)=\frac{\ell_{I,i}(s)}{b_I}.
\]

Then

\[
t_I(s)\prod_{i\in I}\lambda_{I,i}(s)^{2k_i}
=
\frac{t_I(s)q_I(s)^m}
     {b_I^{2\sum_{i\in I}k_i}}
=1.
\]

Thus **all cores have \(\beta=1\)**, with the existing fixed side \(b_I\).

Their physical images are

\[
C_I=
\left\{
w:
\begin{array}{l}
s=\operatorname{zeroOn}(I,w)\in B_I,\\
0<w_i\le \ell_{I,i}(s)\quad(i\in I)
\end{array}
\right\}.
\]

Each image lies in \(\{K\le\delta\}\).

## 3.2 Why these pieces cover

Suppose all \(y_i>0\) and \(\prod_i y_i<\delta\). Consider

\[
H_w(q)=\prod_i\max(y_i,q).
\]

Above the smallest \(y_i\), this is continuous and strictly increasing until it reaches \(\delta\). There is a unique relevant threshold \(q\) with

\[
H_w(q)=\delta.
\]

Let

\[
I=\{i:y_i<q\}.
\]

It is nonempty, and

\[
\delta=q^{|I|}\prod_{j\notin I}y_j.
\]

Consequently \(q=q_I(s)\), the complement belongs to \(B_I\), and \(w\in C_I\).

This is the water-filling interpretation: raise the small coordinates in \(y\)-space to a common threshold until the product reaches \(\delta\).

For Lean, one can avoid packaging an algorithm. Prove a finite-order-statistics lemma, or use the intermediate value theorem for `∏ i, max (y i) q` and define `I` afterward.

## 3.3 Disjointness is a.e., exactly as needed

Away from threshold equalities \(y_i=q\), the active set is unique.

If two closed versions of the pieces overlap, at least one normal coordinate lies on its upper boundary:

\[
w_i=\ell_{I,i}(s).
\]

For fixed \(s\), this is a coordinate hyperplane in the normal fibre. Hence it is null by Fubini. There are only finitely many pieces and normal coordinates.

Coordinate zero sets are also null. The positive level set \(K=\delta\) is null; this can be proved by solving for one positive coordinate and applying Fubini.

Thus

\[
\mathbf 1_{\{K\le\delta\}\cap W}
=
\sum_{\varnothing\ne I}\mathbf 1_{C_I}
\quad\text{Lebesgue-a.e.}
\]

Closed bases may therefore be retained. There is no need for discontinuous normal cutoffs or half-open subtypes in the analytic datum.

## 3.4 Tail and measure identity

For
\[
\mu=(dw|_W)\,\varphi(w),
\]
in the `ENNReal.ofReal` sense, set

\[
\mu_I=\mu|_{C_I},
\qquad
\mu_{\rm tail}=\mu|_{\{K>\delta\}}.
\]

Absolute continuity transfers all the Lebesgue null-boundary facts, giving

\[
\mu=\sum_{\varnothing\ne I}\mu_I+\mu_{\rm tail}.
\]

On the tail, \(K\ge\delta\). Take `δ₀ := δ`.

This proves exactly the measure identity needed by `AnalyticCoreDecomposition`.

## 3.5 Why the collar is uniformly thin

The base inequalities imply \(s_j^{2k_j}\ge q_I(s)\). Hence

\[
\delta=t_I(s)q_I(s)^m\ge q_I(s)^d,
\]
so

\[
q_I(s)\le\delta^{1/d},
\qquad
\ell_{I,i}(s)\le\delta^{1/(2k_i d)}.
\]

Every physical normal width therefore tends uniformly to zero as \(\delta\to0\).

This is the key analytic feature. The scaling \(\lambda_{I,i}\) itself need not tend to zero or remain uniformly bounded as \(\delta\) varies; what matters for convergence is

\[
b_I\lambda_{I,i}(s)=\ell_{I,i}(s).
\]

## 3.6 Signed boxes

For \(W=[-a,a]^d\), apply the same construction to

\[
y_i=|w_i|^{2k_i}.
\]

Split into finitely many full orthants, ignoring their null coordinate boundaries. Use the chosen orthant signs in `Φ`.

A simple implementation uses at most

\[
2^d(2^d-1)
\]

pieces, allowing empty bases. Optimising the indexing is not worth delaying the theorem.

### Consequence for the interface

**No variable `b : K → ℝ` is required for this coordinate collar.**

The trick is not to normalise predetermined rectangular size pieces. It is to choose the physical pieces so that the normalised box side is constant.

`ChartStratumPieces` remains useful for splitting and null-set lemmas, but its fixed-\(\varepsilon\) partition should not dictate this producer’s geometry.

---

# 4. Unit 5: the general compact-box producer

I would expose two levels.

## 4.1 First theorem: uniform normal-series input

For each nonempty coordinate subset \(I\), use the compact **closed coordinate face**

\[
X_I=\{s\in W:s_i=0\ (i\in I)\},
\]

not merely the exact stratum, as the parameter space for the initial series.

Assume:

- uniform normal-series families for prior and observable over \(X_I\);
- a positive common radius \(\rho_I\);
- agreement with the actual functions on the centred normal neighbourhood;
- continuity/global measurability sufficient for `LocalisationData`;
- prior nonnegativity on \(W\).

The closed face includes points where additional coordinates vanish. That is intentional: compactness gives a single uniform normal radius before the exact-stratum bases are selected.

Choose \(\delta\) so small that, for every \(I\) and \(i\in I\),

\[
2\,\delta^{1/(2k_i d)}<\rho_I.
\]

Then restrict the families to \(B_I\), rescale them, and choose, for example,

\[
b'_I=2b_I.
\]

Since
\[
b'_I\sup_{B_I}\lambda_{I,i}
=2\sup_{B_I}\ell_{I,i}<\rho_I,
\]
unit 3 applies uniformly.

The theorem constructs:

- the localisation datum;
- the finite collar decomposition;
- all `CoreNormalMomentPresentation`s;
- the resolved certificate against the coordinate normal data;
- its coefficient certificate;
- the coordinate-free expansion;
- the explicit exponential tail bound.

This is a genuine general compact-box producer from **local normal series**, not a single series converging across the entire original box.

## 4.2 Second theorem: analytic-neighbourhood input

There is an important distinction from producer 1:

> Real analyticity on a neighbourhood of the compact box is not enough to expand one Taylor series across the whole box. It **is** enough to produce a sufficiently thin finite collar, after deriving uniform local normal-series bounds.

So the eventual analytic-facing theorem may assume that prior and observable have real-analytic extensions to an open neighbourhood of \(W\).

The missing bridge must prove:

1. continuity of normal Taylor coefficients in the face parameter;
2. a positive uniform normal radius on each compact face;
3. a weighted-\(\ell^1\) coefficient majorant on a smaller radius;
4. evaluation equality on that smaller normal neighbourhood.

A compactness argument with local analytic expansions, followed by radius shrinkage, provides this mathematically. A bounded complex extension plus Cauchy estimates is one implementation route, not a necessary public hypothesis.

**Do not label the uniform-series-input theorem as already deriving this bridge.** It is a clean stopping point if the Mathlib analytic-uniformity work becomes expensive.

### Global extensions

Keep the extension policy explicit. An arbitrary observable specified only on \(W\) has no prescribed ambient normal jets at boundary strata. Either:

- input an analytic representative on a neighbourhood of \(W\), with a suitable global extension; or
- return an expansion for an explicitly chosen extension and prove the integral is the intended regional integral.

For analytic extensions agreeing on a full-dimensional region, uniqueness supplies the expected equality of boundary germs where applicable.

---

# 5. Compatibility layer: what to express, and what not to conflate

There are three different compatibility claims:

1. **SNC geometry:** labelled equations genuinely define the strata and their tangent/normal spaces.
2. **Phase geometry:** the phase is monomial in divisor-adapted coordinates with the stated multiplicities.
3. **Measure geometry:** the density exponents and units genuinely describe the pulled-back measure.

None follows from the present `ResolvedNormalData.Φ_zero` and continuity assumption.

Also, a fourth distinction is essential:

> Frame independence for a fixed tubular germ is not independence from the tubular germ.

Higher derivatives change under nonlinear normal reparametrisation. Only the first derivative becomes canonical from the first-order normal identification alone.

## 5.1 Implementation convention for the field lists

I recommend implementing the first compatibility structures **patchwise in Euclidean resolved charts**, then adding the atlas/global wrapper.

Below:

- `E := Fin d → ℝ`;
- `B` is an already supplied manifold base with model `IB`;
- `Q : LabelledDefiningEquations IB B E m ι`;
- `N : B → Submodule ℝ E` is the concrete normal bundle;
- `S : Set E` is the stratum image;
- `tube : ∀ x, N x → E` is the chosen tubular germ;
- `divisor : Component → Set E`;
- `I : Finset Component`;
- `label : Fin m ≃ ↥I`.

The global wrapper substitutes the appropriate `R.Stratum I`, identifies `D.N I s` with `N s`, and identifies `D.Φ` with `tube`.

This avoids pretending that arbitrary `U` already has Euclidean derivatives or Lebesgue measure.

## 5.2 `SNCNormalCompatibility`

A workable field list is:

```lean
structure SNCNormalCompatibility
    (Q : LabelledDefiningEquations IB B E m ι)
    (S : Set E)
    (divisor : Component → Set E)
    (I : Finset Component)
    (N : B → Submodule ℝ E) where

  label : Fin m ≃ ↥I

  embedding : Embedding Q.emb
  range_emb : Set.range Q.emb = S

  ambient : ι → Set E
  isOpen_ambient : ∀ a, IsOpen (ambient a)
  preimage_ambient :
    ∀ a, Q.emb ⁻¹' ambient a = Q.baseSet a

  equations_zero :
    ∀ a x, x ∈ Q.baseSet a →
      ∀ l, Q.u a l (Q.emb x) = 0

  stratum_eq_zeroSet :
    ∀ a,
      S ∩ ambient a =
        {y | y ∈ ambient a ∧ ∀ l, Q.u a l y = 0}

  divisor_eq_zeroSet :
    ∀ a l,
      divisor (label l).1 ∩ ambient a =
        {y | y ∈ ambient a ∧ Q.u a l y = 0}

  tangent_eq :
    ∀ a x, x ∈ Q.baseSet a →
      LinearMap.range
        (mfderiv IB 𝓘(ℝ, E) Q.emb x).toLinearMap =
      ⋂ l, LinearMap.ker (fderiv ℝ (Q.u a l) (Q.emb x)).toLinearMap

  normal_eq :
    ∀ x,
      N x =
        (LinearMap.range
          (mfderiv IB 𝓘(ℝ, E) Q.emb x).toLinearMap)ᗮ
```

Some coercions in `tangent_eq` will need adjustment to the precise Mathlib types; the mathematical field list is complete.

For a genuine SNC neighbourhood, add exclusion of components not in \(I\):

```lean
  other_divisors_absent :
    ∀ a j, j ∉ I → Disjoint (ambient a) (divisor j)
```

This requires sufficiently small patches in the **exact** stratum. Do not impose it on a neighbourhood of an entire closed stratum containing deeper strata.

### Upgrade derivative units to equation units

The existing `LabelledDefiningEquations.unit` only compares differentials along the base. It does not say the equations cut out the same divisor nearby.

Add an optional stronger record:

```lean
structure DefiningEquationUnitCompatibility ... where
  unit : ι → ι → Fin m → E → ℝ
  contDiffOn_unit :
    ∀ a b l, ContDiffOn ℝ ∞ (unit a b l)
      (ambient a ∩ ambient b)
  unit_ne :
    ∀ a b l y, y ∈ ambient a ∩ ambient b →
      unit a b l y ≠ 0
  equation_change :
    ∀ a b l y, y ∈ ambient a ∩ ambient b →
      Q.u b l y = unit a b l y * Q.u a l y
```

Together with `equations_zero`, this derives the derivative-unit field already used by `LabelledNormalBundle`.

**This is the right direction of implication.**

## 5.3 Tubular compatibility with `ResolvedNormalData`

Use a separate adapter, rather than burying tubular assertions in the equation record:

```lean
structure ResolvedTubularCompatibility
    (N : B → Submodule ℝ E)
    (abstractN : B → Type*)
    (Φ : ∀ x, abstractN x → E) where

  realise : ∀ x, abstractN x ≃L[ℝ] N x

  tube : ∀ x, N x → E
  radius : B → ℝ
  radius_pos : ∀ x, 0 < radius x

  tube_zero : ∀ x, tube x 0 = Q.emb x

  analyticAt_zero :
    ∀ x, AnalyticAt ℝ (tube x) 0

  hasFDerivAt_zero :
    ∀ x, HasFDerivAt (tube x)
      (N x).subtypeL 0

  Φ_eq :
    ∀ x ξ, ‖realise x ξ‖ < radius x →
      Φ x ξ = tube x (realise x ξ)
```

To certify a genuine tubular neighbourhood, additionally store or reference an existing tubular homeomorphism on the total bundle. Reuse `TubularBridge` when `LiftedFoot` is available.

The straight Euclidean tube from `TubularJacobian` satisfies
\[
\operatorname{tube}(s,\xi)=\operatorname{emb}(s)+\xi.
\]
But do not require all divisor-adapted tubes to have this form. Curved divisors generally need nonlinear normal coordinates to become coordinate hyperplanes.

The current certificate’s global `Φ_eq` is stronger than needed. A future compatible version should use equality on a common neighbourhood containing the normal box and the origin. That is the natural domain of partial tubular maps.

## 5.4 `MonomialPhaseCompatibility`

This should express monomiality in **adapted coordinates**, not merely record an already-normalised phase identity.

For a patch map `Ψ : B × (Fin m → ℝ) → E` and a neighbourhood `Ω`:

```lean
structure MonomialPhaseCompatibility
    (K : E → ℝ)
    (Ψ : B × (Fin m → ℝ) → E)
    (Ω : Set (B × (Fin m → ℝ)))
    (label : Fin m ≃ ↥I)
    (phaseOrder : Component → ℕ) where

  k : Fin m → ℕ
  k_pos : ∀ i, 0 < k i
  k_eq : ∀ i, k i = phaseOrder (label i).1

  unit : B × (Fin m → ℝ) → ℝ
  continuousOn_unit : ContinuousOn unit Ω
  unit_pos : ∀ p ∈ Ω, 0 < unit p
  analyticAt_unit :
    ∀ p ∈ Ω, AnalyticAt ℝ unit p
    -- For a manifold B, use local parameter charts here.

  phase_eq :
    ∀ p ∈ Ω,
      K (Ψ p) = unit p * ∏ i, p.2 i ^ (2 * k i)

  divisor_iff :
    ∀ p ∈ Ω, ∀ i,
      Ψ p ∈ divisor (label i).1 ↔ p.2 i = 0
```

Here `phaseOrder` means the **half-order**. If the geometry stores the full vanishing order, write `2 * k i = phaseOrder ...` instead. Pick one convention and enforce it.

For unit 3, add:

```lean
  unit_normal_independent :
    ∀ p ∈ Ω, unit p = tangentUnit p.1
```

Then the diagonal-rescaling theorem **consumes** this structure to prove `CorePresentation.phase_normal`.

For a genuinely normal-dependent positive analytic unit, the existing leading-term machinery remains directly usable. Producing an all-orders fixed-box core requires additional analytic coordinate-change work; it is not solved by the tangential rescaling above.

## 5.5 `ResolvedDensityCompatibility`

Separate the geometric Jacobian unit from the prior and from tangential partition weights.

A coordinate-patch form is:

```lean
structure ResolvedDensityCompatibility
    (μ : Measure E)
    (Ψ : B × (Fin m → ℝ) → E)
    (ν : Measure B)
    (box : Set (Fin m → ℝ))
    (label : Fin m ≃ ↥I)
    (jacOrder : Component → ℕ) where

  h : Fin m → ℕ
  h_eq : ∀ i, h i = jacOrder (label i).1

  jacUnit : B × (Fin m → ℝ) → ℝ
  measurable_jacUnit : Measurable jacUnit
  jacUnit_pos :
    ∀ᵐ p ∂ν.prod (volume.restrict box), 0 < jacUnit p

  target : Measure E

  transport_volume :
    ((ν.prod (volume.restrict box)).withDensity
      (fun p => ENNReal.ofReal
        ((∏ i, p.2 i ^ h i) * jacUnit p))).map Ψ =
      target
```

For a resolved density, add the actual factorisation:

```lean
  priorFactor : B × (Fin m → ℝ) → ℝ
  tangentialWeight : B → ℝ

  density_eq :
    ∀ᵐ p ∂ν.prod (volume.restrict box),
      density p =
        tangentialWeight p.1 * priorFactor p * jacUnit p
```

Analytic-normal series for these factors belong in an accompanying analytic record, not in the purely measure-theoretic one.

For a chart arising from a differentiable ambient parametrisation, add a geometric constructor whose inputs include

```lean
  det_eq :
    ∀ p ∈ Ω,
      |(fderiv ℝ flatΨ (concat p)).det| =
        (∏ i, |p.2 i| ^ h i) * jacUnit p
```

plus injectivity and derivative hypotheses. It must **prove** `transport_volume` using the Jacobian theorem.

This makes the compatibility record useful rather than merely renaming `CorePresentation.transport`.

For a general resolution map, `|det Dπ|` alone does not establish global transport when charts overlap or the map has multiplicity. The cover/partition or a.e.-injectivity argument still has to be supplied.

## 5.6 Chart-level `label/k_eq/h_eq/frame_conormal`

The first three fields should be explicit:

```lean
label : Fin (n + 1) ≃ ↥I
k_eq : ∀ i, C.k i = phaseOrder (label i).1
h_eq : ∀ i, C.h i = jacOrder (label i).1
```

For `frame_conormal`, decide which frame convention you mean.

Let
\[
\alpha_i=df_i|_{N_s}.
\]

A divisor-adapted normal coordinate frame should satisfy

\[
\alpha_i(F_s e_j)=a_i(s)\,\delta_{ij},
\qquad a_i(s)\ne0.
\]

Schematically:

```lean
frameScale : B → Fin (n + 1) → ℝ
frameScale_ne : ∀ s i, frameScale s i ≠ 0

frame_conormal :
  ∀ s i j,
    conormal s i
      (realise s (frame s (Pi.single j 1))) =
        if i = j then frameScale s i else 0
```

**Do not assert this for the raw gradient row frame in general.** For that frame the pairing is the Gram matrix of the gradients, not a diagonal matrix.

Use the frame dual to the restricted conormal coframe, or retain the Gram-matrix relation as the appropriate compatibility statement. On the coordinate model both conventions coincide up to diagonal scaling.

## 5.7 Coordinate-model proofs

The coordinate model satisfies these structures with:

- labelled equations \(u_i(w)=w_i\);
- equation-transition units \(1\);
- tangent space the complementary coordinate plane;
- normal space the active coordinate plane;
- straight tubular map \(s+\xi\);
- phase orders \(k_i\);
- geometric Jacobian orders \(0\);
- tangential phase unit
  \[
  t_I(s)=\prod_{j\notin I}s_j^{2k_j};
  \]
- coordinate Jacobian unit \(1\) before rescaling;
- Jacobian unit \(\prod_i\lambda_i(s)\) after rescaling;
- `frameScale s i = σ_i * λ_i(s)` for the normalised frame.

Use `CoordStratumAtlas` for the analytic LCI/tubular facts and coordinate projection computations for the conormal pairings. Exact strata are open subsets of coordinate planes, so their tangent and normal calculations are the same.

---

# 6. The first consumers should be constructive, then interpretive

I would not make the normal-jet interpretation the only first consumer.

## First constructive consumer

Prove a theorem along the lines of:

```lean
produceCore_of_coordinateCompat
```

that consumes:

- tangential-unit `MonomialPhaseCompatibility`;
- `ResolvedDensityCompatibility` produced from a Jacobian theorem;
- uniform normal-series data;
- diagonal normalisation data;

and constructs `CorePresentation`, its moment presentation, and its coefficient certificate.

This immediately tests whether the fields contain the right information.

## First interpretive consumer

Then prove:

> For the fixed compatible tubular germ, `D.normalDifferential φ` is the Fréchet derivative of the pulled-back observable on the genuine normal fibre, and its coordinate expressions transform tensorially under linear frame changes.

Concretely, with \(G_s(\xi)=\phi(\pi(\operatorname{tube}(s,\xi)))\),

\[
D^r(G_s\circ F_s)(0)
=
D^rG_s(0)\circ(F_s,\ldots,F_s).
\]

This is the correct frame-independence statement.

For \(r=1\), `hasFDerivAt_zero` also identifies it with the restriction of the ambient differential to the geometric normal space.

For \(r\ge2\):

- it is a genuine derivative of the **chosen tubular pullback**;
- it is not independent of nonlinear changes of the tube;
- it need not equal an intrinsic “normal derivative” without extra choices.

If the tube is straight affine normal translation, it agrees with the ambient higher differential restricted to normal vectors. State that as a separate stronger theorem.

---

# 7. Order, effort, and stopping point

These are planning estimates, not estimates from inspecting the repository’s proof scripts.

| Unit | Main deliverable | Estimated new Lean |
|---|---|---:|
| 3a | Fibrewise diagonal measure transport; coordinate-base adapter | 350–750 lines |
| 3b | Rescaled uniform families; parameterised core and coefficient producer | 450–900 lines |
| 4 | Water-filling collar, compact bases, a.e. disjointness, exact measure decomposition and gap | 900–1,800 lines |
| 5a | General compact-box producer from uniform face-normal series | 350–800 lines |
| 5b | Derive uniform face-normal series from analytic-neighbourhood data | 900–2,000+ lines |
| Compatibility, first slice | Patchwise fields, coordinate instances, constructive consumer, fixed-germ jet interpretation | 700–1,400 lines |
| General tubular adapter | Measure-valued tubular Jacobian and bundle/base transport | 600–1,300+ lines |

### Ranking by value per effort

1. **Unit 3:** highest immediate reuse; turns CCCXIX into a geometric producer.
2. **Unit 4:** highest conceptual value; removes the real collar obstruction without weakening the core interface.
3. **Unit 5a:** inexpensive once 3–4 exist; gives the principal new theorem.
4. **Compatibility first slice:** necessary for honest geometric interpretation; implement alongside 5a.
5. **Unit 5b:** valuable user-facing theorem, but potentially the largest analytic infrastructure task.
6. General SNC/tubular production beyond coordinate charts.

### Recommended stopping point for this phase

Stop when you have:

> **A certificate-producing theorem for a compact signed coordinate box, with monomial phase, arbitrary strata in a finite normalised collar, uniform face-normal analytic input, exact transport, an explicit positive phase-gap tail, and compatibility-backed interpretation of the normal tensors.**

If feasible, append the analytic-neighbourhood-to-uniform-series bridge. Do not make arbitrary Hironaka covers, general normal-dependent-unit elimination, or existence of compatible tubular geometry part of this phase’s completion criterion.

## Bottom line

The existing core interface is adequate for the next coordinate-model phase. The central missing construction is not a variable-width core interface: it is the **right finite curved collar**.

The water-filling decomposition supplies that collar, preserves fixed normal boxes and a common \(\beta=1\), and makes the physical normal widths uniformly small. Together with CCCXIX, it gives a direct route from local analytic data to genuine multi-stratum certificates—without mistaking the existing leading-term variable-unit theory for an all-orders certificate producer.
