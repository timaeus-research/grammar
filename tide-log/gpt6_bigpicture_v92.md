## Recommendation

State the final theorem on a **genuine resolved space equipped with chosen tubular data**, and keep a compatible monomial atlas in a separate certificate used by the proof.

Do **not** identify `PartialResolution` with that object. A finite collection of parametrisations of subsets of `W` does not determine a common resolved space or its normal bundles.

There are also three corrections to make before implementing the target:

1. **The existing `normalTaylorForm` already includes `1/r!`.** The displayed formula must use `rawNormalJet`, or omit its external factorial.
2. **Exact fibre moments are generally not finite power–log sums.** Distinguish exact moments, asymptotic coefficient tensors, and cutoff moment polynomials.
3. **A cutoff in powers of `n` need not give a finite cutoff in normal Taylor order.** At tied crossings, infinitely many normal orders can contribute to one power of `n`. This matters both mathematically and for the Lean theorem.

Subject to these corrections, Daniel’s requirement is attainable as a **conditional, chart-free theorem statement**. It is not presently an unconditional consequence of hironaka’s public interface.

---

# 1. The geometric interface

## 1.1 Use a chain of structures

I recommend separating:

```text
ResolvedGeometry
    common U, π, divisor, strata, numerical orders
            ↓
ResolvedNormalData
    normal bundles, labelled conormal lines, tubular germs
            ↓
ResolvedIntegrationData
    resolved measure, stratum measures, fibre measures, localisation
            ↓
MonomialCompatibilityCertificate
    charts and compatibility proofs
```

The final formula refers to the first three. The fourth appears only among its hypotheses.

Do not put moment-expansion conclusions into `ResolvedGeometry`: that would make the geometric interface circular.

### What sort of space is `U`?

A merely measurable `U` is insufficient for the requested interpretation. It can support a fibre-integral identity, but it cannot by itself say that:

- `S_I` is a smooth stratum;
- `N S_I` is its normal bundle;
- the conormal lines come from divisor components;
- `Φ_I` is a tubular neighbourhood.

Use a finite-dimensional smooth manifold, with its Borel measurable space. Analyticity can initially be certified locally rather than demanded through a new bundled analytic-manifold interface.

For the shortest route through the existing normal-family machinery, use an **embedded presentation**:

- a finite-dimensional Euclidean ambient space `A`;
- an embedding `emb : U → A`;
- `U` a smooth `d`-manifold;
- normal fibres represented by submodules of `A`.

This adds an auxiliary embedding, but adds **no coordinates to the final formula**. Intrinsic normal bundles can replace the embedded presentation later.

Importantly, the normal fibre must represent
\[
T_sU/T_sS_I,
\]
not the full normal space of `S_I` in `A`. Those differ when `U` has positive ambient codimension.

Mathlib’s `ChartedSpace`, `ModelWithCorners`, and `IsManifold` infrastructure is appropriate. I would take `U` and its typeclass instances as parameters to the structure, rather than trying to bundle all instances inside one large record.

## 1.2 Geometric fields

The following is an interface sketch, not claimed to be compiling code against headers not supplied here:

```lean
structure ResolvedGeometry ... where
  π : U → W
  continuous_π : Continuous π
  proper_π : IsProperMap π

  Component : Type
  component_fintype : Fintype Component
  E : Component → Set U
  isClosed_E : ∀ i, IsClosed (E i)

  k : Component → ℕ
  h : Component → ℕ
  k_pos : ∀ i, 0 < k i
```

Define, rather than store, the open incidence stratum:

\[
S_I=\{u\in U:\ \forall i,\ u\in E_i\iff i\in I\}.
\]

```lean
def stratumSet (R : ResolvedGeometry ...) (I : Finset R.Component) :=
  {u | ∀ i, u ∈ R.E i ↔ i ∈ I}

abbrev Stratum (R : ResolvedGeometry ...) (I : Finset R.Component) :=
  ↥(R.stratumSet I)
```

Empty strata can be retained with zero contributions.

Fix the order convention explicitly:

- if locally \(K\circ\pi=u\prod y_i^{k_i}\), use \((h_i+1)/k_i\);
- if the paper writes \(y_i^{2k_i}\), use \((h_i+1)/(2k_i)\).

Do not let the interface silently alternate between these conventions.

For compactly supported problems, properness over the relevant compact region is enough. Properness is useful for producing a finite proof cover; the integration theorem principally needs the resulting compactness and change-of-variables identities.

## 1.3 Normal and tubular fields

For each nonempty stratum, carry:

- `N I s : Submodule ℝ A`, of dimension `I.card`;
- its identification with the intrinsic normal space;
- labelled conormal line subbundles;
- the fibrewise splitting
  \[
  N_s^*S_I\simeq\bigoplus_{i\in I}L_{i,s};
  \]
- a neighbourhood of the zero section in the normal bundle;
- a tubular map from that neighbourhood to `U`;
- a retraction onto `S_I`;
- zero-section and inverse identities;
- sufficient regularity of the tubular map.

A tubular map normally has domain an **open neighbourhood of the zero section**, not all of `NS_I`. The existing `rawNormalJet` takes total fibre maps. Bridge this by extending each fibre map arbitrarily outside its domain and prove that the jet depends only on its germ at zero.

Reuse:

- `conormalSplitting` for the fibrewise algebra;
- `LabelledNormalBundle` for gluing the labelled lines and smooth bundle structure;
- `NormalTaylorForm` for fibrewise jets;
- `IsGlobalNormalSection` for the relevant transformation law.

New work is needed to identify these constructions with the normal bundle of a stratum in the common `U`.

An important limitation: `IsGlobalNormalSection` is not a substitute for constructing the geometry. It verifies the stated compatibility relative to an existing normal presentation.

## 1.4 Integration and localisation fields

Carry a resolved measure `μU` and prove the appropriate change of variables. In the degree-one case, schematically:

```lean
Measure.map R.π μU = μW
```

on the relevant region, where `μW` includes the prior if that is the chosen convention. If chart parametrisations have multiplicity, the weights correcting that multiplicity must already have been accounted for. An a.e. cover alone does not imply this identity.

For each stratum carry:

- a base measure `ν I : Measure (Stratum R I)`;
- a measurable family of measures on its normal fibres;
- localisation data;
- a tubular disintegration identity.

There should be a separate away-from-divisor contribution, with a proved exponentially small estimate when `K` is bounded below there.

### Treat the adapted partition as substantive data

Record exactly what is actually used:

- smooth nonnegative `ρ I`;
- partition identity on the relevant resolved support;
- subordinate support conditions;
- the required normal constancy, normally a **germ near the zero section**;
- compatibility with tubular cutoffs;
- integrability and quantitative estimates furnished by the certificate.

Do not infer all needed integrability just from
\[
V_I\cap E_j=\varnothing\quad(j\notin I).
\]
An open set can avoid a divisor while approaching it arbitrarily closely. The support and decay/separation properties that make the integrals converge must be proved.

Likewise, global fibrewise constancy on a whole tube is stronger than germwise normal constancy and can conflict with the desired compact tubular cutoffs. The interface must distinguish these notions.

## 1.5 The chart certificate

`MonomialCompatibilityCertificate` should certify the following **local, checkable identities**:

1. **Actual charts of `U`.**  
   Local equivalences to open subsets of Euclidean space, covering the resolved support, with smooth transitions.

2. **Divisor incidence.**  
   In each chart, the relevant `E_i` are labelled coordinate hyperplanes; components not in the chart’s label set are absent there.

3. **Normal crossings.**  
   The labelled defining differentials are independent on each stratum.

4. **Monomial phase and density.**
   \[
   K\circ\pi=u\prod_i|y_i|^{k_i},\qquad
   d\mu_U=c\prod_i|y_i|^{h_i}\,dy,
   \]
   with the positivity, regularity, domain and integrability assumptions required by the chart theorems.

5. **Normal compatibility.**  
   The differential of the tubular map at the zero section identifies the abstract normal fibre with the chart-normal quotient. The induced dual identification agrees with the labelled conormal splitting.

6. **Density compatibility.**  
   Local tubular change of variables reproduces the stored base measure and fibre measures.

7. **Localisation compatibility.**  
   The actual partition and cutoffs are the ones used in these identities.

8. **Quantitative analytic control.**  
   The seminorm, support, Taylor and remainder bounds needed to sum normal orders and integrate chart asymptotics.

Items 1–7 are geometric/measure-theoretic compatibility. Item 8 is an analytic admissibility certificate and should probably be a separate structure.

For global coefficients, equality of local representatives **after pairing and integrating** is often the first useful gluing statement. Pointwise tensor gluing is stronger and must not be inferred from equality of global integrals.

---

# 2. The coordinate-free objects

## 2.1 Normal differentials: fix the factorial now

The supplied header says:

```lean
normalTaylorForm ... s r =
  (r.factorial : ℝ)⁻¹ • rawNormalJet ... s r
```

Therefore, to reproduce Daniel’s displayed formula, define

```lean
noncomputable def normalDifferential
    (F : U → ℝ) (I) (s : Stratum R I) (r : ℕ) :=
  rawNormalJet (N I) (tubeFamily I) F s r
```

and use

\[
\frac1{r!}\langle D_\perp^rF,M_r\rangle.
\]

Alternatively, use `normalTaylorForm` and write simply

\[
\langle T_rF,M_r\rangle.
\]

**Do not use `normalTaylorForm` and another external `1/r!`.**

For smooth fibre maps, prove that the iterated derivative is symmetric. Package it as a symmetric continuous multilinear form, not just an unqualified `JetForm`.

For fixed tubular data it is coordinate-independent. Under a *change of tubular neighbourhood*, higher normal derivatives generally mix with other derivatives; they are not individually canonical.

For an infinite Taylor-series identity, smoothness is insufficient. One needs analytic fibre dependence and a convergence radius covering the fibre support, with domination. Analytic `φ` alone does not provide this if `π` or the chosen tubular map is only smooth.

## 2.2 Moment tensors

For a finite-dimensional normal fibre `V`, an economical Lean representation of `Sym^r V` is the continuous dual of the space of symmetric continuous `r`-forms:

```lean
abbrev MomentTensor (V) (r : ℕ) :=
  NormedSpace.Dual ℝ (SymmetricJetForm V r)
```

This avoids needing a substantial new symmetric tensor-power API. A finite-dimensional equivalence to the algebraic symmetric power can be added separately.

Define the pure moment evaluation by
\[
v^{\odot r}(A)=A(v,\ldots,v).
\]

If `η I s n` is the exact normal fibre measure, set
\[
\widehat M_{I,r}(n)(s)(A)
   =\int A(v,\ldots,v)\,d\eta_{I,s,n}(v).
\]

Require the corresponding absolute moment to be finite. Its definition includes the phase, prior, Jacobian and tubular localisation according to the selected disintegration convention.

The existing fibre-measure and contraction machinery is well suited to the scalar equality
\[
\langle A,\widehat M_{I,r}(n)(s)\rangle
  =\int A(v,\ldots,v)\,d\eta_{I,s,n}(v).
\]

### Three different objects

Use distinct names:

1. `exactMoment I r n` — the fibre integral;
2. `momentCoeff I r q` — the tensor coefficient at power–log index `q`;
3. `momentCutoff I r A n` — a finite power–log polynomial:
   \[
   M^{\le A}_{I,r}(n)
   =\sum_{\alpha\le A}\sum_j
      n^{-\alpha}(\log n)^j B_{I,r,\alpha,j}.
   \]

An exact moment is generally **not** equal to its cutoff polynomial.

Initially, state the moment asymptotics in the integrated, tested form needed by the theorem. Pointwise fibrewise asymptotics may fail to be uniform near a stratum boundary.

## 2.3 A serious issue: normal order is not locally finite

Consider the normal-crossing model on \([0,\varepsilon]^2\):
\[
K(x,y)=xy.
\]
For any integer \(R>0\),
\[
\begin{aligned}
\int_0^\varepsilon\!\!\int_0^\varepsilon
 x^R e^{-nxy}\,dy\,dx
 &=\frac1n\int_0^\varepsilon
 x^{R-1}(1-e^{-n\varepsilon x})\,dx\\
 &\sim \frac{\varepsilon^R}{R}\,n^{-1}.
\end{aligned}
\]

Thus arbitrarily high Taylor orders at the deepest stratum contribute to the **same** \(n^{-1}\) coefficient.

Consequences:

- a finite power cutoff does not automatically permit a finite `r` cutoff;
- `Σ r` in the target can genuinely be infinite at one asymptotic order;
- exchanging that sum with asymptotic extraction requires estimates;
- the analogous unrestricted `C∞` theorem based only on infinite jets at the deepest stratum is false: flat functions can contribute on nearby axes.

An adapted partition does not remove this issue from a deepest-stratum piece that is nonzero on a neighbourhood of the crossing.

For the paper-shaped analytic theorem, retain `∑' r` and prove absolute summability using analytic normal Taylor bounds. A finite-jet theorem would need a different allocation of contributions, often involving intrinsic finite-part distributions on shallower strata.

## 2.4 The density on the stratum

Use a measure

```lean
ν I : Measure (Stratum R I)
```

for the paper’s `τ_*|μ_I|`.

But specify its construction. There are two different pushforwards that should not be confused:

- pushing a base density through a parametrisation `τ` of the stratum;
- pushing the full localised resolved measure through a tubular retraction.

The second integrates all normal fibres and generally gives a different measure. In particular, if the exponential is included, it is `n`-dependent.

The clean convention is:

- `ν I` is an `n`-independent base density;
- the normal fibre measures contain the `n`-dependent phase and the remaining weight;
- their product/disintegration reconstructs the localised resolved integral.

The decomposition into base density and fibre density is not unique:
\[
\nu\mapsto f\nu,\qquad M\mapsto f^{-1}M
\]
leaves the pairing integral unchanged.

Therefore `ν I` is not automatically the canonical leading measure. The leading measure is obtained only after inserting the leading scalar moment coefficient, restricting as appropriate, and pushing to `W`.

## 2.5 Pairing and regularisation

With the dual representation,

```lean
def pair (D : SymmetricJetForm V r) (M : MomentTensor V r) : ℝ :=
  M D
```

and the coefficient contribution is

```lean
∫ s : Stratum R I,
  pair (normalDifferential (φ ∘ R.π) I s r)
       (momentCoeff I r q s)
  ∂ν I
```

### Which statement is more honest?

For Daniel’s requested ordinary stratum integrals, prefer:

> fixed adapted localisation, with proved absolute integrability of every displayed coefficient pairing and proved summability in `r`.

Finite parts can remain in the proof.

However, if the chart-face coefficients only glue as distributions, they cannot simply be renamed integrable tensor fields. Then the honest statement is an **intrinsic distributional pairing** on the stratum, with a specified extension/finite-part prescription.

Thus there are two legitimate endpoints:

- **ordinary tensor sections plus measures**, under sufficient localisation and analytic estimates;
- **tensor-valued distributions**, with intrinsic regularisation.

The first matches the displayed formula more closely. It must pass a real integrability gate; the adapted-PoU lemma’s informal description is not a substitute for that proof.

---

# 3. The final theorem

Below is proposed Lean-level notation. The new names describe interfaces to implement, not existing declarations.

Let `PowerLogIndex` contain a rational exponent and a natural log degree. Let `spectrumBelow A` be finite and include **all** terms with exponent at most `A`.

Define, without charts:

```lean
noncomputable def stratumCoefficient
    (D : ResolvedNormalIntegrationData R)
    (B : MomentCoefficientField D)
    (φ : W → ℝ) (I) (r : ℕ) (q : PowerLogIndex) : ℝ :=
  (r.factorial : ℝ)⁻¹ *
    ∫ s : Stratum R I,
      pair
        (D.normalDifferential (φ ∘ R.π) I s r)
        (B.coeff I r q s)
      ∂D.stratumMeasure I

noncomputable def expansionCoefficient ... (q : PowerLogIndex) : ℝ :=
  ∑ I, ∑' r, stratumCoefficient D B φ I r q
```

The moment coefficients `B` should ultimately be **constructed from the certificate**, not arbitrary fields carrying the desired asymptotic theorem as an axiom.

The target theorem is:

```lean
theorem expectation_expansion
    (R : ResolvedGeometry ...)
    (D : ResolvedNormalIntegrationData R)
    (C : MonomialCompatibilityCertificate R D K prior)
    (H : AnalyticExpansionAdmissible C φ)
    (A : ℝ) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℝ =>
        populationIntegral K prior φ n -
          ∑ q ∈ C.spectrumBelow A,
            expansionCoefficient D C.momentCoefficients φ q *
              Real.rpow n (-(q.exponent : ℝ)) *
              Real.log n ^ q.logDegree)
      (fun n : ℝ => Real.rpow n (-A))
```

Here `AnalyticExpansionAdmissible` should be built from:

- analyticity on a neighbourhood of the relevant support;
- analytic normal fibre maps;
- strict Taylor-radius margins;
- integrable majorants;
- the summable quantitative bounds required by the chart estimates.

It should **not** contain the final expansion as a field.

Mathematically:
\[
\int_W\phi\,\varphi\,e^{-nK}
=
\sum_{\substack{(\alpha,j)\\\alpha\le A}}
n^{-\alpha}(\log n)^j
\sum_I\sum_{r\ge0}\frac1{r!}
\int_{S_I}
\left\langle
D_\perp^r(\phi\circ\pi),
B_{I,r,\alpha,j}
\right\rangle\,d\nu_I
+o(n^{-A}).
\]

**There are no charts in this formula.** The finite chart cover is only in `C`.

The `o(n^{-A})` convention requires subtracting all log terms at exponent `A`. A theorem using `< A` needs a different remainder convention.

## Leading-term corollary

Assuming the certificate proves that the leading coefficient has the paper’s order-zero form, define
\[
\mu_{\mathrm{lead}}
=
\sum_{I\ \mathrm{tied}}
\pi_{I*}\left[
\frac{\Gamma(\lambda)}{(m-1)!}\,
a_I\,\nu_I
\right],
\]
with the paper’s \(c_0\)-restriction inserted on the correctly typed space.

For example, if \(c_0\subseteq W\), this can be written as
\[
\sum_{I\ \mathrm{tied}}
\pi_{I*}\left[
\left(\frac{\Gamma(\lambda)}{(m-1)!}a_I\nu_I\right)
\big|_{\pi_I^{-1}(c_0)}
\right].
\]

Then prove
\[
\frac{n^\lambda}{(\log n)^{m-1}}
\int_W\phi\,\varphi\,e^{-nK}
\longrightarrow
\int_W\phi\,d\mu_{\mathrm{lead}}.
\]

The bridge to CCXC should be a separate equality theorem:

```lean
theorem geometricLeadingMeasure_eq_existingLeadingMeasure :
  geometricLeadingMeasure R D C = existingLeadingMeasure ...
```

Prove it from the compatible local density formulas, or from uniqueness of the limiting measure using an adequate determining test class. Equality on analytic tests needs a measure-determining argument; it is not automatic.

### Canonical versus chosen

**Canonical, for fixed original integral:**

- the total power–log coefficient functional, by asymptotic uniqueness;
- the total leading measure;
- the resulting asymptotic expansion.

**Generally choice-dependent:**

- tubular normal derivatives;
- individual moment tensors and their representatives;
- the split between base density and fibre density;
- individual `I` contributions;
- the adapted partition split.

Changing `Φ_I` or `ρ_I` redistributes terms. The theorem should assert invariance of the **total**, not of each summand.

---

# 4. Proof route and examples

## 4.1 How much of #91 remains?

Most of its **local analytic engine** remains useful:

- Mellin/Laurent coefficient extraction;
- log multiplicity bookkeeping;
- finite parts at faces;
- cutoff remainder bounds;
- cancellation and independence under changes of localisation.

What changes is the output boundary:

```text
local chart-face coefficients
        ↓ compatibility + gluing + integration
intrinsic stratum moment coefficients
        ↓
chart-free theorem
```

Do not first develop an elaborate final API of chart-face functionals on `W` if its only purpose is this theorem. Prove the scalar tested identities needed to construct and identify the intrinsic coefficients.

The existing `coverIntegral_eq_sum_pieceContraction` and related contraction theorems provide a useful **exact decomposition bridge**. They do not alone supply full cutoff asymptotics or the uniform estimates needed to interchange an infinite normal-order sum.

## 4.2 Cheapest honest blow-up

For the real projective blow-up of the origin, avoid both an abstract gluing quotient and dependence on a missing projective-manifold API.

Represent a line by its orthogonal rank-one projector. For \(d>0\), define
\[
\mathcal P_1=
\{P\in\mathbb R^{d\times d}:
P^T=P,\ P^2=P,\ \operatorname{tr}P=1\},
\]
and
\[
U=\{(x,P):P\in\mathcal P_1,\ Px=x\}.
\]

Then:

- `π (x,P) = x`;
- the exceptional divisor is `{(0,P)}`;
- `U` is the total space of the tautological real line bundle;
- `π` is proper because `𝒫₁` is compact and the incidence condition is closed;
- away from `x = 0`, the projector is uniquely \(xx^T/\|x\|^2\).

On `Pᵢᵢ > 0`, put `vᵢ = 1`, `vⱼ = Pⱼᵢ/Pᵢᵢ`, and write
\[
P=\frac{vv^T}{\|v\|^2},\qquad x=t\,v.
\]
These give the familiar blow-up charts and explicit transitions.

This is an honest common resolved space, realised as a subtype of a Euclidean ambient space. Establishing its smooth manifold structure still requires work, but it avoids quotient topology and projective-space infrastructure.

For \(K(x)=\|x\|^2\), the exceptional order is `2`, and the volume Jacobian order is `d - 1`. The normal bundle of the exceptional divisor is the tautological line bundle, so this example tests nontrivial bundle gluing.

A disjoint union of the `d` chart domains is **not** the projective blow-up. It can give a weighted integration presentation, but it does not honestly instantiate the intended global geometry without gluing.

For the cube, use an ambient normal-crossing space such as `U = ℝ^d` and put the cube restriction into the integration/support data. This avoids demanding manifold-with-corners infrastructure for the first theorem.

## 4.3 Ordered unit plan

The sizes below are **implementation targets**, not verified estimates. In particular, the full projector blow-up manifold construction or missing finite-part estimates may exceed a 400-line unit. If a gate fails, split the infrastructure rather than hiding it in certificate fields.

| # | Unit | Main declaration or result | Target / gate |
|---|---|---|---|
| 1 | **`Grammar/NormalDifferentialConvention.lean`** | `factorial_smul_normalTaylorForm`: `(r.factorial : ℝ) • normalTaylorForm N Φ F s r = rawNormalJet N Φ F s r`; define unnormalised differential and prove germ invariance | 100–200 lines; fixes the convention before other work |
| 2 | `ResolvedGeometry.lean` | `ResolvedGeometry`, incidence strata, disjointness and divisor-union identities | 200–300; no asymptotic fields |
| 3 | `ResolvedNormalData.lean` | normal/tubular interface; `normalDifferential_isSymmetric`; bridge to `IsGlobalNormalSection` | 250–400; use existing bundle API |
| 4 | `ResolvedIntegrationData.lean` | `localisedIntegral_eq_stratum_fibreIntegral`; away-piece decomposition | 250–400; genuine change of variables |
| 5 | `ResolvedMonomialCertificate.lean` | certificate structures; chart integral equals the stored localised integral | 250–400; quantitative hypotheses named explicitly |
| 6 | `ProjectorBlowupGeometry.lean` | projector incidence model, global `π`, exceptional divisor, properness, explicit chart equivalences | ≤400 **only if supporting matrix lemmas suffice** |
| 7 | `ProjectorBlowupCertificate.lean` | radial model instance, tubular normal family, `k = 2`, `h = d - 1`, density compatibility | 300–400; first substantive instance |
| 8 | `ResolvedExactMoments.lean` | `pair_exactMoment_eq_integral`; `localisedIntegral_eq_tsum_stratumContraction` | 250–400; analytic domination and dependent-fibre measurability |
| 9 | `StratumMomentCoefficients.lean` | construct coefficient representatives from chart results; gluing and integrability | 300–400 **only after #91’s required local estimates exist** |
| 10 | `ResolvedCutoffExpansion.lean` | `expectation_expansion`; summable remainder/interchange theorem | 250–400; tied-crossing infinite-`r` test mandatory |
| 11 | `ResolvedLeadingMeasure.lean` | leading corollary and equality with CCXC measure | 200–350; constants and `c₀` restriction checked |
| 12 | `ResolvedNormalCrossingExamples.lean` | cube and tied normal-crossing instances; normal-order non-local-finiteness regression example | 250–400; ordinary-integrability versus finite-part gate |

The two main stop/go gates are:

1. **Does adapted localisation really produce integrable tensor coefficients?**
2. **Can the chart remainder bounds be summed over all normal orders?**

If either fails, the correct response is to adjust the mathematical statement—not to add an unexplained “compatibility” axiom that asserts the missing theorem.

---

# 5. What hironaka must expose

To produce this structure automatically, hironaka would need more than monomial parametrisations.

It should expose:

1. a common resolved space `U`;
2. a proper analytic map `π : U → W`;
3. an actual atlas of `U`, with domains, inverse chart maps and overlap identities;
4. labelled global exceptional components `E_i`;
5. closedness, smooth-hypersurface structure and normal-crossing incidence;
6. the factorisation of `K ∘ π`, with globally consistent component orders;
7. the Jacobian/density orders and change-of-variables theorem;
8. the relationship between its compact box readout and the manifold atlas;
9. preferably, the iterated blow-up maps and component/strict-transform bookkeeping from which these facts follow.

It need not expose tubular neighbourhoods as part of resolution itself. Those, adapted localisation, and density disintegration can be downstream constructions, provided the necessary smooth geometric infrastructure exists.

Mathematically, an iterated-blow-up construction contains the right geometry. Formally, however, a BM89/box-chart readout may discard precisely the overlap and incidence information required here. Recovering it from `PartialResolution` alone is not justified. Whether retaining it is a modest refactor or a major project depends on the internal construction, which the supplied interface does not establish.

**The honest endpoint now is therefore a conditional theorem on certified resolved geometry.** That endpoint can fully satisfy Daniel’s requirement: the final expansion contains only strata, normal differentials, moment tensors, densities and pushforwards. Charts remain certificates and proof devices, never summation indices or coordinates in the final formula.
