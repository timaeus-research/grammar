## Recommendation

**Target an exact analytic-core presentation plus a certified exponentially small tail—not a direct construction of the current `AdaptedStrataData` for the sharp sublevel measure.**

There are two distinct gaps:

1. **Local normal form:** tractable from hironaka’s chart-form strand.
2. **Compatible localisation across overlapping charts:** not supplied by `PartialResolution`, and not solved by its multiplicity bound.

The second is now grammar’s main geometric obligation. Do not hide it inside a “chart refinement” lemma.

Consequently, I cannot honestly give an eight-module programme *guaranteed* to construct the existing `AdaptedStrataData` from the displayed readout. Its sharp-sublevel transport requirement encounters the obstruction you have already formalised. I can give an eight-unit programme with an explicit blocking geometric theorem and an endpoint that yields the population expansion once that theorem is proved internally.

---

## 1. Architecture: what the certificate should say

### 1.1 Separate the integration certificate from the geometry used to build it

Keep the existing exact chart integrator. Add a wrapper expressing
\[
\int e^{-NK}a\,d\mu
=
\sum_I \int_{B_I}e^{-N\beta u^{2k_I}}
                 A_I(v,u)u^{h_I}\,d\nu_I(v)\,du
+R_N,
\qquad
|R_N|\le C e^{-\delta N}.
\]

Prefer a **measure-level decomposition**, because it handles numerator and denominator with the same localisation:

```lean
-- Schematic interface, not proposed compiling syntax.
structure AnalyticCoreDecomposition (D : LocalisationData U) where
  core tail : Measure U
  measure_eq : D.μ = core + tail
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  δ₀_pos : 0 < δ₀
  tail_obs_integrable : Integrable D.obs tail
  -- Exact finite box presentation of core:
  presentation : FiniteAnalyticBoxPresentation D.phase D.obs core
```

For a finite prior measure,
\[
\left|\int e^{-NK}a\,d\mu_{\mathrm{tail}}\right|
\le e^{-N\delta_0}\int |a|\,d\mu_{\mathrm{tail}}
\quad(N\ge0).
\]

The exact box presentation should transport onto `core`, **without another sharp-sublevel restriction**. Extract the reusable chart-integration argument from the existing theorem rather than changing every existing consumer.

If positive decomposition proves unnecessarily restrictive, a finite signed decomposition with total-variation bounds is a fallback. It should not be the first design: positivity makes the population leading term and denominator estimates cleaner.

### 1.2 The disjoint union of chart domains is not the missing resolved space

It is a useful bookkeeping space, but putting the Jacobian measure on it counts overlaps.

Writing
\[
m(y)=\#\{(i,x):x\in\operatorname{dom}_i,\ \phi_i(x)=y\},
\]
the area/change-of-variables calculation suggests weights \(1/m(\phi_i(x))\). With suitable measurability lemmas, this can give exact transport. It does **not** give normal-analytic amplitudes.

Likewise:

- choosing the first chart containing a point gives measurable indicator weights;
- normalising a cover gives measurable weights;
- using a smooth ambient partition gives smooth pullbacks.

None supplies the required convergent power series in the normal variables.

The multiplicity bound is useful for estimates and integrability. **It is not an analytic partition-of-unity theorem.**

### 1.3 What would actually handle overlaps

The required intermediate theorem is a **compatible divisor-localised atlas**, with weights satisfying both:

1. an exact pushforward sum identity near the zero locus;
2. in each final tubular chart, the weight is a function of the tangential variable alone throughout the integration core.

A sufficient geometric implementation is:

- a genuine analytic modification, at least as a germ over a neighbourhood of the relevant zero set;
- an a.e. one-to-one projection away from the exceptional divisor;
- compatible normal-crossing charts and compatible collars;
- a finite divisor-adapted smooth partition on this common space.

A global analytic-space framework is not necessary: a finite Euclidean atlas with transition maps and the needed gluing/measure properties could suffice. But **the transition maps and compatibility at the divisor must be proved**. They are not fields of the supplied `PartialResolution`.

An alternative is to prove the pushforward identity and tangential analyticity directly for a finite family of chart weights, without constructing a manifold. That is a valid certificate-oriented design, but it is the same substantial geometric obligation in another interface.

**Do not manufacture transition maps merely by taking inverses off the divisor and assume they extend across it.**

### 1.4 Why the two proposed shortcuts do not close this gap

**Ambient partition pulled back.** Generally fatal for *exact* normal analyticity. Replacing a smooth weight by its value on the stratum produces an error vanishing to some normal order, not an exponentially small error. That error can contribute further power–log terms.

Even an infinitely flat difference need not be \(O(e^{-\delta N})\). Exponential localisation requires a positive phase gap on its support.

**Orthant-and-divisor refinement.** Necessary and useful for local normal form, but it neither fixes overlaps nor makes arbitrary chart-domain boundaries compatible with boxes.

So my choice is **(c): exact analytic cores on a compatible divisor-localised presentation, followed by a positive-gap tail**. Use (b) inside that construction.

---

## 2. Local geometry: what is sound, and what needs strengthening

### Exact unit removal

Suppose, after shrinking,
\[
K\circ\phi=u(y)\prod_j y_j^{2k_j},
\qquad u>0.
\]
Choose an active coordinate \(i\) with \(y_i=0\) at the centre and set
\[
T_i(y)=y_i\bigl(u(y)/\beta\bigr)^{1/(2k_i)},
\qquad T_j(y)=y_j\quad(j\ne i).
\]

At the centre the derivative is invertible: the extra terms in the modified row contain \(y_i\), and its diagonal entry is positive. The analytic inverse function theorem therefore gives
\[
K\bigl(\phi(T^{-1}(z))\bigr)
=\beta\prod_j z_j^{2k_j}
\]
on a sufficiently small neighbourhood.

Important qualifications:

- Nonnegativity must hold on an **open chart neighbourhood**, not merely on `dom`.
- Evenness of exponents crossing a coordinate hyperplane must be proved.
- Coordinates nonzero at the centre are absorbed into the unit and treated tangentially.
- If there is no active coordinate, this is an away-from-zero piece.
- The inverse-function theorem gives a neighbourhood, not automatically the required product box. Product containment and finite shrinking are separate lemmas.
- Pulling the Jacobian monomial through this coordinate change preserves its form, with a new analytic nonvanishing unit.

Orthant reflection then handles absolute Jacobians and signs. No global unit-removal assertion is needed.

### The proposed product partition is a useful lemma, not yet `lem:adapted_pou`

The identity
\[
\sum_I\prod_{j\in I}\theta(y_j)
          \prod_{j\notin I}(1-\theta(y_j))=1
\]
is correct. On \(|y_I|<a\), the indicated term is tangential.

But its **whole support** is not contained in that inner tube. For example, with two active coordinates, a transition region in \(y_1\) can meet \(y_2=0\). Its phase is then zero. That transition cannot be thrown into an exponential tail.

A real adapted-localisation proof must reassign such regions to the appropriate smaller active-coordinate strata, compatibly across charts. Prove support and collar compatibility, not just the product identity.

---

## 3. Eight-unit programme, with honest stop rules

These are eight deliverables, not eight equally sized tasks. **Unit 4 is the critical research gate.**

| Unit/module | Deliverable and inputs | Stop rule |
|---|---|---|
| **1. `AnalyticCorePresentation.lean`** | Define exact finite box transport onto a core measure and a core-plus-tail certificate. Extract the chart expansion engine from the current sharp-sublevel theorem. Inputs: existing `ChartPresentation` integration proofs, measure sums and pushforwards. | No geometric existence claim. Prove expansion from the new certificate without adding axioms. |
| **2. `MonomialUnitRemoval.lean`** | Upgrade units to analytic; prove parity/sign lemmas under open-neighbourhood nonnegativity; construct local exact phase and Jacobian normal form. Inputs: hironaka’s analytic-unit bridge, analytic `log`/`exp`, `HasStrictFDerivAt.toOpenPartialHomeomorph`, analytic inverse theorem. | Local neighbourhood theorem only. Do not assert injectivity on the original whole box. |
| **3. `MonomialOrthantBoxes.lean`** | Reflect orthants, split active and tangential coordinates, shrink to product boxes, and establish local transport. Inputs: `map_signReflect_weightedPosBox`, `ResolutionChart.map_absDet`, finite-dimensional coordinate equivalences. | Produce local chart certificates with explicit domain/support hypotheses. No overlap assembly yet. |
| **4. `CompatibleDivisorLocalisation.lean`** | Prove the finite compatible localisation theorem: exact pushforward weights near the relevant zero set, tangential-only weights on final cores, all discarded parts supported at a positive phase level. Inputs: local charts, compactness, bump/partition machinery; **new grammar-owned compatibility geometry**. | Must derive existence from the allowed analytic hypotheses/readout or from an internally proved stronger resolution construction. A structure with an unproved inhabitance theorem is not completion. |
| **5. `CoordinateAdaptedPartition.lean`** | Formalise product cutoff identities, coordinate feet, compatible collar refinements, and saturation/support properties; use Unit 4’s atlas compatibility to globalise them. Inputs: smooth cutoff functions, finite sums/products, CLXXVIII’s coordinate model. | Every transition piece is either represented in another core or has a proved positive phase gap. “Small normal coordinate error” is not a tail proof. |
| **6. `RealAnalyticBoxAmplitude.lean`** | Construct `TangentialData` from tangential cutoffs times jointly real-analytic densities/observables. Prove uniform radius strictly larger than the box side, weighted \(\ell^1\) summability, and continuity into coefficient space. Inputs: `HasFPowerSeriesOnBall`/`AnalyticAt` infrastructure and grammar’s coefficient spaces. | Pointwise analyticity is insufficient. Require uniform majorants after finite shrinking; prove coefficient-space continuity. No holomorphic hypothesis introduced. |
| **7. `CertifiedCoreAssembly.lean`** | Assemble exact transport, `phase_normal`, `amplitude_eq`, and deterministic `fluct_zero`; sum charts without multiplicity overcounting. Inputs: Units 1–6 and `map_absDet`. | The sum of pushforward measures must be exactly the core measure. A two-sided multiplicity comparison does not pass. |
| **8. `PopulationExpansionAnalytic.lean`** | Prove the positive-gap tail estimate; absorb it into every requested power–log remainder order; handle numerator/denominator normalisation and identify the existing canonical coefficient expression. | Publish only with Unit 4 discharged and every compactness, nontriviality, boundary and positivity hypothesis visible. |

### Risk ranking

- **Highest mathematical risk:** Unit 4. The raw chart readout does not carry the overlap compatibility needed by this plan. Inspect whether proved internal chart constructions retain useful transition/modification data; recover such data if available. Otherwise grammar owns a substantial new geometric construction.
- **Highest analytic Lean risk:** Unit 6. Analytic inverse existence is not the whole difficulty; uniform real power-series control in your particular \(\ell^1\) representation is substantial.
- **High measure-engineering risk:** Unit 7—restrictions, exceptional sets, composed coordinate changes, and exact pushforwards.
- **Bounded local geometry:** Units 2–3.
- **Relatively routine after certificates:** Unit 8.

### State the population endpoint precisely

“Real-analytic \(K\ge0\), analytic prior/observable” alone is not enough. The theorem also needs the paper’s integration setting, including appropriate:

- compactness or tail control;
- integrability and nonzero population normalisation;
- treatment of components on which \(K\) vanishes identically;
- compatibility of any integration boundary with the localisation.

An arbitrary measurable integration domain can itself destroy a power–log expansion. The neighbourhood `N` returned by the local readout is not automatically a suitable integration domain for the exact analytic-amplitude theorem.

If the endpoint is an expectation ratio, prove the denominator lower bound from the leading population asymptotic and absorb the resulting polynomial/logarithmic factors multiplying the exponential tail.

---

## 4. Coefficients and the stochastic side

### 4.1 Population coefficient identification is a sensible immediate target

Once exact core transport and amplitude identification are proved, the coefficients are those computed by the existing box machinery. The remaining work is:

1. identify the normal exponents and density powers;
2. identify the restricted amplitude/coefficient data;
3. sum the chart contributions;
4. show compatibility with the paper’s notation and normalisations.

Distinguish:

- **identification for the constructed presentation**, which should be bounded;
- **independence under every compatible presentation**, which needs an asymptotic uniqueness theorem or a geometric invariance argument.

For a common locally finite power–log asymptotic scale, uniqueness is a good way to prove coefficient independence after assembly. Avoid a chart-by-chart invariance project unless the paper requires it.

### 4.2 Keep stochastic division as a hypothesis for now

Scalar monomialisation of
\[
K(w)=\mathbb E[f(X,w)]
\]
does not by itself imply
\[
f(x,\pi(u))=u^k a(x,u)
\]
uniformly in \(x\), nor does it supply the Hypothesis-I envelope.

What is missing is not merely a call to Weierstrass division:

- pointwise or almost-sure divisibility in the parameter variables;
- joint measurability of the quotient;
- parameter-uniform analytic control;
- domination in the required sample-space norm;
- the moment/envelope estimates used by the stochastic argument.

A plausible future route uses analytic maps into an appropriate \(L^p\) or Banach space, plus the statistical inequalities that force divisibility. That is an additional theorem about the statistical model, not a readout of `Q_all`.

**Retain `hca`, `hφ` with their precise quantifiers.** Target unconditional population geometry first. Do not describe single-series Weierstrass division as closing uniform stochastic standard form.

### 4.3 Is localisation plus the annealed remainder enough?

Only after checking the weighted estimate actually needed.

For
\[
\mathbb E|A_n\operatorname{Rem}_n|\to0,
\]
an unweighted bound on \(\mathbb E|\operatorname{Rem}_n|\) is generally insufficient.

Useful sufficient patterns are:

- directly \(\mathbb E|A_n\operatorname{Rem}_{n,\mathrm{core}}|\to0\);
- Hölder with suitable complementary moment bounds;
- a deterministic bound \(|A_n|\le Cn^q(1+\log n)^r\) and an annealed remainder decaying faster than that.

For the tail, if
\[
|\operatorname{Rem}_{n,\mathrm{tail}}|
\le B_n e^{-\delta n},
\]
you need
\[
e^{-\delta n}\mathbb E|A_nB_n|\to0.
\]

Moreover, a deterministic population phase gap does not automatically bound a random likelihood integrand: stochastic fluctuations can offset it. Use the actual stochastic localisation theorem and its moment assumptions.

Thus: **yes if the existing annealed and localisation bounds already control these products; no merely from the labels “exponential tail” and “annealed remainder.”**

---

## 5. What not to open

1. **No E6 imports or reliance on its `AnalyticSpace` skeleton.**
2. **No assertion that finite multiplicity provides analytic overlap weights.**
3. **No replacement of exact analytic amplitudes by smooth ones without changing and reproving the expansion engine.**
4. **No claim that normal Taylor errors are exponentially small.**
5. **No global unit removal on an original chart box without a separate injectivity proof.**
6. **No full abstract lifted-foot theory yet.** Prove the coordinate foot and precisely the chart compatibility needed for localisation.
7. **No uniform stochastic division project as a prerequisite for the population theorem.**
8. **No “unconditional” endpoint obtained by renaming an external geometric hypothesis as a certificate field.**

**First action:** define Unit 1, then write Unit 4’s existence statement *before* implementing the easy local lemmas. That statement will expose exactly which compatibility data must be recovered or developed in grammar. It is the decisive bridge; unit removal is not.
