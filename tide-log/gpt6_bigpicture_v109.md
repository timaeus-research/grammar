# Decision

**Close this phase along two parallel tracks:**

1. **The expectation track:** formalise division of the already-produced expansions, with the correct coefficient class.
2. **The geometric track:** produce **one genuine blow-up application** of the coordinate-free theorem, by transporting local analytic cores to the tautological-line/projector blow-up.

Do **not** turn this phase into an upstream resolution-of-singularities programme. But do not describe the present chart-model result as an application on a genuine resolved space.

There is one important correction to the proposed expectation work:

> A denominator with a positive leading power–log coefficient does **not**, in general, have an inverse admitting an all-order expansion with finitely many polynomial or Laurent-polynomial log terms at each power of \(n\). Rational functions of \(\log n\), or a genuinely two-scale asymptotic formalism, are needed.

Thus I is bounded **with a rational-log target**. It is not bounded as “ordinary finite power–log division” without additional hypotheses.

The assessment below uses your inventory, not an inspection of the current Lean declarations or the exact paper text. Proposed structure names are design names, not claims about existing API.

---

# 1. Ranked gap list

Some letters need splitting: they combine a bounded missing result with a substantially larger generalisation.

| Rank | Gap | Assessment against the plan and §3 |
|---|---|---|
| **1** | **I: normalised expectation** | A direct gap in an expectation theorem: numerator expansions and leading quotient limits do not establish an all-order expansion of \(E_n[\phi]\). Correct the target coefficient class first. |
| **2** | **A + B, restricted to the genuine cube blow-up** | The most important geometric closure: make the certificate theorem apply to an actual \((U,\pi)\), not another chart model with \(\pi=\mathrm{id}\). |
| **3** | **H, for that genuine application** | Identify the leading intrinsic functional/measure with the transported chart density. Existing scalar leading-measure bridges do not automatically prove the paper’s chart-density formula. |
| **4** | **B: reusable compatible-atlas producer** | A genuine plan gap. Extract a sufficient atlas-to-certificate interface from the blow-up application; do not initially promise arbitrary SNC coordinate changes. |
| **5** | **E: analytic tubular geometry** | The chosen-data theorem is legitimate, but existence is not formalised. Close it explicitly for the blow-up; keep general analytic tubular existence conditional. |
| **6** | **F: partial-active collar** | A real producer gap if the plan promises general active subsets. It is not needed to re-prove the full-active boxes already landed. Promote it if the selected atlas application actually requires it. |
| **7** | **G: parity, Gamma formulas, \(d=1\)** | Bounded coefficient-fidelity work. Necessary for corresponding explicit paper formulas, but not for the abstract existence of the expansion. Symmetry of the domain alone does not establish parity cancellation. |
| **8** | **J: box-only agreement** | A small canonicity closure, probably largely a wrapper around integral equality and scalar-coefficient uniqueness. Distinguish this from equality of auxiliary tensor fields. |
| **9** | **D: real-analytic-to-packet producer** | A genuine mismatch if the formalised application is advertised under real analyticity alone. General compact/family complexification is not a bounded finishing unit here. |
| **10** | **C: unconditional application from `hironaka`** | Essential to an *unconditional general resolved-geometry application*, but an upstream programme—not a missing final lemma in the expansion engine. |
| **11** | **J: optimal spectral lattice** | A refinement beyond mere existence of the target expansion unless the paper or plan explicitly promises optimal support. |
| **12** | **K: curved sublevel sets** | An additional application/producer. Not required to close the cube blow-up or the abstract certificate theorem. |
| **Out** | **L** | Outside this phase. Do not reopen Programme P or `averaging_dataset.tex`. |

### What is—and is not—“beyond the paper”

C, D and general E should not simply be dismissed as mathematics beyond the paper. They may be prerequisites to matching the paper’s stated generality. The distinction is:

- **Missing formal coverage of the paper:** C, D, general E, and general B where the paper asserts the corresponding existence/application.
- **Not a bounded closure task for this phase:** those same general existence programmes.
- **Optional refinements/applications:** K and optimal support in J, unless expressly asserted by the target theorem.

---

# 2. Track I: the normalised expectation

## 2.1 Correct theorem shape

Write \(L=\log n\). After factoring the common leading power, suppose the observable-free denominator and an observable numerator have expansions
\[
D(n)=n^{-\lambda}
 \left(P_0(L)+\sum_{\delta>0}n^{-\delta}P_\delta(L)\right),
\]
\[
N_\phi(n)=n^{-\lambda}
 \left(Q_{\phi,0}(L)+\sum_{\delta>0}n^{-\delta}Q_{\phi,\delta}(L)\right),
\]
with the appropriate all-order remainder interpretation. Assume:

- the positive exponent support generates a locally finite additive monoid;
- \(P_0\neq0\), with positive highest-degree coefficient;
- the expansions apply to the **same denominator** \(N_1\), not an independently chosen normaliser;
- the numerator belongs to the corresponding compatible expansion class.

Then the robust target is
\[
\frac{N_\phi(n)}{D(n)}
=
\sum_{\substack{\delta\in\Delta\\\delta\le A}}
n^{-\delta}R_{\phi,\delta}(\log n)
+o(n^{-A}),
\qquad
R_{\phi,\delta}\in\mathbb R(L).
\]

The coefficient recursion is
\[
R_{\phi,0}=\frac{Q_{\phi,0}}{P_0},
\]
\[
R_{\phi,\delta}
=
\frac{
Q_{\phi,\delta}
-\sum_{\substack{\beta>0,\ \eta\ge0\\\beta+\eta=\delta}}
P_\beta R_{\phi,\eta}
}{P_0}.
\]

All logarithmic terms at the leading \(n\)-power belong in \(P_0\). Do not divide only by its highest log monomial and call the resulting finite expression an all-order expansion.

### Why this matters

For example,
\[
D(n)=n^{-\lambda}(\log n+1),\qquad
N(n)=n^{-\lambda}
\]
gives
\[
E(n)=\frac1{\log n+1}.
\]
Any fixed truncation of its inverse-log series has an error much larger than \(n^{-A}\) for every \(A>0\).

Even allowing finitely many **negative** log powers does not fix that problem.

A Laurent-log quotient theorem is a useful special case when \(P_0\) is a single log monomial. A polynomial-log quotient theorem needs still stronger closure conditions.

## 2.2 Four-unit design

### Q1 — Normalisation profile and finite rational-log algebra

**Structures**

- A normalisation profile containing \(\lambda\), the exponent support and \(P_0\).
- Locally finite exponent data, including the additive closure needed by division.
- Finite rational-log truncations and their evaluation for sufficiently large \(n\).

**Producer**

Polynomial-log numerator/denominator truncations → recursive quotient coefficients.

**Gates**

- Each coefficient recursion is finite.
- Nonzero polynomial denominators are eventually nonzero at \(\log n\).
- Rational-log functions have at most polynomial-log growth.
- Test \(1/(\log n+1)\), not just constant leading denominators.

**Stopping rule:** no general-purpose Hahn-series library.

---

### Q2 — Quotient asymptotics with remainders

**Producer**

All-order numerator and denominator expansions → rational-log quotient expansion.

Use input expansions somewhat beyond the desired output cutoff. The proof can then absorb all polynomial-log factors into the positive power margin. This avoids brittle boundary-cutoff bookkeeping.

**Gates**

- Eventual positivity/nonvanishing of the denominator.
- Explicit remainder estimates after division.
- Products and discarded terms remain \(o(n^{-A})\).
- No unjustified inference that positivity of the leading coefficient alone supplies the missing expansion/support hypotheses.

**Stopping rule:** a scalar analytic theorem, independent of resolution geometry.

---

### Q3 — Certificate integration and observable linearity

Use `MomentKernelData` and `withObs` to ensure that:

- the denominator is exactly the observable \(1\) integral;
- numerator coefficients come from the same observable-free kernel;
- quotient coefficients are linear in the observable, because division is by fixed denominator data.

Produce an expectation expansion from the landed certificate expansion. Reuse `jetFunctional`; do not reintroduce a finite-order distribution target.

**Gates**

- The theorem’s left-hand side is literally \(N_n[\phi]/N_n[1]\).
- The observable \(1\) produces expectation identically \(1\).
- Coefficients are independent of auxiliary certificates at the scalar level available from existing canonicity.

---

### Q4 — Leading probability measure and regressions

Under \(\mu_{\mathrm{lead}}(W)>0\), prove
\[
E_n[\phi]\longrightarrow
\frac{\int_W\phi\,d\mu_{\mathrm{lead}}}
     {\mu_{\mathrm{lead}}(W)}.
\]

Connect this to the rational-log expansion’s leading ratio, and regress against the existing posterior/chart quotient limits.

For the cube with \(p(0)>0\), obtain \(E_n[F]\to F(0)\).

**Mirror gate**

The mirror may mark the following as formalised:

> “All-order normalised expectation expansion, with rational functions of \(\log n\) as coefficients, conditional on the stated compatible numerator/denominator expansions and a positive leading normaliser.”

It may mark the paper’s exact theorem only if its coefficient class and remainder convention agree—or after the paper’s formulation is corrected.

---

# 3. Track A/B: a genuine cube blow-up

## 3.1 Concrete choice of \(U\)

Use the real projective blow-up presented as the tautological line bundle in projector coordinates.

Let \(V=\mathbb R^d\), preferably through the Euclidean-space API, and define
\[
\mathcal P_1(V)
=
\{P\in\operatorname{End}(V):
P^*=P,\ P^2=P,\ \operatorname{tr}P=1\}.
\]
For \(d\ge2\), set
\[
U=\{(x,P)\in V\times\mathcal P_1(V):Px=x\},
\qquad
\pi(x,P)=x.
\]

This is the total space of the tautological line bundle over \(\mathbb RP^{d-1}\).

The exceptional divisor is
\[
E=\{(0,P):P\in\mathcal P_1(V)\}.
\]

**Important distinctions**

- \(U\) is not globally `Fin d → ℝ` with one set of blow-up coordinates.
- A subtype of \(V\times\mathbb RP^{d-1}\) is an equivalent presentation, but projector coordinates avoid requiring a separate projective-space quotient API.
- The algebraic subtype definition does not itself prove the analytic-manifold properties: supply the atlas.
- Use the full bundle as the ambient resolved space. Treat \(\pi^{-1}([-1,1]^d)\) as the compact localisation region, not as a boundaryless analytic manifold.
- This \(\pi\) collapses \(E\) and is genuinely nontrivial for \(d\ge2\). Handle \(d=1\) separately; blowing up a principal one-dimensional centre is not the intended nontrivial geometry test.

## 3.2 Explicit charts and phase

In chart \(i\), write \(v_i=1\). Define
\[
\Psi_i(t,v)=
\left(tv,\frac{vv^\top}{\langle v,v\rangle}\right).
\]
Then
\[
\pi\circ\Psi_i(t,v)=tv,
\qquad
|\pi\circ\Psi_i(t,v)|^2=t^2\langle v,v\rangle.
\]

The Euclidean change-of-variables density is
\[
|t|^{d-1}\,dt\,dv.
\]

Thus this is precisely where the former chart model becomes real geometry:

> Replace the chart’s synthetic `π = id` interpretation by the commuting equation \(\pi\circ\Psi_i=\beta_i\), where \(\beta_i(t,v)=tv\).

On an overlap,
\[
v'=\frac{v}{v_j},\qquad t'=t\,v_j,
\]
so the normal transition is fibre-linear with a nonvanishing base-dependent factor.

The phase unit \(1+\sum_{k\ne i}v_k^2\) must be handled by an exact identity or a proved analytic normalisation. It cannot be discarded.

## 3.3 Normal bundle and tubular map

Here the geometry is unusually favourable:
\[
N_EU\simeq\text{tautological line bundle}.
\]
Under this identification, the tubular map is simply
\[
\Phi(P,w)=(w,P),\qquad Pw=w,
\]
restricted to a suitable neighbourhood of the zero section.

This gives a genuine analytic tubular map **from the total normal bundle**.

Do not require a global trivialisation \(E\times\mathbb R\). The tautological line bundle is nontrivial.

Likewise, the exceptional divisor has local defining functions \(t_i\), with
\[
t_j=v_jt_i
\]
on overlaps. It need not have a global regular real-valued defining function.

This is a decisive API gate: if `ResolvedGeometry` requires globally framed normals or global regular scalar equations for every divisor, the proposed blow-up does not fit unchanged.

## 3.4 Compatibility fields that actually matter

A sufficient transport package should contain:

1. **Ambient map compatibility**
   \[
   \pi\circ\Psi_c=\beta_c.
   \]

2. **Labelled divisor compatibility**  
   Local active labels map to global labels, and local divisor zero sets equal pullbacks of the labelled global divisors.

3. **Incidence compatibility — the role of `incident_eq`**  
   The chart’s active/incidence set agrees with the global incidence set at the represented point. Here there is one label: exceptional on the zero section, none off it.

4. **Stratum transport**  
   Chart base points map to the claimed stratum; duplicate representations are handled by the localisation scheme.

5. **Normal and tubular compatibility**  
   A fibrewise linear normal identification, with a commuting tubular-germ diagram. This gives transport of normal derivatives and tensor contractions.

6. **Measure/density transport**  
   An exact change-of-variables statement including \(|t|^{d-1}\), localisation weights and multiplicity handling.

7. **Core and tail transport**  
   A transported `AnalyticCoreDecomposition`, integrability, convergence and phase-gap estimates—not just equality of the final scalar integral.

8. **Observable independence**  
   Localisation, normal identifications and kernel data are selected independently of \(\phi\).

Do **not** initially accept arbitrary analytic tubular coordinate changes. Nonlinear normal changes can mix derivative orders; base changes depending on the normal variable can introduce tangential derivatives. A fibre-linear, tubular-compatible interface is a clean sufficient class and covers this model.

## 3.5 Six-unit design

### B0 — Geometry feasibility gate

Inspect `ResolvedGeometry` and `ResolvedNormalData` against:

- a nontrivial normal line bundle;
- local, unit-related divisor equations;
- local frames on compact stratum pieces;
- a tubular map from the total normal bundle.

**Deliverable:** either a construction path or a precise minimal interface correction.

**Stop immediately** if the interface fundamentally assumes global coorientability. Do not conceal the problem using a disjoint union of charts and call it the blow-up.

---

### B1 — Projector blow-up and atlas

Construct the projector base, \(U\), \(\pi\), \(E\), charts and transitions.

Prove the chart descriptions, incidence equations and the geometric facts required by the existing certificate API. Establish compactness/properness facts needed for localisation.

**Gate:** \(\pi^{-1}(0)=E\); off the origin, \(\pi\) has the expected unique inverse.

---

### B2 — Genuine resolved normal data

Produce `ResolvedGeometry` and `ResolvedNormalData`:

- singleton exceptional label;
- zero-section stratum;
- tautological normal bundle;
- analytic tubular map above;
- local frames and exact compatibility.

**Gate:** chart-frame transitions reproduce \(t'=tv_j\), including signs.

---

### B3 — Compatible chart-core transport

Introduce a small structure—say `CompatibleResolvedChart`—packaging the commuting maps, stratum/normal identifications and exact measure/core transport.

Producer sequence:
```text
local collar / SingletonChartCertificate data
    → transported analytic core
    → transported coefficient-kernel data
    → local contribution on genuine U
```

Reuse local internals of `BlowUpCube.cube_hasExpansion`. The final scalar theorem alone is not enough to reconstruct this transport.

**Gate:** a normal derivative of \(\phi\circ\pi\) becomes exactly the local derivative already used by the producer.

---

### B4 — Finite assembly on the genuine space

For the first application, use measurable a.e.-disjoint direction sectors or an already-established multiplicity-corrected cover.

For maximum-coordinate sectors:

- assign ties by a fixed rule;
- prove discarded/tie boundaries have zero relevant measure;
- extend analytic packets beyond the integration pieces;
- keep the seams out of any claim that these pieces themselves form open analytic charts.

Do not demand an analytic partition of unity. An a.e.-disjoint decomposition is sufficient for this application.

**Producer**
```text
finite transported cores + exact localisation + tail gap
    → ResolvedCertificate with cores : AnalyticCoreDecomposition
    → CoefficientCertificate
```

**Gate:** exact equality with the original cube integral for all admissible observables and \(n\), not merely asymptotic agreement.

---

### B5 — Target theorem, leading measure, density bridge

Apply
`ResolvedCertificate.CoefficientCertificate.hasCoordFreeExpansion`
to this genuine \(U,\pi\).

Recover the landed cube coefficients by scalar canonicity. Connect its leading functional to
\[
\pi^{d/2}p(0)\,\delta_0.
\]

For H, prove the transported leading density identity in this model, preferably as equality of finite measures or equality against all admissible test functions.

**Gate:** three descriptions agree:

1. the genuine resolved-space expansion;
2. `BlowUpCube.cube_hasExpansion`;
3. the canonical leading measure.

**Stopping rule:** one genuine blow-up application plus the sufficient transport interface it actually exercises. No arbitrary-SNC theorem yet.

---

# 4. Handling H and the bounded fidelity work

## H: do not replace a uniform asymptotic statement with a pointwise heuristic

The relation
\[
\widetilde M_\gamma(v,n)
=
c_0(v)M_\gamma(n)+\text{subleading}
\]
needs:

- the precise meaning of “subleading”;
- uniformity or an integrable domination argument in \(v\);
- the correct active normal variables;
- proof that the omitted amplitude terms are genuinely lower at the claimed scale.

In monomial models, higher Taylor terms need not always raise the \(n\)-exponent; they may instead lower log degree, and noncritical variables can contribute through the full amplitude. Do not make a blanket “only the value at the origin matters” lemma.

For the chart-density identity, first prove a chart pushforward/partition formula for the **leading measure**. Expressing it as
\[
\int_K q(v)\,dv=\int_{S_I}c_0\,|dv|
\]
is then a consequence, with chart multiplicity and density conventions explicit.

## G: small follow-on units

After B5:

- **Parity:** require invariance of the complete kernel measure under normal reflection, not merely a symmetric normal domain.
- **\(d=1\):** add the missing cube leading value \(\sqrt\pi F(0)p(0)\).
- **Gaussian Gamma fidelity:** for the radial Gaussian cube, a natural sharp regression is
  \[
  \int_{[-1,1]^d} H(x)e^{-n|x|^2}\,dx
  \sim
  \pi^{d/2}n^{-d/2}
  \sum_{\ell\ge0}
  \frac{\Delta^\ell H(0)}{4^\ell\ell!}\,n^{-\ell},
  \]
  under the relevant regularity assumptions.

That last result sharpens the current half-step support in this model. It should not be advertised as a universal Gamma formula for arbitrary resolved monomial phases.

---

# 5. Explicit non-claims and suggested wording

These are primarily **formalisation-status statements**. They do not require retracting a mathematically justified paper theorem, but the mirror must not imply that its full generality has been mechanised.

### General resolution application — C / general B

> “The formalised all-order coordinate-free expansion is conditional on compatible resolved geometric, analytic-core and coefficient data. We do not yet construct these data for a general analytic problem from the current `hironaka` interface.”

### Real analyticity — D

> “The unconditional local producers currently assume a holomorphic-extension packet. A general producer of such packets from real analyticity has not been formalised.”

### Analytic tubular existence — E

> “Analytic tubular germs are supplied as compatible normal data. Their construction is explicit in the covered models; a general analytic tubular-neighbourhood existence theorem is not formalised.”

After B2, add the genuine blow-up to “covered models.”

### Leading densities — H, until the relevant bridge lands

> “The canonical scalar leading functional and leading measure are formalised under the stated hypotheses. Their general identification with the displayed chartwise intrinsic density is not yet formalised.”

### Expectations — I, until Q1–Q4

> “All-order expansions of the unnormalised integrals and leading normalised limits are formalised. An all-order expansion of the normalised expectation is not yet formalised.”

After Q1–Q4:

> “All-order normalised expectations are formalised with rational-logarithmic coefficients. A finite polynomial-logarithmic form requires additional hypotheses.”

### General collars, coefficient formulas and support — F/G/J

> “The listed collar models and coefficient identities are formalised. General partial-active collars, the stated general parity/Gamma refinements, and optimal spectral support are not claimed beyond those models.”

Update this sentence piecemeal as units land.

### Other domains — K

> “No general curved-sublevel-domain producer is claimed.”

### Outside this phase — L

> “The ‘otherwise larger’ exponent analysis and the number-operator boundary case are outside the coordinate-free expansion completion reported here.”

---

# 6. Audit of §1 versus CCCIII

On the supplied inventory, CCCIII establishes the target **conditional on the certificates**. The following distinctions should be explicit.

## 6.1 Conditional theorem versus existence programme

The safe headline is:

> “The target expansion is proved from resolved and coefficient certificates; producer coverage is listed separately.”

“Coordinate-free expansion completed” would currently conflate those two achievements.

## 6.2 Adapted partition of unity \(\rho_I\)

A supplied localisation datum is not an existence theorem for the plan’s specified adapted partition.

Decide whether §1 really requires that particular presentation:

- If yes, construct it with the necessary packet compatibility.
- If no, replace the requirement by an exact finite localisation scheme, allowing a.e.-disjoint or multiplicity-corrected assembly.

A nontrivial real-analytic subordinate partition of unity is generally not available. Smooth cutoffs also cannot simply be multiplied into a holomorphic packet without checking what analyticity the producer needs. Tangential localisation extended through a tubular map is a possible design, not an automatic solution.

## 6.3 \(n\)-independent \(\nu_I\)

The theorem should bind the stratum measures before \(n\) and the truncation order:
\[
\exists(\nu_I)_I,\ \forall A,\ \ldots
\]
with those same measures throughout.

Do not infer this merely from having an expansion separately for every \(A\). Audit whether the certificate fixes the measures and whether all moving-collar dependence lies in the moments/kernels.

The same applies to a coherent coefficient family across cutoffs.

## 6.4 Observable-independent coefficients

The displayed target asserts that \(B_{I,r,\alpha,j}\) does not depend on \(\phi\).

`MomentKernelData` is the right mechanism, but check that:

- localisation is observable-independent;
- the chosen coefficient certificate is built from the kernel;
- the same \(B\)-fields work for the declared observable class.

A theorem saying “for every \(\phi\), there exists a coefficient certificate” is weaker.

## 6.5 Normal series and integration

Your inventory says this is landed: the normal series is summed pointwise inside the stratum integral. Preserve that exact meaning. Do not silently strengthen it to interchange of summation and integration or a finite-jet representation.

## 6.6 Leading measure equality

Given CCCX as described, the bridge to the canonical leading measure is **not an unfilled general scalar gap**.

What may remain is:

- applying the bridge to each new producer;
- identifying that measure with the paper’s intrinsic chart-density construction;
- proving equality on the intended full observable/test-function class.

For expectations, also require positive total leading mass. Nonnegative prior alone does not guarantee that the proposed leading scale has positive mass.

## 6.7 Scope of canonicity

Scalar coefficient canonicity across certificates does not imply canonical pointwise tensor fields or canonical stratum densities. Those stronger assertions require separate transport or uniqueness arguments.

---

# 7. Phase stopping rule

Declare this phase complete when:

1. **Expectation closure:** the correct all-order quotient theorem is connected to the observable-free certificate API, including the normalised leading probability measure.
2. **Genuine geometry closure:** the projector/tautological-line blow-up carries actual `ResolvedGeometry`, `ResolvedNormalData`, `ResolvedCertificate` and `CoefficientCertificate`, with nontrivial \(\pi\).
3. **Transport fidelity:** the genuine application agrees with the landed cube expansion and canonical leading measure.
4. **Statement audit:** §1 and the mirror accurately separate certificate theorems, producer coverage, scalar canonicity and remaining existence assumptions.

Parity, \(d=1\), and box-extension agreement are sensible small follow-ons if bounded by existing APIs.

**Do not make completion depend on** general Hironaka output, arbitrary SNC gluing, general analytic complexification, a general analytic tubular theorem, optimal spectra, curved domains, or Programme P.

The resulting claim would be substantial and accurate:

> **A certificate-based all-order coordinate-free expansion, an all-order normalised expectation theorem in the correct asymptotic class, and a complete application on a genuine nontrivial resolved space.**
