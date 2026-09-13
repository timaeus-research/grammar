## Recommendation

**Do not presently launch a programme claiming “general analytic \(K\) ⇒ `ResolvedCertificate`.”** There are two separate gaps:

1. **The proposed generality is too broad unless hypotheses on \(W,\varphi,\phi\) are added.**
2. Even under appropriate analytic/tameness hypotheses, the supplied resolution results do not give the **disjoint analytic product localisation** required by the current certificate.

My recommendation is:

- bump to **e301b8971**;
- retain Daniel’s general weighted-transport work;
- add exact-transport and analytic-resolution adapters;
- pursue a **strengthened, explicitly sector-admissible R4** as the next certificate-producing milestone;
- make the missing sectorisation theorem a named research gate, not an implicit obligation buried in the Q induction;
- regard **R3 as the preferred general smooth-amplitude expansion programme**, if general expansions become more important than supplying this particular certificate.

R1 and R2 are possible research directions, not currently justified unit-scale completion plans.

---

## 1. First fix the scope of the target theorem

“\(K\geq0\) analytic on a compact \(W\)” is not enough.

### 1.1 Arbitrary compact integration domains can destroy power–log asymptotics

For example, take
\[
K(x)=x^2,\qquad \varphi=\phi=1,\qquad
W=\{0\}\cup\bigcup_{j\geq0}[4^{-j}/2,4^{-j}].
\]
This is compact, and the phase and amplitudes are analytic. The integral has discrete-scale behaviour; its leading \(n^{-1/2}\)-scale has a nonconstant log-periodic modulation, rather than an ordinary constant power–log coefficient.

Thus some control of the domain near the zero set is essential. Reasonable alternatives include:

- \(W\) contains a neighbourhood of the relevant zero set, so its boundary is entirely in the positive-phase tail;
- a suitable compact semianalytic/subanalytic domain, with its boundary included in the resolution/rectilinearisation problem;
- an explicitly supplied admissible localisation domain.

A compact-domain hypothesis alone cannot be repaired by resolving \(K\).

### 1.2 Analyticity of \(K\) does not supply analytic amplitudes

The amplitude hypothesis must cover the pulled-back prior, observable, Jacobian unit, and localisation weights. For the present engine, the right ultimate requirement is a `HolomorphicBoxExtension`-type packet, uniform over each compact base.

Ambient analyticity near the relevant zero set can be a sufficient input to a producer. Merely smooth \(\varphi\) or \(\phi\) is not.

### 1.3 Locally identically zero phases require separate treatment

If \(K\) vanishes on an open component carrying positive prior mass, the usual exceptional-set-null argument fails, and the integral has a nondecaying contribution. Separate that case, or exclude it componentwise. Do not silently feed it to a producer requiring positive normal phase exponents.

These are mathematical hypotheses, not implementation details.

---

## 2. Ranking the routes

| Route | Assessment |
|---|---|
| **Strengthened R4** | Best next certificate milestone. Require actual product-sector data, not just a constructor whitelist. |
| **R3** | Best established route to general smooth-amplitude expansions under appropriate domain assumptions. Does **not** automatically produce the existing analytic `ResolvedCertificate`. |
| **R1** | Potentially sound, but the requisite theorem is substantially stronger than ordinary tubular-neighbourhood existence. Research gate. |
| **R2** | Potentially sound, but a redesign of the local-to-global resolution construction, not a transport-field flip. Research gate. |
| **R6: rectilinearise walls as well as phase** | Plausible for tame domains; requires a new substantial geometric theorem. Not supplied by Q′ or Watanabe 2.3. |
| **R5** | Useful exact-transport identity, not a coefficient-level correction mechanism. |

### R1: what would actually have to be proved

A common normal projection \(r\) would indeed solve one important overlap problem:
\[
A_i\cap A_j\text{ base-null}
\quad\Longrightarrow\quad
r^{-1}(A_i)\cap r^{-1}(A_j)\text{ measure-null},
\]
provided the measure has the asserted product disintegration.

But you need more than “analytic fibres”:

- common projections on overlapping neighbourhoods;
- compatibility at incident strata;
- fibre coordinates and fibre domains fitting the product cores;
- analytic phase normalisation in those same coordinates;
- analytic density and observable in those coordinates;
- coefficient continuity and a uniform holomorphic radius over compact bases;
- agreement with the supplied `ResolvedNormalData`.

A tubular construction can solve the geometric overlap problem while destroying the required phase or amplitude normal form. Watanabe 2.3 does not export this package.

### R2: the hard part is not exact transport

Measurably disjointifying a finite cover is easy. Disjointifying it **while retaining product domains and analytic normal amplitudes** is the missing theorem.

In particular, replacing a local domain by
\[
\operatorname{dom}_i\setminus
\phi_i^{-1}\!\left(\bigcup_{j<i}\phi_j(\operatorname{dom}_j)\right)
\]
usually introduces normal-dependent walls. The resulting indicator cannot be absorbed into the current normal series.

Threading a stronger invariant through Q would therefore require new Step C and compact-cover constructions. It should not be described as finishing Daniel’s `wt` flip.

### R3: mathematically viable, but a different output interface

The distribution/Mellin route handles smooth localisation correctly. Its residues are not determined by finite total normal jets: they retain dependence on variables transverse to the pole-producing directions. That is exactly how it avoids the §2 obstruction.

A unit-scale implementation is conceivable through:

1. one-variable Mellin continuation with parameter-dependent smooth amplitudes;
2. finite-part distributions and residue operators;
3. tensor/iterated continuation;
4. uniform remainder estimates;
5. finite-chart exact transport.

This is substantial but conventional analysis. It should produce a separate smooth-amplitude expansion interface, with a comparison theorem on analytic amplitudes—not pretend to construct the existing analytic series fields.

### R4 needs strengthening

Even an a.e.-disjoint `PartialResolution` does not automatically give product cores:

- its compact domains can have arbitrary shapes;
- arbitrary `restrict` can cut normal fibres;
- `comp` introduces pullbacks/intersections of domains, which need not be products;
- absorbing a positive phase unit can bend box boundaries.

Thus the correct scope is **sector-admissible resolutions with product-preserving restrictions and compositions**, not simply “no `sigma` or Step C”.

### R5 cannot be corrected after expansion

Writing \(m(y)\) for multiplicity, under the usual change-of-variables hypotheses,
\[
\sum_i (\phi_i)_*(J_i\,dx)=m(y)\,dy.
\]
Dividing by \(m\) inside the integral is valid:
\[
\sum_i(\phi_i)_*
  \left(J_i(x)\frac{1}{m(\phi_i x)}\,dx\right)=dy
\]
on the covered full-measure set.

But \(1/(m\circ\phi_i)\) is generally discontinuous along normal-dependent walls. It recreates the amplitude obstruction.

Nor can scalar coefficients of the integral with amplitude \(m\varphi\phi\) determine those for \(\varphi\phi\). The correction must occur at the amplitude/measure level. The exception is constant multiplicity a.e., where ordinary scalar division works.

---

## 3. Proposed units and their order

Names below are **proposed declarations**, not claims about existing APIs.

### Phase A — Land unconditional, reusable facts

### H0. `Monomialize.Transport.AnalyticResolutionExports`

**Repository:** hironaka local copy.

Add wrappers around both exact analytic outputs without changing frozen declarations.

**Watanabe export, schematic:**
```lean
theorem exists_analyticModification_at
    (hK : AnalyticNear K p)
    (hzero : K p = 0)
    (hnonzero : ¬ LocallyIdenticallyZero K p) :
    ∃ P : AnalyticModificationAt K p, True
```

The packet should expose:

- an open neighbourhood `V` of `p`;
- analytic manifold `U`;
- analytic `g : U → V`;
- properness **as a map to `V`**;
- surjectivity;
- analytic isomorphism off the zero set;
- centred maximal-atlas charts with exact phase monomials;
- analytic, nonvanishing Jacobian units.

Export the nonnegative/even-exponent corollary separately, with the required neighbourhood nonnegativity hypothesis.

Also export a Q′ packet retaining analytic units; do not route through the continuous-unit or two-sided-bound readouts.

**Gate:** `#print axioms` on every public wrapper; verify that the exact identities remain on open chart targets.

---

### G0. `Grammar.Resolution.AnalyticSeed`

**Repository:** grammar.

This should be the **first grammar adapter**.

```lean
theorem exists_analyticResolutionSeed_at
    (hK : AnalyticNear K p)
    (hzero : K p = 0)
    (hnonzero : ¬ LocallyIdenticallyZero K p) :
    Nonempty (AnalyticResolutionSeed K p)
```

`AnalyticResolutionSeed` should contain the exact geometric/local analytic information from H0, **but no `ResolvedCertificate` field** and no invented global divisor or tubular data.

A second adapter:
```lean
def QChart.toAnalyticMonomialChartPacket
    (h : IsAnalyticQChart ...) :
    AnalyticMonomialChartPacket ...
```

**Gate:** imports only the intended axiom-clean chain. Include examples testing phase units, absolute Jacobian units, and exponent conventions.

---

### H1. `Monomialize.Transport.MeasureIdentity`

**Repository:** hironaka local copy; build on Daniel’s branch.

Turn the lower-integral transport predicate into equality of measures.

Let
\[
\rho=(\mathrm{volume}|_N).\mathrm{withDensity}(a).
\]
Prove
\[
\boxed{
\sum_i(\phi_i)_*
 \left[
  (\mathrm{volume}|_{\operatorname{dom}_i})
  .\mathrm{withDensity}
  \bigl(J_i\,\omega_i\,(a\circ\phi_i)\bigr)
 \right]
=\rho .
}
\]

Here \(J_i=|\det D\phi_i|\), in the appropriate `ENNReal` encoding.

**Inputs:** `HasWeightedTransport R ω`, measurability of all densities.

**Output:** a measure equality suitable for `Measure.map` composition and grammar transport lemmas.

**Gate:** derive equality using indicators/measurable sets; test \(g=1\). The overlapping Step C cover must fail the weight-one test unless its domains or weights have actually changed.

---

### H2. `Monomialize.Transport.SectorMultiplicity`

**Repository:** hironaka local copy.

Separate three propositions:

1. individual chart injectivity off exceptional null sets;
2. pairwise a.e.-disjoint chart images;
3. a.e. coverage.

Their conjunction gives multiplicity one and hence weight-one transport.

**Transport:**
\[
\boxed{
\sum_i(\phi_i)_*
  \bigl((dx|_{\operatorname{dom}_i})
        .\mathrm{withDensity}(J_i(a\circ\phi_i))\bigr)
=\rho .
}
\]

**Where disjointness is established:** here, for the standard dominant-coordinate sectors. Use the null tie walls \(|x_a|=|x_b|\).

Give a separate multiplicity-corrected identity as a useful theorem, but do not mark its density analytic.

**Gate:** distinguish the standard blow-up constructors from `blowUpResolutionOn`. “Weight one for two blow-up constructors” must not accidentally include the genuinely overlapping Step C construction.

---

### G1. `Grammar.Resolution.ExactLift`

**Repository:** grammar, using G0.

Watanabe’s off-zero isomorphism already gives an exact lifted measure without choosing overlapping chart weights.

Let \(\rho\) be the prior measure and \(Z=\{K=0\}\). Under \(\rho(Z)=0\), pull \(\rho|_{V\setminus Z}\) back through the measurable equivalence
\[
U\setminus g^{-1}(Z)\simeq V\setminus Z,
\]
then include it into \(U\).

Prove:
\[
\boxed{g_*\mu=\rho|_V.}
\]

For compact \(C\subset V\), restrict to \(g^{-1}(C)\), obtaining:
\[
\boxed{
(g|_{g^{-1}(C)})_*\mu_C=\rho|_C.
}
\]

**Important:** this also fixes the properness target issue. A proper map into an open `V` is not automatically proper into \(\mathbb R^d\). The compact restriction is proper into \(\mathbb R^d\).

**Gate:** prove the zero-set-null hypothesis from analytic nontriviality only where valid. No local-identically-zero component may be hidden in this argument.

This unit settles **exact localisation transport**, not product-core decomposition.

---

## Phase B — The sector-admissible certificate programme

### H3. `Monomialize.Transport.ProductSectorAtlas`

**Repository:** hironaka local copy.

Define a strengthened packet, not a new field on frozen `PartialResolution`.

Its raw ingredients should include:

- finitely many compact product boxes;
- chart maps analytic on neighbourhoods of those boxes;
- a.e. injectivity and nonvanishing Jacobian off prescribed null sets;
- exact monomial phase identities;
- analytic nonvanishing Jacobian units;
- pairwise a.e.-disjoint images;
- coverage of a specified low-phase region;
- any normal-domain restrictions explicitly recorded.

Keep the integration domain/prior localisation separate: one must prove that their indicators are absent, base-only, or otherwise already encoded by admissible sectors.

A useful theorem shape is:
```lean
theorem ProductSectorAtlas.exactTransport
    (A : ProductSectorAtlas K Ω)
    (ha : Measurable a) :
    ∑ i, Measure.map (A.chart i) (A.sourceMeasure a i)
      = (volume.restrict Ω).withDensity a
```

**Where disjointness lives:** it is proved for the target sector images, not manufactured merely by taking a disjoint union of chart labels.

**Gate:** no arbitrary measurable domain is allowed to pass as a “box sector”.

---

### H4. `Monomialize.Transport.ProductSectorConstructors`

**Repository:** hironaka local copy.

Start with:

1. the already sectorised cube blow-up;
2. single analytic coordinate isomorphisms on suitable boxes;
3. `prodId` with genuine product domains;
4. explicitly product-preserving restrictions;
5. explicitly product-preserving compositions.

For restriction and composition, require and prove the relevant domain-shape hypotheses. Do not export unconditional closure theorems.

**Gate:** each constructor must preserve both:

- the measure identity;
- the product/analytic structure.

A constructor preserving only the first belongs in Daniel’s transport library, not in this stronger atlas class.

---

### G2. `Grammar.Resolution.SectorAnalyticInput`

**Repository:** grammar.

From each compact analytic box packet and admissible analytic prior/observable, produce the existing holomorphic-extension input.

Required analytic amplitude:
\[
A_i(u)
 = \varphi(\phi_i(u))\,\phi(\phi_i(u))\,|b_i(u)|
\]
after extracting the monomial Jacobian factor.

If there is a tangential base, produce:
```lean
x : C(Base, WeightedL1CoefficientSpace ...)
```
with common radius and summability bounds.

**Gates:**

- absolute value of the Jacobian unit is analytic on the relevant fixed-sign neighbourhoods;
- compactness supplies a uniform extension radius through a proved lemma;
- no smooth partition weight or normal-dependent indicator enters \(A_i\).

For Q′ charts with a positive phase unit, distinguish:

- producing an expansion using the existing unit-aware producer;
- producing a **constant-phase certificate**.

The latter additionally needs a domain-compatible phase-normalising coordinate change. Local unit absorption alone does not prove that it preserves the atlas.

---

### G3. `Grammar.Resolution.SectorNormalModel`

**Repository:** grammar.

There are two legitimate outputs; choose explicitly.

**A. Artificial chart-model geometry.**  
Construct a finite disjoint union of compact chart-box models, with coordinate divisors and their standard normal data. Define \(\pi\) componentwise.

Compactness gives properness. The exact transport from H3 gives the required prior pushforward.

This can supply an existential certificate over a model geometry, without claiming that the model is Watanabe’s resolved manifold.

**B. The original resolved geometry.**  
Require an independently supplied finite divisor/tubular compatibility packet and prove the chart identifications.

Output A is the more unit-scale choice. Output B remains blocked by the missing global geometry exports.

**Gate:** taking a disjoint union makes source components disjoint, but does **not** correct overlapping target multiplicity. H3’s exact transport is still mandatory.

---

### G4. `Grammar.Resolution.SectorCertificate`

**Repository:** grammar.

Apply the existing compact-box/water-filling producer chartwise, then the finite-sum/transport producers.

The principal identities should be visible in the theorem chain:
\[
\mu=\sum_k\mu_k+\mu_{\rm tail},
\qquad
\mu_k=\mu|_{\mathrm{core}_k},
\qquad
\pi_*\mu=\rho.
\]

**Where core disjointness is established:**

- different chart components: by the disjoint-union construction;
- within a chart: by the existing water-filling decomposition;
- identification with the target prior: by H3, not by the disjoint union.

Then obtain `CoefficientCertificate` from the existing analytic-input producers.

**Gate:** regression against the cube certificate and CCCLXVIII coefficient equality.

---

### G5. `Grammar.Resolution.PositiveTail`

**Repository:** grammar.

Prove the low-phase coverage and gap separately.

A sufficient compactness argument is: the omitted support is compact and disjoint from \(K^{-1}(0)\). Then
\[
K\geq\delta>0
\]
there.

Do not infer a uniform gap merely from “every zero point has some chart” without proving that the retained region contains a neighbourhood of the relevant zero set.

**Gate:** exact measure decomposition, positive \(\delta\), and amplitude integrability sufficient for the exponential-tail estimate.

G4 and G5 together produce the certificate theorem.

---

## 4. The explicitly blocked generalisation unit

Introduce, but do not assert as proved:

```lean
theorem exists_productSectorAtlas_of_analytic_tame_data
    (...) :
    Nonempty (ProductSectorAtlas K Ω)
```

Its hypotheses must specify the domain and amplitude scope discussed above.

There are three possible implementations:

- R1-compatible analytic-normal control data;
- R2-sector-preserving resolution induction;
- R6-simultaneous rectilinearisation of phase, localisation walls, and domain boundary.

**Neither Q′ nor Watanabe 2.3 currently discharges this theorem.**

For a research pilot, require a nontrivial overlap test involving both:

- a normal-dependent tangential transition, such as \(s'=s+u\);
- two local resolutions joined by the compact-cover mechanism.

Passing only the centred cube tests does not address the obstruction.

---

## 5. Daniel’s branch

**Continue it, but separate the two invariants.**

Use:

1. a general measurable/smooth `HasWeightedTransport` layer;
2. an optional stronger `NormalAnalyticWeight` or product-sector layer.

The first serves both consumers as exact measure infrastructure. Its smooth partition-of-unity producers remain useful to the free-energy-formula library and to a future R3 engine.

For grammar’s current engine, a weight producer must prove something like:
```lean
ω (Φ s u) = χ s
```
or, more generally, supply a holomorphic normal-series packet for the weighted amplitude.

Base-only weights are a sufficient special case, **but the common-fibration theorem must precede that producer**. Changing the desired weight type does not construct the fibration.

Thus one common transport abstraction can serve both consumers; one undifferentiated “smooth weight” certificate cannot.

---

## 6. Pin choice and dependency choice

**Pin e301b8971.** It has the verified exact theorem, matching Mathlib, and avoids unnecessary E6/Step 11 material.

Amend the stale grammar note about Watanabe 2.3 after reproducing the axiom audit.

Use the outputs as follows:

- **(b), Watanabe 2.3:** exact local modification, off-zero measurable equivalence, exact lifted measure, already unit-free phase charts.
- **(a), Q′ analytic charts:** finite constructive chart families, transport-constructor work, and analytic-unit packets.
- **Neither:** global compatible tubular structure or disjoint product sectorisation.

There is no reason to import main HEAD for this programme.

---

## 7. Stopping rule and non-claim

Stop after the strengthened R4 theorem if the programme has not proved an actual product-sector existence theorem beyond the already sectorised constructors.

More concretely, stop before:

- hiding normal-dependent indicators inside an analytic-amplitude claim;
- treating arbitrary `restrict` or `comp` as product-preserving;
- using a smooth partition of unity as a normal-analytic one;
- deriving a constant-phase box atlas solely from local unit absorption;
- asserting global divisor/tubular data from Watanabe’s local chart conclusions.

Recommended wording:

> We construct `ResolvedCertificate` and `CoefficientCertificate` for analytic integration data equipped with a finite, exact-transport, sector-admissible analytic product atlas, and for the explicitly verified constructors producing such atlases. We do not prove that every analytic phase on a compact integration domain admits such an atlas. In particular, Q′ analytic monomialisation and Watanabe 2.3 alone are not used to assert a general certificate-supply theorem.

If using the artificial chart-model geometry, add:

> The supplied certificate is over the constructed chart-model geometry; it is not asserted to be a certificate over the original Watanabe resolution manifold.

---

## 8. Corrections and qualifications to §§2–5

The central analytic-localisation obstruction is correct. The main qualifications are:

1. **Infinite normal order:** correct in the stated relevant pole regime. Not every monomial has a nonzero contribution—parity and cancellations can kill terms—but no finite total Taylor truncation generally controls all leading coefficients.

2. **Nonnegative phase ⇒ even exponents:** requires nonnegativity on a full open neighbourhood of the centred chart. Nonnegativity only on \(W\) does not suffice. For example, \(K(x)=x\) on \(W=[0,1]\).

3. **Base-only cutoffs are analytically harmless, but not geometrically automatic.** They require common fibres or separately proved compatibility.

4. **A.e.-disjoint images do not imply product domains.** This is the missing qualification in R4.

5. **Properness is relative to the target.** Proper \(U\to V\), with \(V\) open, is not automatically proper \(U\to\mathbb R^d\).

6. **Dimension two is not yet a theorem.** Shared-wall fitting by tangential recoordinatisation is a plausible pilot, but must preserve phase form, analytic amplitudes, product domains, and crossing compatibility. “Divisors are curves” does not establish all four.

7. **Smooth-weight transport is exact and valuable.** Its failure is specifically as input to the current analytic-normal-series certificate, not as a change-of-variables method.

The useful immediate advance is therefore substantial but sharply bounded: **land exact analytic resolution seeds and exact lifted measures now; make product-sector existence the visible remaining theorem.**
