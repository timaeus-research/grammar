## Executive verdict

**Phase 3 meets its stated stopping gate.** The supplied source implements the intended chain:
\[
\text{holomorphic neighbourhood data}
\longrightarrow \text{uniform closed-face normal series}
\longrightarrow \text{a sufficiently small collar}
\longrightarrow \text{the existing certificates and expansion}.
\]

The important fidelity point is correct: **agreement is on the entire real slice of the chosen complex neighbourhood**, not merely on the box. This supplies the two-sided normal germs required by `OriginalFaceSeries`.

My recommendation is:

1. **Close the paper-facing work with a small hypothesis-localisation/hygiene phase.**
2. Do not make real-analytic complexification the next major project.
3. For continued work toward the standing goal, pursue **signed boxes, then a concrete geometric instance**, using those to determine the general atlas interface.
4. Do not describe the present endpoint as production of certified general resolved geometry.

This is a source-level audit of the supplied files, not a fresh repository build. In particular, the definition of `HasCoordFreeExpansion` and the internals of the upstream certificates were not supplied; claims about their precise asymptotic semantics remain conditional on that existing interface.

---

# A. Audit

## A1. Fidelity and the existential conclusion

### The analytic packet is the right packet

The decisive fields are:
```lean
eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re
```

Set
\[
U=\{w:\operatorname{complexify}(w)\in\Omega\}.
\]
Then \(U\) is an open real neighbourhood of the box. Thus the packet asserts exactly the neighbourhood agreement needed downstream.

The P4 proof actually uses this strength:

1. `complexify_originalNormalMap_mem` puts the normal perturbation in `Ω`.
2. `evalF_uniformSeries` reconstructs the real part of the holomorphic function.
3. `eqϕ` and `eqφ` identify that reconstruction with the **original functions**, including at normal arguments outside the positive box.

There is no hidden substitution of box-only agreement.

### The buffer and shrink are faithful

The construction uses:

- one positive buffer \(R\) around the compact embedded box;
- one common bound for both extensions on its compact tube;
- Cauchy integration radius \(r=R/2\);
- series radius \(\rho=R/4\).

The insertion has operator norm at most one in the supplied sup norms. Consequently there is no missing dimension factor in the containment argument.

P1 correctly separates two obligations:

- continuity and boundedness produce a summable family of Cauchy coefficients;
- holomorphicity gives reconstruction.

That separation is mathematically sound and reusable.

### CCCXXXII really exhibits constructed certificates

The conclusion does not say merely “there exists some expansion certificate.” Its measures and field are explicit applications of:
```lean
certificate ...
coeffCertificate ...
```
to `A.faceSeries` and the chosen collar. That is the intended production statement.

“Constructed” here means **defined in Lean from the inputs, using classical choices**. The buffer, bounds and collar are not computationally effective numerical outputs. This is entirely compatible with the reported axioms.

### Quantifier order: no defect

There are two different uses of “A” in the material: the extension packet and an asymptotic truncation threshold. They should be distinguished in documentation.

In the displayed theorem:
\[
\forall A_{\mathrm{ext}},\quad \exists\delta,\quad
\operatorname{HasCoordFreeExpansion}(\cdots).
\]

The collar is chosen after the extension data, as designed. It is **not chosen after a truncation threshold in the displayed statement**. Provided `HasCoordFreeExpansion` internally quantifies over all truncation orders, one collar works for the full expansion.

No uniform collar over all holomorphic input packets should be expected: their available neighbourhoods can shrink arbitrarily. A uniform-in-a-family theorem would require a shared neighbourhood or buffer.

### `d - 1` and `commonQ`

These are **non-sharp indexing choices, not weakened remainder assertions**, assuming the existing expansion predicate has its advertised meaning.

- `d - 1` is an ambient upper bound on logarithmic degree.
- `commonQ` gives a common containing lattice.
- Unused spectral slots can have zero coefficients.

Neither claims the minimal spectrum, actual nonzero logarithmic degree, or optimal denominator. Moreover, there need not be one “exact log degree” appropriate to every exponent and every observable: resonance and cancellation matter.

**Recommendation:** retain these choices. Do not bundle spectral minimality into the next phase.

---

## A2. Hypothesis hygiene

**Yes, the public theorem should eventually omit all three hypotheses**
```lean
Measurable ϕ
Measurable φ
Integrable φ ((volume.restrict W).withDensity ...)
```
while retaining nonnegativity on \(W\).

But the argument must be stated correctly:

> Continuity on the box does not imply global measurability of functions whose values away from the analytic neighbourhood are arbitrary.

What follows directly is:

- continuity of both restrictions to \(W\);
- measurability, or a.e. strong measurability, relative to `volume.restrict W`;
- boundedness of both restrictions;
- weighted integrability of the observable.

The compact box has finite volume. If \(|\phi|\le B_\phi\) and \(|\varphi|\le B_\varphi\) there, then
\[
\int_W |\phi|\,\operatorname{ofReal}(\varphi)\,dw
\le B_\phi B_\varphi\,\operatorname{vol}(W),
\]
with the usual real/`ENNReal` interpretation.

### The safest wrapper route

Preserve the upstream interfaces. Construct globally measurable representatives agreeing with the original functions on the **whole real slice \(U\)**:
\[
\widetilde\varphi=1_U\,\operatorname{Re}(H_\varphi\circ\operatorname{complexify}),
\qquad
\widetilde\phi=1_U\,\operatorname{Re}(H_\phi\circ\operatorname{complexify}).
\]

They are measurable because the expressions are continuous on the open set \(U\), and are zero outside it. They retain exactly the required normal germs.

Then:

1. build the extension packet for the representatives using the same `Ω`, `Hϕ`, `Hφ`;
2. prove weighted integrability on \(W\);
3. apply the existing `_nonneg_on` theorem;
4. transfer the expansion’s original integral back by equality on \(W\).

**Do not zero-extend merely from \(W\) before building the face series.** That would destroy the negative normal germs at boundary faces.

If the expansion predicate records derivatives of the original functions as well as the integral, the final transport lemma should use equality on \(U\), not merely on \(W\). Inspect that definition first.

This is a cheap follow-up compared with the other candidates, but I would budget **two or three small units**, rather than promise a one-file proof.

---

## A3. Soundness, satisfiability and public forms

### No apparent vacuity problem

Natural nontrivial examples include:

- \(\varphi=1\), with any real polynomial observable;
- positive polynomial priors;
- \(\varphi(w)=\exp(-\sum_i w_i^2)\);
- \(\varphi(w)=w_1\) on a positive box, using `_nonneg_on`.

For polynomial examples, take `Ω = univ` and use the same polynomial over \(\mathbb C\). The box is nonempty in the final theorem because `ha` and `hd` are positive.

The global-nonnegativity version is genuinely more restrictive. For example, a prior with a simple zero on a boundary divisor may change sign across that divisor. The box-local version is therefore important, not cosmetic.

### “Extension” means real-part representation

The packet does **not** require
\[
H_\varphi(\operatorname{complexify}w)=\varphi(w)\in\mathbb C.
\]
It requires equality of real parts. That is sufficient for these proofs.

Consequently the complex function is not uniquely determined by this packet. For example, imaginary-valued contributions on the real slice may leave its real part unchanged. Do not silently identify this interface with a unique complexification theorem.

### `ofRealNhd` is the right public form

The restriction
```lean
Ω ∩ realParts ⁻¹' V
```
is correct and avoids requiring the original functions to agree on irrelevant real points in the original `Ω`.

A minor ergonomic refinement would allow agreement only when both `w ∈ V` and `complexify w ∈ Ω`. The present constructor asks for more agreement than it actually uses. This is not a correctness issue.

### Box-only agreement

Keep it out of the core bridge.

A separately named result could eventually prove an expansion of the original **box integral** using analytic germs supplied by chosen extensions. It must not claim that arbitrary original functions have those two-sided germs.

Once the localisation/transport infrastructure exists, such a theorem should be comparatively inexpensive. Still, it is optional for the paper. If added, use a name such as:

```lean
hasCoordFreeExpansion_of_chosenHolomorphicExtensions_on_box
```

and explicitly identify whose germs supply the coefficients.

---

## A4. The mirror sentence

The mathematical chain is accurately described. Two qualifications should be made explicit:

1. this is the **coordinate monomial model**, not arbitrary resolved geometry;
2. the current theorem still assumes the stated measure-theoretic conditions and box nonnegativity.

Suggested replacement:

> Finally, in the coordinate monomial model on \([0,a]^d\), the local normal series are produced from analytic neighbourhood data. Assuming the stated measure-theoretic hypotheses and nonnegativity of the prior on the box, a prior and observable represented as real parts of holomorphic functions on a complex neighbourhood of the embedded box, with agreement on its real slice, yield uniform closed-face normal series at a common positive radius. The construction uses a uniform complex buffer, bounds on a compact tube, and Cauchy estimates with strict radius shrink. A sufficiently small collar level is then selected, and the existing compact-box producer gives the coordinate-free expansion of the original integral, with its stratum measures and coefficient field constructed from these data.

Retain the complexification non-claim and add:

> This is a producer theorem for the coordinate model; construction of a compatible resolved atlas for general SNC geometry is not included.

After the hygiene follow-up, remove “the stated measure-theoretic hypotheses.”

---

## A5. Reviewer flags and small cleanups

I see no phase-3 fidelity failure in these six files. I would flag the following presentation/API points.

| Item | Assessment |
|---|---|
| `analyticUniformSeries` docstring describes “a holomorphic family” although the definition assumes only continuity and bounds | Clarify that holomorphicity is needed only for reconstruction. |
| `evalF_uniformSeries` is documented as identity for the “original real function” | Its actual conclusion is `evalF = Re H`; the original-function identification occurs in `faceSeries`. Adjust the docstring. |
| `ofRealNhd` lives in the final expansion file | Prefer the buffer/packet module, or a small constructors module, so users need not import the expansion to construct a packet. |
| `ofRealNhd` is marked `noncomputable` | Apparently unnecessary for this constructor; check and remove if Lean permits. |
| `continuousOn_recentred` branches on `Nonempty (Fin (nI I + 1))` | Correct but unnecessarily elaborate: that type has the explicit element `0`. |
| `norm_complexify_le` | Sufficient; an isometry/equality lemma would be useful later, but is not required here. |
| Repeated huge certificate expressions | Introduce a named produced-data bundle or local definitions for maintainability; preserve transparent access to the actual constructors. |
| `hφm` absent from certificate arguments but included in theorem | Not dead: it is passed to the upstream expansion theorem. |
| Common bound stores nonnegativity that later definitions do not visibly consume | Harmless; a `bound_nonneg` accessor may be convenient. |
| `zeroOrders d` in the final theorem | Important scope restriction: this is not yet the general monomial Jacobian-weight producer. |

The plan’s section 6 needs more substantial correction. It mixes two levels:

- **coordinate-model endpoint:** extensions remain hypotheses; face radii, majorants and the local certificate data are now produced;
- **general resolved application:** the compatible geometry, transport, units and local analytic data have not all been produced.

“Everything else … is a theorem” should be qualified as **“given the relevant certificate interfaces”**. Otherwise it suggests that the general application is already a producer theorem.

---

# B. Recommended direction

## Ranking

This is my ranking for the **next investment**, not a ranking of mathematical importance:

| Rank | Candidate | Reason |
|---:|---|---|
| 1 | **(ii) Hypothesis localisation/hygiene** | Small, closes a genuine public-interface defect, and makes the endpoint accurately local. |
| 2 | **(iii) G: signed boxes** | Bounded scope; directly relevant to real divisors; tests transport and finite assembly. |
| 3 | **(iv) E: projector blow-up instance** | Highest-value next geometric milestone, provided its actual chart/Jacobian/unit obligations are audited first. |
| 4 | **(v) J: observable-independent functionals** | Important for the intended language, but needs a fixed observable space and control of choice dependence. |
| 5 | **(vi) General SNC producer** | The central remaining goal, but premature as the next monolithic implementation. Develop its interface through examples. |
| 6 | **(i) General real-analytic complexification** | Mathematically standard, potentially a substantial new Mathlib development, and does not solve the geometric bottleneck. |

**General SNC remains the programme’s destination.** Ranking it fifth means “do not begin by implementing the entire general theorem.”

---

## Top-candidate unit plan: local analytic input, no global measure hypotheses

The names below are statement sketches, not verified existing Mathlib identifiers.

### H1 — Restricted regularity and weighted integrability

**Statements**
```lean
A.continuousOn_prior :
  ContinuousOn ϕ W

A.continuousOn_observable :
  ContinuousOn φ W

A.integrable_observable :
  Integrable φ
    ((volume.restrict W).withDensity
      (fun w => ENNReal.ofReal (ϕ w)))
```

Also produce the corresponding restricted a.e. measurability lemmas.

**Route**

- compose `A.holϕ.continuousOn` with `continuous_complexify`;
- compose with `Complex.continuous_re`;
- use `A.eqϕ` on `W`, and similarly for `φ`;
- use compactness for uniform bounds;
- use finite volume of the compact box;
- use the `withDensity` integrability machinery, or first prove finite weighted mass and apply bounded-function integrability.

**Pitfalls**

- `ContinuousOn` gives restricted, not global, measurability;
- density measurability must be relative to the restricted measure;
- real/`ENNReal` coercions can dominate the proof;
- avoid imposing strict positivity of the prior.

**Size:** roughly 100–220 lines, depending on available restricted-measure helpers.

### H2 — Measurable representatives preserving analytic germs

Define `A.realDomain := complexify ⁻¹' A.Ω`, and representatives zero outside that domain.

**Statements**
```lean
isOpen_realDomain
box_subset_realDomain

measurable_priorRepresentative
measurable_observableRepresentative

priorRepresentative_eq_on_realDomain
observableRepresentative_eq_on_realDomain

representativeExtension :
  HolomorphicBoxExtension a
    A.priorRepresentative A.observableRepresentative
```

**Route**

Use the measurable subtype restriction of a continuous-on function and measurable extension by zero, or the corresponding `MeasurableOn`/indicator API.

**Pitfalls**

- globally defined `Hϕ` need not be measurable outside `Ω`;
- consequently one cannot simply assert global measurability of `Re ∘ Hϕ ∘ complexify`;
- keep the same holomorphic functions and neighbourhood in the new packet;
- do not require analytic nonnegative representatives off the box.

**Size:** roughly 100–200 lines.

### H3 — Public local-input expansion and transport

**Target form**
```lean
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension_local
    (A : HolomorphicBoxExtension a ϕ φ)
    (hd : 0 < d) (ha : 0 < a)
    (hϕ0W : ∀ w ∈ W, 0 ≤ ϕ w) :
    ∃ δ ..., HasCoordFreeExpansion
      produced.stratumMeasure
      produced.field
      produced.spectrum
      W (CoordModel.phase d k) ϕ φ
```

Here `produced` must be a named definition built from the representative extension and the existing producer—not a new assumed certificate.

**Route**

- apply the current `_nonneg_on` theorem to the representatives;
- discharge integrability with H1;
- transport back to the original functions;
- expose a general expansion congruence lemma if one does not already exist.

**Pitfalls**

- inspect whether the predicate depends on functions only through the integral;
- distinguish equality of the resulting expansion from definitional equality of certificates;
- retain germ agreement if derivatives enter the predicate;
- document that the internal certificate may use a nonnegative measurable representative.

**Size:** roughly 120–250 lines, plus a modest congruence lemma if needed.

### Stopping gate

Stop this phase when:

1. the public theorem assumes only the extension packet, geometric positivity conditions, and prior nonnegativity on the box;
2. no global measurability or integrability assumptions remain;
3. modifications outside the real analytic neighbourhood are explicitly harmless;
4. the measures and field are still visibly produced;
5. a constant-prior/nonconstant-polynomial example instantiates the theorem;
6. the paper and plan distinguish the coordinate producer from general geometry.

**Expected total:** about 350–700 lines. The uncertainty is primarily upstream congruence and measure APIs.

---

## Notes on the other candidates

### (i) Complexification: a plausible route, not a cheap bridge

I would not promise a ready-made Mathlib theorem
```lean
AnalyticOnNhd ℝ f U → ∃ complex holomorphic extension near W
```
without checking the pinned Mathlib revision.

A plausible development is:

1. extract local real power-series witnesses from `AnalyticAt`;
2. complexify their continuous multilinear coefficients;
3. prove operator-norm control, allowing a radius loss;
4. sum the complex series and establish holomorphicity;
5. prove agreement with the real function;
6. glue local extensions near the compact box.

Two serious issues:

- **Scalar extension is not scalar restriction.** Complexifying a real multilinear map needs a construction and norm estimates. Dimension/degree-dependent losses must be absorbed by shrinking radii.
- **Gluing requires the right uniqueness theorem.** Agreement on a totally real open set is enough, but not by naively applying a one-variable “accumulation point” identity theorem in several variables.

Use canonical extensions agreeing with the **full real-valued function**, not arbitrary real-part representatives. For balls centred at real points, overlap geometry can simplify the gluing proof.

**Estimate:** a research-sized development—potentially 6–12 substantial units and thousands of lines, unless a close finite-dimensional complexification API already exists. Begin with a capped API reconnaissance and a one-local-germ prototype, not a commitment to the global theorem.

### (iii) Signed coordinates

Use the finite reflection cover first:
\[
R_\varepsilon(u)_i=\varepsilon_i u_i,\qquad
\varepsilon\in\{\pm1\}^d.
\]

For an even monomial phase, reflection preserves the phase. Pull back prior and observable, run the positive-box theorem, and sum.

Essential obligations:

- reflected boxes cover the signed box;
- overlaps lie in coordinate hyperplanes and have Lebesgue measure zero;
- reflections preserve volume;
- extensions pull back along the corresponding complex linear maps;
- normal derivatives acquire the correct sign factors;
- local expansions assemble on a common spectral lattice.

`posPart` is benign algebraically:
\[
(\varphi^+)\circ R_\varepsilon
=(\varphi\circ R_\varepsilon)^+.
\]
But **never claim that positive part preserves analyticity**. Apply the analytic producer before the existing certificate-level positive-part conversion.

Even/odd cancellation is a useful later corollary. It is not a replacement for transport and stratum assembly.

**Estimate:** 4–6 units. Summing scalar expansions is easier than producing a clean signed-stratum tensor statement.

### (iv) Projector blow-up instance

Start with an obligation inventory, not a final theorem name.

Check whether the model requires:

- Jacobian monomial orders other than `zeroOrders`;
- tangential chart parameters;
- signed normal coordinates;
- a nonconstant analytic unit in the phase;
- overlap corrections;
- cutoffs not analytic in the normal variables.

A blow-up chart normally introduces Jacobian vanishing, so direct use of the displayed zero-order producer cannot be presumed.

A credible instance must prove the actual map, Jacobian/density transport, coverage, phase normal form and tail estimate. An instance that merely repackages these as hypotheses does not advance certificate production.

### (v) Observable-independent coefficient functionals

First fix geometry and prior, then choose a common observable space:

- holomorphic functions on a fixed neighbourhood with appropriate seminorms; or
- a suitable smooth test-function space, after finite-jet dependence is proved.

For each fixed spectral slot, aim for:

1. finite normal-jet dependence;
2. linearity in the observable;
3. continuity in a finite-order seminorm;
4. representation by strata-supported distributions.

The full infinite expansion need not have one finite-order bound. Also, the present collar depends on the analytic packet, which includes the observable. J requires either a fixed shared buffer or independence-of-collar/choice results. It is not merely currying the existing coefficient field.

---

# Minimal interface for general SNC geometry

The right interface has two layers.

## 1. Exact finite assembly

For a finite chart index set, supply:

- measurable chart domains and maps to the original integration space;
- local reference measures and measurable nonnegative weights;
- a proved change-of-variables identity accounting for multiplicity;
- local phase and prior/observable pullback identities;
- a tail region with positive phase gap and finite absolute amplitude mass.

Prefer an identity valid for a suitable class of test functions, or a measure identity, over an equality only for the target integrand. That prevents the interface from hiding the observable dependence.

## 2. Compatible local geometric producers

Each chart must provide:

- divisor labels and exponent data;
- monomial Jacobian orders and residual density;
- exact phase normalisation, including the analytic unit;
- the admissible normal-series input;
- exact local core transport;
- stratum maps and conormal transition laws;
- compatibility allowing chartwise densities and moment contractions to assemble into global stratum data.

The interface must **not assume local asymptotic expansions**. Those should come from local producers.

Two warnings are central:

1. **A smooth partition of unity generally destroys holomorphic normal-series input.** Analytic compactly supported partitions are not a general escape route. One needs cutoffs constant/analytic in normal directions on the relevant cores, with transitions handled in a gapped region, or a stronger smooth-amplitude producer.
2. **An a.e.-disjoint partition can destroy box geometry.** Measurable chart ownership is not enough if the resulting local domains have uncontrolled normal boundaries.

Thus “apply a partition of unity” is not yet a formalisation plan. The cutoff/domain compatibility is part of the substantive geometry certificate.

---

# Should the programme stop here for the paper?

**Yes—stop adding major scope for this paper.** I would perform the small hygiene closure and documentation corrections, but not make publication contingent on complexification, signed SNC geometry or the projector instance.

The paper may accurately claim:

> A machine-checked coordinate-free expansion framework, together with a certificate-producing implementation for the compact positive coordinate-monomial model, starting from holomorphic real-part neighbourhood data. The normal series, collar selection, stratum measures and coefficient field are produced within Lean.

It should not claim:

- general real-analytic complexification;
- production of a resolved SNC atlas for arbitrary input geometry;
- an instantiated projector blow-up application unless its geometry is actually discharged;
- optimal spectral support;
- observable-independent continuous coefficient distributions unless J is proved.

**The phase-3 gate is met. The standing global goal is not.** The next large advance should be a genuinely discharged geometric instance, rather than another layer of assumed certificates.
