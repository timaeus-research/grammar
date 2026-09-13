## Decision

**Close E4F as accepted: F0–F1 complete, F2 structural support and packet independence complete, parity and Gamma evaluation explicitly deferred.** You met the “F1, preferably F2” gate; stopping at the new reflection-to-coefficients bridge was the right decision.

For the next phase, I recommend **a bounded J-min gate: observable-independent finite-order coefficient functionals for a fixed certified geometry and prior**. Do not open general intrinsic gluing, automatic complexification, or the partial-active collar concurrently.

After J-min, conduct a paper-claim closure check. If it passes, move to `averaging_dataset.tex`; parity should not become an automatic prerequisite.

This assessment is based on the supplied statements and sources, not an independent checkout/build of `cf32d46`.

---

## 1. E4F closure and statement hygiene

### What is now established

The useful separation is:

| Result | Dimension | Input |
|---|---:|---|
| All-order cube expansion | `d ≥ 1` | Signed-box packet and certified pieces |
| Support in `(d + ℕ)/2` | `d ≥ 1` | Kernel candidate-exponent support |
| Vanishing below `d/2` | `d ≥ 1` | Structural support |
| Value of the coefficient at `d/2` | `d ≥ 2` | Leading-measure comparison |
| Packet independence on the declared spectrum | `d ≥ 1` | Expansion uniqueness |
| Odd-order cancellation; support in `d/2 + ℕ` | — | Deferred |
| Explicit higher-coefficient formula | — | Deferred |

That is a sound, paper-useful stopping point.

### Cite `cube_hasExpansion_support`, not the F1 wrapper

Use these as the principal paper-facing pair:

* `cube_hasExpansion_support`;
* `cubeCoefficient_leading`, with its separate `1 < d` qualification.

The F1 wrapper remains a valid compatibility/convenience theorem, but it is no longer the best headline. Its expansion statement unnecessarily carries the leading-measure dimension restriction.

Also, **neither wrapper itself states the leading coefficient equality**. The prose should cite the equality theorem separately rather than describing the wrapper as though it bundled both conclusions.

### Small changes I would make

1. **Fix the union-of-candidates wording.**

   Say:

   > The assembled coefficient vanishes if its exponent is a candidate exponent of no chart.

   Equivalently, support is contained in the **union** of chart candidate sets. “Off the candidate exponents of every chart” is easy to misread as an intersection statement. The theorem’s quantifiers are correct.

2. **Distinguish support from parity thinning.**

   On the declared log-free half-integer spectrum, restricting to `(d + ℕ)/2` is equivalent to removing exponents below `d/2`. Its additional value is the structural proof, its application to individual pieces, its statement without spectrum membership, and the removal of the `d ≥ 2` restriction.

   It does **not** yet remove alternate half-integer orders.

3. **Give the stronger vanishing theorem a descriptive public name.**

   For example, an alias such as:

   ```lean
   cubeCoefficient_eq_zero_of_exponent_lt_half_dim
   ```

   is preferable to making `cubeCoefficient_eq_zero_of_lt'` the long-term public endpoint. Keep existing names; no disruptive rename is needed.

4. **Say “coefficient at the leading candidate exponent.”**

   `π^(d/2) F(0) p(0)` can vanish. Without a nonvanishing hypothesis, this is not necessarily the first nonzero asymptotic term.

5. **Keep the scope of independence precise.**

   The new theorem proves independence of the analytic packet for fixed `p, F`, on the declared spectrum. It does not by itself prove independence of arbitrary cube decompositions, nor equality of local coefficient fields.

6. **Clarify the word “signed.”**

   Here the signs belong to the box/piece construction; the prior still satisfies `p ≥ 0`. Avoid wording that suggests a signed prior is covered.

None of these is a reason to reopen E4F. They are closure hygiene.

---

## 2. Ranking the next directions

My ranking **for the paper, rather than for mathematical generality**, is:

1. **(ii) J-min: observable-independent finite-order coefficient functionals.**
2. **(vi) Companion note, once the bounded paper-claim check passes.**
3. **(i) Parity, as an optional independent bounded gate.**
4. **(iii) E5 partial-active water-filling.**
5. **(iv) Genuine resolved gluing.**
6. **(v) Automatic complexification from real analyticity.**

The second position is deliberate: once the paper’s Lean claims are faithfully supported, a useful but optional refinement should not indefinitely postpone the companion note.

J-min is the best next fundamentals step because it addresses the distinction between:

> “For each observable, its scalar asymptotic coefficients are intrinsic”

and

> “There is a fixed coefficient functional acting on observables through their jets.”

CCCVIII supplies the first. The paper’s distributional language calls for a controlled version of the second.

---

## 3. Recommended gate: J-min

### Minimal faithful mathematical statement

Fix:

* the certified resolved geometry and normal-differential structure;
* the phase and prior/density;
* a fixed admissible **real vector space of observables**;
* a cutoff `A`.

For every relevant power-log index `q`, construct a linear coefficient functional
\[
L_q:\mathcal V\longrightarrow\mathbb R
\]
and prove that the existing scalar coefficient for each observable is `L_q φ`.

The substantial assertion is a representation
\[
L_q(\varphi)
 =
 \sum_I\sum_{r\le R_A}
 \int_{S_I}
 \left\langle D_{\!N}^{\,r}\varphi(s),B_{q,I,r}(s)\right\rangle\,d\nu_I(s),
\]
with the appropriate pullback of `φ` understood where observables live downstairs, such that:

* `R_A` is finite and independent of `φ`;
* the coefficient fields `B` are independent of `φ`;
* the integrals are justified by the existing certificate hypotheses;
* the formula agrees with the currently constructed scalar coefficients.

It is acceptable for the initial **representation** to depend on the certificate and cutoff. Scalar canonicity should establish that the resulting functional is intrinsic on common admissible observables. Do not require equality of the representing fields.

That is the minimal faithful jet-functional theorem. A `LinearMap` obtained only by choosing scalar coefficients and applying uniqueness is useful scaffolding, but is **not by itself** the paper’s jet representation.

### When may the mirror say “distribution”?

Linearity plus dependence on finitely many derivatives is not, by itself, a formal continuity theorem.

To use “distribution” without qualification, add a finite-order bound of the form
\[
|L_q(\varphi)|
 \le
 \sum_{I,r} C_{q,I,r}
 \sup_{s\in K_I}\|D_{\!N}^{\,r}\varphi(s)\|,
\]
or the corresponding bound appropriate to the actual stratum measures and supports.

With compactly supported/localised integrable fields, the natural constants come from their `L¹` norms. This can support an extension to smooth tests, provided the normal derivatives and their topology are available there.

Two important boundaries:

* A functional on analytic observables should initially be called an **analytic jet functional**, unless the requisite continuity/test-function interface is proved.
* A distribution upstairs acts on downstairs observables through pullback. Its pushforward support lies in the images of the relevant strata. Do not conflate the two spaces.

In particular, compactly supported analytic functions on a connected open ambient domain are not a suitable replacement for the usual smooth test space.

### Observable domain

Do not let “admissible observable” mean merely “there exists some packet” without proving closure under addition and scalar multiplication.

For the first gate, a good choice is a **fixed common extension domain**, with fixed geometry/prior data and a vector space of compatible observable extensions or their real restrictions. Then prove independence of the extension witness.

This avoids making every linearity proof also solve a domain-intersection and packet-reconstruction problem.

### Five-unit plan

These are implementation work packages, not calendar estimates.

#### J0 — Freeze the interface

Specify:

* fixed data versus observable-dependent data;
* the admissible observable vector space;
* the coefficient index set and cutoff;
* the target finite-jet formula.

**Gate:** demonstrate that the existing construction’s observable dependence is confined to the claimed jets, apart from auxiliary analytic bounds/choices whose irrelevance will be proved.

If the density construction genuinely entangles the observable with the prior, stop and redesign before implementation spreads.

#### J1 — Separate the jet-linear kernel

Construct the finite-jet operator before substituting an observable. Prove its linearity and a uniform finite derivative-order bound at the fixed cutoff.

**Gate:** no representing coefficient field depends on the test observable.

This is the decisive bridge. Do not satisfy it by packaging a fresh field for each `φ`.

#### J2 — Recover the existing scalar coefficients

Prove that evaluating the jet operator on `φ` gives the existing coefficient construction.

Use uniqueness as needed to remove dependence on auxiliary radii, admissibility bounds, or packet choices.

**Gate:** an equality theorem connects the new functional to the old coefficient API; this is not a parallel expansion construction.

#### J3 — Package the functional and canonicity

Expose `L_q` as a real linear map. Prove:

* agreement across certificates on a common observable domain, using CCCVIII;
* compatibility across cutoffs;
* finite-normal-jet locality.

**Gate:** distinguish equality of functionals from equality of tensor representatives.

#### J4 — Continuity bound and paper wrapper

Prove the finite-order seminorm estimate. Package a distribution only if the available smooth-test API makes that a small consequence.

Add a concise theorem expressing the expansion with coefficients `L_q φ`.

**Gate:** the mirror uses exactly the achieved terminology:
“finite-order coefficient functional,” or “distribution” if continuity on the stated test space is established.

### Budget and stopping rule

Budget **five units, with at most one narrowly justified repair unit**.

* If J1 fails to expose an observable-independent kernel within its time-box, close the attempt with the interface obstruction documented.
* If J0–J3 land but smooth distribution packaging becomes a new infrastructure project, **close J-min at the jet-functional theorem**, with whatever continuity estimate is available, and qualify the paper.
* Do not make J-min include global gluing, canonical tensor representatives, automatic complexification, or explicit Gamma evaluation.

One further scope check: if the paper’s `E_n[φ]` denotes a coefficient of a **normalised expectation**, rather than of the unnormalised Laplace integral, state that separately. Dividing by the partition function requires the appropriate nonzero-leading-denominator hypothesis and a quotient-expansion argument. The numerator functional alone is not that theorem.

---

## 4. The deferred alternatives

### (i) Parity: the exact bridge and a bounded budget

The required bridge is **reflection equivariance of the total prior–observable jet contraction**, not merely reflection of the observable germ.

Let `σ*` flip the normal sign at `β`. At a common tangential base point, write the normalised Taylor coefficients of the residual prior-density factor and observable as
\[
a_{\sigma,i}(t),\qquad f_{\sigma,j}(t).
\]
After factoring out the positive-normal monomial of order `h₀`, establish
\[
a_{\sigma^*,i}=(-1)^i a_{\sigma,i},
\qquad
f_{\sigma^*,j}=(-1)^j f_{\sigma,j}.
\]
Consequently,
\[
T_{\sigma^*,\ell}(t)
 =
 (-1)^\ell T_{\sigma,\ell}(t),
\qquad
T_{\sigma,\ell}
 =
 \sum_{i+j=\ell}a_{\sigma,i}f_{\sigma,j}.
\]
For unnormalised derivative conventions, insert the existing binomial/factorial weights; they must be the same on both sides.

**The implementation bridge should connect this equality to the actual coefficient path** through `boxCoeff` / `familySpectralCoeff`, ultimately yielding the schematic theorem
\[
\operatorname{pieceCoefficient}(\beta,\sigma^*,q_\ell)
 =
 (-1)^\ell
 \operatorname{pieceCoefficient}(\beta,\sigma,q_\ell),
\quad
q_\ell=((d+\ell)/2,0).
\]

The tangential domain, measure, and phase-dependent weights must be shown invariant under this normal flip, or transported by an explicit equality/change of variables.

Crucially, **do not introduce `(-1)^(d−1)` from the Jacobian order**: the piece density uses the absolute Jacobian and a positive normal coordinate. The parity concerns the residual analytic Taylor order.

Budget **three to five units**:

1. reflection transport for the actual prior and observable jets;
2. convolution equivariance and passage through the coefficient kernel;
3. fixed-point-free sign pairing;
4. optional integer-step support wrapper and mirror cleanup.

**Hard gate after unit 2:** if the bridge requires a general functoriality theory for certificates, stop. No Gamma formula belongs in this gate.

### (iii) E5 partial-active collar

This is a genuine reusable generalisation, but not currently the highest-value paper closure task.

Provisional budget: **six to nine units**, subject to a first-unit interface audit:

1. active/inactive data and hypotheses;
2. partial-active water-filling map and inverse;
3. collar/image and boundary control;
4. differential/Jacobian calculation;
5. measure transport and integrability;
6. certificate construction;
7. specialisation to G;
8. specialisation to E3;
9. optional API consolidation.

The recovery theorems are acceptance criteria. A third implementation merely resembling G and E3 is not sufficient.

### (iv) The `π = id` wedge proposal

There is a cheap **integration assembly** construction here, but not obviously a cheap resolved geometry.

An a.e.-disjoint measurable wedge cover is enough to split an integral. It does not establish the normal-coordinate, smoothness, phase-monomialisation, or compatibility requirements of `ResolvedGeometry`.

In this model:

* the cube phase vanishes only at the origin, not along the wedge diagonals;
* the diagonal boundaries are partition seams, not the exceptional divisor;
* the blow-up’s directional exceptional fibre is precisely what `π = id` does not retain;
* pairwise intersections alone generally do not specify all higher-incidence/corner data.

Null seams may be irrelevant to the original volume integral but cannot simply be ignored in a proposed geometric stratum structure.

Thus:

> **Yes** to a small measurable/a.e. assembly interface, if useful beyond the already proved sum theorems.  
> **No** to presenting that interface as intrinsic resolved gluing without checking every geometric field.

A one-unit feasibility audit is reasonable. I would not budget a global resolved object until that audit identifies the transition and normal-structure obligations. This is a multi-gate project, not a substitute for parity or J-min.

### (v) Complexification

Keep the explicit holomorphic-extension hypothesis.

A real-analytic-to-complex-extension theorem entails local complexification of power-series data, compatibility, and a common neighbourhood over the relevant compact box, with the control required by your packet API. That is substantial analytic infrastructure.

At most authorise a **one-unit reconnaissance** of Mathlib’s scalar-extension and analytic-series interfaces. Do not promise a full implementation budget from the information here, and do not make it a paper-completion dependency.

---

## 5. The mirror

The content is appropriate, but twelve dotted theorem names in one sentence obscure the logical structure. Split it into three claims.

### A. Certified chart assembly

Cite the original-integral decomposition and the certified piece-to-cube expansion. Keep the intermediate singleton theorems in the annotation/dependency explanation rather than putting every one in the main sentence.

### B. Coefficient fidelity

The headline citations should be:

* `cubeCoefficient_eq_zero_of_not_support`;
* `cube_hasExpansion_support`;
* `cubeCoefficient_leading`;
* `cubeCoefficient_eq_of_packets`.

State explicitly:

* expansion and support: `d ≥ 1`;
* Gaussian value at `d/2`: `d ≥ 2`;
* packet independence: fixed `p, F`, declared spectrum.

`cube_hasExpansion_from_leading` can leave the headline sentence. Retain it in the detailed mapping if useful.

### C. Germ identification and boundaries

Retain `normalDifferential_obsRep_piece`. Mention `obsRep_piece_eventuallyEq` in the detailed annotation if the paper discusses germs explicitly.

Keep the current non-claims, and add or sharpen:

* no identification of the `d = 1` leading coefficient in this development;
* no claim that local tensor fields are packet-independent;
* no automatic passage from real analyticity to the required holomorphic packet.

A compact paper-facing formulation would be:

> For `d ≥ 1`, the signed-box analytic packet with nonnegative prior yields, by certified chartwise assembly, a log-free all-order expansion of the original quadratic cube integral supported at `(d+ℓ)/2`, `ℓ ∈ ℕ`. Its scalar coefficients are independent of the packet representing the same prior and observable on the declared spectrum. For `d ≥ 2`, the coefficient at `d/2` equals `π^{d/2}F(0)p(0)`. This is chartwise assembly, not an intrinsically glued resolved geometry; odd-order cancellation and explicit higher-coefficient evaluation are not asserted.

## Authorisation

**Accept E4F and freeze it after documentation/API hygiene. Open J-min alone, with the five-unit plan above. At its closure, audit the paper’s remaining Lean claims and, absent a concrete unsupported claim, transition to the companion note.** Parity remains a well-defined optional gate—not an unfinished obligation hidden inside E4F.
