## Executive verdict

**Phase G delivers the intended signed-coordinate expansion architecture. I would accept the mathematical implementation, but not yet close the stopping gate: item 7—the reflection-sensitive regressions—remains open.**

Two qualifications matter:

1. **The exact measure specification is proved.** The stronger gloss “\(2^d\) copies of *the same* one-sided measure at the deepest stratum” additionally requires equality of the piece masses. Reflection fixes the deepest stratum, but does not by itself prove packet-independence of those masses.
2. **This is a source-level audit of the supplied material, not a fresh kernel/build audit.** The literal §8 of consult #100 and the statement of CCCVIII were not included. I can audit the described gate obligations, but cannot honestly certify their original numbering or invoke an unseen canonicity theorem with exact arguments.

My recommendation is:

> **Close G with a small regression unit; then pursue E through a bounded Jacobian-weighted producer pilot. Do not start general SNC gluing yet.**

---

# A. Audit

## A1. Gate check

Here is the substantive gate reconciliation; the labels describe the obligations rather than reconstructing an unavailable numbered list.

| Obligation | Verdict | Evidence / qualification |
|---|---|---|
| Signed packet, reflection pullback, genuinely local analytic input | **Pass** | `pullback` uses the reflected complex domain and reflected holomorphic functions. No entire extension is required. |
| Finite reflection cover and legitimate integral decomposition | **Pass** | Ambient-volume overlap is removed a.e.; `setIntegral_signedBox_eq_sum` requires integrability, which G6 supplies. |
| Correct action on normal coordinates and jets | **Pass** | `reflNormal`, `refl_Φ`, and `normalDifferential_comp_refl` supply the actual normal-sign action. It is not merely a base-point pushforward. |
| Transport expansions, not resolved certificates | **Pass** | `piece_expansion` applies `hasCoordFreeExpansion_refl` to the one-sided expansion. No reflected `ResolvedCertificate` is constructed. |
| Common collar and common spectrum | **Pass** | `exists_delta_common` handles finitely many packet radii; `pieceCertificate_cores_k` identifies every exponent family with `coordCoresK k`. |
| RN-weighted assembly, with series justification | **Pass** | G5 proves the required summability/integrability for the actual observable germs; G4 then proves coefficient and expansion assembly. |
| Reflection-sensitive regressions | **Open** | Explicitly not landed. See below. |
| Public signed-box theorem and usable instance | **Pass** | Existential collar theorem, explicit coefficient-sum specification, a.e. support, and polynomial instance are present. |

### The measures and deepest-stratum multiplicity

The theorem proves exactly
\[
\nu_I^{\mathrm{signed}}
  =\sum_{\sigma\in\{\pm1\}^d}(R_\sigma)_*\nu_{\sigma,I}.
\]

This is the correct specification. In particular:

- all \(2^d\) signs participate;
- there is no quotient by the stabilizer of a stratum;
- there is no division of the measure by \(2^d\);
- ambient-volume nullity of coordinate hyperplanes is **not** used to discard stratum mass.

At the deepest stratum, reflection is the identity. Thus the unconditional consequence is
\[
\nu_{\mathrm{deep}}^{\mathrm{signed}}
  =\sum_\sigma \nu_{\sigma,\mathrm{deep}},
\]
after the natural identification.

If each piece is \(m_\sigma\delta_0\), this is
\[
\left(\sum_\sigma m_\sigma\right)\delta_0.
\]
It becomes \(2^d m\delta_0\) once \(m_\sigma=m\) is established.

**Do not cite `pieceCertificate_cores_k` for that equality:** it establishes independence of exponents, not independence of measures. The supplied material does not expose enough of `stratumMeasure` to independently verify equal deepest-stratum masses for arbitrary packets.

### The RN field

The field is correctly
\[
B^{\mathrm{signed}}=\sum_\sigma
  \frac{d\nu_\sigma}{d\nu^{\mathrm{signed}}}\,B_\sigma^{\mathrm{transported}}.
\]

“RN-averaged” is good explanatory language **a.e. with respect to the sum measure**. It should not suggest a canonical pointwise averaging rule on null sets.

The fundamental check is the proved identity
\[
C^{\mathrm{signed}}(\phi,q)
 =\sum_\sigma C_\sigma(\phi\circ R_\sigma,q).
\]
This is what prevents duplicated boundary mass from introducing an extra multiplicative factor.

### Public hypotheses

Apart from the coordinate-model parameters
\[
k:\mathrm{Fin}\,d\to\mathbb N,\qquad \forall i,\;0<k_i,
\]
the public existential theorem requires exactly:

- the signed packet `A`;
- `0 < d`;
- `0 < a`;
- nonnegativity of the prior on the signed box.

The collar inequalities are **existential conclusions**, not caller obligations.

There is no exposed requirement of:

- global nonnegativity;
- global measurability or integrability of the original real functions;
- global smoothness;
- an entire complex extension;
- a signed resolved certificate;
- pointwise disjoint orthants.

There is, however, an important **local hypothesis inside the packet**: `eqϕ` and `eqφ` hold throughout the real slice of `Ω`, not only on the box. That supplies the germs needed for normal derivatives at boundary points. This is intended, not hidden global regularity.

---

## A2. Regression checks: what to add

I recommend separating three questions:

1. Does finite orthant enumeration count the strata correctly?
2. Does RN assembly avoid overcounting?
3. Does normal reflection act on jets?

A test that only restates `expansionCoefficient_signed` answers mainly the first question. A test that only proves the odd integral is zero does not directly inspect the assembled field. We should have at least one concrete test of the actual tensor transport.

Below, coefficient notation suppresses the existing `normalData` arguments. These are exact mathematical test specifications, not claimed paste-ready Lean—the constructors for `MomentTensor` and the full coefficient definition were not supplied.

### R1. One-dimensional origin: mass and RN normalization

Use \(d=1\), \(I=\{0\}\), and write \(o\) for its origin.

First add the actual-piece specialization:
\[
\nu^{\mathrm{signed}}_{\{0\}}
 =\nu_{+,\{0\}}+\nu_{-,\{0\}},
\]
because both stratum reflections are identity, and
\[
C^{\mathrm{signed}}(\phi,q)
 =C_+(\phi,q)+C_-(\phi\circ(-\mathrm{id}),q).
\]

Then add a **synthetic assembly test with an explicit expected value**:

- each of the two untransported stratum measures is \(\delta_o\);
- only stratum \(I\), order \(r=0\), and one selected index \(q_0\) have a nonzero field;
- the tensor is evaluation of a zero-jet;
- the observable is \(1\).

Prove:
\[
\nu^{\mathrm{sum}}_I=2\delta_o,\qquad
C^{\mathrm{sum}}(1,q_0)=2.
\]

Optionally prove each RN weight is \(1/2\), \(\nu^{\mathrm{sum}}_I\)-a.e. The coefficient identity already tests the important normalization without forcing an explicit `rnDeriv` calculation.

This catches both “keep only one origin copy” and “sum the fields against the sum measure without RN weights.”

### R2. Two-dimensional crossing

Use \(d=2\), \(I=\{0,1\}\), and all four signs.

Add the actual-piece specializations:
\[
\nu^{\mathrm{signed}}_I
 =\nu_{++,I}+\nu_{+-,I}+\nu_{-+,I}+\nu_{--,I},
\]
and
\[
C^{\mathrm{signed}}(\phi,q)
 =C_{++}(\phi,q)
  +C_{+-}(\phi\circ R_{+-},q)
  +C_{-+}(\phi\circ R_{-+},q)
  +C_{--}(\phi\circ R_{--},q).
\]

For a non-tautological crossing fixture, use four copies of \(\delta_o\) and the order-zero evaluation tensor as above. Prove:
\[
\nu^{\mathrm{sum}}_I=4\delta_o,\qquad
C^{\mathrm{sum}}(1,q_0)=4.
\]

Do **not** make “the crossing is counted once” the expected behavior.

A useful additional crossing test uses the order-two tensor
\[
T(J)=J(e_0,e_1).
\]
Prove for every sign:
\[
(\operatorname{reflTensor}_\sigma T)(J)
 =\operatorname{sgn}(\sigma,0)\operatorname{sgn}(\sigma,1)\,T(J).
\]
With \(J=D^2(w_0w_1)(0)\), \(T(J)=1\). This exercises the mixed normal action at a genuine crossing.

### R3. Cheapest genuinely sign-discriminating test

**This is the minimum must-have.**

In \(d=1\), at the origin, let \(e\) be the positive unit normal and let
\[
T(J)=J(e)
\]
be the order-one evaluation tensor. Let \(\sigma_-\) denote the negative reflection. Prove
\[
\bigl(\operatorname{reflTensor}_{\sigma_-}T\bigr)
       \bigl(D_N(w\mapsto w_0)(o)\bigr)=-1,
\]
whereas
\[
T\bigl(D_N(w\mapsto w_0)(o)\bigr)=1.
\]

This fails immediately if `jetPull` is replaced by identity. It needs no analytic certificate, coefficient canonicity, Gamma function, or asymptotic uniqueness theorem.

To exercise assembly as well, extend the same fixture:

- two identical unreflected measures \(\delta_o\);
- two identical unreflected fields, supported at \(I,r=1,q_0\), with tensor \(T\);
- transport each by its sign;
- assemble with `glueField`.

Then prove
\[
C^{\mathrm{sum}}(w\mapsto w_0,q_0)=0.
\]

The two unassembled contributions are \(1\) and \(-1\). Omitting normal-sign transport gives \(2\), not \(0\). Since \(1!=1\), this avoids distracting factorial arithmetic.

**That synthetic coefficient test is my preferred cheapest end-to-end transport/assembly regression.** It deliberately tests the generic machinery without asking the producer to expose a specially normalized moment tensor.

### Can odd-integral cancellation prove the produced coefficients vanish?

Yes, **through asymptotic uniqueness**, not merely through the displayed coefficient-sum identity.

For constant prior, reflection gives, for every real \(n\),
\[
\int_{[-a,a]}w\,e^{-nw^{2k}}\,dw=0.
\]
Integrability on the compact box and unconditional reflection change of variables make this elementary.

Combining this with the signed expansion should imply
\[
C^{\mathrm{signed}}(w\mapsto w_0,q)=0
\]
for every \(q\) in the expansion’s admissible spectrum, provided the library has uniqueness of the corresponding power-log expansion. A statement for **all** `PowerLogIndex` additionally needs coefficient support/vanishing off that spectrum.

The correct proof route is:

1. the Laplace function is identically zero;
2. the signed theorem gives an expansion with assembled coefficients;
3. the zero function has the zero expansion;
4. uniqueness identifies the coefficients.

No observable-linearity theorem is needed.

But **CCC VIII cannot be assumed to supply step 4 from its name alone**. Its statement is absent here. A theorem comparing two resolved certificates may not apply directly to the assembled signed data, which intentionally are not a resolved certificate. In that case, factor out the underlying expansion-uniqueness lemma.

Likewise, comparing the positive-box certificates for \(\phi\) and \(-\phi\) does not by itself establish coefficient negation: they describe different integrals. One first needs to negate an expansion or otherwise supply the equality being compared.

**Recommendation:** land R3 first; add the produced odd-observable test if expansion uniqueness is already conveniently accessible. Do not make phase G wait for project J.

---

## A3. Fidelity and maintenance review

### Changes I would request

1. **Clarify “holomorphic extension.”**  
   The packet records
   \[
   \phi(w)=\operatorname{Re}H_\phi(w),
   \]
   not \(H_\phi(w)=\phi(w)\) as a complex-valued identity. This is entirely usable, but docstrings should say “holomorphic representatives whose real parts agree on the real neighborhood,” or explicitly document the convention.

2. **Qualify the deepest-stratum claim.**  
   State the sum specification unconditionally. State equal-copy multiplicity only with a proved equal-mass lemma.

3. **Define “unchanged spectrum” precisely.**  
   It means the same coordinate lattice and logarithmic-degree bound as the positive pieces:
   `spectrumLe (coordCommonQ k) (d - 1)`. It does not mean every permitted coefficient is nonzero or that the grid is minimal.

4. **Distinguish support from topological support.**  
   `ae_signedStratumMeasure_mem_signedBox` proves concentration in the box. The current “live in” wording is fine; do not advertise a separate topological-support theorem unless derived.

5. **Do not advertise canonical assembled measures or fields.**  
   They depend on the packet, collar, and producer. The coefficient-sum specification is proved; choice-independence of the signed coefficients is a further uniqueness corollary.

6. **Fix the apparent truncated module header if literal.**  
   The supplied full source starts with `chart gluing. Zero ... -/`. I assume this is excerpt damage.

### Things I would not flag as defects

- **Directed `rfl` for exponent normalization:** good. A stable named normal form is better than asking elaboration to compare two enormous packet-dependent certificates.
- **G5 landing before G4:** correct dependency engineering.
- **Unconditional derivative transport:** legitimate for a continuous linear equivalence; no omitted smoothness hypothesis is apparent.
- **Germ-based regularity:** exactly the right repair. It avoids imposing global regularity on the original observable.
- **`subst hJ` in the transport lemma:** compatible with a source-level `▸`-free convention. It does not mean the kernel contains no equality transport.
- **Local `have` finiteness instances:** not hidden assumptions. They are proved local instances supplied to typeclass search. For readability I would prefer named `letI` declarations when convenient, but this is stylistic.
- **`integrableOn_signedBox` not using positivity:** a strength, not a missing hypothesis. Packet continuity on the compact box suffices.

For release, record `#check`/`#print` outputs for the two public theorems and rerun `#print axioms`. This verifies the elaborated hypothesis list rather than inferring it from section-variable declarations.

---

## A4. Paper sentence

> For a monomial phase on a two-sided coordinate box, we construct a coordinate-free power-log Laplace expansion from analytic prior and observable data, by reflecting the one-sided expansions and assembling their stratum measures and moment fields with Radon–Nikodym weights. This supplies the signed coordinate model underlying local normal-crossings descriptions of a real divisor.

Add a scope sentence:

> The current producer treats zero Jacobian orders; applications to resolved non-coordinate geometries additionally require verified chart, Jacobian, and assembly data.

“Underlying local model” is justified. “We prove the expansion for arbitrary real divisors” is not.

---

# B. Direction after G

## B1. Ranking

For the next development phase:

1. **(iv) E projector blow-up instance**, beginning with a tightly scoped producer/Jacobian pilot.
2. **(v) J observable-independent functionals.**
3. **Stop at G**, if the paper’s intended claim is the coordinate-model theorem.
4. **(vi) General SNC gluing interface.**
5. **(i) Further complexification**, absent a specific missing real-analytic-to-packet theorem.

The reason to put E first is that it tests whether the architecture reaches actual geometry. The reason to delay general SNC gluing is that one verified non-coordinate instance will reveal the correct interface better than speculative abstraction.

J is valuable, but distinguish:

- scalar coefficient additivity/linearity obtained from uniqueness;
- one observable-independent geometric measure/field construction;
- continuity of those functionals in an explicitly chosen analytic topology.

Those are progressively stronger projects. G does not prove the latter two.

---

## B2. How much changes for monomial Jacobians?

There are **two different targets**.

### Target 1: get a weighted integral expansion cheaply

On a positive orthant,
\[
\prod_i |w_i|^{h_i}=\prod_i w_i^{h_i}
\]
for natural-number orders. Therefore the monomial weight can be absorbed into the analytic prior:
\[
\widetilde\varphi(w)=\left(\prod_iw_i^{h_i}\right)\varphi(w).
\]

This can reuse the existing zero-order producer.

On the signed box, when some \(h_i\) is odd, \(\prod_i|w_i|^{h_i}\) is generally not analytic across the coordinate hyperplanes. Thus it cannot simply be inserted into one signed holomorphic packet. But it **can** be handled orthantwise:

1. reflect the original analytic data;
2. multiply each positive-box prior by \(\prod_i u_i^{h_i}\);
3. produce each positive expansion;
4. reflect and RN-assemble.

G4 already provides the assembly abstraction needed for this.

**This is a legitimate pilot for weighted scalar integrals, but it does not produce a certificate whose resolved geometry records the actual Jacobian orders.**

### Target 2: produce certificates with the correct `h`

This is the right target for a faithful resolved-geometry instance.

The changes should primarily run through the **one-sided collar producer**, not through reflection or RN assembly. G3 is already parameterized by `h`, and G4/G5 are generic.

Audit and generalize:

- collar core `h` to the appropriate reindexing of the ambient order family;
- density/change-of-variables identities;
- face/core series contracts and integrability bounds involving the weight;
- Mellin numerator shifts and pole/residue formulas;
- spectrum inclusion;
- stratum measure and moment-field definitions;
- producer-to-certificate and public expansion wrappers.

The important pole arithmetic becomes, schematically,
\[
\frac{h_i+1+m_i}{2k_i}.
\]
For integral orders this shifts numerators rather than introducing new denominator factors. Nevertheless, the existing spectrum containment must be reproved; it should not be waved through because `commonQ` only mentions `k`.

The geometric collar decomposition, reflection cover, and finite RN assembly should survive substantially unchanged. Whether the analytic-series layer already abstracts all dependence on `h` requires inspection of the earlier source.

---

## B3. Proposed unit plan

### G7 — `SignedBoxRegression`

Land the three fixtures above:

- one-dimensional origin normalization;
- two-dimensional crossing multiplicity;
- order-one negative-reflection coefficient cancellation.

Add the produced odd-observable corollary if uniqueness is readily available.

**Gate:** G is closed.

### E0 — `ProjectorBlowupObligations`

Before generalizing code, write the actual chart equations and a compile-checked obligation table:

- blow-down maps and relevant domains;
- exact phase pullback, including any nonvanishing unit;
- absolute Jacobian and its order family;
- exceptional/null sets and change of variables;
- active normal coordinates versus tangential/base coordinates;
- finite coverage or partition identity;
- transformed analytic prior/observable packets.

No source for E was supplied, so I cannot certify its particular orders or coverage obligations here.

**Gate:** decide whether nonzero `h` is the only producer blocker. It may not be: the current coordinate model requires positive `k i` in every modeled coordinate, whereas a blow-up chart may have inactive tangential coordinates.

### E1 — `WeightedOrthantPilot`

Use prior absorption to prove one required weighted chart integral expansion with existing machinery.

Do this only as a small pilot, not as a parallel permanent producer stack.

**Gate:** a concrete nonzero Jacobian weight reaches an expansion; document that certificate geometry still has zero orders.

### E2 — `CollarCoresWithOrders`

Generalize the core and its density identities to the order family needed by E.

Include named compatibility lemmas recovering the zero-order implementation.

**Gate:** weighted core identities, exponent/order normal forms, and all old zero-order tests pass.

### E3 — `WeightedCollarCertificates`

Thread the orders through face-series conversion, integrability, certificate production, coefficient production, and spectrum containment.

**Gate:** a positive-box theorem producing the correct `geometry d k h hk`, not merely a weighted prior in zero-order geometry.

### E4 — `SignedWeightedExpansion`

Reuse reflection and assembly for the weighted pieces.

**Gate:** signed expansion for the absolute monomial Jacobian, with exact coefficient-sum and measure specifications; no false signed-analytic hypothesis on \(|w|^h\).

### E5 — `ProjectorBlowupExpansion`

Discharge the chart obligations and derive the original integral expansion.

Two cautions:

- a nonvanishing phase unit cannot simply be absorbed into the prior;
- analytic cutoff/partition functions are not automatic—nontrivial compactly supported analytic partitions are unavailable in the usual sense.

Use an exact measurable partition where possible, or state and prove the appropriate regularity interface rather than silently changing the analytic contract.

**Final gate:** one theorem about the original non-coordinate integral, with no unresolved Jacobian, chart-coverage, or certificate-production assumptions.

---

# What the paper should claim now

The strongest clean present claim is:

> A fully formalized local expansion theorem for analytic data in the one-sided and two-sided monomial coordinate models, with coordinate-free normal-jet coefficients, explicit stratum-measure assembly, and polynomial instances.

It may also explain that reflection transport and finite RN assembly are reusable beyond the coordinate model.

It should **not yet claim** an instantiated general resolution theorem, arbitrary SNC gluing, a blow-up application with nonzero Jacobian orders, or observable-independent canonical moment fields.

**Bottom line:** G’s construction is sound on the supplied evidence. Close the regression gap, qualify the equal-copy measure gloss, and let one concrete E chart—not a general SNC interface—drive the next abstraction.
