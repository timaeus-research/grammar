## 1. Fidelity audit

**Verdict: the theorem gives a coordinate-free presentation of a conditional expansion. It does not yet establish an intrinsic, choice-independent coefficient field.** That distinction belongs in the headline.

The landed formula gets the important analytic points right:

- raw normal jets paired with exactly one factor `1/r!`;
- coefficient tensors, not exact fibre moments, in the power–log expansion;
- `∫ s, ∑' r, …`, retaining all normal orders at tied crossings;
- remainder genuinely `IsLittleO` against `n ^ (-A)`.

### (a) Fields versus total coefficients

Neither `chartTensor_pair` nor frame transport proves independence under changing charts, boxes, density factorizations, or partitions. They establish the relevant **transport/pairing identity for the chosen presentation**. Covariance between two presentations additionally requires their data to transform compatibly.

Even fixing `(ν_I, Φ)` does not, from these certificates, determine `B`. Existence of suitable fields is acceptable for a coordinate-free representation theorem; do **not** assert their canonicity.

Prove canonicity at the correct level:
```lean
-- schematic: different certificates, same original integral
theorem expansionCoefficient_eq_of_certificates ...
```
using uniqueness of asymptotic coefficients after zero-extending to a common spectral lattice. This gives scalar coefficient equality for each admissible `φ`, not equality of tensor fields.

**Important additional issue:** both certificates currently depend on `φ`. Thus the theorem does not by itself produce a single observable-independent family defining
```lean
φ ↦ D.expansionCoefficient ν B φ q
```
on a test-function space. For that claim, freeze the geometric/density data and certify a class of observables against those same data.

### (b) Spectrum

A certificate-dependent lattice is fine: it is an **indexing envelope**, not necessarily the intrinsic nonzero spectrum. Its construction may use charts without putting coordinates into the coefficient formula.

Two repairs:

1. `HasCoordFreeExpansion` imposes no spectral conditions on `spec`; remove its docstring claim “all indices with exponent `≤ A`”, or add a separate spectrum predicate.
2. Add the cleaner corollary using
   ```lean
   (spectrumBelow Q Dg A).filter (fun q => q.exponent ≤ A)
   ```
   Terms with exponent `> A` are individually `o(n⁻ᴬ)`, regardless of their fixed log degree. This removes the artificial `max (A+1) 1` from the public formula.

Eventually expose an existential wrapper over `ν`, `B`, and an admissible spectrum, rather than explicit `commonQ C.adapted.k` and `commonD C.n`.

### (c) Pointwise summation

**Keep `∫ ∑' r` as the primary statement.** No tensor-field continuity assumption is needed merely to state or prove that scalar identity.

However, Lean’s `tsum` and Bochner integral are totalized operations. Export explicit companion results asserting:

- convergence of the scalar normal-order series, at least almost everywhere;
- integrability of its sum.

The chart `HasSum` theorem and the canonical coefficient identity should supply these for the assembled field.

An optional `∑' r, ∫ …` corollary needs actual interchange hypotheses, for example integrable summands and
\[
\sum_r\int |f_r(s)|\,d\nu_I(s)<\infty.
\]
**Continuity alone is insufficient**, even on compact bases.

## 2. The certificates

### What `datum_eq` honestly certifies

It is a sufficient and sensible **algebraic factorization hypothesis** for the current theorem. It need not block publication of this conditional result.

But the excerpt does **not** certify that `cc` is the Taylor family of the geometric density `c`. In particular, when `φ = 0`, `datum_eq` can hold for arbitrary summable `cc`. Rename its current documentation accordingly.

For density-derived, observable-independent tensors, split the obligations:

```lean
-- schematic
DensityCoefficientCertificate:
  cc
  cc_abs
  density_series_eq  -- cc genuinely represents c on the required normal domain

ObservableCoefficientCertificate φ:
  jet_abs
  observable_series_eq
```

Then derive `datum_eq` from these and `amplitude_eq`, or provide an algebraic constructor that builds the amplitude datum as the Cauchy product.

### Deriving it from analytic equality

Yes, that is the desirable constructor theorem, but observe two qualifications:

- Equality on a full-dimensional normal box can give coefficient uniqueness under the appropriate analytic-domain hypotheses. An arbitrary accumulating set does not suffice in several variables.
- If `amplitude_eq` is only almost everywhere in the product, Fubini normally gives coefficient equality **for almost every base point**, not every `s`. Either retain the stronger pointwise certificate as an explicit convenience, or generalize the integration-facing API to an a.e. `datum_eq`.

Also, the supplied `NormalMomentPresentation` has radius `> b`. That is not automatically the stronger radius `> (n+1) * b` proposed in candidate B. Prove the precise norm-dependent estimate; do not silently strengthen the existing hypothesis.

### Geometry honesty check

From the excerpt alone, `du` is an independent family of covectors and `Φ` is merely continuous at zero. Those fields alone do not establish genuine divisor conormals or tubular geometry. Verify that the relevant compatibility with the divisor is certified elsewhere; otherwise describe this as **chosen normal data**, and add the missing geometric compatibility before claiming an intrinsic conormal construction.

Also check finite dimensionality explicitly: `finrank_N = I.card` does not exclude an infinite-dimensional fibre when `I = ∅`, since infinite-dimensional spaces have `finrank = 0`. Add fibrewise `FiniteDimensional`, or assume finite-dimensional ambient `A`.

## 3. Next units

**Recommended order: A → D → B → C → E.** Sizes below are rough module-scale estimates, not repository-verified forecasts.

| Unit | Recommendation | Status / size |
|---|---|---|
| **A: first instance** | Start with the one-dimensional, one-chart product model; then a tied-crossing regression example. | **Immediate acceptance gate**; roughly 1–3 modules |
| **D: uniqueness** | Prove once for `CutoffExpansion`; derive certificate-independence of scalar coefficients. | **Gate for canonicity claims**; 1–2 modules |
| **B: jets ↔ series coefficients** | Build the analytic constructors eliminating manual `jet_abs` and factorization proofs. | **Gate for scalable applicability**; roughly 2–5 modules |
| **C: leading measure** | Extract the leading limit, then identify it with CCXC by equality of limits for admissible observables. | High-value corollary; 1–3 modules if existing support lemmas suffice |
| **E: projector blow-up geometry** | Do after a cheap complete instance and stabilization of the certificate API. | **Gate for that geometric model**, not this conditional theorem; substantially larger, plausibly 6–12+ modules |

### A: cheapest convincing test

Prefer a legitimate existing one-chart geometry over assembling the full isolated-zero blow-up immediately. Use a **nonconstant polynomial observable**, not only `φ = 1`.

A useful analytic benchmark is
\[
\int_0^b(1+a x^2)e^{-Nx^2}\,dx
=\frac{\sqrt\pi}{2}N^{-1/2}
 +\frac{a\sqrt\pi}{4}N^{-3/2}
 +\text{exponentially small remainder}.
\]
It tests normalization, a nonzero higher jet, field transport, and the final theorem. Adapt the domain to the actual supported geometry API.

Then instantiate a two-variable tied crossing. That is the regression test for retaining `∑' r`.

### D: uniqueness details

Require positive lattice denominators. Compare different lattices on a common refinement, zero-extending coefficients and padding log degrees by zero.

Proof: choose the least differing exponent and, there, the greatest differing log degree; normalize by that power–log scale. The leading nonzero constant contradicts the cutoff remainder.

Only coefficients **on the supported lattice and within the declared degree bound** are determined. `CutoffExpansion` cannot determine arbitrary values of `c μ j` that never enter its sums.

### C: do not identify the leading measure by inspection

First establish the spectral vanishing conditions below `λ` and above log degree `m−1` at `λ`. Use a cutoff strictly beyond `λ`.

Do **not** assume the leading coefficient is automatically the `r = 0` term. Identify the complete leading functional with CCXC’s measure using the established limit. A functional-level statement again needs fixed geometric/density data across observables.

**Before these units:** make the docstring repairs, export scalar convergence/integrability, and add the `≤ A` truncation corollary. Those are small completion tasks.

## 4. Mirror paragraph

```tex
\paragraph{Lean formalisation.}
In namespace \texttt{Grammar}, \texttt{hasCoordFreeExpansion} proves the
unnormalised integral expansion conditional on a resolved normal datum,
a \texttt{ResolvedCertificate}, and a \texttt{CoefficientCertificate}.
Its coefficients are stratum integrals of
$\sum_{r\ge0}(r!)^{-1}\langle D_\perp^r(\phi\circ\pi),B_{I,r,\alpha,j}\rangle$,
where the series is summed inside the integral.
The fields are constructed from chart coefficient tensors by frame transport
and Radon--Nikodym assembly; chart choices remain in this construction.
For every real cutoff $A$, the certified finite truncation has remainder $o(n^{-A})$.
This is a coordinate-free representation, not a claim that the individual fields
are choice-independent, that exact moments are finite power--log sums,
or that the certificates have been constructed for every resolved geometry.
```

## 5. Headline corrections

Replace:

> “THE GOAL STATEMENT: no coordinates — only …”

with:

> **Certified coordinate-free expansion:** the displayed coefficients use stratum integrals and contractions of chosen normal jets with moment coefficient fields. Charts enter the certificates and the construction; independence of the individual fields is not asserted.

Specific overclaims to avoid:

- **“Intrinsic conormal derivatives.”** Higher jets depend on tubular data; the excerpt does not establish all geometric compatibility.
- **“Density Taylor family.”** Currently `cc` is certified as a factorization family, not independently as the Taylor family of `c`.
- **“Canonical coefficient fields.”** Only the assembled scalar coefficients are candidates for asymptotic uniqueness.
- **“No coordinates in the Lean statement at all.”** The ambient observable still has domain `Fin d → ℝ`, and the spectrum explicitly references certificate chart data. The defensible claim concerns the **geometric coefficient formula**, not literal absence of coordinate types.
- **“Expectation expansion proved.”** This theorem concerns the unnormalized integral. Normalized expectations need the denominator/nonvanishing and asymptotic-division corollary.
- **“Axiom-clean therefore geometrically complete.”** The axiom report validates the Lean proofs relative to their hypotheses; it does not instantiate or strengthen the certificates.

**Bottom line:** accept units 1–7 as the conditional coordinate-free representation milestone. Gate the stronger “intrinsic final theorem” headline on a complete instance, honest density/observable separation, and uniqueness of the assembled coefficients.
