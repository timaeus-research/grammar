## 1. Audit

**Verdict:** the statements shown support the revised claims. This is a statement-level audit of excerpts, not an independent repository build; axiom cleanliness does not itself verify that the hypotheses model the intended geometry.

- **Completion (CCCIV).** The summability and integrability statements close the evident definitional gaps. They do **not** by themselves assert interchange of the normal-order sum with integration. The `≤ A` truncation is appropriate: all logarithmic degrees at exponent `A` must remain; terms with exponent strictly greater than `A` are negligible. “Indexing envelope”, “chosen fields”, “factorisation family”, and “unnormalised integral” are the right qualifications.

- **First instance (CCCV–VII).** This is a genuine instance of the complete certificate pipeline, not merely a restatement with its main hypotheses assumed. A boundary zero and a one-sided chart are perfectly legitimate; null endpoints account for the open/closed box discrepancy. Say **“the theorem has an explicit one-dimensional, one-chart polynomial instance”**, rather than leaving “inhabited” unexplained. It does not test chart overlap, nontrivial resolution, crossings, or logarithmic terms.

- **Uniqueness (CCCVIII).** **Yes: this is the right scalar canonicity statement.** For the same integral and fixed observable, different certificate/coefficient-certificate pairs yield identical assembled coefficients, including across different lattice envelopes. The zero-extension hypotheses in the underlying comparison theorem are essential and correctly explicit.  
  Two limits: the displayed corollary fixes **`R` and `D` too**, so it is not yet literally a comparison between different resolved geometries; and it proves neither equality of fields nor observable-independent geometric coefficients. The abstract scalar uniqueness theorem is the appropriate route to a future cross-resolution comparison.

- **Jets versus series (CCCIX).** Correctly scoped: analytic power-series presentations recover the normalised jet coefficient family, and a sufficient interior-radius condition gives absolute summability. This identifies the **monomial coefficient family**, not arbitrary nonsymmetric multilinear presentations themselves. `ofSeries` still requires the factorisation identity and summability of `cc`; it does not manufacture those geometric inputs.

- **Leading term/measure (CCCX).** **Yes**, a certificate-specific admissible lattice is fine: it is an envelope containing every potentially nonzero coefficient. Predecessor vanishing is therefore sufficient. Note that `hasLeadingTerm_expansionCoefficient` permits a **zero** limiting coefficient; a genuinely nonzero leading asymptotic requires the additional nonvanishing supplied in the existence theorem. That existence theorem is conditional on some coefficient being nonzero—it does not rule out an all-orders-flat integral.  
  **Yes**, the measure bridge is correctly scoped: it assumes the CCXC leading-measure statement at the same scale and requires the entire product `φϕ` to equal a bounded continuous test. It identifies one scalar coefficient with a measure integral; it neither constructs that measure nor proves the bridge for arbitrary measurable insertions.

## 2. What remains worth doing?

**Recommendation: H → F → stop this programme unless a specific new headline is wanted.** Stopping now is already defensible. Neither E nor I is an unpaid obligation of the existing conditional representation theorem.

Effort bands below are rough person-effort estimates, assuming familiarity with the repository.

| Priority | Candidate | Value / scope | Size |
|---|---|---|---|
| 1 | **H: explicit Gaussian coefficients** | Best cheap regression test: checks factorials, half-interval normalisation, kernels, and assembled coefficients. | Small: days |
| 2 | **F: tied crossing** | Best next substantive instance: dimension two, genuine logarithms, and a meaningful test of the normal-order representation. | Medium: roughly 1–3 weeks |
| 3 | **K: stop** | Sensible default after H/F—or immediately if paper delivery dominates. | — |
| Conditional | **J: observable-independent functional** | Do this for a headline about coefficient functionals, rather than coefficients for one fixed insertion. | Medium–large: weeks |
| Conditional | **I: core + phase-gap interface** | Highest infrastructure value if the next goal is transferring general geometric models into the expansion theorem. | Large: several weeks or more |
| Low | **G: two-sided interval** | Useful signed-frame/two-chart regression, but little new mathematics. | Small–medium: days to a week or two |
| Defer | **E: projector blow-up** | A valuable nontrivial-resolution showcase, but currently pays a substantial interface cost. Reassess after I or a clear adapter design. | Very large: multi-week to months |

### Gates versus bookkeeping

- **H:** no new headline is gated on it, but it is excellent assurance. State the displayed Gaussian expression as an **asymptotic**, not an exact finite-interval integral; the finite-endpoint correction is exponentially small for fixed positive `ρ`.

- **F:** gates a claim of an **explicit logarithmic crossing instance**. One important correction: a fixed polynomial has only finitely many nonzero jets, so it does **not alone demonstrate an actually infinite normal-order sum**.  
  To demonstrate failure of a uniform finite-jet bound, use a family of increasingly high-degree polynomials: off-diagonal monomials can contribute to the same nonlogarithmic coefficient at exponent `1/2`. To exhibit genuinely infinitely many contributions for one observable, add an analytic nonpolynomial example with convergence control. The polynomial crossing instance remains worthwhile without that extension.

- **G:** mostly bookkeeping, though the negative chart tests a convention the half-interval does not. Not a gate for current claims.

- **J:** gates “canonical coefficient **functional** on an observable class”. Merely writing `φ ↦ …` is insufficient: specify an observable class with certificates, support/zero-extension conventions, and closure sufficient to prove linearity. A distribution claim additionally needs continuity in an appropriate topology. This still would not make the representing fields unique.

- **I:** gates the proposed **core-based route**, not every conceivable treatment of curved sublevel sets. It is genuine infrastructure: localization, tail control, and compatibility with the coefficient representation must all be transferred. Before implementing it, map precisely which existing `BlowUpCube` outputs would satisfy the new interface.

- **E:** gates an explicit **projector-blow-up certificate instance**, not a general resolution-to-expansion theorem. It would not, by itself, establish existence of certificates from the Hironaka interface.

**Do not create another round of generic “small completion tasks”.** The current theorem package is coherent. Further work should buy a named example, a functional-level statement, or a new existence/transport interface.

## 3. Paper-facing summary

Given resolved geometric, analytic, transport, and coefficient-factorisation certificates, Lean proves an all-orders power–log expansion of the unnormalised partition integral with insertion.  
Its coefficients are represented by stratum integrals pairing chosen normal tensor fields with normal derivatives of the insertion.  
Normal-order summability, integrability, and truncation through exponent `A` with remainder `o(n⁻ᴬ)` are proved.  
For a fixed insertion and resolved normal setup, the assembled scalar coefficients are independent of the certificate choices and lattice envelopes.  
A first nonzero coefficient, when one exists, determines the leading asymptotic.  
Assuming a leading measure at that scale, the coefficient equals its integral against the bounded continuous test representing the insertion times density.  
Analytic series are linked to normalised jets, and an explicit one-sided polynomial Gaussian instance traverses the full pipeline.  
The results do not establish canonical fields, general certificate existence from resolution, or an observable-independent coefficient-distribution theorem.
