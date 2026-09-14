## Verdict

**Target B passes at the level of the supplied statements and proof architecture.** Resolving the product, splitting its analytic factors, absorbing the positive phase unit, and then reading the domain by coordinate signs is a sound route. The export is substantially stronger than an atlas-extraction result: it reaches an exact measure transport with an exponentially suppressed tail and then a coordinate-free expansion.

Two qualifications matter for the project’s claims:

- The exported domain class is **compact globally basic analytic-inequality domains in a connected analytic ambient open set**, not yet arbitrary compact semianalytic sets.
- Your conclusion about identically zero chart factors is correct, but the proposed argument that the image of an arbitrary resolution chart is open is not.

This is a statement-level audit of the material supplied, not an independent check of the two repository revisions.

## 1. Audit of the hypotheses and construction

### (i) The product condition at the origin

The actual hypotheses are:

\[
0\in W,\qquad F(0)=0,\qquad F=K\prod_\ell\pi_\ell
\text{ has nonzero germ at }0.
\]

They **do not require**
\[
0\in W_{\mathrm{dom}}\cap\{K=0\}.
\]

In particular, the origin may lie outside the inequality domain, or satisfy \(K(0)>0\) with some boundary factor vanishing there. The origin is an anchor for the modification theorem, not necessarily a point contributing to the asymptotics.

A paper-facing wrapper should ordinarily choose a point
\[
p\in W_{\mathrm{dom}}\cap\{K=0\}
\]
and translate it to the origin. This automatically supplies the product-zero condition. If that set is empty, compactness and nonnegativity give a positive phase gap on a nonempty domain, so the pure-tail theorem applies instead.

The nonzero-germ condition is substantive: on connected \(W\), it excludes \(K\equiv0\) and every identically zero boundary factor. Conversely, analyticity, connectedness, and nontriviality of each factor give product nontriviality, including at the chosen anchor. Thus the natural façade is:

- discard identically zero, hence vacuous, boundary inequalities;
- separate the identically zero phase;
- handle the positive-phase case by a tail;
- otherwise anchor at a phase zero.

### (ii) Compact domain inside an open analytic ambient

**Yes: this matches the paper’s compact-domain/open-neighbourhood distinction.** Rename the Lean ambient `W` to something like `A` in documentation, and write

\[
D=A\cap\bigcap_\ell\{\pi_\ell\ge0\}.
\]

Then `IsCompact D` and \(D\subset A\), with \(A\) open, give the required buffer between the integration domain and the ambient boundary. This is desirable, not an unwanted strengthening of the paper’s neighbourhood assumption.

A ball inequality is a convenient way to enforce compactness when presenting a basic domain. It should be chosen so that it does not alter the intended domain; adding it does not turn an arbitrary semianalytic set into a single basic domain.

The actual remaining domain issue is **basic versus general semianalytic**, not compact versus open.

### (iii) Local prior and cutoff

**Yes, add this wrapper.** For compact \(D\subset U\subset A\), with \(U\) open, choose a smooth cutoff \(\chi\) satisfying

\[
0\le\chi\le1,\qquad
\chi=1\text{ near }D,\qquad
\operatorname{tsupport}\chi\Subset U.
\]

Multiply the locally smooth prior by \(\chi\), extend by zero, and apply the existing theorem. The integral over \(D\) is unchanged. Losing analyticity of the cutoff prior is harmless: your consumer requires only smoothness.

There are two distinctions worth documenting:

- `tsupport prior ⊆ A` **does not itself imply compact support** when \(A\) is unbounded.
- Nevertheless, **`HasCompactSupport prior` is unnecessary for the landed theorem**: compactness of \(D\) already makes `tsupport prior ∩ D` compact. The cutoff construction additionally produces compact support, but callers need not supply it.

Preserving global nonnegativity by this construction requires the local prior to be nonnegative on the cutoff’s support. If nonnegativity is assumed only on \(D\), that extension argument is not automatic. For the scalar expansion, a convenient alternative is to use a nonnegative cutoff as the transport prior and put the local prior into the observable.

If the paper also treats the observable as smooth only on a neighbourhood, extend/localize it in the same wrapper.

### (iv) `Measurable K`

**Remove it from the paper-facing statement using the Target A pattern.** Analyticity supplies measurability on the relevant open neighbourhood; an indicator or piecewise representative supplies a globally measurable function agreeing there.

Keep `Measurable K` in the consumer if that simplifies its interface. It is not a mathematical restriction worth exposing in the analytic corollary.

### (v) Identically zero boundary factors

The conclusion is airtight **using the product resolution data**, but not quite by the image-openness argument proposed.

A resolution chart has open coordinate target, but its image under the modification need not be open at exceptional points. Thus one cannot simply assert that `rep(target) ∩ W` is open.

Instead:

1. `hne` and the identity theorem on connected \(W\) imply that \(F\) is not identically zero on any nonempty ambient open subset.
2. A raw Watanabe chart represents \(F\circ\mathrm{rep}\) by a nonzero unit times a monomial.
3. Consequently \(F\circ\mathrm{rep}\) is nonzero off its coordinate walls.
4. Since it is the product of the pulled-back factors, no pulled-back factor can vanish identically on that chart neighbourhood.

Equivalently, one can use the modification’s regular, diffeomorphic locus. Connectedness of the chart image is not the relevant issue.

So retaining the general `zero` field in the domain-reading API is sensible, while recording that the product-extraction constructor uses only the nonzero-factor case.

### Transport and sector audit

Nothing in the supplied architecture suggests a missing boundary correction:

- Enlarging exceptional walls to `allWalls` is legitimate because they remain null.
- The domain comparison is only almost everywhere, which is exactly sufficient for these absolutely continuous source measures.
- Absorption scales one coordinate by a positive function, so it preserves coordinate signs and the boundary exponents.
- The target-weight construction, its a.e. vanishing outside the domain, and the exceptional-image null argument are the right ingredients for an **exact measure identity**, rather than an informal change-of-variables argument.
- The phase gap is taken on the compact unresolved remainder of the relevant support/domain, which is the correct place to obtain a uniform exponential tail.

## 2. Distance to the paper’s theorem

| Remaining item | Status and likely cost |
|---|---|
| Arbitrary anchor instead of the origin | Translation wrapper; **S**, reusing Target A. |
| No phase zeros on the compact domain | Pure-tail wrapper; **S**. Empty domain is trivial. |
| Phase identically zero | Integral is constant in \(n\). **S** as a separate theorem; fitting it into the same certificate may require a constant-term branch if exponent \(0\) is excluded. |
| Identically zero boundary functions | Delete vacuous inequalities; **S** preprocessing, with some finite-index bookkeeping. |
| Prior and observable smooth only near the domain | Cutoff/extension wrapper; **S**, especially with existing localization infrastructure. |
| Remove global `Measurable K` | **S**, reuse Target A. |
| An independently named compact domain \(D\) with an equality to `boundaryDomain A π` | Rewriting façade; **S**. |
| Disconnected analytic neighbourhood | Finite localization/component gluing over the compact domain, including zero-phase components; **M** unless finite-sum gluing is already packaged. |
| Arbitrary compact semianalytic domain | Genuine additional domain front end: local Boolean descriptions, localization, overlap/sign-pattern bookkeeping, and finite gluing; **M or larger**, depending on existing infrastructure. |

For the disconnected case, only finitely many ambient connected components can meet a compact set contained in the open neighbourhood. That makes the reduction finite, but does not eliminate the need to assemble certificates.

The general semianalytic gap should remain explicit. A compact semianalytic set need not arrive as one simultaneous list of global weak inequalities. Finite unions, local descriptions, and Boolean operations require additional work; taking a union of overlapping basic-domain integrals would double-count.

### What I would do now

Add a small **Target B façade module**, not another geometric target:

1. Arbitrary phase-zero anchor.
2. Local prior/observable and removal of `Measurable K`.
3. Positive-phase branch.
4. A domain-equality argument allowing callers to name their compact \(D\).

Reuse the Target A cleanups rather than developing parallel machinery. State the identically zero phase separately if the certificate format does not already accommodate constants. Do **not** hold closure hostage to general semianalytic gluing.

## 3. Coefficients and RLCT

The right current claims are:

- intrinsic scalar coefficients, independent of the chosen transport;
- logarithmic degree bounded by \(d-1\);
- linear dependence on the observable.

One cheap addition is a public **coefficient-linearity corollary**, if it is not already exposed. Derive it from linearity of the integral and uniqueness of the scalar asymptotic expansion, allowing different witnesses for `Q` and `D`. Do not claim that the witness denominators themselves are canonical.

An RLCT identification needs more care than “the certificate’s leading exponent equals \(\lambda\)”:

- A certificate’s admissible exponent grid is not its first **nonzero** coefficient.
- A zero or signed observable can eliminate the leading term.
- A prior that vanishes near the singular locus, or to positive order along it, can change the effective leading exponent.
- A domain may have no positive-volume admissible sector at the relevant zeros.
- The `E5` notion must concern the same restricted domain and weighting convention.

With a positive density and a noncancelling observable, one expects the first nonzero exponent to match the corresponding RLCT, and the leading log power to reflect its multiplicity. If an existing `HasLLCExponentsOn` theorem already supplies precisely that leading asymptotic for the same integral, uniqueness may make the bridge **S/M**. Without that exact alignment, it is a **separate readout project**, not a closing cleanup.

## 4. Stopping decision and wording

**Close the “atlas from resolution data” project.** Its central dependency is discharged: no independently assumed family monomialisation or hand-supplied boundary-compatible atlas remains. Treat the façade work above as bounded API polish.

The closure non-claims should be:

- no general compact-semianalytic-domain front end yet;
- no unqualified treatment of identically zero phases or disconnected zero-phase components in this export;
- no unrestricted local-data interface until the cutoff wrapper lands;
- no identification of leading nonzero coefficients with RLCT data;
- no assertion of a nonzero leading coefficient for arbitrary observables;
- no explicit algorithm computing intrinsic coefficients merely from their existence.

### Paper-mirror paragraph — eight sentences

> Target B constructs boundary-compatible local normal forms and the resulting smooth Laplace expansion for compact domains presented by finitely many analytic weak inequalities inside a connected open analytic neighbourhood. The phase is assumed nonnegative on that neighbourhood, and the product of the phase with the boundary functions has a nonzero germ and vanishes at the chosen origin. Rather than assuming simultaneous monomialisation, the construction resolves this single product and splits its factors in the ring of convergent power series. Nonnegativity makes the phase exponents even, and an analytic coordinate change absorbs its positive unit. The boundary inequalities then select finitely many coordinate orthants, with equality to the original domain almost everywhere in each chart. Cutoffs on the resolution space yield an exact measure decomposition into these sector contributions and a tail separated from the phase-zero locus. For a globally smooth nonnegative prior supported in the ambient neighbourhood and a globally smooth observable, the formalisation proves an intrinsic scalar asymptotic expansion with logarithmic degree at most \(d-1\). The result does not yet supply a front end for arbitrary compact semianalytic sets or identify the leading nonzero exponent with RLCT data.

**Acceptance statement:** Target B is accepted as the axiom-clean completion of the product-resolution-to-sector-transport-to-smooth-expansion pipeline for compact basic analytic-inequality domains under its stated hypotheses; the core project is closed, with general semianalytic gluing and RLCT identification explicitly outside scope.
