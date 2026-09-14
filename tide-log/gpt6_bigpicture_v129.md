**Close Theorem D.** The substantive gap—nonvanishing of the geometrically predicted leading coefficient—has been filled. Two qualifications matter for the paper: distinguish a *leading-order bound* from a *nonzero leading term*, and make the **positive realising point** version primary rather than the much stronger positivity-on-the-entire-supported-zero-set hypothesis.

This is a mathematical audit of the supplied signatures and proof descriptions, not an inspection of the Lean definitions or proofs.

## A. Audit

### 1. CDXXXVII: the correct finite-order statement

This supplies a uniform finite-order estimate in the finitely many transported charts, with constants depending on the chosen transport and geometric/prior data.

Your intended qualification is right, but I would avoid saying “the functionals are distributions only chart-wise.” Say instead:

> The coefficient functionals satisfy explicit finite-order chart-seminorm bounds; continuity in a global test-function topology on the resolved manifold is not formalised.

The estimates are the mathematical ingredients for distributional continuity. They are not themselves a formal development of that topology.

### 2. CDXXXVIII: modification independence has the right scope

The eventual-equality theorem is a strong and clean uniqueness statement. Its geometric applications establish independence for:

- the unit observable;
- observables pulled back from the **same base observable**;
- the corresponding unit-observable leading index.

They do **not** canonically identify arbitrary smooth observables on different resolved spaces. Your D7 disclaimer is correct.

Once a strictly positive leading asymptotic has been obtained on both modifications, uniqueness of a nonzero power–log leading term also identifies the numerical pair \((\lambda,m)\). Thus the geometrically computed pair is an invariant of the base partition problem under your hypotheses—not merely chart-independent on one modification.

### 3. CDXXXIX: “extremal” does not, by itself, mean attained or nonzero

The example `isExtremalData_zero` is the warning label. `IsExtremalData lam m` imposes inequalities and a resonance bound; it does not assert sharpness.

Accordingly:

- `isLeadingIndex_of_extremalData` means that all preceding coefficients vanish.
- It does **not** assert that the coefficient at \((\lambda,m-1)\) is nonzero.
- The normalised limit can be zero.
- For \(m=0\), `m - 1` is truncated natural subtraction, not a logarithmic power of \(-1\).

Reserve “the leading term” or “the RLCT pair” for the realised, positive case. For general extremal data, “leading-order bound” or “candidate leading index” is safer prose.

Likewise, even after unit-observable positivity, the coefficient for a signed observable—or one vanishing on the relevant locus—can be zero. You have a common leading scale for all observables, not a nonzero leading equivalent for every observable.

### 4. CDXL–CDXLI: the lower-bound route is sufficient

**Yes: one positive orthant suffices.** You need a positive lower bound at the predicted scale, not the total leading constant.

The described argument has exactly the necessary structure:

1. On \((0,\varepsilon]^d\), the monomial phase is nonzero.
2. Off-zero injectivity makes the chart-to-base map injective on that orthant.
3. Change of variables produces the absolute Jacobian factor
   \[
   |b(u)|\prod_j u_j^{h_j}.
   \]
4. Nonnegativity of the base integrand permits restriction to its image.
5. Nonvanishing of \(b\), continuity, and positivity of the prior at the centre provide a uniform positive lower bound on a sufficiently small orthant.
6. The monomial theorem supplies a positive limit at the scale
   \(N^{-\lambda}(\log N)^{m-1}\).
7. The already-proved convergence of the normalised full partition function converts that lower bound into strict positivity of its limiting coefficient.

The usual change-of-variables obligations—measurability, integrability, differentiability on the relevant domain, and injectivity—must of course be discharged. Nothing additional concerning the other orthants is needed. The half-open boundary convention causes no asymptotic problem.

There is also no need for an upper comparison with the monomial box: the engine has already supplied the finite normalised limit.

### 5. CDXLII: existence is genuinely achieved

Finite wall types, followed by minimisation over the **wall types actually occurring on the zero fibre**, give the minimum ratio. The least uniform resonance bound is attained by integer-valued minimality.

Two mathematical details should remain explicit in the exposition:

- Ratios are taken over active walls, \(k>0\).
- Wall counts retain multiplicity, as in your multiset—not merely the number of distinct numerical pairs \((k,h)\).

A nonempty zero fibre must supply an active wall at a zero point; that is the geometric fact ensuring the minimisation is nonempty. In the realised result, \(m\ge1\) and the active-wall equality also give \(\lambda>0\).

The empty-zero-fibre theorem says all power–log coefficients vanish. Do not present that as existence of an RLCT pair.

## Your readings (a)–(d)

### (a) Identification and terminology

**Your minimum/maximum reading is correct under the positivity condition needed for nonvanishing.** Specifically,
\[
\lambda_*=\min_{\substack{P\in Z_0\\(k,h)\in\mathrm{pairs}(P)}}\frac{h+1}{2k},
\qquad
m_*=\max_{P\in Z_0}
\#\left\{\text{walls at }P:\frac{h+1}{2k}=\lambda_*\right\},
\]
with active walls and multiplicities understood.

It is fair to call \(\lambda_*\) the **RLCT**, provided the paper explains the convention:

> We identify the RLCT and its multiplicity through the leading Laplace asymptotic; identification with the rightmost pole of the associated zeta function is not part of the formalisation.

That is clearer than repeatedly saying “the extremal exponent … which equals the RLCT,” where “equals” could suggest that the pole equivalence was proved.

For the convention \(\zeta(z)=\int K^z\,\mathrm{prior}\), the expected pole is at **\(-\lambda_*\)**, of order \(m_*\). State the convention if discussing poles.

### (b) Positivity: make the realiser version primary

Your uniform positivity hypothesis is sufficient, but **substantially stronger than is usually desirable for compactly supported smooth priors**.

For example, with \(K(x,y)=x^2\), a compactly supported prior positive at the origin generally meets the zero line at boundary points of its support where the prior vanishes. Your uniform hypothesis then fails, even though the usual RLCT asymptotic is entirely standard and a positive realising point exists.

Thus I recommend:

- **Primary sharp statement:** extremal data are realised at a zero-fibre point where the prior is positive.
- **Convenient automatic-existence corollary:** nonempty zero fibre and positivity throughout its base image.

The stronger condition is not merely excluding troublesome priors; it also excludes many harmless cutoffs. Conversely, failure of that condition does not imply the geometric prediction fails. Vanishing at all relevant realisers can change the answer, and smooth flat vanishing can change it dramatically, but boundary vanishing elsewhere need not matter.

### (c) Resonance and logarithmic multiplicity

Correct. Extremality gives
\[
2k\lambda_*\le h+1.
\]
Together with \(2k\lambda_*=h+1+n\), \(n\in\mathbb N\), this forces \(n=0\). Hence resonance counts precisely the minimal-ratio walls through the point, and their maximum \(m_*\) produces log power \(m_*-1\).

### (d) Non-claims

All appropriate, with two wording refinements:

- You **do** identify \(c\) as the positive unit-observable coefficient. What you lack is an explicit local/geometric formula for it.
- Use the chart-seminorm wording above rather than “distributions only chart-wise.”

## B. Suggested paper paragraph

> **Theorem D is established for the resolved smooth engine.** Its coefficient functionals are chart-independent on a fixed modification and satisfy finite-order chart-seminorm estimates; for observables pulled back from the base, they are also independent of the modification. On the compact supported zero fibre, the intrinsic wall data determine a minimum ratio \(\lambda_*=(h+1)/(2k)\) and a maximum multiplicity \(m_*\) of minimal-ratio walls meeting at a point. If this multiplicity is realised at a point where the pulled-back prior is positive, then the Euclidean partition function satisfies \(Z_N[1]\sim cN^{-\lambda_*}(\log N)^{m_*-1}\), with \(c>0\), and the corresponding normalised integrals of every smooth resolved observable converge to their leading coefficient. Such a positive realiser exists whenever the zero fibre is nonempty and the prior is positive throughout its base image. This identifies the RLCT and multiplicity in the Laplace-asymptotic sense; the leading functional is positive and satisfies the resonant-zero-fibre sup bound. Zeta-pole identification, a Riesz representation, and comparison of arbitrary observables across different modifications are not claimed.

The qualification now is an explicit **hypothesis of the geometric theorem**, not a missing nonvanishing argument. Do not describe the result merely as “conditional leading-index results.”

## C. Closure and optional follow-ups

**CLOSE it. No additional unit is needed to justify the paper-facing theorem.**

My ranking by marginal value *after closure*:

| Rank | Candidate | Cost | Assessment |
|---|---|---:|---|
| 1 | \(x^2y^2\) local regression | S | Excellent sanity/example theorem: tests multiplicity two, the log term, and the useful positive-realiser hypothesis with ordinary cutoffs. |
| 2 | Riesz representation on the compact resonant fibre | M | A worthwhile conceptual upgrade. Requires the restriction/extension and density machinery, not just invoking Riesz. |
| 3 | Zeta-pole identification | M–L | Valuable if the paper promises the pole formulation of RLCT; otherwise a separate analytic extension. |
| 4 | Common-refinement/kernel D7 | L | Broader scope, but unnecessary for the base-observable invariance already established. |

If you want one final packaging unit rather than new mathematics, make it a **single positive-realiser asymptotic corollary** combining coefficient vanishing, convergence, and strict positivity. That improves discoverability and matches the primary paper statement. It is not a reason to keep Theorem D open.