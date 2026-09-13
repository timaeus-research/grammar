## Decision

**Accept J-min as closed at J3, with J4 recorded as a rejected finite-order target—not an unfinished obligation.** The landed endpoint meets the substantive stopping rule: one produced kernel, a genuine vector space of observables, linear coefficient functionals, and an all-orders expansion using their values.

**Close the paper’s Lean programme after a bounded claim-wording pass.** Neither distribution infrastructure nor general resolution production should become a new prerequisite. Then move to a claim survey of `averaging_dataset.tex`.

This assessment uses the supplied sources and your status report; it is not an independent repository audit.

## 1. J-min closure and the J4 finding

### 1.1 What is now established

The important distinction has been preserved correctly:

- **Abstract level:** a certificate yields kernel data and certifies its own observable. The `rfl` identities expose the field’s construction, but do not make the abstract amplitude certificate reusable for arbitrary observables.
- **Producer level:** changing the observable extension on the **same domain** preserves the produced kernel.
- **Functional level:** `jetFunctional` is an actual `LinearMap`, and `hasCoordFreeExpansion_obsSpace` uses that map’s values as the expansion coefficients.

That is a satisfactory endpoint, not merely a definition of an unconstrained `tsum`.

Keep the fixed-domain qualification prominent: this proves a common functional on `obsSpace A.Ω`, not automatic admissibility of every smooth or locally analytic observable on an unspecified neighbourhood.

### 1.2 Infinite order: accept the obstruction, narrow the wording

The correct conclusion is:

> The exact-moment representation can involve arbitrarily high normal derivatives at a fixed spectral index. In general it does not truncate at an observable-independent normal order.

Do **not** strengthen this to “every coefficient at every codimension-\(\ge2\) stratum has infinite order.” Special indices, kernels, cancellations, and observables can behave differently.

There is also a point to check in the J4 diagnostic:

> “Nonzero exactly when the minimum of the candidate exponents equals \(\mu\)”

is too strong as a general statement about the full coefficient kernel. The minimum determines the leading exponent of a monomial integral, but nonminimal candidate exponents can contribute subleading coefficients.

For example, on the unit square, for nonnegative integers \(a<b\),
\[
I_{a,b}(N)
=\int_0^1\!\int_0^1 x^a y^b e^{-Nx^2y^2}\,dx\,dy
=\frac{J_a(N)-J_b(N)}{b-a},
\qquad
J_c(N)=\int_0^1 t^c e^{-Nt^2}\,dt.
\]
Thus there are contributions at both \((a+1)/2\) and \((b+1)/2\). Nevertheless, **fixing \(a\) and letting \(b>a\) vary already proves the intended obstruction:** the coefficient at \((a+1)/2\) receives contributions from arbitrarily large total Taylor degrees. At \(b=a\), the logarithmic resonance must be treated separately.

This calculation is an explanatory mathematical check, not a claim that a Gamma formula has been formalised.

### 1.3 Terminology and one immediate documentation fix

Use:

> **Linear coefficient functional on analytic observables, represented by a convergent series of normal-jet pairings.**

“**Analytic jet functional**” is a good short name once defined that way. Do not use it as shorthand for a topological analytic functional, hyperfunction, or distribution.

There is a concrete stale claim in the supplied CCCLIII module header:

> “the observable-independent **finite-order** coefficient functional”

Remove “finite-order.” Also replace the closing sentence suggesting that J4 is merely an omitted finite-order continuity bound with something like:

> “The exact-moment representation need not have finite normal order. No topology or continuity on a smooth test-function space, and no distributional extension, is asserted.”

This is a closure edit, not another research unit.

### 1.4 Is a weighted estimate worth one unit?

**Optional, not a closure requirement.** My default recommendation is to defer it unless the paper actually needs a quantitative bound.

The displayed proposed estimate needs correction. From the stated coefficient formula, assuming compatible tensor norms with
\[
|\langle J,B\rangle|\le \|J\|\,\|B\|,
\]
the direct bound is
\[
|L_q\psi|
\le
\sum_I\int_{S_I}
\sum_{r=0}^{\infty}
\frac{1}{r!}
\|B_{I,r,q}(s)\|\,
\|D_\perp^r\psi(s)\|\;d\nu_I(s).
\]
One cannot simply insert \(b^r\) on the right: for \(b<1\), that makes the proposed bound smaller. A weighted formulation must compensate by an inverse weight in the jet norm, or use the actual chart-scaled tensors and majorants. Moreover, your box sizes and frames are chart-dependent.

Two further distinctions matter:

1. `Certified` gives summability of scalar pairings and integrability of their sums. It does **not by itself** give integrability of the sum of products of tensor and jet norms.
2. An absolute-majorant inequality is not yet continuity for a pre-existing analytic-function topology. A topology or a fixed controlling seminorm must be specified.

If you choose this follow-up, cap it at **one unit**:

- reuse the existing certificate majorants;
- prove an absolute-majorant estimate with explicit finiteness hypotheses;
- obtain a fixed-space seminorm bound only if it follows directly;
- stop before analytic topological-vector-space or smooth-distribution infrastructure.

An observable-dependent certificate bound alone adds little to the paper’s headline theorem. A prior-dependent bound against a fixed analytic seminorm would add more, but may exceed that budget.

## 2. Paper-claim closure list

The dots and zero audit mismatches establish excellent traceability. They do not, by themselves, establish that surrounding prose has exactly the theorem’s scope.

### (a) Supported

Subject to the exact hypotheses of the cited declarations:

1. **A coordinate-free coefficient formula from resolved and coefficient certificates**, with an all-orders power–log expansion and the stated little-\(o\) remainder.
2. **Coordinate monomial producers:** the reported one-sided and two-sided box constructions from holomorphic packets, for arbitrary positive coordinate orders, with trivial Jacobian orders.
3. **Cube blow-up model producers and assembly:** the reported chart constructions with units and Jacobian order \(d-1\), assembled into the original cube integral.
4. **The reported spectral containment**, including the cube support \((d+\ell)/2\), and the cube leading coefficient under its \(d\ge2\) hypotheses.
5. **Scalar coefficient canonicity / packet independence** to the extent stated by the cited uniqueness theorems.
6. **Observable-independent produced kernel under `withObs` on the same domain.**
7. **Real-linear analytic coefficient functionals** and the expansion with their values as coefficients.
8. **Dependence of the pairing formula on normal germs at the covered bases**, together with vanishing of the field off those bases.

For cube linearity and other material not included here, this classification relies on your reported landed results.

### (b) Supported only with explicit qualifications

| Paper phrase | Required qualification |
|---|---|
| “Coordinate-free expansion” | A tensorial formulation relative to supplied resolved geometry, normal data, measures, frames and certificates—not intrinsic gluing or independence of all geometric choices. |
| “The kernel depends only on the prior” | With the model, geometry, collar/chart parameters and prior extension data fixed; the proved producer identity varies the observable on a fixed extension domain. |
| “Canonical coefficients” | Scalar asymptotic coefficients under the relevant uniqueness hypotheses—not canonical tensor fields or chartwise densities. |
| “All orders” | Every fixed truncation order has the stated asymptotic remainder—not convergence of the full asymptotic expansion. |
| “Spectrum” | An allowed spectral set unless nonvanishing is separately proved; admissible terms may have zero coefficient. |
| “For analytic observables” | Observables satisfying the precise extension condition on the fixed domain and the producer’s other hypotheses. |
| “General resolved geometry” | The abstract theorem accepts such geometry **with certificates**. Their existence is not derived from a general resolution theorem. |
| “Exceptional-divisor coefficients” | A normal-jet representation over the designated strata; this alone does not establish distributional support. |

### (c) Unsupported as Lean-facing claims; reword or drop

#### (i) “The expansion coefficients are distributions supported on the exceptional divisor”

**Unsupported. Replace it.**

Suggested wording:

> “For the certified models, the expansion coefficients are linear functionals on the specified analytic observable space, represented by convergent normal-jet pairings over resolved strata. No extension to distributions on smooth test functions is asserted.”

There are two separate missing assertions: continuity on a smooth test space, and a distributional support theorem. Also, your functional acts on observables downstairs via pullback. A distribution on the resolved space and a distribution downstairs supported on the image of the divisor are different objects.

Crucially:

> Infinite order of this particular jet representation does not, by itself, prove that no alternative distributional representation exists.

A reorganisation over positive-dimensional strata could behave differently. The justified conclusion is “the finite-order truncation target fails for this representation; distribution packaging is not established.”

#### (ii) “The expectation functional \(E_n[\phi]\)” meaning a normalised expectation

**Unsupported by the numerator theorem alone.**

Use
\[
N_n[\psi]=\int_W\psi(w)\varphi(w)e^{-nK(w)}\,dw,
\qquad
Z_n=N_n[1].
\]
The landed theorem is about \(N_n\). If “expectation” means
\[
E_n[\psi]=N_n[\psi]/Z_n,
\]
say explicitly that its expansion is not supplied by this theorem.

A ratio theorem requires, at minimum:

- identification of the denominator with \(N_n[1]\);
- eventual nonvanishing, normally via a positive leading coefficient;
- denominator scale and remainder control;
- an actual quotient-expansion theorem.

Do not assume the numerator spectrum survives division: logarithmic denominators can produce inverse-log or other reorganised asymptotics.

`GibbsJointRatio` may provide useful infrastructure, but its existence is not an instantiation for these coefficients. **Renaming the numerator closes this paper gap without opening a ratio programme.**

#### (iii) A main theorem asserted for a general Hironaka resolution

**Not supported as an unconditional formalised theorem.**

Recommended statement structure:

> **Certificate theorem.** Given resolved geometry equipped with a `ResolvedCertificate` and a `CoefficientCertificate`, the integral admits the stated coordinate-free expansion.

Then:

> **Formalised instances.** These certificates are constructed for the coordinate monomial box models and the specified cube blow-up models.

A broader mathematical theorem may remain in the paper with its own proof, but the prose must distinguish it from the Lean result. Hironaka alone should not silently stand in for production of analytic amplitude identities, measures, units, normal presentations, summability and global assembly.

#### Other claims to exclude

Continue to exclude the reported non-claims: general SNC atlas production, intrinsic gluing, parity cancellation, Gamma formula, the missing \(d=1\) leading value, tensor-field packet independence, and automatic complexification.

### Paper closure gate

I recommend only these actions:

1. Correct the stale finite-order module documentation and narrow the J4 diagnostic.
2. Search theorem statements, abstract, introduction and captions for **distribution**, **support**, **expectation**, **general resolution**, **canonical**, and **finite order**.
3. Apply the distinctions above wherever those words exceed the cited result.
4. Refresh the pin and audit after edits; push the synchronised mirror to Overleaf.
5. Mark the Lean-facing paper programme closed.

**No new Lean theorem is mandatory for this gate.** If the paper insists on retaining one of the stronger Lean claims, that becomes a separately scoped obligation—not an implicit continuation of J-min.

## 3. Transition to `averaging_dataset.tex`

**Yes: the first companion-note consult should be a claim-and-dependency survey, not implementation.** Preserve the already formalised §4 as a closed asset unless the survey finds an actual mismatch.

### What to send

1. **The full current `.tex`**, including appendices, macros defining probabilistic notation, and version/commit.
2. **The `\leanref` inventory**, mapping each dot to its declaration, plus the note’s current audit report.
3. **Exact statements and declaration names** for likely reusable results in:
   - `EmpiricalConcentration`;
   - `GibbsJointRatio`;
   - `PosteriorTransfer`;
   - `L1Seq`;
   - the existing §4 fluctuation results.
   
   Start with statements; send proof internals only where dependencies become unclear.
4. **A notation-and-limit sheet:**
   - dataset size versus inverse temperature/sample-size parameters;
   - what is random and on which probability space;
   - fixed prior/model versus dataset-dependent objects;
   - numerator versus normalised posterior expectation;
   - convergence mode for every remainder;
   - separate, iterated or joint limits.
5. **Editorial priorities:** which claims are central, which may become conditional, and which may be moved to an appendix or dropped.

### The survey’s required output

A ledger with one row per substantive claim:

> exact claim → exact hypotheses → existing declaration → missing bridge → status → proposed unit/gate.

In particular, distinguish:

- population asymptotics from empirical asymptotics;
- a pathwise expansion from an expansion whose remainder is controlled in probability or \(L^1\);
- scalar coefficient CLTs from joint finite-dimensional or functional CLTs;
- concentration estimates from distributional convergence;
- a fixed spectral structure from dataset-dependent exponents or multiplicities;
- numerator fluctuations from normalised-ratio fluctuations.

A deterministic theorem applied separately to each dataset does **not** automatically supply a stochastic remainder estimate. Likewise, a coefficient CLT does not automatically justify exchanging dataset averaging with a jet series, integral or asymptotic limit.

### Unit discipline

The survey should select the smallest missing bridge feeding a central note claim. Each implementation unit must have:

- one explicit target theorem;
- a hypothesis list matching the note;
- named reusable dependencies;
- a success gate and a stopping rule;
- a corresponding `.tex` edit if the original claim is too strong.

Do not pre-authorise a general empirical-process or functional-CLT programme. If a missing bridge requires that scale of infrastructure, make the note conditional or narrow it first.

**Final disposition:** J-min closed; paper closure requires a short scope-and-wording pass, not distribution work; next consult is the companion note’s claim survey using the `.tex`, dot map, theorem signatures and limit conventions.
