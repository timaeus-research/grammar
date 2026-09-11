**Recommendation: do a bounded Hironaka audit first, then prove the smallest honest single-chart endpoint. Do not globally replace cubes by positive-phase-boundary regions yet.**

The bridge is now a real theorem, but inhabitance remains a geometric assertion. Three corrections matter:

1. **A cube is not an invalid integration domain.** It is a domain your present fibre-product interface does not automatically accommodate.
2. **Positive phase on the boundary is a substantial global hypothesis**, not a harmless choice of a smaller neighbourhood.
3. **“Contained in one monomial chart” is weaker than “admits one compatible strip/box construction.”** The former does not, by itself, eliminate the cutting problem.

I am taking the reported Lean interfaces as given; I have not inspected the repository or the paper’s precise hypotheses.

## A. Do not make the positive-boundary endpoint the only endpoint

For continuous \(K\geq0\) and compact \(\Omega\), your condition
\[
Z\cap\Omega\subseteq\operatorname{int}\Omega
\]
does give a positive lower bound for \(K\) on a neighbourhood of \(\partial\Omega\). Thus **a sufficiently small boundary shell is a tail**. That part is correct.

But this is often unavailable for the local examples you want.

For example, if
\[
K(x,y)=x^2y^2
\]
on \(\mathbb R^2\), **no compact region containing the origin in its interior has positive phase everywhere on its boundary**. Follow either coordinate axis until it leaves the region. It crosses the boundary at phase zero.

More generally, a compact region containing a zero cannot satisfy your condition if the connected component of \(Z\) through that zero continues out of every compact region. This is exactly why positive-dimensional zero sets make a *local* positive-boundary formulation restrictive.

Consequently:

* `Ω := {K ≤ ε} ∩ L` works only if the artificial boundary from \(L\) is already separated from \(Z\).
* It does not solve the problem merely because \(\varepsilon>0\).
* A normal-coordinate product box usually **fails** the positive-boundary condition, while being perfectly suitable for your tiling interface.

That last point exposes a conflict between your proposed change in A and your proposed example in B.

### What to change

Keep, or introduce, a **region-parametric conditional endpoint**:

> Given localisation on \(\Omega\) and an exact normal tiling of \(\Omega\), obtain the expansion.

You already effectively have this. Then establish separate sufficient hypotheses:

1. **Adapted product/box regions**, including ones whose tangential boundary meets \(Z\).
2. **Positive-phase-boundary regions**, where boundary geometry can be ignored near the low-phase set—but the interior cross-chart problem still needs solving.
3. Eventually, **ordinary cubes or other domains with boundary**, using boundary-compatible geometry if needed.

The claim “cube boundary points cannot be handled by any chart” is too strong. They can sometimes be handled directly, and more generally one can try to resolve/rectilinearise the phase **together with the domain’s defining inequalities**. What fails is the inference from phase monomialisation alone to your particular rectangular presentations.

### Cutoffs and the paper

A smooth cutoff is not equivalent to hard integration over a positive-boundary region. It changes the weight. Nor does a general smooth cutoff preserve your analytic \(\ell^1\)-amplitude interface.

However, **“smooth amplitudes preclude power–log asymptotics” would be wrong**. They can be treated by finite Taylor expansions with remainder estimates, order by order. That is a different analytic backend, not an immediate inhabitant of your current one.

If the paper explicitly assumes compact \(W\) with \(K>0\) on \(\partial W\), then your positive-boundary formulation captures that boundary-separation feature. **Do not attribute that assumption to the paper without checking the exact statement.** It is not a generic consequence of choosing \(W\) small.

## B. Yes to a single-chart theorem—but split the claim

There are three distinct endpoints here.

### B0. Exact monomial on an adapted product box

Start here.

Assume:

* exact monomial phase on a product box;
* a monomial Jacobian weight times a positive analytic unit;
* either an amplitude datum directly, or joint analyticity with the required series margin;
* the evident injectivity and measure hypotheses.

Then reflections, `PositiveBoxCore`, and `ExactNormalTiling` should give an unconditional theorem. With all active normal coordinates already in one box, **you may not need `MonomialTiling` at all**: the orthants themselves are the pieces, up to null coordinate hyperplanes.

This is the cheapest honest endpoint for coordinate-power products. It also gives a valuable integration test of the whole bridge.

**Prove an actual expansion theorem for an explicit phase, not merely another structure-to-structure implication.**

### B1. One globally compatible normalisation, with an adapted image region

Next prove the theorem you describe for
\[
\Omega=\phi\bigl(T^{-1}(R)\bigr),
\]
where \(R\) is a specified box on which **one chosen normalisation and its inverse are valid**, with analytic neighbourhoods adequate for the amplitudes.

This is worthwhile. It upgrades the exact-monomial example to a genuinely nontrivial analytic-unit theorem and tests every ingredient you have landed.

Your proposed composition route is credible **under those explicit uniform hypotheses**.

### B2. Arbitrary low-phase region contained in one chart

Do **not** identify this with B1.

Suppose the low-phase part of \(\Omega\) is contained in \(\phi(V)\). The pullback of \(\Omega\) can still cut normal fibres arbitrarily. Likewise, covering the relevant divisor by several strip-normalisation neighbourhoods creates overlap ownership problems even though the original map \(\phi\) is one chart.

Thus:

> One chart removes cross-chart transition geometry only when the construction uses a compatible domain decomposition within that chart.

It does not magically make the pulled-back integration region rectangular.

### Four plumbing hazards worth stating now

Your estimate may be right for B1, but I would not endorse “no new ideas” until these are explicit.

1. **The series margin is not supplied by a finite tangential cover alone.**  
   Joint analyticity at \((v_0,0)\) gives a sufficiently small normal radius. It need not cover a previously fixed normal height \(b\). Choose heights after obtaining uniform analytic control, or prove the required refinement lemma.

   In particular, shrinking a normal box does **not** generally leave a phase-gap remainder: another normal coordinate can still vanish. Your absorption/tiling theorem is relevant precisely here.

2. **Disjoint measurable bases need compact envelopes, not necessarily compact ownership sets.**  
   Subtracting earlier members of a finite compact cover generally produces noncompact measurable sets. State the amplitude theorem on a compact envelope and restrict its measure to a measurable ownership subset.

3. **The full Jacobian factorisation must survive every composition.**  
   You need the final monomial exponents and an analytic nonvanishing residual unit—not merely a pointwise determinant formula. Taking absolute values is harmless only after controlling the residual unit’s sign on the neighbourhood being used.

4. **Coverage modulo null sets is an independent obligation.**  
   Orthant walls, exceptional coordinate sets, and their images must be disposed of explicitly. Chartwise injectivity away from the exceptional set does not itself state the necessary measure identity.

**Verdict:** B0 is unquestionably worth doing. B1 is worth doing after B0. B2 should remain conditional until its domain geometry is supplied.

B1 reduces the general problem to cross-chart geometry **plus domain adaptation and compatible ownership**. Saying “exactly cross-chart tiling” is honest only if that phrase explicitly includes those obligations.

## C. The cross-chart proposals

### C1. Analytic monomial transitions: useful, not sufficient as stated

There are two different spaces here:

* the resolved/source space, where the exceptional divisor lives;
* the original target, where its image can be singular and the resolution map collapses directions.

A chart transition can extend analytically across the divisor **on an actual source-chart overlap**. That is ordinary atlas behaviour. But a common target image does not automatically determine such an overlap at exceptional points.

In particular, writing
\[
\phi_2^{-1}\circ\phi_1
\]
on the divisor is generally invalid if these are maps to the original space: the inverse need not exist there.

Your wall claim also needs weakening:

> An analytic hypersurface transverse to the exceptional divisor upstairs need not map to a smooth analytic hypersurface downstairs at the divisor image.

Blow-down can collapse it, make its image singular, or produce only a semianalytic/subanalytic piece. Analyticity off the divisor does not repair this.

### A simple transition test

Even among ordinary analytic coordinate systems, preserving the divisor and the phase is weaker than preserving fibres. Consider
\[
(x,t)\longmapsto(x,s=t+x),\qquad K=x^2.
\]
The divisor coordinate is unchanged; the transition is analytic across \(x=0\); the exact monomial phase is unchanged.

But the tangential wall \(t=0\) becomes \(s=x\), not a wall saturated for the new normal fibres.

This is **not** a counterexample to all possible refinements: one can straighten that particular wall again. It is a counterexample to the proposed implication that analytic divisor-compatible transitions automatically preserve the rectangular structure you need.

### A genuinely sufficient condition

A deliberately strong sufficient interface would require:

* overlap domains that are unions of cylinders;
* a common tangential foliation, so tangential coordinates transform independently of normal coordinates;
* normal coordinates related by permutations and constant positive rescalings, with compatible phase exponents;
* compatible rectangular normal domains.

For a finite family, you can transport normal cut levels, make a finite rectangular refinement, and partition tangential ownership measurably.

Allowing normal rescalings by positive analytic functions of the tangential variables is a plausible next generalisation, but then **variable-height refinement is a theorem to prove**, not something included for free.

Actual resolution atlases generally provide much less than this strong fibre-compatible interface. Normal-crossings divisor coordinates often transform monomially up to analytic units; that does **not** mean the units are independent of normal variables or that tangential coordinates preserve a chosen normal fibration.

So:

* **Yes:** audit analytic transitions on a genuine resolved space.
* **No:** do not make “analytic monomial transitions” your new asserted inhabitance criterion without a precise refinement theorem.
* **No:** do not expect target-stratum tiling alone to eliminate exceptional-fibre geometry.

A more defensible research proposition is a **finite boundary-adaptation/ownership theorem on the resolved space**, rather than analytic-wall descent to the target.

### C2. Measurable subtraction and exhaustion

Your diagnosis is correct.

Allowing arbitrary measurable tangential bases handles an ownership set of the form
\[
A'\times(0,b]^m.
\]
It does not handle an arbitrary measurable subset of
\[
A\times(0,b]^m).
\]
You need fibre saturation, at least modulo the relevant measure, or an independent rectangularisation theorem.

A.e.-disjointness weakens the treatment of walls themselves. It does not remove positive-measure wedges created by tilted walls.

And **infinite exhaustion is an additional analytic problem**: convergence of the measures or integrals does not by itself justify passing full asymptotic expansions through the exhaustion. You would need uniform remainder control and summability of coefficients.

So: no free lunch, twice.

## D. Five bounded audit questions

Read theorem statements and structure fields first. Trace constructors only when a field’s meaning is unclear.

| Question | “Yes” must actually mean |
|---|---|
| **1. Is there a common resolved object?** | The output charts belong to one resolved space/map, or equivalent explicit gluing data exist—not just a finite family of admissible composites into the target. |
| **2. Are overlaps certified across the divisor?** | Actual source overlaps, analytic inverse transitions, compatibility with the target map, and coherent identification of divisor components. Individual monomial formulas are not enough. |
| **3. Is coverage proper/compact enough?** | A compact relevant target set has a controlled compact preimage, or an equivalent finite relatively compact chart cover with analytic extension margins. Pointwise chart existence is not enough. |
| **4. Is global multiplicity controlled?** | Off a controlled null exceptional image, the resolved map is one-to-one, or there is an explicit multiplicity formula suitable for integration. Chartwise injectivity alone is not enough. |
| **5. Is there boundary-compatible ownership?** | Finite a.e.-disjoint ownership domains whose chart pullbacks have the required normal-product shape, or a theorem simultaneously adapting prescribed boundaries to that shape. |

For `Q(n)` refinement, ask particularly whether replacing a partial resolution by resolutions of pulled-back functions preserves **global overlap and ownership information**, or merely preserves coverage and monomialisation.

### Interpreting the answers

* **Yes to all five:** route (ii) is plausibly an extraction/plumbing project.
* **Yes to 1–4, no to 5:** you have the right geometric substrate, but the central tiling theorem remains new mathematics. This is not “just prove monomial transitions.”
* **No to 1 or 2:** a chartwise `Q(n)` output is not yet a resolution atlas. Do not silently import atlas facts from the informal construction.
* **No to 3 or 4:** even a different gluing method will need additional global coverage/integration infrastructure.

Questions 1–4 being positive would also support a future smooth-amplitude route using partitions of unity. They do not make that route compatible with the existing \(\ell^1\)-analytic backend without further work.

**Audit stop rule:** produce this five-entry table with declaration names and exact missing fields. Stop before proving a new resolution theorem during the audit.

## E. Order of work and stop rules

### 1. Freeze the current logical status in the documentation

Do this immediately and briefly.

* `MonomialTiling` supplies local exact measurable decomposition machinery.
* `ExactNormalTiling.cutoffExpansion` is the conditional analytic conclusion.
* `HasExactNormalTilings d → CompatibleDivisorLocalisation d` is a bridge, not inhabitance.
* No general adapted partition of unity or global compatible tiling has thereby been constructed.

For the paper bookkeeping, mark `exists_monomialTiling` as replacing **part of the role** of `lem:adapted_pou`, unless you have checked equality of hypotheses and scope. Local tiling is not automatically the paper’s global gluing lemma.

Do not put an unconditional “main theorem proved” dot beside a conditional expansion theorem.

### 2. Run the bounded Hironaka audit

This comes before changing the endpoint. Its result determines whether you are adapting an existing global object or asking a chartwise monomialisation theorem for information it never promised.

**Stop:** once the five answers are documented.

### 3. Prove B0 and an explicit example

Exact monomial, adapted box, orthants, analytic amplitude with an explicit convergence margin. End with an actual cutoff expansion.

**Stop:** if this unexpectedly requires arbitrary overlap ownership, narrow the statement. B0 should not become another name for the research gate.

### 4. Prove B1, not B2

One specified strip normalisation, one adapted image region, explicit analytic margins, finite measurable base partitions inside compact envelopes.

**Stop:** the first time the proof says “cover by finitely many normalisation charts and subtract previous images.” That has crossed back into the unresolved ownership problem.

### 5. Choose the general endpoint only after the audit

* If the paper assumes positive-phase boundary, add that global formulation—but do not discard adapted-box local theorems.
* If the target remains arbitrary cubes, state the missing boundary-adaptation theorem honestly.
* If the resolution output lacks compatible ownership, leave the general theorem conditional or pursue a separately budgeted smooth-amplitude backend.

**Bottom line:** your strongest next deliverable is **an unconditional adapted single-chart expansion**, preceded by a short audit. The wrong next move is to replace cubes by positive-boundary regions and present that as merely correcting the shape: it changes the scope, excludes basic local normal-crossings examples, and still does not solve cross-chart gluing.
