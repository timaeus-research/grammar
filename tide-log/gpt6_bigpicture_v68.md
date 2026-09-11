## Decision

**Take route (i), but first prove a corrected local rectangular-extraction theorem. Do not start recovering a global resolution space from the hironaka internals yet.**

Your analysis substantially simplifies the **single-chart** problem. It does not solve the cross-chart localisation problem. The useful distinction is:

1. **Exact monomial product box → one core:** essentially correct.
2. **Monomial product box → smaller product cores and a gapped remainder:** your recursive mechanism works, with a clean invariant.
3. **Finite overlapping monomial charts → such a decomposition of the target measure:** still an additional geometric theorem.

Two corrections matter immediately:

- Your proposed interface must require **injectivity off a null exceptional set**, not injectivity on the entire box.
- Unit 6 needs **more than the stated estimate with \(R>b\)**. The coordinate expansion has an exponential combinatorial cost; the number of words with a prescribed multiplicity is not polynomial.

Also check whether Unit 1 actually permits **different numbers of normal variables in different cores**. Your proposed construction needs that.

---

## 1. Claims (A)–(E)

### (A): Yes, conditional on the amplitude and transport hypotheses

An exact monomial product box is a single core. Splitting normal coordinates into orthants and putting the signs into the compact tangential parameter is the right construction.

The lower-dimensional faces require no separate cores:

- the faces themselves are null for the relevant absolutely continuous chart measure;
- their neighbourhoods are already included in the full box integral;
- the box theorem computes the asymptotics of that entire integral, including contributions associated with different normal exponents.

Thus **do not stratify the interior of a deep box merely because it contains several divisor strata**. That would duplicate work.

But “exact monomial phase on a box” alone is not enough. You also need:

- the appropriate change-of-variables statement;
- the monomial Jacobian factor;
- an amplitude with an absolutely summable Taylor expansion on the chosen box.

In particular, **real analyticity on a neighbourhood of a real closed box does not imply that its Taylor series at the normal origin converges throughout that box**. Shrinking below a suitable normal Taylor radius remains necessary.

Your correction from continuous to analytic observable is appropriate for this route. More precisely, analyticity of the observable is a natural sufficient hypothesis; the amplitude condition does not logically force every observable to be analytic, since special densities or degeneracies can conceal nonanalyticity.

### (B): Correct on a sufficiently small product strip, not on the arbitrary readout domain

Write
\[
T_i(y)=y_i\rho(y),\qquad
\partial_iT_i=\rho+y_i\partial_i\rho.
\]

On a compact tangential base crossed with a sufficiently small interval about \(y_i=0\), positivity of \(\rho\) gives a uniform strip on which this derivative is positive. Fibrewise monotonicity then proves injectivity. The other coordinates are unchanged.

Your image-box inclusion is also correct **when the domain really contains the full fibres**
\[
Q'\times[-b_0,b_0].
\]
It is not a consequence of compactness for an arbitrary `dom i` supplied by `PartialResolution`.

The Jacobian formula is right:
\[
|\det D(\phi\circ T^{-1})|
=
|z^h|\left(
\frac{|v|\rho^{-h_i}}{\rho+y_i\partial_i\rho}
\right)\circ T^{-1}.
\]
On a suitable connected neighbourhood, the bracket is a positive analytic unit.

So:

- no IFT is needed for the injectivity argument on that strip;
- local analytic inversion is still needed;
- the pointwise inverses glue by injectivity, giving analyticity of the inverse throughout the relevant open image.

**Do not package this as a global statement about an arbitrary monomial chart domain.** Package it as a rectangular-strip theorem.

### (C): The mechanism works; use a weighted-product invariant

This is your strongest simplification. There is a clean way to make the recursion precise.

For a state with remaining normal set \(S\), let \(B_S\) be its tangential base and set
\[
q_S(t)=\prod_{i\notin S}|t_i|^{k_i}.
\]
Maintain the invariant
\[
q_S(t)\ge b^{\sum_{i\notin S}k_i}.
\tag{*}
\]

Initially this follows from \(|t_i|>b\) outside \(S\). After leftovers are transferred, the individual inequalities \(|t_i|>b\) need not remain true, but \((*)\) does. **That is the invariant the proof should use.**

Choose \(i\in S\), and put
\[
w_i=u_iq_S(t)^{1/k_i},\qquad
L_{S,i}=b^{1+\left(\sum_{j\notin S}k_j\right)/k_i}.
\]
Then \((*)\) guarantees that the fixed interval \(|w_i|\le L_{S,i}\) lies inside the available fibre.

The leftover satisfies
\[
q_S(t)|u_i|^{k_i}
>
L_{S,i}^{k_i}
=
b^{\sum_{j\notin S}k_j+k_i}.
\]
That is exactly the invariant for the child state \(S\setminus\{i\}\).

Consequently:

- each extraction produces a product core;
- each leftover becomes part of a tangential base for a smaller normal set;
- recursion terminates;
- the final zero-normal states are uniformly gapped.

The rescaling Jacobian is \(q_S^{1/k_i}\); the **inverse** Jacobian appearing in the transported density is its reciprocal.

#### Necessary bookkeeping

1. **Bases carry history.** They are not simply the original sets \(\{|t_i|>b\}\). Use a finite family of states, or merge compatible bases only after proving disjointness.

2. **Half-open sets versus compact parameters.** Your literal partition has strict inequalities and therefore generally noncompact bases. Use compact closures and prove overlaps are null, or otherwise provide compact carriers with restricted measures. For these monomial walls and Lebesgue-derived measures, this is manageable, but it is a theorem.

3. **Unequal side lengths.** The extracted box has side \(L_{S,i}\) in one coordinate and \(b\) in the others. If `CorePresentation` requires one common side, equalise by a constant diagonal rescaling. For sides \(r_j\), choose
   \[
   B=\left(\prod_j r_j^{k_j}\right)^{1/\sum_j k_j},
   \qquad z_j=(r_j/B)s_j.
   \]
   This preserves the coefficient \(\beta\).

4. **Different normal dimensions.** The recursion genuinely creates different \(|S|\). If `AnalyticCoreDecomposition D M K n β` fixes the same positive-normal dimension for every core, revise the interface to a dependent family. Padding with additional positive-exponent variables is not harmless.

5. **Amplitude convergence still needs proof.** Here the rescaling depends only on tangential variables, which is excellent: normal analyticity reduces to that of the original amplitude under diagonal scaling. But provide a uniform summability estimate, not just “analytic near the closed box.”

**Verdict:** this is a complete local replacement for a cutoff construction *inside a suitable exact-monomial product box*. It is not yet a complete replacement for the paper’s global localisation lemma. Nor would I certify that the paper’s stated lemma is false without checking its precise hypotheses and proof.

### (D): Locally yes; prefer shrinking

Using \(z_{i_0}\) as a tangential coordinate near its nonzero level wall is legitimate where the relevant coordinate map is nonsingular. Your existing map \(T\) supplies precisely such coordinates in the monotonicity strip.

But “transverse to the divisor” needs a stratified interpretation. At divisor crossings, transversality merely to one component is not enough to guarantee simultaneous coordinate adaptation.

My recommendation is unequivocal:

> **Shrink local boxes so the unit-removal map is an analytic diffeomorphism on a neighbourhood of each box. Do not solve the noninjective outer-region problem in the first implementation.**

Compactness gives a finite local cover of an appropriate compact divisor locus. This makes shrinking harmless for **local analysis**. It does **not** make it harmless for exact assembly: the resulting boxes overlap, which is the unresolved gate.

### (E): Correct warning, overstated characterisation and conclusion

Three separate points:

1. **The readout does not expose compatible transitions or a common resolved space.** Correct.

2. **Cross-chart assembly is exactly wall matching.** Too narrow. Wall matching is one possible solution. Other solutions include divisor-adapted weights on a common space, further simultaneous resolution/rectilinearisation, or a different asymptotic theorem allowing smooth localisation.

3. **Therefore the proposition is not provable from the readout.** Too strong as a logical claim. The readout does not directly supply what your proposed construction requires. That is not an impossibility theorem: one might prove substantial additional geometry from the finite analytic maps, or invoke a stronger resolution theorem.

Also, analytic transition maps would not by themselves finish the job. They must preserve the relevant divisor structure, and the proposed walls must remain suitably adapted at all corners and intersections.

Finally, **a.e. cover is sufficient for the measure identity**. The null-set qualification is not itself the obstruction. The missing ingredient is control of positive-measure overlaps and of localisation amplitudes near the divisor.

---

## 2. Which route?

### Recommend (i), with a stronger and more honest contract

Yes: an interface theorem is the right next deliverable. It is useful progress, not completion.

I would separate two interfaces.

#### A. Exact-normal tiling interface

Finite pieces with:

- compact tangential parameter spaces;
- product normal boxes;
- exact phase \(\beta u^{2k}\);
- a.e. injectivity/change-of-variables data;
- monomial Jacobian density;
- uniform normal analyticity/summability data;
- pairwise a.e.-disjoint images;
- coverage of the target low-phase measure;
- all pieces supported in the intended target region.

From this, prove the decomposition directly.

#### B. Geometric monomial-box tiling interface

Finite sufficiently small monomial boxes with analytic units and geometric measure data. Prove that these produce interface A using unit removal and rectangular extraction.

Do not make the second interface so weak that it hides the original problem. In particular:

- **Whole-box injectivity is wrong.** The blow-up map
  \[
  (x,s)\mapsto(x,xs)
  \]
  collapses an entire divisor fibre. Require injectivity off an exceptional null set.
- **“Analytic on a neighbourhood” does not supply the required Taylor-radius margin.** Either include smallness/admissibility certificates or prove their construction.
- **Target restriction matters.** If the theorem concerns closed cubes, pieces must transport into the cube. Coverage by images that protrude outside the cube does not suffice. Cube-boundary geometry may itself need simultaneous adaptation.
- Include the assumptions on the target density. Geometry cannot produce an analytic amplitude from an arbitrary base density.

Name the remaining inhabitance statement explicitly. The stop rule remains:

> Proving `DivisorAdaptedTiling → HasAnalyticCoreDecomposition` is a conditional bridge theorem, not a proof of `CompatibleDivisorLocalisation`.

### Route (ii): audit first; do not commit to recovery

The slope-chart example is valid. But it does not establish that the formalised Q induction retains the structure needed to iterate that tiling.

The questions are:

- Are sibling charts restrictions of one common blow-up?
- Are their refinements compatible on overlaps?
- Are centres globally compatible, or selected independently in local branches?
- How are compact domains restricted after each refinement?
- Can ancestor ownership regions be represented by divisor-adapted inequalities after later coordinate changes?

Shears are not inherently destructive: on a genuine common space they are coordinate changes. The danger is **independent branchwise constructions without coherence**, not the presence of shears. Similarly, a.e. cover is not inherently destructive.

From your readout alone, I cannot honestly say that BM89 as formalised answers these questions positively.

**Size:** recovering only a forgotten tree could be modest. Recovering a tree *with coherent ownership regions and compatible refinement* is a new substantial geometry project—potentially many thousands of lines and months, not another 1,500–2,500-line unit. If centres are incompatible, adding fields will not repair it; a different construction may be needed.

Commission a bounded source audit before choosing this route.

### Route (iii): viable only if you relax the destination theorem

Arbitrary measurable ownership of chart overlaps introduces indicators with uncontrolled normal dependence. Dividing by overlap multiplicity has the same defect. Signed decomposition does not magically remove it.

However, your stronger assertion that exact tiling is necessary for the **population expansion itself** is wrong. Smooth partitions and general normal-crossing asymptotic theorems can account for all transition-region power-law terms.

What they do not automatically provide is your **exact analytic-core decomposition**. Thus there are two research targets:

- prove the exact decomposition interface;
- prove the population asymptotics by a more flexible smooth-amplitude theorem.

The second may ultimately be geometrically cheaper, but it changes the analytic architecture. Do not pursue it casually while claiming to complete Unit 1’s interface.

---

## 3. Size and formulation of (C)

Use the invariant \((*)\) and a fixed elimination order. That is slicker than an informal recursion over all strata.

A useful state contains:

- remaining normal set \(S\);
- compact tangential carrier and measure;
- the weighted-product lower bound;
- a product-domain representation;
- ownership/disjointness information.

The one-step lemma extracts one core and returns a state with one fewer normal coordinate. Prove termination by \(|S|\), and flatten the finite output tree afterwards.

The logarithmic picture is excellent for designing and checking the inequalities. I would **not** formalise polyhedral geometry merely to prove this lemma. It introduces infinities at zero, exponentiation, and measure bookkeeping without eliminating the essential extraction.

A “largest-normalised coordinate” rule still creates comparison walls. It is not obviously simpler than fixed-order elimination.

Your 1,500–2,500-line estimate is plausible for the **geometric splitting engine**, assuming existing infrastructure. It is optimistic if it includes compact-carrier bookkeeping, change of variables, dimension reindexing, common-side normalisation, and ℓ¹ amplitudes.

---

## 4. Unit 6: the important trap

Your coefficient formula is the right coordinate expansion:
\[
c_\gamma(v)
=
\sum_{\operatorname{mult}(r)=\gamma}
p_{v,|\gamma|}(e_{r(1)},\ldots,e_{r(|\gamma|)}).
\]

But
\[
\#\{r:\operatorname{mult}(r)=\gamma\}
=\frac{m!}{\prod_i\gamma_i!},
\]
and summing over \(|\gamma|=m\) gives \(d^m\), not a polynomial.

With the elementary multilinear norm estimate,
\[
\sum_{|\gamma|=m}|c_\gamma(v)|
\le d^m\|p_{v,m}\|.
\]
Therefore a safe direct hypothesis is
\[
db<R,
\]
with a strict intermediate radius for geometric domination. **\(R>b\) alone does not justify your proposed proof**, even with the sup norm. Real multilinear norm control does not automatically give the desired complex-polydisc coefficient estimate without loss.

The pragmatic choice is to shrink the box and absorb this dimension factor. Do not develop optimal several-variable coefficient bounds unless needed.

Two further traps:

- **Arbitrary choices of \(p_v\) need not vary continuously.** Use canonical Taylor data, or prove that the aggregated monomial coefficients equal the appropriate normal partial derivatives. General multilinear representatives need not be uniquely determined off the diagonal.
- **Coordinatewise continuity is insufficient for ℓ¹ continuity.** Prove a uniform summable tail estimate on the compact tangential base, then combine it with continuity of finite truncations.

Joint analyticity near \(K\times\{0\}\), with compact \(K\), should supply the requisite finite-cover uniform estimates. State this as a separate lemma.

I would not promise a ready-made Mathlib `FormalMultilinearSeries ↔ MvPowerSeries` bridge for this exact task without inspecting the pinned version. The reliable approach is:

1. homogeneous coordinate expansion by multilinearity;
2. finite grouping by multiplicity;
3. a dimension-loss ℓ¹ estimate;
4. uniform-tail continuity;
5. evaluation equality by absolute summability and regrouping.

---

## 5. Next four units and stop rules

### Unit 3: parity, local strip normalisation, and interface audit

- Prove local evenness/positive-unit results.
- Prove the compact product-strip monotonicity theorem.
- Ensure inverse analyticity holds on a neighbourhood of the output box.
- Fix heterogeneous normal dimensions and target-support requirements in Unit 1.

**Stop rule:** do not proceed with an interface that cannot represent the output of the proposed recursion.

### Unit 4a: exact-monomial rectangular extraction

Implement the weighted-product invariant and fixed-order recursion. Initially separate geometry from amplitude summability.

**Stop rule:** the theorem must include a.e. disjointness, complete coverage, and a strictly positive tail gap—not merely a covering family of cores.

### Unit 6: uniform analytic coefficients into ℓ¹

Use a generous radius margin and prove continuity in the ℓ¹ norm.

**Stop rule:** pointwise existence of power series or pointwise ℓ¹ membership is not enough for `x : C(K, DataSpace …)`.

### Unit 4b: conditional geometric bridge

Define the corrected tiling interface and prove its implication to `HasAnalyticCoreDecomposition`. In parallel, perform a bounded audit of hironaka’s refinement construction.

**Stop rule:** if the audit does not identify a concrete coherence invariant preserved by refinement, do not launch “tree recovery” as routine formalisation. Record inhabitance as the remaining research proposition.

All of this can live in `grammar`, including stronger wrapper readouts proved using accessible hironaka internals.

**Bottom line:** (A) is right, and (C) is a genuinely useful local solution. They remove unnecessary internal-stratum localisation. They do not yet establish compatible ownership across charts. Build and certify that local machinery now; expose the global obligation precisely; do not confuse the resulting conditional theorem with passage through the research gate.
