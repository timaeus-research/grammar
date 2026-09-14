## Verdict

**Close level (2) as the resolved geometric and germ-locality layer, with a narrowly scoped optional addendum.** The landed results supply intrinsic data on a **fixed resolved manifold**, closed depth and resonance filtrations, coefficient locality on the corresponding compact zero-fibre subsets, and conditional leading positivity and domination.

The principal wording corrections are:

- **Closed superlevel sets**, not “closed strata.”
- **Chart-independent on a fixed modification**, not “resolution-independent.”
- **Germ-local coefficient functionals**, not yet continuous distributions unless continuity has been proved elsewhere.
- **Conditional leading-index results**, not an unconditional identification with the RLCT.

I cannot inspect the commits or the text of #127 here. This is an audit of the supplied signatures and proof descriptions, not an independent source-code audit.

## A. Audit

### (i) Intrinsic depth and coordinate-subspace strata

Yes, the supplied results are adequate, with this formulation:

> On the fixed resolved manifold, the exponent-pair multiset and its cardinality are chart-independent; depth has closed superlevel sets, and each exact-depth stratum is locally a coordinate subspace in a chart centred at one of its points.

Three distinctions matter.

1. **“Intrinsic” has a specified ambient object.**  
   `pairData_eq_of_centered` and `pairs_eq_pairData` remove the choice of centred chart. They do not remove the choice of modification.

2. **The closed objects are the filtration levels.**  
   `isClosed_depthGE` proves that \(\{d\ge c\}\) is closed, equivalently that depth is upper semicontinuous. The exact stratum
   \[
   \{d=c\}=\{d\ge c\}\setminus\{d\ge c+1\}
   \]
   is generally only locally closed. The same distinction applies to resonance counts.

3. **The coordinate-subspace assertion is centred and local.**  
   At a point \(P\) of depth \(c\), `mem_depthGE_iff_of_centered`, together with `not_mem_depthGE_succ_of_mem_source`, identifies the exact-depth-\(c\) locus inside that centred chart with the vanishing of all its active coordinates. In an arbitrary, uncentred chart, an exact-depth locus is generally a union of coordinate pieces, not one coordinate subspace.

Thus **“locally coordinate-subspace strata” is justified without a bundled submanifold theorem**. Avoid implying that Lean already contains the submanifold inclusion, its tangent bundle, or a Whitney-stratification package. The pair data also retain more information than depth alone.

### (ii) Resonant support and the contrapositive

The neighbourhood hypothesis is exactly the right hypothesis for a support statement. Support controls dependence on **germs near a set**, not merely dependence on pointwise values there.

Write
\[
S_{\mu,q}=Z_0\cap\{r_\mu\ge q+1\}.
\]
Your two primary assertions should be:

\[
F=0\text{ near }S_{\mu,q}\quad\Longrightarrow\quad
\mathcal T_{\mu,q}[F]=0,
\]
and
\[
F=G\text{ near }S_{\mu,q}\quad\Longrightarrow\quad
\mathcal T_{\mu,q}[F]=\mathcal T_{\mu,q}[G].
\]

These are precisely the supplied vanishing and germ-congruence theorems.

**Also state the contrapositive as a short corollary:**
\[
\mathcal T_{\mu,q}[F]\ne0
\quad\Longrightarrow\quad
S_{\mu,q}\cap\operatorname{tsupport}(F)\ne\varnothing.
\]
Indeed, disjointness gives an open neighbourhood of \(S_{\mu,q}\) on which \(F\) vanishes. Compactness is not needed for this elementary implication.

For the paper, the germ statement should remain primary. You may summarize it as
\[
\operatorname{supp}\mathcal T_{\mu,q}\subseteq S_{\mu,q},
\]
provided you explain that this is the support/locality assertion for the coefficient functional. **Without D3b, do not silently upgrade that notation into a claim that a continuous distribution has been constructed.**

Also preserve the distinction between the full divisor and `Ξ.zeroFibre`: identify \(Z_0\) explicitly with the compact, prior-relevant zero fibre used by `Ξ`.

### (iii) Resonance convention

Yes. With phase exponent \(2k\), Jacobian exponent \(h\), and Taylor shift \(m\), the one-variable Mellin denominator has the form
\[
h+m+1-2k\mu.
\]
Consequently the candidate resonance condition is
\[
2k\mu=h+1+m,\qquad m\in\mathbb N.
\]

This agrees with `Resonates` and with the convention
\[
|\det D\pi|=|b|\prod_j |u_j|^{h_j}.
\]
On sectors, the signs are absorbed into the smooth factors and coordinate choices.

Two qualifications:

- This is **candidate resonance**, not a guarantee of a nonzero coefficient or an actual pole. Taylor coefficients, symmetry, and summation can eliminate candidates.
- \(q+1\) resonant directions are necessary for a logarithmic coefficient of degree \(q\), matching the pole-order/log-degree shift.

Restricting intrinsic pairs to \(k>0\) is appropriate. The new inactive-exponent theorem supplies the stronger geometric fact that inactive directions do not conceal Jacobian vanishing in these boxes.

### (iv) Other headline qualifications

The remaining statements look consistent at signature level, subject to these boundaries:

- **Off-divisor local diffeomorphism** is not global injectivity, a global diffeomorphism, or a covering-space statement.
- **Resonant support is an upper bound**, not equality with the support.
- **Depth bounds logarithmic degree**, but does not guarantee that the maximal permitted logarithmic term occurs.
- `IsLeadingIndex` alone does **not** assert nonvanishing at the designated index; `IsLeadingIndexOne` does.
- The positivity and domination results are **conditional on the leading-index hypotheses**.
- The landed supremum bound is over the prior-relevant locus \(L\), not yet over \(Z_0\).
- Nothing here constructs normal-jet kernels or proves modification-independence of the intrinsic pair data.

The extension from centred boxes to **every point of every even chart box** is especially valuable: `pairs_eq_of_mem_source` is the real bridge from chart invariance to geometry throughout \(U\).

## B. What is worth doing next?

### Recommended scope

**Freeze the structural level-(2) milestone now.** Do not make D7, a hand-built global regression modification, or common-refinement geometry prerequisites for closing it.

If you want one bounded follow-up, my ranking is:

| Item | Recommendation |
|---|---|
| Leading sup bound over \(Z_0\), preferably \(S_{\mu,q}\) | Best immediate value/cost |
| D3b continuity on \(U\) | Best next foundational theorem if the paper says “distribution” |
| Scalar coefficient independence for downstairs observables | Check for a cheap uniqueness corollary |
| Riesz representation of the leading functional | Optional clean endpoint |
| Leading-index/RLCT nonvanishing criterion | Valuable separate extension |
| Full \(x^2y^2\) modification regression | Useful, but not a closure requirement |
| D7 kernels | Defer |
| Geometric comparison through common refinements | Defer |

### 1. The zero-fibre sup bound is likely cheaper than “D8b” suggests

Separate the bound from Riesz representation.

For a leading functional \(\mathcal T\), germ locality and the existing domination estimate should give
\[
|\mathcal T[G]|
\le
\sup_{P\in S_{\mu_0,q_0}}|G(P)|\,\mathcal T[1],
\]
hence also the weaker \(Z_0\)-sup bound.

The argument does **not** require D3b:

1. Choose \(M>\sup_S|G|\).
2. Choose a smooth bounded scalar function \(\theta\) which is the identity on an interval containing \(G(S)\) and satisfies \(|\theta|\le M\).
3. Then \(\theta\circ G=G\) near \(S\).
4. Apply germ congruence and the existing global bound to \(\theta\circ G\).
5. Let \(M\) decrease to \(\sup_S|G|\).

This uses smooth saturation, compactness, and elementary order limits, rather than chartwise derivative estimates. **I would try this first.**

It also marks a genuine distinction: general coefficients can depend on normal jets; this leading coefficient is bounded by values on its compact support set.

### 2. D3b is the right final infrastructure task

If the intended paper calls all \(\mathcal T_{\mu,q}^U\) **distributions**, D3b is worth doing. It promotes the current geometric locality theorem to a statement about continuous linear functionals.

Aim for a finite chartwise seminorm estimate:
\[
|\mathcal T_{\mu,q}[F]|
\le C\sum_{a}\max_{|\alpha|\le M}
\sup_{K_a}\left|\partial^\alpha(F\circ\phi_a^{-1})\right|.
\]
Specify the topology and compact chart sets explicitly. Pullbacks involving fixed partitions, Jacobian units, and prior factors must be included in the continuity argument.

If that packaging starts expanding into a new manifold-function-space API, stop at the explicit seminorm bound and state its analytic continuity consequence carefully. D3b is not needed to justify the already landed germ assertions.

### 3. Riesz becomes natural after the compact sup bound

The compact sup bound lets the leading functional descend to restrictions of smooth functions on \(S\). Density of smooth restrictions in \(C(S)\), followed by extension and Riesz representation, then gives a finite positive measure supported there.

That is a clean mathematical endpoint, but its Lean cost may lie in the density/extension interface rather than asymptotics. Keep it separate from the inexpensive sup-bound target.

### 4. Resolution-independence has a cheaper scalar version

A common refinement is **not automatically necessary** to prove independence of scalar expansion coefficients.

For a downstairs observable \(f\), if two modifications both transport their resolved integrals to the same original integral, then uniqueness of the asymptotic expansion identifies their coefficients. One needs compatible remainder orders and the appropriate local finiteness or finite truncation of the two spectra.

Thus distinguish:

- **Coefficient independence for pullbacks of the same downstairs observable:** potentially a short corollary of transport and expansion uniqueness.
- **Comparison of arbitrary observables on different resolved manifolds:** requires a compatibility notion.
- **Geometric comparison of pair data, strata, or kernels:** genuinely a different, larger project.

This is worth checking before assigning all “resolution-independence” work an XL estimate. The fixed-\(U\) pair multiset itself should not be advertised as invariant under further blowups.

### 5. Leading index and RLCT: positive prior helps, but “some zero point” is insufficient for a specified index

The natural local candidate is
\[
\lambda_P=\min_{j\in\mathrm{active}(P)}
\frac{h_j+1}{2k_j},
\qquad
m_P=\#\left\{j:\frac{h_j+1}{2k_j}=\lambda_P\right\},
\]
with expected logarithmic degree \(m_P-1\).

A useful sufficient condition is:

> A point realizing the proposed global extremal pair \((\lambda_*,m_*)\) has strictly positive transported prior density, while the expansion already rules out all preceding indices.

Positivity at **some** zero point does not identify an arbitrarily proposed first index: another part of the prior-relevant zero fibre may dominate, or the chart realizing the smallest formal candidate may have vanishing prior.

I would prove nonvanishing by a **positive box lower bound**, rather than by positivity of every engine face coefficient. A lower bound
\[
Z_N[1]\ge c\,N^{-\lambda_*}(\log N)^{m_*-1}
\]
combined with the normalized-limit theorem and preceding vanishing forces the target coefficient to be positive. This avoids cancellation bookkeeping inside the coefficient formula.

That is a worthwhile RLCT bridge, but it is a new nonvanishing lemma, not something supplied by the current conditional leading theorems.

### 6. Regression and kernels

For \(x^2y^2\), first add inexpensive engine or local-data regressions:
\[
(k_1,h_1)=(k_2,h_2)=(1,0),\qquad
\lambda=\tfrac12,\quad q=1
\]
at the crossing, with depth one along either punctured axis. These test conventions without requiring an entire global `WatanabeModificationOn`.

Keep D7 deferred. Normal-jet presentations add substantial structure beyond the support/locality statement and are not demanded by “express this in terms of resolution data and the stratification.”

**Nothing essential to that quoted request remains missing.** The missing items concern continuity, representation, nonvanishing, and comparison—not the promised intrinsic resolved description.

## C. Paper paragraph — ten sentences

> Fix a Watanabe modification and nonnegative phase, and work on its resolved manifold \(U\). The theorem `pairData_eq_of_centered`, together with `pairs_eq_pairData`, makes the multiset of active phase–Jacobian exponent pairs independent of the centred even chart, while `pairs_eq_of_mem_source` computes it at every point of any such chart from the coordinate walls through that point. Its cardinality defines the depth, and, assuming continuity of the phase, `isClosed_depthGE` proves that the depth superlevel sets are closed. The theorem `mem_depthGE_iff_of_centered`, together with the local upper bound on depth, identifies each exact-depth stratum locally with a coordinate subspace in a chart centred on that stratum. For an exponent \(\mu\), the resonance count retains those pairs \((k,h)\) for which \(2k\mu=h+1+m\) for some nonnegative integer \(m\), and `isClosed_resonanceGE` gives the corresponding closed filtration. The theorem `coeff_eq_zero_of_eventually_zero_resonant` shows that the coefficient \(\mathcal T_{\mu,q}^U\) vanishes whenever the observable vanishes on a neighbourhood of the compact set \(Z_0\cap\{r_\mu\ge q+1\}\). Equivalently, `coeff_congr_of_eventuallyEq_resonant` states that this coefficient depends only on the observable’s germ near that set, giving its asserted support bound. The weaker depth-locality statement and `coeff_eq_zero_of_tsupport_subset_shallowOpen` show that observables supported in depth at most \(c\) contribute no logarithmic degrees \(q\ge c\). For leading terms, `tendsto_normalised_of_leading` extracts the coefficient as a normalized integral limit, and `isLeadingIndex_of_one` promotes a first nonzero coefficient of the constant observable to a leading index for all smooth observables. Finally, `coeff_one_pos_of_leading_one`, `coeff_nonneg_of_leading_one`, and `abs_coeff_le_of_leading_one` give conditional positivity and supremum domination for that leading functional on the prior-relevant locus.

### Non-claims to list

- No bundled submanifold or Whitney-stratification theorem; exact strata are not claimed to be closed.
- No invariance of exponent-pair data under changing the modification.
- No continuous-distribution assertion for general coefficients until continuity is supplied.
- No pointwise-zero-on-\(Z_0\) vanishing theorem for general coefficients; the landed hypothesis is neighbourhood vanishing.
- No equality between the resonant upper support bound and actual support.
- No guarantee that candidate resonances or maximal allowed logarithmic degrees occur.
- No normal-jet/kernel presentation.
- No landed \(Z_0\)-sup bound or Riesz measure representation.
- No unconditional existence or identification of `IsLeadingIndexOne`, and no general RLCT nonvanishing theorem.
- No general comparison theorem for arbitrary observables on different resolutions.
