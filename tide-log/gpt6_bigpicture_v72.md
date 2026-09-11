**My recommendation: do not make general rectilinearisation the next milestone. Prove a genuine single-chart region expansion, then finite exact-localisation gluing.** This gives the paper a regional expansion theorem—not merely an exponent theorem—while keeping the remaining geometric obligation explicit.

Also, distinguish two problems that need not have the same solution:

- **Hard-region localisation:** the pulled-back indicator of the region can be nonsmooth. This is where your cross-chart/boundary gate remains serious.
- **Smooth localisation:** a partition of unity upstairs can remove chart overlap exactly. If your local theorem accepts the resulting smooth amplitudes, subanalytic rectilinearisation may be unnecessary for this version of the paper’s theorem.

I cannot verify theorem signatures or Mathlib API names against the repository here. The recommendations below are at the mathematical/interface level, with API families to inspect.

## 1. Ranking the targets

### First: a single-chart region expansion, followed by exact finite gluing

A useful single-chart hypothesis is substantially stronger than “one chart covers the region a.e.” It should assert:

1. A source domain \(D\) of precisely the type supported by the local expansion theorem.
2. A chart map \(\pi:D\to\Omega\), injective off the certified negligible set.
3. Coverage of \(\Omega\) up to a target-null set.
4. The appropriate change-of-variables identity, including the Jacobian.
5. The pulled-back observable/Jacobian unit belongs to the local theorem’s datum class.

Then
\[
\int_\Omega \varphi(w)e^{-NK(w)}\,dw
=
\int_D (\varphi\circ\pi)(x)J_\pi(x)e^{-N(K\circ\pi)(x)}\,dx
\]
is an **exact identity**, and the regional expansion is the local expansion.

That is a good bounded milestone. It is conditional geometry, but a real theorem about a region integral. It should include at least one actual instantiation, rather than merely introducing another interface equivalent to the missing bridge.

The natural next generalisation is a **finite exact weighted decomposition**, not an overlap estimate. If weights upstairs satisfy
\[
\sum_p \pi_{p*}\bigl(\eta_p J_p\,dx\bigr)
=
1_\Omega\,dw,
\]
and each weighted datum is locally admissible, then expansions and coefficients add exactly.

**Important possible shortcut:** if the paper’s integral already has a smooth compactly supported localisation, try a partition of unity on the resolved space. Overlapping chart images are then harmless. The remaining obligations are compactness/finite coverage, smooth cutoff construction, and closure of your datum class under multiplication by those cutoffs. That is different from rectilinearising a hard region.

### Second: leading coefficients under exact localisation

Once you have exact gluing, the leading-coefficient theorem is inexpensive.

Order the pairs by
\[
(\lambda_p,m_p)\prec(\lambda_q,m_q)
\quad\Longleftrightarrow\quad
\lambda_p<\lambda_q
\ \text{or}\ 
\lambda_p=\lambda_q,\ m_p>m_q.
\]
For finitely many pieces,
\[
\lambda_*=\min_p\lambda_p,\qquad
m_*=\max_{\lambda_p=\lambda_*}m_p.
\]
If
\[
N^{\lambda_p}(\log N)^{1-m_p}I_p(N)\longrightarrow c_p,
\]
then exact gluing gives
\[
N^{\lambda_*}(\log N)^{1-m_*}Z_\Omega(N)
\longrightarrow
\sum_{\substack{\lambda_p=\lambda_*\\m_p=m_*}}c_p.
\]

Here the \(c_p\) must be coefficients of the **actual weighted pieces**. They are not invariant numbers attached to divisor points independently of the chosen localisation.

Your proposed disjointness condition needs strengthening:

> A.e.-disjoint images of the extremal pieces alone do not suffice.

You also need the remaining region to be negligible at the extremal scale, or an exact decomposition of the entire integral into those pieces and certified subdominant pieces.

Cheap sufficient conditions are:

- all pieces cover the region a.e.;
- their target images are pairwise a.e. disjoint;
- every piece has a certified local expansion.

Alternatively, exact weights summing to one are enough; disjointness is unnecessary.

On a genuine resolution that is an isomorphism off the exceptional locus, disjoint subsets **of the resolved space** have disjoint target images off that locus. Thus different coordinate charts are not intrinsically the problem: independently chosen, overlapping chart neighbourhoods are.

### Third: statistical consequences at the order/centering level

The identified pair can discharge the **exponent-identification component** of a statistical interface. It cannot generally discharge a localisation identity or coefficient-level expansion.

Split `CompatibleDivisorLocalisation`, if practical, into obligations such as:

- exponent pair agreement;
- leading normalised limit;
- full deterministic expansion;
- convergence/control of sample data;
- uniform integrability or moment bounds.

CCIX/CCIX-b can supply the first. They may identify the exponents in an independently established second. They do not manufacture the others.

There is, however, a useful stronger consequence than the logarithmic slope you listed. If
\[
A_n=n^{\lambda_*}(\log n)^{1-m_*},
\qquad A_nZ_n^{\rm emp}\Rightarrow L,
\]
where \(L\) is finite and strictly positive a.s., then
\[
-\log Z_n^{\rm emp}
-\lambda_*\log n
+(m_*-1)\log\log n
\Rightarrow -\log L.
\]
In particular, the centred free energy is \(O_{\mathbb P}(1)\).

That is worth exposing as a paper-facing theorem. It does **not** establish Gaussianity of \(\log L\).

Nor does weak convergence supply annealed asymptotics. For example, \(W_n=1\) with probability \(1-1/n\), and \(W_n=n^3\) otherwise, satisfies \(W_n\Rightarrow1\) while \(\mathbb EW_n\asymp n^2\). Expectations, log-expectations, and inverse moments need their respective additional controls.

### Fourth: small-ball and intrinsic-invariant corollaries

These are cheap enough to do immediately, despite being lower-ranked as research targets:

- every sufficiently small ball has the identified pair;
- weighted small balls have the same pair for strictly positive continuous weights locally bounded above and below;
- resolution independence, stated explicitly for two admissible resolutions;
- \(\lambda_*>0\), \(\lambda_*\in\mathbb Q\), and \(1\le m_*\le d\), where supported by your divisor data.

The rationality/dimension statements make the “RLCT” interpretation particularly clear.

For your coefficient lower bound, state a **liminf theorem**, not a coefficient-existence theorem:
\[
I_{\rm piece}(N)\le Z_{B_r}(N),\qquad
A_N I_{\rm piece}(N)\to c_{\rm piece}
\quad\Longrightarrow\quad
c_{\rm piece}\le\liminf_N A_NZ_{B_r}(N).
\]
If the ball’s normalised limit later exists, this becomes the desired coefficient bound. The piece must lie inside that ball, and its coefficient may change when you shrink it.

### Last: the unrestricted hard-region expansion

I would not budget general subanalytic rectilinearisation as a ten-unit target.

Also, “sum the charts and show overlap is lower order” is **not a default escape hatch**. Two copies of the same chart already double the leading term. Distinct overlapping charts can overlap along the dominant divisor contribution, so their overlap has exactly the leading order.

An overlap-error theorem is valid with a certified subdominant-overlap hypothesis, but proving that hypothesis may be the original geometric problem.

## 2. First three Lean-level statements for the top target

I would separate transport, expansion, and gluing.

### Statement 1 — exact transport for a single-chart region

A schematic interface:

```lean
SingleChartRegionData K Ω D π J
```

should carry the geometric/change-of-variables facts, with the existing local chart data attached separately.

Its first theorem should say:

```lean
singleChartRegion_integral_eq
```

**Hypotheses**

- measurability of the relevant sets and maps;
- certified chart change of variables;
- a.e. coverage and a.e. injectivity as required by that theorem;
- integrability of the target and source integrands.

**Conclusion**, for each relevant \(N\):
\[
Z_\Omega[\varphi](N)=I_D[\varphi\circ\pi,J](N).
\]

A particularly clean measure-level formulation is
\[
\mathrm{volume}\!\restriction_\Omega
=
\mathrm{map}\,\pi\bigl((\mathrm{volume}\!\restriction_D)
                     .\mathrm{withDensity}\,J\bigr),
\]
with \(J\) interpreted as an `ℝ≥0∞` density. This isolates geometry from every subsequent observable theorem.

**Mathlib/API to use**

- `Measure.restrict`, `Measure.map`, `Measure.withDensity`;
- the `integral_map` and `integral_withDensity` API;
- a.e. congruence of integrals;
- your already-certified split-box change-of-variables theorem.

**Hazards**

- Source-null exceptional sets are not automatically target-null under arbitrary maps. Reuse the established chart theorem.
- A.e. coverage without multiplicity control is insufficient.
- “The chart covers \(\Omega\)” does not imply that its source domain is a box. Require the actual domain identification.
- Do not try to apply `integral_map` as though it proves change of variables: the pushforward measure identity is the geometric content.

### Statement 2 — single-chart region expansion with explicit coefficients

```lean
singleChartRegion_hasExpansion
```

**Hypotheses**

- `SingleChartRegionData`;
- \(K\circ\pi\) has your certified local monomial form;
- the pulled-back weighted observable defines admissible local Taylor data;
- the hypotheses of the existing local expansion theorem.

**Conclusion**

The regional integral has the local power–log expansion, and its coefficients are the existing local face-integral coefficients.

For each supported truncation level \(B\), schematically:
\[
Z_\Omega[\varphi](N)
=
\sum_{(\lambda,j)\in S_B}
c_{\lambda,j}\,N^{-\lambda}(\log N)^j
+R_B(N),
\]
with exactly the remainder assertion your local theorem provides.

Do not strengthen the remainder while transporting it.

**Mathlib/API to use**

Mostly equality rewriting and your existing expansion theorem. Depending on representation, inspect `Asymptotics.IsLittleO`, `IsBigO`, and their congruence/transport lemmas.

**Hazards**

- Preserve the distinction between log degree \(j\) and pole multiplicity \(m=j+1\).
- A signed smooth observable can annihilate the nominal leading coefficient. Full expansion transports, but the actual leading pair need not equal the positive-weight RLCT pair.
- Multiplication by a smooth cutoff must be certified in your datum class. If that class requires analyticity or a convergent full Taylor representation, smooth partition-of-unity localisation is not automatic.

### Statement 3 — finite exact localisation glues expansions and leading coefficients

```lean
finite_localisation_hasExpansion
```

**Hypotheses**

- a finite index type;
- an exact integral identity
  \[
  Z(N)=\sum_p I_p(N),
  \]
  preferably derived from a finite pushforward-measure decomposition;
- a certified expansion for every \(I_p\).

**Conclusions**

1. The global coefficient at each exponent/log degree is the sum of the local coefficients at that same exponent/log degree.
2. The finite sum has the corresponding expansion.
3. Under local leading-limit hypotheses, the global normalised limit is the sum over extremal pairs displayed above.

For positive partition weights and a positive observable, prove positivity of that sum when at least one extremal piece has positive leading coefficient.

**Mathlib/API to use**

- finite-sum integral lemmas (`integral_finset_sum` family, with integrability obligations);
- finite-sum limit lemmas (`Filter.Tendsto`/`Finset` sum API);
- finite-sum closure for little-\(o\) or big-\(O\);
- your existing power–log dominance lemmas.

**Hazards**

- Equal exponent/log-degree terms must be merged, not concatenated as distinct asymptotic orders.
- For signed observables, cancellation can eliminate the dominant sum.
- Same \(\lambda\), smaller \(m\) is lower order by a logarithm—not by a positive power of \(N\).
- Establish a common truncation/remainder scale before summing.

**Scope discipline:** these three statements are plausibly bounded if you reuse the current local expansion and change-of-variables machinery. Building a general smooth partition-of-unity localisation theorem on the resolved space is a separate task. Do not quietly include it in the estimate.

## 3. What is over-claimed in §1?

Taking your theorem summaries at face value, the core identification looks right. The qualifications are important.

### “Unconditional” needs a precise meaning

If `Q_all` is a proved theorem instantiated without an extra geometric hypothesis, fine. If it remains a premise, the result is **relative to the supplied resolution theorem**. Axiom-clean does not mean premise-free.

What you have certainly removed, on your account, is the extra support/localisation condition previously obstructing the RLCT formula.

### “Independently of region and observable” is too broad

Safe wording is:

> Independent of the admissible resolution and localisation choices, and of strictly positive locally regular weights, within the sufficiently small neighbourhood regime.

It is not independent of:

- arbitrary signed or vanishing observables;
- arbitrary regions, even ones containing \(w\), if they extend to other singularities;
- arbitrary portions of charts that fail to capture the divisor contribution.

### Θ is not a coefficient theorem

You have the power–log order and hence the deterministic free-energy expansion with \(O(1)\) remainder. You do not thereby have convergence of the normalised integral.

Consequently, your small-ball “leading coefficient is bounded below” should presently be stated as the liminf bound above.

### Check multiplicity subtraction at the type boundary

The assertion
\[
m_*-1=\theta_H-1
\]
identifies multiplicities only with the relevant positivity and coercion conventions handled correctly. In particular, natural-number truncated subtraction should not silently replace subtraction in \(\mathbb R\). Expose \(m_*\ge1\) and, ideally, the direct multiplicity equality whenever the types allow it.

---

**Bottom line:** finish the cheap intrinsic-pair/free-energy corollaries, then land a **single-chart region expansion with explicit coefficients and one genuine instantiation**. Generalise it to exact finite weighted localisation. That moves the Lean mirror toward `thm:expectation_expansion` without pretending that Θ supplies coefficients, that chart overlaps are subdominant, or that statistical averaging follows from convergence in distribution alone.
