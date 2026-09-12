## 1. Audit

**Verdict: a substantive, correctly scoped conditional leading-measure theorem has landed—not yet an unconditional coefficient theorem for arbitrary original regions \(W\).** The compact theorem separately gives a more automatic **order-of-growth** result.

Two limits on this audit: the mirror paragraph is missing after its heading, and some declarations are truncated or show only structure names. Thus I can audit the displayed interfaces, but not verify the hidden density formula or enumerate the fields of the certificate structures.

### Prior and coefficient density

The interfaces distinguish the two conventions correctly:

- `globalLaplace W K a` uses the **entire amplitude** \(a\).
- `targetIntegral W F K p` uses amplitude \(F p.w\).
- The general-prior `R.leadingMeasure ... (p := p)` already incorporates the prior through the face density. Its coefficient is therefore
  \[
  \int F\,d\sigma_p,
  \]
  **not** \(\int Fp\,d\sigma_p\).
- The exported `hasLeadingMeasure_of_aeDisjoint` instead constructs \(\sigma_1\), with unit prior, and tests against arbitrary bounded continuous amplitudes.

The explicit coefficient representation is a sum of **weighted face/residual integrals pushed to the target**, schematically
\[
\sum_{\text{tied pieces}}
 \int_{\text{base}}\beta(z)
 \int_{\text{unit box}} B_p(z,u)\,
       \mathrm{residualWeight}(u)\,
       F(\Phi(\mathrm{facePoint}(z,u)))\,du\,dz.
\]
That is genuinely geometric coefficient data. It should not be described as unweighted integration over original strata, or as a canonical Hausdorff measure on those strata.

The dependence on `p` is consistent throughout the displayed bridge. Checking that `faceAmp` includes the pulled-back prior **exactly once** requires its omitted definition.

### What `HasLeadingMeasure` means

For the **finite measures constructed here**, it expresses convergence of normalized Laplace measures against every bounded continuous test:
\[
\frac{\int_W a(x)e^{-tK(x)}\,dx}
     {t^{-\lambda}(\log t)^q}
\longrightarrow \int a\,d\sigma.
\]

This is finite-measure weak convergence—not a full asymptotic expansion, a rate, or convergence against all measurable or unbounded observables. For a zero coefficient it gives only a smaller-order statement; asymptotic equivalence requires the displayed nonvanishing condition.

**Analyticity and global boundedness are different requirements.** An analytic observable need not be globally bounded. Nevertheless, the general-prior theorem
`hasLeadingTerm_targetIntegral_of_aeDisjoint` already handles observables satisfying the stated pullback continuity, measurability, and integrability assumptions. Thus the development is not confined to globally bounded analytic observables.

Alternatively, a compact-localization/cutoff lemma can connect analytic observables to the bounded-continuous API. Such an extension must be justified; it is not part of weak convergence by definition.

Also, the displayed `HasLeadingMeasure` API does not require finiteness of an arbitrary supplied measure. Reserve the weak-convergence interpretation for finite measures; Lean’s totalized integral does not itself establish finiteness.

### Other scope points

- `hne : activeCharts.Nonempty` does **not** establish that the leading measure is nonzero. Nonnegative residual factors can vanish.
- Uniqueness at fixed \((\lambda,q)\) is proved for finite measures. Uniqueness of the pair additionally requires nonzero measures.
- General concentration on \(K^{-1}(0)\) is not established by the displayed support utilities alone: they require an a.e. mapping hypothesis. The cube example supplies its concentration proof explicitly.
- `exponent_of_compact` proves **\(\Theta\)**, not a leading coefficient or leading measure.
- The cube theorem is a concrete calibrated example, with \(d>1\), not evidence that the general geometric hypotheses have been automatically discharged.

### Mirror paragraph

I cannot assess the absent paragraph. A safe replacement would be:

> Given a finite resolution cover with almost-everywhere disjoint chart images and certified product-monomial chart data, we construct a finite leading measure as a sum of pushforwards of weighted face measures over the tied leading pieces. Its integrals give the leading coefficients of the original target integrals, subject to the stated observable and prior hypotheses. For unit prior this yields convergence against all bounded continuous tests. Separately, under analytic positivity and interior-zero hypotheses, a compact-region theorem establishes the leading power–log order without constructing its coefficient.

Avoid claiming that these results automatically construct the leading measure for every analytic problem on the paper’s original \(W\).

## 2. Next direction

**Close the core programme; do not start another hypothesis-heavy route.** Ranked remaining work:

1. **Bounded-open-region corollary: worthwhile.** Assume \(\overline W\subset U\), bounded open \(W\), and no zeros on \(\partial W\), together with the compact theorem’s analytic, positivity, nontrivial-germ, and zero-existence assumptions. Apply `exponent_of_compact` to \(\overline W\); the boundary contribution is exponentially small by a positive gap. **No boundary-volume-zero assumption is needed.** This is a useful bridge to original integration domains, but remains a \(\Theta\) theorem.

2. **General concentration theorem: genuine structural value.** Under finite-volume/measurability assumptions and continuous nonnegative \(K\), derive
   \[
   \sigma\bigl((\overline W\cap K^{-1}(0))^c\bigr)=0
   \]
   for finite `HasLeadingMeasure`. This replaces repeated geometric support arguments where only concentration is needed.

3. **Prior/cutoff compatibility: small API work only.** For a nonnegative bounded continuous prior \(p\), test with \(ap\), and identify the weighted limit with \(p\,\sigma_1\). If both geometric constructions apply, uniqueness identifies \(\sigma_p=p\,\sigma_1\). For locally continuous priors, add justified compact localization. **Arbitrary measurable or unbounded priors do not follow from weak convergence.** The existing general-prior target-integral theorem already does much of the useful work.

4. **`BoxFamily` wrapper:** worthwhile only if it derives a commonly used certificate package and materially simplifies applications. Not a new mathematical milestone.

5. **Ownership partition plus assumed Laplace normal density:** defer. Measurable ownership restrictions can destroy the regularity used by the local asymptotics. Assuming the needed density limit largely relocates the missing analysis. Pursue this only with a concrete derivation for a useful overlapping cover.

## 3. What remains hypothesized

For the **general coefficient/leading-measure construction**:

- A finite `ResolutionCover`, or a `PartialResolution`, including its bundled geometric/change-of-variables requirements.
- Compatible `ProductMonomialChartVar` data for every chart, including their bundled monomialization, domain, and regularity requirements.
- Global measurability and nonnegativity of \(K\).
- A common \(0<\varepsilon\), with \(\varepsilon\le b_i\).
- A nonempty active-chart set.
- Pointwise nonnegativity of each residual factor `r`.
- **A.e. disjoint target chart images.**
- For general prior: the bundled `TubeWeight` requirements and the displayed continuity of its chart pullbacks.
- For general observable: measurability, continuity of chart pullbacks on the specified sets, and integrability of \(Fp.w\) on the image union.
- For an original \(W\) different from that union: a proved a.e. identification, or the locality theorem’s measurable finite-volume sets and positive energy gap on both differences.
- For nonzero leading asymptotic equivalence: nonzero coefficient; positivity/support conditions are sufficient but not automatic.

For **`exponent_of_compact`**: open \(U\), compact \(W\subset U\), analytic \(K,F\) on \(U\), measurable \(K\), \(K\ge0\), \(F>0\), existence of a zero in \(W\), every such zero interior to \(W\), and no locally identically-zero germ there. **Resolution data and local \(\Theta\) estimates are conclusions/internal constructions here, not additional input hypotheses.**

The omitted structure fields are the only obstacle to expanding this into a literally field-by-field hypothesis inventory.
