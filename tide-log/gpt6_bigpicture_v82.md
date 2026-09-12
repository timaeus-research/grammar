**My recommendation: add the abstract leading-atlas interface now, without changing the scalar API; keep the old chart package; and develop the variable-unit path alongside it.** The essential new mathematics is already landed. The remaining risks are geometric positivity, coefficient compatibility, and the precise scope of the product-chart hypotheses—not the finite-sum asymptotics.

## Q1. Atlas interface: (a), as an additive extraction

I would choose **(a), but explicitly not a seven-module refactor**.

Add:
```lean
structure LeadingCell where
  integral : ℝ → ℝ
  coeff : ℝ
  lam : ℝ
  mult : ℕ
  hasLeadingTerm :
    HasLeadingTerm integral coeff lam (mult - 1)

structure FiniteLeadingAtlas (Z : ℝ → ℝ) where
  -- finite index type, cells, and equality for N ≥ 0
```

Preserve the present `mult - 1` convention. Do not introduce positivity, geometry, or nonzero-coefficient requirements into this record: a cell may have zero coefficient.

Then:

1. Add `ScalarUnitCell.toLeading`, `VarUnitCell.toLeading`.
2. Extract `tied` and `hasLeadingTerm_of_extremal` once.
3. Add `FiniteScalarUnitAtlas.toLeading`.
4. Prove `hasLeadingTerm_boltzmannIntegral_of_leadingAtlases'`.
5. Keep the existing scalar theorem, with its existing statement, as a corollary.

The generic atlas needs **no tangential dimension parameter**. Geometry and dimension belong to its concrete producers.

For the variable path, I would still have a small concrete `FiniteVarUnitAtlas t Z`, with `toLeading`, if this is the easiest way to retain the current
```lean
obtain ⟨…, rfl⟩
```
pattern. This is not option (b)’s duplicated asymptotic infrastructure: it is a concrete geometric wrapper with one abstract consumer.

Likewise, positivity and residual-face computations should remain concrete. Do not try to reconstruct `A`, `u`, or reflected cells from `LeadingCell`.

### Why now?

Your stated refactor surface identifies exactly the abstraction boundary: the generic consumer only needs four quantities, a certificate, and an equality. Extracting that boundary now prevents duplicating the coefficient selector, the extremal theorem, and the global assembly theorem.

But **mixing does not force (a)**. Since scalar cells embed into variable cells, even a heterogeneous finite collection can be homogenised to variable cells. Thus (b) is mathematically adequate and a defensible emergency fallback. My preference for (a) is maintainability, not a claim that the variable theorem otherwise cannot be assembled.

Acceptance criterion: **no downstream scalar statement changes, and no example changes**.

---

## Q2. Unit 4 contracts

### (i) Variable normal form: yes

Use
\[
q_{\mathrm{var}}(z,n)
 =u(\Psi(z,n))\,\operatorname{tangentialMonomial}(z),
\]
with the chart-coordinate conventions of the existing scalar theorem.

The theorem should be purely algebraic/geometric and have no `hind` hypothesis. Retain exactly the existing allocation of active coordinates between base and normal variables.

### (ii) Continuity and positivity: yes, with an explicit nonvanishing lemma

The needed package is:

```text
q_var_continuousOn_closedPiece
tangentialMonomial_ne_zero_on_base
q_var_ne_zero_on_closedPiece
q_var_nonneg_on_closedPiece
q_var_pos_on_closedPiece
```

The question mark about the base must become a proved lemma, not an implicit premise. Typically the cutoff construction gives, for each active coordinate assigned to the base,
\[
|z_j|\ge \varepsilon>0.
\]
That is what guarantees the tangential monomial is nonzero. A closed base defined merely by “not zero” would need further justification, especially when taking closures.

The positivity argument is:

1. `u ≠ 0` and the tangential nonvanishing give `q_var ≠ 0` everywhere on the closed piece.
2. At normal points with every coordinate nonzero,
   \[
   \prod_a n_a^{2k_a}>0.
   \]
   Hence `K ≥ 0` and the normal form give `q_var ≥ 0`, and therefore `q_var > 0`.
3. Such normal points are dense in the closed normal box, since its radius is positive.
4. Continuity gives `q_var ≥ 0` at the remaining points; nonvanishing upgrades this to strict positivity.

This proof works separately for each base point and needs **no connectedness assumption**.

**Do not strengthen the package to `u > 0` on `W`.** The conclusion needed is positivity of `q_var` on the piece. It is local, follows from the available geometric hypotheses, and avoids unnecessary sign assumptions outside the chart domain.

In particular, `u ≠ 0` and `K ≥ 0` are sufficient **together with the normal-form identity, tangential nonvanishing, and density inside the region where that identity holds**. They are not, as bare hypotheses, sufficient to conclude `u > 0` on arbitrary `W`. Connectedness of `W` alone does not repair the absence of information relating `K` and `u` there.

### (iii) Piece bridge: yes

Add:

- `varPieceCell`;
- `pieceIntegral_eq_varSymIntegral`;
- `varPieceAtlas`;
- its concrete-to-leading conversion.

The integral bridge should reuse the existing adapted-integral and almost-everywhere box-boundary lemmas. Only the pointwise phase substitution changes.

Keep the equality for `N ≥ 0` if that is the existing assembly contract; no benefit comes from broadening it here.

### (iv) Chart-data existence theorem: yes

Tietze-extend both functions from
\[
S=\text{base}\times\text{closed normal box}.
\]

Require or derive explicitly:

- `S` compact, hence closed;
- continuity of the original amplitude and `q_var` on `S`;
- extension agreement on **all of `S`**, not merely almost everywhere;
- positivity of the extended unit on `S`.

There is no need for the extension to be positive globally. Your landed `VarUnitCell` interface deliberately permits this.

I would add one small but important compatibility API here:

> **Cell integrals and coefficients are independent of the chosen extensions, provided the extensions agree on the closed piece.**

For coefficients, this uses that every reflected projected-face point remains in the closed piece. This will save trouble when comparing numerator and denominator constructions, scalar and variable constructions, and classical-choice atlases.

### (v) Product-chart theorem: yes, but split leading terms from positivity

Use a descriptively named package such as `VariableProductMonomialChart` or `ProductMonomialChartVar`, not a primed public name.

Prove in this order:

1. `exists_varPieceAtlas`;
2. a concrete piece-data predicate and chosen atlas;
3. the global **signed-amplitude leading-term theorem**;
4. nonnegativity of coefficients;
5. positivity of an identified extremal coefficient;
6. the asymptotic-equivalence theorem.

The leading-term theorem itself should **not acquire `F ≥ 0`**. CCLV gives you signed amplitudes; preserve that strength. Nonnegativity and nonvanishing belong to the equivalence/positivity layer.

For nonnegativity, the hypotheses concern both factors:

- nonnegative base weight `βw`;
- nonnegative face amplitude `A`.

In the chart application, derive these from the cover/density hypotheses and `F ≥ 0`; `F ≥ 0` alone is not an abstract cell-level substitute for both.

#### Does the identified-pair argument transfer verbatim?

**The extremal-index selection transfers; the analytic positivity argument transfers after a helper lemma.** I would not promise literal proof reuse.

The new multiplier
\[
u_{\mathrm{face}}^{-\lambda}
\]
is strictly positive on the entire face. On the compact reflected face it also has a positive lower bound. Consequently, if the old positive face amplitude is `A`, then for some `c > 0`,
\[
A\,u_{\mathrm{face}}^{-\lambda}\ge cA
\]
where `A ≥ 0`. Monotonicity reduces positivity to the old coefficient argument.

This is often cleaner than rebuilding “positive continuous integrand on a positive-measure neighbourhood” in each product-chart proof. The signed or merely integrable base weight must still be handled under the same positivity hypotheses as before.

Also preserve the existing hypothesis that makes the selected amplitude genuinely positive. `F ≥ 0` by itself does not ensure a positive extremal coefficient.

### (vi) Posterior: essentially yes

Apply `tendsto_posteriorExpectation_of_hasLeadingTerm` to numerator and denominator with the same extremal pair.

The remaining obligations are:

- numerator measurability/integrability and amplitude regularity;
- denominator coefficient nonzero, normally strictly positive;
- numerator and denominator use the same geometric exponent pair;
- any stated face-ratio formula is compatible with the chosen extensions/atlases.

The numerator may be signed, and its leading coefficient may be zero. No new variable-unit asymptotic estimate is needed.

### Requested order

I approve your three mathematical units, with a small infrastructure prelude:

1. **Prelude:** abstract leading atlas and conversions; preserve scalar statements.
2. **4A:** (i)–(iv), including positivity and extension-independence.
3. **4B:** (v), signed leading term first, then positivity and equivalence.
4. **4C:** (vi) and tied-strata residual formula.

The tied-strata proof should reuse the landed variable reflected-face formulas. The coefficient must retain `u` on the **minimal face with residual coordinates present**, not freeze it at the full stratum foot.

---

## Q3. Keep `unit_indep` in the old package

**Keep `ProductMonomialChart` unchanged.** Add the weaker package and a forgetful map:
```lean
ProductMonomialChart.toVar :
  ProductMonomialChart ... → ProductMonomialChartVar ...
```

Do not use a `Prop`-valued flag. That introduces branching into precisely the interface that should become simpler.

The old examples remain untouched. Later you can make the scalar package an extension of a common core if that proves worthwhile, but it is not part of this programme.

Compatibility should be stated at the useful observational level:

- same piece integral;
- same exponent and multiplicity;
- same coefficient under `unit_indep`.

Do **not** demand equality between independently chosen scalar and variable atlases. Their Tietze extensions may differ away from the closed piece. The extension-independence lemmas are the right tool.

---

## Q4. Regression constants

All three predictions are correct, for **Lebesgue measure, amplitude one, and no prior normalisation**.

### 1. \(K=(1+y^2)x^2y^4\)

The minimal coordinate is `y`, and the face unit is `1`. Thus
\[
c
=4\,\frac{\Gamma(1/4)}4\int_0^1x^{-1/2}\,dx
=2\Gamma(1/4).
\]

Therefore
\[
Z(N)\sim 2\Gamma(1/4)N^{-1/4}.
\]

### 2. \(K=(1+x^2+y^2)x^2y^4\)

The face unit is \(1+x^2\), so
\[
c=\Gamma(1/4)\int_0^1x^{-1/2}(1+x^2)^{-1/4}\,dx.
\]

There is no need to evaluate that integral further. This is the important regression distinguishing **minimal-face freezing** from full-foot freezing.

At `ε = 1`, the additional boundary-base contribution is null under the supplied piece geometry; keep a separate measure-zero lemma rather than identifying the piece with the empty set.

### 3. \(K=x^2y^4z^4\)

Here \(\lambda=1/4\), multiplicity \(2\), hence log power \(1\). On the positive orthant,
\[
c_+
=\frac{\Gamma(1/4)}{16}
  \int_0^1x^{-1/2}\,dx
=\frac{\Gamma(1/4)}8.
\]
Eight orthants give
\[
\boxed{c=\Gamma(1/4)},\qquad
Z(N)\sim\Gamma(1/4)N^{-1/4}\log N.
\]

Your distinction is correct: the full piece is indexed by `{0,1,2}`, but its **minimal coordinate set** is `{1,2}`. Those are different indexing notions.

### Before or after assembly?

**Both, at different levels.**

- Run the three hand-built symmetric-cell regressions now, before product-chart assembly.
- After 4B, prove the one-chart-cover versions through the new headline theorem.
- After 4C, test the residual formula and one posterior example.

This gives an early test of constants without postponing the genuinely valuable end-to-end tests.

---

## Q5. Priority and the remaining resolution-to-package gap

### Priority

My ordering is:

1. **B-small:** direct-cell regressions as immediate smoke tests.
2. **A:** complete 4A–4C.
3. **B-full:** end-to-end cover regressions.
4. **R4 scope/dependency statement**, written while the hypotheses are fresh.
5. **C / R3:** regular supplied cover weights.
6. **D:** subleading/expansion-level results.

I would not insert an unspecified §3–§4 project ahead of these without examining a concrete missing statement. Module and dot counts do not determine coverage.

Also separate **Θ bounds** from **subleading expansions**:

- once positive-coefficient equivalence is available, the corresponding Θ statement is a cheap corollary;
- subleading expansions require substantially more regularity and remainder analysis. They do not follow from the continuous-amplitude, continuous-unit leading-term certificates.

### What resolution does not automatically supply

After A, the unit-normal-independence restriction is gone. But the conclusion is still:

> Leading asymptotics for finite covers equipped with the stated product-chart, density, support, and nonvanishing data.

It is not yet automatically a theorem for every raw monomial resolution chart. Based on the interface you describe, the remaining bridge has these components:

| Product-package requirement | Relation to resolution |
|---|---|
| Monomial phase and Jacobian data, nonvanishing units | Standard resolution output, subject to the chosen resolution theorem’s precise statement |
| Centred product domain `productDom J T b` | Requires shrinking/recentring and refining local charts; not the arbitrary original chart domain |
| Compact inactive base and closed-piece containment in the chart | Requires localisation with margin inside the coordinate neighbourhood |
| One compatible positive cutoff, `ε ≤ b` | A finite-refinement/minimum argument once positive chart margins exist |
| Cover weights factoring through inactive coordinates | **Not supplied by resolution and not generally satisfied by ordinary partitions of unity** |
| Continuous adapted amplitudes with the required factorisation | Requires density regularity and treatment of the cover weights |
| Finite assembly and negligible boundary bookkeeping | Requires compact support/properness/localisation and the cover construction |
| Positive dominant coefficient | Requires support/nonvanishing of the density at a contributing extremal locus, not resolution alone |

The product-domain condition is generally a **local-refinement task**, not an intrinsic obstruction. Near a point, divisor coordinates that vanish there are normal coordinates; divisor coordinates that do not vanish there can be bounded away from zero and absorbed into tangential/unit data. Formalising that refinement and its integral bookkeeping is still real work.

The weight-factorisation restriction is more substantial. R3 should permit a supplied regular chart weight depending on **all coordinates**, absorbed into the continuous amplitude. Merely replacing counting weights by “regular weights” while retaining inactive-coordinate factorisation would not close that gap.

There is also a possible **away-from-zero remainder** obligation: pieces with phase bounded below positively contribute exponentially small terms, provided the weighted amplitude is integrable. If the current cover/tube assembly already handles these, reuse it; otherwise it belongs explicitly in the resolution-to-product bridge.

Finally, positivity determines which geometric strata actually contribute. A density can vanish on all nominally extremal faces. Resolution delivers candidate exponent data; identifying the leading pair for a particular integral additionally needs the existing nonvanishing hypotheses or a support-sensitive selection theorem.

**Suggested scope remark after A:**

> The product-chart asymptotic and posterior theorems allow continuous positive units depending on all normal and tangential coordinates. Their application to general resolution data still requires a finite compatible product refinement, admissible cover-weight/density data, and the stated nonvanishing conditions. Arbitrary supplied regular cover weights and subleading expansions remain outside the present theorem.

That is a substantial removal of a genuine hypothesis, without conflating it with the still-unformalised localisation bridge.
