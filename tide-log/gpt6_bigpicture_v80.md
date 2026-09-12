## Recommendation

**Finish R1, but do not make lower-dimensional signed-box measure theory a prerequisite.** Make the projected orthant formula the canonical coefficient theorem, and treat its geometric signed-face presentation as a separate identity.

My ranking is:

| Rank | Item | Reason |
|---|---|---|
| 1 | **R1: residual-face coefficients + unequal-exponent example** | Closes the remaining P3 case using established asymptotics. The example tests genuinely new behaviour rather than just packaging. |
| 2 | **R7: fidelity review** | The posterior theorem is now substantial enough to need a precise scope statement. Run a light gate immediately; consolidate after R1. |
| 3 | **R2: normal-dependent phase unit** | The main local analytic obstruction to using general resolution charts. |
| 4 | **R3: regular supplied weights** | A second, independent obstruction to the resolution bridge. It belongs before R4 implementation, not after it. |
| 5 | **R4: resolution-to-product-cover bridge** | High ultimate payoff, but currently a dependency audit/design task, not a realistic single implementation unit. |
| 6 | **R6: subleading posterior terms** | Useful, but scalar-unit expansions must precede quotient bookkeeping. Lower leverage than removing the local restrictions. |
| 7 | **R5: empirical transfer** | Important for fidelity, but not a routine consequence of the population coefficient theorem or equality of exponents. It needs its own probabilistic programme. |

Thus I agree with your prior through **R1 → R7 → R2**, but would replace the last arrow by **R2 + R3 → R4**.

### A five-unit programme

1. **Residual orthant coefficient theorem**, including minimal-reflection reduction.
2. **Unequal-exponent one-chart example** \(K=x^2y^4\), preferably with one posterior observable.
3. **Fidelity consolidation** for CCXLI–the new modules.
4. **Normal-dependent unit: first local analytic theorem**, with an explicit route toward the residual-face case.
5. **Supplied-weight interface and overlap obstruction audit**; finish with a concrete R4 dependency statement.

For only three units, stop after unit 3. For four, add the local R2 theorem. Do not count “unconditional analytic posterior theorem” as the fifth unit.

---

## Q2. R1 contracts and the cheaper route

### 1. Keep the projected orthant formula as the primary formula

Yes: **your proposed cheaper route is the right one**. The library already has a mathematically meaningful residual-face integral. It is not necessary to replace it immediately by an integral over a coordinate subtype.

Here is the contract I would use, suppressing chart reindexing.

For a tied piece \(I\), put
\[
M=\{a\in I:\operatorname{ratioExp}(a)=\lambda\},\qquad
L=I\setminus M,\qquad m=|M|,
\]
and write
\[
\alpha_a=h_a-2k_a\lambda,\qquad
s=\sum_{a\in L}(\alpha_a+1).
\]
Then \(m\ge1\), \(\alpha_a=-1\) on \(M\), and \(\alpha_a>-1\) on \(L\).

With the phase factor and base density left outside, the orthant-summed coefficient has the form
\[
C_M\int_B \beta(z)q(z)^{-\lambda}\,
 b^s
 \sum_{\sigma\in\{\pm1\}^{I}}
 \int_{(0,1]^I}
 A\!\left(z,\operatorname{reflect}_{\sigma}
                  (b\,\operatorname{faceProj}u)\right)
 \prod_{a\in L}u_a^{\alpha_a}\,du\,dz,
\]
where
\[
C_M=\frac{\Gamma(\lambda)}{(m-1)!}
       \prod_{a\in M}\frac1{e_a},
\qquad e_a=2k_a.
\]

This is already an explicit residual-face formula: the amplitude is evaluated on the minimal face, and the nonminimal singular weight is displayed.

**Important:** the denominator product is over \(M\), not over all of \(I\). The existing all-minimal theorem conceals this distinction because there \(M=I\).

### 2. Suggested module: `ProductChartResidualFace`

Its public contracts should be approximately:

#### A. Residual exponent and scaling identities

- `residualExponent_gt_neg_one`
- `boxScaleExponent_eq_sum_residual`
- `minimalSet_nonempty_of_tied`

The scaling identity is
\[
\sum_{a\in I}h_a+|I|
 -2\lambda\sum_{a\in I}k_a
 =
\sum_{a\in L}(h_a-2k_a\lambda+1).
\]

Use cardinality-based statements at this interface rather than exposing the kernel’s `n + 1` indexing conventions.

These lemmas should isolate all the arithmetic needed later, including conversion between `e` and `2*k`.

#### B. Reflection reduction

Prove pointwise that reflections on \(M\) have no effect after `faceProj`. Then prove the finite-sum identity
\[
\sum_{\sigma\in\{\pm1\}^{I}} f(\sigma|_L)
 =
2^{|M|}\sum_{\tau\in\{\pm1\}^{L}}f(\tau).
\]

This is **finite combinatorics**, not coordinate-splitting measure theory. It can use an equivalence between sign assignments on \(I\) and pairs of assignments on \(M,L\).

Do **not** strengthen it to a factor \(2^{|I|}\) times one orthant integral. That only works when there are no residual sign choices, or when additional reflection symmetry of the amplitude is supplied.

#### C. Expanded cell and tied-piece coefficients

- An identity expanding `boxFaceCoeff` into \(C_M b^s\) times the projected unit-box integral.
- An identity expanding the tied reflection sum and extracting \(2^{|M|}\).
- A global extremal coefficient theorem obtained by rewriting `productCoeffD_extremal_eq_sum_tied`.

Reuse:

- `amplitudeCoeff`, `faceLeadConst`, `faceProj`, `residualWeight`;
- the existing cell coefficient expansion;
- `tied_iff`;
- `productCoeffD_extremal_eq_sum_tied`;
- `prod_normalHalfExp_inv`, suitably restricted to the actual minimal set.

There should be **no new asymptotic proof** here. This unit is coefficient identification.

### 3. A useful intermediate signed-box identity without coordinate splitting

There is an additional cheap route using your existing full-box symmetrisation.

Define
\[
g_z(v)=A(z,\operatorname{zero}_M v)
        \prod_{a\in L}|v_a|^{\alpha_a}.
\]
Then the orthant expression above can be written
\[
C_M b^{-|M|}
  \int_B\beta(z)q(z)^{-\lambda}
     \int_{[-b,b]^I}g_z(v)\,dv\,dz.
\]

The factor \(b^{-|M|}\) is essential. Indeed, full-dimensional dilation contributes
\[
b^{|I|+\sum_{L}\alpha_a}=b^{|M|+s},
\]
whereas the original coefficient carries \(b^s\).

This identity uses:

1. full-box symmetrisation;
2. full-dimensional scalar dilation;
3. the scaling identity above.

It does **not** require splitting the measure into \(M\)- and \(L\)-coordinates.

You can therefore offer three presentations:

- canonical projected orthant formula;
- full-dimensional signed-box formula with \(b^{-|M|}\);
- later, genuine lower-dimensional signed-face formula.

The last is
\[
2^{|M|}C_M
\int_B\beta(z)q(z)^{-\lambda}
 \int_{[-b,b]^L}
 A(z,\operatorname{insertZero}_M v)
 \prod_{a\in L}|v_a|^{\alpha_a}\,dv\,dz.
\]

Here the remaining identity is exactly integration of the dummy \(M\)-coordinates, whose volume is \((2b)^{|M|}\).

**Naming gate:** do not call the full-dimensional auxiliary integral “volume on the face” without explaining the normalization. The actual face has ambient Lebesgue measure zero when \(M\ne\varnothing\).

### 4. Integrability pitfalls

For signed observables, finite-sum and iterated-integral rewrites need actual integrability hypotheses or derived lemmas—not just measurability.

The intended proof is standard:

- continuous amplitude bounded on the relevant compact box;
- \(\alpha_a>-1\) on residual coordinates;
- one-dimensional integrability of \(t^{\alpha_a}\);
- finite-product integrability.

At zero, Lean’s totalised `Real.rpow` need not encode the intended infinite singular value. That is harmless **a.e.**, but endpoints should be handled explicitly in the identity library.

Also keep the base phase \(q(z)^{-\lambda}\) and its existing integrability/boundedness evidence intact. Do not silently derive base integrability merely from residual-coordinate integrability.

### 5. The \(x^2y^4\) regression example

Your correction is right:
\[
\lambda_*=\tfrac14,\qquad M=\{y\},\qquad k_*=0.
\]

For Lebesgue measure on \([-1,1]^2\), the predicted theorem is
\[
\boxed{\displaystyle
\int_{[-1,1]^2}e^{-Nx^2y^4}\,dx\,dy
\sim 2\Gamma(\tfrac14)\,N^{-1/4}.}
\]

The signed-face calculation is
\[
2\frac{\Gamma(1/4)}4
 \int_{-1}^{1}|x|^{-1/2}\,dx
=
\frac{\Gamma(1/4)}2\cdot4
=
2\Gamma(1/4).
\]

This is a much better R1 regression test than another all-minimal example.

Two implementation cautions:

- With a general cutoff, account for both tied strata \(\{y\}\) and \(\{x,y\}\). Their separate contributions may depend on the cutoff.
- With cutoff equal to the box radius, some outer pieces may disappear or become null. If you exploit this shortcut, still retain a theorem showing that the global formula includes all tied strata correctly.

A particularly useful posterior check is
\[
E_N[x^2]\longrightarrow \frac15.
\]
The limiting residual-face density is proportional to \(|x|^{-1/2}\), so
\[
\frac{\int_{-1}^1x^2|x|^{-1/2}\,dx}
     {\int_{-1}^1|x|^{-1/2}\,dx}
=\frac15.
\]
Optionally add \(E_N[y^2]\to0\), which exercises a vanishing numerator coefficient.

---

## What R2, R3 and R4 should actually promise

### R2: freeze the phase on the **minimal face**, not necessarily at the full origin

For a general positive normal-dependent unit, the anticipated leading density contains
\[
u(z,\operatorname{insertZero}_M v_L)^{-\lambda}.
\]

It generally does **not** contain merely \(u(z,0_I)^{-\lambda}\). Nonminimal coordinates remain integrated in the leading coefficient.

This is a crucial design point. A theorem that freezes all active coordinates would be wrong in the residual case.

A manageable first R2 unit is:

- positive continuous unit on a compact product neighbourhood;
- uniform positive lower bound;
- all-minimal leading asymptotic with parameters;
- signed continuous amplitude;
- coefficient obtained by evaluating the unit on the minimal face.

Then extend to residual directions using their integrable singular weights. Alternatively, attack the general minimal-face theorem directly if the existing estimates already support it.

Avoid assuming that a root-coordinate change solves everything: it generally turns product boxes into nonproduct domains, reintroducing boundary and cutoff work.

### R3: supplied regular weights

The clean interface should expose nonnegative regular weights whose sum is one on the covered integration region, with chartwise pullbacks entering the amplitude.

An amplitude-absorbing implementation is attractive if it avoids duplicating `ResolutionCover`. The interface still needs to record:

- the reconstruction identity for the global integral;
- required pullback continuity/measurability;
- support/subordination conditions;
- positivity/nonvanishing conditions used for the denominator.

Counting weights should remain a special case where their regularity or factorisation is actually available.

### R4: realistic deliverable

Initially prove a theorem of the form:

> A resolution with a finite subordinate product-box refinement, suitable regular weights, and the required local monomial/unit/Jacobian data produces an admissible analytic cover.

Then audit which hypotheses follow from the existing Hironaka API.

Shrinking boxes alone does not discharge:

- phase dependence;
- overlap-weight regularity;
- global integral reconstruction;
- treatment of uncovered or zero-free regions;
- compactness/properness or other finiteness assumptions;
- positivity of the leading normaliser coefficient.

“Unconditional for analytic \(K\ge0\)” must still specify the domain, prior, integrability and geometric setting. Analytic nonnegativity by itself is not enough.

---

## Q3. Audit of the supplied statements

**I see no mathematical contradiction in the displayed completed statements.** This is a statement-level audit, not verification of omitted section parameters, definitions or the truncated theorem.

### `tendsto_div_same_pair`

Correct with a possibly zero numerator coefficient, provided `HasLeadingTerm` means convergence after normalization, rather than equivalence to a necessarily nonzero comparison function.

The denominator coefficient only needs to be nonzero for the quotient limit. Positivity is appropriately stronger in the posterior theorem.

Keep a separate check on `div_isEquivalent`: equivalence to a zero leading comparison is not the same assertion as a normalized limit of zero. Its coefficient hypotheses matter.

### Totalised posterior expectation

Mathematically sound as an API choice. The theorem supplies eventual positive denominator, so totalisation does not affect the limit.

The mirror remark should nevertheless say:

> Defined as a totalised quotient for all real \(N\); it is a normalized expectation where the normaliser is positive and the underlying weight is nonnegative.

Do not advertise positivity for every \(N\) from an eventual-positivity theorem.

### `tied_iff` and natural subtraction

The statement is fine **if the proof uses positivity of `pieceMult` before cancelling natural subtraction**.

The unsafe inference would be
\[
m-1=k\implies m=k+1
\]
without \(m\ge1\): it fails at \(m=k=0\).

Here the left-hand condition `pieceLam = coverLam`, together with a nonempty piece and attainment of its finite minimum, supplies a nonempty minimising set. Thus `pieceMult ≥ 1` is available. On the right, `card M = coverDeg + 1` directly supplies nonemptiness.

I would expose and reuse:

- `one_le_pieceMult`;
- `pieceMult_sub_one_eq_iff`.

That makes this corner auditable rather than buried in `omega`.

### `productCoeffD_extremal_eq_sum_minimal`

The hypothesis has the right scope:

- only charts with \(|M_i|=k_*+1\) can contribute at the extremal pair;
- requiring \(M_i=\operatorname{supp}e_i\) for those charts forces every contributing piece to equal \(M_i\);
- other charts contribute zero at that pair.

“Attaining charts” should mean **attaining both the exponent and maximal logarithmic degree**, not merely containing a coordinate of ratio \(\lambda_*\).

This is a restricted all-minimal formula, not the general residual formula.

### Zero-dimensional base and \(\sqrt\pi\)

Correct. The finite product Lebesgue measure on `Fin 0 → ℝ` has mass one on its singleton universe. There is no missing factor from the base.

The coefficient checks:
\[
2^2\frac{\Gamma(1/2)}{1!}\frac1{2\cdot2}
=\sqrt\pi.
\]
The logarithmic degree is \(2-1=1\). The stated asymptotic is consistent.

### “Intrinsic coefficient”

Your cutoff-independence and linearity theorems establish useful intrinsicness. Be precise about its extent:

- independent of cutoff within the stated admissible setup;
- linear in the observable;
- identified by the leading normalized limit.

Independence under changing the entire cover/chart system requires comparing two certificates for the **same global integral and same asymptotic scale**. It is plausible via uniqueness, but is not literally the displayed cutoff theorem.

---

## Fidelity gate: the most important remaining distinction

The current posterior result is a **deterministic Gibbs/population leading-limit theorem** under product-chart, weight-factorisation and positive-face hypotheses. It is not yet the full empirical posterior expansion in the paper.

In particular, R5 should not be framed as “same empirical exponent, therefore same posterior coefficient ratio.” Equality of exponents does not identify leading coefficients or posterior limits.

Even ordinary uniform convergence \(L_n\to K\) is insufficient for that argument: the exponent contains \(n(L_n-K)\). A perturbation theorem based on
\[
n\|L_n-K\|_\infty\to0
\]
would be sufficient in an appropriate setting, but is usually far stronger than statistical fluctuation scales provide. Random leading weights may survive, especially along singular strata.

The fidelity review should therefore distinguish:

1. deterministic leading asymptotics;
2. explicit deterministic coefficient ratios;
3. empirical stochastic transfer;
4. subleading or full expectation expansions.

**Bottom line:** land the residual formula in the representation your library already supports, test \(2\Gamma(1/4)\) and preferably the posterior limit \(1/5\), then remove the two independent chart restrictions—phase dependence and overlap weights—before promising the resolution bridge.
