## Verdict

**u286: PASS. u287: PASS for the authorised conditional leading-order quotient. Overall: A4-L passes the mathematical statement/proof gate.**

No blocking mathematical issue appears in the supplied excerpts. There are **nonblocking documentation corrections**, especially concerning the scaled theorem, the common-phase specialisation, and the meaning of the in-probability remainder comparison.

This review is based on the supplied statements and proofs, with the earlier results treated as frozen; it is not an independent repository build.

## 1. u286 — quotients in distribution

### Statement

`tendstoInDistribution_div` has the right hypotheses and conclusion:

- **Joint** convergence of `(Y i, W i)`, not merely two marginal convergences.
- Measurability of all four real-valued random variables.
- The exact limiting-denominator condition
  \[
  \mu'\{\omega:B(\omega)=0\}=0.
  \]
- Convergence of the laws of the totalised quotients.

The ambient `[l.IsCountablyGenerated]` is a genuine restriction of this implementation, appropriately supplied for the bounded-Lipschitz characterisation. It includes the usual sequence setting.

**Nothing is assumed or concluded about `W i ≠ 0` almost surely at any fixed index.** Totalised division makes the finite-index quotient measurable even on its zero-denominator set.

### Truncation and comparison

For `δ > 0`,
\[
T_\delta(a,b)=\frac{ab}{\max(b^2,\delta^2)}
\]
is globally continuous because its denominator is bounded below by the strictly positive number `δ²`.

The equality with `a/b` on `δ ≤ |b|` is correct. The comparison lemma is also correct:

- The oscillation hypothesis bounds every test-function difference by `C`.
- It also bounds `f` by `‖f 0‖ + C`, ensuring integrability on a probability space.
- Outside `{|V| ≤ δ}`, the difference is zero.
- Integrating the indicator bound gives exactly
  \[
  \left|\int f(U/V)-\int f(T_\delta(U,V))\right|
  \le C\,P(|V|\le\delta).
  \]

The closed exceptional set is a harmless overestimate: equality with division already holds on its boundary.

### Tails, portmanteau, and error bounds

The tails lemma correctly uses continuity from above for the decreasing measurable sets
\[
\{|B|\le 1/(m+1)\},
\]
whose intersection is `{B = 0}`. Finiteness is available from the probability-measure assumption.

The portmanteau argument is sound:

1. Project joint convergence through `Prod.snd` to obtain `W ⇒ B`.
2. Apply the closed-set bound to `{b : |b| ≤ δ}`.
3. Choose `δ` with limiting probability strictly below `η`.
4. Deduce that the source probabilities are eventually strictly below `η`.

There is **no missing boundary-null assumption**: this uses the closed-set upper bound, not convergence of the probabilities of those sets.

The choice
\[
\eta=\frac{\varepsilon}{6(C+1)}
\]
is valid since `C ≥ 0`. Each truncation error is at most `Cη ≤ ε/3`; the fixed-truncation integral difference is strictly below `ε/3`. The triangle inequalities therefore give the required strict `ε` bound. The bookkeeping also handles `C = 0`.

### Scaled form

The statement and proof are correct under
```lean
ha : ∀ i, a i ≠ 0
```
Cancellation holds even when `V i ω = 0`, using totalised division.

**Docstring correction:** delete the discussion of indices where `a_ℓ = 0`. Such indices are excluded by `ha`, and totalised division does not generally preserve the cancellation identity there. For example, `U = V = 1` and `a = 0` give a scaled quotient of `0`, but an original quotient of `1`.

## 2. u287 — assembled leading posterior quotient

### Joint model and common phase

`PairData` is an honest joint datum:

- Its underlying normed space is `JointData × JointData`, with the product sup norm.
- The declared measurable structure is its Borel σ-algebra.
- Both projections are continuous.
- `hXY` is convergence of the **whole pair**, retaining dependence between numerator and denominator.

The ordering is consistent throughout: data are stored as **denominator, numerator**, while `pairCoeff` produces **numerator coefficient, denominator coefficient**, as required for division.

However, **the type does not enforce a shared random phase or the amplitude relation `η_φ = φ·η_1`**. It supplies the same chart framework and fixed analytic parameters to both components, but permits distinct phase data.

The docstring should explicitly say that the paper’s common-phase, amplitude-linked construction is a **special case**. This generality is not a mathematical defect.

### Joint normalised convergence

The proof establishes the right source-space comparison. Write
\[
a_i=N_i^{-\mu_0}(\log N_i)^{j_0},\qquad
C_i=\operatorname{pairCoeff}(XY_i).
\]
On the intersection of the four indexwise a.e. events supplied by the decompositions and predecessor hypotheses,
\[
\frac{Z^\phi_i}{a_i}-C^\phi_i
=
\bigl(gRemainder^\phi_i-C^\phi_i\bigr)+\frac{E^\phi_i}{a_i},
\]
and likewise for the denominator.

This is exactly the algebra performed by unfolding the remainder and rewriting the predecessor sums to zero.

The probabilistic steps are sound:

- Uniform remainder estimates on joint balls, together with norm-boundedness in probability of `XY`, give the **vector remainder-minus-source-coefficient error** tending to zero in probability.
- Separate residual convergence in probability gives convergence of the residual pair by a union bound; no independence is needed.
- Adding the vector errors preserves convergence to zero in probability.
- Continuous mapping gives joint convergence of `pairCoeff(XY i)` to `pairCoeff(Z)`.
- Vector Slutsky transfers that convergence to the normalised external numerator/denominator pair.

There is no attempt to manufacture joint convergence from marginal convergence.

**Important docstring correction:** the proof does not show that the remainders converge in probability to coefficients evaluated at the limiting datum `Z`. It shows that the remainders **minus coefficients evaluated at the same source datum `XY i`** converge in probability to zero. The limiting datum may live on a different probability space.

### Leading-scale and source hypotheses

The scale is exactly the authorised
\[
a_i=N_i^{-\mu_0}(\log N_i)^{j_0}.
\]
The lattice and degree hypotheses match the frozen assembled remainder result. In the final theorem, `N_i > 1` makes both the real-power factor and the logarithmic-power factor positive, so `a_i ≠ 0`.

The predecessor hypotheses are correctly imposed **at every source index, almost surely**, for both families. More precisely, they require the **aggregate predecessor sum evaluated at `N_i`** to vanish. They do not require each predecessor coefficient to vanish separately. That weaker aggregate condition is sufficient for the displayed algebra and matches the authorised gate.

The final `hB` is exactly nonvanishing almost surely of the limiting **denominator** canonical coefficient. It does not assert positivity.

Consequently, `tendstoInDistribution_posterior_leading` faithfully gives the authorised assembled common-target leading quotient
\[
\frac{Z^\phi_i}{Z^1_i}
\Rightarrow
\frac{C^\phi_{\mu_0,j_0}(Z.\mathrm{num})}
     {C^1_{\mu_0,j_0}(Z.\mathrm{den})}.
\]

This is a **conditional leading-term rendering**, not a derivation that the posterior model satisfies the hypotheses. In particular, numerator nonvanishing is not required: the numerator coefficient may be zero, yielding a zero limit. The theorem therefore need not certify a common *first nonzero* index for both families.

## 3. Scope and non-claims

Headline XXXVIII respects the authorised boundaries:

- The target `(μ₀, j₀)` is fixed and deterministic.
- Source predecessor vanishing is assumed; limit vanishing alone would not control amplified lower-order source contributions.
- Exact source vanishing is a sufficient hypothesis here, not a claim that no weaker negligibility condition could work.
- Finite-sample denominator positivity is neither assumed nor derived.
- Joint tangential-data convergence remains a hypothesis.
- No all-orders quotient expansion or random leading-index selection is obtained.
- **No convergence of expectations or moments follows.** The posterior expectation is itself the random quotient under study; convergence of its distribution does not imply convergence of its expectation over the sampling randomness.

## 4. Before freezing A4-L

### Blocking fixes

**None identified.**

### Nonblocking should-fix list

1. **Scaled quotient docstring:** remove the zero-normalisation clause; state cancellation under `∀ i, a i ≠ 0`.
2. **Common-phase scope:** explicitly describe the shared-phase, amplitude-linked posterior model as a specialisation, not a constraint encoded by `PairData`.
3. **Probability comparison wording:** say “remainders minus coefficients at the source datum tend to zero in probability.”
4. **Leading-target precision:** clarify that aggregate predecessor sums vanish at the source scales; individual coefficient vanishing and numerator nonvanishing are not asserted.
5. Add **“no expectation/moment convergence”** to the documented non-claims.

**Recommendation:** freeze units 286–287 as mathematically passed, with these documentation cleanups.
