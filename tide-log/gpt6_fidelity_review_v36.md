## Verdict

**u302 PASS · u303 PASS · u304 PASS · u305 PASS.**

No blocking mathematical or statement-level fixes in the four supplied files. This is a fidelity review of the supplied statements and proofs, taking the reported successful build and frozen upstream interfaces as given—not an independent compilation or re-audit of P1–P3.

The main release cautions concern **scope and labels**, not these proofs: actual nonzero leading terms versus candidate/divisor-order predictions; signed integral ratios versus genuine posterior expectations; and conditional geometric assembly versus construction of the external decompositions.

## 1. u302 — quotient and three cases: PASS

`isEquivalent_quotient_powLog` is the faithful algebraic core:
\[
\frac{Z_n}{Z_d}\sim
\frac{C_n}{C_d}N^{-(\mu-\lambda)}
\frac{(\log N)^{j_n}}{(\log N)^{j_d}}.
\]

- Keeping the logarithmic factor as a quotient of natural powers avoids truncated natural subtraction.
- `Cd ≠ 0` is sufficient for this theorem. **`Cn ≠ 0` is needed for the interpretation as an actual nonzero numerator leading term and for the order exclusion in u303, not for quotient algebra or these limit results.**
- The eventual restriction `N > 1` supplies all the required nonzero powers and logarithms.
- The three limit results are correct.

The power-decay squeeze is valid. For `N ≥ exp 1`,
\[
(\log N)^{j_d}\ge1,\qquad
0\le \frac{(\log N)^{j_n}}{(\log N)^{j_d}}
\le(\log N)^{j_n}\le(1+\log N)^{j_n}.
\]
The positive power gap dominates the latter polynomial in `log N`.

**Nonblocking documentation correction:** “with `C_φ = 0` nothing is asserted” is slightly too absolute for the actual generic lemmas. They do allow zero `Cn`, but equivalence to the zero function is a very strong condition—eventual vanishing—not a next-term theorem. Prefer:

> Classification concerns actual nonzero leading coefficients. A vanishing candidate coefficient does not supply a numerator equivalence or identify its next leading pair.

For the paper’s multiplicity formulation, retain `m,r ≥ 1`: only then does `r < m` correspond exactly to `r−1 < m−1`. The Lean theorems correctly work directly with log degrees.

## 2. u303 — bounded observables and order exclusion: PASS

### Integral inequality

The objects and assumptions are right:

- the same population weight appears in numerator and denominator;
- `c ≥ 0` on the box;
- `|φ| ≤ B` on the box;
- continuity supplies the integrability used by the proof;
- the monomial-exponential weight is nonnegative there.

Neither `β > 0` nor `N > 0` is needed for this fixed-parameter inequality: the exponential remains positive and the integrands remain continuous on the relevant bounded domain.

The theorem uses **an arbitrary uniform bound `B`**, rather than a formally defined sup norm. The `‖φ‖∞` prose is appropriate mathematical shorthand, but the release statement should explain that distinction.

### Order exclusion

The proof is sound:

1. Nonzero `Cn`, `Cd` give eventual `R ≠ 0`.
2. Equivalence yields `q/R → 1`.
3. Consequently, eventually `|q| ≥ |R|/2`.
4. Either excluded ordering forces `|R| → ∞`:
   - `μ < λ`: positive power growth dominates any denominator log degree;
   - `μ = λ`, `jn > jd`: a positive natural log power diverges.
5. This contradicts eventual boundedness of `|q|`.

No hypothesis is missing. In particular, `hCn` is indispensable here and is present.

**Nonblocking interface improvement:** the integral inequality and abstract order theorem are separate; no theorem in this file explicitly composes them. The composition is valid. A nonnegative denominator with a nonzero asymptotic leading coefficient is eventually positive, so division gives the required bounded quotient. A short documentation bridge is sufficient; a convenience corollary would be useful but is not a release blocker.

## 3. u304 — energy insertion: PASS

The coefficient calculation is faithful and includes the essential normalisation argument, not merely the exponent shift.

Under `∀ i, 0 < k i`:

- every ratio increases by one;
- the level/minimiser set is preserved after shifting `λ` to `λ+1`;
- multiplicity and face projection are unchanged;
- the residual exponents are unchanged;
- the remaining face-constant factor changes by
  \[
  \Gamma(\lambda+1)\beta^{-(\lambda+1)}
  =\frac{\lambda}{\beta}\Gamma(\lambda)\beta^{-\lambda}.
  \]

Thus
\[
A(h+2k,k,\lambda+1,\beta;\psi)
=\frac{\lambda}{\beta}A(h,k,\lambda,\beta;\psi)
\]
is correct.

`energy_ratio_tendsto` then uses:

- the exact monomial insertion identity;
- the **same amplitude `ψ`**;
- two genuine asymptotic equivalences;
- the original nonzero coefficient and the resulting nonzero shifted coefficient;
- cancellation of the identical log degree.

It proves precisely
\[
N\,\frac{\mathcal Z_N[K\circ\pi]}{\mathcal Z_N[1]}
\longrightarrow\frac{\lambda}{\beta}.
\]

The assumptions suffice for the analytic ratio theorem. Positivity of `ψ` is unnecessary for that result, but interpreting the ratio as a posterior expectation requires the corresponding nonnegative base-density setting.

### Non-claim wording

The non-claims are substantively right. One **should-fix** is the temperature factor in the displayed derivative identity. For weight `exp(-β N K)`, the prospective identity is
\[
\mathcal Z_N[K]=-\frac1\beta\frac{d}{dN}\mathcal Z_N[1].
\]
The version without `1/β` is the `β=1` version. Likewise, the prospective general-temperature correction would be
\[
-\frac{m-1}{\beta N\log N}.
\]

Neither is established here, and neither should be inferred by differentiating an asymptotic equivalent.

## 4. u305 — assembled energy ratio: PASS

This preserves the required coupling between numerator and denominator:

- same chart family;
- same tangential measures;
- same zero-noise data `x`, hence the same amplitudes;
- only the weights shift from `h_I` to `h_I+2k_I`.

The shifted ordering hypotheses are correctly transported. The tied-chart condition is preserved, and on every contributing chart `λ_I = μ_*`. Therefore
\[
A_{*,K}=\frac{\mu_*}{\beta}A_*,
\]
including when chart coefficients are signed.

The theorem correctly requires **two external decompositions** and controls the residuals at their **different scales**:
\[
E=o\!\left(N^{-\mu_*}(\log N)^{m_*-1}\right),
\quad
E_K=o\!\left(N^{-(\mu_*+1)}(\log N)^{m_*-1}\right).
\]
The numerator estimate is stronger than negligibility merely at the denominator scale; it is explicitly assumed.

The conclusion
\[
N\,Z_K(N)/Z_{\rm pop}(N)\to\mu_*/\beta
\]
is correct. Calling `μ_*` the **global RLCT** additionally invokes the external geometric identification of this chart minimum with the model’s global RLCT. The theorem does not construct that identification.

## 5. Release audit

### (a) Suggested release paragraph

> **Programme P establishes the rewritten leading-order population normal-form results of §3.** For the stated monomial-chart hypotheses, it identifies the leading power–log scale and its face-functional coefficient, transfers these results through the supported tangential integration and finite-chart assembly, and obtains asymptotic equivalences when the relevant leading coefficient is nonzero. For observable insertions with actual nonzero leading terms, it proves the leading expectation quotient and its three admissible regimes; boundedness relative to a common nonnegative base integrand excludes a numerator that precedes the denominator. For the energy observable \(K\), it proves the exact face-coefficient shift \(A_K=(\lambda/\beta)A\), and hence \(N E_N[K]\to\lambda/\beta\), with the corresponding assembled conclusion \(N E_N[K]\to\mu_*/\beta\). Construction of the geometric normal forms, identification with the original model and its RLCT, and the external assembly decompositions and residual estimates remain hypotheses; these are leading-order population results, not a full higher-order or noisy empirical expansion.

### (b) Non-claims for headlines and author note

Reproduce the following scope boundaries:

1. **No general full asymptotic series.** Leading terms and the stated remainder controls do not supply arbitrary higher-order coefficients.
2. **No differentiation of asymptotic equivalents.** No partition-function derivative identity or `1/(N log N)` energy correction is proved here.
3. **No next-leading-term recovery after cancellation.** If a candidate chart or assembled coefficient vanishes, these equivalence theorems do not identify the next pair.
4. **No general observable-order rule from divisor orders alone.** The quotient classification assumes actual nonzero numerator and denominator leading terms.
5. **No order exclusion for unrelated expansions.** The exclusion requires a bounded quotient, supplied in the posterior application by a bounded observable and a common nonnegative base integrand.
6. **No automatic probability interpretation for signed amplitudes.** The analytic ratio results are more general than posterior expectations.
7. **No construction of the external geometry or global integral decomposition.** Original-model identification, chart validity, and any required outside-chart controls remain external.
8. **No automatic control of the energy residual from the denominator residual.** The two residual estimates are separate assumptions at their respective scales.
9. **No removal of the stated chart hypotheses**, including positive `k_i` where required.
10. **No noisy empirical or stochastic conclusion from the population tranche.** In particular, do not advertise these results as generalisation-error or stochastic free-energy theorems.

### (c) Last corrections before freezing

**Blocking fixes: none.**

**Nonblocking should-fixes:**

- Replace u302’s absolute zero-coefficient disclaimer with the candidate-coefficient wording above.
- Qualify the derivative non-claim by `β=1`, or insert `1/β`; do the same for the prospective correction.
- Make the `B` versus `‖φ‖∞` convention explicit.
- State the short positivity/division bridge between u303’s integral inequality and abstract bounded-quotient theorem.
- Keep “posterior expectation” and “global RLCT” conditional on their external probabilistic/geometric identifications.

### (d) Mirror annotations and paper labels

Use the labels as **cross-references to the rewritten statements**, not as unqualified assertions that every part of the old statement has been formalised.

| Paper label | Safe annotation |
|---|---|
| `thm:expectation_expansion` | “Leading-order population normal-form version.” **Not** “full expectation expansion.” |
| `eq:thm_leading_coeff` | The proved face-functional coefficient, with its exact normalisation and hypotheses. |
| `eq:lambda_I_f` | Only the precise chart exponent/minimum formula actually established upstream; distinguish candidate scale from an actual leading pair when coefficients can vanish. |
| `eq:mu_I_phi` | **Do not attach to u302/u303 as a proof of an observable exponent formula.** Those units accept actual leading pairs; they do not derive a general `μ_φ` from divisor orders. A restricted upstream shifted-monomial result may receive a correspondingly restricted annotation. |
| `eq:expectation_leading` | u302, with nonzero actual leading coefficients for the paper-facing classification; u303 supplies the bounded-observable order constraint. |
| `ex:phi_equals_K` | u304/u305, explicitly limited to the leading energy limit and the assembled theorem’s external decomposition hypotheses. |

I would not certify the exact upstream mappings for `eq:lambda_I_f` or `eq:mu_I_phi` without their rewritten text and corresponding P1–P3 statements. The safe release rule is: **label the proved restricted statement, and spell out the restriction next to the label.**

**Overall: PASS for the final theorem tranche; proceed to release audit with the documentation qualifications above.**
