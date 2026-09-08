## Verdict

| Unit | Verdict |
|---|---|
| **293 — `PopulationLeadingIsolation.lean`** | **PASS** |
| **294 — `PopulationLeadingCoeff.lean`** | **PASS** |

**No blocking fixes.** On the supplied frozen interfaces, these implement route A–D faithfully and complete the stated P1 leading-coefficient identification. This is a source-level fidelity review; I have not independently rerun the reported build.

## 1. Polynomial growth uniqueness

**Yes: this is the right reusable lemma, and the proof is mathematically sound.**

The statement correctly separates:
- coefficients **within the finite polynomial** above degree `r`;
- identification of `a r` when `r ≤ n`;
- the necessary conclusion `A = 0` when `n < r`, without constraining the unused value `a r`.

The three degree cases work as intended:

1. **`degree P > r`:** the absolute quotient tends to infinity. Composition with `hx` contradicts convergence of the absolute quotient to `|A|`.
2. **`degree P = r`:** the denominator `X^r` has leading coefficient `1`, so the quotient limit is `P.leadingCoeff = P.coeff r`.
3. **`degree P < r`:** the quotient tends to zero and `P.coeff r = 0`.

Using `Polynomial.degree` handles the zero polynomial correctly. Neither monotonicity nor surjectivity of `x` is required—`x → +∞` is sufficient. Potential zeros of `x` at finite sample sizes do not affect the argument.

## 2. Spectral isolation at `L = λ + 1/Q`

**Complete and correct.** The full lattice gap is safe because `latticeBelow` uses the strict cutoff **`μ < L`**. A candidate exactly at `λ + 1/Q` is excluded.

More precisely, the proof establishes:
- `λ = m'/Q` by attainment and `ratio_mem_lattice`;
- `λ < L`, hence membership of `λ` in the cutoff set;
- any summation exponent `μ` already has the form `m/Q`;
- if such a `μ ≠ λ` were a candidate, minimality gives `λ ≤ μ`, hence `λ < μ`;
- integer spacing then gives `m ≥ m' + 1`, contradicting `μ < λ + 1/Q`.

Thus every other summation exponent is a non-candidate, and `hC.vanish` kills its coefficients.

This also eliminates sub-`λ` terms: a candidate there would contradict `le_of_candidateExp`. One useful detail is that the proof does **not** need a separate candidate-lattice theorem for `μ`: its membership in the summation lattice already supplies that fact.

## 3. Normalised remainder

**Correct throughout.**

- **Unit-box specialisation:** `boxScale k 1 N = N`, and both box prefactors reduce to `1`.
- **Cutoff positivity:** attainment and `hk` give `λ > 0`; consequently `L > λ > 0`.
- **Sign-free constant:** replacing `K` by `|K|` is legitimate because the cutoff factor is nonnegative for `N ≥ 1`. No positivity assumption on `K` is smuggled in.
- **Logarithmic denominator:** for `N ≥ exp 1`,
  \[
  (\log N)^{m-1}\ge 1.
  \]
  This includes exponent zero. The denominator is strictly positive on this eventual region.
- **Squeeze:** the resulting majorant is
  \[
  |K|\,\frac{N^{-L}(1+\log N)^n}{N^{-\lambda}},
  \]
  which tends to zero by `tendsto_cutoff_ratio`.

The theorem’s generality over `cξ`, `cη` is also honest: it is a conditional consequence of the supplied Taylor-tree conclusion, not an independent assertion that every such family admits that conclusion.

## 4. Leading-coefficient identification

**Faithful to the corrected chart-level statement at `b = 1`.**

The integral bridge preserves the amplitude, monomial weight, exponential phase, and domain exactly. Subtracting the normalised remainder from Headline VIII’s normalised integral limit gives
\[
\frac{\sum_{j=0}^{n}C(\lambda,j)(\log N)^j}
     {(\log N)^{m-1}}
\longrightarrow \operatorname{amplitudeCoeff}(h,k,\lambda,\beta,\eta).
\]
The eventual cancellation of `N^(-λ)` is justified by positivity for `N > 1`. Polynomial uniqueness then gives precisely the two claimed conclusions.

The multiplicity bound is used correctly:
\[
m\le n+1\quad\Longrightarrow\quad m-1\le n.
\]
With natural subtraction, this implication does not itself require proving `m ≥ 1`. Attainment does ensure positive multiplicity, so there is no semantic mismatch with the intended meaning of `m`.

The hypotheses are explicit and honest:
- the existential headline retains `R > 1` and holomorphic extension;
- `Continuous η` is ambient continuity, as required by the frozen Headline VIII theorem;
- equality of real parts on the positive box alone is not silently treated as establishing that continuity;
- no nonvanishing is asserted.

The residual/face integration in `amplitudeCoeff` is fully retained. This is not a replacement of the face functional by corner evaluation.

### Nonblocking documentation fixes

1. **“Canonical coefficients.”** The headline constructs an existential coefficient system; it does not define a canonical system or prove full-system uniqueness. The stronger conditional theorem shows that **every admissible system has these same identified coefficients**. Prefer “the Taylor-tree coefficients” or “any admissible Taylor-tree coefficient system.”

2. **Continuity wording.** The headline docstring says “continuous amplitude on `(0,1]^{n+1}`,” whereas the formal hypothesis is `Continuous η` on the whole ambient space. Align the prose with the statement.

3. **“Only when every ratio is minimal.”** As a universal formula for arbitrary amplitudes, corner evaluation is justified in the all-minimal case. Particular amplitudes can give accidental agreement otherwise. Prefer:
   > “In the all-minimal case this reduces to corner evaluation; in general the face integral is essential.”

## 5. Non-claims and P2 recommendations

### Non-claims to record

P1 does **not** establish:
- that `λ` is the first exponent with a **nonzero** coefficient;
- that the logarithmic degree is exactly `m−1` when the identified coefficient vanishes;
- formulas for the lower coefficients `C(λ,j)`, `j < m−1`;
- constraints on `C(λ,j)` for `j > n`, which lie outside the displayed polynomial;
- uniqueness of the entire coefficient system;
- arbitrary-box or chart-summed/global conclusions.

### P2: monomial shift

The planned approach is appropriate. Use a distinct symbol, say `s : Fin d → ℕ`, for the shift:
\[
\eta(u)=u^s\psi(u),\qquad h'=h+s.
\]

Prove the integral identity, then apply the population theorem directly to `(h', k, ψ)`. This yields the shifted candidate support, minimum, multiplicity, and face functional.

Two statement-level cautions:

- **State the regularity assumptions on `ψ`.** Continuity or holomorphic extendibility of `ψ` should not be inferred merely from a pointwise factorisation of `η`. If division by a monomial is intended to produce that extension, prove the necessary divisibility/removable-singularity result separately.
- **Distinguish coefficient systems.** Re-running the construction gives a system supported on the shifted candidates. It does not automatically prove that the previously obtained unshifted system has shifted support; transferring that claim requires further uniqueness.

### P2: positivity

The intended criterion is sound, but distinguish continuity of the amplitude from regularity of the **weighted** integrand.

For nonminimal coordinates,
\[
h'_i-2k_i\lambda'>-1.
\]
The residual weight is positive on the positive box and integrable, but it need not extend continuously to its boundary.

A clean sufficient criterion is:
- `ψ` is continuous;
- `ψ ≥ 0` on the relevant projected face;
- `ψ > 0` at a point of that face.

Then prove positivity on a positive-measure portion of the integration domain, integrability of the weighted function, and positivity of its integral; combine with `faceLeadConst_pos`. If the point may lie on the closed face boundary, explicitly use relative neighbourhoods/density to obtain that positive-measure portion. Positivity at an unrelated ambient point is insufficient.

### Non-unit boxes

**Leave this to P3/P5.** Nothing in P1 or the proposed unit-box P2 requires it.

Your rescaling is correct for `b > 0`:
\[
Z_b(N)=b^{|h|+d}Z_1(Nb^{2|k|};\eta(b\,\cdot)).
\]
For orientation, the highest-log coefficient at exponent `λ` becomes
\[
b^{|h|+d-2\lambda|k|}
\,\operatorname{amplitudeCoeff}(h,k,\lambda,\beta,\eta(b\,\cdot)).
\]
The constant shift in the logarithm affects lower log coefficients, not this highest-log coefficient. Full coefficient transport and remainder bookkeeping belong naturally in the later rescaling package.

**Bottom line:** P1 passes, with only documentation should-fixes. Proceed to P2 using an explicitly shifted representation and an honest weighted-integral positivity lemma.
