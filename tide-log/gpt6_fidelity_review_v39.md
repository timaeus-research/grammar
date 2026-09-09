## Verdict

**PASS for units 313, 314, 315a, and 315. GO for unit 316, subject to explicit remainder and leading-support obligations below.**

The coefficient recurrence is now established by the required Route B: actual representation shift, moment recurrence, binomial algebra, and justified `tsum` linearity—not differentiation of an asymptotic remainder.

I am reviewing the supplied proofs mathematically and taking your compilation report as given; I have not independently run Lean.

## 1. Unit 313 — PASS

The differentiation-under-the-integral argument is sound.

- On `Metric.ball N₀ (N₀ / 2)`, with `N₀ > 0`, one has `N > 0`.
- On the unit box, `c x = ∏ i, x i ^ (2 * k i) ≥ 0`.
- Therefore `exp (-(β * N * c x)) ≤ 1`, and
  \[
  |G'(N,x)|\le |a(x)|\,\beta c(x).
  \]
- The bound is integrable by continuity on the bounded unit box. Neither positivity of `η` nor strict positivity of the `k i` is needed here.
- The pointwise derivative and the conversion back to `origPhaseIntegral` have the correct sign and factors.

The normalization is exactly
\[
Z'(N)=-\beta Z_K(N),\qquad
Z_K(N)=-\frac1\beta Z'(N).
\]

**No totalised-`deriv` issue:** `deriv_popIntegral` comes directly from a proved `HasDerivAt`. This is an exact identity, not an asymptotic differentiation rule.

**Nonblocking documentation improvement:** the prose says “continuous amplitude on the unit box,” whereas the theorem assumes globally `Continuous η`. This is a harmless stronger hypothesis; either describe it precisely or weaken it later if useful.

## 2. Unit 314 — PASS

The recurrence is correct:
\[
M(\mu+1,i)=\frac{\mu M(\mu,i)-iM(\mu,i-1)}{\beta},
\qquad \mu>0,\ \beta>0.
\]

The proof properly supplies both integrability conditions and both boundary limits for integration by parts.

- **At zero, `i = 0`:** this reduces to \(t^\mu\to0\).
- **At zero, `i > 0`:**
  \[
  \bigl(-\log t\;t^{\mu/i}\bigr)^i
  =t^\mu(-\log t)^i,
  \]
  so the cited logarithm–power limit applies.
- **At infinity:** for \(t\ge1\),
  \[
  |t^\mu(-\log t)^i e^{-\beta t}|
  \le t^{\mu+i}e^{-\beta t}\to0.
  \]
  This works for every real `μ` in the infinity lemma.
- The antiderivative \(v=-e^{-\beta t}/\beta\) gives the displayed sign.

The `i = 0` case is genuinely harmless: natural subtraction makes `i - 1 = 0`, and the corresponding finite moment is multiplied by zero. The proof does not exploit undefined divergent moments or totalised integrals.

**Blocking fixes: none.**

## 3. Unit 315a — PASS

This satisfies the representation-level requirement.

In `basisConv_shift`:

- The resonant condition is preserved:
  \[
  t.1+1=(w+1)+1\iff t.1=w+1.
  \]
- In the nonresonant branch, the `gRep` parameter is unchanged:
  \[
  (w+1)-(t.1+1)+1=w-t.1+1.
  \]
- The shift parameter agrees after composing shifts:
  \[
  (t.1+1)-1=(t.1-1)+1.
  \]

Thus the result is equality of the actual lists, not merely equality of their interpreted functions. `conv_shift` lifts this through `flatMap`; the induction gives `stateDensityRep_shift`; and `coeffAt_shift` transports the actual filtered coefficient sums, including any duplicate terms.

Together with `monoWeights_add_two_k`, this proves exactly the shift needed for every Taylor multi-index `γ`.

**Blocking fixes: none.**

## 4. Unit 315 — PASS

All the delicate finite-sum and infinite-sum steps are correct.

### Kernel transport

- The `q = j` contribution to the second sum vanishes because its scalar factor is zero.
- On the remaining range,
  \[
  \binom qj(q-j)=(j+1)\binom q{j+1}
  \]
  gives precisely the coefficient multiplying the next log degree.
- `Nat.sub_sub` gives the correct moment index.
- When `j > n`, both relevant intervals are empty.

### Functional and population transport

The two source summands are summable by `summable_kernel_term`. This justifies subtraction inside the `tsum`; scalar extraction then gives the functional identity. The common prefactor involving `k` is unchanged by shifting `h`.

Unit 291 transfers the result to `familySpectralCoeff`, with positivity at `μ + 1` properly discharged.

The generality is honest: **every real `μ > 0` and every natural log degree `j`**, not just supported exponents or nonzero coefficients.

### Important limitation

`population_coeff_eq_zero_of_lt` proves only the ambient degree bound
\[
j>n\implies C(\mu,j)=0.
\]
It does **not**, in general, prove the leading-exponent bound
\[
C(\lambda,q)=0\quad(q\ge m).
\]
The latter remains a separate support/multiplicity theorem unless `m = n + 1`.

**Nonblocking should-fix:** mark the final paragraph of the module documentation explicitly:

- leading specialization uses `C(λ,m) = 0` and `m ≥ 1`;
- next-log specialization is for **`m ≥ 2`**.

The general transport theorem itself needs no change.

## 5. Gate for unit 316

### The proposed limit and quotient algebra are correct

For `m ≥ 2`, put \(L=\log N\), and write
\[
Z=N^{-\lambda}L^{m-2}(AL+B+\varepsilon),\qquad
Z_K=N^{-\lambda-1}L^{m-2}(A_KL+B_K+\varepsilon_K),
\]
with \(\varepsilon,\varepsilon_K\to0\).

Using \(A_K=\lambda A/\beta\), your exact quotient identity is correct **eventually**, where the factors being cancelled are nonzero:
\[
NL\left(\frac{Z_K}{Z}-\frac{\lambda}{\beta N}\right)
=
\frac{A(B_K+\varepsilon_K)-A_K(B+\varepsilon)}
 {A\left(A+(B+\varepsilon)/L\right)}.
\]
Its limit is
\[
\frac{AB_K-A_KB}{A^2}=-\frac{m-1}{\beta}.
\]

There is no need for `A > 0`: `A ≠ 0` suffices.

### Required obligations before closing the theorem

#### A. Prove the leading-support vanishing

Supply
\[
C(\lambda,q)=0\quad(q\ge m),
\]
not merely the ambient bound above `n`. In particular, `C(λ,m)=0` gives the leading transport identity.

The general recurrence then also transports the leading-support vanishing to the shifted coefficients.

#### B. State the remainders at the required scale

For `m ≥ 2`, the precise requirements are
\[
R=o\!\left(N^{-\lambda}L^{m-2}\right),\qquad
R_K=o\!\left(N^{-\lambda-1}L^{m-2}\right).
\]

Your proposed generalization in (a) is valid **if the existing proof already establishes**
\[
R/N^{-\lambda}\to0
\]
or a stronger power-gap estimate. Since \(L^j\ge1\) eventually, division by an additional natural power of `L` then preserves convergence to zero.

But convergence only after normalization by the *leading* scale \(N^{-\lambda}L^{m-1}\) does not suffice to deduce the next-log result. The proof must retain the stronger remainder estimate.

Also account for terms at exponents strictly above `λ`: these must vanish at the chosen normalization, using the existing spectral-tail/gap machinery.

#### C. The `m = 1` branch needs a stronger log-weighted remainder

Your separate branch is right, but **(a), for natural `j`, does not supply its needed estimate**.

Here one needs
\[
R=o(N^{-\lambda}/L),\qquad
R_K=o(N^{-\lambda-1}/L),
\]
equivalently
\[
L\varepsilon\to0,\qquad L\varepsilon_K\to0.
\]

Then the useful identity is
\[
NL\left(\frac{Z_K}{Z}-\frac{\lambda}{\beta N}\right)
=
\frac{A(L\varepsilon_K)-A_K(L\varepsilon)}
 {A(A+\varepsilon)}
\longrightarrow0.
\]

A genuine positive power gap supplies this extra logarithm. Merely knowing \(\varepsilon,\varepsilon_K\to0\) does not.

#### D. Establish eventual nonvanishing explicitly

From
\[
\frac{Z}{N^{-\lambda}L^{m-1}}\to A\ne0
\]
obtain `Z N ≠ 0` eventually. Restrict quotient algebra also to `N > 1`, so `N`, `log N`, and the normalization factors are nonzero.

Totalised division causes no problem for the final `Tendsto` statement, but it cannot justify cancellation before these eventual facts are available.

#### E. Connect the shifted integral to the energy insertion

If not already packaged, add the exact bridge
\[
Z_K(N)=Z_{h+2k,\eta}(N),
\]
by `pow_add` and product algebra. Also use the existing amplitude-reconstruction/expansion hypotheses to connect the abstract coefficient family to the actual `Z` and `Z_K`.

## Scope recommendation

**Proceed with unit 316.** First prove a reusable quotient lemma from the explicit two-term hypotheses, with the `m = 1` branch separate; then instantiate it using the population expansion.

For an assembled version:

- **Attempt it now** if assembly is finite and the stronger remainder estimates and common coefficient identification are already available. Sum coefficients at the relevant exponent/log degrees, including lower-multiplicity contributions to the second coefficient.
- **Defer it** if it requires new uniform remainder estimates, countable-sum interchange, or a new spectral-gap argument. Pointwise little‑`o` statements alone do not justify infinite assembly.

**Bottom line:** no blocking fixes to 313–315. The remaining gate conditions are candidate-specific leading-support vanishing and the correctly scaled remainders—especially the extra logarithmic control for `m = 1`.
