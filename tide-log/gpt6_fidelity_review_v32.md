## Verdict

| Unit | Verdict | Assessment |
|---|---|---|
| **u290** | **PASS** | Correct zero-phase specialization, explicitly connected to the original population integral, preserving the entire `TaylorTreeConclusion`. |
| **u291** | **PASS** | Correct algebraic collapse and admissible canonical-coefficient identification; no unjustified convergence claim in the formal statements. |
| **u292** | **PASS** | Correct Gamma-moment identification with the required positivity assumptions. |

**No blocking fixes before proceeding.** The planned uniqueness route is sound. Its main additional ingredient is a finite-polynomial growth/uniqueness lemma, not differentiation of asymptotics.

This assessment uses the supplied files and frozen interfaces; it is not an independent compilation check.

## 1. u290: population integral and full remainder

The specialization is faithful:

- `Fξ := fun _ => (0 : ℂ)` is holomorphic.
- Its real part agrees with `ξ := fun _ => (0 : ℝ)` on the box.
- In `origPhaseIntegral`, this makes the fluctuation contribution
  \[
  \beta\sqrt N\,u^k\xi(u)
  \]
  identically zero. The remaining integrand is exactly
  \[
  \eta(u)u^h e^{-\beta N u^{2k}}.
  \]
- `taylorFamily_const_zero` correctly identifies the resulting phase coefficient family with zero.

Crucially, the theorem retains the **whole** `TaylorTreeConclusion`, rather than extracting a weaker expansion. Thus its remainder, `isBigO`, support, summability, coefficient identification, and dictionary conclusions are preserved unchanged.

The remainder remains *packaged for the family integral*, but the accompanying equality with the original integral holds for every `N`. Consequently, all those integral conclusions transport directly to the original population integral. This meets the stated acceptance criterion: the original integral is exposed explicitly, not merely mentioned in documentation.

### Amplitude hypothesis

The precise hypothesis is
\[
\operatorname{Re}F_\eta(u)=\eta(u)
\]
on the real box. It does **not** require \(F_\eta(u)=\eta(u)\) as a complex equality.

The documentation gives the real-part Taylor family explicitly, so it is not materially misleading. Nevertheless, “has a holomorphic extension” can conventionally suggest complex-valued equality on the real slice. A more exact wording would be:

> “admits a holomorphic function on the polydisc whose real part agrees with `η` on the box.”

This is a **nonblocking documentation improvement**.

## 2. u291: coefficient collapse and its interpretation

All the displayed identities are correct.

At zero phase,
\[
J=\operatorname{fluctFamily}(0)=0.
\]
For \(p>0\), \(J^{*p}=0\), hence the amplitude convolution and its kernel functional vanish. At \(p=0\),
\[
J^{*0}=\delta_0,\qquad c_\eta*\delta_0=c_\eta,
\qquad \frac{\beta^0}{0!}=1.
\]
Therefore
\[
\operatorname{familyCoeffSeries}(0,c_\eta)
=\operatorname{familyCoeffTerm}(0,c_\eta,0)
=K_k\sum_\gamma' c_{\eta,\gamma}S_0(\mu,j;\gamma).
\]

The proof of convolution with the delta family correctly uses the restriction \(\alpha\leq\gamma\). That restriction is important because subtraction is truncated coordinatewise in \(\mathbb N\).

### Convergence

The distinction in the file is right:

- The **outer** series has only one potentially nonzero term, so its collapse is unconditional.
- The **inner** amplitude expression remains a `tsum`; the unconditional algebraic identities do not establish its absolute convergence for arbitrary `cη`.

`familySpectralCoeff_population` is the right canonical-coefficient bridge. Its hypotheses are precisely the frozen bridge’s hypotheses after discharging `AbsSummable 0`:

- `hk`;
- `hβ`;
- `AbsSummable cη`;
- `hμ`.

There is no missing phase assumption.

One logical distinction worth retaining in later documentation: equality with `familySpectralCoeff` is not, by itself, a proof of absolute convergence of the inner series. When that assertion is needed, cite or apply the existing admissible-kernel summability result.

### “Dressed-moment expansion”

This identification is accurate **at the normal-form coefficient level**. The kernel uses the state density for the shifted monomial \(u^{h+\gamma}\), and the finite sum
\[
\sum_{q=j}^{n}
  \operatorname{coeffAt}(\rho_{h+\gamma},\mu,q)
  \binom qj
  \operatorname{fluctMoment}(\beta,0,0,\mu,q-j)
\]
is exactly the corresponding zero-phase coefficient kernel.

The \((-\log t)^{q-j}\) convention in `fluctMoment` accounts for the sign arising from the logarithmic expansion; there is no missing additional sign.

The wording should not be read as establishing the geometric tubular construction or admissibility of arbitrary localized amplitudes. u290’s scope disclaimer appropriately excludes those claims.

**Small documentation improvements:**

1. Write \(j\leq q\leq n\), rather than just \(q\geq j\).
2. In the prose describing the canonical coefficient, include `hk` and `β > 0`, not only absolute summability and `μ > 0`.
3. Explain that \(c_{\eta,\gamma}=\eta_\gamma/\gamma!\) when \(\eta_\gamma\) denotes the derivative data. For arbitrary input `cη`, that derivative interpretation is not an additional formal conclusion.

## 3. u292: Gamma moment

Correct.

At \(a=p=i=0\), the integrand simplifies exactly to
\[
t^{\mu-1}e^{-\beta t}.
\]
The proof then applies the supplied Gamma-integral identity directly. No differentiation under an integral or under an asymptotic expansion occurs.

The assumptions
\[
\mu>0,\qquad \beta>0
\]
are the correct ones, and the positivity corollary follows correctly.

Here `β ^ (-μ)` is real exponentiation, since the exponent is real. With `β > 0`, it is precisely the paper’s \(\beta^{-\lambda}\) after identifying \(\mu=\lambda\). There is no convention mismatch.

## 4. Unit-3 factorial and scaling audit

**The population integrand is genuinely used.** The explicit `origPhaseIntegral … (fun _ => 0) η` equality is the decisive point.

**No duplicated amplitude factorial appears.**

- `taylorFamily` divides the coordinate derivatives by `multiFactorial γ` once.
- u291 uses `cη γ` directly.
- The surviving outer factor is \(\beta^0/0!=1\), not an amplitude factorial.
- No further division by \(\gamma!\) is inserted into the kernel.

**No duplicated box scaling appears in these units.**

- u290 passes the unscaled Taylor families to the inherited conclusion, letting that conclusion handle its established box scaling.
- u291 is a family-coefficient identity with no box parameter.
- u292 introduces no box factor.

In subsequent applications to `TaylorTreeConclusion.coeff_eq`, use the collapse on the family actually present there—namely `scale cη b`, alongside the inherited normalization factors. Do **not** substitute the unscaled `cη` unless \(b=1\) or an appropriate scaling identity has been applied.

Starting the uniqueness argument at \(b=1\) is therefore a good choice.

## 5. Planned leading-coefficient identification

Yes: a normalized-integral limit, together with the cutoff expansion and support information, is enough.

Write
\[
r=m-1,\qquad
P(x)=\sum_{j=0}^{n}C(\lambda,j)x^j.
\]
After eliminating sub-\(\lambda\) exponents and ensuring that the cutoff includes no supported exponent strictly between \(\lambda\) and \(L\), the expansion becomes
\[
Z(N)=N^{-\lambda}P(\log N)+R(N),
\]
where
\[
R(N)=O\!\left(N^{-L}(1+\log N)^n\right),
\qquad L>\lambda.
\]

The needed steps are:

### A. Justify the isolated exponent

For \(L=\lambda+1/(2Q)\), prove that the actual support lattice has no point in \((\lambda,L]\). The chosen gap is valid only once the relevant lattice denominator and membership facts have been established.

Support below \(\lambda\) must also be eliminated formally; merely calling \(\lambda\) the leading exponent is not a substitute for that lemma.

### B. Show the normalized remainder tends to zero

Eventually \(N>1\), so division by \((\log N)^r\) is legitimate. Prove
\[
N^\lambda(\log N)^{-r}R(N)\longrightarrow0.
\]
The bound reduces to a power-decay-versus-log-growth estimate:
\[
N^{-(L-\lambda)}
\frac{(1+\log N)^n}{(\log N)^r}\longrightarrow0.
\]

This is where the strict gap \(L-\lambda>0\) is used.

### C. Transfer the normalized integral limit to the polynomial

Match the original integral and normalization in `headline_normal_moment_amplitude`. If it gives
\[
N^\lambda(\log N)^{-r}Z(N)\longrightarrow A,
\]
then subtraction of the normalized remainder yields
\[
\frac{P(\log N)}{(\log N)^r}\longrightarrow A.
\]

Also establish the intended multiplicity convention, in particular \(m\geq1\).

### D. Apply polynomial growth uniqueness

The useful reusable lemma is:

> If a finite polynomial \(P(x)=\sum_j a_jx^j\) satisfies  
> \(P(x)/x^r\to A\) as \(x\to+\infty\), then \(a_j=0\) for every \(j>r\), and \(a_r=A\), with absent coefficients interpreted as zero.

For this application it is enough to formulate the lemma along any parameter \(x(N)\to+\infty\), then take \(x(N)=\log N\).

The proof reads off the highest nonzero degree. If that degree \(d\) exceeds \(r\), then
\[
\frac{P(x)}{x^r}\sim a_dx^{d-r},
\]
which cannot converge to a finite real number. Once higher coefficients vanish, all terms below degree \(r\) tend to zero after division, leaving \(a_r\).

Thus **dividing and taking limits is sufficient, provided this polynomial argument is included**. One cannot simply take finite limits termwise before eliminating the higher, potentially divergent terms.

No assumption \(A\neq0\) is needed to identify the coefficients. Positivity or nonvanishing of the face functional is needed only to conclude that the identified coefficient is genuinely nonzero.

### Cleanest route

Use one finite-polynomial uniqueness lemma, then apply it after a single normalized-remainder estimate. This is cleaner than building full uniqueness of all asymptotic coefficients or repeatedly extracting the highest logarithmic degree.

## Fix list

**Blocking:** none.

**Nonblocking should-fixes:**

- Clarify “holomorphic extension” as real-part agreement.
- Include all positivity hypotheses in u291’s canonical-coefficient prose.
- Make the finite \(q\)-range explicit.
- Keep derivative data \(\eta_\gamma\) distinct from already factorial-normalized coefficients `cη γ`.
- In later boxed coefficient statements, visibly retain the inherited scaling and normalization.
- Optionally add a directly rewritten original-integral remainder corollary for usability; it is not necessary for u290’s acceptance.

**Proceed with the remaining P1 units.**
