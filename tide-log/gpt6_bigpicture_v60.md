## Recommendation

**Make the next campaign about closing the finite-\(n\) moment interface, not constructing a matrix square root.**

There is a useful shortcut: you may not need a pathwise comparison with the *limiting* coefficient \(D_\rho(\xi_n)\). The Hölder–Tonelli argument of CXLIX works directly on the **finite-\(n\) chart integral**, with its deterministic population weight. This avoids radial substitution, logarithmic density estimates, and comparison of the full chart field with its face restriction.

I would run **six bounded units**, in the order below. Units 1–3 are the campaign; 4–5 are optional completion work; 6 is the paper/release pass.

I have not inspected the present files or records. The statements below are precise mathematical interfaces, but proposed Lean names and arguments involving `TanCertificate` are schematic, not claims about its existing fields.

---

## 1. Generalise the moment bridge to deterministic finite-\(n\) weights

**Priority: highest. One focused unit.**

### The reusable statement

Let \(P\) be a probability measure, \(\nu\) a finite measure, \(p\ge1\), and \(H(\omega,u)\) jointly measurable. Assume
\[
\mathbb E e^{pH(\cdot,u)}\le1
\quad\text{for }\nu\text{-a.e. }u.
\]
Then
\[
\mathbb E\left[\left(\int e^{H(\omega,u)}\,d\nu(u)\right)^p\right]
 \le \nu(U)^p.
\]

Proposed declaration:

```lean
lintegral_rpow_lintegral_exp_le_mass_rpow
```

Prove this first in `ENNReal`, including the zero-mass case. It is essentially the CXLIX proof with the Gamma-specific algebra removed.

### The finite-\(n\) application

Let \(r_n:U\to\mathbb R\), \(w\ge0\), \(A_n\ge0\), and
\[
J_n(\omega)
 =\int_U w(u)a(u)
   e^{-\beta r_n(u)^2+\beta r_n(u)\xi_n(\omega,u)}\,d\mu(u),
\qquad |a(u)|\le M.
\]
Assume the **full-domain** pointwise estimate
\[
\mathbb E e^{t\xi_n(\cdot,u)}\le e^{ct^2/2}
\]
for the required \(n,u,t\). Put
\[
\alpha=\beta(1-p\beta c/2)>0,\qquad
B_n(\alpha)=A_n\int_Uw(u)e^{-\alpha r_n(u)^2}\,d\mu(u).
\]
Then
\[
\boxed{\quad
\mathbb E|A_nJ_n|^p\le \bigl(MB_n(\alpha)\bigr)^p.
\quad}
\]

Proposed declaration:

```lean
moment_scaled_integral_le_population_mass
```

The proof uses the deterministic measure
\[
d\nu_n=A_nw(u)e^{-\alpha r_n(u)^2}\,d\mu(u)
\]
and
\[
H_n=-(\beta-\alpha)r_n^2+\beta r_n\xi_n.
\]
Exactly as before,
\[
-p(\beta-\alpha)r_n^2+\frac c2(p\beta r_n)^2=0.
\]

**This is the central new observation:** the desired uniform moment bound reduces to a bound on a *deterministic population integral at temperature \(\alpha\)*. A pathwise \(D_\rho\)-domination is not necessary.

### Inputs

- Reuse CXLIX’s Hölder implementation:
  `ENNReal.lintegral_mul_le_Lp_mul_Lq`.
- Tonelli and the existing exponential-moment interface.
- `Measure.withDensity` for the deterministic weight, if convenient.
- Existing domination-to-integrability lemmas after the `ENNReal` theorem.

### Traps

1. **Do not start with a Bochner integral whose integrability is unproved.** Establish finiteness of the nonnegative envelope a.e.; then establish pathwise integrability and the real-valued moment statement. Compact continuous chart data may discharge this separately.
2. If \(r_n\) can be negative, require the MGF bound for all real arguments. On a positive box with a nonnegative monomial, nonnegative arguments suffice.
3. This needs a uniform sub-Gaussian bound on the field **throughout the integration domain**, not merely on the limiting face.
4. For uniform integrability, use \(p>1\). The hypothesis permitting some such \(p\) is \(\beta c<2\).
5. This is a sufficient bound, not a sharp moment classification.

**Stop rule:** extract the generic lemma and this application. Do not add a general-purpose random weighted-measure API.

---

## 2. Instantiate it for the certified box model

**Priority: highest. One unit, with a certificate audit first.**

For the usual positive-box model,
\[
r_n(u)=\sqrt n\,u^k,\qquad r_n(u)^2=n\,u^{2k},
\]
and \(w(u)=u^h\), possibly with a deterministic base measure and localisation weight.

The target is:

```lean
TanCertificate.moment_scaled_tanIntegral_le
```

with mathematical conclusion
\[
\mathbb E\left|A_n\,\mathrm{tanIntegral}_n(\xi_n)\right|^p
 \le
 \left[
 M A_n\int_{\mathrm{box}}u^h e^{-\alpha n u^{2k}}\,du
 \right]^p.
\]

Then prove the uniform version:

```lean
TanCertificate.uniform_moment_scaled_tanIntegral
```

under a certified deterministic bound
\[
\sup_{n\ge n_0}
 A_n\int_{\mathrm{box}}u^h e^{-\alpha n u^{2k}}\,du
 \le C_\alpha.
\]

Its conclusion is simply
\[
\sup_{n\ge n_0}\mathbb E
 \left|A_n\,\mathrm{tanIntegral}_n(\xi_n)\right|^p
 \le (MC_\alpha)^p.
\]

### How to discharge the deterministic bound

Use the existing **population core theorem at temperature \(\alpha>0\)**. A finite limit of the scaled nonnegative population integral gives eventual boundedness. A full uniform bound only needs a finite-initial-segment argument if the assembly theorem actually demands it.

This is preferable to proving an explicit radial-density upper bound.

### What the certificate does—and does not—supply

The audit should identify these separately:

1. the exact deterministic integral representation;
2. bounded amplitude/localisation;
3. the population scaled-mass bound at \(\alpha\);
4. joint measurability of the random chart field;
5. its uniform pointwise MGF bound.

A `TanCertificate` may supply 1–3. It should **not silently be credited with 4–5**.

For an original chart integral, transport through `ExactBoxCoreCertificate` only where its measure identity is available. This does not construct that certificate.

### Why I would not target the proposed pathwise \(D_\rho(\xi_n)\) bound first

There are two genuine obstructions:

- the finite-\(n\) field generally depends on the radial/normal variables, whereas the limiting coefficient sees a face field;
- the finite-\(n\) radial pushforward contains logarithmic factors. Their normalised ratios need not have a uniform constant bound near radial zero.

Neither obstruction affects the weighted-measure proof above.

A radial-constant special case may admit a \(D_\rho\)-comparison, but it is a specialisation, not the main interface to pursue.

### Traps

- \(A_n\) at \(n=0,1\), especially when it contains powers of \(\log n\): formulate eventual statements first.
- The population theorem must concern the **same model weight**. Bounded amplitude permits replacing it by a positive envelope; it does not identify two unrelated integrals.
- Changing temperature must be justified. Prefer applying a theorem quantified over positive temperatures; do not infer it merely from integer asymptotics at one temperature.
- Do not assume bounded original observations automatically give bounded **normalised chart coefficients**. That is a separate analytic/statistical input.

**Stop rule:** if the certificate lacks the required population envelope theorem, add that precise deterministic corollary. If the chart-field MGF is unavailable, land the conditional theorem and retain that named hypothesis. No resolution or unit-removal work in this unit.

---

## 3. Close the expectation assembly for this certified subclass

**Priority: high. One unit.**

The target should explicitly combine:

- certified finite-\(n\) core representations;
- the field-limit hypothesis already used for convergence in distribution;
- the full-domain pointwise MGF bound;
- Units 1–2;
- the existing expected-remainder theorem.

A schematic declaration:

```lean
tendsto_integral_scaled_assembly_of_certified_subgaussian_cores
```

with conclusion
\[
\mathbb E[A_nZ_n]\longrightarrow \mathbb E L,
\]
where \(L\) is the already-certified limiting assembled coefficient.

This removes the **abstract uniform-\(p\)-moment hypothesis** for that subclass. It does not remove the field-limit or geometric-certification hypotheses.

### Finite sums

For finitely many cores \(Y_{j,n}\), the elementary bound
\[
\left|\sum_{j=1}^JY_{j,n}\right|^p
 \le J^{p-1}\sum_{j=1}^J|Y_{j,n}|^p
\]
is sufficient. Use Minkowski only if the existing API makes it shorter.

For positive mixtures, a disjoint-union version of Unit 1 is also possible, but not necessary.

An \(L^1\)-negligible remainder is enough to transfer convergence of expectations. **Do not demand a \(p\)-moment estimate on the remainder unless the existing assembly interface truly needs one.**

### Exact limiting expectation

Where the limit is a compact-base Gaussian coefficient, combine with CL:
\[
\mathbb E D_\rho(G)
 =\Gamma(\lambda)\int_K
 [\beta(1-\beta C(x,x)/2)]^{-\lambda}\,d\rho(x).
\]

For constant diagonal \(c\),
\[
\mathbb E D_\rho(G)
 =D_\rho(0)(1-\beta c/2)^{-\lambda}.
\]

This is the appropriate paper-facing result: **an annealed asymptotic for certified sub-Gaussian cores**, not merely an abstract UI lemma.

### Non-claims

- No construction of the empirical field limit.
- No unconditional theorem from the original statistical model.
- No replacement of \(\mathbb E\log D\) by \(\log\mathbb ED\).
- No next-order correction.
- No positivity assertion for a signed assembled limit without its own hypothesis.

**Stop rule:** one end-to-end corollary, plus the small finite-sum lemma if needed. Once it compiles, the campaign’s main objective is met.

---

## 4. Finish the Gaussian adapter without making Gram factorisation the objective

**Priority: medium. One capped unit.**

### First deliverable: scalar and linear-combination laws

For a Borel random element \(G:\Omega\to C(K,\mathbb R)\) with Gaussian pushforward law, prove that every finite linear combination of evaluations is Gaussian.

Assuming centring and covariance certificates,
\[
\mathbb E G(x)=0,\qquad
C(x,y)=\mathbb E[G(x)G(y)],
\]
the target is
\[
\sum_i\theta_iG(x_i)
 \sim N\!\left(0,\sum_{i,j}\theta_i\theta_j C(x_i,x_j)\right).
\]

Proposed names:

```lean
gaussian_linearCombination_eval_of_isGaussian
gaussian_eval_of_isGaussian
```

The variance expression is nonnegative by its identification with the integral of a square. No matrix square root is needed for this fact.

### Inputs

- `ContinuousMap.evalCLM`.
- Finite linear combinations of continuous linear maps.
- The pushforward/projection API for `IsGaussian`.
- CLIII’s \(L^2\) result to justify the mean and covariance integrals.
- Uniqueness of a real Gaussian law from its mean and variance.

I am confident about `ContinuousMap.evalCLM` and the Fernique input already used. I would inspect the exact `IsGaussian` projection and Gaussian-law characterisation names in this pinned Mathlib rather than guess them.

### Can this finish `GaussianField.ofIsGaussian`?

Possibly, without changing `gaussianVector`:

- if the existing finite-dimensional target law already has a theorem identifying all linear projections, compare characteristic functions/projections;
- identify the pushforward law of the evaluation map with that target law.

A Gram factor is needed to **construct a particular covariance-model representation**, not intrinsically to show that evaluations of a Gaussian Banach random element are jointly Gaussian.

Keep the current record and definition unless there is a compelling local reason to change them.

### Traps

- `IsGaussian` does not supply centring.
- The covariance certificate still has content. Replace a distributional certificate by mean/covariance certificates; do not claim it vanished.
- Singular covariance is legitimate.
- Banach Gaussianity does not construct a law from an arbitrary kernel.

**Stop rule:** land scalar/linear-combination laws. Spend at most one additional API investigation on finite-dimensional law identification. If that route is blocked, defer the full constructor improvement; do not begin a spectral-theorem library project.

**Verdict on 1B:** worthwhile at this cap, but lower priority than Units 1–3.

---

## 5. Bilocal critical boundary by iterated one-dimensional substitutions

**Priority: optional. One unit.**

I would not start with a two-dimensional linear-equivalence change of variables.

Assuming the intended integral is
\[
I_\lambda(a,b,h)
 =\int_0^\infty\!\!\int_0^\infty
 t^{\lambda-1}s^{\lambda-1}
 e^{-at-bs+h\sqrt{ts}}\,ds\,dt,
\]
the precise boundary theorem is
\[
a,b>0,\quad\lambda>0,\quad h=2\sqrt{ab}
\quad\Longrightarrow\quad
I_\lambda(a,b,h)<\infty
\iff \lambda<\tfrac14.
\]

Proposed declaration:

```lean
bilocal_lintegral_lt_top_iff_of_critical
```

### Cleaner route

At the boundary the exponent is
\[
-(\sqrt{at}-\sqrt{bs})^2.
\]
For each \(t>0\), substitute
\[
s=(a/b)t z.
\]
Tonelli then gives, in the extended nonnegative sense,
\[
I_\lambda
 =(ab)^{-\lambda}
 \int_0^\infty z^{\lambda-1}
 \left(\int_0^\infty
       y^{2\lambda-1}e^{-y(1-\sqrt z)^2}\,dy\right)dz.
\]
Away from \(z=1\), the inner Gamma integral yields
\[
I_\lambda
 =\Gamma(2\lambda)(ab)^{-\lambda}
 \int_0^\infty z^{\lambda-1}|1-\sqrt z|^{-4\lambda}\,dz,
\]
with the value at \(z=1\) handled a.e.

Now split into:

- near \(0\): comparable to \(z^{\lambda-1}\);
- near \(1\): comparable to \(|z-1|^{-4\lambda}\);
- near infinity: comparable to \(z^{-\lambda-1}\).

Only the middle region imposes a new condition: \(4\lambda<1\).

### Inputs

- Tonelli for `lintegral`.
- One-dimensional positive-scaling substitution.
- The existing Gamma integral.
- Existing power-integrability tests.
- The identity
  \[
  |1-\sqrt z|=\frac{|1-z|}{1+\sqrt z}.
  \]

The exact scaling-substitution lemma names need checking. This route should avoid `Measure.addHaar_image_linearMap` entirely.

### Traps and scope

- Require \(a,b>0\). Degenerate endpoints are different cases.
- Work with `lintegral` until finiteness is established.
- At \(z=1\), the inner integral is infinite. A null singleton does not force divergence; the neighbourhood singularity does.
- This classifies this bilocal kernel, not arbitrary continuum critical moments.

**Stop rule:** prove the finiteness iff. No exact beta-function value, unequal-index generalisation, or quantitative critical truncation theorem in this unit.

**Verdict:** worthwhile as a compact paper-closing theorem, but not ahead of the expectation bridge.

---

## 6. Paper audit and release

**Priority: mandatory bookkeeping; no speculative theorem development.**

### What is specifically dot-ready

Without seeing the sources, I cannot identify actual un-dotted sentences or labels. These are the descriptions I would search for and certify:

| Paper statement by description | Status |
|---|---|
| A measurable \(C(K)\)-valued field has jointly measurable evaluations; its compact-base coefficient is measurable | Already supplied by CXLIX |
| A Gaussian Banach law supplies the second sup-norm moment required by the field record | Already supplied by CLIII, **not** the centred finite-dimensional law certificate |
| Pointwise sub-Gaussian MGFs imply the stated compact-base \(p\)-moment bound | Already supplied by CXLIX |
| Exact annealed compact-base denominator, constant-diagonal inflation, and positive-measure overcritical divergence | Already supplied by CL |
| Sharp scalar two-sided growth up to constants | CLI plus CXLVI |
| Scalar critical-line finiteness iff | CLII |
| Identification of both population power–log exponents for the same integral | CLIV |
| Identification of the empirical logarithmic exponent after population comparison | CLIV, for \(\lambda\) only |
| Finite-\(n\) certified-core uniform moments from full-chart MGFs | Dot only after Unit 2 |
| Annealed assembly with that abstract moment hypothesis discharged | Dot only after Unit 3 |
| Bilocal boundary iff | Dot only after Unit 5 |

Two easy audit traps:

- `S_\lambda(a) \asymp a^{2\lambda-1}e^{\beta a^2/4}` is formalised; the **exact asymptotic ratio constant** in the numerical report is not established by two-sided bounds.
- A numerical check of an interpolation or integration-by-parts identity is not its theorem citation. Keep numerical evidence and formal support separately labelled.

### Next-order theory

**Still premature as a campaign priority.** The new work makes this sharper, not weaker: there is now a short route to closing an important leading-order expectation interface.

Reconsider next order only after an explicit certified class has an end-to-end expectation theorem, and after naming the extra hypotheses for the proposed correction: coefficient-family control, remainder rates, and the relevant non-cancellation condition. Do not extrapolate a next-order result from leading-order UI.

---

## Text corrections before pushing

I would make the following changes now, then ask the user to authorise the Overleaf push. **Do not hold the present accurate results hostage to Units 1–5.**

### 1. Broaden the named remaining moment interface

Replace wording suggesting that the specific pathwise domination is necessary by:

> The expectation assembly still requires uniform integrability of the scaled finite-\(n\) cores. One sufficient input is domination by the compact-base coefficient as above. An alternative is a direct moment bound using the finite-\(n\) population weight; neither finite-\(n\) application is established here.

After Units 1–3 land, replace the last sentence with the certified-subclass theorem and its full-chart MGF hypothesis.

### 2. Distinguish the two random-field domains

Add:

> A pointwise exponential-moment bound for the limiting face field is not, by itself, a bound for the finite-\(n\) field throughout a chart.

This is the most important new qualification.

### 3. State the UI temperature condition explicitly

> The displayed \(p\)-moment estimate yields uniform integrability when it is available for some \(p>1\); with this sufficient bound, such a choice requires \(\beta c<2\).

Do not describe the \(p=1\) result alone as supplying UI.

### 4. Keep the Gaussian adapter accurately scoped

Prefer:

> A Borel Gaussian law on \(C(K)\) supplies the sup-norm second moment by Fernique. The present constructor additionally takes the centred finite-dimensional evaluation-law certificate.

After Unit 4, say exactly which part has been replaced by mean/covariance certificates.

### 5. Preserve the annealed/quenched distinction

Keep the three quantities already separated:
\[
\log D_\rho(0),\qquad \mathbb E\log D_\rho(G),\qquad
\log\mathbb ED_\rho(G).
\]

Where the relevant finiteness hypotheses hold, Jensen gives an inequality between the last two—not an identification. Also retain the statement that the annealed first moment depends only on the covariance diagonal.

For the “strictly subcritical everywhere” first-moment statement, keep the ambient compactness and continuity assumptions visible; pointwise strictness alone on an arbitrary measurable base need not give integrability.

### 6. Tighten exponent-identification prose

> The pair is identified by comparing two order descriptions of the same population integral. The empirical logarithmic limit transports the power exponent only.

In Lean-facing explanations, avoid ambiguity between natural subtraction \(m-1\) and real subtraction; use the existing \(m\ge1\) hypothesis when translating.

### 7. Label computations as checks

Call the reported quadrature and MC results **consistency checks**. The interpolation agreement at approximately two standard errors is not strong numerical confirmation of an exact value, and the observed sharp-ratio limit is not yet a formal asymptotic-equivalence theorem.

---

## Campaign stop rule

**Mandatory success:** Units 1–3, or their precise conditional versions with the missing full-chart MGF input explicitly exposed.

**Optional budget:** at most one unit each for the Gaussian adapter and bilocal boundary.

**Do not open:** Gram-factor infrastructure, kernel-to-Gaussian construction, analytic unit removal, certified-presentation construction, or next-order assembly.

The highest-value next headline is:

> **Uniform moments—and hence annealed assembly—for certified finite-\(n\) sub-Gaussian cores, using bounded scaled population mass at a reduced temperature.**

That closes a real interface left by #59 without pretending to close the geometric or empirical-process bridges.
