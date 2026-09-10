## Recommendation

**Make the next programme a bounded attempt to remove the sample-datum limit hypothesis—not another moment campaign.** CLX–CLXI have closed the two advertised moment inputs for this subclass. The remaining analytic issue is now sharply isolated.

The important observation is:

> A deterministic estimate \(\|X_n\|\lesssim\sqrt n\) does not obstruct using a mass-dependent remainder estimate if the sample data already converge in law in a fixed \(\ell^1\) space. That convergence makes their norms bounded in probability.

Thus there is a credible route to the limit theorem. The obstruction, if any, is **uniformity of the deterministic remainder on bounded—or compact—sets of data**, not the growing deterministic bound itself.

Based on the descriptions supplied, the closest existing statement is **CXVIII’s joint convergence of a finite vector of canonical coefficients at the sample datum**, combined with its \(\ell^1\)-valued sample-data convergence. CXLVIII’s Slutsky assembly is the final transfer mechanism; it does not itself supply the missing approximation.

Below, proposed theorem names and signatures are schematic. I am not claiming to have checked their existing argument order or the repository’s precise convergence API.

---

# Ranked programme: six units

Units 1–4 are the main line. Unit 5 is optional. Unit 6 is mandatory bookkeeping.

## 1. Localise the deterministic leading approximation using tightness

### Target

First extract a **locally uniform leading approximation**, not a new expansion.

Let:

- \(E\) be the fixed data space containing the sample data;
- \(B_n:E\to\mathbb R\) be the globally scaled box core, or finite assembled core;
- \(F:E\to\mathbb R\) be its leading coefficient.

A useful deterministic interface is:

\[
\forall R>0,\ \forall\varepsilon>0,\quad
\forall^\infty n,\quad
\forall x,\ \|x\|\le R\Longrightarrow |B_n(x)-F(x)|\le\varepsilon.
\tag{LU}
\]

Alternatively, expose the actual estimate:

\[
\forall R>0,\ \exists C_R<\infty,\ \exists N_R,\quad
n\ge N_R,\ \|x\|\le R
\Longrightarrow |B_n(x)-F(x)|\le C_Rq_n,
\qquad q_n\to0.
\]

The index threshold must be uniform in \(x\) on the chosen set.

Then prove a reusable probability lemma:

```lean
-- Schematic; probability convergence API to be chosen locally.
scaled_error_tendstoInProbability_of_norm_boundedInProbability
    (hX : norms of X_n are bounded in probability)
    (hlocal : locally uniform approximation of B_n by F on norm balls) :
    B_n (X_n ·) - F (X_n ·) → 0 in probability
```

In explicit tail form, the conclusion is

\[
\forall\varepsilon>0,\quad
\mathbb P\{|B_n(X_n)-F(X_n)|>\varepsilon\}\longrightarrow0.
\]

The proof uses only

\[
\mathbb P\{|B_n(X_n)-F(X_n)|>\varepsilon\}
\le \mathbb P\{\|X_n\|>R\}
\]

eventually in \(n\), followed by the bounded-in-probability choice of \(R\).

### Where to obtain the hypothesis

Inspect `boxTaylorTree_isBigO` and the estimates feeding it.

- If its constant is an explicit locally bounded function of data mass, package that dependence.
- If it is merely `∀ x, ... =O[...] ...` with an untracked existential constant and threshold, it does **not** imply (LU).
- If norm-ball uniformity is unavailable, uniformity on compact subsets is enough, together with tightness in the fixed Polish data space.

Infinite-dimensional closed balls are not compact. Do not identify these two routes.

### Mathlib inputs

- Continuous mapping for convergence in distribution, applied to `norm`.
- Boundedness in probability of a real sequence converging in distribution; alternatively tightness/Portmanteau.
- Elementary event inclusion and measure monotonicity.

I am not confident of the exact Mathlib names for the first two in this version. The elementary tail lemma can avoid a substantial excursion into the general tightness API.

### Cap and stop condition

**Cap:** one probability helper and one locally uniform leading estimate.

If obtaining the latter requires reconstructing the Taylor-tree proof or developing new all-orders machinery, stop this unit. Record the missing uniformity lemma explicitly and retain the limit hypothesis.

**Non-claim:** boundedness in probability does not supply moment bounds for a mass-dependent remainder. This unit proves an \(o_{\mathbb P}(1)\) error, not an \(L^1\) error.

---

## 2. Derive the sample-core distributional limit

### Target

For chart \(j\), let \(B_j(x)\) denote its **complete leading coefficient at its own scale**, including the box-radius, temperature and normalisation constants already present in the deterministic theorem.

At global scale \((\lambda,m)\), define

\[
F(x)=
\sum_{\substack{j:\lambda_j=\lambda\\m_j=m}} B_j(x_j).
\]

Charts with \(\lambda_j>\lambda\), or with \(\lambda_j=\lambda\) and \(m_j<m\), contribute zero at this scale.

Prove:

```lean
tendstoInDistribution_scaled_coreSum_sampleDatum
    (hjoint : joint sample-data / canonical-coefficient convergence)
    (hlocal : Unit 1 approximation)
    (hdom : all chart exponent pairs dominate the global scale) :
    A_n * coreSum_n(sampleDatum) ⇒ F(X∞)
```

Use CXVIII’s finite-vector canonical-coefficient convergence directly if it already gives convergence of the vector defining \(F\). There is no reason to reprove continuous mapping for those coefficients.

The proof is:

1. the leading coefficient vector converges jointly;
2. the scaled core minus its leading coefficient tends to zero in probability;
3. Slutsky gives the claimed limit.

### Essential jointness audit

Individual chart CLTs are not enough for the law of their sum. The charts are functions of the same observations and are generally correlated.

Use the existing joint sample theorem if it covers the required finite chart family. Otherwise package that finite family into one product/direct-sum data variable and verify the existing CLT hypotheses there. **Do not introduce independent Gaussian copies for the charts.**

Likewise, if the displayed data spaces vary syntactically with \(n\), first identify the fixed \(\ell^1\) ambient space in which CXVIII asserts convergence. Tightness is being used in that common space.

### Inputs

- Existing coefficient-vector convergence in `SampleExpansion`/the joint-sample chain.
- Unit 1.
- Existing CXLVIII distributional Slutsky assembly, or its underlying addition lemma.
- Existing exponent comparisons from CLX and the leading asymptotic chain.

### Traps

- Do not omit \(b_j\)-dependent constants by replacing \(B_j\) with a raw coefficient symbol.
- A cancellation in \(F\) gives a possibly zero limit. It does not license a next-order theorem.
- There is no need to control the remainder by substituting the crude \(\sqrt n\) norm bound.

**Stop rule:** if joint convergence is not covered by the existing finite-family infrastructure, state precisely the missing joint hypothesis; do not start a new Banach CLT campaign.

---

## 3. Identify the limiting coefficient as a Gaussian compact-base functional

This is a **law-identification unit**, not a new Gaussian-field construction.

### First target: reconstruct the field from the existing Gaussian data law

Let \(\nu\) be the centred \(\ell^1\) Gaussian limit and let

\[
T_j:E\longrightarrow C(K_j,\mathbb R)
\]

be the continuous linear reconstruction of the leading face phase. Set \(G_j=T_jZ\), \(Z\sim\nu\).

The fixed amplitude datum contributes to the deterministic amplitude; its zero-phase property ensures it does not shift \(G_j\).

Use CLIX to obtain the relevant `GaussianField` records from:

- the pushed-forward Banach Gaussian law;
- centring;
- covariance certificates.

For joint quantities, the covariance must be the **joint chart kernel**

\[
C_{ij}(u,v)
=\operatorname{Cov}\!\left(
  \xi_{Y^{(i)}_0}(u),\xi_{Y^{(j)}_0}(v)
 \right),
\]

with centring included where the observation fields are not already centred.

CLIX removes the separate finite-dimensional-law certificate. It does not remove the mean and covariance certificates.

### Second target: the exact bridge statement

The bounded statement to seek is an identity of functionals, followed by an identity of laws:

\[
F(Z+A)=\sum_j\kappa_jD_{\rho_j}(G_j)
\quad\text{a.s.},
\tag{ID}
\]

with only globally leading charts retained. Here the \(\kappa_j,\rho_j\), and the meaning of \(D_{\rho_j}\), must be the ones obtained from the existing leading-coefficient theorem—not newly chosen analogues.

Then:

```lean
map_limitingLeadingCoeff_eq_map_compactBaseFunctional :
    law (F (Z + A)) =
      law (∑ j, κ j * D (ρ j) (G j))
```

If an arbitrary \(L\) is already specified as the distributional limit of the same scaled core, uniqueness of the limit gives equality of its law with this law.

With integrability:

```lean
integral_limit_eq_integral_compactBaseFunctional :
    E[L] = E[∑ j, κ j * D (ρ j) (G j)]
```

This is equality of expectations through equality of laws; no coupling or almost-sure equality with the user’s \(L\) is required.

### Is this “the Gaussian quartet expectation”?

**Not automatically.** It is the Gaussian expectation of the identified leading functional. A quartet theorem applies only if its functional and hypotheses match that functional.

In particular:

- a first moment of a partition/denominator functional needs a first-moment averaging theorem;
- products, insertions and quotients require their corresponding identities and integrability conditions;
- Gaussianity plus covariance does not itself prove any of these functionals integrable.

For illustration, **if the existing convention is**

\[
D_\rho(G)=
\int_K w(u)\int_0^\infty
 t^{\lambda-1}e^{-\beta t+\beta\sqrt t\,G(u)}\,dt\,d\rho(u),
\]

then for nonnegative \(w\), Tonelli and the Gaussian MGF give

\[
\mathbb ED_\rho(G)=
\int_K w(u)\int_0^\infty
t^{\lambda-1}
e^{-[\beta-\beta^2C(u,u)/2]t}\,dt\,d\rho(u).
\]

Under a uniform positive lower bound on the bracket, this becomes the corresponding Gamma integral. For signed bounded amplitudes, first establish absolute integrability.

This is a **covariance-modified population-type integral**, not generally the original population coefficient at temperature \(\beta\). If \(C(u,u)\) varies, it is not even a single scalar temperature replacement. Actual normalisation constants must follow the repository’s definition of \(D_\rho\).

### Inputs and cap

- Existing continuous reconstruction into `C(K, ℝ)`.
- Preservation of Gaussian law by continuous linear maps; exact Mathlib name not asserted.
- `GaussianField.ofIsGaussianCertificates`.
- Existing compact-base first-moment/expectation bridge.
- Equality-of-law transport of integrals.

**Cap:** one reconstruction adapter, one functional identity, one law/expectation corollary. No new quotient, quartet or sharp-integrability classification.

---

## 4. Publish one end-to-end sample-datum theorem

If Units 1–3 succeed, add a single discoverable wrapper:

```lean
tendsto_integral_scaled_assembly_sampleDatum_gaussianLeading :
    E[A_n * (coreSum_n(sampleDatum) + Rem_n)]
      → E[∑ j, κ j * D (ρ j) (G j)]
```

Its assumptions should visibly separate:

1. **Existing sampling CLT hypotheses**, including the actual \(\ell^1\)-tail/summability conditions;
2. bounded phase observations, or the later sub-Gaussian replacement;
3. fixed zero-phase amplitudes with bounded amplitude mass;
4. positive temperature and an admissible \(p>1\), with \(p\beta M_0^2<2\);
5. domination of chart exponent pairs;
6. \(\mathbb E|A_n\mathrm{Rem}_n|\to0\);
7. the deterministic certified-box setup.

The scalar core-limit hypothesis should disappear **only if Unit 2 has actually discharged it**.

The wrapper is essentially Unit 2 plus CLXI plus Unit 3. Do not duplicate the moment proof.

If Unit 1 stops, the useful fallback theorem is instead:

> conditional on the stated core convergence in distribution and the Gaussian-functional law identification, the full scaled expectation converges to that Gaussian-functional expectation.

### Important boundary

Bounded phase observations used by Hoeffding do **not** by themselves establish the \(\ell^1\) CLT. Keep the existing CLT assumptions visible. Nor does this wrapper construct an `ExactBoxCoreCertificate` from the original geometric model.

---

## 5. Optional: replace bounded observations by uniform scalar sub-Gaussian evaluations

**Worth one adapter unit, but rank it below closing the limit.**

The right abstraction is not an unspecified “sub-Gaussian \(\ell^1\) random variable.” It is:

\[
\forall j,\ \forall u\in[0,1]^{d_j},\quad
\xi_{Y^{(j)}_0}(u)-\mathbb E\xi_{Y^{(j)}_0}(u)
\text{ has sub-Gaussian MGF proxy }c_j,
\]

with \(c_j\le c\), uniformly over the full box.

Target:

```lean
lintegral_exp_phase_sampleDatum_le_of_hasSubgaussianMGF :
    E₊[exp (t * ξ_n(u))] ≤ exp (c * t^2 / 2)
```

and then:

```lean
tendsto_integral_scaled_assembly_sampleDatum_of_subgaussian :
    -- CLXI conclusion, with p * β * c < 2
```

### Inputs

`HasSubgaussianMGF.sum` is the natural supplied API. Check the exact scaling and parameter convention in Mathlib: whether its parameter is a variance proxy or its square must not be guessed. Also check the independent-family hypothesis expected by `sum`.

One can avoid the \(n=0\) normalisation issue in the generic sum lemma by proving the result for \(n\ge1\), then handling the zero index separately.

### Traps

- Independence is over sample index, not over spatial points or charts.
- A pointwise proxy \(c(u)\) without a uniform bound does not feed the current theorem unchanged.
- Scalar evaluation integrability is not automatically Bochner integrability of the \(\ell^1\)-valued observation.
- This extension weakens the MGF hypothesis only. It does not manufacture the existing data CLT or its tail assumptions.

**Cap:** MGF adapter plus one assembly corollary. No Banach sub-Gaussian theory.

---

## 6. Paper and theorem-map closure

Do this whether or not the limit-closing attempt succeeds.

### A. Reduced-temperature sentence

The sentence

> “The uniform moment reduces to a bound on the deterministic population integral at the reduced temperature”

is accurate **as a description of the generic proof step**, assuming the other hypotheses are displayed. Standing alone, it understates the present achievement and can sound like an equivalence.

Prefer:

> The deterministic-weight estimate bounds the \(p\)-th moment by the \(p\)-th power of a population mass at the reduced temperature \(\alpha=\beta(1-p\beta c/2)>0\). For dominated monomial boxes, the required population bound follows from the proved monomial asymptotics. For bounded i.i.d. sample data, Hoeffding’s inequality supplies the full-box exponential-moment hypothesis.

“Bounds” is better than an unqualified “reduces”: this is a sufficient estimate, not a sharp moment classification.

Also remove stale “bounded random data” wording from descriptions of the final chain where the implemented hypothesis is now **bounded amplitude mass**. The sample datum need not have uniformly bounded full data norm.

### B. Suggested table rows

| Interface | Current accurate wording |
|---|---|
| Uniform moments | Uniform \(p\)-th moments for dominated certified box cores under bounded amplitude mass and a full-box sub-Gaussian MGF bound; population bounds are derived. For bounded i.i.d. sample data, the MGF bound is supplied by Hoeffding. |
| Expectation assembly | Annealed sample-datum assembly theorem, conditional on convergence in distribution of the scaled core and vanishing scaled \(L^1\) remainder; finite-\(n\) moment inputs are discharged under the stated hypotheses. |
| Banach-law adapter | A supplied Banach Gaussian law with centring and covariance certificates determines the finite-dimensional Gaussian laws and yields a `GaussianField`; no Gaussian law is constructed from the kernel alone. |

Do not describe the second row merely as “uniform integrability assumed.” Conversely, do not erase its distributional-limit condition.

### C. Abstract wording now

Yes: **the mirror should now claim a conditional annealed sample-datum assembly theorem.** That is an established theorem with substantive finite-\(n\) inputs proved, not just an abstract conditional observation.

Suggested abstract insertion:

> For finite certified box cores generated by bounded i.i.d. phase observations and fixed amplitudes, we prove uniform moments of order \(p>1\) in an explicit sufficient temperature range. The proof combines a full-box Hoeffding bound with deterministic monomial asymptotics at a reduced temperature. Consequently, convergence in distribution of the scaled empirical core upgrades to convergence of expectations after addition of a remainder negligible in scaled \(L^1\).

Optional final qualification:

> The distributional limit and the geometric construction of the certified cores remain separate inputs.

The longer assumptions—dominated exponent pairs and the precise amplitude condition—belong in the introduction/theorem statement.

### D. Introduction wording now

> The sample-datum result does not infer finite-sample exponential moments from the limiting Gaussian field. Instead, it proves them directly from the sampling law, uniformly over the full box. Together with the deterministic reduced-temperature population estimate, this discharges the moment hypotheses needed to pass from an assumed distributional limit of the scaled core to its limiting expectation.

Then explicitly state:

\[
A_nZ_n^{\mathrm{core}}\Rightarrow L,\qquad
\mathbb E|A_n\mathrm{Rem}_n|\to0
\quad\Longrightarrow\quad
\mathbb E[A_n(Z_n^{\mathrm{core}}+\mathrm{Rem}_n)]
\to\mathbb EL,
\]

under the theorem’s sampling, amplitude, exponent and temperature assumptions.

### E. Honest phrasing of the “field limit”

For CLXI itself, call it:

> **the distributional limit of the scaled empirical core**

rather than simply “the field limit.” The hypothesis is scalar core convergence, not necessarily convergence of the whole spatial field.

Add:

> Existing results establish convergence of the sample data in \(\ell^1\), under the stated CLT hypotheses, and joint convergence of finite canonical-coefficient vectors. Passing from these coefficients to the \(n\)-dependent scaled core additionally requires a remainder estimate uniform on high-probability sets of data.

That identifies the precise remaining implication without falsely suggesting that no functional convergence has been proved anywhere.

### F. Non-claims update

Replace the overly broad final empirical clause by something like:

> No unconditional empirical fluctuation theorem from the original statistical model is claimed. The expectation theorem for bounded i.i.d. sample data uses certified box cores, an assumed distributional limit of the scaled core, and a scaled \(L^1\)-negligible external remainder; its full-box MGF and reduced-temperature population bounds are proved under the stated sampling, exponent and temperature conditions.

Keep the general moment hypotheses in the description of the more general abstract theorem, not as though they remain external for CLXI.

All Overleaf changes should remain local until authorisation to push.

---

# Global stop rule

End the campaign after these interfaces, not after a new geometric or Gaussian programme.

- **Success:** derive the core limit using tightness and locally uniform deterministic control; identify its leading Gaussian functional; invoke CLXI in one wrapper.
- **Honest partial success:** isolate the locally uniform approximation as the sole missing analytic bridge, retain the scalar core-limit hypothesis, and publish the already-proved conditional annealed assembly accurately.
- **Do not open:** geometric certification, analytic-unit removal, new \(\ell^1\) CLT hypotheses, sharp temperature classification, or post-cancellation corrections.

The decisive first task is therefore a narrow audit:

> Does `boxTaylorTree_isBigO` already contain enough controlled dependence on data mass to yield uniform leading asymptotics on each fixed mass ball?

If yes, the \(\sqrt n\) deterministic norm bound is a distraction: CXVIII’s tightness is the appropriate tool. If no, document that exact uniformity gap rather than calling the whole limit theorem an unexplained external input.
