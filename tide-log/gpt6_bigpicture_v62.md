## Recommendation

The main annealed programme is now complete **at the certified-core interface**. I would not open another asymptotic-order or geometric programme yet.

The next bounded programme should be:

1. **Audit and certify the sampling identity, including centring and sign.**
2. Remove boundedness from the Gaussian-functional identification.
3. Prove the full-box sub-Gaussian empirical MGF and moment bound.
4. Assemble the unbounded-observation annealed theorem.
5. Add the constant-face-variance corollary and a normal-location normalization check.
6. Close the paper and theorem-map interfaces.

Unit 1 is a release gate. Units 2–4 are worth doing now, particularly because genuinely Gaussian observations in the motivating normal models are not bounded. Stop after these six units.

I cannot inspect `prop:sampling` or the Lean declarations from the supplied excerpts. Thus I cannot certify that their signs currently agree. What follows gives the exact identities against which they must be checked.

---

## 1. First priority: centring is not an amplitude adjustment

### The decisive distinction

There are three different deterministic objects:

- the **population loss**, which determines the deterministic exponential phase;
- the **mean of the phase-observation coefficient vector**, which is subtracted when constructing the empirical fluctuation;
- the **amplitude**, which multiplies the exponential.

A zero-phase amplitude datum `A` is **not generally a carrier for the mean phase coefficients**.

If `E[c_γ b^{|γ|}]` are coordinates of the observation's mean phase datum, their proper place is in the population phase and in the centring subtraction. They cannot simply be put into the amplitude coordinates of `A`.

Indeed, leaving a nonzero mean in an uncentred sample datum produces
\[
n^{-1/2}\sum_{i<n}Y_i
=
n^{-1/2}\sum_{i<n}(Y_i-EY_0)+\sqrt n\,EY_0.
\]
No fixed datum `A` absorbs the last term. Exponentiating a deterministic mean contribution into an amplitude would generally create an **\(n\)-dependent amplitude**, outside the stated theorem.

### The algebra the note must satisfy

Let \(g(x,u)\) be the chart loss observable, and set
\[
K(u)=E[g(X_0,u)],\qquad
\zeta_n(u)=n^{-1/2}\sum_{i<n}\bigl(g(X_i,u)-K(u)\bigr).
\]
Then, for \(n>0\),
\[
\sum_{i<n}g(X_i,u)=nK(u)+\sqrt n\,\zeta_n(u).
\]
Consequently, if the note defines \(\xi_n=-\zeta_n\),
\[
-\beta\sum_{i<n}g(X_i,u)
=
-\beta nK(u)+\beta\sqrt n\,\xi_n(u).
\tag{S}
\]

For a factored loss \(g(x,u)=\rho(u)q(x,u)\), the corresponding identity is
\[
\sum_{i<n}g(X_i,u)
=
nK(u)-\sqrt n\,\rho(u)\xi_n(u),
\]
where now
\[
\xi_n(u)
=
-n^{-1/2}\sum_{i<n}\bigl(q(X_i,u)-E q(X_0,u)\bigr).
\tag{SF}
\]

**Check whether `prop:sampling` uses the fluctuation of \(g\), of \(q\), or of its negative.** These are not interchangeable definitions.

In particular:

- If `phaseObs` represents \(q\), the centred sample phase represents \(\zeta_n\), not \(\xi_n\).
- If `phaseObs` represents \(-q\), it represents \(\xi_n\).
- A third convention is possible if the model core already uses the opposite sign in its phase argument.

The sampling identity must decide this; the limiting first moment cannot. **Gaussian symmetry can conceal a sign error in the first-moment formula while leaving the finite-sample identity and joint statements wrong.**

### Unit 1 — Lean deliverables

The following are proposed theorem names, not claims about existing identifiers.

1. **Evaluation commutes with the Bochner mean**
   ```lean
   phaseEval_mean :
     phaseEvalCLM u (∫ x, phaseObs x ∂P)
       = ∫ x, phaseEvalCLM u (phaseObs x) ∂P
   ```
   under the actual integrability hypotheses.

2. **Exact centred evaluation**
   ```lean
   phaseEval_sampleDatum :
     phaseEvalCLM u (sampleDatum n ω)
       = (Real.sqrt n)⁻¹ *
           ∑ i ∈ Finset.range n,
             (phaseEvalCLM u (phaseObs (X i ω))
               - ∫ x, phaseEvalCLM u (phaseObs x) ∂P)
   ```
   with the repository’s actual sample indexing and `hA`. If sample data and `A` are added separately, state this for their sum instead.

3. **Amplitude unchanged**
   ```lean
   amplitude_sampleDatum_add :
     etaField (centeredSampleDatum n ω + A) u = etaField A u
   ```
   using the zero-amplitude property of the observations.

4. **Sampling/core compatibility:** an exact identity, before limits or expectations, identifying the paper’s \(\xi_n\) with either the sample phase or its negative, and identifying the resulting exponential with the certified box core.

Use linearity, finite-sum algebra, and commutation of continuous linear maps with Bochner integration. No new probability theorem is needed.

**Gate:** do not ship the claimed application to `prop:sampling` until the fourth statement is established. If only an abstract observation-to-core theorem is available, label the paper application as conditional on this compatibility identity.

---

## 2. Remove boundedness from CLXIV without constructing a new Gaussian theory

### Unit 2 — Gaussian functionals under \(L^2\) observations

The boundedness in the truncation argument is stronger than necessary.

Prove the analogue of
```lean
map_eq_gaussianReal_of_marginals
```
with
```lean
MemLp Y₀ 2 P
```
in place of the uniform norm bound, retaining the existing Gaussian marginal and tail certificates for `ν`:
\[
\nu.map\,L=N\!\left(0,\operatorname{Var}_P(L(Y_0))\right).
\]

The replacement proof is:
\[
L(T_FY_0)\longrightarrow L(Y_0)\quad\text{in }L^2,
\]
hence convergence of means, second moments, and variances. A valid dominating function is a constant multiple of \(\|Y_0\|^2\), rather than a constant.

Your existing coordinate certificate should also yield the needed Banach-valued \(L^2\) fact:
\[
\bigl\|\|Y_0\|_{\ell^1}\bigr\|_{L^2}
\le \sum_j\|(Y_0)_j\|_{L^2}.
\]
Use finite-coordinate Minkowski followed by monotone convergence/Fatou. Reuse this result if already present.

**Mathlib inputs:** `MemLp`, Bochner integration, \(L^2\) convergence/dominated convergence, and the existing characteristic-function proof ending in `Measure.ext_of_charFun`.

**Traps**

- Retain the existing strong measurability and probability-measure assumptions.
- If the marginal covariance is for centred observations, say so explicitly. Variance is unchanged by centring, but second moment is not.
- Do not replace the summable coordinate-\(L^2\) certificate by `MemLp Y₀ 2` as a sufficient condition for the \(\ell^1\) CLT.

**Non-claim:** still no need for a Banach-space `IsGaussian` instance.

---

## 3. Unit 5 is now worth doing—but use scalar, full-box sub-Gaussianity

### Unit 3 — Uniform sub-Gaussian empirical phase bounds

Use a variance-proxy parameter \(\kappa\ge0\), defined by the convention
\[
E\exp(tQ_u)\le \exp(\kappa t^2/2)
\quad(t\in\mathbb R),
\qquad
Q_u=\xi_{Y_0}(u)-E\xi_{Y_0}(u).
\tag{MGF}
\]

Require this for every \(u\) in the **full integration box**, not merely on the leading face.

The primary Lean statement should say that the normalized empirical phase has the same proxy:
```lean
hasSubgaussianMGF_empiricalPhase
```
schematically,
\[
n^{-1/2}\sum_{i<n}Q_u(X_i)
\quad\text{has sub-Gaussian proxy }\kappa,\qquad n>0.
\]

**Mathlib inputs:** `HasSubgaussianMGF` and `HasSubgaussianMGF.sum`; use the available scaling/composition lemmas after checking their exact signatures and parameter convention. Independence comes from the observations, not from the spatial evaluations.

The key analytic inequality, in the normalized core variable \(r\), is
\[
E\exp\!\left[-p\beta r^2+p\beta r\,\xi_n(u)\right]
\le
\exp\!\left[-p\beta
       \left(1-\frac{p\beta\kappa}{2}\right)r^2\right].
\tag{B}
\]

Then generalize the existing uniform moment theorem to
\[
p>1,\qquad p\beta\kappa<2.
\]

**Important normalization trap:** equation (B) uses the phase evaluation paired with the normalized quadratic core \(-\beta r^2\). If the observable is paired instead with \(-\beta c r^2\), the proxy must be correspondingly rescaled. Unit 1 must settle this normalization.

Also prove, or reuse,
\[
\operatorname{Var}(Q_u)\le\kappa.
\]
This must be the sharp proxy bound if the advertised threshold is to remain \(\beta\kappa<2\).

**Non-claims**

- No sub-Gaussian bound for the entire \(\ell^1\) norm.
- No automatic \(\ell^1\) CLT from scalar evaluation bounds.
- No independence across face points.
- No removal of the external remainder hypothesis.

---

## 4. Assemble, rather than rebuild, the unbounded theorem

### Unit 4 — Sub-Gaussian single- and several-chart wrappers

Combine Units 2–3 with CLXII–CLXV.

The single-chart conclusion is the existing annealed limit and identified face integral, with bounded observations replaced by:

1. the existing \(\ell^1\) CLT certificate;
2. the uniform full-box sub-Gaussian proxy \(\kappa\);
3. \(p>1\) and \(p\beta\kappa<2\);
4. the same zero-phase amplitude datum;
5. the same scaled \(L^1\)-negligible remainder.

For the first-moment identification, the variance bound becomes
\[
\sigma^2(v)\le\kappa.
\]
The Gaussian integration and Fubini proof then use
\[
\beta\left(1-\frac{\beta\kappa}{2}\right)>0.
\]

Preserve the distinction:

- **Gaussian first-moment identification:** \(\beta\kappa<2\).
- **The chosen \(L^p\)/UI argument:** \(p\beta\kappa<2\).

For finitely many charts, allow proxies \(\kappa_I\). A common \(p>1\) satisfying the inequalities for every chart is the clean wrapper; using \(\max_I\kappa_I\) is convenient but not intrinsic.

The expected leading sum is the finite sum of the chart face integrals. **Cross-chart covariance is essential to its joint law, but not to this first-moment sum.**

**Stop rule for Units 2–4:** no redesign of the CLT framework, no general Banach sub-Gaussian API, and no new geometric input. If a general-purpose abstraction becomes the main work, retreat to the scalar lemma actually needed here.

---

## 5. Constant variance: a useful corollary, not a new identification programme

### Unit 5 — Effective-temperature corollary and model sanity check

Let \(\mu_{\mathrm{face}}\) be the weighted residual face measure used by CLXV. Assume
\[
\sigma^2(\pi u)=v_0
\quad\mu_{\mathrm{face}}\text{-a.e.},
\qquad \beta v_0<2.
\]
Then prove
```lean
integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance
```
with conclusion
\[
E_\nu[C_\beta^b(Z+A)]
=
C_{\beta_{\mathrm{eff}}}^b(A),
\qquad
\beta_{\mathrm{eff}}=\beta(1-\beta v_0/2),
\]
where the right side is explicitly the **zero-phase population coefficient with the same geometric data and amplitude**.

Almost-everywhere constancy suffices; do not require pointwise constancy gratuitously. Nor should you state an “if and only if”: a particular signed amplitude can produce accidental integral equalities.

For finitely many charts, constant variance on each leading face gives chart-specific effective temperatures. A single effective temperature for the assembled coefficient requires a common variance, absent further identities.

### Normal-location check

For the standard negative-log likelihood ratio in \(X\sim N(0,1)\),
\[
g_a(X)=\frac{a^2}{2}-aX.
\]
Thus
\[
K(a)=a^2/2,\qquad
\sum_{i<n}g_a(X_i)=na^2/2-a\sum_{i<n}X_i.
\]

If the normalized core coordinate is \(\rho=a/\sqrt2\), its phase is
\[
\xi_n=\sqrt2\,n^{-1/2}\sum_{i<n}X_i,
\]
with variance \(2\), not \(1\). This is only a normalization check—not an assertion about the paper’s convention—but it is exactly the sort of factor that the `N(x₀x₁,1)` example must verify.

This example also explains why the sub-Gaussian extension has immediate value. It does **not** certify the resolution presentation, localization, or remainder.

---

## 6. Paper closure and a hard stop

### Abstract: recommended empirical paragraph

> For bounded i.i.d. chart observations satisfying an \(\ell^1\) central-limit certificate, we derive the distributional limit of the scaled empirical core for one or finitely many charts. Uniform moment bounds yield convergence of expectations after addition of a scaled \(L^1\)-negligible remainder. We identify the limiting expectation as a covariance-modified leading face integral: the temperature is replaced pointwise by \(\beta(1-\beta\sigma^2/2)\), and by a single scalar effective temperature when the evaluation variance is constant on the contributing face. These results are conditional on the certified chart-core representation and the stated remainder estimate.

After Unit 4, replace the opening condition by:

> For i.i.d. chart observations satisfying an \(\ell^1\) central-limit certificate and a uniform full-box sub-Gaussian bound, …

Keep the strict temperature/moment condition in the theorem and nearby introductory statement.

Yes: replace “derived for a single chart” by “derived for one or finitely many charts.” Yes: mention the identified expectation. That is now a principal result, not unfinished identification work.

### Introduction: centring paragraph

Insert the following **only after Unit 1 confirms the convention**:

> The empirical phase is centred. Writing \(\zeta_n\) for the normalized centred fluctuation of the chart observable, our sampling convention is \(\xi_n=-\zeta_n\). The population mean is retained in the deterministic population phase, so that the empirical exponent splits exactly into the population exponent and the centred fluctuation term. The deterministic datum \(A\) supplies the amplitude and has zero phase; it does not absorb an uncentred mean phase.

Immediately display the actual version of (S) or (SF), with the paper’s factors and notation.

If the observable map represents \(\zeta_n\), explicitly state that the core receives its negative. Do not leave this to Gaussian symmetry.

### Interface table

I would split the current expectation row:

| Interface | Supplied | Still external / not asserted |
|---|---|---|
| Empirical sampling | Exact centred coefficient/evaluation identity, including sign—once Unit 1 lands | Original-model-to-certified-core compatibility unless separately proved |
| Distributional assembly | Single- and finite-chart scaled-core limits from the joint \(\ell^1\) sample-data limit | CLT/tail certificates and certified chart data |
| Annealed assembly | Convergence of expectations under the moment bound | Scaled \(L^1\)-negligibility of the external remainder |
| First-moment identification | Covariance-modified face integral; constant-variance corollary | No general equality with the population coefficient at the original temperature \(\beta\) |

The last column should not describe equality at the original temperature as a merely missing proof. **It is generally a different quantity.**

Apply the same qualification in the mirror.

### Non-claims and historical headlines

Two updates are needed:

1. Replace the blanket phase-field non-claim with:
   > No empirical phase-field CLT from a scalar CLT alone, or without the stated \(\ell^1\) tail and representation hypotheses.

   If the represented field map into the intended function space is already continuous, the corresponding field convergence is a continuous-mapping corollary. Do not retain a blanket denial inconsistent with the supplied \(\ell^1\) result.

2. Mark the Gaussian-identification non-claims in CLXII–CLXIV as **historically superseded by CLXIV–CLXV**. Preserve verbatim historical rows if desired, but add current-status annotations.

Keep the geometric and remainder non-claims. Update “bounded” only after the sub-Gaussian wrappers land.

Add the new modules to the reading order; the present empirical chain should no longer end before `SampleDatumLimit`, `JointSampleLimit`, `L1GaussianFunctional`, and `LeadingCoeffGaussianMoment`.

No push without authorization.

---

## What not to open next

- **Next logarithmic order:** defer. The natural stochastic statement subtracts the leading coefficient evaluated at the *current sample datum*. Replacing it by a limiting random coefficient at logarithmic accuracy requires more than weak convergence. Deterministic two-term uniformity does not supply a coupling or convergence rate.
- **Cancellation:** a zero assembled leading coefficient still gives the current zero limit; it does not identify the next scale.
- **Geometric bridge:** keep closed. Nothing here removes its analytic-unit, localization, measure-identity, or certificate-construction obligations.
- **Gaussian Banach infrastructure:** unnecessary for this programme.

### Final stop rule

Stop once the sampling identity is exact, the bounded theorem is recovered as a special case of the sub-Gaussian wrapper, the constant-variance corollary is normalization-checked, and both papers state the same interface.

If Unit 1 fails, stop earlier: repair the sign/centring connection and restrict the application claim. That is more important than every additional theorem in this list.
