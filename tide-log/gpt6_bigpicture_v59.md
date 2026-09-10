## Recommendation

Make #59 a **“Gaussian-law inputs → uniform integrability → honest empirical expectations”** campaign, not a next-order campaign.

The most valuable new observation is that **pointwise sub-Gaussian bounds can give uniform \(L^p\) bounds for the leading compact-base coefficient directly**. This addresses a genuine missing hypothesis in CXLVIII; proving more moments of the Gaussian limit does not.

I recommend **six committed units and one expendable unit**, ranked below. I would not begin \(1/n\) corrections this round.

Two corrections should guide the whole campaign:

1. **The displayed compact-base Jensen bound is a \(p\ge1\) statement.** For \(0<p<1\), its direction reverses. Audit the note’s real-\(p\) mixture proof accordingly; the finite-mixture theorem can still hold, but needs subadditivity in that range.
2. **`IsGaussian` plus covariance does not specify a centred law.** The Gaussian-field constructor must include zero mean, or define a centred field explicitly.

I cannot identify additional paper labels reliably without the files. Below I distinguish concrete dot candidates from statements that still need a bridge.

---

# Unit 1 — Canonical compact Gaussian laws and Fernique discharge

### Target

Provide a constructor from a **centred Gaussian Borel probability measure on \(C(K,\mathbb R)\)** to the existing `GaussianField` interface.

Use the canonical probability space first:

```lean
Ω := C(K, ℝ)
P := μ
G := id
```

with compact metric \(K\), a Gaussian probability measure \(\mu\), and centring
\[
\int f(x)\,d\mu(f)=0 \qquad(x\in K).
\]

There are two useful constructors.

### 1A. Cheap constructor: discharge only the sup-norm moment

Keep the finite-dimensional-law fields supplied, but replace the explicit moment hypothesis by Gaussianity of the \(C(K,\mathbb R)\)-valued law.

Schematic target:

```lean
integrable_sq_norm_of_isGaussian :
  Integrable (fun f : C(K, ℝ) => ‖f‖ ^ 2) μ
```

Then provide a pullback version for a measurable \(G:\Omega\to C(K,\mathbb R)\) with law \(\mu\).

**Yes:** `IsGaussian.memLp_id` at exponent \(2\) is exactly the right mathematical input. Use it rather than reproving Fernique. `IsGaussian.exists_integrable_exp_sq` gives a stronger optional corollary, not a prerequisite.

### 1B. Complete constructor: derive the finite-dimensional laws

Define
\[
C_\mu(x,y)=\int f(x)f(y)\,d\mu(f).
\]

Prove:

* continuity of \(C_\mu\), by dominated convergence with dominator \(\|f\|_\infty^2\);
* symmetry;
* finite PSD:
  \[
  \sum_{ij}v_iv_jC_\mu(x_i,x_j)
  =\int\Bigl(\sum_i v_i f(x_i)\Bigr)^2\,d\mu(f)\ge0;
  \]
* each finite evaluation map is a continuous linear map;
* its pushforward is centred Gaussian with covariance `kernelMatrix`;
* a real Gram factor \(A\) exists, including singular covariance matrices;
* equality with the existing `gaussianVector A` follows from Gaussian uniqueness by mean and covariance.

Suggested endpoint:

```lean
GaussianField.of_centeredGaussianLaw
```

and, separately,

```lean
GaussianField.of_hasLaw_centeredGaussian
```

### Mathlib inputs

Confident:

* `ProbabilityTheory.IsGaussian`
* `IsGaussian.memLp_id`
* `IsGaussian.exists_integrable_exp_sq`

Also needed, but inspect exact names:

* Gaussian pushforward under continuous linear maps;
* uniqueness of finite-dimensional Gaussian measures from mean and covariance;
* real PSD matrix factorisation/square root;
* continuous-linear evaluation maps on `ContinuousMap`.

Do **not** budget against an assumed theorem named `Matrix.PosSemidef.sqrt` until checking the actual API.

### Traps and non-claims

* Gaussianity is not centring.
* Declare the Borel measurable structure on the sup-norm space explicitly.
* Do not silently replace a process with measurable evaluations by a Borel random element without proving the upgrade.
* This constructs the **record from a Gaussian law**, not a Gaussian law from an arbitrary PSD kernel.
* No Kolmogorov extension or continuity theorem is claimed.

### Stop rule

If finite-dimensional Gaussian uniqueness or matrix factorisation becomes infrastructure-heavy, land 1A immediately. Keep the existing evaluation-law certificate in 1B; do not let that block the rest of the campaign.

---

# Unit 2 — Compact-base moments and the exact annealed denominator

This is the compact-base completion with the best paper payoff.

Let
\[
D_\rho(g)=\int_K S_\lambda(g(x))\,d\rho(x),
\qquad M=\rho(K)>0.
\]

## 2A. Joint measurability

Land a reusable lemma for
\[
(\omega,x)\longmapsto G(\omega)(x).
\]

For a Borel-measurable \(C(K,\mathbb R)\)-valued map, use continuity of evaluation and composition. For the existing `GaussianField` interface, which supplies measurable evaluations and continuous paths, use a Carathéodory measurability theorem.

Your proposed `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` is a plausible route; check its exact hypotheses and argument order. A finite-quantisation approximation is a fallback already well matched to this library.

## 2B. Jensen–Tonelli, with the correct range

For \(p\ge1\):
\[
\mathbb E[D_\rho(G)^p]
\le M^{p-1}\int_K\mathbb E[S_\lambda(G(x))^p]\,d\rho(x).
\]

Prefer an ENNReal statement first:

```lean
lintegral_compactD_rpow_le
```

followed by an integrability corollary.

For a centred Gaussian field with
\[
C(x,x)\le c,\qquad p\beta c<2,
\]
derive finite \(p\)-moment. Supply a **uniform scalar bound**, not merely pointwise scalar integrability, before integrating over \(x\).

### Important limitation

Do not advertise this argument as proving sharp compact-base sufficiency for every \(p>0\).

For \(0<p<1\):

* finite sums can use \((\sum a_i)^p\le\sum a_i^p\);
* that bound is not partition-independent as the number of atoms increases;
* the displayed continuum Jensen inequality is reversed.

One can obtain \(p<1\) moments from a finite first or higher moment, but that does not cover the entire regime \(p\beta c<2\). Sharp continuum results there require another argument.

## 2C. Exact first moment

For constant covariance diagonal \(C(x,x)=c\), put
\[
\delta=1-\frac{\beta c}{2}.
\]
If \(\delta>0\), prove
\[
\boxed{\mathbb E D_\rho(G)
=M\Gamma(\lambda)(\beta\delta)^{-\lambda}.}
\]

The proof is Tonelli and the scalar Gaussian MGF:
\[
\mathbb E e^{\beta\sqrt t\,G(x)}
=e^{\beta^2ct/2}.
\]

Also land the variable-diagonal form under a uniform subcritical bound:
\[
\mathbb E D_\rho(G)
=\Gamma(\lambda)\int_K
\left[\beta\left(1-\frac{\beta C(x,x)}2\right)\right]^{-\lambda}\,d\rho(x).
\]

Suggested names:

```lean
GaussianField.integral_compactD_eq_of_const_diag
GaussianField.integral_compactD_eq
```

### Traps and non-claims

* Correlations do not enter this **first-moment** formula.
* They do enter \(\mathbb E\log D\), \(Q\), and \(V\).
* An overcritical variance at one \(\rho\)-null point is not, by itself, a Tonelli divergence argument.
* The field’s second sup-norm moment makes \(\mathbb E|\log D|\) finite for all \(\beta>0\); it does **not** make \(\mathbb E D\) finite for all \(\beta\).

### Stop rule

Land \(p\ge1\), joint measurability, and the exact first moment. Defer sharp \(p<1\) continuum thresholds.

---

# Unit 3 — Uniform empirical \(L^p\) bounds from pointwise MGFs

**This is the campaign’s central new bridge.**

It needs neither Gaussian empirical fields nor a supremum-tail theorem.

Suppose \(X:\Omega\times K\to\mathbb R\) is jointly measurable and
\[
\mathbb E e^{tX(\cdot,x)}\le e^{ct^2/2}
\]
for the nonnegative \(t\) used below, for \(\rho\)-a.e. \(x\). Let \(p\ge1\) and \(p\beta c<2\). Then
\[
\boxed{
\mathbb E[D_\rho(X)^p]
\le
\left[
M\Gamma(\lambda)
\{\beta(1-p\beta c/2)\}^{-\lambda}
\right]^p.
}
\]

This bound is not intended to be the exact Gaussian moment. Its advantages are that it is explicit, partition-independent, and uniform over empirical approximants.

### Clean proof avoiding quadratic-exponential integrability

Set
\[
\alpha=\beta(1-p\beta c/2)>0,\qquad
B=M\Gamma(\lambda)\alpha^{-\lambda}.
\]

Normalize
\[
d\rho(x)\,t^{\lambda-1}e^{-\alpha t}\,dt
\]
to a probability measure \(\nu\). Then
\[
D_\rho(X)=B\int
e^{-(\beta-\alpha)t+\beta\sqrt t\,X(x)}\,d\nu(x,t).
\]

Jensen and Tonelli give
\[
\mathbb E D_\rho(X)^p
\le B^p\int
e^{-p(\beta-\alpha)t}
\mathbb E e^{p\beta\sqrt t\,X(x)}\,d\nu.
\]
The exponent cancels because
\[
p(\beta-\alpha)=p^2\beta^2c/2.
\]

This is an especially good Lean proof: positive integrands, one normalized finite measure, one Jensen inequality, and Tonelli.

Suggested endpoints:

```lean
lintegral_compactD_rpow_le_of_subgaussian
uniform_compactD_rpow_bound_of_subgaussian
```

The theorem can initially use the explicit iterated integral rather than `compactD` if that avoids unnecessary continuity assumptions.

## Empirical corollary

For bounded independent observations with uniform range \(r\), use the landed Hoeffding result with
\[
c=(r/2)^2.
\]
Then, uniformly in \(n\),
\[
\mathbb E D_\rho(\xi_n)^p\le B^p.
\]

When \(\beta c<2\), choose
\[
1<p<\frac2{\beta c}.
\]

This supplies uniform integrability of these leading coefficients. The same strict condition also supplies the annealed gap decay in CXXXIX.

## Attach it honestly to CXLVIII

A further hypothesis is still necessary to move from the leading functional to the finite-\(n\) core. Accept either:

* a uniform pointwise domination
  \[
  |A_nZ_n^{\rm core}|\le K D_\rho(\xi_n);
  \]
* or a decomposition
  \[
  A_nZ_n^{\rm core}=D_\rho(\xi_n)+E_n,
  \qquad \sup_n\mathbb E|E_n|^p<\infty.
  \]

Then derive the core moment hypothesis required by `tendsto_integral_scaled_assembly`.

An \(L^p\)-small error is stronger and useful, but is not needed merely for the uniform bound.

### Traps and non-claims

* A distributional remainder estimate does not supply this \(L^p\) error bound.
* Taylor-tree asymptotics do not automatically provide a finite-\(n\) domination.
* Do not substitute the Gaussian limit’s moment for the empirical uniform bound.
* No independence across base points \(x\) is required.
* Independence across observations is used only to obtain the empirical MGF estimate.

### Stop rule

Land the MGF theorem and bounded-observation corollary even if the actual core domination is not yet available. Name the remaining domination/error hypothesis explicitly in the assembly wrapper.

---

# Unit 4 — Conditional population/empirical exponent identification

Yes, there is a clean theorem worth landing, but it must compare **the same population integral**, not infer empirical exponents from the existence of a Hironaka exponent.

Use ambient dimension `d` and sampling index `n`; keep `Q d` explicit to avoid conflating them.

## Required comparison diagram

For the population specialization \(\xi=0\), prove or assume:
\[
A_nZ_n^{\rm pop}\longrightarrow L_0,\qquad L_0>0,
\]
where
\[
A_n=n^\lambda/(\log n)^{m-1}.
\]

This may come from the exact-core adapter, population model asymptotics, and the gap bound.

Separately, the pinned Hironaka theorem, with `Q d`, supplies
\[
Z_n^{\rm pop}
=\Theta\!\left(n^{-\lambda_H}(\log n)^{m_H-1}\right).
\]

Then apply uniqueness of power–log orders to obtain
\[
\lambda=\lambda_H,\qquad m=m_H.
\]

Finally transport the empirical theorem to
\[
\frac{\log Z_n^{\rm emp}}{\log n}
\longrightarrow-\lambda_H
\quad\text{in probability}.
\]

Suggested split:

```lean
exponentPair_eq_of_population_comparison
tendstoInMeasure_log_div_log_of_population_comparison
```

These are schematic names; reuse the existing uniqueness-of-orders API.

### Traps

* Align the phase and asymptotic parameter: \(e^{-n f}\), \(e^{-\beta n\phi^2}\), and \(e^{-n\phi}\) are not interchangeable.
* If Hironaka gives a continuous-parameter theorem, explicitly restrict to integer sampling.
* Positivity/noncancellation of \(L_0\) is essential.
* The logarithmic empirical conclusion identifies \(\lambda\), not \(m\). Identification of \(m\) comes from the deterministic power–log comparison.
* Two separate exponent theorems do not establish that their input integrals coincide.

### Stop rule

Make this a conditional comparison theorem. Do not attempt construction of the missing certified presentation or removal of analytic units.

---

# Unit 5 — Finish the scalar critical \(p\)-moment line

This is worthwhile now: one analytic estimate closes a conspicuous strict-inequality gap.

For \(\beta,\lambda,p,v>0\), at \(p\beta v=2\), prove
\[
\boxed{
\mathbb E S_\lambda(X)^p<\infty
\iff p(2\lambda-1)<-1.
}
\]

## Missing analytic lemma

The landed lower bound needs a matching polynomially sharp upper bound:

\[
\exists C>0,\quad
S_\lambda(a)\le C\,a^{2\lambda-1}e^{\beta a^2/4}
\qquad(a\ge2).
\]

Together with CXLVI this gives two-sided comparability.

Use \(t=u^2\):
\[
S_\lambda(a)
=2e^{\beta a^2/4}
\int_0^\infty
u^{2\lambda-1}e^{-\beta(u-a/2)^2}\,du.
\]

Split away the possible singularity at \(u=0\); do not bound \(u^{2\lambda-1}\) globally by a multiple of \(a^{2\lambda-1}\) when \(2\lambda-1<0\).

At criticality the Gaussian exponential cancels, leaving the tail test
\[
\int_2^\infty a^{p(2\lambda-1)}\,da.
\]

Suggested endpoints:

```lean
fluctuation_le_polynomial_mul_gaussian
integrable_fluctuation_rpow_gaussianReal_iff_of_critical
```

Then finish finite mixtures by coordinatewise criteria.

### Useful sanity consequence

At the critical line, finiteness is possible only when \(p>1\), since
\[
\lambda<\frac{p-1}{2p}.
\]
For \(p\le1\) and \(\lambda>0\), critical moments always diverge.

### Real-\(p\) audit

For finite mixtures:

* \(p\ge1\): weighted Jensen;
* \(0<p\le1\): subadditivity, with weights raised to \(p\).

Do not reuse the same Jensen formula across both ranges.

### Stop rule

If the sharp upper bound becomes a large asymptotic-analysis project, stop after that lemma’s local estimates. No compact-base critical classification this round.

---

# Unit 6 — Publication audit, interface table, and targeted checks

This should be a deliverable, not an unbounded prose cleanup.

## Dot candidates

Without the source files, I would audit these statements by description rather than invent labels:

| Paper statement | Status / action |
|---|---|
| Compact-base Gaussian IBP and integrated interpolation, variable diagonal | Already dot-ready from CXLV |
| General-diagonal replacement of \(cM_2-Q\) by `Diag − Q` | Already dot-ready |
| Sharp strict finite-mixture moment threshold | Already dot-ready, with real-\(p\) proof audit |
| Continuum constant-diagonal annealed denominator | Dot after unit 2 |
| Gaussian Banach-law assumptions imply the sup-norm moment assumption | Dot after unit 1 |
| Uniform moments for bounded empirical leading coefficients | Dot after unit 3; not for the actual core without its adapter hypothesis |
| Identification of empirical \(\lambda\) with population \(\lambda_H\) | Dot only in the conditional form of unit 4 |
| Exact model/core equality | Already dot-ready **given** `ExactBoxCoreCertificate` |
| Existence of that certificate from Hironaka | Still not dot-ready |
| Expected empirical coefficient equals the population coefficient | Not a theorem; generally false |
| \(1/n\) correction from third cumulants alone | Not dot-ready; generally the wrong order claim |

## Restatement of text correction 6

I would now make it the following explicit distinction:

> The compact-base identities are obtained for continuous Gaussian fields with a finite second sup-norm moment, by mass-preserving finite quantisation. The covariance diagonal need not be constant: the variance term is \(\mathrm{Diag}-Q\). These quenched logarithmic identities require no annealed-denominator threshold. In contrast, finiteness of the annealed denominator is controlled by the Gaussian exponential-moment threshold. Neither statement identifies the mean limiting empirical coefficient with the population coefficient.

After unit 1, append:

> A centred Gaussian Borel law on \(C(K,\mathbb R)\) supplies the sup-norm moment by Fernique; this does not construct such a law from an arbitrary continuous PSD kernel.

Keep the following three quantities visibly separate:
\[
\log D_\rho(0),\qquad
\mathbb E\log D_\rho(G),\qquad
\log\mathbb E D_\rho(G).
\]

For constant diagonal in the subcritical regime,
\[
\mathbb E D_\rho(G)
=D_\rho(0)\left(1-\frac{\beta c}{2}\right)^{-\lambda}.
\]
That formula makes the population-versus-limit distinction concrete.

## Interface table: requested rows

I still recommend this table, ideally in the mirror and in abbreviated form in the note.

| Interface | Supplied hypotheses | Formal output | Not supplied |
|---|---|---|---|
| Hironaka population theorem | Analytic/nonnegative phase, theorem-specific geometric hypotheses, explicit `Q d` | Population Laplace order | Empirical field, exact adapted core coordinates |
| Certified chart core | `ExactBoxCoreCertificate`, including measure and phase identities | Actual chart integral equals `tanIntegral` | Certificate existence; removal of positive units |
| Model expansion | Coefficient-family and Taylor-tree hypotheses | Model leading coefficient and remainders | Identification with geometry without a core certificate |
| Empirical field limit | The stated field/coefficient convergence hypotheses | Limiting random model coefficient | A field CLT from a scalar CLT |
| Pathwise gap | Positive gap and fluctuation bound on the good event | Pathwise exponentially small remainder | Expected smallness on the complement |
| Annealed gap | Pointwise exponential moments and an integrable envelope | Expected exponentially small remainder | Supremum concentration or chaining |
| Compact Gaussian base | Continuous paths, Gaussian evaluation laws, second sup-norm moment | IBP, interpolation, positivity of expected log correction | Gaussian-process existence |
| Gaussian Banach-law adapter | Centred Gaussian Borel law on \(C(K,\mathbb R)\) | Gaussian-field inputs, including the moment | Construction from a kernel |
| Scaled empirical assembly | Core convergence in law and negligible scaled remainder | Distributional limit and logarithmic exponent | Expectation convergence without uniform integrability |
| Expectation assembly | Additionally a uniform core \(p\)-moment, \(p>1\) | Mean asymptotics with coefficient \(\mathbb E L\) | Equality with the population coefficient |
| Exponent comparison | Same population integral, positive population leading coefficient, both order descriptions | Equality of exponent pairs | Geometric compatibility from two unrelated theorems |

Mark rows involving #59 as conditional/planned until landed.

## Non-claim cleanup

Replace the blanket phrase **“the fluctuation term (population case only)”** by something scoped, for example:

> An unconditional geometric construction and empirical fluctuation theorem from the original statistical model; the present empirical results use certified cores and explicit field-limit/moment hypotheses.

The existing wording now understates the conditional empirical results.

## Numerical checks before Overleaf

Use deterministic quadrature where possible; Monte Carlo is weakest precisely near the moment thresholds.

1. **One-point base:** check the first-moment formula against one-dimensional Gaussian quadrature.
2. **Rank-one constant field:** \(G(x)=X\). This reduces every partition to the same scalar calculation and tests mass factors.
3. **Variable diagonal, including singular covariance:** numerically test
   \[
   \mathbb EH=\beta\mathbb E(\mathrm{Diag}-Q).
   \]
   A mistakenly retained constant-\(c\) formula should fail here.
4. **Interpolation:** compare direct quadrature of \(\mathbb E\log D\) with the \(s\)-integral.
5. **Critical moments:** inspect truncated integrals on logarithmic cutoffs, not apparently stable Monte Carlo means.

Record seeds, quadrature tolerances, and truncation ranges. Numerical agreement is a transcription check, not evidence added to the Lean theorem.

### Stop rule

One interface table, one status audit, and a small reproducible check script. No broad rewriting of the main paper.

---

# Unit 7 — Expendable: bilocal boundary

Keep this last. I would not drop it permanently, but it should not delay the expectation campaign.

If the actual integral is the equal-exponent canonical form
\[
I_\lambda(a,b,h)=
\int_0^\infty\!\!\int_0^\infty
t^{\lambda-1}s^{\lambda-1}
e^{-at-bs+h\sqrt{ts}}\,dt\,ds,
\]
then for \(a,b>0\), \(h=2\sqrt{ab}\), the prediction is correct:
\[
I_\lambda(a,b,h)<\infty\iff 0<\lambda<\tfrac14.
\]

With \(t=x^2,s=y^2\), the exponent becomes
\[
-(\sqrt a\,x-\sqrt b\,y)^2.
\]
The ridge contributes the tail power \(r^{4\lambda-2}\).

For this **equal-exponent** integral, \(a\le0\) or \(b\le0\) gives divergence. The zero cases with negative \(h\) need a real argument: they are not settled by “the integrand grows in one coordinate.” Integrating one square-root coordinate exposes a logarithmic divergence at the other coordinate’s origin.

Do not transfer that conclusion without checking the exponents: unequal powers can behave differently when a diagonal coefficient vanishes.

### Stop rule

Only start after units 1–6. Stop if the coordinate-change or integrability infrastructure exceeds a small standalone module.

---

## Why not next-order averaging now?

A generic third cumulant produces an **\(n^{-1/2}\)** correction, not automatically an \(n^{-1}\) correction. At order \(n^{-1}\), one generally needs both fourth-cumulant contributions and quadratic third-cumulant contributions.

Moreover, an Edgeworth expansion for \(\mathbb E\log D\) needs:

* a sufficiently strong approximation theorem for the empirical vector;
* derivative bounds for the unbounded test function;
* moment and tail control for the remainder;
* an explicit cancellation if the \(n^{-1/2}\) term is absent.

Taylor trees and Gaussian Stein identities do not alone provide these inputs. A future finite-dimensional pilot is sensible, but this campaign should first make the existing leading-order expectation theorem usable.

## Campaign-wide stop rule

Declare #59 successful once you have:

1. a Fernique moment adapter;
2. compact annealed first moments;
3. a uniform empirical leading-coefficient \(L^p\) theorem;
4. an assembly wrapper that exposes, rather than hides, the remaining core error hypothesis;
5. the conditional exponent comparison;
6. corrected paper interfaces.

The scalar critical line is valuable completion work. The bilocal boundary remains expendable. **No new geometric existence theorem, field CLT, or Edgeworth machinery should become an implicit dependency of this campaign.**
