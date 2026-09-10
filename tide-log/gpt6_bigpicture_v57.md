## Recommendation

**Close the note’s finite-resolution programme now, after a small dataset-facing bridge and the corrections below. Return the main campaign to the paper.**

The compact-base transfer is worthwhile **as a two-unit, hypothesis-explicit extension**, not as a campaign to build Gaussian-process infrastructure. In particular, an explicit second sup-norm moment is enough: Fernique need not enter the transfer proof.

There are two important corrections to make immediately:

1. The marked-posterior interpretation has an erroneous factor \(1/2\):  
   \[
   W_i=\langle T\mathbf1_i\rangle_g,
   \]
   not \(\frac12\langle T\mathbf1_i\rangle_g\).
2. The worked bilocal example gives an insufficient domain for its **series** when the covariance is negative. Absolute convergence requires the condition involving \(|b|\).

I cannot inspect the pinned Lean source here. Below, existing declaration names are those you supplied; new theorem names are proposals. I will not invent an exact Mathlib uniform-integrability theorem name.

---

# 1. Ranked programme: at most eight units

| Rank | Unit | Deliverable |
|---|---|---|
| 1 | Dataset expectation bridge | Weak convergence + explicit moment/UI hypothesis; finite-resolution annealed denominator corollary |
| 2 | Paper A3 | Positive-gap remainder with an explicit fluctuation bound |
| 3 | Paper A2 | Exact tangential/normal weighted-box decomposition |
| 4 | Paper analytic certificate | Normal-variable analytic coefficient envelope, with tangential dependence retained |
| 5 | Paper cover assembly | Conditional analytic-core decomposition modulo a positive-gap remainder |
| 6 | Compact base I | Atomic approximation and partition-independent deterministic bounds |
| 7 | Compact base II | Transfer of quartet and interpolation identities under a second sup-norm moment |
| 8 | Optional scalar moment theorem | Strict \(p\)-moment thresholds by one-dimensional bounds—not \(p\)-fold integration |

Units 6–8 are optional. **A successful five-unit campaign already closes the present priority list.**

The descriptions of A2 below are a precise replacement specification: the actual #55/#56 A2 statement is not included in this conversation, so I cannot honestly recover its exact original wording.

---

# 2. Q1: compact-base transfer

## Minimal setup

Use a **nonempty compact metrizable space**, not an arbitrary compact topological space:

```lean
variable
  [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (ρ : Measure K) [IsFiniteMeasure ρ]
  (G : Ω → C(K, ℝ))
```

Assume:

1. `Measurable G`—or `AEStronglyMeasurable G P`, if that better matches the integration interface.
2. `ρ ≠ 0`.
3. \(\beta,\lambda>0\).
4. For every nonempty finite family \(w_i\), the evaluation vector has law `gaussianVector A` for some finite matrix \(A\).
5. Its diagonal covariance is the same fixed \(c\).
6. **Explicit moment hypothesis**
   \[
   \int \|G(\omega)\|_\infty^2\,dP(\omega)<\infty.
   \]

The finite-dimensional-law formulation you suggest is adequate. It is a clean way to avoid `IsGaussianProcess`. Allow the source dimension of \(A\) to vary with the finite family.

Define
\[
b(w,v)=\mathbb E[G(w)G(v)].
\]
The second sup-norm moment implies that this is well-defined and continuous on \(K\times K\), by dominated convergence. The finite-dimensional law assumption supplies positive semidefiniteness and \(b(w,w)=c\).

Do not assume only “continuous covariance”: that alone does not supply a measurable continuous-path random element.

## Continuum definitions

For \(g\in C(K)\), put
\[
\begin{aligned}
D(g)&=\int_K S_\lambda(g(w))\,d\rho(w),\\
r_g(w)&=\frac{S_{\lambda+1/2}(g(w))}{D(g)},\\
M_2(g)&=\frac{\int_K S_{\lambda+1}(g(w))\,d\rho(w)}{D(g)},\\
H(g)&=\int_K g(w)r_g(w)\,d\rho(w),\\
Q(g)&=\iint_{K\times K}b(w,v)r_g(w)r_g(v)\,d\rho(w)d\rho(v),\\
V(g)&=cM_2(g)-Q(g).
\end{aligned}
\]

Here \(r_g\) is a density relative to \(\rho\); the atomic \(W_i\) includes the corresponding atom mass.

## The essential improvement: second moments suffice

Let \(R=\|g\|_\infty\), \(M=\rho(K)>0\). Obtain bounds **independent of the number and sizes of atoms**:
\[
\begin{aligned}
0<M_2(g)&\le \frac{2\lambda}{\beta}+\frac{R^2}{4},\\
|H(g)|&\le R\sqrt{\frac{2\lambda}{\beta}+\frac{R^2}{4}},\\
0\le V(g)&\le c\left(\frac{2\lambda}{\beta}+\frac{R^2}{4}\right),\\
|\log D(g)|&\le |\log M|+C_{\beta,\lambda}
                 +\frac{\beta R^2}{2}+2\lambda R.
\end{aligned}
\]

For the logarithm, use
\[
M\inf_{|a|\le R}S_\lambda(a)
 \le D(g)\le
M\sup_{|a|\le R}S_\lambda(a).
\]

**Do not use** the current finite-dimensional logarithm bound involving \(|\log\rho_j|\) and a sum over all coordinates. It is unsuitable for refinement of partitions.

Thus:

- no arbitrary polynomial moments are needed for these particular transfers;
- no exponential moment is needed;
- Fernique is only a means of **discharging the explicit sup-norm moment assumption**.

## Atomic approximation

Choose finite measurable partitions of mesh tending to zero; use atom masses \(\rho(K_i)\) and representatives in the nonempty cells. Drop zero-mass cells. Then
\[
\rho_n=\sum_i\rho(K_i)\delta_{w_i},
\qquad \rho_n(K)=M.
\]

For every continuous integrand, the quadrature converges by uniform continuity. Apply this to the one-variable integrands and to the two-variable integrand defining \(Q\). This gives pathwise convergence of \(D,M_2,H,V,\log D\).

Alternatively, take a mass-preserving sequence of finitely supported measures converging weakly to \(\rho\), if that interface is already cheaper in the repository. Building a general weak-density theorem is not part of this unit.

## Statements to transfer

Under the above assumptions:
\[
\mathbb EH=\beta\mathbb EV,\qquad
\mathbb EM_2=\frac{\lambda}{\beta}+\frac12\mathbb EH,
\qquad \mathbb EH\ge0.
\]

With \(V_s(g)=V(\sqrt s\,g)\), retaining the original covariance kernel:
\[
\mathbb E\log D(G)
=\log\!\big(M\Gamma(\lambda)\beta^{-\lambda}\big)
+\frac{\beta^2}{2}\int_0^1\mathbb EV_s(G)\,ds.
\]

Hence the expected-log lower bound.

The existing exact finite interpolation identity should be transferred directly using domination on \([0,1]\times\Omega\). **Do not first rebuild infinite-dimensional Gaussian IBP.**

### Fernique boundary

A corollary for a centred Gaussian random element of \(C(K)\) is natural using `exists_integrable_exp_sq`. But finite-dimensional Gaussian evaluations do not plug into that theorem automatically: one must bridge to Gaussianity under all continuous linear functionals.

That bridge is mathematically standard for compact metric \(K\), but it is a separate library task. For this campaign:

> State the sup-norm second moment explicitly; add the Fernique corollary only if the random-element Gaussian-law interface is already available.

**Budget: two units. Stop rather than creating a third unit of process infrastructure.**

---

# 3. Q2: higher moments

Your strict thresholds and endpoint are correct, for \(\lambda>0\), \(p\ge1\). At the endpoint \(p=1\), the condition becomes \(\lambda<0\), so the moment always diverges in the present range.

I would **not** spend a unit on a general `Measure.pi` cone-divergence argument solely for this proposition.

## Cheaper optional route

For strict subcriticality, choose \(\eta\in(0,1)\) and complete the square to obtain
\[
S_\lambda(a)
\le \Gamma(\lambda)(\beta\eta)^{-\lambda}
 \exp\!\left(\frac{\beta a_+^2}{4(1-\eta)}\right).
\]
If \(\beta cp<2\), choose \(\eta\) sufficiently small and integrate its \(p\)-th power against the scalar Gaussian density.

For strict supercriticality, establish, for sufficiently large \(a>0\),
\[
S_\lambda(a)\ge C_{\beta,\lambda}
 a^{2\lambda-1}e^{\beta a^2/4}.
\]
Restrict the \(T\)-integral to \(T\in[a/2,a/2+1]\). The Gaussian density then leaves a positive quadratic exponential when \(\beta cp>2\).

This proves the strict criteria in one dimension and would even support real positive powers. The latter extension need not be part of the deliverable.

**Recommendation:** retain `prop:moments` as established-but-unformalised for now. If unit 8 is used, formalise only the two strict implications. Leave the endpoint unformalised.

---

# 4. Q3: the dataset-facing expectation theorem

## Separate the probabilistic bridge from the coefficient computation

The clean bridge is:

> Let \(C_n\) and \(C\) be measurable real random variables, possibly on different probability spaces. Suppose \(C_n\Rightarrow C\), and for some \(\varepsilon>0\),
> \[
> \sup_n\mathbb E|C_n|^{1+\varepsilon}<\infty.
> \]
> Then \(C\) is integrable and
> \[
> \mathbb EC_n\longrightarrow\mathbb EC.
> \]

A UI version is equally valid. The moment version is usually easier to instantiate and package.

### No coupling or joint law is needed here

Scalar convergence in distribution is enough.

A joint-law theorem is needed **earlier**, if one is trying to deduce convergence of a ratio or another multivariate functional from convergence of its components. Separate marginal convergence of numerator and denominator is insufficient. If `sample_stochastic_expansion` already supplies \(C_n\Rightarrow C(G)\), that issue has already been settled for this coefficient.

## A reliable formal proof without a guessed UI API

Use bounded continuous clipping
\[
T_R(x)=\max(-R,\min(x,R)).
\]

Weak convergence gives convergence of \(\mathbb E T_R(C_n)\). The moment bound gives
\[
\mathbb E|C_n-T_R(C_n)|
 \le R^{-\varepsilon}\mathbb E|C_n|^{1+\varepsilon}.
\]
Apply weak convergence to bounded truncations of \(|x|^{1+\varepsilon}\) to obtain the same moment bound for \(C\), then let \(R\to\infty\).

This uses:

- the bounded-continuous-test characterization of convergence in distribution;
- `BoundedContinuousFunction`;
- elementary integral inequalities;
- monotone convergence or dominated convergence for the truncations.

I cannot certify the precise pinned Mathlib declaration name for “UI + convergence in distribution implies convergence of expectations.” In particular, an API based on `tendstoInMeasure` cannot be applied directly to convergence in distribution. **Do not silently substitute those notions.** A small clipping lemma is a safe bounded deliverable.

## Specialisation to \(Q=0\)

For
\[
C(G)=D(G)=\sum_i\rho_iS_\lambda(G_i),\qquad b_{ii}=2,
\]
the theorem becomes, for \(0<\beta<1\),
\[
C_n\Rightarrow D(G),\quad
\sup_n\mathbb E|C_n|^{1+\varepsilon}<\infty
\quad\Longrightarrow\quad
\mathbb EC_n\to
\Gamma(\lambda)[\beta(1-\beta)]^{-\lambda}\sum_i\rho_i.
\]

This is a theorem about a **raw leading coefficient**. It is not the expected Bayes-error theorem: the latter uses normalised limits and the quartet, not merely \(Q=0\).

For a remainder \(R_n\to0\) in probability, the corresponding moment/UI hypothesis gives \(\mathbb E|R_n|\to0\). Record that separately if needed to pass from a leading coefficient to the full scaled empirical quantity.

## Record the denominator corollary now

Yes:
\[
\mathbb E_+D(G)=
\begin{cases}
\Gamma(\lambda)[\beta(1-\beta)]^{-\lambda}\sum_i\rho_i,
 &0<\beta<1,\\
+\infty,&\beta\ge1.
\end{cases}
\]

Use finite sums in `ℝ≥0∞`; then supply the integrability/Bochner corollary below threshold. It is a short packaging lemma, not a new unit.

A useful additional consequence costs little:

> If \(C_n\ge0\), \(C_n\Rightarrow D(G)\), and \(\mathbb E_+D(G)=\infty\), then \(\mathbb E_+C_n\to\infty\).

Bounded truncations prove this without UI. In particular, **UI is impossible at \(\beta\ge1\)** under that convergence.

---

# 5. Q4: return to the paper—four precise units

## Unit 2: A3, positive-gap remainder

This should come first because it has the cleanest contract.

Let \(E\) be a measurable region, \(\kappa>0\), and \(K(u)\ge\kappa\) on \(E\). Suppose the phase is
\[
-\beta nK(u)+\beta\sqrt n\,\sqrt{K(u)}\,\xi_n(u),
\]
with \(\sup_E|\xi_n|\le B_n\). If eventually
\[
B_n\le \tfrac12\sqrt{n\kappa},
\]
then pointwise on \(E\),
\[
-\beta nK+\beta\sqrt n\sqrt K\,\xi_n
\le-\tfrac{\beta}{2}nK
\le-\tfrac{\beta\kappa}{2}n.
\]

For an integrable amplitude envelope \(A\),
\[
\left|\int_E a_n(u)e^{\text{phase}}\,d\mu(u)\right|
\le \left(\int_E A\,d\mu\right)e^{-\beta\kappa n/2}.
\]

Polynomial prefactors can subsequently be absorbed into a slightly weaker exponential rate.

**Non-claims:** pathwise \(B_n=o(\sqrt n)\), or \(B_n=O_P(1)\), does not automatically give an exponentially small *expected* remainder. That requires a tail/moment estimate on the exceptional datasets.

## Unit 3: A2, exact weighted-box decomposition

For a resolved box and
\[
K(u)=a(u)\prod_i u_i^{2k_i},\qquad a(u)\ge a_0>0,
\]
split coordinates into
\[
N=\{i:k_i>0\},\qquad T=\{i:k_i=0\}.
\]

For a cutoff \(r_i\in(0,b_i)\), partition the normal-coordinate box into cells indexed by \(S\subseteq N\):

- \(u_i<r_i\) for \(i\in S\);
- \(u_i\ge r_i\) for \(i\in N\setminus S\);
- tangential coordinates remain unrestricted.

Use half-open conventions for literal disjointness, or prove that the boundaries have zero measure for the weighted volume measure.

Deliver:

1. Exact finite sum of the weighted integral over these cells.
2. On \(S=\varnothing\),
   \[
   K\ge a_0\prod_{i\in N}r_i^{2k_i}>0.
   \]
3. On \(S\ne\varnothing\), absorb the bounded-away normal factors into the unit:
   \[
   K=a_S(u)\prod_{i\in S}u_i^{2k_i},
   \qquad a_S>0.
   \]

**Critical trap:** a coordinate bounded away from zero has become a parameter for that cell; a translated monomial is not a monomial at the new origin. Do not erase its analytic unit without an explicit change-of-variable theorem.

This is an exact integration/decomposition theorem, not yet a Taylor certificate.

## Unit 4: normal analytic certificate

The right target is not necessarily joint analyticity in every coordinate. It is a uniform normal-variable expansion:
\[
a(x,v,w)=\sum_\alpha a_\alpha(x,w)v^\alpha,
\]
where \(v\) denotes the small normal coordinates, \(w\) all retained parameters, and for some radius \(R\),
\[
\sum_\alpha R^{|\alpha|}
 \sup_w|a_\alpha(x,w)|\le A(x)
\]
with the precise integrability of \(A\) required by the existing grammar theorem.

Deliver the map from this certificate into the existing Taylor-data/analytic-certificate interface.

Two valid versions:

- assume the summable envelope explicitly;
- derive it from a **uniform** analytic extension and majorant, if that infrastructure is already present.

**Non-claim:** pointwise real analyticity on a compact real box alone is not the probabilistic coefficient envelope. Smooth tangential weights are also not jointly analytic amplitudes.

## Unit 5: `ResolutionCover` assembly

Assume:

1. an axiom-clean finite resolved integration formula;
2. compatible weighted-box parametrisations;
3. the unit-4 certificates on all core cells;
4. a positive gap on the discarded part.

Prove
\[
Z_n=\sum_{j\in J} Z^{\mathrm{core}}_{n,j}+R_n,
\]
with every core term accepted by the existing standard-integral theorem and \(R_n\) bounded by unit 2.

**Do not claim this for an arbitrary analytic `ResolutionCover` solely because its charts are analytic.** The missing work can include:

- change of variables and multiplicities;
- control of overlaps;
- the transformed density;
- nonanalytic partition-of-unity weights;
- uniform coefficient envelopes.

There is no general compactly supported analytic partition of unity to make those issues disappear.

The pinned `hironaka` dependency may discharge resolution and normal-crossing inputs through its axiom-clean declarations. It does not, merely by being available, discharge the analytic and probabilistic interfaces above.

---

# 6. Q5: exact text corrections

## A. Abstract: narrow the finiteness/formalisation claim

Replace the opening claim about “their exact domains of finiteness” with:

> “exact one-point Gaussian averages and their finiteness threshold, together with bilocal integral and series formulas and formalised strict-regime finiteness and divergence results”

Replace “These statements are formalised in Lean (blue dots)” with:

> “Blue dots identify the formalised statements. The higher-moment criterion and the bilocal boundary classification are proved mathematically but are not part of the present Lean development.”

## B. Scope: annealed identities are probabilistic

Replace:

> “Exact finite-sample identities of the sampling model (no probability)”

with:

> “Exact finite-sample statements: the algebraic sampling identity and fluctuation sign, and the probabilistic annealed identity under independence and likelihood normalisation.”

## C. Likelihood support condition: reverse the relevant direction

The present support sentence is wrong. Replace it with:

> “The identity \(\mathbb E_q e^{-f(X,u)}=1\) requires \(\int_{\{q>0\}}p(x\mid\pi(u))\,dx=1\), equivalently that the model distribution place no mass outside the support of \(q\). A finite real log-likelihood ratio \(q\)-almost surely additionally requires \(p(\cdot\mid\pi(u))>0\) \(q\)-almost surely.”

Support containment in the direction currently stated is not enough.

## D. Sampling sign audit: make the interpretation conditional

Replace “the coefficient family … is therefore that of \(-a\)” with:

> “To instantiate this library construction for the likelihood convention \eqref{eq:a_defn}, the coefficient family \(c_\gamma(x)\) must be chosen as the Taylor coefficients of \(-a(x,\cdot)\).”

The algebra does not itself identify an abstract coefficient family with a model’s coefficients.

## E. Divisor approach

Add:

> “Here the approach is through points with \(\phi_t\ne0\), at least eventually.”

Also make the last conclusion explicitly conditional on the stated envelope and second-moment continuity assumptions.

## F. Fisher-information remark

“No analogous closed formula” is too strong. Replace the final sentence with:

> “In several dimensions the resolved coefficient depends on the blow-up direction. At leading order in a regular model, normalised score directions do give a Fisher-matrix expression for the directional covariance; no coordinate-independent formula for arbitrary resolved charts is needed or claimed here.”

## G. Bilocal proposition: distinguish the proved domains

After the proposition, insert:

> “The Lean results establish the integral identity, finiteness for \(A,B>0\) and \(H<2\sqrt{AB}\), divergence for \(A,B>0\) and \(H>2\sqrt{AB}\), and the absolutely convergent series for \(|H|<2\sqrt{AB}\). The remaining boundary classification is not formalised.”

The full “if and only if” is mathematically correct for the equal exponents used here, but its proof currently omits \(A\le0\) or \(B\le0\). Either remove the full classification or add:

> “If \(A<0\) or \(B<0\), fixing the other variable in a compact positive interval gives divergence. If \(A=0\), \(B\ge0\), and \(H<0\), integration in \(t\) gives a constant multiple of \(\int_0^\infty s^{-1}e^{-Bs}\,ds\), which diverges; the other zero-boundary cases are immediate or symmetric.”

## H. Series versus finiteness: state the absolute-value condition

Before the displayed \(c=c'=2\) series, write:

> “For \(c=c'=2\), the absolutely convergent series is valid when \(0<\beta<(1+|b|/2)^{-1}\). The integral itself is finite throughout \(0<\beta<1\) when \(b\le0\), and throughout \(0<\beta<(1+b/2)^{-1}\) when \(b>0\), with the previously stated critical-line qualification.”

For the connected formula, explicitly retain \(\beta<1\) so that the individual means are finite.

## I. After `prop:moments`

Replace the entire formalisation-status sentence with:

> “For \(c=2\), \(\beta<1/p\) is the strict subcritical region of the pointwise \(p\)-th moment; the endpoint depends on \(\lambda\). This does not by itself classify moments of continuum spatial integrals. The present Lean development proves the bilocal strict-regime results described above, but not the critical-line classification, the nonpositive-\(A\) or nonpositive-\(B\) cases, or this higher-moment proposition.”

Use \(\mathbb E_+\), rather than an undifferentiated expectation, in the proposition’s divergence assertions.

## J. Worked floor-rises example

Replace the justification for exchanging expectations with:

> “For nonnegative \(\eta\), Tonelli permits the exchange of the dataset and base integrals; constant variance then makes the one-point expectation independent of the base point. For signed \(\eta\), assume the corresponding absolute integrability.”

Replace the series domain with:

> “valid for \(0<\beta<(1+|b(w,w')|/2)^{-1}\).”

A uniform sufficient condition for all covariance values with diagonal \(2\) is \(\beta<1/2\).

## K. Marked posterior: fix the factor

Replace
\[
W_i=\tfrac12\langle T\mathbf1_i\rangle_g
\]
by
\[
W_i=\langle T\mathbf1_i\rangle_g.
\]

The radial partition function in that convention is \(D/2\), so the factors cancel in the ratio.

## L. Polynomial bounds: exclude \(D\)

Replace “every quantity is polynomially bounded in \(g\)” with:

> “The normalised quantities \(W_i,M_2,H,Q,V\) are polynomially bounded in \(g\); \(\log D\) has a quadratic bound. The raw denominator \(D\) generally has exponential-quadratic growth.”

The reported landed-summary claim that \(D\) itself is polynomially bounded cannot be correct for positive weights and unrestricted \(g\). Audit the declaration intended there; this may simply be a summary typo.

## M. Quartet: do not identify the statistical invariant prematurely

Replace “Defining the singular fluctuation” with:

> “Defining the finite-resolution Gaussian fluctuation parameter \(\nu:=\tfrac12\mathbb E H(G)\)”

Replace “These are the four coefficients of Watanabe’s formulas” with:

> “These are the algebraic combinations appearing in Watanabe’s four expected-error formulas. Their identification with coefficients of a statistical model requires the additional transfer and remainder hypotheses stated below.”

## N. Relation section: spatially constant phase qualification

Replace the sentence saying the earlier population-ratio claim “is true only for a spatially constant phase” with:

> “For a spatially constant phase, the common \(S_\lambda\) factor cancels from location-only posterior ratios. It need not cancel from energy observables, and no general statement that normalisation first matters at relative order \(1/n\) follows.”

“Only” was also too strong: special observables and other symmetries can produce cancellation.

## O. Relation section: close the finite/continuum gap explicitly

Replace the final “with such hypotheses” sentence with:

> “For a finite-resolution limit, convergence of the relevant scaled observables together with uniform integrability and a predictive Taylor-remainder estimate permits the quartet algebra to determine the expected coefficients. For the continuum spatial posterior, one additionally needs a continuum version of the Gaussian identities, or a proved discretisation transfer. These hypotheses are not discharged here.”

## P. Discussion: raw bilocal pairings already exist

Replace:

> “For raw quantities the pairings are local … normalisation forces bilocal pairings”

with:

> “Raw one-point quantities involve local pairings; raw multipoint quantities already involve bilocal cross-pairings. Normalised observables couple base points through the common denominator and are handled here by exact self-normalised identities rather than by a denominator series.”

Replace the unconditional \(1/n\) sentence with:

> “Under the statistical transfer and remainder hypotheses, the leading expected-error coefficients have the two-parameter form determined by \(\lambda\) and \(\nu\). The present finite-resolution Gaussian theorem establishes that algebra, not the finite-sample expansion itself.”

## Q. Heuristic appendix

After the Isserlis paragraph, add:

> “Termwise expectation of the source series requires a separate absolute-integrability argument; the pairing description alone does not justify exchanging the infinite sum and expectation.”

Replace the final compact-base sentence with:

> “A compact-base extension can be obtained by mass-preserving atomic approximation, provided the field is a measurable \(C(K)\)-valued random element with the stated finite-dimensional Gaussian laws and an integrable squared sup norm. Fernique can supply the latter under an appropriate Gaussian random-element hypothesis. This transfer is not yet formalised.”

For the denominator expansion, add:

> “Finiteness of \(\bar D\) alone is not sufficient: the Taylor series for \(\log(1+\delta)\) and its termwise expectation require additional control. In particular, higher moments may fail even when \(\bar D<\infty\).”

## Promotion/demotion

- **Keep covariance interpolation in the main text.** It is now a central result.
- Promote the finite-resolution denominator dichotomy to a short corollary in the annealed-identity paragraph.
- Put the future conditional expectation-transfer theorem there too.
- Move the full unformalised bilocal boundary classification to a remark or appendix if the main proposition is intended to advertise precisely the dotted theorem.
- Do not promote the diagrammatics or phase-transition narrative.

---

# Stop rule

Stop when:

1. the text corrections and finite-resolution denominator corollary are landed;
2. the conditional expectation bridge is available;
3. the paper’s positive-gap and box-decomposition interfaces are explicit;
4. the analytic-core assembly is either proved from named certificates or blocked by a precisely identified missing certificate.

For compact base, stop after two units: **no new Gaussian-process framework, no implicit Fernique bridge, no partition-dependent domination**.

For higher moments, stop at the strict scalar thresholds—or leave the proposition unformalised. The endpoint and general \(p\)-dimensional cone machinery are not prerequisites for either the companion note or the next paper campaign.
