**Rank 2 supplies the substantive deterministic E1 theorem.** Reusing `spatialPhase_tendsto` is a better route than introducing a marked radial limit.

The main qualifications are:

1. `ChartLeading` is a sound, but potentially stronger-than-necessary, localisation hypothesis. It does **not** by itself assert that the leading coefficient is nonzero.
2. The all-smooth-\(F\) result is credible under the stated compactness, boundedness, and tail hypotheses.
3. The proposed explanation involving “mass on the deeper fibre” needs correction: **integrable face densities do not acquire mass on the boundaries of their face boxes**.
4. The missing uniformity lemma is obtainable by a direct, finite-\(N\), locally Lipschitz estimate.
5. Computing the expectation of the limiting Gaussian residue is not yet an annealed convergence theorem; that additionally requires uniform integrability or a direct expectation argument.

I am auditing the mathematical statements and interfaces supplied here, rather than reporting a source-level inspection of #138 or the Lean declarations.

## (a) The leading-pair interface

### `ChartLeading` is acceptable—with precise wording

The condition
\[
\forall p,\qquad
\lambda\le \frac{h_{p,i}+1}{2k_{p,i}}\quad\text{for every }i,
\qquad
\#\left\{i:\frac{h_{p,i}+1}{2k_{p,i}}=\lambda\right\}\le m
\]
is sufficient for the theorem you describe. It correctly constrains the **chosen localised transport**, rather than an arbitrary global index.

However, it is an **upper-bound condition on the asymptotic scale**, not an assertion that this is the actual leading pair. For example:

- \(\lambda\) could be strictly below every chart ratio;
- \(m\) could exceed every multiplicity at \(\lambda\);
- the extremising faces could all have zero amplitude.

In all these cases the stated limit can be zero.

Thus the paper may say:

> The transport is chart-leading at \((\lambda,m)\).

It should only say

> \(\lambda\) is the minimal chart ratio and \(m\) its maximal multiplicity

if attainment is also assumed. To call it the **effective RLCT pair**, add positivity/nonvanishing on at least one extremising face. For \(F=1\), positive face mass is the natural condition.

### Bridging from `IsExtremalData`

An extra chart-support incidence hypothesis is a reasonable bridge, but **“every chart face meets \(Z_0\)” needs clarification**.

- To prove each ratio is at least \(\lambda\), meeting the relevant codimension-one face can suffice, assuming chart ratios agree with the geometric wall ratios.
- To bound the number of simultaneous resonant coordinates, individual face intersections are insufficient. The relevant **simultaneous resonant intersection** must meet the supported zero fibre.

For example, two resonant coordinate faces may each meet the prior’s support while their intersection does not. The box sees multiplicity two; the supported zero fibre may only see multiplicity one.

A clean sufficient hypothesis is that the full corner of each nonempty-dimensional chart meets the supported zero fibre, with the necessary chart-source and wall-identification conditions. A less restrictive hypothesis asks for the particular intersections needed by the multiplicity argument.

I would make this a **separate geometric bridge theorem**, not a dependency of the already-landed analytic theorem.

### Support-aware weakening: feasible, but not a one-line extension

If the amplitude vanishes on a **neighbourhood of the entire closed face** \(u_i=0\), then that coordinate can indeed be excluded from determining the asymptotic pair. On the amplitude’s support, \(u_i\ge\varepsilon>0\), so its contribution to the monomial phase is a bounded positive unit.

Consequently, there is no contribution from the putative pole belonging to that excluded face.

But two distinctions matter:

1. **Vanishing on a face is not vanishing near it.**  
   A finite-order zero can shift a ratio rather than eliminate its contribution.

2. **A zero leading coefficient at the box’s smallest ratio is insufficient.**  
   `spatialPhase_tendsto` then gives only
   \[
   I_N=o\!\left(N^{-l'}(\log N)^{q'}\right).
   \]
   That does not establish the desired asymptotic at a faster scale.

The practical proof of (ii) is:

- obtain a uniform collar on which the amplitude vanishes;
- treat excluded coordinates as additional base parameters;
- apply the phase theorem in the remaining small coordinates;
- absorb the separated coordinates into a positive phase unit;
- establish domination uniformly over the enlarged base.

If every coordinate is separated from zero, the contribution is exponentially small.

Compactness is important when obtaining a uniform collar. Absence from the support on an **open** face does not automatically give a collar uniform up to its boundary or over a noncompact base.

Also, constraining only individually supported coordinate faces is not the fully sharp support-aware interface: the multiplicity issue depends on **supported intersections**. A genuinely intrinsic weakening will likely require a support-adapted subdivision or partition of unity.

**Recommendation:** retain `ChartLeading` for Rank 2 and the first paper-facing theorem. Treat support-adapted weakening as subsequent geometry/analysis, not corrective work required to validate Rank 2.

## (b) All smooth \(F\), and the total-mass issue

### No admissibility is needed for the face formula

For a contributing piece, \(J=\operatorname{resSet}(\lambda)\) has size \(m\). Every \(i\notin J\) satisfies
\[
\frac{h_i+1}{2k_i}>\lambda,
\qquad\text{hence}\qquad
h_i-2k_i\lambda>-1.
\]
Thus
\[
\prod_{i\notin J}w_i^{h_i-2k_i\lambda}
\]
is integrable on the entire face box. Bounded branch representatives make \(S_\lambda(\widehat\psi)\) bounded, and smooth \(F\) is bounded on the relevant compact chart images.

Subject to the stated base-integrability and tail hypotheses, **there is no analytic need to make \(F\) vanish near \(D_{m+1}\)**.

For \(F=1\), the formula is therefore a valid explicit asymptotic coefficient. It is a positive RLCT leading constant if an effective extremising face has positive mass; otherwise it can be zero.

At zero field,
\[
S_\lambda(0)=\Gamma(\lambda),
\]
so the full face formula reduces to
\[
\frac{\Gamma(\lambda)}
{(m-1)!\prod_{j\in J}2k_j}
\int \rho(0_J,w)\prod_{i\notin J}w_i^{h_i-2k_i\lambda}\,dw\,d\nu_p.
\]
If the population library supplies `coeff 1` as the coefficient of the same integral at the same scale, equality follows by **uniqueness of the limit**, independently of its stratum-measure identification theorem.

### But “including mass on the deeper fibre” is generally the wrong reading

Using closed rather than open face boxes does not create additional boundary mass. An integrable density with respect to the free-coordinate Lebesgue measure gives zero mass to
\[
\{w_i=0\}\quad(i\notin J).
\]

In particular, if—as posited in (c)—the face map sends almost every point with all free coordinates positive into \(X\), then the full face pushforward is concentrated on \(X\). Its restriction to \(X\) has the **same total mass**.

The deeper fibre can lie in the *topological support* of the resulting measure without carrying measure mass.

Therefore the following three claims cannot all hold without some additional distinction:

1. the full coefficient is the integral of these finite face densities;
2. almost every face-reference point maps into \(X\);
3. restricting to \(X\) loses mass whenever \(D_{m+1}\ne\varnothing\).

In particular, **“\(\nu(X)\le c\), with equality iff \(D_{m+1}=\varnothing\)” is not reconciled merely by saying that closed face boxes include the deeper fibre.** Nonemptiness of a removed set does not imply positive measure.

I would audit the exact earlier statement and its hypotheses. Possibilities include:

- it was only an inequality, or only a sufficient condition for equality;
- it concerns a different residue measure or coefficient;
- its zero-order hypotheses are not available here;
- its geometry does not establish the a.e.-in-\(X\) assertion used in (c).

Do not carry the proposed strictness interpretation into the mirror without resolving this.

## (c) Extending identification beyond compactly supported tests

The cleanest route is a **general integrable pushforward lemma**, rather than another asymptotic argument.

For each contributing face, establish:

1. measurability of the face map;
2. a.e. membership of its image in \(X\);
3. integrability of the empirical face density;
4. integrability of
   \[
   (F\circ\mathrm{faceMap})\,\mathrm{empFaceDensity}.
   \]

Then use integration against `withDensity`, pushforward, and the finite sum over faces and pieces.

Under `ChartLeading`, item 3 follows from the strict non-resonant exponent inequalities. Item 4 follows from boundedness of \(F\) on the compact face images. This directly handles admissible smooth \(F\), without requiring their support to be compact in \(X\).

A useful abstract API would be:

> If \(F\circ\mathrm{faceMap}\) times the face density is integrable on every contributing face, then the integral of \(F\) against the empirical stratum measure equals the sum of the face integrals.

The test-function theorem then becomes a corollary.

An alternative is to reuse population integrability through the bound
\[
0<
\frac{S_\lambda(a)}{\Gamma(\lambda)}
\le C_{\lambda,M}
\qquad (|a|\le M).
\]
When the zero-field/population identity is available, this gives domination of the empirical measure by \(C_{\lambda,M}\nu^{\rm pop}\), allowing reuse of `integrable_stratumMeasure`.

**The direct face-integrability route is cleaner for Rank 2:** it avoids importing the zero-order bridge.

There is also an important consequence: if the a.e.-in-\(X\) statement and compact-image bounds hold for every smooth \(F\), this route identifies the limit for **all smooth \(F\)**, not merely admissible ones. That would settle the total-mass question in (b) affirmatively as equality—not as missing deeper-fibre mass.

## (d) The zero-field population identity

Keep the two assertions separate:

- **Analytic theorem:** the empirical limit is the measure defined by the branchwise face densities.
- **Population comparison:** under the already-proved zero-order condition,
  \[
  \nu(0)=\nu^{\rm pop}.
  \]

`ChartLeading` constrains the listed pieces. It cannot, without a coverage theorem, control exact-stratum points not represented by those pieces.

A possible bridge is:

1. every relevant exact-stratum point belongs to a transport chart source;
2. the geometric walls there are represented by the chart coordinates;
3. geometric ratios and multiplicities agree with the chart data;
4. chart-leading inequalities imply the required zero-order condition.

If the zero-order condition is global, coverage merely over the prior’s support may still be insufficient for that particular declaration. One might instead prove a supported measure identity.

**For the paper now, your proposed separation is the right choice.** Additionally state that zero field recovers the population integral and hence its asymptotic coefficient whenever the population coefficient theorem applies. That sanity check need not await a global measure identity.

## (e) Ranks 3–5

### Rank 3: uniformity on compact sets of branch representatives

Yes: use a compactness-plus-Lipschitz argument. A direct derivative bound is simpler than comparing temperature-shifted nearby fields.

Write
\[
t=N u^{2k},\qquad
g_t(a)=e^{-t+\sqrt t\,a}.
\]
For \(|a|,|b|\le M\), the mean-value estimate gives
\[
|g_t(a)-g_t(b)|
\le |a-b|\sqrt t\,e^{-t+M\sqrt t}.
\]
Using
\[
M\sqrt t\le t/4+M^2,
\qquad
\sqrt t\,e^{-t/4}\le \sqrt{2/e},
\]
we obtain
\[
\boxed{
|g_t(a)-g_t(b)|
\le \sqrt{2/e}\,e^{M^2}|a-b|e^{-t/2}.
}
\]

Consequently,
\[
|I_N(\xi,\eta)-I_N(\zeta,\eta)|
\le C_M\|\xi-\zeta\|_\infty I_{N/2}(0,|\eta|).
\]

After normalization by
\[
s_N=N^{-\lambda}(\log N)^{m-1},
\]
your half-temperature boundedness theorem supplies an eventual Lipschitz constant independent of \(N\).

For a finite collection of pieces, let
\[
E=\prod_p C(K_p),\qquad
K_p=\mathrm{Base}_p\times[0,b]^{d_p},
\]
with the maximum sup norm. Here assume the \(K_p\) are compact metric spaces; otherwise specify an appropriate bounded-continuous function space.

Define \(T_N:E\to\mathbb R\) by the normalized sum of core box integrals, and \(T:E\to\mathbb R\) by the summed face functional. Prove:

> **Uniform asymptotics on compact field families.**  
> Suppose \(T_N(f)\to T(f)\) for every \(f\in E\). Suppose that for every \(R\), the maps \(T_N\), eventually in \(N\), are uniformly \(L_R\)-Lipschitz on the radius-\(R\) ball, and \(T\) is locally Lipschitz. Then, for every compact \(C\subset E\),
> \[
> \sup_{f\in C}|T_N(f)-T(f)|\longrightarrow0.
> \]

Proof: choose a finite \(\varepsilon\)-net in \(C\), use pointwise convergence at its centres, and bound the two approximation errors by the finite-\(N\) and limiting Lipschitz constants.

Arzelà–Ascoli is useful for *establishing tightness or compactness of field families*, but is not needed inside this lemma.

It is worth defining \(T_N,T\) on **all continuous branch tuples**, rather than only tuples accompanied by a global `RootField` witness. The analytic box formulas make sense there, and this considerably simplifies the probabilistic interface.

### Rank 4: convergence in distribution

Assume jointly
\[
L_n=(\operatorname{loc}_{n,p})_p\Rightarrow G
\quad\text{in }E.
\]
Piecewise marginal convergence is not enough; joint convergence is the right hypothesis.

Compact-uniform convergence and tightness give
\[
T_n(L_n)-T(L_n)\xrightarrow{\mathbb P}0.
\]
Continuity of \(T\) gives
\[
T(L_n)\Rightarrow T(G).
\]

For the tail, if the global root-field bound satisfies \(M_n=O_p(1)\), then
\[
\frac{|\mathrm{tail}_n|}{s_n}
\le C e^{M_n^2/2}\frac{e^{-\delta n/2}}{s_n}
\xrightarrow{\mathbb P}0.
\]
Thus
\[
\boxed{
\frac{Z_n^{\rm emp}[F;\xi_n]}{s_n}
\Rightarrow T(G).
}
\]

No independence between the core fields and their tail bounds is needed.

Writing \(T(G)=\int F\,d\nu(G)\) is legitimate if \(\nu(G)\) is defined directly from branch tuples. If that notation requires a global root field, separately establish that the limiting tuple satisfies the necessary compatibility conditions.

### Rank 5: Gaussian expectation—and separately annealed convergence

For a centred Gaussian face value with variance \(v\),
\[
\mathbb E S_\lambda(G)
=\Gamma(\lambda)(1-v/2)^{-\lambda},
\qquad v<2.
\]

Hence Tonelli gives the expected positive residue measure; signed \(F\) requires absolute integrability. A uniform facewise variance gap
\[
v\le 2-\varepsilon
\]
is a convenient sufficient condition. Pointwise \(v<2\) alone need not ensure integrability after integrating over the faces.

No independence between different face values is needed: only the one-point Gaussian law enters this expectation.

For a constant variance \(v\), the expected limiting coefficient is
\[
(1-v/2)^{-\lambda}
\]
times the zero-field face coefficient. Identifying the latter with a population stratum integral requires the comparison hypotheses from (d).

**Crucial non-implication:** Rank 4 plus this calculation does not establish
\[
\mathbb E[Z_n^{\rm emp}/s_n]\to\mathbb E[T(G)].
\]
For that, prove uniform integrability or work directly with finite-\(n\) expectations. \(M_n=O_p(1)\) is not enough. For example, a suitable uniform exponential moment bound on \(M_n^2\), combined with your deterministic domination, would suffice.

### Suggested size and priority

These are rough planning estimates, not repository-based line counts.

| Rank | Deliverable | Relative size |
|---|---|---|
| 3 | Finite-\(N\) local Lipschitz bound; abstract compact-uniform lemma; application to pieces | Medium: roughly 300–800 Lean lines |
| 4 | Joint field-law transfer, random tail removal, measurability/tightness interface | Medium–large: roughly 400–1200, highly dependent on existing probability APIs |
| 5a | Gaussian expectation of the limiting face measure | Small–medium: roughly 150–400 with the stated Gaussian integral lemma |
| 5b | Actual annealed convergence under explicit UI assumptions | Separate medium task; potentially larger if UI infrastructure is missing |

Priority: **3 → 4**, with **5a parallelisable**. Keep 5b visibly separate. Likewise, do not put support-adapted weakening of `ChartLeading` on the critical path.

## (f) Suggested paper statement

### Theorem A — Empirical leading residue for a chart-leading transport

Let a resolved localisation admit a finite transport presentation satisfying the standing normal-crossing, compactness, measure-decomposition, and tail-gap hypotheses. Assume the chart phase constants are one.

Let \(\lambda>0\) and \(m\ge1\). Suppose that on every transport piece,
\[
\lambda\le\frac{h_{p,i}+1}{2k_{p,i}}
\quad\text{for all }i,
\qquad
\#\left\{i:\frac{h_{p,i}+1}{2k_{p,i}}=\lambda\right\}\le m.
\]
Let \(\psi\) be a bounded measurable root field with continuous branch representatives \(\widehat\psi_p\) on the pieces’ closed parameter boxes.

For smooth \(F\), under the standing amplitude and tail-integrability hypotheses, set
\[
Z_N^{\rm emp}[F;\psi]
=
\int_U
F(P)\exp\!\left(
-NK(\pi(P))+\sqrt{N}\sqrt{K(\pi(P))}\,\psi(P)
\right)d\mu_U(P).
\]
Then
\[
N^\lambda(\log N)^{-(m-1)}Z_N^{\rm emp}[F;\psi]
\longrightarrow \mathcal R_{\lambda,m}(F;\widehat\psi),
\]
where, writing
\[
J_p=\left\{i:\frac{h_{p,i}+1}{2k_{p,i}}=\lambda\right\},
\]
the residue is
\[
\mathcal R_{\lambda,m}(F;\widehat\psi)
=
\sum_{p:\,|J_p|=m}
\frac{1}{(m-1)!\prod_{j\in J_p}2k_{p,j}}
\int_{\mathrm{Base}_p}
\int_{(0,b]^{J_p^c}}
\operatorname{amp}_p(s;0_{J_p},w)\,
S_\lambda\!\left(\widehat\psi_p(s;0_{J_p},w)\right)
\prod_{i\notin J_p}w_i^{h_{p,i}-2k_{p,i}\lambda}
\,dw\,d\nu_p(s).
\]

For test functions compactly supported in \(X=U\setminus D_{m+1}\),
\[
\mathcal R_{\lambda,m}(F;\widehat\psi)
=
\int_X F\,d\nu^\lambda_m(\widehat\psi),
\]
where the empirical stratum measure is defined by these branchwise face densities.

**Lean annotations:** `ChartLeading`, `hasLeadingTerm_empZ`, `hasLeadingTerm_empZ_eq_integral`.

### Geometric explanation

> `ChartLeading` says that no coordinate wall in the chosen localised transport has ratio below \(\lambda\), and no transport chart contains more than \(m\) coordinate walls of ratio \(\lambda\); it constrains the presented charts even where the prior amplitude vanishes.

### Explicit non-claims

- The hypotheses do not assert that the displayed coefficient is nonzero or that the pair is the effective RLCT pair.
- `ChartLeading` is not presently derived from pointwise extremality on the supported zero fibre.
- The theorem is deterministic for a fixed bounded field; an \(N\)-dependent empirical field requires the subsequent function-space convergence theorem.
- Convergence merely of traces on \(Z_0\) is not asserted to suffice.
- Fields are branchwise/normal-side fields, including the signs required by signed monomials.
- The all-smooth face formula has no vanishing-near-\(D_{m+1}\) hypothesis; the currently landed stratum-integral identification is stated for tests.
- Agreement with the population stratum measure at zero field is a separate theorem under its zero-order hypothesis.
- Gaussian expectation of the limiting residue is not, without additional integrability, an annealed limit theorem.

That wording presents Rank 2 as the substantial result it is, while leaving the geometric bridge, stronger identification, and probabilistic transfer as clearly delimited next steps.