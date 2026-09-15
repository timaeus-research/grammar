## Audit verdict

On the interfaces you report, Stage 7 closes the **deterministic resolved expansion**. The substantive remaining identification is the resolved graded formula, not another assembly theorem.

Two qualifications should be kept explicit:

1. `SmoothRootField` expresses **branchwise ambient smooth extendibility**, not a globally smooth field across the divisor.
2. The “population amplitude multiplied by \(S_\mu(\widehat\psi)/\Gamma(\mu)\)” interpretation is automatically valid **piecewise**; it need not define a single smooth amplitude downstairs.

I am auditing the stated interfaces here, rather than independently inspecting `41370fe` or the earlier numbered audits.

## (a) `SmoothRootField`

### (i) Is this the right notion?

**Yes, as a sufficient formal notion**, with the following precise reading:

> On each chart–orthant piece, the root field agrees on the open piece with the restriction of a smooth function of the ambient chart coordinates, and this representative supplies its extension to the walls.

The orthant sign inside `Tm` is consistent with this. For two orthants of one chart, `Lψ p` may be different smooth functions. Their values are constrained only where the corresponding pieces represent actual points of \(U\): there, `loc_eq` forces agreement with the same downstairs \(\psi\).

For example, if locally
\[
K\circ\pi=u^{2k},\qquad (K-K_n)\circ\pi=u^k a(u),
\]
then
\[
\frac{(K-K_n)\circ\pi}{\sqrt{K\circ\pi}}
=\frac{u^k}{|u^k|}a(u).
\]
For odd \(k\), the two branch representatives are \(a\) and \(-a\). Evaluating those representatives at the signed chart coordinate is correct. The sign in the coordinate map and the sign in the representative perform different jobs; they are not a double counting.

There is no hidden inconsistency in `loc_eq_Lψ` together with `loc_eq`. These are compatibility requirements, not assertions that arbitrary choices of representatives work. In particular:

- pieces overlapping downstairs must agree on the represented open sets;
- opposite-wall limits need not agree;
- smoothness and agreement on the open piece determine the relevant boundary traces and jets; the boundary values are not free extra data.

Two wording cautions:

- Global `ContDiff ℝ ∞ (Lψ p)` on all chart coordinate space is stronger than merely being smooth up to the relevant compact piece. It is a convenient sufficient hypothesis, not a claimed characterization of every possible “wall-smooth” root field.
- This theorem does **not** construct such representatives for a statistical model or for its empirical fields. That remains a model-dependent hypothesis.

### (ii) The global bound

The global bound is entirely reasonable for the public theorem, especially because it matches `hasLeadingTerm_empZ`.

The natural weaker tail hypothesis is
\[
|\psi|\le M\quad\text{a.e. for the total-variation measure of the tail integral}.
\]
Equivalently, an appropriate bound on the amplitude-supported tail is enough. A pointwise support formulation is often easier to use, but the a.e. formulation is analytically sharp.

I would **not refactor the main interface now**. If useful, expose a lower-level tail estimate with the weaker hypothesis. The compact-piece bounds already come from the smooth representatives; they do not require a global bound away from those pieces.

### (iii) Normalisation

Yes: state the normalisation explicitly, once, adjacent to the resolved theorem:
\[
Z_\psi(N)=\int_U F(x)
 \exp\!\left(-NK(x)+\sqrt N\,\sqrt{K(x)}\,\psi(x)\right)\,dx.
\]
For the statistical application,
\[
\psi_n=\frac{\sqrt n\,(K-K_n)}{\sqrt K}
\quad\text{on }\{K>0\},
\qquad
Z_{\psi_n}(n)=\int F e^{-nK_n},
\]
where the latter identity requires the defining relation on the integration domain, at least a.e.

Emphasise that \(\sqrt K\) is the **nonnegative** square root. Thus the branch signs are contained in the representatives of \(\psi\). This fixes both the positive sign of the empirical perturbation and the Mellin replacement
\[
S_\mu(a)=\int_0^\infty s^{\mu-1}e^{-s+a\sqrt s}\,ds.
\]

Most importantly, the resolved theorem is an asymptotic statement for a **fixed** \(\psi\). Substituting \(\psi=\psi_n\) and \(N=n\) requires uniform control; it is not an immediate consequence of a fixed-field expansion.

## (b) Resolved graded identification

### Recommended route: compare coefficients before expanding faces

Do **not** redo the rectangular collapse, and do **not** initially push dilation through every face integral.

Prove a rectangular empirical–population coefficient identity:
\[
\operatorname{empCoeffRect}(\eta,\zeta;\mu,c-1)
=
\operatorname{smoothCoeff}_{b}
 \left(\frac{\eta S_\mu(\zeta)}{\Gamma(\mu)};
       \mu,c-1\right),
\]
under the appropriate deep-vanishing hypothesis and with the existing population rectangle conventions.

Then invoke the already-proved **general-\(b\)** population face formula on the right.

This separates three independent mechanisms:

1. dilation;
2. the empirical replacement rule;
3. the population face calculation.

### Suggested proof sequence

Assume \(c\ge1\), \(\mu>0\), and positive side lengths, together with the existing dimension/degree hypotheses.

**1. Transport deep jets under dilation.**

For \(D_b(v)=bv\), positive dilation preserves zero-coordinate patterns:
\[
D_b(\operatorname{deepSet}(d,1,c))
=\operatorname{deepSet}(d,b,c).
\]
Then
\[
\partial^\alpha(\eta\circ D_b)
=b^\alpha(\partial^\alpha\eta)\circ D_b
\]
transports the required `JetsZeroOn`.

This should be a reusable dilation lemma. No new geometric argument concerning \(F\) is needed: use `jetsZeroOn_amp_deep` first, then this lemma. Match the existing convention carefully: the geometric hypothesis is vanishing near \(D_{c+1}\), whatever index the implementation uses for the corresponding `deepSet`.

**2. Eliminate upper log degrees.**

Obtain
\[
c^1_{\mu,j}=0\qquad(j\ge c).
\]
Also ensure that the weighted population amplitude has the required deep jets. This follows from Leibniz:
\[
\eta\text{ has zero jets}\Longrightarrow
\eta\,S_\mu(\zeta)/\Gamma(\mu)\text{ has zero jets},
\]
to the orders required by the population theorem.

**3. Apply scaling only after upper-degree vanishing.**

In general, dilation mixes log degrees:
\[
c^b_{\mu,q}
=A_bB_b^{-\mu}
 \sum_{j\ge q}\binom jq(\log B_b)^{j-q}c^1_{\mu,j}.
\]
At \(q=c-1\), the preceding vanishing reduces this to
\[
c^b_{\mu,c-1}
=A_bB_b^{-\mu}c^1_{\mu,c-1}.
\]

The unit replacement theorem and the corresponding population scaling law now give the desired rectangle identity. Here the useful definitional identity is
\[
\left(\frac{\eta S_\mu(\zeta)}{\Gamma(\mu)}\right)\circ D_b
=\frac{(\eta\circ D_b)S_\mu(\zeta\circ D_b)}{\Gamma(\mu)}.
\]

If a population coefficient scaling lemma is missing, prove that reusable lemma—possibly by expansion uniqueness—rather than repeating Mellin collapse.

**4. Apply the general-\(b\) population face formula.**

Do this fibrewise in the base variable, then integrate and sum over pieces. Prefer equality of the canonical coefficient integrands before integration; this avoids needing a separate dominated-convergence argument at this stage.

### Constants audit

The normalisation check is:
\[
\Gamma(\mu)\,
\partial_J^\alpha
 \left[\frac{\eta S_\mu(\zeta)}{\Gamma(\mu)}\right]
=
\partial_J^\alpha[\eta S_\mu(\zeta)].
\]
Consequently the empirical face expression, when written using
\(\partial_J^\alpha[\eta S_\mu(\zeta)]\), has the population factor
\[
\frac{1}{(c-1)!\prod_{j\in J}2k_j},
\]
with **no remaining \(\Gamma(\mu)\)**. All Taylor factorials and signs must remain exactly where the population `faceW`/`faceCoef_top_eq` convention places them.

There is also a useful independent scaling check. Under
\[
A_b=\prod_i b_i^{h_i+1},\qquad B_b=\prod_i b_i^{2k_i},
\]
the derivative contributes \(\prod_{j\in J}b_j^{\alpha_j}\), and substitution in the complementary face integral cancels the complementary factors of \(A_bB_b^{-\mu}\). The remaining factors are
\[
\prod_{j\in J}b_j^{h_j+1+\alpha_j-2k_j\mu}=1
\]
by resonance. Thus no unexplained powers of \(b\) should survive in the general-\(b\) face formula.

This verifies the scaling mechanism; the exact `faceW` factorial convention must be checked against its actual definition, not inferred from its name.

### What the resolved corollary should say

Define a **branchwise weighted stratum sum** using
\[
\eta_{p,s,\mu}(v)
=\frac{\operatorname{amp}_{p,s}(v)
 S_\mu(L\psi_p(Tm_p(s,v)))}{\Gamma(\mu)}.
\]
Then prove
\[
\operatorname{resolvedCoeff}_\xi(\mu,c-1)
=\operatorname{weightedStratumSum}_\xi(\mu,c).
\]

Calling this “the population stratum formula with the replacement
\(\eta\mapsto\eta S_\mu(\widehat\psi)/\Gamma(\mu)\)” is correct. Calling it literally `Ξ.coeff` for a new global smooth downstairs amplitude needs an additional descent/compatibility theorem. Opposite branch representatives can obstruct that interpretation.

## (c) Recovering the leading theorem

**Yes—this is worth doing, and is probably the best next closure unit.**

The clean statement is, under the shared hypotheses of the two theorems and \(m\ge1\),
\[
\operatorname{resolvedCoeff}_\xi(\lambda,m-1)
=
\sum_p\int_{\operatorname{Base}_p}
       \operatorname{pieceFaceLimit}_{p,\xi}\,d\nu_p.
\]
This identifies the expansion coefficient with the independently established leading formula, without deep vanishing.

Include the coefficient-support consequences if inexpensive:
\[
\operatorname{resolvedCoeff}_\xi(\mu,q)=0
\quad(0<\mu<\lambda),
\qquad
\operatorname{resolvedCoeff}_\xi(\lambda,j)=0
\quad(j\ge m).
\]

### Two routes

**Shortest consistency route:** a general lemma combining a `CutoffExpansion` with an independently known leading limit.

A finite limit after division by
\(N^{-\lambda}(\log N)^{m-1}\) forces all more dominant expansion terms to vanish and identifies the coefficient at that order. The proof uses the finite ordered asymptotic scale below a cutoff \(L>\lambda\). It does not assume the limiting coefficient is nonzero.

This route directly connects the two independently proved results and avoids redoing resonance combinatorics.

**Structural route:** prove support from the box face engine.

Possible poles have the form
\[
\mu=\frac{h_i+\alpha_i+1}{2k_i},\qquad\alpha_i\ge0.
\]
`ChartLeading λ m` excludes poles below \(\lambda\). At \(\lambda\), resonance requires \(\alpha_i=0\) in a critical coordinate, and there are at most \(m\) such coordinates. Hence the maximum log degree is \(m-1\).

Both are sound. I would choose the first for a small closure unit and retain the second if those support lemmas already nearly exist.

**Lattice caveat:** state the generic extraction lemma on the expansion lattice, or explicitly use zero extension off it. `ChartLeading λ m` alone need not force an arbitrary lower bound \(\lambda\) to belong to the common lattice. Likewise handle \(m-1\) beyond the stored degree by the existing padding/zero convention.

The resulting face expression is precisely the \(\alpha=0\) replacement rule at \(\lambda\), without the deep-vanishing hypothesis. It does not, by itself, assert that this coefficient is nonzero.

## (d) Random fields

For the paper, **the programme can stop at the deterministic theorem**, preferably with (b) and (c) added. Stage 7 alone should not be advertised as a random-field expansion.

For a next analytic unit, I recommend:

> **Continuity of a finite resolved coefficient vector under finite-order, compact-uniform convergence of branch representatives.**

Fix \(L\), the decomposition, and a sufficiently large jet order for all coefficients with \(0<\mu<L\). Assume the required ambient derivatives of \(L\psi_{n,p}\) converge uniformly on the compact chart images to those of \(L\psi_p\). Then
\[
\operatorname{resolvedCoeff}_{\xi_n}(\mu,q)
\longrightarrow
\operatorname{resolvedCoeff}_{\xi}(\mu,q)
\]
for the finite lattice vector under consideration.

Sequential compact-uniform convergence gives eventual uniform jet bounds. The Mellin domination has the standard shape
\[
C\,s^{\mu-1}(1+\sqrt s)^r e^{-s+M\sqrt s},
\]
which is integrable for \(\mu>0\). Apply dominated convergence through the face/Mellin construction and then the finite base integrals.

Keep this unit deterministic and avoid introducing a full function-space topology if a sequential statement suffices.

Three distinctions matter:

- Stage 7 gives constants uniform over the **base**, not automatically over a sequence of fields.
- Coefficient continuity alone does not control the **diagonal remainder** at \(N=n\).
- A stochastic result additionally needs measurable random coefficients and high-probability control of the relevant jet bounds and tail bound.

For a fixed cutoff, deterministic uniform jet and tail bounds yield a uniform remainder theorem for a family. Tight versions can then give an \(O_{\mathbb P}\)-type remainder at the corresponding rate. But establishing that probabilistic wrapper is a separate unit, not a corollary of pointwise existence of constants.

## (e) Paper-facing statement and priorities

### Suggested paragraph

> Let \(\psi\) be a bounded deterministic root field whose representative on each resolved chart–orthant piece extends smoothly in the chart coordinates, including at the boundary faces. Then the empirical partition function
> \[
> Z_\psi(N)=\int_U F\,e^{-NK+\sqrt N\,\sqrt K\,\psi}
> \]
> admits a cutoff asymptotic expansion on the same common exponent lattice and with the same logarithmic degree bound as the population resolved expansion. Its coefficients are finite sums of base integrals of the canonical empirical box coefficients. They are uniquely determined on this lattice and degree range. At \(\psi=0\), the partition function and all resolved coefficients agree with their population counterparts. The theorem allows different smooth branch representatives on different orthants; it does not require the root field to extend smoothly across the divisor.

### Non-claims

- No construction of smooth root representatives for an arbitrary statistical model.
- No smooth descent across walls or automatic global weighted-amplitude interpretation.
- No uniform expansion over varying fields without uniform hypotheses.
- No random-field convergence, tightness, or stochastic diagonal remainder theorem.
- No resolved graded stratum identification until (b) lands.
- No nonvanishing of a proposed leading coefficient without an additional argument.
- No claim that every point of the common lattice carries a nonzero coefficient.

### Recommended order and small-unit split

| Priority | Unit | Scope |
|---|---|---|
| **1** | **(c) Leading consistency** | Generic expansion/leading-limit compatibility, then the resolved face-limit identification. |
| **2a** | **(b) Rectangle replacement** | Deep-jet dilation, upper-degree vanishing, rectangular empirical–population identity. |
| **2b** | **(b) Resolved graded formula** | Fibrewise general-\(b\) face formula, base integration, piece sum, weighted stratum statement. |
| **3** | **(d) Coefficient continuity** | First prove box/family continuity; resolved finite-vector continuity can be a separate wrapper unit. |

These are plausible \(\lesssim500\)-line units given the reported infrastructure, not reliable line-count guarantees.

**Bottom line:** close (c), then finish (b) without repeating the rectangular analysis. Treat (d) as a separate stability/probability programme. The present resolved expansion already supports a substantial and accurately delimited deterministic theorem.