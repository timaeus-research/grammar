## Recommendation

Your prior is substantially right: **P1 → P3 → P2**, with **a targeted P7 review before and during those units**, rather than leaving all fidelity checking until the end.

The next milestone should be:

> **A leading-order posterior theorem, with a geometrically readable coefficient and a non-vacuous executable example.**

Do not yet describe it as the paper’s full “expectation expansion”: it is the leading-order expectation limit, plus relative-rate statements when separate numerator asymptotics are available.

One limitation of this consult: several appendix definitions and section hypotheses are omitted. I can assess the mathematical contracts and identify audit obligations, but cannot certify their implementation from these excerpts alone.

---

# Q1. Ranking and a five-unit programme

### Priority ranking

| Priority | Candidate | Reason |
|---|---|---|
| 1 | **P1: posterior expectations** | Small proof distance; immediately delivers the paper-facing statistical object. |
| 2 | **P3: coefficient formula** | Turns the posterior limit from a ratio of opaque choices into interpretable face integrals. Must include non-all-minimal tied pieces. |
| 3 | **P2: one-chart corollaries and example** | Discharges the strongest artificial hypothesis in an important special case and tests normalization. |
| Gate | **P7: fidelity review** | A short review now is essential; a comprehensive review can follow the above. |
| 4 | **P4: supplied weights** | Important infrastructure, but **does not itself remove normal-coordinate dependence of weights**. |
| 5 | **P5: normal-dependent phase unit** | A genuine analytic extension, with considerably greater proof risk. |
| 6 | **P6: tube-measure identification** | Valuable after the concrete coefficient API is stable. Otherwise two representations are moving simultaneously. |

P4 versus P5 depends on your next advertised generality target. For realistic multi-chart applications, P4 is probably first, but its scope must include **putting suitable weights into the amplitude**, not merely changing the cover structure.

### Proposed five units

1. **Abstract posterior transfer**
   - Same-pair limit.
   - Different-pair normalized limit.
   - Eventual denominator positivity.
   - Explicit signed-numerator and zero-coefficient handling.

2. **Product-chart posterior theorem**
   - Denominator \(F=1\), positive coefficient from the existing dominant-face theorem.
   - Arbitrary admissible observable, without requiring its nonnegativity.
   - A small moment wrapper only where CCXL already provides the necessary certificates.

3. **Tied-stratum classification and all-minimal coefficient formula**
   - Classify every extremal tied \(I\).
   - Assemble the reflected all-minimal formula.
   - Prove coefficient uniqueness/choice independence.

4. **General tied-piece residual-face formula**
   - Retain non-minimal normal coordinates as integration variables.
   - Assemble the total coefficient, and hence an explicit posterior-limit formula.

5. **One-chart discharge and regression examples**
   - \(r=1\), automatic `weight_eq`.
   - Whole-box corollary.
   - \(K=x^2y^2\), including the coefficient.
   - Ideally also \(K=x^2y^4\), which tests the non-all-minimal contribution.

Run a targeted fidelity checklist through all five. If limited to three units, combine 1–2, do 3, then do 5; defer the genuinely general part of P3 rather than publishing an incomplete “total coefficient” formula.

---

# Q2. Contracts for P1

## 1. Fix the notation first

In your existing API,
\[
Z_N[F]=R.\mathrm{boltzmannIntegral}\;F\;K\;p\;N
\]
already contains the density \(p\).

Thus define
\[
E_N[\varphi]=\frac{Z_N[\varphi]}{Z_N[1]},
\]
**not** by passing \(\varphi p\) and \(p\) as observables while also supplying the existing `p` argument.

A suitable schematic definition is:

```lean
noncomputable def posteriorExpectation
    (R : ResolutionCover d ι)
    (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (φ : (Fin d → ℝ) → ℝ) (N : ℝ) : ℝ :=
  R.boltzmannIntegral φ K p N /
    R.boltzmannIntegral (fun _ => 1) K p N
```

Lean’s totalized division is adequate. Document that this function is assigned the usual totalized value when the denominator vanishes, and prove that **eventually it is the genuine normalized expectation**. No dependent “posterior defined only when positive” API is needed for asymptotics.

## 2. Abstract transfer module

Use `HasLeadingTerm.tendsto_div_ratio` as the central theorem.

### Same-pair specialization

```lean
theorem HasLeadingTerm.tendsto_div_same_pair
    (hnum : HasLeadingTerm Znum cnum lam k)
    (hden : HasLeadingTerm Zden cden lam k)
    (hcden : cden ≠ 0) :
    Tendsto (fun N => Znum N / Zden N) atTop
      (𝓝 (cnum / cden))
```

Proof: the existing ratio theorem, followed by eventual cancellation of the common scale. Establish scale nonvanishing on, say, \(N>1\); do not attempt global cancellation.

**Important:** allow `cnum = 0`. That is one of the main benefits of using `HasLeadingTerm`, rather than requiring an asymptotic equivalence for the numerator.

### Eventual positivity

```lean
theorem HasLeadingTerm.eventually_pos
    (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    ∀ᶠ N in atTop, 0 < Z N
```

Reuse the existing bridge from a nonzero leading coefficient to equivalence if available. Otherwise use convergence of \(Z/\mathrm{scale}\) and eventual positivity of the scale.

This only gives eventual positivity; positivity for every finite \(N\) is a separate integral theorem and unnecessary for the main limit.

### Different-pair specialization

Keep the primary API in terms of **a ratio of scales**:

\[
\frac{E_N}{S_{\lambda_\varphi,k_\varphi}(N)/
                  S_{\lambda_1,k_1}(N)}
\longrightarrow \frac{c_\varphi}{c_1}.
\]

This is almost exactly `tendsto_div_ratio`.

Then derive:

- If \(c_\varphi\ne0\), a relative asymptotic equivalent at that scale ratio.
- If
  \[
  \lambda_\varphi>\lambda_1
  \quad\text{or}\quad
  \lambda_\varphi=\lambda_1,\;k_\varphi<k_1,
  \]
  then \(E_N\to0\).
- If \(c_\varphi=0\), obtain **little-o of that scale ratio**, not an equivalent with coefficient zero.

For display,
\[
\frac{S_{\lambda_\varphi,k_\varphi}}{S_{\lambda_1,k_1}}
=N^{-(\lambda_\varphi-\lambda_1)}
 (\log N)^{k_\varphi-k_1}.
\]
But do not encode the last exponent using truncated `Nat.sub`. Keep a quotient of natural powers, or cast to integers/reals before subtraction.

Also distinguish two claims:

1. A zero coefficient at the denominator’s pair proves \(E_N\to0\).
2. A specific improved rate requires a separate numerator certificate at an improved pair.

The first does not supply the second.

## 3. Product-chart wrapper

Let
\[
\lambda_*=\mathrm{coverLam},\qquad k_*=\mathrm{coverDeg}.
\]
Obtain:

- A numerator certificate from `hasLeadingTerm_boltzmannIntegral_of_productChartsD`.
- A positive denominator coefficient from
  `boltzmannIntegral_isEquivalent_of_productCharts_extremal`, specialized to \(F=1\).
- The denominator leading-term certificate from the corresponding `D` theorem.

The intended contract is:

```text
all existing product-chart analytic/integrability hypotheses
+ active-coordinate nonemptiness
+ p ≥ 0
+ r_i ≥ 0
+ one extremal all-minimal stratum
+ positive dominant-face measure for F = 1
⇒
  0 < c₁
  ∧ eventually 0 < Z_N[1]
  ∧ E_N[φ] → cφ / c₁.
```

The numerator needs the existing admissibility hypotheses, **not** `φ ≥ 0`, provided the leading-term theorem indeed accepts signed observables.

The dominant-face condition with \(F=1\) is enough. No additional assertion “\(p>0\) somewhere” is required: positive measure of the specified face already includes the relevant positivity of \(p\), and is stronger and better located than an arbitrary pointwise witness.

### Useful supporting lemmas

Prioritize:

- `dominantFace_one`: simplify away \(1>0\).
- Constant observable: \(E_N[a]\to a\).
- Coefficient linearity in the observable.
- Coefficient uniqueness at a fixed pair.

Linearity and uniqueness are particularly useful because different observables currently produce different choice-selected atlases. They let you reason about coefficients without comparing those atlases.

### A warning about vanishing observables

Do not yet state vaguely:

> “If \(\varphi\) vanishes on dominant faces, then \(c_\varphi=0\).”

Specify which faces and what measure. For a non-all-minimal tied piece, the leading coefficient samples the locus where **the minimal coordinates vanish**, while the other normal coordinates remain integration variables.

Vanishing merely at the full normal origin of every piece is not sufficient.

---

# Q2. Contracts for P3

## 1. First prove the exact tied-stratum classification

For a chart \(i\), put
\[
M_i=\{j\in\operatorname{supp}e_i:
             (h_{ij}+1)/e_{ij}=\lambda_*\}.
\]

An extremal tied piece \(I\) satisfies
\[
\operatorname{pieceLam}(I)=\lambda_*,
\qquad
\operatorname{pieceMult}(I)-1=k_*.
\]

Since \(\lambda_*\) is globally minimal,
\[
\operatorname{pieceMult}(I)=|I\cap M_i|.
\]
By the definition of \(k_*\), this forces
\[
|M_i|=k_*+1,\qquad M_i\subseteq I.
\]

Conversely, those two conditions imply that \(I\) is tied.

Thus:

> **Tied pieces are exactly the supersets of the full minimal set in a chart attaining maximal minimal multiplicity.**

Among them, the all-minimal piece is exactly \(I=M_i\). All other tied pieces have residual normal coordinates.

This is the key combinatorial interface for the whole coefficient programme.

## 2. All-minimal assembly

For `I = M_i`, reuse:

- `IsPieceAtlasData`;
- the exposed atlas equality;
- `ratioExp_normal_eq`, `minRatio_normal_eq`, `multCount_normal_eq`;
- `coeff_of_all_minimal'`;
- the facts that reflection fixes normal zero and preserves the exponents and scalar phase.

The resulting reflected sum should have the form
\[
2^{|I|}\,
\frac{\Gamma(\lambda_*)}{(|I|-1)!}
\prod_{j\in I}\frac1{e_{ij}}
\int_{\mathrm{base}}
 \beta(z)\,q(z)^{-\lambda_*}\,A(z,0)\,dz.
\]

But **derive the \(2^{|I|}\) factor from the constructed atlas**, rather than installing it as an assumed formula. Check:

- the actual reflection index cardinality;
- whether `coeff` is per orthant or already symmetric;
- whether any normalization is absorbed in `β`;
- transport of `q'` and `A'` to the named chart data.

The displayed `faceConst` strongly indicates the per-orthant normalization, but the omitted definitions must settle it.

## 3. General tied-piece formula

For \(I\supseteq M_i\), set \(L=I\setminus M_i\). The correct leading-face operation is
\[
n_{M_i}=0,\qquad n_L\text{ retained}.
\]

The residual density has exponents
\[
h_{ij}-\lambda_* e_{ij}>-1
\qquad (j\in L).
\]
That strict inequality is the integrability lemma to expose.

With residual coordinates integrated over a signed box, the schematic chart formula is
\[
\frac{2^{|M_i|}\Gamma(\lambda_*)}{(|M_i|-1)!}
\prod_{j\in M_i}\frac1{e_{ij}}
\int_{\mathrm{base}}\!
 \beta(z)q(z)^{-\lambda_*}
 \int_{[-\varepsilon,\varepsilon]^L}\!
 A(z,(0_{M_i},v))
 \prod_{j\in L}|v_j|^{h_{ij}-\lambda_*e_{ij}}
 \,dv\,dz.
\]

Use the existing general `coeff` definition to prove the precisely normalized version. This formula also explains why there is no universal external \(2^{|I|}\) factor when the residual coordinates are already integrated over a signed box.

A good module boundary is:

1. General scalar-cell residual-face formula.
2. Reflection assembly.
3. Product-piece specialization.
4. Finite sum over tied pieces.

Do not jump directly from the all-minimal theorem to a total formula by discarding \(I\supsetneq M_i\). Those pieces can contribute positively at the same extremal pair.

## 4. Make the assembled coefficient intrinsic

At a fixed pair, `HasLeadingTerm` should imply coefficient uniqueness. Use it to prove independence from:

- the chosen atlas witnesses;
- admissible extension witnesses `q'`, `A'`;
- the cutoff \(\varepsilon\), when comparing valid constructions at the same pair.

Individual piece coefficients need not be cutoff-independent. The **total** coefficient is.

This is an inexpensive but important fidelity result.

---

# Q3. Consistency, possible misstatements, and audit points

## 1. `weight_eq` is restrictive, but not vacuous

Here is a genuinely overlapping two-chart model.

Take \(d=2\), coordinates \((s,t)\), identity chart maps, phase
\[
K(s,t)=s^2,
\]
phase unit \(u=1\), Jacobian exponents \(h=0\), Jacobian unit \(v=1\), and domains
\[
D_1=[-1,1]\times[0,2],\qquad
D_2=[-1,1]\times[1,3].
\]

These are centred product domains with active coordinate \(s\), radius \(b=1\), and inactive bases
\[
T_1=\{0\}\times[0,2],\qquad
T_2=\{0\}\times[1,3].
\]

Write \(B_1=[0,2]\), \(B_2=[1,3]\), and define
\[
r_i(s,t)=
\frac{\mathbf 1_{B_i}(t)}
     {\mathbf 1_{B_1}(t)+\mathbf 1_{B_2}(t)},
\]
using totalized division outside their union.

On each chart domain, the counting weight is exactly \(r_i(0,t)\):

- weight \(1\) on the non-overlap;
- weight \(1/2\) on the overlap;
- including the closed interval endpoints.

These factors are measurable, bounded by \(1\), and independent of \(s\). Subject to the remaining `ResolutionCover` packaging requirements, this realizes precisely the desired two-chart geometry over the union of those rectangles.

So `weight_eq` is consistent even with variable overlap multiplicity. What matters is that the overlap pattern is **saturated in the active fibres**.

## 2. P4 alone does not solve gap (a)

A supplied smooth partition of unity will generally satisfy
\[
w_i(\Phi_i(y))
\]
depending on active coordinates. It will therefore still fail the current `weight_eq`.

The useful extension is:

> Allow sufficiently regular pulled-back weights to enter the continuous amplitude, leaving only suitable measurable inactive factors in `β`.

Consequently, an audit for P4 must track more than “measurability, boundedness, sum-to-one.” It must track **where the weight enters the scalar-cell regularity hypotheses**.

Also, nonnegativity and subordination are real requirements: sum-to-one alone does not give nonnegative cell coefficients or the intended transport identity.

## 3. The dominant-face location is conceptually correct

Your described definition—foot condition, membership in the original domain, and strict positivity/nonvanishing of the surviving density factors—is the right location for the all-minimal positivity theorem.

In particular:

- `footCondition` preserves the piece’s restrictions on active coordinates outside \(I\).
- `dom` keeps the point in the actual chart product domain.
- The Jacobian **unit** and surviving tangential monomial should be nonzero.
- The full Jacobian determinant need not be nonzero there: normal Jacobian powers can vanish on the face.

Do not replace the current base-coordinate measure by ambient \(d\)-dimensional volume. A positive-codimension face has ambient volume zero. A later intrinsic-face statement should use the pushforward of base volume under
\[
z\mapsto\Psi(z,0),
\]
with the appropriate normalization if identifying it with Hausdorff measure.

Audit especially the zero-dimensional base case: its volume convention must give the intended positive mass to the singleton.

## 4. Some positivity assumptions are stronger than necessary

Counting weights are nonnegative, and indeed positive on their own images. From `weight_eq`, together with a foot point in the domain, you can recover the corresponding positivity of `r` on the **relevant inactive base**.

Thus global `∀ x, 0 ≤ r x` is convenient but not mathematically essential. Values of `r` outside the relevant base are unconstrained by `weight_eq`; they can often be repaired by replacing `r` with `max r 0`, preserving the factorization on the domain.

Similarly, global nonnegativity of \(F,p\) could eventually be localized. This is API improvement, not an urgent defect.

## 5. What is not justified merely by the current declarations

- `exists_extremal_stratum` does **not** imply positive dominant-face measure. A compact inactive base may have zero relevant measure.
- `coverLam` and `coverDeg` are geometric candidate exponents; without coefficient positivity, they need not be the actual leading pair of the weighted integral.
- Kernel axiom cleanliness does not establish that the hypotheses are broadly realizable.
- The separate Hironaka-based results do not yet make this product-chart equivalent unconditional. A bridge constructing this stronger package remains absent.

## 6. Regression constants

For unit density on the whole square,
\[
\int_{[-1,1]^2} e^{-N x^2y^2}\,dx\,dy
\sim \sqrt{\pi}\,N^{-1/2}\log N.
\]

So your proposed example should yield
\[
\lambda_*=\tfrac12,\qquad k_*=1,\qquad c=\sqrt{\pi}.
\]

This tests both the factorial/Gamma normalization and the reflection factor. Add \(K=x^2y^4\) if possible: it tests the residual-face formula, which the equal-exponent example cannot.

---

**Bottom line:** deliver P1 now; make P3 explicitly about **minimal-coordinate faces with residual integration**, not only all-minimal pieces; and use P2 as a normalization and non-vacuity test. Keep generic-cover claims qualified until weight regularity—not merely the choice of partition—has been addressed.
