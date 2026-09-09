## Verdict

**N3 PASS, within the stated analytic-family scope.** The eight obligations from v37 are present in the four files; consolidating them has not dropped a mathematical step.

| Unit | Verdict | Reason |
|---|---|---|
| 309 | **PASS** | Genuine ℓ¹ continuity from coordinate continuity and a common summable majorant. |
| 310 | **PASS** | Correct parameter continuity of Cauchy coefficients, with inverses taken only on a nonzero-radius torus. |
| 311 | **PASS** | Uses actual `DataSpace` coordinates, proves continuity in its norm, and includes the essential reconstruction. |
| 312 | **PASS** | Transfers both the population integral and its face-functional limit to the supplied analytic family; continuous tangential factors are covered compositionally. |

No blocking N3 fixes. This is a fidelity review of the supplied complete files and frozen interfaces, taking the reported compilation as given.

## 1. Unit 309: the ℓ¹ criterion

The proof is correct.

At a fixed `x₀`:

* The head is a finite sum of continuous functions, tending to zero.
* The coordinate difference satisfies
  \[
  |F(x)_i-F(x_0)_i|\le |F(x)_i|+|F(x_0)_i|\le 2B_i.
  \]
* `Summable.sum_add_tsum_compl` splits the actual norm sum into that head and its complementary tail.
* The complementary tail is bounded by \(2\sum_{i\notin s}B_i<\varepsilon/2\).
* The head is eventually \(<\varepsilon/2\).

The coercion work is honest:

* `hcoe` explicitly identifies subtraction in `lp` with pointwise subtraction.
* The subtype `{i // i ∉ s}` and the subtype of the complement of the set coercion of `s` express the same predicate definitionally. Thus `hs' : … := hs` is not an unproved change of summation domain.

There is no hidden need for a metric or first-countable parameter space. The proof uses neighborhoods and continuity directly.

Nor is a separate assumption `∀ i, 0 ≤ B i` missing: at the chosen `x₀`, it follows from `hbound x₀ i`. If `X` is empty, continuity is vacuous.

## 2. Unit 310: parameter continuity

**The hypothesis is appropriate and sufficient.** Joint continuity on
\[
X\times\overline{\mathbb D}_r^d
\]
restricts to joint continuity on the torus product. Continuity of the inverse monomial then supplies precisely the integrand hypothesis needed by `continuousOn_iterOp_param`.

The invertibility argument is sound: membership in the torus gives \(\|w_i\|=r\), and `hr` excludes \(w_i=0\).

The closed-polydisc hypothesis is stronger than this particular coefficient-continuity theorem needs—joint continuity on the torus product would suffice—but it is a natural common hypothesis for the public analytic-family interface. This is not a defect.

## 3. Unit 311: coordinates, radius gap, and reconstruction

### Actual weighted coordinates

Yes. The decisive coordinate identity is
\[
\operatorname{ofFamilies}(1,0,c)(\mathrm{inr}\,\gamma)
   =c_\gamma\,1^{|\gamma|}=c_\gamma.
\]

The `change` steps expose that encoding rather than treating `ofFamilies` as an unweighted coefficient container by assumption. Consequently:

* `xiCoord_analyticDatum = 0` is correct;
* `etaCoord_analyticDatum = polyRealCoeff …` is correct;
* the continuity proof bounds the **actual coordinates of the actual datum**.

The majorant is therefore correctly
\[
B(\mathrm{inl}\,\gamma)=0,\qquad
B(\mathrm{inr}\,\gamma)=M r^{-|\gamma|}.
\]

This satisfies the v37 weighted-coordinate requirement.

### Strict radius gap

The gap `1 < r` is correctly placed. It does two distinct jobs:

1. \(r^{-1}<1\) makes the geometric majorant summable over multiindices.
2. Every point of the closed unit cube lies strictly inside the radius-\(r\) polydisc, including its boundary points.

It is essential to this general construction and proof, though not a necessary condition for every individual family to be admissible. Some special families would admit weaker assumptions.

The additional `r < R` gap supplies the Cauchy reconstruction machinery from holomorphy on the larger open polydisc. Neither gap has been silently replaced by a non-strict inequality.

### Reconstruction

The reconstruction is faithful. Applying the continuous real-linear map `Complex.reCLM` to the complex `HasSum` gives, at real arguments,
\[
\sum_\gamma \operatorname{Re}(c_\gamma)\,u^\gamma
  =\operatorname{Re}F(u),
\]
because \(u^\gamma\) is real.

This does **not** require the complex coefficients themselves to be real or `F` to take real values on the real slice. The represented amplitude is explicitly `Re F`.

Finally, `dataAmplitude_eq_of_mem` removes clamping only on the closed cube, exactly where reconstruction is needed. There is no unjustified global equality between the clamped represented amplitude and the unrestricted real amplitude.

### Uniform bound

Stating `hM` on the closed polydisc and restricting it to the torus is entirely legitimate. The hypothesis also fits the compactness-based way one ordinarily obtains a common bound.

Notably, datum construction itself uses individual holomorphic summability; the common `hM` is used to establish continuity of the family in ℓ¹. That separation is correct.

## 4. Unit 312: public bridge and tangential factor

The bridge delivers what N3 promised.

There are two distinct substitutions, both present:

1. **Population integral:** reconstruction on the unit box identifies the original amplitude integral with `dataBoxIntegral` for the zero-noise datum.
2. **Limiting face functional:** reconstruction on the closed cube identifies the face functional, including boundary faces reached by `faceProj`.

The second point is important: equality only on the open integration region would not by itself justify replacing the limiting face amplitude. `amplitudeCoeff_congr_closedCube` handles precisely this issue.

The resulting theorem is genuinely stated in terms of the supplied family `realAmp F`, not merely in terms of a newly constructed datum. The equivalence theorem also correctly retains the nonzero **integrated** face-functional hypothesis.

### The `ρ` lemmas

They are adequate for the promised multiplication obligation:

* fixed-parameter holomorphy is preserved;
* joint continuity is preserved;
* compactness bounds the continuous tangential factor by its sup norm;
* `Re(ρ F) = ρ Re F` identifies the intended amplitude.

A theorem instantiating the entire bridge for the scaled family would improve convenience, but it would add no missing mathematical argument. The user can instantiate the existing bridge with
```lean
fun v w => ((ρ v : ℝ) : ℂ) * F v w
```
and the supplied three hypothesis-preservation lemmas.

## 5. Scope and nonblocking improvements

N3 establishes:

> A supplied common holomorphic family, jointly continuous and uniformly bounded on an intermediate closed polydisc with \(1<r<R\), defines continuous zero-noise tangential data representing its real amplitude on the cube; the population tangential asymptotic theorem applies.

It does **not** establish:

* construction of chart maps, Jacobians, or the underlying analytic family;
* construction of a common complex neighborhood from pointwise real analyticity;
* construction, support properties, or partition-of-unity properties of a cutoff;
* preservation of normal analyticity under an arbitrary normal-dependent cutoff;
* nonvanishing or positivity of the integrated leading coefficient;
* the N2 differentiated/quotient asymptotics.

**Nonblocking should-fixes:**

1. Add a compactness corollary obtaining `∃ M, hM` from joint continuity on the compact product.
2. Add a scaled-family public bridge corollary if this is a frequent downstream call.
3. Keep the documentation’s claim of closing analytic admissibility explicitly conditional on the supplied common neighborhood and family hypotheses, as the surrounding text already does.

## 6. N2 gate: approve the coefficient route, with explicit side conditions

**Yes: this is the right Route B gate.** It avoids the invalid general maneuver of differentiating an asymptotic remainder.

### Unit 313: exact derivative identity

For population integrals with amplitude independent of \(N\), the target should explicitly fix the convention:
\[
Z'(N)=-\beta Z_K(N),
\]
where \(Z_K\) inserts \(u^{2k}\), equivalently shifts \(h\) to \(h+2k\).

For tangential integrals, if included, justify the outer differentiation as well; otherwise state clearly that 313 is the chart/population identity. The exact identity must come from the integrals, not from differentiation of the expansion.

### Unit 314: coefficient transport

Your moment recurrence is correct:
\[
M(\mu+1,i)
 =\frac{\mu M(\mu,i)-iM(\mu,i-1)}{\beta}.
\]

**Important qualification:** the integration-by-parts proof needs \(\mu>0\) and \(\beta>0\). At zero and infinity these are what justify the boundary behavior and integrability. Do not state the moment recurrence for arbitrary real \(\mu\) merely because Lean gives an integral a totalized value.

The \(i=0\) case should be treated explicitly, or encoded so the predecessor term is harmlessly multiplied by zero.

With the density-shift theorem and coefficient extraction proved, the binomial identity gives
\[
C_K(\mu+1,j)
 =\frac{\mu C(\mu,j)-(j+1)C(\mu,j+1)}{\beta}.
\]

This is the right general deliverable. If it is stated for **every** real \(\mu\), prove the nonpositive/unsupported cases through coefficient support vanishing; do not obtain them from an unrestricted moment recurrence.

Also ensure that “coefficients unchanged” is a theorem about the actual `coeffAt` representation under shift, not just a pointwise density identity.

At the leading exponent, the required specializations are:
\[
A_K=\frac{\lambda A}{\beta},
\qquad
B_K=\frac{\lambda B-(m-1)A}{\beta}.
\]
They require the established degree bound \(C(\lambda,m)=0\). The second formula is the \(m\ge2\) branch.

### Unit 315: two-term quotient

For \(m\ge2\), the proposed centered limit
\[
\frac{Z(N)}{N^{-\lambda}(\log N)^{m-2}}-A\log N\longrightarrow B
\]
is exactly the useful formulation. Obtain the corresponding limit for \(Z_K\), centered using \(A_K,B_K\).

Then, assuming \(A\ne0\),
\[
\frac{Z_K(N)}{Z(N)}
 =\frac{\lambda}{\beta N}
  -\frac{m-1}{\beta N\log N}
  +o\!\left(\frac1{N\log N}\right).
\]

Equivalently, a convenient Lean target is
\[
N\log N\left(\frac{Z_K(N)}{Z(N)}
                -\frac{\lambda}{\beta N}\right)
 \longrightarrow-\frac{m-1}{\beta}.
\]

The remaining expansion obligations are:

* isolate the leading exponent at the chosen cutoff;
* establish the log-degree bound at that exponent;
* show the cutoff remainder vanishes after the relevant normalization;
* obtain the shifted expansion as well;
* derive eventual denominator nonvanishing from \(A\ne0\).

A positive cutoff gap suffices: even a remainder carrying a fixed power of `log N` is negligible after these normalizations. Use the actual `CutoffExpansion` remainder statement rather than strengthening it unnecessarily to a pure \(O(N^{-L})\) bound.

### The \(m=1\) branch

Your conclusion is correct, but **split this branch explicitly**. Natural-number subtraction makes a uniform `m - 2` formulation misleading here.

There is no \(B\) term. The isolated expansion gives
\[
Z=N^{-\lambda}(A+\varepsilon),\qquad
Z_K=N^{-(\lambda+1)}
       \left(\frac{\lambda A}{\beta}+\varepsilon_K\right),
\]
with
\[
(\log N)\varepsilon\to0,\qquad
(\log N)\varepsilon_K\to0.
\]
The positive cutoff gap supplies these stronger errors. With \(A\ne0\), this yields
\[
\frac{Z_K}{Z}
 =\frac{\lambda}{\beta N}
   +o\!\left(\frac1{N\log N}\right).
\]

**Gate decision:** GO for 313–315 on this route. The genuine blocking requirements for that next gate are moment-domain conditions, actual coefficient-shift transport, the log-degree/isolated-spectrum facts, and the separate \(m=1\) error estimate—not any missing N3 construction.
