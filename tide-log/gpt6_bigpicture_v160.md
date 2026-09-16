**The landed batch looks sound. The main correction to A3 is that zeroth-order evaluation separates genuine amplitudes, but does not separate elements of the raw `CubeJetSpace`.** You need a holonomic amplitude space—or an equivalent closed-range argument.

My recommended order now is:

1. **B(iii)-(β): probabilistic division and the actual diagonal expansion.**
2. **A(a): coefficient functional infrastructure, then Gaussian averaging.**
3. **B(iii)-(α), only for explicitly identified finite-dimensional outputs.**

The frozen samplewise theorem is a useful cheap wrapper, but must not be mistaken for a diagonal theorem.

## A. Jet-level Gaussian averaging

### A1. Your argument is correct on a genuine amplitude Banach space

Suppose `E` is a real Banach space of amplitudes on the box, with continuous linear evaluations
\[
\operatorname{ev}_x:E\to\mathbb R
\]
that **jointly separate points**. Suppose the coefficient is represented by
\[
\Phi:E\toL[\mathbb R]\mathbb R.
\]

Then, for an integrable random amplitude \(F\),
\[
\mathbb E[\Phi(F)]=\Phi(\mathbb E F).
\]
If \(F_\omega(x)=\eta(x)Y_\omega(x)^{2j}\), pointwise Gaussian moments give
\[
\operatorname{ev}_x(\mathbb EF)
=\eta(x)\frac{(2j)!}{2^j j!}V(x)^j.
\]
Provided the amplitude \(u_j:x\mapsto\eta(x)V(x)^j\) belongs to `E`, separation by evaluations gives
\[
\mathbb EF=\frac{(2j)!}{2^j j!}\,u_j.
\]

Thus **no separate differentiation-under-expectation theorem is needed in the Gaussian averaging theorem**. Its analytic content has been absorbed into the construction of `E` and Bochner integrability in `E`.

Also:

* Pointwise centred Gaussian laws suffice; joint Gaussianity is not needed for this theorem.
* There is no Isserlis theorem to prove here.
* The index shift \(\mu+j\) is generating-series bookkeeping, not part of Gaussian averaging. Prove the averaging theorem at an arbitrary admissible coefficient index \(\nu\), then instantiate \(\nu=\mu+j\).

### A2. The raw jet space is not that space

For
```lean
CubeJetSpace d R b
```
the zeroth component does **not** determine the higher components. Consequently,
```text
zeroth component of ∫ jet(Fω) = κ · η V^j
```
does not, by itself, identify the Bochner integral as
```text
κ • jet(η V^j).
```

Likewise, “globally smooth functions with the sup-jet norm on the box” is not immediately a Banach space:

* before quotienting, this is generally only a seminorm;
* after quotienting, the smooth-amplitude space is generally incomplete.

The clean construction is:

1. Let `S` be the linear range of jets of admissible smooth amplitudes.
2. Let `E` be its closure inside `CubeJetSpace`.
3. Prove that zeroth-order evaluations jointly separate points of `E`.

Step 3 is the **holonomicity lemma**. For a nondegenerate closed box, uniform convergence of functions and their derivatives preserves the derivative relations. One can prove this using the fundamental theorem along coordinate segments and then extend identities to the boundary.

That is a real infrastructure obligation; it should not be hidden inside “evaluation is continuous”.

An equivalent route is to start with a bona fide Banach space of \(C^R\) functions on the box. But unless that API already exists locally, the closed jet range is likely the better fit.

### A3. What the engine must supply

Fix the chart, depth, admissible coefficient index and all structural hypotheses. Write
\[
c(\eta)=\operatorname{empCoeffAtDepthFam}
  (\lambda \tau\,v,\eta(v))\,h\,k\,p\,\nu\,q.
\]

You need the following.

#### 1. A jet-norm-to-`FamJetBound` lemma

Choose \(R\) large enough to control every mixed derivative appearing in `FamJetBound`. If its orders are exactly the componentwise orders \(m\le p\), then
\[
R=\sum_i p_i
\]
is sufficient, subject to the usual identification of mixed partials with iterated Fréchet derivatives.

Prove, with a deterministic constant `Cjet`,
```lean
FamJetBound (fun _ v => η v) p 1
  (Cjet * ‖cubeJet R b η hη‖) 0
```
for admissible smooth `η`.

This is the missing link between the existing coefficient estimate and a normed-space estimate. Keep any basis/operator-norm constants explicit initially.

#### 2. Linearity for constant families

You need
```lean
c (η + ξ) = c η + c ξ
c (a • η) = a * c η
```
under the fixed structural hypotheses.

The existing family additivity is relevant. For scalar multiplication, either prove its family counterpart directly from the finite formula, or transfer the plain-engine result through the compatibility theorem below. Do not assume the plain `const_mul` theorem already applies to this family definition.

#### 3. Boundedness

From `exists_abs_empCoeffAtDepthFam_le`, extract the selected coefficient and obtain
\[
|c(\eta)|\le K\|\operatorname{jet}_R\eta\|.
\]

This extraction needs the specified lattice membership and `q ≤ d - 1`; retain those conditions in the construction.

#### 4. Jet-locality

**Yes:** under those same hypotheses, the zero-bound argument should prove it.

If the order-\(R\) jets of `η` and `ξ` coincide, their relevant mixed derivatives agree. Hence the constant family associated to `η - ξ` satisfies
```lean
FamJetBound ... p 1 0 0
```
and the coefficient estimate gives `c (η - ξ) = 0`. Linearity finishes.

Alternatively, once the norm bound is proved, locality follows immediately from
\[
|c(\eta-\xi)|\le K\|\operatorname{jet}_R(\eta-\xi)\|=0.
\]

This avoids a separate traversal of the Taylor-tree definition.

### A4. Lean-shaped construction

The following is a construction outline, not a claim that these local names already exist:

```lean
-- SmoothAmp is the appropriate vector space of admissible smooth amplitudes.
jetLM : SmoothAmp →ₗ[ℝ] CubeJetSpace d R b
coeffLM : SmoothAmp →ₗ[ℝ] ℝ

hlocal : LinearMap.ker jetLM ≤ LinearMap.ker coeffLM
```

Descend through the range:
```lean
S := LinearMap.range jetLM

coeffOnRange : S →ₗ[ℝ] ℝ

hbound : ∀ z : S, ‖coeffOnRange z‖ ≤ K * ‖z‖

coeffOnRangeCLM : S →L[ℝ] ℝ :=
  coeffOnRange.mkContinuous K hbound
```

Then extend continuously to
```lean
E := S.topologicalClosure
```
using completeness of `ℝ`. No Hahn–Banach extension to arbitrary nonholonomic jets is needed.

The key API should be:

```lean
amplitudeJet : SmoothAmp →ₗ[ℝ] E
evalCLM : Box → E →L[ℝ] ℝ
coefficientCLM : E →L[ℝ] ℝ

eval_amplitudeJet ...
eval_ext ...
coefficientCLM_amplitudeJet ...
```

The exact closure/extension plumbing can use whichever Mathlib completion or dense-extension API is most convenient.

### A5. State the averaging theorem abstractly first

A useful schematic statement is:

```lean
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

variable (ev : Box → E →L[ℝ] ℝ)
variable (hev_ext :
  ∀ u v : E, (∀ x, ev x u = ev x v) → u = v)
variable (Φ : E →L[ℝ] ℝ)

-- F is the random amplitude; u represents η * V^j.
theorem integral_coefficient_even
    (hF : Integrable F P)
    (hFeval : ∀ x, ∀ᵐ ω ∂P, ev x (F ω) = η x * (Y ω x)^(2*j))
    (hu : ∀ x, ev x u = η x * V x^j)
    (hGaussian : ∀ x, HasCenteredGaussianLaw (Y · x) (V x) P) :
    (∫ ω, Φ (F ω) ∂P) =
      ((2*j)! / (2^j * j!) : ℝ) * Φ u
```

Here `HasCenteredGaussianLaw` is schematic; use the repository’s actual law formulation and the parameter type expected by `gaussianReal`.

The proof is:

1. `integral_comp_comm` for `Φ`;
2. `integral_comp_comm` for each `ev x`;
3. DXXXVI and transport of integrals through the marginal law;
4. `hev_ext`.

The odd theorem identifies `∫ F = 0` in exactly the same way. Pointwise a.e. evaluation identities suffice; no uncountable intersection over box points is required.

The engine corollary is therefore exactly the requested identity, **with admissibility of \(\mu+j\), the fixed-depth hypotheses, and membership of the deterministic candidate amplitude in `E` stated explicitly**.

### A6. Plain/family compatibility

I do not recall a verified existing name. Specify and prove something like:

```lean
empCoeff_zero_eq_empCoeffAtDepthFam_const
```

with conclusion
```lean
empCoeff η 0 h k ν q =
  empCoeffAtDepthFam (fun _ v => η v) h k p ν q
```
and all depth, window and regularity hypotheses required by the definitions.

Do not promise definitional equality. Prove it by unfolding if practical; otherwise compare the two zero-field expansions using coefficient uniqueness, with matching cutoffs and normalisations.

This theorem is part of A(a), not an optional final rewrite.

---

## B. Quotient-block transfer

### B1. The frozen samplewise theorem is worth stating

Yes. State it explicitly as a **frozen-parameter** result:
\[
\forall^{\text{a.e.}}\omega,\quad \forall n,\quad \forall J\ge1,
\]
the quotient as a function of the independent asymptotic variable \(N\) has the expansion supplied by `cutoff_div_isBigO'`.

All constants and eventual thresholds may depend on \((\omega,n,J)\). **This says nothing by itself about evaluating at \(N=n\).**

The leading-data obligations are:

1. An exact lattice identity
   \[
   \lambda=m_0/Q,\qquad m_0\in\mathbb N.
   \]
2. Vanishing below \(m_0\) for numerator and denominator.
3. Nonzero leading denominator block.

A positive leading coefficient supplies item 3. For items 1–2, prefer existing structural coefficient theorems if available. Otherwise:

* denominator leading asymptotics plus expansion uniqueness eliminate smaller exponents and excessive logarithmic degrees;
* for bounded observables,
  \[
  |Z_{\mathrm{obs}}|\le \|\mathrm{obs}\|_\infty Z_1
  \]
  supplies the corresponding numerator growth bound, from which its lower-exponent coefficients vanish.

This deduction requires an actual finite-expansion uniqueness argument; `BoxLeading` does not syntactically imply `VanishBelow`.

**Small API issue:** your `VanishBelow` quantifies over *every* `q`. An expansion of log degree `D` only controls `q ≤ D`. Either use the engine’s zero-extension theorem for `q > D`, or introduce a degree-restricted vanishing predicate. This is not a defect in the landed theorem, but it matters at the bridge boundary.

### B2. For the actual posterior, prove a probabilistic division lemma

Yes: use the **proof structure**, not the deterministic `IsBigO` statement.

A clean general theorem is the following. Write \(O_P\) for boundedness in probability of the scaled quantities. Let deterministic sequences satisfy
\[
x_n>0,\qquad g_n\ge1,\qquad x_ng_n\to0,
\]
and let \(J\ge1\). Assume:

* the finite family
  \[
  a_{j,n}/g_n,\quad b_{j,n}/g_n,\qquad j<J
  \]
  is tight;
* \(b_{0,n}\) is bounded away from zero in probability;
* with
  \[
  A_n^*=\sum_{j<J}a_{j,n}x_n^j,\qquad
  B_n^*=\sum_{j<J}b_{j,n}x_n^j,
  \]
  one has
  \[
  A_n-A_n^*=O_P(x_n^Jg_n),\qquad
  B_n-B_n^*=O_P(x_n^Jg_n).
  \]

Then
\[
\boxed{
\frac{A_n}{B_n}
-\sum_{j<J}\operatorname{quotientBlocks}(a_{\bullet,n},b_{\bullet,n})_j x_n^j
=O_P(x_n^Jg_n^{J+1}).
}
\]

Use a genuine lower-tail condition:
\[
\forall\varepsilon>0\ \exists c>0,\quad
\mathbb P(|b_{0,n}|<c)<\varepsilon
\quad\text{eventually}.
\]
Do **not** replace this by tightness of Lean’s total inverse alone: `0⁻¹ = 0`, so that would fail to exclude zero denominators.

#### Proof architecture

Localise to an event on which:

* all finitely many coefficient bounds have a common deterministic constant;
* both scaled remainders are bounded;
* \(|b_{0,n}|\ge c\).

Its complement has arbitrarily small probability. On that event, deterministic smallness of \(x_ng_n\) gives:

* a lower bound for \(|B_n|\);
* bounds for the recursively defined quotient blocks;
* the finite polynomial-product remainder bound.

The best reusable refactor is therefore:

> Extract a **pointwise quantitative division estimate with explicit constants and a smallness threshold**, then derive both the deterministic and probabilistic asymptotic theorems from it.

Do not try to choose samplewise `IsBigO` constants and prove them tight afterward.

### B3. The current bridge inputs should support this—with one cutoff qualification

Take
\[
x_n=n^{-1/Q},\qquad g_n=(1+\log n)^D,
\]
and normalise both integrals by \(n^\lambda\).

Finite coefficient-vector convergence supplies tightness of all block coefficients, hence
\[
a_{j,n},b_{j,n}=O_P(g_n).
\]

For the denominator, set \(s=m-1\). You need the structural zero statements above degree \(s\) at exponent \(\lambda\), together with
\[
b_{\lambda,s}(n)\Rightarrow B,\qquad B>0\ \text{a.s.}
\]
and tight lower logarithmic coefficients. Then
\[
(\log n)^{-s}b_{0,n}-b_{\lambda,s}(n)\to_P0,
\]
which yields the required lower-tail bound for \(b_{0,n}\).

The cutoff qualification is important:

> Since `tendstoInMeasure_chartRemainder` gives little-oh only for exponents strictly below `U`, choose  
> \[
> U>\lambda+J/Q.
> \]

Use that larger expansion and then truncate to `j < J`. The omitted `j = J` block is generally only
\[
O_P(x_n^Jg_n),
\]
not little-oh at that scale. That is sufficient for the probabilistic division theorem.

Thus, assuming the stated joint law includes numerator and denominator coefficients together and the aggregated remainder transfer is available, **(β) is available from the present inputs plus this new algebraic-probabilistic lemma and the leading-data interface**.

The conclusion is exactly your proposed bounded-in-probability remainder, with `1 + log n` initially. Replace it by `log n` in a subsequent asymptotic-equivalence corollary.

Do not claim little-oh at the displayed quotient-error scale merely because the analytic cutoff remainders are little-oh: the omitted algebraic quotient terms can survive at that scale.

### B4. Clarify what the “quotient-block coefficient vector” in (α) means

The blocks \(R_j(L)\) are generally **rational functions**, not polynomials.

There is a useful globally continuous representation avoiding division altogether:
\[
R_j(L)=\frac{P_j(L)}{B_0(L)^{j+1}},
\]
where
\[
P_0=A_0,\qquad
P_j=A_jB_0^j-\sum_{i=1}^j B_iP_{j-i}B_0^{i-1}.
\]

For fixed `J,D`, the finite coefficient vector of
\[
(B_0,P_0,\ldots,P_{J-1})
\]
is a polynomial function of the input coefficient vector. Its convergence in law follows from **globally continuous** mapping, with no exceptional-set theorem.

This is the cheapest meaningful version of (α). It is a nonreduced rational representation, which is perfectly adequate.

If instead you want:

* monic-normalised rational data, or
* finite inverse-log expansion coefficients,

then reciprocal leading coefficients enter. For a positive limiting leading coefficient, use
\[
b\longmapsto\frac1{\max(b,\varepsilon)}
\]
to obtain a globally continuous truncated map. But **one fixed \(\varepsilon\) does not prove the desired theorem**. You still need a localisation/approximation argument letting \(\varepsilon\downarrow0\).

Also, \(B_0\)’s leading coefficient being nonzero does not guarantee \(B_0(L)\ne0\) at an arbitrary fixed finite \(L\). Keep rational representation, fixed-\(L\) evaluation and moving-\(\log n\) evaluation distinct.

---

## C. Review and final priorities

Nothing listed is intrinsically vacuous or obviously misstated.

* **`g^(J+1)`**: valid, deliberately nonsharp worst-case algebraic growth. Keep it.
* **`hint` in the zeta identity**: appropriate for an initial-strip integral identity. Later package strip hypotheses implying `hint`; do not erase a real integrability obligation.
* **`−Y` in D**: correct if the deformation convention contributes the minus sign. Since the limit is centred Gaussian, `−Y` and `Y` have the same law and covariance.
* **`VanishBelow` over all `q`**: stronger than finite-log-degree expansion data alone provide; supply zero-extension or restrict the predicate.
* **A3**: evaluation-based identification is valid only after the holonomic-space issue is resolved.

**Implementation order:**

1. Leading-block bridge facts and the quantitative division estimate.
2. Probabilistic division → actual diagonal all-orders expansion, B(iii)-(β).
3. A(a): constant-family compatibility → bounded coefficient functional → holonomic amplitude space → Gaussian averaging.
4. Optional (α): globally continuous nonreduced rational representation first.

**Skip for now:** a general Isserlis theorem, a broad continuous-a.e. mapping API, reduced rational-function topology, and optimisation of logarithmic remainder powers. State the frozen corollary when convenient, but do not let it substitute for the diagonal result.