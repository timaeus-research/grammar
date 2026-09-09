**I recommend (A) + (B), with two important corrections:** use a **measure-transport certificate**, not merely measurable chart bijections, and formulate item (3) as invariance relative to a **chosen fibre-linear tubular structure**. Do not claim intrinsic higher normal derivatives under arbitrary changes of tubular neighbourhood.

There are also two issues in the paper’s displayed coordinate-free formula that should be settled before formalising it:

1. **Fibre integration versus pushforward measure:** unnormalised fibre moments must be integrated against the reference base measure, not against the pushforward of that same density without a normalisation factor.
2. **Taylor degree versus asymptotic order:** the sum over normal Taylor degrees is generally not an asymptotic scale for a monomial phase. Relating it to `familyCoeffSeries_population` requires convergent summation/regrouping, not merely a finite Taylor formula.

Below is a six-unit plan. Lean snippets are **target signatures**, not claimed drop-in code against your pin; existing arguments of `tanIntegral`, coefficient series, and Taylor-tree conclusions are suppressed where their exact signatures were not supplied.

## 1. Measured pullback, localisation, and finite partition

**Priority: first.** This is inexpensive and discharges the exponential-tail part cleanly.

### Separate the measure-theoretic statement from resolution geometry

Absorb the nonnegative prior and absolute Jacobian into a positive resolved measure `μ`. Write
\[
Z(N)=\int F(z)e^{-NK(z)}\,d\mu(z).
\]
Here `F = φ ∘ π`; this avoids repeatedly proving measurability and integrability of three factors.

A useful minimal structure is:

```lean
structure LocalisationData (U : Type*) [MeasurableSpace U] where
  μ       : Measure U
  phase   : U → ℝ
  obs     : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg    : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable  : Integrable obs μ
  δ       : ℝ
  δ_pos   : 0 < δ
```

For the finite partition, use a separate certificate:

```lean
structure FiniteSublevelPartition
    (D : LocalisationData U) (ι : Type*) [Fintype ι] where
  ρ            : ι → U → ℝ
  measurable_ρ : ∀ i, Measurable (ρ i)
  nonneg_ρ     : ∀ i, ∀ᵐ z ∂D.μ, 0 ≤ ρ i z
  sum_eq_one   :
    ∀ᵐ z ∂D.μ.restrict {z | D.phase z < D.δ},
      ∑ i, ρ i z = 1
```

No global support condition is needed for the analytic decomposition: work throughout with `μ.restrict Uδ`.

### Target theorems

For `0 ≤ N`:

```lean
theorem localisation_bound :
  |Z D N - Zsublevel D N| ≤
    (∫ z, |D.obs z| ∂D.μ) * Real.exp (-D.δ * N)
```

And:

```lean
theorem sublevel_eq_sum :
  Zsublevel D N =
    ∑ i, ∫ z in {z | D.phase z < D.δ},
      P.ρ i z * D.obs z * Real.exp (-N * D.phase z) ∂D.μ
```

Nonnegativity and the sum-one condition imply `ρ i ≤ 1` almost everywhere on the sublevel, giving the required integrability.

### Pullback target

For an original measured space `X`, the clean input is:

```lean
hπ : Measurable π
htransport : Measure.map π μResolved = μOriginal
```

Then prove the original integral equals the resolved integral for pulled-back phase and observable.

This certificate can subsequently be obtained from the supplied change-of-variables theorem on the regular locus, together with exceptional-set/null-set arguments. **Do not represent resolution merely by a globally injective map:** it generally is not one.

### Critical rate correction

Your existing assembly hypothesis is **little-o**, not big-O:
```lean
Tendsto (fun N => E N * exp (ε * N)) atTop (𝓝 0)
```

A bound `|E N| ≤ C * exp (-δ * N)` proves this for **every `0 < ε < δ`**, not generally for `ε = δ`. Export a corollary with `ε = δ / 2`.

**Inputs:** measurable restriction, Bochner integral estimates, finite-sum integration, exponential limits.  
**Non-claim:** no resolution existence, and no derivation of the resolution’s transport certificate yet.

---

## 2. Weighted chart presentation and analytic realisation as `tanIntegral`

**Priority: second.** This is the main bridge into the repository’s existing theorem.

### Use finite charts, not necessarily one chart per stratum

Use an index `a : Fin M`, with a label `stratum a`. Multiple charts and orthants may belong to the same stratum. Grouping by strata is a later finite-sum identity.

For each chart, supply:

- a compact base `B a`, finite measure `ν a`;
- normal dimension and the existing box parameters;
- a measurable map `Φ a : B a × E a → U`;
- nonnegative chart density;
- phase normal form;
- a **measure-transport identity**.

Let
\[
\lambda_a=\nu_a\otimes(\mathrm{vol}|_{\mathrm{box}_a}),\qquad
q_a(v,u)=|u|^{h_a}c_a(v,u).
\]
The decisive field is schematically:

```lean
chart_transport :
  Measure.map Φ
    (λ.withDensity (fun p => ENNReal.ofReal (q p))) =
  (μ.restrict Uδ).withDensity
    (fun z => ENNReal.ofReal (ρ a z))
```

Also require, at least almost everywhere on `λ`:

```lean
phase_normal :
  phase (Φ (v, u)) = monomialPhase k u
```

A measurable bijection alone gives neither of these facts.

For genuine geometric charts, keep a stronger wrapper containing differentiability, injectivity, determinant identities, and measurable domains. A helper theorem then produces `chart_transport` using `integral_image_eq_integral_abs_det_fderiv_smul`. The downstream assembly should depend only on the transport certificate.

### Analytic input: an equality of amplitudes, not an equality of integrals

Supply
```lean
x : TangentialData B d
```
and an amplitude-realisation certificate of the form
```lean
amplitude_eq :
  ∀ᵐ (v, u) ∂λ,
    evalChartDatum (x v) u = obs (Φ (v, u)) * c (v, u)
```
with the exact evaluation convention used by `familyPhaseIntegralBox`.

Then prove:

```lean
theorem stratumChartIntegral_eq_tanIntegral :
  ∫ z in Uδ, ρ a z * obs z * exp (-N * phase z) ∂μ =
    tanIntegral ν ... x N
```

This is not circular: the input identifies a pointwise analytic amplitude and transports a measure; the theorem establishes the integral identity.

### Package the result

`AdaptedStrataData` should consist of:

1. localisation and finite-partition data;
2. weighted chart presentations;
3. analytic datum realisations;
4. optionally, geometric labels and adaptation properties.

Export:

```lean
theorem resolved_decomposition :
  Z D N = gInt ... D.x N + D.tail N

theorem resolved_tail_bound :
  0 ≤ N →
  |D.tail N| ≤ D.tailConstant * exp (-D.δ * N)

theorem resolved_tail_small :
  0 < ε → ε < D.δ →
  Tendsto (fun N => D.tail N * exp (ε * N)) atTop (𝓝 0)
```

If the existing parameter ranges over all reals, define `tail := Z - gInt` globally and prove its integral interpretation and bound for `N ≥ 0`. Do not accidentally demand integrability for negative `N`.

### Scope choices and traps

- **Assume exact phase normal form in this release.** A positive unit
  \[
  a(v,u)u^{2k}
  \]
  is not removed for free. Locally, for `k j > 0`, one can try
  \[
  u'_j=u_j\,a(v,u)^{1/(2k_j)}.
  \]
  Proving analyticity, local invertibility, transformed density, and the resulting domain description is another theorem. The new domain need not be a product box.
- **Analyticity must cover the actual amplitude.** Include the prior, Jacobian unit, and every normal-variable-dependent cutoff. Smoothness is insufficient for the existing convergent coefficient-family machinery.
- **Normal-constant partition functions** can be placed in `ν`; alternatively retain them in the amplitude. An arbitrary smooth partition of unity does not establish their existence.
- **A sublevel of a monomial phase is not generally a product box.** Supply an actual product-domain presentation, or prove a separate domain-replacement statement. Do not hide a nonanalytic indicator inside an “analytic amplitude.”
- **Finite charts need justification.** Noncompact strata need not admit the required finite presentation. Compactly supported data may help, but do not automatically produce compact product bases.
- **Signed normal coordinates:** split into orthants and include all multiplicities. Discarding coordinate hyperplanes requires absolute continuity of the chart measure. A factor `2^d` is valid only with the appropriate reflection symmetry.
- For the current positive-dimensional chart engine, either assume all contributing charts have positive normal dimension or handle rank-zero pieces separately.

**Inputs:** Unit 1, change of variables or measure transport, Fubini, existing chart amplitude evaluation.  
**Non-claim:** existence of a fibre-saturated, normal-constant adapted partition from a normal-crossing resolution.

---

## 3. Normal Taylor tensors and fibre-linear covariance

**Priority: third; independent of Unit 2.**

Fix a finite-dimensional real normed space `E`. There is no need to implement `Sym^r` as a bundle.

```lean
abbrev JetForm (E : Type*) ... (r : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ

def normalJet (F : E → ℝ) (r : ℕ) : JetForm E r :=
  iteratedFDeriv ℝ r F 0

def homogeneousTaylor (F : E → ℝ) (r : ℕ) (u : E) : ℝ :=
  (r.factorial : ℝ)⁻¹ * normalJet F r (fun _ => u)
```

Prove, for a continuous linear equivalence `L : E ≃L[ℝ] E` and sufficient differentiability:

```lean
theorem normalJet_comp_linear :
  normalJet (F ∘ L) r =
    (normalJet F r).compContinuousLinearMap (fun _ => L.toContinuousLinearMap)

theorem homogeneousTaylor_comp_linear :
  homogeneousTaylor (F ∘ L) r u =
    homogeneousTaylor F r (L u)
```

Use `ContinuousLinearMap.iteratedFDeriv_comp_right`.

For a base parameter, apply this pointwise to `F v` and `L v`. No derivatives of `L` in the base appear because these are **fibre derivatives**.

### Coordinate convention

If `u' = L u`, the new coordinate expression is
\[
F'(u')=F(L^{-1}u').
\]
Thus the new jet is pulled back by `L⁻¹`. For diagonal `L = diag(g_i)`, multiindex derivative components transform by
\[
\partial^\gamma F' = \Bigl(\prod_i g_i^{-\gamma_i}\Bigr)\partial^\gamma F.
\]

Be explicit about whether `D_γ` means derivatives or Taylor coefficients: the factorial conventions differ.

### Essential non-claim

These are normal jets **relative to a chosen tubular identification** and invariant under its fibre-linear changes of frame.

They are not canonical under arbitrary tubular changes. Even on a line, a nonlinear change `u' = u + a u²` changes the second Taylor coefficient when the first derivative is nonzero. More generally, restricting an ambient differential to a “normal direction” requires an appropriate choice of normal splitting or tubular map.

Porting the sister repo’s tubular-chart results does not by itself remove this issue.

---

## 4. Moment functionals, Fubini, and invariant pairing

**Priority: fourth.**

### Avoid tensor infrastructure by using the dual of multilinear forms

For a finite positive measure `η` on `E` with finite `r`-th moment, define:

\[
\operatorname{Moment}_{\eta,r}(A)
   =\int A(u,\ldots,u)\,d\eta(u).
\]

A useful target is:

```lean
def momentFunctional
    (η : Measure E)
    (hη : IsFiniteMeasure η)
    (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    JetForm E r →L[ℝ] ℝ
```

Its norm is bounded by `∫ ‖u‖^r dη`. Restricting to symmetric forms is optional: the diagonal evaluation already ignores the irrelevant nonsymmetric part.

For each fibre and `N`, use
\[
d\eta_{v,N}(u)
 =1_{D_v}(u)|u|^h e^{-NK(v,u)}c(v,u)\,du.
\]

### Transport target

With `η' = Measure.map L η`:

```lean
theorem moment_pairing_invariant :
  momentFunctional η' ... (normalJet (F ∘ L.symm) r) =
    momentFunctional η  ... (normalJet F r)
```

This is the robust coordinate-free statement. It works for arbitrary invertible linear changes provided the **domain and measure are transported**.

No condition such as `∏ g_i^(2*k_i) = 1` is needed for this theorem. Such a condition is relevant only if you insist that the transported phase retain the identical monomial expression. Likewise, a diagonal scaling does not usually preserve the same box.

### Fubini target

First prove the direct chart formula, under joint measurability and absolute integrability:

\[
\int_{B\times D}H(v,u)c(v,u)\,d(\nu\otimes du)
=
\int_B\left(\int_D H(v,u)c(v,u)\,du\right)d\nu(v).
\]

This is the useful formal content of `eq:pushforward_local`. Fibrewise compact support alone does not establish global integrability over a noncompact base.

### Correct the pushforward normalisation

Let
\[
d\Omega=c(v,u)\,du\,d\nu(v),\qquad
C(v)=\int c(v,u)\,du.
\]
Then
\[
\tau_*\Omega=C(v)\,d\nu(v).
\]

Consequently, either use:

- **unnormalised moments** with outer measure `ν`; or
- **normalised conditional fibre measures**
  \[
  d\kappa_v=C(v)^{-1}c(v,u)\,du
  \]
  with outer measure `τ_*Ω`.

Using raw moments containing `c` and then integrating them against `τ_*Ω` counts `C(v)` twice.

Implement the product-chart normalisation directly, treating `C(v)=0` separately. No general disintegration theorem is necessary. To use the paper’s exact notation, explicitly declare that `|μ_I|_v` denotes the normalised conditional fibre measure.

---

## 5. Taylor–moment identity and compatibility with canonical chart coefficients

**Priority: fifth, and the substantive item-(3) connection to existing code.**

### First: finite-degree contraction

For `E = Fin d → ℝ`, prove:
\[
\frac1{r!}\operatorname{Moment}_{v,N,r}(D^rF_v)
=
\sum_{|\gamma|=r}
 \frac{\partial^\gamma F_v(0)}{\gamma!}\,
 \widetilde M_\gamma(v,N).
\]

This needs:

- the diagonal expansion of a symmetric multilinear form;
- counting words with a prescribed multiindex;
- finite-sum integration;
- the moment integrability established in Unit 4.

If the repository already represents Taylor coefficients directly, prove an intermediate polynomial-coefficient statement first. Relate those coefficients to `iteratedFDeriv` in a separate lemma.

### Second: genuinely connect the analytic family

For the coordinate-free formula in the question, `F` is the observable and `c` belongs to the moment measure. Therefore it is not enough merely to know that the product `F*c` has an analytic datum.

Supply analytic realisations of:

- `F(v, ·)`;
- `c(v, ·)`;
- their product as the datum used by `familyCoeffSeries_population`.

Then prove that the product datum agrees with the canonical Cauchy product.

The target is an **absolutely convergent identity**:
\[
Z_a(N)=
\sum_{r=0}^{\infty}\frac1{r!}
 \int_{B_a}
 \left\langle D^rF_{a,v},M^{\rm raw}_{a,r}(v,N)\right\rangle d\nu_a(v),
\]
or its normalised-pushforward equivalent.

Uniform analytic control on the integration box, with a suitable radius margin, is a convenient sufficient hypothesis. Mere analyticity near the zero section does not ensure convergence over the entire box.

### Third: canonical-series compatibility

Prove that substituting the dressed-moment expansions and performing the justified sums gives precisely `familyCoeffSeries_population`, and after base integration and finite assembly, `gCoeff`.

This is where existing absolute-convergence/Cauchy-product results should do most of the work.

**Do not define a coefficient by a formal, unjustified**
\[
\sum_r [N^{-p}\log^jN](\text{degree-}r\text{ moment term}).
\]
Establish the summation interchange with the bounds used by the existing chart theorem.

### Important mathematical trap

For a phase such as `x²*y²`, higher powers of `x` can still contribute at the same power of `N`. Thus normal Taylor degree is not generally ordered by asymptotic decay.

The honest theorem has:

1. a convergent Taylor–moment representation; and
2. the existing power–log asymptotic expansion obtained from that representation.

It should not assert that truncating at degree `r` automatically gives the paper’s arbitrary-order asymptotic remainder.

---

## 6. Conditional geometric main theorem

**Priority: last; mostly assembly once Units 1–5 exist.**

I would use two structures:

```lean
AdaptedStrataData
```

for the measured decomposition and chart analytic amplitudes, and

```lean
NormalMomentPresentation D
```

for the observable/density analytic factorisation, fixed fibre-linear tubular presentation, moment integrability, and compatibility of normal Taylor coefficients with the existing analytic datum.

This keeps item (2) useful even if the more delicate moment compatibility takes longer.

### Main expansion theorem: target shape

```lean
theorem expectation_expansion_of_adaptedStrataData
    (D : AdaptedStrataData ...)
    (T : NormalMomentPresentation D) :
    AssembledExpansionConclusion
      (Z := D.populationIntegral)
      (coeff := D.gCoeff)
    ∧
    (∀ N, 0 ≤ N →
      D.populationIntegral N =
        D.tail N +
          ∑ a, ∑' r,
            (r.factorial : ℝ)⁻¹ *
              ∫ v,
                T.moment a v r N
                  (T.normalJet a v r)
                ∂T.baseMeasure a)
    ∧
    CanonicalMomentSeriesCompatibility T D.gCoeff
    ∧
    FibreLinearPresentationInvariant T
```

Here:

- `AssembledExpansionConclusion` should reuse the repository’s actual assembled Taylor-tree conclusion, or be a thin wrapper around it.
- `baseMeasure` is either the reference base measure with raw moments, or the pushforward measure with normalised moments—**one convention only**.
- `CanonicalMomentSeriesCompatibility` is the theorem from Unit 5, not an assumed field that simply restates the desired conclusion.
- `FibreLinearPresentationInvariant` means compatibility under certified measurable fibre-linear frame changes, including transport of domains and densities. It does not claim a constructed global symmetric-tensor bundle.

Export the quantitative tail separately:
```lean
|D.tail N| ≤ D.tailConstant * exp (-D.δ * N)
```
and the normalised leading-term corollary:

```lean
theorem population_first_nonzero_of_adaptedStrataData
    (D : AdaptedStrataData ...)
    (hne : ∃ p, D.gCoeff p ≠ 0) :
    -- exactly the conclusion of
    -- population_first_nonzero_assembled_exp
```

The proof supplies `resolved_decomposition` and `resolved_tail_small` with `ε = δ/2`. The nonvanishing hypothesis remains necessary for a first-nonzero conclusion; it is not needed for the expansion itself.

If starting from an original population integral on `X`, add the measured resolution map and its transport certificate, then rewrite using Unit 1.

## What this release would—and would not—establish

**It would establish:**

> A resolution presented by certified weighted adapted charts and analytic amplitudes yields the existing quantitative power–log expansion. Its local integrals admit a Taylor–moment representation whose contractions are invariant under fibre-linear changes of normal frame, and that representation produces the existing canonical coefficients.

**It would not establish:**

- Hironaka or existence of the required resolution presentation;
- existence of the paper’s specially adapted partition of unity from Mathlib’s ordinary partition theorem;
- global tubular neighbourhoods or a normal-bundle/symmetric-tensor-bundle API;
- canonical higher normal derivatives independent of the chosen tubular structure;
- automatic removal of phase units while preserving product boxes;
- an asymptotic ordering by normal Taylor degree;
- the literal pushforward-measure formula without resolving fibre normalisation.

This is a substantial, defensible narrowing of the geometric gap. I would defer (C): it adds considerable infrastructure without solving the domain, normalisation, and summation issues that actually control the correctness of the bridge.
