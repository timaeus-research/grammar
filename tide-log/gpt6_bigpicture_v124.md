## Executive verdict

**On the statements supplied, the first release boundary is reached:** you have an intrinsic coefficient distribution on the original space, a concrete finite-order estimate, compact support, the wall-image support theorem, and the testwise expansion. Theorem B remains its chart-face presentation.

The main qualifications are:

- `{K = 0}` is a valid support-containment target, but need not be closed when `K` is only measurable.
- `engineOrder` is a presentation-dependent **upper bound**, not an intrinsic or optimal order.
- The distribution is presently on all of `E`, not on an arbitrary open domain.
- Intrinsicness concerns the coefficients; the chosen lattice parameters and estimates remain presentation data.
- C5 should use a compactly controlled functional on smooth face functions, then restrict it to test functions. This also exposes a separate issue: a chart pullback need only be smooth near the relevant compact set.

This is a statement-level audit, not an independent verification of the Lean implementation.

# 1. Audit of CDXV–CDXVII

### 1.1 What is established

For every `μ q`, your results give
\[
T^X_{\mu,q}\in\mathcal D'(E),
\qquad
T^X_{\mu,q}(f)=\operatorname{observableCoeff}_X(\mu,q,f),
\]
with
\[
|T^X_{\mu,q}(f)|
 \le C^X_{\mu,q}M
\]
whenever the derivatives through order `engineOrder X μ` are bounded by `M` on `coreImage X`.

Because `coreImage X` is compact, this is a global finite-order, compact-set estimate. Together with
\[
\operatorname{supp}T^X_{\mu,q}
 \subseteq \operatorname{wallImage}X\cap\operatorname{tsupport}(\operatorname{prior}),
\]
it supports precisely the phrase **“compactly supported finite-order distribution.”**

The equality theorem makes the distribution intrinsic under the comparisons covered by its type. One implementation audit point is worth checking: **do its implicit parameters allow genuinely different chart counts, chart indexing types, and auxiliary presentations?** If `X` and `Y` must share some presentation parameters, state the intrinsicness theorem at exactly that scope, or add a repackaging/comparison corollary.

### 1.2 The zero set

The statement
```lean
dsupport (coeffDistribution X μ q) ⊆
  {x | X.K x = 0} ∩ tsupport X.prior
```
is mathematically meaningful with only measurable `K`. A closed support can be contained in a nonclosed set.

What you should **not** infer is that `{K ≠ 0}` is open. Thus:

- “supported in the zero set of `K`” is correct;
- “vanishes on the open complement of the zero set” requires additional hypotheses;
- without those hypotheses, use the interior of `{K ≠ 0}`, or quantify over open subsets of `{K ≠ 0}`.

The stronger geometric support information remains the compact wall-image theorem.

### 1.3 Order and ambient domain

`engineOrder` is a satisfactory replacement for the proposed `R_eng`, and apparently a sharper one than `chartJetTotal`. Record:

> The coefficient distribution has order at most `engineOrder X μ`.

Do not call that number *the* order or an intrinsic order. The theorem also usefully gives an order bound independent of `q`.

Using `Ω = ⊤` correctly realizes “on the original space.” It does not prove a general-open-domain theorem, but no such generalization is needed for this release.

### 1.4 Expansion parameters

The expansion with `X.decomp.commonQ/commonD` is correct. Its meaning is:

> This presentation supplies an admissible discrete indexing lattice for the intrinsic coefficients.

It does not assert that these parameters are intrinsic or minimal. There is no need to canonicalize them now. Comparisons between presentations can regard both coefficient families as indexed by all `μ,q`, with zeros away from their respective admissible supports.

# 2. Cheap boundary additions

I would add the following.

### A. Distribution-level coefficient support

By extensionality and `coeff_support`:

```lean
theorem coeffDistribution_eq_zero_of_not_mem_spectrum ...
theorem coeffDistribution_eq_zero_of_logDegree_gt ...
```

State these using the actual predicates from `coeff_support`; derive the readable `q > d - 1` version only with its existing dimension assumptions. In particular, avoid silently losing the `d = 0` case through truncated natural subtraction.

### B. A linear-map alias

If useful for downstream algebra:

```lean
def coeffLinearMap X μ q : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ :=
  (coeffDistribution X μ q).toLinearMap
```

This should be an alias/coercion lemma, not another construction.

### C. Open-set vanishing away from the zero set

A useful hypothesis-free formulation is:

```lean
theorem isVanishingOn_of_subset_nonzero
    (U : Opens E)
    (hU : (U : Set E) ⊆ {x | X.K x ≠ 0}) :
    (coeffDistribution X μ q).IsVanishingOn U
```

Adapt argument order to the actual API. The interior version is an immediate corollary. If an openness assumption on `{K ≠ 0}` is available, specialize to that set.

### D. Positivity of bound constants

If not already public, expose:
```lean
engineOrder_nonneg -- unnecessary if Nat
jetConst_nonneg
```
Only the second is substantive. Public nonnegativity lemmas make subsequent estimates easier.

### Not cheap: the top logarithmic coefficient

Do **not** derive an order-zero theorem for the leading logarithmic coefficient merely from `coeff_support` or the existing jet bound.

The paper’s deepest-stratum formula needs identification of the relevant leading exponent and log multiplicity, followed by elimination or cancellation of all derivative-bearing terms. That deserves a separate theorem with explicit hypotheses. It may yield a measure, but the present finite-order bound alone does not.

### Trivial phase

A direct regression is useful if `K = 0` is admitted by the engine:

\[
T_{0,0}(f)=\int \mathrm{prior}\,f,\qquad
T_{\mu,q}=0\quad\text{for }(\mu,q)\ne(0,0),
\]
with the precise indexing convention of the expansion.

If the engine excludes the identically zero phase, do not manufacture an engine instance just for this. State the elementary `partitionObs` identity separately.

# 3. Land `Zdist` now

**Yes: S-sized, and logically independent of C4s.**

The clean constructor is intrinsic in `K, prior`; `X` should only supply the hypotheses.

For nonnegative prior and nonnegative phase on its relevant support,
\[
|Z_N(f)|
 \le \left(\int \mathrm{prior}\right)M
\]
when `N ≥ 0` and `|f| ≤ M` on `tsupport prior`.

For a signed prior, replace the constant by `∫ |prior|`. If `K` is merely measurable and no nonnegativity or suitable exponential-integrability assumption is available, the proposed estimate does **not** follow.

Suggested interface:

```lean
def Zdist X (N : ℝ) (hN : 0 ≤ N) : 𝓓'(Ω, ℝ)

theorem Zdist_apply ...
theorem Zdist_bound ...
theorem dsupport_Zdist_subset :
  dsupport (Zdist X N hN) ⊆ tsupport X.prior

theorem Zdist_eq_of_eq ...
```

Then restate C4w using `Zdist_apply`. Call it a **testwise/weak expansion**; do not imply a uniform remainder over a class of test functions.

# 4. C5: the recommended object

## 4.1 The geometry

For a piece `P` and face `J`, put
```lean
Active P := Fin (da P)
Tangential P J := {i : Active P // i ∉ J}
Normal P J := {i : Active P // i ∈ J}
```

Use the existing face-coordinate types if they already encode these.

Distinguish the base’s ambient Euclidean space from its compact integration set:

```lean
BaseSpace P
baseBox P : Set (BaseSpace P)
νbase P : Measure (BaseSpace P)

TangSpace P J := Tangential P J → ℝ
FaceSpace P J := BaseSpace P × TangSpace P J

faceBox P J :=
  baseBox P ×ˢ Set.pi Set.univ (fun k => Set.Icc 0 (b k))
```

The distribution lives on the **ambient** `FaceSpace`, not on the compact base subtype. The finite base measure must be carried by `baseBox`.

Its dimension is `d - |J|` if the piece splitting indeed has
`dim BaseSpace + da P = d`.

## 4.2 Face factorization: yes, with a precise distinction

For smooth `U`, the renormalized functional depends only on
\[
w\longmapsto U(\operatorname{glue}_J(0,w)).
\]

Tangential jets on the face are determined by this restricted smooth function. They are not additional ambient normal data.

The key statement should be an **operator identity**, not initially an existential factorization:

\[
\left[\operatorname{remList}_{p,l_K}F\right]
       (\operatorname{glue}_J(0,w))
=
\operatorname{remList}_{p_K,\mathrm{finRange}}
       \bigl(F\circ\operatorname{glue}_J(0,\cdot)\bigr)(w).
\]

The actual coordinate ordering may require a transported list instead of `finRange`. Preserve the existing ordering first; simplify later.

This is the first C5 unit.

## 4.3 Define the tangential density

For each eligible `m`, define
\[
H_{s,m,a}(w)
 =
 \bigl(\partial_J^{m-a}\rho_{P,s}\bigr)
       (\operatorname{glue}_J(0,w)).
\]

For a smooth function `u` on `FaceSpace`, write `u_s(w) := u(s,w)`. Define
\[
\begin{aligned}
B_{P,J,a,\mu,q}(u)
={}&\int_s
\sum_{\substack{m\in\mathrm{idxL}\\a\le m}}
 \mathrm{faceW}(J,m-a)
\sum_{j=q}^{D_J}
 c_{m,j,\mu,q}\\
&\qquad\qquad\cdot
 \mathrm{faceCoeffInt}
 \left(
 \operatorname{remList}_{p_K}
        (H_{s,m,a}\,u_s)
 \right)
 \,d\nu_{\rm base}(s),
\end{aligned}
\]
where `c` is exactly `faceCoef * C(j,q)` from Theorem B.

**Do not include the outer `faceW J a` in this definition.** Keeping it outside makes reconstruction literally match Theorem B.

The density-splitting theorem is then
```lean
B ... u =
  ∫ s, renormFunctional (ρfam P s) ...
    (fun v => u (s, projectK J v)) ∂νbase P
```
for smooth `u`, followed by its specialization to a general ambient `U` using face restriction.

## 4.4 Smooth functional first: recommended

Yes, your alternative is the right formal architecture.

One correction of terminology: **Mathlib distributions do not need compact support; their test functions do.** Here `B` will additionally have compact support.

Use the project’s existing bundled smooth-function type if available. Otherwise a small wrapper is enough:

```lean
abbrev SmoothFace :=
  {u : FaceSpace P J → ℝ // ContDiff ℝ ∞ u}
```

Equip it with the inherited real module structure, then define

```lean
def faceFunctional : SmoothFace P J →ₗ[ℝ] ℝ
```

No topology on `SmoothFace` is needed for C5.

Prove the compact-set jet bound, and restrict to test functions:

```lean
def faceDistribution :
    𝓓'((⊤ : Opens (FaceSpace P J)), ℝ)
```

with
```lean
faceDistribution_apply
```
identifying its action with `faceFunctional`.

### Important extra issue: chart-local smoothness

The expression
\[
(s,w)\mapsto
\partial_J^a(\mathrm{obs}\circ\psi_i\circ T_P)
                 (\operatorname{glue}_J(0,w))
\]
may only be smooth near `faceBox`, because `ψ_i` may only be smooth on its chart domain.

Defining `B` on globally smooth functions fixes the noncompact-support issue, but **does not itself fix this local-smoothness issue**.

There are two clean solutions:

1. If `obsfam` is already globally smooth by construction, use it directly.
2. Otherwise choose once per piece/face a cutoff supported inside the chart-valid region and equal to one near `faceBox`; use the resulting global smooth representative.

Define `faceJet` as that representative and prove independence from the representative. Do not silently claim the raw chart expression is globally smooth.

# 5. C5 estimates and support

## 5.1 Tangential order

I agree with
\[
R_{P,J}=\sum_{k\in K}p_k.
\]

Only tangential derivatives of `u` are used. No base derivative is required. The normal derivatives `m-a` fall entirely on the fixed density.

The useful primary estimate is an anisotropic one:

```lean
TangentialJetBound R faceBox u M :=
  ∀ s ∈ baseBox, ∀ r ≤ R, ∀ w ∈ closedKBox,
    ‖iteratedFDeriv ℝ r (fun w => u (s, w)) w‖ ≤ M
```

Then prove
```lean
theorem abs_faceFunctional_le_tangential
    (hM : 0 ≤ M)
    (hu : TangentialJetBound R faceBox u M) :
    |faceFunctional ... u| ≤ faceConst ... * M
```

A joint `JetBound R faceBox u M` implies this through the linear isometric inclusion of tangential directions. That supplies the ordinary finite-order distribution theorem.

A safe constant has the schematic form
\[
\sum_m |\mathrm{faceW}_{m-a}|
 \sum_j |\mathrm{faceCoef}_{m,j}|\,C(j,q)\,
 2^{R_{P,J}}D_{m,a}\,
 \left(\prod_{k\in K}\frac1{(p_k-1)!}\right)
 \mathrm{faceMajorant}_{j-q}\,
 \nu_{\rm base}(\mathrm{univ}),
\]
where `D_{m,a}` bounds the required tangential derivatives of `H`.

Use the existing bound machinery rather than aiming to optimize this constant.

**Integrability is part of this unit.** `integral_add` and scalar linearity require the relevant integrability facts; finite measure alone does not make arbitrary parameter-dependent integrands integrable. Reuse the family measurability and uniform bounds already available for `ρfam`.

## 5.2 Support

The safest first locality theorem is:

```lean
theorem faceFunctional_eq_zero_of_eventuallyEq_zero
    (hu : u =ᶠ[𝓝ˢ faceBox] 0) :
    faceFunctional ... u = 0
```

or an explicit open-neighborhood formulation. It immediately gives

```lean
theorem dsupport_faceDistribution_subset :
  dsupport (faceDistribution ...) ⊆ faceBox
```

and compact support.

The stronger statement “`u = 0` pointwise on `faceBox` implies `B u = 0`” is also valid under the positive-width box hypotheses: for each fixed base parameter, the box has dense interior in the tangential space, and smoothness determines its boundary tangential jets. Handle `K = ∅` separately or through the zero-dimensional API.

Do not prove this merely by saying “the integral is over the box”: `remList` also contains Taylor subtraction terms. Either:

- use the integral remainder formula, whose segments stay inside the box; or
- prove tangential derivatives vanish on the box from smoothness and positive widths.

Neighborhood locality is cheaper and already sufficient for distributional support and cutoff independence.

## 5.3 Reconstruction

The endpoint theorem should quantify over test functions on the original space:

```lean
theorem coeffDistribution_eq_sum_faceFunctional
    (f : 𝓓(Ω, ℝ)) :
    coeffDistribution X μ q f =
      ∑ P, ∑ J, ∑ a ∈ idxL ...,
        faceW J a *
          faceFunctional X P J a μ q
            (faceJet X P J a f)
```

This should be a short consequence of:

1. `coeffDistribution_apply`;
2. Theorem B applied to `X.withObs f f.contDiff`;
3. compatibility of its density/observable families with those of `X`;
4. face factorization;
5. representative independence.

The compatibility in item 3 is worth making explicit: `B` must depend on the fixed density data, not accidentally on the transported observable.

One also gets the accounting check
\[
|a|+\sum_{k\in K}p_k\le \sum_i p_i.
\]
Thus C5 reconstructs the existing active-coordinate derivative budget. It need not improve the already landed global order bound.

# 6. Grouping and normalization

Grouping by `|a| = r` is cheap finite-sum algebra, but optional.

The `1/r!` normalization is **not** automatic. Your current formula is multi-index based and already has `faceW` weights. Passing to a symmetric normal-tensor pairing invokes
\[
D^r f[h,\ldots,h]
 =\sum_{|\alpha|=r}\frac{r!}{\alpha!}
      \partial^\alpha f\,h^\alpha,
\]
so the resulting normalization depends on the chosen tensor and coefficient conventions.

Recommendation:

- optionally prove the regrouping theorem;
- leave tensor normalization out of C5;
- do not present `1/r!` as a harmless cosmetic rewrite.

# 7. Units and delegation

A reasonable division is:

| Unit | Content | Relative size |
|---|---|---|
| C5a | Restriction commutes with tangential derivatives, Taylor operators, `remList` | M |
| C5b | Face geometry, compact box, base measure support, joint-to-tangential jet bound | S–M |
| C5c | Tangential functional, integrability, linearity, density-splitting identity | M |
| C5d | Tangential bound, distribution constructor, support | M |
| C5e | Face-jet representatives, independence, reconstruction | M; larger if local chart extension is new |
| C5f | Optional regrouping and derivative-budget corollaries | S |

**First unit:** C5a, independent of the engine and base integration.

Delegate independently:

- restriction/remainder algebra;
- generic compact-set smooth-functional-to-distribution infrastructure;
- face geometry and tangential jet estimates;
- the `Zdist` boundary addition.

Keep density splitting and final reconstruction together, or agree on their exact interfaces first. They are the most sensitive to Theorem B’s indexing conventions.

# 8. C4s: statement and timing

I would land `Zdist` now, finish C5, and then do C4s. A small preliminary audit of the remainder constants is worthwhile, but C4s should not block the chart-face release.

## 8.1 Prefer a `JetBound` statement

Avoid introducing
\[
\max_{r\le R}\sup_Q\|D^r f\|
\]
as the first Lean interface. You already have the right abstraction:

```lean
∀ A, ∃ R C N₀,
  0 ≤ C ∧
  ∀ f M, 0 ≤ M →
    JetBound R Q f M →
    ∀ N, N₀ ≤ N →
      |Zdist X N ... f - truncatedCoeffSum X A N f|
        ≤ C * M * N ^ (-A) * (Real.log N) ^ L
```

Take `N₀ ≥ 2`; use the engine’s actual logarithmic exponent, specializing to `d - 1` where justified.

This is a worthwhile uniform theorem. It is uniform on the unit ball of a fixed compact-set jet seminorm, not merely testwise.

## 8.2 Order formula

Use the existing depth constructor rather than writing the schematic real expression `2kL - h` as a natural-valued definition. The actual order needs the engine’s rounding, positivity, and depth conventions:

```lean
remainderOrder X L :=
  Finset.univ.sup fun P =>
    ∑ j, remainderDepth X P L j
```

Then use the same density-product and chart-composition bridge as C1b/C1c.

Check that **every** remainder contribution is amplitude-linear with constants independent of `f`: Taylor terms, tail terms, finite coefficient corrections, and any eventual threshold. Pointwise remainder results with an `f`-dependent threshold are not yet the uniform theorem.

## 8.3 Obtaining little-o after truncation at `A`

Your proposed strategy is correct, but needs one explicit step.

Applying an estimate at `A' > A` controls the remainder after truncation at `A'`, not directly the remainder after truncation at `A`. Write
\[
Z_N-S_A
  =(Z_N-S_{A'})+(S_{A'}-S_A).
\]

The second term is a finite band of coefficients with exponents strictly greater than `A`. Their coefficient bounds and the positive spectral gap above `A` make it uniformly `o(N^{-A})`.

Thus the clean uniform little-o statement is:
\[
\forall\varepsilon>0\;\exists N_0\;
\forall f,M,N,\quad
\operatorname{JetBound}(R,Q,f,M),\ N\ge N_0
\Longrightarrow
|Z_N(f)-S_A(N,f)|\le\varepsilon M N^{-A}.
\]

The truncation must include **all log powers at every exponent `μ ≤ A`**. Otherwise boundary terms can obstruct little-o.

# 9. Non-claims and an eight-sentence mirror

You have not supplied the actual #123 paragraph, so I cannot audit it verbatim. This replacement matches the supplied boundary:

> For each exponent and logarithmic degree, the observable coefficient defines a continuous linear distribution on the original Euclidean space.  
> This distribution is intrinsic under the established comparison theorem for engine data with the same phase and prior.  
> Each presentation supplies a compact-set jet estimate and hence a finite upper bound on its distributional order.  
> Its support is contained in the compact wall image and in the topological support of the prior, and consequently in the zero set of the phase.  
> This zero-set containment does not require the phase’s zero set to be closed.  
> Theorem B presents the coefficient through chart-face renormalized functionals, without asserting that those functionals are measures.  
> Evaluation against each fixed test function yields the established asymptotic expansion, with admissible lattice parameters supplied by the chosen presentation.  
> No optimal order, canonical chart-face decomposition, measure representation, or uniform remainder estimate is claimed at this boundary.

C5 then strengthens sentence six to a genuine finite-order chart-face distribution presentation. The finite-part regression supports the caution against general order-zero claims; it does not itself identify the order of every coefficient in the engine.
