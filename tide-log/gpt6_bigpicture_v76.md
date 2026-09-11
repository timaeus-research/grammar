## Recommendation

**Do A, then B, then a concrete A+B piece-to-atlas bridge; use the fourth and fifth units for E. Defer C.** Keep D as the next application once that bridge exists.

The important milestone is not another abstract summation theorem. It is:

> **A nonempty prescribed chart–stratum piece actually instantiates the analytic cell machinery under explicit, checkable geometric hypotheses.**

A+B make this possible for units independent of the normal coordinates. They do **not** solve the general analytic-unit problem, but they produce a meaningful special case rather than another conditional interface.

---

## Q1. Ranking and proposed sequence

### Ranking

| Rank | Option | Assessment |
|---|---|---|
| **1** | **A: tangentially varying scalar unit** | Highest immediate value. Removes a genuine mismatch between the existing cells and even constant-chart-unit monomial pieces. Low analytic risk. |
| **2** | **B: two-sided assembly** | Necessary bookkeeping, not optional geometry. Together with A, gets the prescribed normal box into the existing analytic normal form. |
| **3** | **E: face coefficient and uniqueness** | Best next contribution to `eq:thm_leading_coeff`. First expose the explicit face formula, then prove representation-independence at a fixed scale. |
| **4** | **D: normal moments** | Useful for `thm:expectation_expansion`, but initially only gives moment leading terms on the model cells. It does not yet give the paper’s full expansion or identify the existing tube measures. |
| **5** | **C: prescribed-piece strip normalisation** | The local/global-in-one-coordinate diffeomorphism is plausible; the image-domain-to-cell step is the serious obstruction. It is not honestly a one-unit extension of CCXXX. |

### Next 3–5 units

1. **`ScalarUnitKernel`** — A, with pointwise and integrated certificates.
2. **`SymmetricScalarUnitCells`** — B plus the scalar-unit cell/finite-atlas packaging.
3. **`NormalConstantUnitPieceAtlas`** — the first concrete bridge from an adapted piece to these cells, under explicit amplitude, base, parity, and phase-factorisation assumptions.
4. **`BoxFaceFunctional`** — identify the existing analytic coefficient with an explicit face integral.
5. **`LeadingCoeffUniqueness`** — representation-independence at a common scale, and the conditional resolved-face formula.

If limited to three units, stop after the concrete bridge. If the face-integral identity is already nearly available by unfolding `amplitudeCoeff`, combine units 4–5 and use the spare unit for **D’s shifted-exponent moment theorem**.

### Value for the paper

- **A+B+bridge:** a genuine special-case analytic input to both target results.
- **E:** the most direct route to the *form* of `eq:thm_leading_coeff`.
- **D:** the most direct route toward normal-moment contributions to `thm:expectation_expansion`, but a leading-term theorem for each insertion is not an expansion with a controlled remainder.
- **C:** ultimately needed for general units by this prescribed-piece route, but its domain problem should not be hidden behind “normalisation”.

---

## Q2. Contracts for A

The following are suggested contracts, not claims about existing declaration names beyond those in your appendix.

### Unit 1: `ScalarUnitKernel`

Use a separate name for the phase unit, say `q`, so it cannot be confused with the tangential density `βw`.

```lean
noncomputable def scalarBoxKernel
    (q : (Fin t → ℝ) → ℝ)
    (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  boxKernel n h k 1 b A z (N * q z)
```

This definition avoids rebuilding `origPhaseIntegral`. Prove the corresponding identity with the prescribed kernel whose phase coefficient is `q z`.

```lean
theorem scalarBoxKernel_eq_origPhaseIntegral :
  scalarBoxKernel n h k b q A z N =
    origPhaseIntegral n h k (q z) N b (fun _ => 0) (A z)
```

No positivity should be needed for this algebraic identity.

Define the coefficient by reference to the unit-1 coefficient:

```lean
noncomputable def scalarBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  (q z) ^ (-l) * boxFaceCoeff n h k 1 b A l z
```

Here the power is real `rpow`.

### A.1. General positive time-rescaling lemma

Put this in the leading-term infrastructure if it is not already available.

```lean
theorem HasLeadingTerm.comp_mul_const
    (hZ : HasLeadingTerm Z c l j) (ha : 0 < a) :
    HasLeadingTerm (fun N => Z (N * a)) (a ^ (-l) * c) l j
```

The underlying scale statement is

\[
\frac{s_{\lambda,j}(aN)}{s_{\lambda,j}(N)}
\longrightarrow a^{-\lambda}.
\]

Only eventual positivity of \(N\), \(aN\), and their logarithms is needed; do not force identities involving division by the scale at small \(N\).

**Reuse:** the definition of `HasLeadingTerm`, existing scale-change lemmas if any, and standard `atTop` multiplication lemmas.

### A.2. Pointwise certificate

```lean
theorem hasLeadingTerm_scalarBoxKernel
    (hk : ∀ i, 0 < k i)
    (hb : 0 < b)
    (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A))
    (hqz : 0 < q z) :
    HasLeadingTerm
      (scalarBoxKernel n h k b q A z)
      (scalarBoxFaceCoeff n h k b q A l z)
      l (multCount (ratioExp h k) l - 1)
```

**Proof:** CCXXIX at phase unit 1, followed by positive time rescaling.

Notably, **no continuity of `q` is needed pointwise**.

### A.3. Uniform domination: use comparison, not uniform logarithm algebra

Your proposed uniform scale-ratio argument is sound. But for the theorem actually needed by CCXXVII, there is a simpler proof.

Assume

```lean
hq0 : 0 < q₀
hq_lower : ∀ z ∈ T, q₀ ≤ q z
```

For \(N\ge0\), positivity of the monomial density and phase gives

\[
|L_N^{q(z)}[A](z)|
\le L_N^{q_0}[|A|](z).
\]

The right side is exactly a **constant-unit kernel already covered by CCXXIX**. Since `abs ∘ uncurry A` is continuous, apply `eventually_abs_boxKernel_div_le` to this kernel.

Recommended public statement:

```lean
theorem eventually_abs_scalarBoxKernel_div_le
    (hk : ∀ i, 0 < k i)
    (hb : 0 < b) (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A))
    (hT : IsCompact T)
    (hq0 : 0 < q₀)
    (hq_lower : ∀ z ∈ T, q₀ ≤ q z) :
    ∃ C, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ z ∈ T,
        |scalarBoxKernel n h k b q A z N /
          powLogScale l (multCount (ratioExp h k) l - 1) N| ≤ C
```

Advantages:

- no upper bound on `q`;
- no continuity of `q` for this bound;
- no new uniform asymptotic theorem;
- no need to manage a uniform logarithmic scale ratio.

Prove the integral comparison with explicit integrability on the bounded cube. Do not rely on order properties of totalised integrals without discharging those hypotheses.

### A.4. Integrated certificate

For the first public version, use the convenient geometric hypotheses:

```lean
hq : ContinuousOn q T
hq_pos : ∀ z ∈ T, 0 < q z
hT : IsCompact T
hβw : IntegrableOn βw T
```

Then:

```lean
theorem hasLeadingTerm_integral_scalarBoxKernel
    ...
    (hq : ContinuousOn q T)
    (hq_pos : ∀ z ∈ T, 0 < q z)
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm
      (fun N => ∫ z in T,
        βw z * scalarBoxKernel n h k b q A z N)
      (∫ z in T,
        βw z * scalarBoxFaceCoeff n h k b q A l z)
      l (multCount (ratioExp h k) l - 1)
```

**Proof obligations:**

1. Obtain a uniform positive lower bound on `q` from compactness, treating the empty base separately.
2. Establish measurability of the parameterised kernels and coefficient on the restricted base.
3. Apply the pointwise certificate.
4. Apply the comparison-based bound.
5. Use CCXXVII with constant domination \(G(z)=C\).

**Reuse:**

- `hasLeadingTerm_boxKernel`;
- `eventually_abs_boxKernel_div_le`;
- `hasLeadingTerm_integral_of_dominated_kernel`;
- the parameter-integral measurability infrastructure already used in CCXXIX.

A more general version with measurable `q` and an explicit positive lower bound can come later.

### A.5. Scalar-unit cells are a genuine interface extension

Do **not** imply that A produces `FiniteConstantUnitAtlas`. A varying `q(z)` does not automatically yield a finite atlas of the old cells.

Introduce, for example:

```lean
structure ScalarUnitCell (t : ℕ) where
  -- same n, h, k, b, A, base, βw fields
  q : (Fin t → ℝ) → ℝ
  q_cont : ContinuousOn q base
  q_pos : ∀ z ∈ base, 0 < q z
```

and `FiniteScalarUnitAtlas`, with the same exact-decomposition field.

Provide:

- embedding of `ConstantUnitCell` into `ScalarUnitCell`;
- cell leading-term theorem;
- finite-atlas extremal theorem;
- the scalar-unit analogue of `hasLeadingTerm_boltzmannIntegral_of_atlases`.

These are short adaptations of CCXXX. Avoid a large generic-cell abstraction unless duplication actually becomes troublesome.

---

## The following two units: what makes A useful

### Unit 2: symmetric-box assembly

For continuous amplitudes, prove the scaled reflection identity

\[
L_N^{\mathrm{sym}}(z)
=
\sum_{\sigma}
L_N^+\bigl[A_\sigma\bigr](z),
\qquad
A_\sigma(z,u)=A(z,\operatorname{reflect}_\sigma u).
\]

Use:

- `integral_symBox_eq_sum_reflect`;
- dilation by \(b\);
- invariance of \(|u_j|^{h_j}\) under reflection;
- evenness of \(u_j^{2k_j}\).

The result should package the symmetric kernel as a finite scalar-unit atlas indexed by `Fin (n+1) → Bool`.

**Boundary convention:** prove equality a.e. between the open box used by the piece and the half-open box used by the integration theorem. Coordinate faces have volume zero. Exact disjoint set equality is unnecessary.

### Unit 3: the concrete piece bridge

The first bridge should accept the analytic factorisation as a hypothesis, rather than hide its extraction from `IsMonomialChart`.

Require, on the relevant product region:

1. an adapted density;
2. a positive scalar phase factor `q z`;
3. positive half-exponents `k`;
4. a continuous amplitude `A`;
5. an a.e. identity
   \[
   \text{piece integrand}
   =
   1_T(z)\,\beta_w(z)\,
   1_{(-b,b)^r}(n)\,
   A(z,n)\prod_j|n_j|^{h_j}
   e^{-Nq(z)\prod_j n_j^{2k_j}};
   \]
6. the necessary integrability for changing order and summing;
7. a compact integration carrier for the base.

Then use `pieceIntegral_eq_adapted`, parity reindexing, and orthant assembly to construct the atlas.

After that, give a corollary extracting these inputs from monomial charts **whose phase unit is independent of the normal coordinates**. A constant chart unit is a special case.

Two details deserve explicit contracts:

- **Measurable \(F\) is insufficient for continuous `A`.** The bridge needs stronger regularity of the pulled-back observable and residual density, or a separate approximation theorem.
- **The natural base dimension is \(d-r\), whereas the displayed CCXXX Boltzmann theorem requires atlases with `t = d`.** Resolve this explicitly. Prefer letting the atlas base dimension depend on the piece. Alternatively prove a dummy-coordinate padding construction using a finite-volume carrier of volume one. Embedding the base into a lower-dimensional subspace of \(\mathbb R^d\) is not valid: ambient Lebesgue measure would vanish there.

---

## Why I would not schedule C now

### The diffeomorphism part is feasible

Fix \(j_0\in I\), write \(e=e_{j_0}>0\), and set

\[
\rho(z,n)=u(z,n)^{1/e},\qquad
s_{j_0}=n_{j_0}\rho(z,n),\qquad s_j=n_j\quad(j\ne j_0).
\]

For a **fixed compact carrier** of the other variables, positivity and \(C^1\) regularity give uniform bounds

\[
\rho\ge c>0,\qquad |\partial_{j_0}\rho|\le M
\]

on a suitable compact neighbourhood. For sufficiently small \(b\),

\[
\partial_{n_{j_0}}s_{j_0}
=\rho+n_{j_0}\partial_{j_0}\rho
\ge c-bM>0.
\]

Because the other coordinates are unchanged, strict monotonicity on each \(n_{j_0}\)-interval proves injectivity on the whole product piece. Analytic inverse regularity follows locally and patches by uniqueness.

This argument requires a common neighbourhood and common bounds. It should not be phrased as merely “positive on the piece, therefore choose ε small”, especially when the tangential base itself changes with ε.

### The image is a variable strip, not a cube

Writing \(n'\) for the unchanged normal coordinates, the image is

\[
z\in T,\quad n'\in(-b,b)^{r-1},\quad
g_-(z,n')<s_{j_0}<g_+(z,n'),
\]

where

\[
g_\pm(z,n')=\pm b\,\rho(z,n',\pm b).
\]

The transformed monomial density still has the prescribed power in \(s_{j_0}\), with a positive smooth residual factor absorbed into the amplitude. But the **domain indicator has variable boundaries**.

Mapping this interval back to a fixed interval generally reintroduces a unit depending on the remaining normal variables. Thus the proposed normalisation does not close the problem.

### Honest output of C

Its immediate output should be something like a **`NormalisedStripDensity`**:

- a fibre-preserving change of variables;
- analytic inverse on a neighbourhood;
- variable endpoint functions;
- transformed continuous amplitude;
- exact change-of-variables integral identity.

It should **not** directly claim a `ScalarUnitCell` or `ConstantUnitCell`.

To obtain finite cube cells afterwards, one needs additional work:

- a kernel theorem on variable strips; or
- an allocation subordinate to normalised product charts, with supports allowing continuous extension of amplitudes; or
- a stratified treatment of the portions outside an inner product box.

A finite exact axis-aligned tiling is not generally available for curved strip boundaries. An allocation is the more natural route, but a subordinate allocation on a neighbourhood does not by itself remove the original piece’s discontinuous boundary indicator.

Also, the outer part is **not automatically exponentially small**: other normal coordinates can still vanish there. Depending on the critical ratios, it can contribute at the leading scale.

---

## E and D: scope the deliverables carefully

### E: split explicit formula from coordinate-free interpretation

First prove a face-evaluation theorem for the existing coefficient. If

\[
J=\{j:\operatorname{ratioExp}(h,k,j)=\lambda\},
\]

the model face is obtained by setting the coordinates in \(J\) to zero and integrating over the remaining normal coordinates with the appropriate residual powers.

If **all ratios are minimal**, all normal coordinates are set to zero: the normal face integral becomes an evaluation at the normal origin, leaving the tangential integral.

Audit the exact constants against the existing definition:

- \(\Gamma(\lambda)\);
- factorial/log multiplicity;
- factors involving \(2k_j\);
- dilation powers of \(b\);
- phase-unit powers.

Do not guess these from the paper’s notation.

Then prove uniqueness:

> If two decompositions give `HasLeadingTerm Z c₁ λ j` and `HasLeadingTerm Z c₂ λ j`, then `c₁ = c₂`.

This establishes **representation-independence of the scalar coefficient at a fixed scale**. It does not, on its own, identify an intrinsic face density or prove its coordinate transformation law. Call the result “decomposition-independent coefficient” until that additional geometric identification is supplied.

### D: shifted moments have two caveats

On a positive orthant, \(u^\alpha\) really does replace \(h\) by \(h+\alpha\), giving

\[
\lambda_\alpha=\min_j\frac{h_j+\alpha_j+1}{2k_j}.
\]

But:

1. on a symmetric box, signed moments acquire orthant signs and can cancel;
2. dividing by the partition function requires a **nonzero, normally positive denominator coefficient**.

Even after that, identifying the resulting probability measure with `condTubeNormalMeasure` requires an explicit equality of measures or densities. It is not a consequence of matching scaling exponents.

---

## Q3. Audit of CCXXVI–CCXXX

From the supplied statements, I see **no evident mathematical contradiction**. I cannot audit proof details from signatures alone. The main risks are descriptions and missing bridges.

### 1. CCXXVI: a zero certificate is not a nonzero asymptotic

The divisor-free conclusion is appropriate. Likewise, the extremal theorem allows a strictly dominating pair and therefore a zero coefficient.

Document:

> “A leading-term certificate at the chosen scale, possibly with coefficient zero.”

Do not infer that the chosen pair is the actual leading pair, or that numerator/denominator asymptotic division is available.

### 2. CCXXVIII: `AdaptedProductDensity` does not itself assert measurability of `beta`

The structure comment says “measurable only”, but the displayed fields contain **no measurability hypothesis on `beta`** and no regularity field on `amp`.

That is fine for an algebraic a.e.-factorisation structure if subsequent integral theorems supply the needed hypotheses. The documentation should say:

> “Tangential weight; regularity is imposed by downstream integration theorems.”

Also, the fibre-constant hypothesis is strong: it concerns the **allocation including the domain indicator**, not merely a partition weight with weak normal variation.

### 3. Adapted density does not supply the cell’s compact base

The displayed constructor supplies a measurable foot-condition base. It does not visibly supply compactness. Bounds on tangential coordinates come from an appropriate compact chart carrier or effective support, not from the foot condition alone.

A correct bridge may integrate over a compact carrier and put the actual base indicator into `βw`. That support reduction must be proved.

### 4. CCXXIX’s analytic scope is narrower than arbitrary monomial charts

The hypotheses explicitly require:

- strictly positive normal half-exponents;
- natural-number density exponents;
- globally jointly continuous amplitude.

That is consistent with the model theorem. The chart bridge must establish these, including parity from the actual hypotheses of `even_positive_form_halfExp`. Nonnegativity only on a one-sided domain would not by itself force even exponents.

### 5. CCXXX is conditional on an exact analytic-cell decomposition

“Conditional on adapted geometry” is acceptable shorthand, but I would sharpen it to:

> **Conditional on finite exact scalar/cube-kernel decompositions of every nonempty chart–stratum piece. No such decomposition is constructed here from general monomial charts or from fibre-constant allocation alone.**

Indeed, the displayed theorem takes `FiniteConstantUnitAtlas` directly; it does not take or produce `AdaptedProductDensity`.

That is an honest and useful theorem. The next accomplishment should be **one concrete constructor for its hypotheses**, suitably extended to scalar units—not another statement suggesting that the general geometric constructor is already implicit.
