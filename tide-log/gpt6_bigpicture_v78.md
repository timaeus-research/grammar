## Recommendation

**Close the existing conditional pipeline before adding a new analytic mechanism.** N1 is the right next target, but split its conclusion into:

1. a leading-term theorem, allowing a zero coefficient;
2. a combinatorial identification of the geometric extremal pair;
3. a positivity theorem with a **dominant-face positivity hypothesis**, not merely “\(F,p\ge0\), positive somewhere.”

Two qualifications matter immediately:

- Product-shaped domains do give the required fibre saturation for every \(I\). **They do not automatically give fibre-constant cover weights.**
- A geometric extremal pair is not necessarily the actual leading pair for a given amplitude: its coefficient can vanish.

These are the main issues to settle before writing the large assembly theorem.

## Q1. Ranking and the next five units

| Rank | Candidate | Reason |
|---|---|---|
| **1** | **N1 — end-to-end assembly** | Highest payoff from the landed work. It turns the existing constructors and assembly machinery into a usable theorem about the original integral. |
| **2** | **N7 — targeted fidelity review** | Do this first operationally, but keep it bounded. Audit weight hypotheses, multiplicity conventions, positivity, and what “leading” means when the coefficient is zero. |
| **3** | **N2 — whole-box theorem** | Best concrete example and regression test; substantially less geometric bookkeeping. A one-chart cover also avoids the difficult overlap-weight hypothesis. |
| **4** | **N3 — normal-dependent units** | The next substantive analytic generalisation after closing N1. It removes a genuinely restrictive hypothesis, but should not delay assembly. |
| **5** | **N4 — tube-measure identification** | Important for fidelity and interpretation, but less valuable than making the present asymptotic theorem usable first. |
| **6** | **N6 — statistical transfer** | Better after the positive denominator theorem and the relevant measure/moment identifications are stable. |
| **7** | **N5 — all orders** | A large scope increase while the first-order global theorem is still unassembled. Also, analytic amplitude alone does not settle all cutoff/parameter issues. |

### Proposed five-unit programme

1. **CCXLI `ProductChartHypotheses`**  
   Targeted review, hypothesis packages, and notation/convention lemmas.
2. **CCXLII `ProductChartPieceData`**  
   Derive the CCXXXVIII hypotheses uniformly for every nonempty \(I\).
3. **CCXLIII `ProductChartCoverAsymptotics`**  
   Instantiate the existing global scalar-atlas theorem.
4. **CCXLIV `ProductChartExtremalPair`**  
   Compute the pair over chart–stratum indices and simplify it to divisor ratios.
5. **CCXLV `PositiveProductChartAsymptotics`**  
   Nonnegative total coefficient, a sufficient tied-face positivity theorem, and genuine equivalence. Include a small one-chart/all-minimal example if space permits.

The standalone N2 theorem is then the next unit, or a substitute for unit 5 if positivity requires a substantial new general-face argument. Do not hide that argument inside the assembly module.

---

## Q2. Contracts for N1

### 1. Separate the analytic and geometric hypothesis packages

I would not start with one enormous `ProductMonomialChart` containing everything, including \(F\). Use two layers.

#### A. Generic per-piece input package

A schematic structure:

```lean
structure ScalarAtlasChartData
    (R : ResolutionCover d ι) (i : ι)
    (K : (Fin d → ℝ) → ℝ) (ε : ℝ) where
  e h : Fin d →₀ ℕ
  W : Set (Fin d → ℝ)
  monomial : IsMonomialChart K ... e h W
  u v : (Fin d → ℝ) → ℝ
  -- explicit witnesses compatible with `monomial`
  -- continuity, unit nonvanishing, phase and determinant identities

  pieceData :
    ∀ I, I ⊆ e.support → I.Nonempty →
      -- closed T', bounded measurable ρT,
      -- hdom, hρ, normal-independence,
      -- and the zero-point hypothesis
```

The exact factoring should follow the fields of `IsMonomialChart`. **Avoid storing a second, unrelated pair of monomial witnesses** if that structure already provides the required ones.

Keep the assumptions on \(F\), \(p\), their pullback continuity, and integrability at theorem level. The chart geometry should be reusable across observables.

This layer gives an assembly theorem even when the geometric product-box model is not the source of the piece data.

#### B. Concrete centred-product realisation

A second structure, tentatively `CenteredProductMonomialChart`, should certify:

- \(J=e.support\);
- a compact inactive-coordinate base \(T\);
- a normal radius \(b>0\);
- the exact domain description
  \[
  y\in\mathrm{dom}
  \iff
  y_{J^c}\in T \ \land\ \forall j\in J,\ |y_j|\le b;
  \]
- an open monomial neighbourhood \(W\supseteq\mathrm{dom}\);
- simultaneous zeroing map \(P_J\);
- unit independence
  \[
  u(y)=u(P_Jy)\qquad(y\in\mathrm{dom});
  \]
- **a separate cover-weight factorisation**
  \[
  R.weight\,i\,((R.chart\,i).\Phi y)
  =r_i(y_{J^c})\qquad(y\in\mathrm{dom}),
  \]
  with \(r_i\) measurable and bounded.

The last item is essential. The weight is determined by the cover images, not freely chosen. Arbitrary overlaps can make it depend on active coordinates even when every source domain is a perfect product box.

Thus the honest theorem is about **product charts with normal-independent units and compatible cover weights**.

For a one-chart cover, the weight condition should be discharged by a lemma showing the weight is \(1\) on the relevant image, using the library’s `Φ`/`φ` compatibility. Do not silently replace `Φ` by `φ`.

### 2. Uniform per-piece choices of \(T'\) and \(\rho_T\)

Fix \(I\subseteq J\), \(I\ne\varnothing\). Let \(P_I\) zero exactly the coordinates in \(I\).

A convenient ambient-foot set is

\[
T'_I=
\left\{x:
\begin{array}{l}
x_j=0\quad(j\in I),\\
x_{J^c}\in T,\\
\varepsilon\le |x_j|\le b\quad(j\in J\setminus I)
\end{array}
\right\}.
\]

This is a **foot-space product of the inactive base and closed annuli**, not just the original inactive base. It is closed, indeed compact under the stated hypotheses.

Then prove:

```lean
∀ y ∈ sizePiece J ε I,
  y ∈ chart.dom ↔ planeFoot split y ∈ T'_I
```

The selected normal coordinates already satisfy \(|y_j|<\varepsilon<b\), so their domain bounds are automatic. The remaining active coordinates supply the annuli.

An alternative is to omit the lower annulus bound in \(T'_I\), since it is already supplied by `sizePiece`. Both work; choose one and use it consistently.

For the density, define globally

\[
\rho_{T,I}(x)=r_i(x_{J^c}).
\]

It need not be supported on \(T'_I\). The restriction machinery handles support.

**Do not define \(\rho_T\) merely by evaluating the cover weight at the foot and expect the result to follow.** That construction still requires the missing equality between the original weight and its foot value.

The same product geometry proves that \(P_Iy\in\mathrm{dom}\) whenever \(y\in\mathrm{dom}\). Hence simultaneous unit independence implies the required piece independence:

\[
u(y)=u(P_Jy)=u(P_J(P_Iy))=u(P_Iy).
\]

This deserves a standalone lemma.

### 3. Choice of \(\varepsilon\)

For finitely many chart radii \(b_i>0\), choose one common

\[
0<\varepsilon< b_i\quad\text{for every relevant }i.
\]

For a nonempty finite index type, half the minimum radius is adequate. A finite-positive-lower-bound lemma is cleaner than repeatedly constructing a `Finset.min'`.

Two edge cases:

- Empty cover: handle separately or use a lower-bound existence lemma that treats it vacuously.
- Charts with \(e_i.support=\varnothing\): they contribute only divisor-free pieces and need no nonempty-stratum atlas.

Strict inequality is a good public hypothesis, even if fibre saturation alone only needs \(\varepsilon\le b_i\).

The compact domain uses closed normal boxes, whereas the pieces use strict selected-coordinate bounds. Reuse the existing closed-ball membership lemma for continuity on the closed cell; do not turn the compact domain into an open box.

### 4. Uniform atlas construction

Define

```lean
tdim i I := d - I.card
```

and isolate the arithmetic transport from

```lean
d - (I.card - 1 + 1)
```

in one lemma under `I.Nonempty`.

Then expose a theorem of the form:

```lean
∃ At :
    ∀ i I, I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (d - I.card) (...),
  ∀ i I hI hne σ,
    (At i I hI hne).cell σ |>.lam = pieceLam i I ∧
    (At i I hI hne).cell σ |>.mult = pieceMult i I
```

Use classical choice once, behind a definition or theorem boundary. Do not force downstream proofs to unfold the Tietze extension or the chosen atlas.

**Reuse:** CCXXXVIII for each atlas; CCXXXVI–VII through that constructor.

**Pitfall:** “nonempty piece” is ambiguous. The existing assembly theorem asks for every **nonempty index set \(I\)**, including geometrically empty pieces. Either construct their zero atlases through the existing machinery, or explicitly provide a zero-piece branch. Do not silently strengthen “\(I\ne\varnothing\)” to “the region has positive measure.”

Likewise, derive the zero-point hypothesis from a nonempty product base, or retain it explicitly. An empty chart domain does not itself supply such a point.

### 5. First global theorem: arbitrary dominating pair

Before computing extrema, write the cheap theorem:

```lean
hasLeadingTerm_boltzmannIntegral_of_productCharts
```

with supplied \(\lambda_0,k_0\) and piece-level bounds

\[
\lambda_0\le\lambda_{i,I},\qquad
\lambda_{i,I}=\lambda_0\Rightarrow m_{i,I}-1\le k_0.
\]

Its proof should be essentially:

1. obtain the uniform atlases;
2. rewrite cell parameters using their certificates;
3. invoke `hasLeadingTerm_boltzmannIntegral_of_scalarAtlases'`.

Expose the coefficient as the existing tied-atlas sum. An explicit face-integral formula can be a later theorem.

Then provide a thin `coverIntegral` wrapper, schematically

\[
N\longmapsto
R.coverIntegral\,
  (\lambda x,\ F(x)p.w(x))\,
  (\lambda x,\ -N K(x)).
\]

Check the precise definition of `boltzmannIntegral` and multiplication order before claiming a definitional equality.

### 6. Extremal pair across \((i,I)\)

Define the finite dependent index type

\[
\mathcal P=\{(i,I):I\subseteq J_i,\ I\ne\varnothing\}.
\]

For \(j\in J_i\), put

\[
r_{ij}=\frac{h_i(j)+1}{e_i(j)}.
\]

Parity identifies this with the existing ratio using `normalHalfExp`.

For a piece,

\[
\lambda_{i,I}=\min_{j\in I}r_{ij},\qquad
m_{i,I}=\#\{j\in I:r_{ij}=\lambda_{i,I}\}.
\]

The global ordering is:

- **minimum** \(\lambda\);
- among those, **maximum** \(m-1\).

Prove that explicitly rather than relying on an opaque pair order.

When some active divisor exists,

\[
\boxed{\lambda_*=\min_{i,\ j\in J_i}r_{ij}}
\]

and, because the full subset \(I=J_i\) is included,

\[
\boxed{
k_*=
\max_{\substack{i\\\exists j\in J_i,\ r_{ij}=\lambda_*}}
\left(\#\{j\in J_i:r_{ij}=\lambda_*\}-1\right).
}
\]

This avoids enumerating powersets in the final user-facing formula.

These are **geometric extrema over the prescribed indices**. Empty domains, zero weights, and amplitudes vanishing on dominant faces can make their coefficient zero. Until positivity is proved, do not describe them as the actual leading exponents of the observable.

If there are no active divisors, return the divisor-free negligibility theorem, not an arbitrary minimum of an empty family.

### 7. Positivity: stage it honestly

First prove an abstract assembly lemma:

- every tied coefficient is nonnegative;
- at least one tied coefficient is positive;
- therefore the total coefficient is positive and the global result is a genuine `~`.

Then supply a concrete sufficient criterion from CCXXXIX:

- a tied piece whose normal ratios are all minimal;
- the corresponding cell has nonnegative base weight and face amplitude;
- both are strictly positive together on a set of positive tangential measure.

There is an important remaining gap:

> CCXXXIX’s all-minimal positivity theorem does not automatically establish positivity for every dominant piece.

A dominant full piece may contain both minimal and nonminimal coordinates. Its face coefficient then involves integration over the nonminimal coordinates. General N1 positivity requires a general-face nonnegativity/positivity theorem, or a clearly advertised sufficient all-minimal tied-piece hypothesis.

Also, existentially choosing an atlas is not enough for concrete positivity. Expose a constructor certificate connecting its cells’ coefficients to the chart face amplitudes, or add a strengthened `exists_pieceAtlas_of_chart` corollary carrying that certificate.

---

## Q3. Statement audit

From the displayed statements, I see **no demonstrated mathematical error**, but several qualifications need to be reflected in the prose.

### 1. Multiplicity versus logarithmic degree

The appendix states

```lean
cell.mult = multCount ...
```

whereas the contextual description says cells are at “\((\minRatio,\#\min-1)\).”

That is correct only if “at” denotes the **asymptotic pair**

\[
(\texttt{cell.lam},\texttt{cell.mult}-1).
\]

The stored multiplicity itself is \(\#\min\), not \(\#\min-1\). Standardise this terminology now.

### 2. “Positive somewhere” is insufficient for N1

This is a problem with the proposed conclusion, not the displayed CCXXXIX theorem.

For example,

\[
K(x)=x^2,\qquad p(x)=1,\qquad F(x)=x^2
\]

on a centred interval has nonnegative amplitude, positive away from zero. Nevertheless, its coefficient at the geometric exponent \(1/2\) is zero; its actual decay is \(N^{-3/2}\).

The needed positivity is on a **dominant face with the relevant measure and cover weight**. The stated positive-measure hypothesis in `coeff_pos_of_all_minimal` correctly captures that distinction.

Also, the displayed chart constructor assumes continuity of \(v\), not explicitly \(v\ne0\). Any deduction of positive face amplitude must account for \(|v|\), as well as the tangential Jacobian monomial.

### 3. The symmetric coefficient formula is specifically all-minimal

The factor

\[
2^{n+1}\,\texttt{coeff}
\]

is justified in the all-minimal case because the relevant face evaluates every normal coordinate at zero, where all reflected amplitudes agree.

It is not the general reflected-coefficient formula when nonminimal coordinates remain free. The theorem name `hasLeadingTerm_symIntegral` should be checked for visible hypotheses: if it is restricted to the all-minimal situation, make that clear in its documentation or name.

The displayed `symIntegral_isEquivalent_of_all_minimal` is appropriately restricted.

### 4. The ratio-limit statement looks sound

`HasLeadingTerm.tendsto_div_ratio` needs neither ordering of the exponents nor ordering of the log degrees. It is simply division of two normalised limits, with a nonzero denominator limit.

The use of total real division does not invalidate the algebraic rearrangement.

### 5. Signed moments may have zero coefficient

The displayed symmetric-moment theorem correctly sums orthant coefficients with signs. Odd-moment cancellation can make the sum zero.

Thus it proves a `HasLeadingTerm` statement at the shifted geometric pair, **not necessarily a nonzero leading term or a genuine equivalence**. Document this alongside the theorem.

### 6. Scope of the review

The excerpt does not expose the complete statements of every CCXXXVI–CCXL theorem, nor the definitions of the coefficient prefactors. A full audit should therefore specifically check:

- exponent parity and the simultaneous zero-point hypothesis;
- the all-minimal assumptions on reflection identities;
- the normalisation of `faceConst`;
- compatibility of `Φ` and `φ`;
- whether atlas construction exposes enough coefficient information for positivity.

**Bottom line:** assemble N1 now, but advertise it first as a strong-hypothesis leading-term theorem with a possibly zero coefficient. Make positive dominant-face mass—not generic positivity somewhere—the gate to the final `~` theorem.
