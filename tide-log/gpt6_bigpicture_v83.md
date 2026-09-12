Yes: **take (B) for R3**, as a theorem about localisation by a supplied partition, rather than changing the meaning of `ResolutionCover.weight`. It removes the mathematical restriction you want to remove, while preserving the counting-cover infrastructure and its compatibility theorems.

The main qualification is that this gives a **new top-level assembly theorem**, not a generalisation of every existing multi-chart product theorem. That is a good boundary for this programme.

## Q1. R3: supplied partition, one-chart analysis, finite assembly

### 1. State the decomposition in terms of the weights actually integrated

Put
\[
A_i=\phi_i(\operatorname{dom}_i),\qquad U=\bigcup_i A_i,
\qquad g_N(x)=F(x)p(x)e^{-NK(x)}.
\]

The fundamental condition is
\[
\boxed{\quad
\sum_i \mathbf 1_{A_i}(x)\psi_i(x)=1
\quad\text{for a.e. }x\in U.
\quad}
\]

Under the requisite measurability and integrability hypotheses, it gives exactly
\[
\boxed{\quad
\int_U F(x)p(x)e^{-NK(x)}\,dx
=
\sum_i\int_{A_i}F(x)p(x)\psi_i(x)e^{-NK(x)}\,dx.
\quad}
\]

Equivalently, using the one-chart covers \(R_i\),
\[
\operatorname{boltzmannIntegral}_R(F,K,p,N)
=
\sum_i
\operatorname{boltzmannIntegral}_{R_i}(F,K,p\psi_i,N).
\]

This is the identity to formalise first. It does **not** insert the original counting weights on the right.

For signed \(F\), retain explicit integrability hypotheses, or discharge them from the existing bounded-observable/compact-domain assumptions. Measurability and the partition identity alone are not enough to invoke finite-sum identities for general Bochner integrals.

### 2. A conventional subordinate-partition wrapper

A convenient sufficient interface is:

* \(\psi_i\) measurable;
* \(\psi_i\geq0\);
* \(\sum_i\psi_i(x)=1\) on \(U\);
* for \(x\in U\setminus A_i\), \(\psi_i(x)=0\).

The last two conditions imply the masked identity above. They can be weakened to a.e. conditions for the decomposition theorem.

**You do not need global**
\[
\operatorname{supp}\psi_i\subseteq A_i.
\]
Relative subordination on \(U\) is enough: values outside \(U\) never enter the identity. Moreover, requiring topological support containment in a compact chart image can be unnecessarily strong.

Conversely, as you note, merely requiring \(\sum_i\psi_i=1\) on \(U\) is insufficient when the right-hand integrals are restricted to \(A_i\). Positive “leakage” from \(\psi_i\) into \(U\setminus A_i\) loses mass.

I would therefore expose two layers:

1. **Core decomposition:** masked partition identity.
2. **User-facing partition theorem:** ordinary partition identity plus relative subordination.

This also accommodates supplied chart-domain allocations later, without committing to a new cover structure.

### 3. Regularity belongs to the one-chart analytic data

The algebraic decomposition needs no continuity. The asymptotic theorem needs precisely enough regularity to make
\[
\psi_i(\phi_i(\Psi_i(z,n)))
\]
a continuous factor of the piece amplitude on the set required by the Tietze/normal-form machinery.

Thus the clean analytic hypothesis is:

> The pulled-back supplied weight has the continuous representative/extension required on each chart’s normal-form neighbourhood \(W_i\).

An ambient function continuous on an open neighbourhood of \(U\) is a pleasant sufficient hypothesis, provided its pullback is defined on the relevant neighbourhood. It should be a convenience wrapper, not the core abstraction.

Continuity merely on \(A_i\) gives continuity on \(\operatorname{dom}_i\), but does **not by itself** supply whatever your package requires outside that domain on \(W_i\). One must either:

* assume the needed pullback continuity directly; or
* construct a continuous extension from the actual closed carrier used by the piece theorem.

Do not silently pass from relative continuity on the image to continuity throughout \(W_i\).

### 4. Boundedness and `TubeWeight`

Nonnegativity and \(\sum_i\psi_i=1\) imply \(0\leq\psi_i\leq1\) **on \(U\)**. That need not give a global `TubeWeight`.

Two reasonable interfaces are:

* require globally bounded nonnegative measurable \(\psi_i\), with regularity only where needed; or
* use a bounded representative agreeing with \(\psi_i\) on \(U\).

For instance, clipping a globally supplied regular function to \([0,1]\) preserves continuity and changes nothing on \(U\). In contrast, extension by zero across the boundary of \(U\) can destroy the pullback regularity you need. Avoid making that the default construction.

### 5. What disappears, and what remains

For a one-chart counting cover,
\[
\rho_i(\phi_i(y))=1\qquad(y\in\operatorname{dom}_i).
\]
Consequently, the allocation part of the old chart data can use \(r=1\), and the genuinely normal-dependent factor \(\psi_i\circ\phi_i\) sits in the amplitude through the prior \(p\psi_i\).

This removes the **supplied-weight fibre-constancy restriction**. It does not remove:

* the product/fibre hypotheses on the chart domain;
* the closed-foot/carrier hypotheses;
* the resolution-to-product localisation gap.

That distinction belongs in the scope statement.

### 6. The headline theorem

For each \(i\), apply the landed one-chart variable-unit theorem with prior \(p\psi_i\), obtaining
\[
Z_{i,N}[F]
=
C_i[F]\,N^{-\lambda_i}(\log N)^{k_i}
+
o\!\left(N^{-\lambda_i}(\log N)^{k_i}\right).
\]

Define
\[
\lambda_*=\min_i\lambda_i,\qquad
k_*=\max_{\lambda_i=\lambda_*}k_i,
\]
and let \(T\) be the charts attaining both extrema. Then the signed headline is
\[
\boxed{
Z_N[F]
=
\left(\sum_{i\in T}C_i[F]\right)
N^{-\lambda_*}(\log N)^{k_*}
+
o\!\left(N^{-\lambda_*}(\log N)^{k_*}\right).
}
\]

Under positivity of the summed normaliser coefficient,
\[
Z_N[1]\sim
\left(\sum_{i\in T}C_i[1]\right)
N^{-\lambda_*}(\log N)^{k_*},
\]
and the posterior consequence is
\[
\boxed{
\mathbb E_N[F]\longrightarrow
\frac{\sum_{i\in T}C_i[F]}
     {\sum_{i\in T}C_i[1]}.
}
\]

Suggested headline families:

* `boltzmannIntegral_eq_sum_of_subordinatePartition`;
* `hasLeadingTerm_boltzmannIntegral_of_partition_productChartsV`;
* `boltzmannIntegral_isEquivalent_of_partition_productChartsV_extremal`;
* `tendsto_posteriorExpectation_of_partition_productChartsV`.

**Positivity trap:** a partition does not automatically make a chart attaining the candidate extremal pair contribute positively. Require the appropriate dominant-face positivity witness, or prove it separately from geometric compatibility of the cover. For residual faces, positivity on a positive-measure portion of the relevant face is the operative condition.

Also, if an extremal coefficient vanishes, do not simply discard that chart and promote the next pair: a zero leading coefficient only gives an \(o\)-statement at the old scale, not a sufficiently strong remainder at the next scale.

There is no need to audit/rework all twelve `R.weight` modules for this route. Later, if chart-level transport with arbitrary allocations becomes useful in its own right, (A) can still be added independently.

## Q2. Residual formula first; regression second

**Yes, worth doing—but first add the chart-data residual formula.**

CCLVII and CCLXII already provide good evidence for the analytic engine. The missing theorem of independent value is the elimination of the chosen atlas from the residual coefficient formula. That is the variable-unit analogue of the useful part of CCLI.

The next generic theorem should turn `IsVarPieceAtlasData` into a formula directly in terms of:

* the original piece amplitude;
* the phase restricted to the dominant normal face;
* the base weight;
* residual sign classes and residual monomial powers.

Schematically, if \(J\) denotes the minimal normal coordinates and \(L\) the residual ones, its integrand should have the shape
\[
\beta(z)\,
A(z,0_J,\tau r)\,
V(z,0_J,\tau r)^{-\lambda}
\prod_{\ell\in L}r_\ell^{h_\ell-\lambda m_\ell},
\]
summed over residual signs \(\tau\), integrated over the inherited base/residual domain, and multiplied by the **existing CCLVI prefactor**, including \(2^{|J|}\).

Here \(V\) is the positive coefficient phase—your `varPhase`, including its tangential factor—not the whole phase containing the vanishing normal monomial.

Two safeguards:

1. **Restrict to the face; do not freeze all normal coordinates.**  
   In general,
   \[
   V(z,0_J,\tau r)\ne V(z,0).
   \]
   This is exactly why the frozen-cell argument is not the residual theorem.

2. **Keep CCLVI’s domain and normalisation verbatim.**  
   Avoid introducing a second convention for signs, radii, Gamma factors, or factorials in the chart bridge.

Then add an “inner/universal tied stratum” corollary analogous to `productCoeffD_eq_of_inner`. The example should only identify the face and evaluate its integral.

For
\[
K(x,y)=(1+x^2+y^2)x^2y^4,
\]
the minimal normal coordinate is \(y\), and the residual face is \(y=0\). The resulting factor is precisely
\[
|x|^{-1/2}(1+x^2)^{-1/4}.
\]
That makes
\[
Z_N[1]\sim \Gamma(1/4)I\,N^{-1/4}
\]
an especially good regression: it catches the incorrect replacement of the residual face unit by its value at the full normal origin.

## Q3. Add the stronger free-energy asymptotic, not just \(O(1)\)

Given
\[
Z_N\sim C\,N^{-\lambda}(\log N)^k,\qquad C>0,
\]
the cheap generic consequences are:

### Two-sided bounds

Eventually,
\[
\frac C2\,N^{-\lambda}(\log N)^k
\leq Z_N\leq
2C\,N^{-\lambda}(\log N)^k.
\]

Equivalently, the scaled ratio is eventually between \(C/2\) and \(2C\). This supplies the requested \(\Theta\) statement, and also eventual strict positivity of \(Z_N\).

### Free energy, including the constant

The stronger conclusion is
\[
\boxed{
-\log Z_N
=
\lambda\log N-k\log\log N-\log C+o(1).
}
\]
In limit form,
\[
-\log Z_N-\lambda\log N+k\log\log N
\longrightarrow-\log C.
\]

This immediately implies the \(O(1)\) form. In Lean, isolate the eventual region \(N>1\), establish positivity, and take logarithms of the positive scaled ratio.

I would prove these **once for the generic positive-coefficient leading-term/equivalence interface**, then expose thin wrappers for:

* the scalar product-cover theorem;
* the variable-unit product-cover theorem;
* the new supplied-partition theorem.

This connects the small-ball and cover programmes through a shared asymptotic lemma rather than another parallel free-energy development.

It is important to label the result correctly: the \(o(1)\) free-energy correction is a consequence of the leading equivalent, **not** a subleading expansion or a quantitative remainder rate.

## Q4. Recommended next five units

| Order | Unit | Principal new content |
|---|---|---|
| 1 | Supplied-partition localisation | Precise masked decomposition; relative-subordination wrapper; bounded-prior construction |
| 2 | Supplied-partition variable assembly | Signed leading term, positive equivalent, posterior ratio via one-chart packages |
| 3 | Generic positive-leading consequences | Two-sided bounds and free-energy limit with constant; cover wrappers |
| 4 | Variable residual chart formula | `IsVarPieceAtlasData` residual face formula; inner-stratum coefficient corollary |
| 5 | Residual end-to-end example | \((1+x^2+y^2)x^2y^4\), preferably including a genuinely informative posterior |

If units 1–2 fit naturally into one module, move the residual work forward. Do not inflate the decomposition layer merely to fill a unit.

### A better posterior example

Rather than adding a separate tied-square example with limit \(F(0,0)\), use the residual regression itself. It has a non-atomic limiting distribution along \(y=0\):
\[
\mathbb E_N[F]\longrightarrow
\frac{
\displaystyle\int_{-1}^{1}
F(x,0)\,|x|^{-1/2}(1+x^2)^{-1/4}\,dx
}{
\displaystyle\int_{-1}^{1}
|x|^{-1/2}(1+x^2)^{-1/4}\,dx
}.
\]

For example,
\[
\boxed{
\mathbb E_N[x^2]\longrightarrow
\frac{\displaystyle\int_0^1x^{3/2}(1+x^2)^{-1/4}\,dx}
     {\displaystyle\int_0^1x^{-1/2}(1+x^2)^{-1/4}\,dx}
\in(0,1).
}
\]

That is substantially more informative than \(\mathbb E_N[e^x]\to1\) for the tied square. It simultaneously demonstrates:

* a genuinely normal-dependent unit;
* a residual dominant face;
* a nontrivial limiting observable;
* the unit’s effect on the limiting posterior density.

Use the library’s usual bounded extension of the observable if the global interface requires one.

### Beyond these units

The next major target should be **a conditional localisation constructor from suitable resolution data to product-package data**, not a subleading expansion. Start with a precise statement of the extra neighbourhood, carrier, product-domain, and regular-partition hypotheses that make the constructor possible. R3 solves the allocation-weight obstruction; it does not by itself solve the geometric domain obstruction.

Subleading terms remain a separate analytic programme requiring stronger regularity and remainder control. Nothing in the completed general-unit theorem should be stretched to suggest those estimates are already implicit.

**Bottom line:** land R3 by finite localisation, extract the cheap but strong free-energy consequences, and then make the residual chart formula earn its keep through one combined normaliser/posterior regression.
