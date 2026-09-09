## Recommendation: a 24-unit Programme Q, with stop gates

**Proceed with N1 first, N3 second, and a tightly limited version of N2 third.** Include N4 as a small, independent deliverable. Do not reopen resolution, and do not let N2 turn into differentiated all-orders asymptotics.

The principal mathematical addition should be:

> **For an assembled population normal form, either there is a first nonzero coefficient, which gives an asymptotic equivalent, or all coefficients vanish and the function is superpolynomially small—provided expansions are available to arbitrary cutoffs.**

This resolves the cancellation branch left open by Programme P without pretending that nonvanishing is automatic.

### Ranking and budget

Budgets below include public wrappers, documentation, and regressions—not just the central lemma.

| Rank | Item | Budget | Decision and gate |
|---|---|---:|---|
| 1 | **N1: selection after cancellation; flat alternative** | **6** | GO. First verify cutoff compatibility and predecessor completeness. Do not assume the whole pair order is well-founded. |
| 2 | **N3: analytic-family → `TangentialData`** | **8** | GO, conditionally on a common complex neighbourhood, a strict radius gap, and uniform boundary control. No construction of the tangential cutoff. |
| 3 | **N2: exact energy identity + universal first log correction** | **7** | GO with Route B for the correction. Gate after two units: exhibit the coefficient recurrence and the precise two-term remainder requirement. |
| 4 | **N4: arbitrary positive box size** | **3** | GO. Exact dilation first, coefficient transport second. |
| 5 | **N8: zero-noise continuity of coefficients** | **2** | Reserve only; substitute for work stopped at a gate. Deterministic continuity first, not a new empirical-expansion theorem. |
| 6 | **N5: general-dimensional parity** | **4–5** | Defer from Q. Useful, but less urgent than admissibility and cancellation. |
| 7 | **N6: conditional wall-crossing** | **0–1** | Fold in as a corollary if genuinely immediate. No standalone programme or headline. |
| 8 | **N7: all-orders division** | **0** | Still NO-GO without a specified asymptotic algebra and remainder convention. Two-term quotient algebra is allowed. |

**Hard cap: 24 new units.** N1 + N3 + N2 + N4 exhaust that cap. If a gate fails, ship the honest partial result and use remaining capacity for N8; do not borrow beyond 24.

Review checkpoints:

1. N1 complete.
2. N3 complete.
3. N2 gate decision.
4. Release audit, including N4 and any substitutions.

Unit counts are ceilings, not invitations to split trivial lemmas into separate modules.

---

## 1. N1: what exactly to prove

### The essential distinction

There are three different assertions:

1. **Finite selection:** a nonempty finite collection of nonzero coefficients has a first pair.
2. **Global validity:** that selected pair has no nonzero predecessor in the entire admissible coefficient domain.
3. **Asymptotics:** the frozen target theorem applies to that pair.

Only the first is pure finite-order theory. The second needs an explicit bridge from `indexSet D Q L` to the global admissible domain.

In particular:

- `precedes` is **not** well-founded on all of `ℝ × ℕ`.
- Even at one exponent, unrestricted descending log degree prevents that argument.
- A finite cutoff works because it must contain **every admissible predecessor of the selected target**.
- Use a cutoff **strictly above the target exponent**, unless the actual boundary convention has already been proved adequate.
- If coefficients are represented through cutoff-dependent objects, first prove their compatibility. “The coefficients ought to be the same” is not an interface.

### Public deliverables

I would require these four mathematical outputs:

1. First-nonzero selection from a nonzero coefficient below some cutoff.
2. Independence of the selected pair from enlarging the cutoff.
3. The corresponding asymptotic equivalent, specialized to the assembled population integral.
4. Flatness:
   \[
   \bigl(\forall p\text{ admissible},\ C_p=0\bigr)
   \Longrightarrow
   \forall L\in\mathbb R,\quad \mathcal Z_{\rm pop}=o(N^{-L}).
   \]

For the fourth, require expansions at arbitrarily large cutoffs. A single cutoff does not suffice. If the available remainder is only \(O(N^{-H}(\log N)^r)\), choose \(H>L\); do not mislabel that bound as little‑\(o\) at \(H\).

The flat branch does **not** imply exact zero. Exponentially small, nonzero functions are the basic regression against that overclaim.

---

## 2. First three units: Lean-level contracts

One qualification matters here: the extraction does not provide the actual types or argument order of `D`, `Q`, `gCoeff`, `CutoffExpansion`, or `isEquivalent_normalForm_pop`. I cannot honestly give certified drop-in declarations using those constants.

Below are **exact abstract-layer theorem headers**. Bind the local `precedes` to the existing relation and the local `gCoeff` to the assembled coefficient function. The adapter is a source-check task, not permission to change the mathematical statement. The snippets are headers, not proposed `axiom` declarations.

I use real exponents and real coefficients below; confirm that representation at the adapter boundary.

```lean
abbrev PopPair := ℝ × ℕ

variable
  (precedes : PopPair → PopPair → Prop)
  (gCoeff : PopPair → ℝ)
```

### Q1 / provisional u306 — finite first-nonzero selection

```lean
theorem exists_first_nonzero_finset
    (S : Finset PopPair)
    (horder :
      ∀ p q, precedes p q ↔
        p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2))
    (hne : ∃ p ∈ S, gCoeff p ≠ 0) :
    ∃ p ∈ S,
      gCoeff p ≠ 0 ∧
      ∀ q ∈ S, precedes q p → gCoeff q = 0
```

**Instantiation:** `S := indexSet D Q L`, with the actual coefficient function curried to a pair.

Prove this classically on the finite nonzero support. Prefer reusing finite-order machinery; do not install a global order instance on coefficient pairs just for this theorem.

**Regression:** at fixed \(\mu\), the larger \(j\) wins. This catches the most consequential orientation error.

### Q2 / provisional u307 — lift to the global domain and prove uniqueness

Let `A` denote the actual global admissible pair domain, not all pairs unless coefficients have explicitly been extended by zero.

```lean
theorem existsUnique_first_nonzero_of_cutoff
    (A : Set PopPair)
    (S : Finset PopPair)
    (horder :
      ∀ p q, precedes p q ↔
        p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2))
    (hSA : ∀ p ∈ S, p ∈ A)
    (hclosed :
      ∀ p ∈ S, ∀ q ∈ A,
        precedes q p → q ∈ S)
    (hne : ∃ p ∈ S, gCoeff p ≠ 0) :
    ∃! p : PopPair,
      p ∈ A ∧
      gCoeff p ≠ 0 ∧
      ∀ q ∈ A, precedes q p → gCoeff q = 0
```

The substantive seabed work in this unit is proving `hclosed` for the chosen cutoff interface.

Also export cutoff coherence: any two cutoff selections satisfying this contract agree. That follows from global uniqueness; it should not require a second selection algorithm.

**Gate:** if `indexSet D Q L` omits admissible predecessors because of a boundary or truncation convention, fix the adapter or enlarge the cutoff. Do not weaken “first nonzero” to “first among the terms we happened to retain.”

### Q3 / provisional u308 — selected-target asymptotics

The abstract selection-to-asymptotics contract is:

```lean
theorem existsUnique_first_nonzero_isEquivalent
    (A : Set PopPair)
    (S : Finset PopPair)
    (Z : ℝ → ℝ)
    (horder :
      ∀ p q, precedes p q ↔
        p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2))
    (hSA : ∀ p ∈ S, p ∈ A)
    (hclosed :
      ∀ p ∈ S, ∀ q ∈ A,
        precedes q p → q ∈ S)
    (hne : ∃ p ∈ S, gCoeff p ≠ 0)
    (h_target :
      ∀ p ∈ A,
        gCoeff p ≠ 0 →
        (∀ q ∈ A, precedes q p → gCoeff q = 0) →
        Asymptotics.IsEquivalent Filter.atTop Z
          (fun N : ℝ =>
            gCoeff p * Real.rpow N (-p.1) *
              (Real.log N) ^ p.2)) :
    ∃! p : PopPair,
      p ∈ A ∧
      gCoeff p ≠ 0 ∧
      (∀ q ∈ A, precedes q p → gCoeff q = 0) ∧
      Asymptotics.IsEquivalent Filter.atTop Z
        (fun N : ℝ =>
          gCoeff p * Real.rpow N (-p.1) *
            (Real.log N) ^ p.2)
```

**The callback theorem alone does not count as completion of this unit.** Its public specialization must discharge `h_target` using `isEquivalent_normalForm_pop`, through the existing `predSet`/`absPredSum` interface, and retain every actual `CutoffExpansion` hypothesis.

For a chart, specialize `Z` to

```lean
fun N =>
  origPhaseIntegral n h k β N 1 (fun _ => 0) η
```

For the assembled result, use the existing assembled integral and its decomposition hypotheses.

**Important assembled gate:** an error term negligible at Programme P’s first candidate need not be negligible at the post-cancellation target. The new theorem must require the decomposition error to be negligible at the selected scale—or have an all-cutoff error hypothesis. This is the main extra issue I would add to your N1 description.

The remaining N1 units cover arbitrary-cutoff flatness, the assembled/error wrappers, and cancellation/flatness regressions.

---

## 3. N3: close the functional-analytic bridge, not the geometric assertion

This is worth doing now. It turns a substantial class of paper hypotheses into the actual `TangentialData` interface.

Use the following input package:

- a common polydisc centred at the normal origin;
- joint continuity on the parameter space times a closed Cauchy polydisc;
- holomorphy in the normal variables on an open neighbourhood of that closed polydisc;
- a uniform bound \(M\) there;
- a strict gap between the DataSpace weight radius \(b\) and Cauchy radius \(r\);
- the necessary reality condition for the real amplitude interface.

Then
\[
|c_\gamma(v)|\le M r^{-|\gamma|},
\qquad
b^{|\gamma|}|c_\gamma(v)|
   \le M(b/r)^{|\gamma|}.
\]

The sum of the latter majorant over multi-indices is finite. Combine:

1. coefficientwise continuity from `CircleOpParam`;
2. a uniform summable majorant;
3. finite-head/uniform-tail control;

to obtain continuity into weighted \(\ell^1\).

### Eight-unit ceiling

A reasonable decomposition is:

- generic weighted-\(\ell^1\) continuity criterion;
- continuity of Cauchy coefficients;
- uniform multi-index geometric majorant;
- continuous coefficient-family map;
- reconstruction/agreement with the original analytic amplitude;
- zero-noise `ofFamilies`/`TangentialData` wrapper;
- multiplication by a continuous tangential factor;
- public integral bridge and regressions.

**Reconstruction is essential.** A continuous sequence-valued map alone does not establish that its associated box amplitude is the supplied \(F_v\).

For \(\rho(v)c(v,u)(\phi\circ\pi)(v,u)\), this programme proves admissibility **when those analytic-family and cutoff hypotheses are supplied**. It does not prove that a subordinate partition can be chosen constant in normal directions. Compactness may give the uniform bound from joint continuity, but it does not supply a common holomorphic neighbourhood out of nothing.

---

## 4. N2: Route B, and only the universal first log correction

### Exact identity: GO independently

Prove, for \(N>0\),
\[
Z_K(N)=-\frac1\beta Z'(N),
\]
where \(K\circ\pi=u^{2k}\) and the two integrals use the same amplitude.

On the positive unit box, the phase monomial is bounded. Local differentiation under the integral should therefore require only the appropriate absolute integrability of the weighted amplitude, not full analyticity.

Use a neighbourhood of a fixed \(N_0>0\). Do not accidentally claim a two-sided derivative at \(N=0\) from this argument.

### Correction: Route B is the honest cheaper route

Do **not** differentiate a `CutoffExpansion` merely because it holds for every \(N\). Neither an asymptotic remainder bound nor an exact pointwise series identity provides derivative control by itself.

Target the coefficient identity, with \(j\ge1\):
\[
A_K=\frac{\lambda}{\beta}A,
\qquad
B_K=\frac{\lambda B-jA}{\beta},
\]
where
\[
\begin{aligned}
Z(N)&=N^{-\lambda}
 \bigl(A(\log N)^j+B(\log N)^{j-1}
       +o((\log N)^{j-1})\bigr),\\
Z_K(N)&=N^{-\lambda-1}
 \bigl(A_K(\log N)^j+B_K(\log N)^{j-1}
       +o((\log N)^{j-1})\bigr).
\end{aligned}
\]

Derive the second identity from the shifted-weight coefficient formula and the required moment recurrence/integration by parts. The displayed `q = j+1` contribution in your description is a route into that calculation, not by itself the entire coefficient.

Then two-term division gives, for \(A\ne0\),
\[
\frac{Z_K(N)}{Z(N)}
=
\frac{\lambda}{\beta N}
-\frac{j}{\beta N\log N}
+o\!\left(\frac1{N\log N}\right).
\]

This is precisely the intended correction when \(\beta=1\) and \(j=m-1\).

Treat \(j=0\) separately: the statement becomes
\[
Z_K/Z=\lambda/(\beta N)+o(1/(N\log N)),
\]
**if** the available expansion and coefficient support establish that stronger remainder. Do not introduce a negative log-degree coefficient into the polynomial-log interface.

### Stop gate

After two units, require:

- the exact moment/coefficient recurrence has been identified;
- all contributions to \(B_K\) are accounted for;
- the two required little‑\(o\) expansions can be obtained without differentiating remainders.

If not, release the exact identity and stop N2 there.

**Do not replace this target with general \(\phi\) two-term division.** For general \(\phi\), “the second term” requires selecting among log corrections and later exponents and handling cancellations. The energy observable has a special universal cancellation of \(B\); exploit it.

Assembled energy correction is optional within the seven units, and needs appropriately stronger control of both decomposition errors. Programme P’s leading-order assembled error hypotheses are not automatically sufficient.

---

## 5. N4 and the reserves

### N4: exact dilation, then binomial transport

For \(b>0\), put
\[
H=\sum_i h_i+d,\qquad K=\sum_i k_i.
\]
Here \(d\) is the actual number of coordinates—not an assumed interpretation of the Lean dimension index.

Prove
\[
Z_b(N)=b^H Z_1(Nb^{2K};\,\eta(b\,\cdot)).
\]

A term \(C(\mu,j)N^{-\mu}(\log N)^j\) transports using
\[
b^{H-2K\mu}C(\mu,j)
 \bigl(\log N+2K\log b\bigr)^j.
\]

Your top-log formula follows. Lower-log coefficients require the full binomial sum over higher log degrees at the same exponent. Include the admissibility of the rescaled amplitude; dilation can consume the available analytic-radius margin.

### N8: useful, but label it narrowly

Prove continuity of population specialization and:
\[
X_a\to0 \quad\Longrightarrow\quad
C_{\mu,j}(X_a)\to C_{\mu,j}(0)
\]
in the actual data topology.

This is not yet convergence of whole asymptotic expansions: that additionally needs uniform remainder control. Nor does usual normalized empirical noise necessarily converge to zero; it can have a nondegenerate limit.

### N5 and N6

For parity, use reflection-invariant phase **and the absolute-density convention**. With \(|u|^h\), amplitude parity is the relevant parity; with a signed \(u^h\) integrand, it is not interchangeable.

For wall-crossing, prove only local constancy of the selected pair where its coefficient stays nonzero and all predecessors vanish throughout the parameter neighbourhood. Continuity alone does not make predecessor vanishing persist.

---

## 6. Release labels and non-claims

Use labels that describe the actual scope:

- **First-nonzero selection for assembled population normal forms**
- **Superpolynomial flatness under all-cutoff coefficient vanishing**
- **Uniform analytic-family admissibility on a common polydisc**
- **Exact chart energy derivative identity**
- **First logarithmic energy correction under two-term expansion hypotheses**
- **Positive-box dilation and coefficient transport**

Avoid “full §3,” “full expectation expansion,” “RLCT theorem,” and “empirical-to-population theorem.”

The release non-claims should explicitly retain:

1. No resolution, atlas, or change-of-variables construction.
2. No construction of a normally constant subordinate partition.
3. No identification of the selected exponent with the model’s RLCT.
4. No automatic nonzero coefficient after cancellation.
5. No exact-zero conclusion from coefficient flatness.
6. No post-cancellation assembled asymptotic without adequate decomposition-error control.
7. No termwise differentiation of asymptotic remainders.
8. No all-orders inverse-log division.
9. No general-observable second-term theorem from the energy calculation.
10. No stochastic expansion limit from coefficient continuity alone.

**Bottom line:** close cancellation and analytic admissibility first. Then obtain the energy correction through coefficient algebra, not a differentiated remainder. That is a substantial, bounded continuation of §3 while keeping the deferred geometry genuinely out of scope.
