## 1. Fidelity check

**DCLXIII–DCLXIV match the recursion described**, with one correction to the commentary about low depths.

- **(a) Truncation and factors are correct.** Hasse derivatives vanish above `P.natDegree`, including for `P = 0`. The flat contribution is
  \[
  \frac2s\cdot\frac{\operatorname{primZero}P}{2}
  =\frac1s\operatorname{primZero}P,
  \]
  the correction contribution is \((2/s)\sum_j2^jJ_jH_jP\), and the residual contribution is \(2Q/s\).
- **(b) No depth hypothesis is needed.** But **do not describe the low-depth premises as false/vacuous**. Under the usual Gaussian normalization, depth one already has a constant asymptotic polynomial; depth zero can have the zero polynomial with an exponentially small remainder. The unconditional scalar recursion is the correct justification.
- **(c) The dummy values are fine**, provided public claims about `enginePoly` retain `2 ≤ L`. In particular, do not advertise its successor recursion without that guard.
- **(d) \(K_2=2/s\) is correct:** for \(\ell\ge0\),
  \[
  \ell+\log2+3\le4(1+\ell).
  \]
  Keep straight whether the displayed bound concerns \(Z_2-P_2/\sqrt N\) or \(\sqrt N Z_2-P_2\); multiplication by \(\sqrt N\) supplies the stated `HasPolyRate` bound.

## 2. Ranking and next deliverables

**Ranking: (d) > (a) > (f) > (e) > (b) > (c).**

My next day-sized target is **uniqueness, then the structural coefficient API and exact degree/leading coefficient**. Treat second/third-coefficient consistency as a stretch goal rather than making the whole of (a) one acceptance gate.

### First: (d), canonicality of the engine

Proposed interface:

```lean
theorem polynomial_eq_zero_of_tendsto_eval_zero
    {P : ℝ[X]}
    (h : Tendsto (fun x : ℝ => P.eval x) atTop (𝓝 0)) :
    P = 0

theorem HasPolyRate.unique
    {L : ℕ} {P R : ℝ[X]}
    (hP : HasPolyRate L P) (hR : HasPolyRate L R) :
    P = R

theorem HasPolyRate.eq_enginePoly
    {L : ℕ} (hL : 2 ≤ L) {P : ℝ[X]}
    (hP : HasPolyRate L P) :
    P = enginePoly L
```

**Proof route:** put \(N=e^t\), \(t\ge0\). Then
\[
|(P-R)(t)|\le(K_P+K_R)(1+t)e^{-t/2}\longrightarrow0.
\]
A nonzero constant cannot tend to zero; a positive-degree real polynomial has absolute value tending to infinity.

For later Mellin identification, an even more useful public theorem is:

```lean
theorem eq_enginePoly_of_tendsto_sub
    {L : ℕ} (hL : 2 ≤ L) {P : ℝ[X]}
    (hP : Tendsto
      (fun N : ℝ =>
        Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N))
      atTop (𝓝 0)) :
    P = enginePoly L
```

This requires only an **\(o(1)\) normalized remainder** from the Mellin argument, not reproduction of the engine’s quantitative rate.

**Mathlib-name caution:** I would not promise an exact `Polynomial.eq_zero_of_...` or polynomial-limit lemma without checking the pinned Mathlib. Make the first theorem above your stable local wrapper. Search the polynomial asymptotics API for `tendsto`, `leadingCoeff`, and `norm`; the mathematical proof is independent of which existing limit lemma is available.

### Second: (a), coefficients and degree

Avoid the `k - 1`/division-by-zero presentation. Publish separate zero and successor formulas:

```lean
theorem coeff_stepPoly_zero (P : ℝ[X]) (Q : ℝ) :
    (stepPoly P Q).coeff 0 =
      (2 / s) *
        ((∑ j ∈ range (P.natDegree + 1),
          2 ^ j * gaussJlogPow j * P.coeff j) + Q)

theorem coeff_stepPoly_succ (P : ℝ[X]) (Q : ℝ) (k : ℕ) :
    (stepPoly P Q).coeff (k + 1) =
      P.coeff k / (s * (k + 1 : ℝ)) +
      (2 / s) *
        ∑ j ∈ range (P.natDegree + 1),
          2 ^ j * gaussJlogPow j *
            ((k + 1 + j).choose j : ℝ) *
              P.coeff (k + 1 + j)
```

Here `s` abbreviates `Real.sqrt (2 * Real.pi)`.

Supporting and acceptance interfaces:

```lean
theorem coeff_primZero_succ (P : ℝ[X]) (k : ℕ) :
    (primZero P).coeff (k + 1) = P.coeff k / (k + 1 : ℝ)

theorem natDegree_primZero {P : ℝ[X]} (hP : P ≠ 0) :
    (primZero P).natDegree = P.natDegree + 1

theorem natDegree_stepPoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ) :
    (stepPoly P Q).natDegree = P.natDegree + 1

theorem coeff_enginePoly_top (L : ℕ) (hL : 2 ≤ L) :
    (enginePoly L).coeff (L - 1) =
      1 / ((Nat.factorial (L - 1) : ℝ) * s ^ (L - 1))

theorem natDegree_enginePoly (L : ℕ) (hL : 2 ≤ L) :
    (enginePoly L).natDegree = L - 1
```

**Expected Mathlib name:** `Polynomial.coeff_hasseDeriv`. Its content is
\[
(H_jP).\mathrm{coeff}\,k=\binom{k+j}{j}P.\mathrm{coeff}(k+j),
\]
possibly presented with natural scalar multiplication and reordered addition. Verify its argument order locally.

**There cannot be a pre-existing Mathlib `natDegree_primZero` for this project-defined primitive.** Prove that local lemma from its coefficient formula, then show the Hasse sum and constant have degree at most `P.natDegree`. Useful expected names are `Polynomial.coeff_eq_zero_of_natDegree_lt` and `Polynomial.natDegree_le_iff_coeff_eq_zero`.

For the next two coefficients:

- \(B_L\): seed at depth two;
- \(C_L\): seed at depth three;
- thereafter their successor coefficients have positive index, so **the new residual mass contributes nothing**.

Thus they need only the appropriate low Gaussian log moments, not evaluation of further \(Q_L\).

### Remaining choices

- **(f):** highest-value analytic follow-up, but define the normalization of `G_r` before stating a bridge. A formal generating-series identity alone does **not** identify the residual constants without an analytic bridge or a jet asymptotic.
- **(e):** good separate NB deliverable. **I cannot verify the exact weight from equation labels alone**, since their contents are not supplied. If `nb_surrogate` is precisely \(Nz^2/(2V)\), up to a \(z\)-independent term, then indeed
  \[
  w(z)=e^{-Nz^2/(2V)},\qquad
  \mathbb E_{\rm sur}[z\mid\lambda]
  =\frac{\int z\,w(z)\rho(\lambda,z)\,dz}
         {\int w(z)\rho(\lambda,z)\,dz}.
  \]
  The factor \(m(\lambda)^{-1}\) cancels. Prove denominator positivity and weighted integrability; do not substitute this for DCLXI’s unweighted mean.
- **(b):** include it essentially for free in (a).
- **(c):** defer unless quantitative evaluation is needed. Your displayed recurrence is correct for the tracked witnesses, but an “explicit” \(K_L\) remains partly existential until `Cd` and the coefficient constants are chosen explicitly. No uniform-in-depth claim follows.

## 3. Convention hazards

1. **Normalization:** `enginePoly L` approximates **\(\sqrt N Z_L(N)\)** at argument `log N`, not \(Z_L\), and not at `log √N`.
2. **Hasse versus ordinary derivatives:** \(H_jP=P^{(j)}/j!\). The factor \(2^j\) is already present; add neither another factorial nor another power of two.
3. **Moment aliases:** add simp bridges for `gaussJlogPow 1/2/3` to the existing named moments, after checking their definitions. Also name the zeroth-moment bridge.
4. **Residual indexing:** `residualMass L P_L` is \(Q_L\), but the legacy name describes the **destination depth**: `residualMass_two = depthThreeQint`, etc.
5. **Zero polynomial:** exact degree growth needs `P ≠ 0`; the step theorem itself does not.
6. **Numerics versus identification:** the checks strongly support the Mellin identification, but the current formal result is the **canonical integral-defined polynomial**, once uniqueness is added—not yet its all-depth closed zeta-coefficient formula.