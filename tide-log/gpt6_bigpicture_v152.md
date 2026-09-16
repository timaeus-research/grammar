The main correction is in **3(a)**: the displayed uniform estimate gives **\(O_P\), not \(o_P\), at its own cutoff rate**. Also, a fixed stochastic jet order \(R\) supports only the cutoffs whose required deterministic derivative orders are at most \(R\).

My implementation priority would be **1 → 2 → 4 → 3 → 5**, with 4 kept small. Formalise **(a) and then (b), with corrected rates**; defer (c) and the leading-constant identification.

All new Lean declarations below are **schematic statement shapes**, not claims about existing declaration names.

## 1. Add bounded-jet uniformity, not continuity of the remainder constant

Your proposed lemma is the right interface. For fixed \(\eta,p,b\), prove

```lean
theorem fieldJetBound_of_jetBoundOn
    (hη : ContDiff ℝ ∞ η)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ζ, ContDiff ℝ ∞ ζ →
        JetBoundOn p (closedBox d b) ζ B →
        FieldJetBound η ζ p b C B
```

Here `JetBoundOn` must include the **zeroth derivative**. Otherwise the exponential factor `exp (B * τ)` is not justified.

A useful stronger version exports a fixed constant \(A\), depending only on \(\eta,p,b\), such that one can use
\[
C(B)=A(1+B)^{|p|},\qquad B\ge0.
\]
A larger polynomial is equally acceptable.

### Proof route

First audit `exists_pdMulti_fieldFam_bound`. If its proof constructs its constants from finitely many suprema of derivatives, generalise that proof rather than duplicate it. The essential issue is the quantifier order:
\[
\forall\zeta\;\exists C_\zeta
\quad\not\Rightarrow\quad
\forall B\;\exists C_B\;\forall\zeta\text{ with bounded jets}.
\]

If that audit is awkward, a direct induction/Leibniz–Faà-di-Bruno proof is appropriate:
\[
\partial^m(\eta e^{\tau\zeta})
=e^{\tau\zeta}
 \sum \text{constant}\cdot\partial^a\eta
       \prod_{\ell=1}^{r}(\tau\,\partial^{b_\ell}\zeta),
\qquad r\le |m|\le |p|.
\]
On the box, bound this by a fixed constant times
\[
(1+B)^{|p|}(1+\tau)^{|p|}e^{B\tau}.
\]

Compactness and smoothness bound the finitely many derivatives of fixed \(\eta\).

### Best downstream wrapper

After exact dilation, export a rectangle lemma saying that for every jet radius \(B\), there is a **single remainder constant for the entire jet ball**:

```lean
theorem empRect_remainder_uniform_on_jetBall
    ...
    (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ζ, ContDiff ℝ ∞ ζ →
        JetBoundOn pRequired (closedBox d b) ζ B →
        ∀ N : ℝ, 1 ≤ N →
          |empIntegralRect η ζ h k b N -
              absSpectralSum (Qamb k) (d - 1)
                (empCoeffRect η ζ h k b) U N|
            ≤ K * (N ^ (-U) * (1 + Real.log N) ^ (d - 1))
```

This consumes `emp_cutoffExpansion_uniform` and dilation. It hides all the bookkeeping involving \(C\), \(K_0(U,B)\), and derivative rescaling.

**No continuity of \(B\mapsto K(B)\) is needed.** In particular, the existing theorem only gives existential \(K_0(U,B)\); do not silently treat that choice as continuous or monotone.

---

## 2. Tightness gives bounded norms; localisation is the clean assembly

Let \(E\) be the normed jet space and \(\nu_n=\mathbb P\circ Y_n^{-1}\). The useful probability-bound interface is:

```lean
∀ ε : ℝ, 0 < ε →
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ n, ℙ {ω | B < ‖Y n ω‖} ≤ ENNReal.ofReal ε
```

An eventual-in-\(n\) version suffices for \(O_P(1)\) and convergence in probability.

### From tightness

Consume:

- measurability of `Y n`;
- tightness of the family of pushforward probability measures;
- compact sets in a normed space are bounded;
- the measure-map identity for the measurable norm-tail set.

For each \(\varepsilon>0\), choose compact \(K\) with
\[
\nu_n(K^c)\le\varepsilon\quad\text{for all }n.
\]
Choose \(B\ge0\) with \(K\subseteq\{x:\|x\|\le B\}\). Then
\[
\{\|Y_n\|>B\}\subseteq\{Y_n\notin K\}.
\]

I would add a small bridge lemma with the displayed interface rather than expose Mathlib’s particular `IsTightMeasureSet` formulation throughout the remainder proof. The exact existing declaration names should be checked in the repository.

### Remainder assembly

If
\[
|\mathrm{Rem}_n|\le K_B a_n
\quad\text{on }\{\|Y_n\|\le B\},
\]
then for any deterministic \(s_n\) with \(|s_n|a_n\to0\),
\[
s_n\mathrm{Rem}_n\longrightarrow0
\quad\text{in probability}.
\]

Indeed, after choosing \(B\), eventually \(K_B|s_n|a_n\le\delta\), so
\[
\mathbb P(|s_n\mathrm{Rem}_n|>\delta)
\le\mathbb P(\|Y_n\|>B)\le\varepsilon.
\]

This **localised jet-ball argument** avoids constructing a monotone constant function entirely.

Your `tendstoInMeasure_zero_of_tight_bound` is also appropriate. To meet its monotonicity hypothesis, choose constants on integer balls and replace them by finite running maxima:
\[
\widehat K(B)=\max_{0\le j\le\lceil B\rceil}K_j.
\]
Continuity is unnecessary.

### Jet-order restriction

For cutoff \(U\), set
\[
p_U=\operatorname{depthOf}\bigl(h,k,
       \max(\lceil U\rceil_+,L_0(h))\bigr).
\]
You need the stochastic jet space to control all derivatives used by `FieldJetBound`; a sufficient condition is
\[
|p_U|\le R,
\]
with the corresponding dilation/reconstruction bounds.

**\(R\ge\texttt{cubeOrder}\) alone is not enough for arbitrary \(U\).** A.s. smoothness does not give tightness of higher derivatives.

---

## 3. The honest stochastic expansions

Write \(S_U(n,\zeta)\) for the canonical spectral sum with cutoff \(U\).

### (a) Chart expansion: yes, but correct the rate

The direct conclusion is
\[
n^U(1+\log n)^{-(d-1)}
  \bigl[I_n-S_U(n,\zeta_n)\bigr]=O_P(1).
\]

It does **not** generally converge to zero. For example, if the lattice contains \(U\), an omitted term
\[
a_U(\zeta_n)n^{-U}(\log n)^{d-1}
\]
survives at that normalisation.

The clean little-\(o_P\) statement is: for \(A<U\),
\[
n^A(1+\log n)^{-(d-1)}
  \bigl[I_n-S_U(n,\zeta_n)\bigr]\longrightarrow0
\]
in probability.

Schematic shape:

```lean
theorem chart_remainder_tendstoInMeasure
    (hAU : A < U)
    (horder : requiredOrder h k U ≤ R)
    (hjets : TightJetFamily ℙ jetR)
    (hsmooth : ∀ n, ∀ᵐ ω ∂ℙ, ContDiff ℝ ∞ (ζ n ω))
    ... :
    TendstoInMeasure ℙ
      (fun n ω =>
        (n : ℝ) ^ A *
          (1 + Real.log (n : ℝ)) ^ (-(d - 1 : ℝ)) *
          (empIntegralRect η (ζ n ω) h k b n -
            absSpectralSum (Qamb k) (d - 1)
              (empCoeffRect η (ζ n ω) h k b) U n))
      atTop (fun _ => 0)
```

Use \(n+1\), positive naturals, or eventual \(n\ge1\) to avoid distracting endpoint issues.

You can combine this with `jointChartTopCoeffLaw`: **the expansion has canonical random coefficients, and selected top coefficients have the established joint law**. No law for all coefficients is asserted.

**Additional interface to check:** measurability/a.e. measurability of the lower random coefficients and the spectral sum. Smoothness of every sample alone does not establish this. If their definitions use parameterised integrals, prove measurable dependence separately; continuity is not required. Do not smuggle this in through the top-coefficient law.

### A useful alternative convention

If you want a little-\(o_P\) remainder at a named exponent \(A\), retain **all lattice terms with \(\mu\le A\)** and prove the bound using a cutoff \(U>A\) lying before the next lattice point. This is a closed-cutoff expansion, not the strict-cutoff statement in your question.

It still requires enough stochastic derivative control for the proof cutoff \(U\).

### (b) Total evidence: yes; the tail is super-polynomially small in probability

Assuming the stated bound, \(\beta>0\), \(\varepsilon>0\), and fixed finite \(A\), on \(\{|M_n|\le B\}\),
\[
|T_n|\le A e^{\beta B^2/2}e^{-n\beta\varepsilon/2}.
\]
Thus, for every real \(a\),
\[
n^aT_n\longrightarrow0
\quad\text{in probability}.
\]
The same holds after any fixed logarithmic factor.

The cheapest implementation is a generalisation of the proof of `TailData.tendstoZero`, consuming:

- `M_n = O_p(1)`;
- the exponential tail inequality;
- deterministic polynomial-times-exponential decay;
- `tendstoInMeasure_zero_of_tight_bound`.

If only the leading-scale convergence were available, deeper decay would not follow. It follows here from the **stronger explicit inequality**.

For finitely many charts, choose \(U_\alpha>A\), with each required order supported by \(R\). Then
\[
n^A\left[
E_n-\sum_\alpha S_{\alpha,U_\alpha}(n,\zeta_{\alpha,n})
\right]\longrightarrow0
\]
in probability: the positive exponent gap absorbs all finite logarithmic powers.

This version avoids forcing a common chart dimension/log normalisation. Consume `ae_totalEvidence_eq`, the chart remainder theorems, finite-sum stability, and the strengthened tail lemma.

### (c) Evidence subleading law: defer

Your present tools do not generally identify the law of an evidence residual after subtracting only a leading term.

The precise requirement is not necessarily **laws** for all preceding coefficients:

- if you subtract all preceding coefficients **exactly as random variables**, their laws are unnecessary;
- if they are not subtracted, you need vanishing/negligibility;
- if you replace them by approximations, you need approximation errors at the target scale.

You then need the target coefficient’s law and a negligible remainder.

As for `DeepVanishing`, if indeed
\[
\mathrm{deepSet}(c')\subseteq\mathrm{deepSet}(c)
\quad(c'\ge c),
\]
the monotonicity lemma should be straightforward:

```lean
theorem DeepVanishing.mono
    (hη : DeepVanishing η b c) (hcc' : c ≤ c') :
    DeepVanishing η b c'
```

But this only helps at the **higher vanishing levels**. It does not recover lower log coefficients. Moreover, the assertion “at every \(\mu\), degrees \(\ge c\) vanish” must be checked against the actual coefficient-vanishing theorem and its index-dependent hypotheses; set nesting alone does not establish it.

---

## 4. Lattice alignment: mask unless support has actually been proved

From the statement of `CutoffExpansion` alone, coefficients off the lattice are **unconstrained**. Changing them arbitrarily leaves every spectral sum unchanged.

Therefore I cannot conclude from the supplied declarations that `empCoeffRect` is definitionally zero there. Audit:

1. `empCoeff`;
2. `scaleCoeff`;
3. any existing coefficient-support theorem.

Even if the desired zero is true, it may be theorem-level rather than definitional.

For a common denominator \(Q\), choose \(Q_\alpha\mid Q\), for example the finite lcm. Define

```lean
noncomputable def totalCoeff (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ α, if OnChartLattice α μ then chartCoeff α μ j else 0
```

Use the actual lattice convention, including whether zero is included. If chart log-degree bounds differ, also zero-extend in `j`.

Then prove a **finite-sum reindexing identity**:
\[
\sum_\alpha S_{\alpha,U}
=
S_{Q,D,U}(c_{\mathrm{total}}),
\]
where \(D\) dominates the chart degree bounds.

For the first total-evidence theorem, it is simpler to leave the expression as a sum of chart spectral sums. Common-lattice assembly is a presentation layer, not a prerequisite for the stochastic estimate.

---

## 5. Leading-constant identification: park the full proof, audit the factorial now

The proposed route is sound, subject to these checks.

1. **Fluctuation functions.** Integrand equality and `integral_congr` should suffice, once domains, real-power conventions, and argument signs agree. The substitution \(\zeta=-G\) makes the sign check important.

2. **Weight identity.** On strictly positive coordinates, use real-power product/addition identities:
   \[
   \prod_j y_j^{h'_j-2\lambda k'_j}
   =
   \left(\prod_j |y_j|^{h'_j}\right)
   \left(\prod_j y_j^{2k'_j}\right)^{-\lambda}.
   \]
   Boundary zeros should be removed a.e., not handled by unrestricted `rpow` algebra.

3. **Residue set.** Prove the essential-index equivalence and cardinality first. This controls both the coordinate map and the factorial.

4. **Coordinate permutation.** Prove the pointwise compatibility
   \[
   \operatorname{glue}(J,0,w)
   =
   \operatorname{splitCoords}(e,(0,y))
   \]
   under your chosen reindexing. This catches inverse-equivalence mistakes before measure theory. Use the available volume-preserving finite-product permutation theorem; verify its actual name and direction locally.

5. **Open versus half-open boxes.** Coordinate boundary hyperplanes have volume zero. The box replacement is therefore an a.e. integral equality; it does not require boundary integrability separately.

### The factorial is a real red flag

If
\[
q=\mathrm{multCount}=r+2,
\]
then
\[
(q-1)!=(r+1)!,
\]
**not \(r!\)**.

If the two candidate formulas literally contain these different factorials without another compensating factor, they are not equal. Check whether one formula is a residue, a log coefficient, or a differentiated quantity. Do not leave this as final simplification.

Also, the displayed \(b\)-power cancellation holds when the sums run over the \(q\) essential coordinates satisfying \(h_i+1=2k_i\lambda\); it does not remove arbitrary nonessential-coordinate dependence.

## Recommended deliverables

1. Bounded-jet uniform `FieldJetBound`.
2. Rectangle remainder uniform on jet balls.
3. Tight jet family ⇒ uniform norm-tail bounds.
4. Chart remainder: \(O_P\) at cutoff rate, \(o_P\) at every slower rate, **with an explicit required-order hypothesis**.
5. Super-polynomial tail decay and total-evidence assembly.
6. Optional common-lattice reindexing.
7. Later: lower-coefficient theory and constant identification.

The two blockers to claiming “a full expansion to every order” now are **finite available jet order** and **the exact-cutoff \(O_P\)/\(o_P\) distinction**, not the Gaussian top-coefficient law.