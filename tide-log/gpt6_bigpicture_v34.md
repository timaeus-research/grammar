## Recommendation: GO on A3, with a new cap and a hard unit-3 gate

A1–A2 is a clean release boundary and should remain one. But the completed estimates make **conditional tangential integration and finite assembly a well-justified next tranche**, not a speculative extension. The missing work is chiefly integration, function-space continuity, and finite spectral bookkeeping.

Authorize **12–16 units, hard cap 18**, with:
- **Review after unit 3:** deterministic tangential theorem and stochastic statement/type gate.
- **Review after unit 8:** integrated stochastic theorem, or a precise explanation of what remains.
- **Final review:** finite assembly and an explicit audit of the external decomposition assumptions.

Do **not** include resolution geometry, derivation from Hypothesis I, Gaussian identification, or posterior division in this budget.

The intended new headline should be:

> **The stochastic Taylor tree after tangential integration and finite chart assembly, conditional on joint convergence of chart data in compact-tangential weighted-ℓ¹ function spaces and an external chart decomposition with negligible residual.**

This is stronger than XXXV, but still not an unconditional formalisation of the paper’s global theorem.

---

## 1. Deterministic `lemma:AsymInt`: use two layers

Your proposed inequality is correct. I recommend a **small measure-theoretic core**, with **`C(K, DataSpace)` as the public stochastic interface**.

### Layer 1: integration of a uniformly controlled family

Let \((K,\nu)\) be a finite measure space, let \(E=\mathrm{DataSpace}(n+1)\), and suppose
\[
x:K\to E,\qquad \|x(v)\|\le R\quad\text{a.e.}
\]
with sufficient measurability—`AEStronglyMeasurable x ν` is a convenient robust hypothesis.

Write
\[
\mathcal Z_N(x)=\int_K Z(N;x(v))\,d\nu(v),\qquad
\mathcal C_{\mu,j}(x)=\int_K C_{\mu,j}(x(v))\,d\nu(v).
\]

For \(R\ge0\), under the existing cutoff hypotheses,
\[
\begin{aligned}
\left|\mathcal Z_N(x)
-\sum_{\mu\in\Lambda_L}N^{-\mu}
       \sum_{j\le n}\mathcal C_{\mu,j}(x)(\log N)^j\right|
\le {}&
\nu(K)\,b^{|h|+d}\operatorname{dataCutoffConst}(R)\\
&\cdot(Nb^{2|k|})^{-L}
 (1+\log(Nb^{2|k|}))^n .
\end{aligned}
\]
Here \(\nu(K)\) denotes the finite real mass, e.g. `(ν Set.univ).toReal`.

Prove integrability explicitly before manipulating Bochner integrals. The continuity and ballwise bounds already supply it for the real-valued integrands.

For ordered remainders, the particularly useful interface is
\[
\left|\mathcal R_N^{\mu,j}(x)-\mathcal C_{\mu,j}(x)\right|
\le \nu(K)\,\operatorname{remainderMajorant}(\ldots,R,N),
\]
where \(\mathcal R\) is defined from \(\mathcal Z\) and the integrated predecessor coefficients. The proof uses the identity
\[
\mathcal R_N^{\mu,j}(x)-\mathcal C_{\mu,j}(x)
=
\int_K\bigl(R_N^{\mu,j}(x(v))-C_{\mu,j}(x(v))\bigr)\,d\nu(v).
\]

Export this identity at meaningful normalization thresholds, as well as the estimate.

**No infinite series interchange is needed.** Integrate the finite-cutoff estimate, then normalize. That is the right replacement for the paper’s unstated `lemma:AsymInt`.

### Layer 2: compact continuous tangential data

Take \(K\) compact metrizable, with a finite Borel measure, and define
\[
T=C(K,E)
\]
with the sup norm. Then evaluation gives \(\|x(v)\|\le\|x\|_\infty\), and
\[
|\mathcal C_{\mu,j}(x)-\mathcal C_{\mu,j}(y)|
\le \nu(K)\,L_{\mu,j}(R)\|x-y\|_\infty
\]
on the radius-\(R\) ball. The integrated \(Z(N;\cdot)\) has the analogous estimate for fixed \(N\ge0\).

Thus both maps are continuous and Borel measurable, and the integrated remainder converges uniformly on sup-norm balls.

**Recommendation:** prove the measure-theoretic wrapper without building a general \(L^\infty\)-data theory. An \(L^\infty\) stochastic interface introduces equivalence classes and potentially nonseparable spaces without helping the immediate target. An \(L^p\) hypothesis alone would not control the nonlinear phase dependence.

This is a sufficient, honest version of `AsymInt`; it is not a claim to recover an absent source statement in maximal generality.

---

## 2. Phase, amplitude, and the missing partition weight

Yes: use one map
\[
v\longmapsto \bigl(c_\xi(v),c_\eta(v)\bigr)\in E_b\times E_b.
\]
Allow both entries to vary in the abstract theorem. Deterministic amplitude is a specialization of the random data model, not a reason to build a separate theory.

The paper has a genuine notational omission: its displayed integrated coefficients drop \(\rho_I\). Formalise one of the following conventions and use it consistently:

1. **Absorb \(\rho_I(v)\) into the amplitude.** This is my preferred convention:
   \[
   \eta_I(u,v)=\rho_I(v)\phi(\pi_I(u,v))c_I(u,v),
   \]
   with the normal monomial factors recorded separately in \(h_I\).

2. Keep \(\rho_I\) explicit in every coefficient integral, or use the positive weighted measure \(\rho_I\,dv\) when \(\rho_I\ge0\).

Do not absorb it into \(\eta\) and also weight the measure.

Absorption into the amplitude is harmless for normal Taylor coefficients because \(\rho_I\) depends only on \(v\). It also accommodates signed observables without introducing signed measures.

For noncompact strata, take a compact tangential domain containing the support and use the restricted measure. Compact support alone is **not** the domination argument: the weighted-ℓ¹ tangential data must be continuous or otherwise measurably bounded there.

In particular, do not infer
\[
v\mapsto(c_\xi(v),c_\eta(v))\in C(K,E_b\times E_b)
\]
merely from pointwise analyticity in \(u\). That function-space regularity remains an explicit assumption until separately proved.

---

## 3. Stochastic tangential theorem: your proposed shape is right

Assume measurable random elements
\[
X_\ell:\Omega_\ell\to T,\qquad X_\ell\Rightarrow X,
\]
and deterministic sample sizes \(N_\ell\ge0\), \(N_\ell\to\infty\). Using \(\ell\) as sequence index avoids confusing it with normal dimension or sample size.

Then the deliverables should exactly parallel XXXV:

1. Every finite integrated coefficient vector converges in distribution:
   \[
   \bigl(\mathcal C_{\mu_i,j_i}(X_\ell)\bigr)_i
   \Rightarrow
   \bigl(\mathcal C_{\mu_i,j_i}(X)\bigr)_i.
   \]

2. Every finite vector of integrated ordered-remainder errors tends to zero in probability:
   \[
   \bigl(\mathcal R_{N_\ell}^{\mu_i,j_i}(X_\ell)
          -\mathcal C_{\mu_i,j_i}(X_\ell)\bigr)_i
   \xrightarrow{p}0.
   \]

3. Consequently, the remainder vector converges jointly in distribution to the limiting coefficient vector.

The proof is the existing architecture:
- continuous mapping;
- boundedness in probability of \(\|X_\ell\|_\infty\);
- uniform error estimates on sup-norm balls;
- Slutsky.

### Implementation cautions

- **Measurability of the integral functional:** prove its ballwise Lipschitz bound, hence continuity, hence Borel measurability. Do not make parameterized-integral measurability the critical path.
- **Borel structure:** explicitly arrange the Borel measurable-space instance on `C(K,E)` and test the probability theorem signatures early.
- **Polishness:** mathematically, \(C(K,E)\) is Polish for compact metrizable \(K\) and separable Banach \(E\); your countable-index ℓ¹ data space qualifies. Merely saying “compact” without metrizability would not justify this claim.
- **Local compactness:** it is not mathematically needed. In particular, norm-boundedness in probability comes from applying weak convergence to the real-valued norm—not from compactness of Banach-space balls.
- **Mathlib:** verify the exact instances needed by the existing probability lemmas in the first unit. I would not assume repository-specific typeclass compatibility without that test.

No pathwise convergence in \(v\), Skorokhod representation, or stochastic dominated-convergence theorem is required.

---

## 4. Finite chart assembly: dependent product, not sigma type or padding

Choose **a new generic finite-assembly interface, reusing generic lemmas from the old assembly files where possible**.

For a finite chart index type \(\mathcal I\), let
\[
T_I=C(K_I,\mathrm{DataSpace}(d_I)),\qquad
T_{\mathrm{all}}=\prod_{I\in\mathcal I}T_I.
\]

In Lean this is a dependent function type, schematically
```lean
∀ I, TangentialData I
```
—not `Σ I, TangentialData I`. A sigma type selects one chart; assembly needs all charts simultaneously.

Do not pad to a common normal dimension. Dummy normal variables introduce avoidable questions about exponents, integration factors, and coefficient compatibility.

### Separate the analytic wrapper from the algebra

The assembly kernel should consume:
- chart integrals;
- chart coefficient maps;
- locally finite spectral index sets or finite cutoffs;
- coefficient continuity/bounds;
- uniform cutoff bounds.

It need not know the internal weighted-ℓ¹ representation. Instantiate it with the tangential results.

If the existing d=2 results already have this abstract shape, generalize/reuse them. If they only assemble a leading exponent and log multiplicity, they are not enough for the full ordered tree.

### Common spectral bookkeeping

Use the union of chart exponent sets, with zero coefficients outside each chart’s support, and
\[
D=\max_I(d_I-1)
\]
as the common log-degree bound. Set chart coefficients to zero for \(j>d_I-1\).

A common rational lattice \(Q^{-1}\mathbb N\), using a common multiple of chart denominators, is an acceptable implementation device. Distinguish it from the actual support: it may contain additional zero-coefficient slots.

Define
\[
C^{\mathrm{all}}_{\mu,j}(x)
=\sum_I\mathcal C^I_{\mu,j}(x_I),
\]
with the existing ordering
\[
(\nu,q)\prec(\mu,j)
\iff \nu<\mu\ \lor\ (\nu=\mu\land q>j).
\]

**Important:** do not simply invoke each chart’s ordered-remainder theorem at a global target. The target may not belong to that chart’s lattice, and the global log degree may exceed its native range. The safest construction is:

1. integrate each chart’s cutoff theorem;
2. sum those cutoff theorems at one cutoff \(L>\mu\);
3. regroup onto the common finite index set;
4. prove the global normalized-remainder bound.

Prove the required support/zero-padding lemmas explicitly. Cancellation between chart coefficients is allowed; the full tree theorem does not assert that its earliest candidate coefficient is nonzero.

### Joint stochastic input is indispensable

Require
\[
X_\ell\Rightarrow X\quad\text{in }T_{\mathrm{all}}.
\]
Separate marginal convergence chart by chart does not suffice. Independence is neither required nor generally appropriate.

### External decomposition and its residual

Write the external identity as
\[
Z_\ell^{\mathrm{global}}
=\sum_I\mathcal Z^I_{N_\ell}(X_{\ell,I})+E_\ell,
\]
with measurable quantities and equality almost surely if that is the natural formulation.

For a target \((\mu,j)\), the exact residual requirement is
\[
\frac{E_\ell}
 {N_\ell^{-\mu}(\log N_\ell)^j}
\xrightarrow{p}0.
\]

For the whole tree, quantify this over every admissible target. For a finite-vector theorem, only those finitely many targets are necessary.

A convenient sufficient condition is
\[
e^{\varepsilon N_\ell}E_\ell\xrightarrow{p}0
\]
for some \(\varepsilon>0\). Another is negligibility at every positive polynomial scale. Export a lemma turning such a condition into all needed normalized-scale conditions.

Be careful about the source’s exponential claim: a bound
\[
|E_\ell|\le e^{-cN_\ell}O_p(1)
\]
gives exponential little-\(o_p\) at any smaller positive rate, not automatically at rate \(c\).

The external identity is where partition weights, Jacobians, overlap handling, tangential restrictions, and the away-from-minimum contribution must be accounted for. An abstract assembly theorem can assume that identity; it cannot certify the geometry behind it.

---

## 5. A4: a small honest quotient theorem exists, but defer its implementation

The statement gate should use **normalized integrals**, not just leading coefficient convergence.

Let
\[
a_\ell=N_\ell^{-\mu_0}(\log N_\ell)^{j_0},
\]
and assume jointly
\[
\left(
\frac{Z_\ell[\phi]}{a_\ell},
\frac{Z_\ell[1]}{a_\ell}
\right)
\Rightarrow (A,B),
\qquad \mathbb P(B=0)=0.
\]
Then
\[
\frac{Z_\ell[\phi]}{Z_\ell[1]}\Rightarrow \frac AB,
\]
using a measurable convention at finite-sample zero denominators, or an eventual-a.s. nonzero hypothesis if the intended posterior must literally be defined.

To derive this from tree coefficients, require
\[
Z_\ell[\phi]/a_\ell-C^\phi_{\mu_0,j_0}(X_\ell)\xrightarrow p0,
\quad
Z_\ell[1]/a_\ell-C^1_{\mu_0,j_0}(X_\ell)\xrightarrow p0.
\]
Thus all preceding contributions must vanish or be negligible at that scale. **Joint convergence of the two coefficients alone is insufficient.**

Defer:
- deriving the common leading scale;
- proving denominator positivity/nonvanishing from geometry;
- resolving chart cancellation;
- higher-order quotient expansions and their joint remainder control;
- expectation convergence or uniform integrability.

Budget this later as roughly **2–4 units after a statement gate**, subject to the available almost-sure continuous-mapping/division API. Do not let it consume A3’s cap.

---

## 6. First three units and stop criteria

### u278 — Statement lock and function-space feasibility
Deliver:
- compact-tangential data type;
- definitions of integrated integral, coefficient, and ordered remainder;
- explicit partition-weight convention;
- minimal measurable/AE-bounded deterministic interface;
- a compiling check of the intended `C(K,E)` stochastic hypotheses and existing probability interfaces.

Also record the finite-assembly joint-data and residual statements, without implementing them.

### u279 — Integrability, finite-cutoff integration, continuity
Deliver:
- integrability of all relevant integrands;
- the integrated cutoff estimate;
- ballwise Lipschitz continuity of integrated coefficients and fixed-\(N\) integrals.

### u280 — Integrated ordered remainder and hard review
Deliver:
- normalized-remainder/integral identity;
- explicit integrated majorant;
- uniform convergence on sup-norm balls;
- finite-vector version if routine.

**Pass gate:** a genuine deterministic `AsymInt` theorem, with explicit domination and weight handling, plus a viable stochastic function-space interface.

**Stop or rescope at unit 3 if:**
- domination is being inferred from compact support alone;
- weighted-ℓ¹ tangential continuity is being silently inferred from pointwise analyticity;
- the stochastic interface needs a substantial new probability/function-space infrastructure project;
- the public theorem has become too geometry-heavy to retain a clean conditional statement.

Suggested remaining allocation:

| Work | Units |
|---|---:|
| First-three-unit gate | 3 |
| Integrated stochastic tree and joint vectors | 2–3 |
| Generic finite spectral assembly | 3–4 |
| Joint stochastic assembly and residual transfer | 2–3 |
| Interfaces, audits, review repairs | 2–3 |
| **Total** | **12–16** |

If assembly stalls, release the integrated one-stratum theorem rather than weakening its hypotheses or overstating its scope. At the hard cap, freeze at the last reviewed boundary.

**Bottom line:** proceed. The right A3 is a controlled extension of the existing uniform-on-balls machinery—not an attempt to fill all of the paper’s geometric and empirical-process gaps at once.
