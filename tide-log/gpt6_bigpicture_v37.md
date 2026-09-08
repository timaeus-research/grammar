## Decision

**GO for a staged, conditional population theorem. NO-GO for declaring the present geometric §3 theorem proved.**

Your proposed direction is substantially right, but five corrections are load-bearing:

1. **After absorbing \(u^l\) into the weight, the leading face functional is applied to \(\eta'\), not to \(u^l\eta'\).**
2. **A smooth partition of unity does not supply the analytic amplitude hypotheses of `thm_TaylorTree`.** This is a separate gap from geometric change of variables.
3. **The leading coefficient lives on the minimal-ratio face**, not generally at the deepest corner or solely on the named stratum.
4. **Cancellation can lower the logarithmic degree without changing the exponent.** Vanishing of the proposed leading coefficient does not imply a strictly larger exponent.
5. **Wall-crossing is not determined by divisor orders alone**, and continuity in a parameter does not establish the stated piecewise-constant claim.

I recommend a replacement headed **“Population expansions from admissible normal-form data”**, followed by a conditional application to a resolution. Use chart indices, not intrinsically defined per-stratum contributions, at this stage.

I have not inspected or compiled against the repository. The programme below uses the supplied interfaces; source-level names and argument order must be checked before admitting units.

---

# 1. Replacement statement for the authors

The following is suitable for the staging note. It deliberately separates analysis from geometry.

## Theorem A — Population expansion from normal-form data

Let \(\mathcal A\) be a finite family of normal-form charts. For each \(\alpha\in\mathcal A\), let:

- \((T_\alpha,\nu_\alpha)\) be a compact parameter space with a finite positive measure;
- \(d_\alpha\geq1\), \(k_{\alpha i}\in\mathbb N_{>0}\), \(h_{\alpha i},l_{\alpha i}\in\mathbb N\);
- \(b_\alpha>0\);
- \(\eta_\alpha(v,u)=u^{l_\alpha}\psi_\alpha(v,u)\), for
  \(u\in[0,b_\alpha]^{d_\alpha}\).

Assume that the normal-variable Taylor coefficients of \(\psi_\alpha(v,\cdot)\), scaled to the box, form a continuous family in the weighted-\(\ell^1\) coefficient space used in the Taylor-tree theorem. In particular, it suffices to have holomorphic extensions to a common larger normal polydisc, with the continuity and uniform bounds needed for this coefficient-space hypothesis.

For fixed \(\beta>0\), set
\[
Z_{\alpha,n}
 =
 \int_{T_\alpha}\int_{[0,b_\alpha]^{d_\alpha}}
 u^{h_\alpha+l_\alpha}
 e^{-\beta n u^{2k_\alpha}}
 \psi_\alpha(v,u)\,du\,d\nu_\alpha(v).
\]

Suppose the population partition function under consideration satisfies
\[
\mathcal Z_{\beta,n}[\phi]
 =\sum_{\alpha\in\mathcal A}Z_{\alpha,n}+R_n,
 \qquad R_n=O(e^{-\epsilon n})
\]
for some \(\epsilon>0\).

Then:

### (a) Expansion and support

Each chart contribution has an expansion
\[
Z_{\alpha,n}
 \sim
 \sum_{\mu\in\Lambda(h_\alpha+l_\alpha,k_\alpha)}
 n^{-\mu}
 \sum_{j=0}^{d_\alpha-1}
 C_{\alpha,\mu,j}(\phi)(\log n)^j,
\]
where
\[
\Lambda(H,k)
 =
 \bigcup_i
 \left\{\frac{H_i+1+r}{2k_i}:r\in\mathbb N\right\}.
\]

The expansion has the cutoff remainder supplied by the population specialisation of the Taylor-tree theorem, and hence satisfies the paper’s ordered asymptotic convention.

The global coefficients are
\[
C_{\mu,j}(\phi)=\sum_\alpha C_{\alpha,\mu,j}(\phi),
\]
with missing chart coefficients interpreted as zero. The exponential residual contributes no coefficients.

These are **candidate supports**. Membership in the support set does not assert that the corresponding coefficient is nonzero.

### (b) Population coefficient formula

The chart coefficients are obtained by specialising the Taylor-tree coefficient formula to \(\xi=0\). Only fluctuation order \(p=0\) remains.

On the unit box, writing
\[
\psi_\alpha(v,u)=\sum_\gamma a_{\alpha,\gamma}(v)u^\gamma
\]
with \(a_{\alpha,\gamma}\) the normalised Taylor coefficients, the coefficient functional is
\[
C_{\alpha,\mu,j}
 =
 \int_{T_\alpha}
 K_{k_\alpha}\sum_\gamma
 a_{\alpha,\gamma}(v)
 S_0(\mu,j;\gamma)\,d\nu_\alpha(v),
\]
using the state kernels for weight \(h_\alpha+l_\alpha\). The series has the absolute convergence established by the Taylor-tree theorem.

For a general box, coefficients are those obtained after the existing box rescaling, including the translation of \(\log n\). One must not identify the coefficients before and after that translation without the appropriate binomial transformation.

Here
\[
\operatorname{fluctMoment}(\beta,0,0,\mu,r)
 =
 \int_0^\infty
 t^{\mu-1}(-\log t)^r e^{-\beta t}\,dt,
\]
and, for \(\mu>0\),
\[
\operatorname{fluctMoment}(\beta,0,0,\mu,0)
 =\Gamma(\mu)\beta^{-\mu}.
\]

Calling the higher moments Gamma derivatives is legitimate once differentiation under this Mellin integral has been justified; it is not needed for the initial formalisation.

### (c) First candidate and its coefficient

Write
\[
H_{\alpha i}=h_{\alpha i}+l_{\alpha i},\qquad
\mu_\alpha=\min_i\frac{H_{\alpha i}+1}{2k_{\alpha i}},
\]
\[
J_\alpha
 =\left\{i:\frac{H_{\alpha i}+1}{2k_{\alpha i}}=\mu_\alpha\right\},
 \qquad m_\alpha=|J_\alpha|.
\]

Let \(P_{J_\alpha}u\) set the coordinates in \(J_\alpha\) to zero. Then
\[
\frac{Z_{\alpha,n}}
 {n^{-\mu_\alpha}(\log n)^{m_\alpha-1}}
 \longrightarrow A_\alpha,
\]
where
\[
\boxed{
A_\alpha=
\frac{\Gamma(\mu_\alpha)\beta^{-\mu_\alpha}}
     {(m_\alpha-1)!}
\left(\prod_{i\in J_\alpha}\frac1{2k_{\alpha i}}\right)
\int_{T_\alpha}
\int_{[0,b_\alpha]^{J_\alpha^c}}
\psi_\alpha(v,P_{J_\alpha}u)
\prod_{i\notin J_\alpha}
u_i^{H_{\alpha i}-2k_{\alpha i}\mu_\alpha}
\,du\,d\nu_\alpha(v).
}
\]

All residual exponents exceed \(-1\), so the displayed weight is integrable.

In particular,
\[
C_{\alpha,\mu_\alpha,m_\alpha-1}=A_\alpha,
\]
and there are no terms at smaller exponents or at exponent \(\mu_\alpha\) with larger logarithmic degree.

If \(A_\alpha\neq0\), this is the actual leading term. Otherwise the expansion determines subsequent terms; the next nonzero term may have the **same exponent and a smaller logarithmic degree**.

A sufficient positivity condition is that the face amplitude is nonnegative almost everywhere and positive on a set of positive weighted product measure. For continuous amplitudes, “positive at one point” suffices only with the relevant support condition on the tangential measure and the face domain.

### (d) Global leading term

Let
\[
\mu_*=\min_\alpha\mu_\alpha,\qquad
m_*=\max_{\alpha:\mu_\alpha=\mu_*}m_\alpha,
\]
and
\[
A_*=
\sum_{\alpha:\mu_\alpha=\mu_*,\,m_\alpha=m_*}A_\alpha.
\]

Then
\[
\frac{\mathcal Z_{\beta,n}[\phi]}
 {n^{-\mu_*}(\log n)^{m_*-1}}
 \longrightarrow A_*.
\]

If \(A_*\neq0\), this gives the leading asymptotic equivalence. If it vanishes, the actual leading term must be found from the first nonzero **assembled coefficient**, ordered by increasing exponent and decreasing logarithmic degree.

The theorem does not assert that such a nonzero coefficient exists for every signed observable.

---

## Important corrections to your proposed face formula

For
\[
\eta=u^l\eta',
\]
there are two equivalent integral presentations:
\[
u^h\eta=u^{h+l}\eta'.
\]

Applying Headline VIII to the second presentation gives the shifted face functional with:

- weight \(H=h+l\);
- minimal set computed from \(H\);
- amplitude **\(\eta'\)**.

Using \((u^l\eta')(P_Ju)\) after shifting the weight would count the vanishing twice and often make a genuinely nonzero coefficient appear zero.

For the all-minimal case, the formula reduces to
\[
A_\alpha=
\frac{\Gamma(\mu_\alpha)\beta^{-\mu_\alpha}}
 {(m_\alpha-1)!}
\prod_i\frac1{2k_{\alpha i}}
\int_{T_\alpha}\psi_\alpha(v,0)\,d\nu_\alpha(v).
\]

Only in this case is evaluation at the deepest corner the general answer.

---

# 2. Replacement for §3.6

## Corollary B — Leading population expectations

Suppose the denominator and numerator have actual nonzero leading terms
\[
\mathcal Z_n[1]\sim
C\,n^{-\lambda}(\log n)^{m-1},
\qquad C>0,
\]
\[
\mathcal Z_n[\phi]\sim
C_\phi\,n^{-\mu}(\log n)^{r-1},
\qquad C_\phi\neq0.
\]

Then the denominator is eventually positive and
\[
E_n[\phi]\sim
\frac{C_\phi}{C}\,
n^{-(\mu-\lambda)}(\log n)^{r-m}.
\]

Consequently:

- \(\mu=\lambda,\ r=m\): \(E_n[\phi]\to C_\phi/C\);
- \(\mu=\lambda,\ r<m\): logarithmic decay;
- \(\mu>\lambda\): power decay, with the displayed logarithmic modifier.

These are classifications of **actual leading pairs**, not classifications derived solely from divisor orders.

For a genuine posterior expectation with bounded \(\phi\),
\[
|\mathcal Z_n[\phi]|
 \leq \|\phi\|_\infty\mathcal Z_n[1].
\]
Thus, if a nonzero numerator leading pair exists, it cannot predict growth beyond the denominator scale: \(\mu<\lambda\), or \(\mu=\lambda,r>m\), is excluded. This exclusion uses the common positive underlying integral, not merely two unrelated abstract expansions.

If every numerator coefficient vanishes, this corollary does not assign a nonzero leading equivalent.

### Wall-crossing

**Remove the present conclusion as a theorem.**

Replace it by:

> Along a parameterised family, candidate supports may change when available monomial factors change. Actual leading pairs may also change when assembled coefficient functionals vanish, even when divisor orders remain unchanged. Local stability of a specified leading pair requires nonvanishing of its coefficient and control of all predecessor coefficients.

A continuous parameter family alone gives no useful piecewise-constant stratification theorem. An analytic finite-dimensional parameter programme would need its own hypotheses and proof.

---

# 3. What “vanishing order” should mean here

For the formal theorem, use:

\[
\eta(v,u)=u^l\psi(v,u)
\]
with \(\psi\) satisfying the stated analytic coefficient-family assumptions.

Call \(l\) an **admissible monomial factor**. It need not be the maximal factor.

For an analytic amplitude, this is equivalent locally to Taylor support
\[
a_\gamma(v)=0\quad\text{whenever }\gamma\not\geq l,
\]
provided the analytic division and parameter regularity are established.

Do not make generic divisorial orders part of the first Lean interface. The implication
\[
\operatorname{ord}_{E_i}(\phi\circ\pi)\geq l_i
\quad\Longrightarrow\quad
\phi\circ\pi=u^l\psi
\]
belongs to the geometric/analytic bridge.

Also distinguish raw derivatives from normalised Taylor coefficients. If
\(a_\gamma=\partial^\gamma\eta(0)/\gamma!\), do not introduce another \(\gamma!\) in the coefficient formula.

---

# 4. Geometry, smooth cutoffs, and parity

## Steps 1–3 must currently remain hypotheses

They could eventually be replaced by a genuine geometric theorem, but **not by merely relabelling the present Steps 1–3 as a lemma**.

Two independent obligations remain:

1. **Geometric decomposition:** change of variables, localisation, finite charts, measures, overlaps and cutoffs.
2. **Analytic admissibility:** the resulting chart amplitudes belong to the class covered by the expansion theorem.

The second is especially important. A smooth cutoff \(\kappa(v,u)\) generally destroys analyticity in \(u\). A nontrivial analytic bump function cannot repair this.

Accordingly:

> `thm:TaylorTree` at \(\xi=0\) proves the analytic normal-form population theorem. It does not, by itself, prove the population theorem for arbitrary smooth localisation amplitudes produced by a resolution.

There are legitimate future routes:

- a smooth-amplitude population expansion theorem;
- a carefully proved face-adapted decomposition preserving the required normal analyticity;
- another analytic argument with explicit uniform remainder estimates.

None should be silently included in the present release.

## Ordinary normal Taylor truncation is not an asymptotic truncation

The paper’s assertion about discarding the normal Taylor remainder needs substantial repair.

For example,
\[
K(x,y)=x^2y^2,\qquad h=(0,2),
\]
has \(\lambda=1/2\) with minimal set \(J=\{x\}\). Every amplitude monomial \(y^r\) retains exponent \(1/2\). Arbitrarily high total Taylor degree can therefore contribute to the leading coefficient.

Even with equal initial ratios, shifting one coordinate may reduce multiplicity while retaining the same exponent.

Thus:

> A finite total-degree Taylor polynomial does not generally determine the expansion to an arbitrary prescribed power of \(n^{-1}\).

The absolutely convergent dressed coefficient series is the correct replacement. The Taylor tree is not justification for the naive finite Taylor truncation stated in §3.

## Parity

For the bare density
\[
u^\gamma|u|^h e^{-n u^{2k}}
\]
on a symmetric interval, oddness is controlled by **\(\gamma\)**, not \(h+\gamma\).

Moreover, an arbitrary amplitude or cutoff can destroy that bare parity cancellation. One must apply parity to the full expanded amplitude.

For the first theorem and Lean release:

- state explicitly that normal boxes are one-sided;
- allow signed charts only through supplied one-sided normal-form data;
- make no new multidimensional parity theorem claim.

Splitting an interior chart into orthants is conceptually available, but the transformed amplitudes and resulting coefficient cancellations must be accounted for. It is not justified by importing the paper’s parity sentence unchanged.

## Coordinate-free material

Retain, if desired, as **interpretation after the analytic theorem**:

- normal jets relative to a chosen sufficiently regular tubular identification;
- contraction with normal moment tensors;
- invariance under linear changes of the split normal frame.

Do not claim independence from the tubular identification. Linear frame invariance does not establish that.

Remove the coordinate-free infinite expansion from the main theorem until its precise jet convention, measures and asymptotic meaning are supplied.

---

# 5. Formalisation programme

## Scope and budget

Authorise a **20-unit hard cap**, not an open-ended §3 programme.

| Work package | Units | Decision |
|---|---:|---|
| P1: zero-noise specialisation, coefficient collapse, Gamma moment, leading-coefficient identification | 5 | GO |
| P2: monomial shift, shifted support, shifted face functional, positivity | 4 | GO |
| P3: deterministic tangential/global expansion and negligible residual | 3 | GO; reuse |
| P4: quotient and bounded-observable compatibility | 2 | GO; reuse |
| P5: \(K\)-observable shift, chart and conditional finite assembly | 2 | GO |
| Regression/cancellation examples and hypothesis audit | 2 | Required |
| Final headline and author-note/interface audit | 2 | Required |

These are reviewable theorem units, not a demand for twenty new modules. Prefer extending existing interfaces over parallel infrastructure.

**Reviews:** after units 3, 5, 9, 12, 16 and 20.  
**First gate:** approve the corrected mathematical staging note before proceeding beyond unit 3.

If numbering continues from 289, the first three are provisionally u290–u292.

---

## First three Lean-level targets

These are exact mathematical target signatures in the supplied vocabulary, **not claimed compiled declarations**. Check source argument order and namespace placement before committing them.

### u290 — Population Taylor tree on the original integral

```lean
theorem population_TaylorTree_taylor
    (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β)
    {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ}
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b),
      (Fη (fun i => (u i : ℂ))).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b
        (taylorFamily (n + 1)
          (fun _ : (Fin (n + 1) → ℂ) => (0 : ℂ)))
        (taylorFamily (n + 1) Fη) C ∧
      ∀ N,
        familyPhaseIntegralBox n h k β N b
          (taylorFamily (n + 1)
            (fun _ : (Fin (n + 1) → ℂ) => (0 : ℂ)))
          (taylorFamily (n + 1) Fη)
        =
        origPhaseIntegral n h k β N b
          (fun _ => 0) η
```

Proof: instantiate `thm_TaylorTree_taylor` with the constant-zero holomorphic function.

Required companion simplification:
```lean
taylorFamily (n + 1) (fun _ => (0 : ℂ)) = 0
```

**Acceptance:** the theorem exposes the original population integral, not only the family integral. Preserve the complete existing remainder conclusion.

### u291 — Collapse of the population outer coefficient series

```lean
theorem familyCoeffSeries_population
    (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β)
    (cη : CoeffFamily (n + 1))
    (μ : ℝ) (hμ : 0 < μ) (j : ℕ) :
    familyCoeffSeries n h k β
      (0 : CoeffFamily (n + 1)) cη μ j
    =
    familyCoeffTerm n h k β
      (0 : CoeffFamily (n + 1)) cη μ j 0
```

Core helper:
```lean
∀ p : ℕ, p ≠ 0 →
  familyCoeffTerm n h k β
    (0 : CoeffFamily (n + 1)) cη μ j p = 0
```

Use the zero fluctuation family and the positive convolution powers of zero. Do not rebuild the convergence theory.

**Acceptance:** expand the surviving term in documentation against the existing \(K_k\sum_\gamma c_{\eta,\gamma}S_0\) kernel. This outer-series collapse does **not by itself** establish absolute convergence of the inner amplitude series for arbitrary `cη`; invoke the existing admissibility hypotheses for that assertion.

### u292 — Zero-noise, zero-log Mellin moment

```lean
theorem fluctMoment_population_zero_log
    (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) :
    fluctMoment β 0 0 μ 0
      = Real.Gamma μ * β ^ (-μ)
```

Proof: existing Gamma integral plus positive rescaling, or an existing fluctuation-moment evaluation if already present.

**Acceptance:** explicit \(\mu>0,\beta>0\); no derivative-under-asymptotics argument.

**Unit-3 review:** check that the zero-noise specialisation really uses the population integrand and that neither amplitude factorials nor box scaling have been duplicated.

---

## Remaining P1: identify canonical coefficients by uniqueness

Do not directly expand every state kernel to prove the leading coefficient formula.

Preferred route:

1. obtain the population `CutoffExpansion`;
2. use support to eliminate exponents below \(\lambda\);
3. use Headline VIII’s normalised limit;
4. compare the two descriptions to eliminate log degrees above \(m-1\);
5. identify the canonical coefficient at \((\lambda,m-1)\) with the face functional.

Start at \(b=1\). Transfer to general \(b\) through the existing box-rescaling interface.

This is both cheaper and less fragile than a second Mellin-residue calculation.

---

## P2: shift by re-presenting the integral

The first shift theorem should be the exact identity
```lean
origPhaseIntegral n h k β N b (fun _ => 0)
  (fun u => (∏ i, u i ^ l i) * ψ u)
=
origPhaseIntegral n (fun i => h i + l i) k β N b
  (fun _ => 0) ψ
```

Then apply the population theorem with weight `h + l`.

Obtain:

- support on `candidateExp (fun i => h i + l i) k μ`;
- the shifted minimum and multiplicity;
- the face limit for residual amplitude `ψ`;
- nonzero-leading equivalence when that face functional is nonzero.

Only afterwards identify these shifted coefficients with the canonical coefficients of the unshifted presentation, using uniqueness on a common lattice.

**Do not start by proving analytic division from coefficient support.** Factorisation is the cheap, honest interface.

For positivity, audit the actual generality of `blockCoeff_pos_of_nonneg_ne_zero`. The supplied summary does not establish that it directly covers every mixed-ratio configuration and arbitrary tangential measure. If adaptation requires new block geometry, first expose the hypothesis
```lean
0 < faceFunctional ...
```
and prove the general nonnegative-integral criterion separately within the four-unit cap.

---

## P3: deterministic assembly

Reuse `CutoffExpansion`, `cutoffExpansion_tan`, `add/sum/refine/pad`, and `gInt/gCoeff`.

Required outputs:

1. fixed deterministic zero-noise joint data give
   ```lean
   CutoffExpansion (commonQ k) (commonD n)
     (gInt ν h k β b x)
     (gCoeff ν h k β b x)
   ```
2. adding an exponentially small residual preserves this expansion;
3. ordered extraction and the min-exponent/max-log leading rule, with the assembled coefficient explicitly required nonzero.

**Important:** a fixed `JointData` need not have zero noise. The existing `tendsto_normalForm_pop` is an abstract deterministic assembly result; its name does not certify that its input is a population datum.

Either construct data through a zero-noise embedding or include an explicit zero-noise condition. This is a required interface audit.

Do not reprove XV or u289 under new names merely to accumulate §3 dots.

---

## P4: quotient

Reuse XIV wherever possible. State the ratio with real logarithmic powers or a quotient of natural powers so that \(r-m<0\) is represented correctly.

The bounded-observable inequality is a useful optional bridge lemma inside this allocation. If there is no common positive-measure integral interface available, state it as an additional hypothesis rather than pretending unrelated chart families establish it.

No wall-crossing formalisation in this programme.

---

## P5: the observable \(K\)

For a single chart with amplitude \(c\), compare weights \(h\) and \(h+2k\):

\[
\lambda'=\lambda+1,\qquad J'=J,\qquad m'=m,
\]
and the residual face weight is unchanged. Hence
\[
A_K=\frac{\lambda}{\beta}A_1.
\]

If \(A_1\neq0\),
\[
\boxed{\quad nE_{\beta,n}[K]\longrightarrow\lambda/\beta.\quad}
\]

For \(\beta=1\), this is \(\lambda\).

Finite assembly gives the same statement provided numerator and denominator use the same charts and the numerator is the chartwise phase insertion, with suitable negligible residuals.

**Defer:**

- exact differentiation under the original geometric integral;
- higher Gamma derivative identities;
- the correction \(-(m-1)/(n\log n)\).

The correction is accessible from coefficient-level identities, but it is not a consequence of differentiating a bare asymptotic equivalent and is outside this cap.

---

## P6: frame invariance

**Defer.**

It is mathematically separate, does not close the analytic or geometric gap, and risks creating a misleading “coordinate-free theorem formalised” impression.

A coordinate computation would merit a dot only for that coordinate computation—not for tubular normal derivatives on a manifold.

---

# 6. Required regression examples

Two examples should be mandatory rather than decorative.

### Mixed-ratio face dependence

Use \(h=(0,2)\), \(k=(1,1)\), with amplitude depending on \(y\). Show that the leading coefficient depends on the whole \(x=0\) face.

For instance, amplitudes \(1\) and \(1+y\) have the same corner value but different leading coefficients.

This rejects the general corner-only coefficient formula.

### Signed cancellation

In the same model, take
\[
\psi(x,y)=1-\frac32y.
\]
The leading face weight is \(y\), and
\[
\int_0^1\left(1-\frac32y\right)y\,dy=0,
\]
although \(\psi(0,0)=1\).

This directly rejects “nonzero deepest normal jet implies the proposed leading term is nonzero,” without relying on cross-chart cancellation.

Also document, even if not formalised as a separate example, that cancellation of a top log coefficient may expose a lower log coefficient at the same exponent.

---

# 7. Staging note for the authors

I would include the following executive text.

> **Status and proposed correction.**  
> The present §3 theorem conflates candidate exponents with nonzero leading terms and identifies a general mixed-ratio leading coefficient with a deepest-stratum value. The corrected theorem is an analytic normal-form population expansion, obtained from the Taylor-tree machinery at zero empirical process, followed by tangential integration and finite assembly. Monomial divisibility shifts the candidate support. Actual leading terms are determined by nonzero face-supported coefficient functionals after assembly.
>
> **Formalisation boundary.**  
> The Lean development proves the analytic implications for supplied one-sided normal-form data, including coefficient support, convergent population coefficient formulas, leading face limits, conditional assembly, and leading posterior quotients. It does not construct a resolution, prove its change-of-variables formula, construct compatible tubular neighbourhoods or partitions of unity, or show that a geometrically localised amplitude satisfies the analytic hypotheses.
>
> **Remaining bridge.**  
> The decomposition and its analytic admissibility remain explicit hypotheses. In particular, smooth localisation does not automatically meet the holomorphic normal-variable hypotheses of the current Taylor-tree theorem. No unconditional theorem about arbitrary resolved population integrals is claimed.

### Errata to list explicitly

1. **Leading exponent from divisorial order:** replace “is the leading exponent” by “is the first candidate exponent,” followed by the face-functional nonvanishing condition.
2. **Vanishing top coefficient:** remove “otherwise strictly larger”; smaller log degree at the same exponent is possible.
3. **Leading coefficient:** replace the corner/stratum-only formula by the mixed-ratio face integral.
4. **Shifted amplitude:** after shifting \(h\mapsto h+l\), use the residual amplitude \(\psi\).
5. **Cutoff dependence:** the displayed bare \(a_{-m}\) generally depends on \(b\) through nonminimal coordinates. It is not a function only of \((k_i,h_i)\).
6. **Candidate invariance under cutoffs:** fixed normal-form candidate sets provide allowable support; actual nonzero coefficients and actual leading pairs can change or disappear under cutoffs.
7. **Parity:** with \(|u|^h\), odd bare moments are controlled by the amplitude monomial parity, not \(h+\gamma\).
8. **Taylor remainder:** finite normal Taylor degree is not generally an asymptotic-order cutoff.
9. **Adapted partition of unity:** normal constancy, saturation and compatibility near incident strata require a real construction; they are not consequences of ordinary smooth partition-of-unity existence.
10. **Denominator positivity:** justify it through positive face functionals and a positive assembled leading coefficient, not generally through a deepest-stratum density integral.
11. **Wall-crossing:** include coefficient cancellation loci; remove the unsupported continuity-to-piecewise-constancy inference.
12. **Population versus empirical:** shared candidate support does not license transferring the old claims about actual shifted leading exponents and wall-crossing unchanged to the empirical case.

---

# 8. Gates and stop criterion

**Gate A — mathematical approval:** authors approve the conditional normal-form theorem, mixed-ratio face formula, and removal of the unsupported wall-crossing conclusion.

**Gate B — analytic admissibility:** every theorem identifies whether it assumes analytic normal data, merely continuous amplitudes for a leading limit, or an external geometric decomposition. No silent interchange.

**Gate C — coefficient identity:** population coefficients are linked to existing canonical coefficients, including box scaling and uniqueness. No parallel informal coefficient system.

**Gate D — positivity and cancellation:** every asymptotic equivalence carries a nonzero coefficient hypothesis or a proved positivity criterion.

**Gate E — release:** clean pinned build, no `sorry`, no added `axiom`, dependency audit, two regression examples, and the staging note’s non-claims reproduced in the headline documentation.

**Stop at 20 units**, or earlier if completion would require:

- a smooth-amplitude all-orders theorem;
- a geometric construction;
- analytic division with new parameter-uniform estimates;
- new infinite coefficient infrastructure;
- a general parity programme.

At that point release the proved conditional analytic result and name the remaining bridge. Do not enlarge the scope to preserve the appearance of a completed §3.

**Bottom line:** rewrite §3 around **canonical coefficient functionals and admissible normal-form data**, not around generic divisor orders and deepest-stratum jets. That is a substantive correction the existing seabed can support, while keeping the genuinely geometric theorem visibly unproved.
