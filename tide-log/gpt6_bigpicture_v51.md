## Recommendation

**If you want one more substantive block, do (a), strengthened to include chart-allocation corrections—not just another evidence graph law. Budget five units, then stop.** This closes the gap between the chartwise theory and a finite assembled model while producing a genuinely new observable: the first correction to the posterior distribution of the chart label.

My ranking is:

1. **(a), plus finite-chart allocation corrections.**
2. **(c),** if transverse sensitivity is an intended scientific output; otherwise it is a short corollary rather than a block.
3. **(b), conditional on a compact-temperature remainder audit.**
4. **(f), Euler-constant regression only.** The uniform-assembly caveat belongs in priority 1.
5. **(d), only after establishing the sharper uniform remainder.**
6. **(e), maintenance, not a theorem block.**

### The three explicit answers

**(i) Is (a) now cheap?**  
**Relatively cheap, yes.** The random transfer and quotient parts should be routine with your delivered machinery. The substantive deterministic obligation is uniform scale separation for the discarded charts. Finite assembly then requires no new local asymptotic analysis, provided each chart’s uniform two-term theorem is available on the compact projections of the common data set.

**(ii) Is (b) reachable without reopening the Taylor tree?**  
**Not from the stated results alone.** Joint continuity of the tilt does not absorb the variation of the temperature in the base evidence integral. It may require only a compact-parameter strengthening of the existing estimates, rather than any new Taylor expansion, but that must be checked. I would not budget a theorem unit around it before that audit.

**(iii) Is this a natural stopping point?**  
**Yes.** CIII completes a coherent chartwise programme: deterministic expansions → joint random observables → expectations under UI. Final consolidation is already defensible and preferable to collecting easy transfer corollaries. The five-unit block below is justified only if finite assembled models are part of the intended endpoint. After it, I would consolidate rather than automatically pursue (b) or (d).

---

# Proposed five-unit block

The Lean names below are target shapes, not claims about existing identifiers.

## Common setup

Let `ι` be finite, and let the data space be a finite product
```lean
D := ∀ i : ι, Dᵢ i
```
or, more generally, a Polish common data space equipped with continuous maps into the chart data spaces. **There is no independence assumption.**

For chart \(i\), write
\[
E_{i,N}(x)
 :=\frac{N^{\lambda_i}}{L_N^{m_i-1}}Z_{i,N}(x),
 \qquad L_N=\log N,
\]
with the existing uniform expansion
\[
L_N(E_{i,N}-F_i)\longrightarrow B_i
\]
on compact data sets. All chart functions below are pulled back to \(D\).

Choose the global dominant pair:
\[
\lambda=\min_i\lambda_i,\qquad
m=\max_{\lambda_i=\lambda}m_i.
\]
Define
\[
I_0=\{i:\lambda_i=\lambda,\ m_i=m\},\qquad
I_1=\{i:\lambda_i=\lambda,\ m_i+1=m\}.
\]
Set
\[
A=\sum_{i\in I_0}F_i,\qquad
D_{\!1}=\sum_{i\in I_0}B_i+\sum_{i\in I_1}F_i.
\]

Use a name such as `assembledCorrection` for \(D_1\), avoiding collision with the data space.

---

## Unit 397 — Uniform finite-chart scale separation

**Target:** lift the scalar scale comparisons to compact-uniform negligibility with data-dependent chart factors.

Put
\[
q_{i,N}
 =N^{-(\lambda_i-\lambda)}
   \frac{L_N^{m_i-1}}{L_N^{m-1}}.
\]
For every compact \(K\subseteq D\), prove
\[
L_N q_{i,N}E_{i,N}\longrightarrow 0
\quad\text{uniformly on }K
\]
when either:

- \(\lambda_i>\lambda\), or
- \(\lambda_i=\lambda\) and \(m_i+1<m\).

A useful generic target is:

```lean
-- Schematic
theorem tendstoUniformlyOn_scalar_mul_zero_of_eventually_bounded
    (ha : Tendsto a atTop (𝓝 0))
    (hbounded : EventuallyUniformlyBoundedOn f K) :
    TendstoUniformlyOn
      (fun N x => a N * f N x)
      (fun _ => 0) atTop K
```

Then specialize it to `a N = L N * q i N`.

**Inputs**

- Uniform two-term chart convergence, hence eventual uniform boundedness on compacts.
- Continuity of \(F_i,B_i\) and compact boundedness.
- `tendsto_shift_ratio` and logarithmic power comparisons.

**Traps**

- Do not use truncated natural subtraction to represent \(m_i-m\). Keep the ratio of natural powers or use an explicitly integer-valued exponent.
- Treat \(N=0,1\) through eventual statements.
- The lower-log chart case is uniform because its normalized chart evidence is bounded—not because pointwise negligibility automatically upgrades.

**Payoff:** this closes the old “uniform remainder after assembly” caveat at its actual source.

---

## Unit 398 — Compact-uniform assembled two-term theorem

Define
\[
Z_N^{\mathrm{asm}}=\sum_i Z_{i,N},\qquad
G_N=\frac{N^\lambda}{L_N^{m-1}}Z_N^{\mathrm{asm}}.
\]

**Main target**
```lean
theorem tendstoUniformlyOn_assembled_nextLog
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x =>
        L N * (assembledScaledEvidence N x - assembledLead x))
      assembledCorrection atTop K
```

That is,
\[
L_N(G_N-A)\longrightarrow D_1
\quad\text{uniformly on compact sets}.
\]

Also expose:

- continuity of `assembledLead` and `assembledCorrection`;
- compact-uniform leading convergence \(G_N\to A\);
- eventual uniform positivity of \(G_N\) on compact subsets of
  \[
  D_+=\{x:A(x)>0\}.
  \]

**Inputs**

- LXXXIII `assembled_twoTerm` for the decomposition and coefficient formula.
- Unit 397.
- Finite sums of uniform limits.
- Existing compact positivity machinery.

**Traps**

- The \(I_1\) contribution is \(F_i\), not \(B_i\).
- No positivity of every individual \(F_i\) is needed for the analytic statement.
- Work on **total-leading-coefficient positivity**, not the unnecessarily small domain \(\bigcap_i\{F_i>0\}\).
- Do not claim anything on \(A=0\).

This unit should establish one reusable uniform theorem, not duplicate the pointwise assembly proof chart by chart.

---

## Unit 399 — First correction to chart allocations

This is the highest-value addition beyond the assembly itself.

Define globally normalized chart contributions
\[
g_{i,N}=\frac{N^\lambda}{L_N^{m-1}}Z_{i,N}.
\]
Let
\[
a_i=
\begin{cases}
F_i&i\in I_0,\\
0&\text{otherwise},
\end{cases}
\qquad
d_i=
\begin{cases}
B_i&i\in I_0,\\
F_i&i\in I_1,\\
0&\text{otherwise}.
\end{cases}
\]
Then \(\sum_i a_i=A\) and \(\sum_i d_i=D_1\).

On \(D_+\), define
\[
p_{i,N}=\frac{Z_{i,N}}{\sum_j Z_{j,N}},\qquad
p_i=\frac{a_i}{A},
\]
and
\[
h_i=\frac{d_i}{A}-\frac{a_iD_1}{A^2}.
\]

**Main target**
```lean
theorem tendstoUniformlyOn_chartAllocation_nextLog
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x i =>
        L N * (chartAllocation N x i - chartAllocationLead x i))
      chartAllocationCorrection atTop K
```

Package this in the finite-product topology. Also prove
\[
\sum_i p_i=1,\qquad \sum_i h_i=0.
\]

The useful explicit consequences are:

- **Dominant chart:** correction \(B_i/A-F_iD_1/A^2\).
- **One-log-lower chart:** \(L_Np_{i,N}\to F_i/A\).
- **All remaining charts:** \(L_Np_{i,N}\to0\).

**Inputs**

- Units 397–398.
- Generic uniform quotient lemma.
- Finite-product uniform convergence.

**Traps and non-claims**

- Call these *probability allocations* only under nonnegativity of the chart contributions and positivity of their sum.
- With overlapping charts, they describe the label induced by the chosen decomposition or partition of unity. They need not be intrinsic geometric component probabilities.
- Zero leading weight in an individual chart is allowed. This is not an asymptotic expansion after cancellation of the **total** face coefficient.

---

## Unit 400 — Assembled observable quotients and marked expectations

Prove the assembled ratio theorem once, with coefficient-family numerators.

Suppose normalized numerator contributions \(Y_{i,N}\) satisfy compact-uniform two-term expansions with coefficients \(U_i,V_i\), at the same chart scales as the denominator. Define
\[
C=\sum_{I_0}U_i,\qquad
E=\sum_{I_0}V_i+\sum_{I_1}U_i.
\]
For
\[
R_N=\frac{\sum_iY_{i,N}}{\sum_iZ_{i,N}},
\]
prove
\[
L_N\left(R_N-\frac CA\right)
\longrightarrow
\frac EA-\frac{CD_1}{A^2}
\]
uniformly on compact subsets of \(D_+\).

**Lean-level shape**
```lean
theorem tendstoUniformlyOn_assembled_quotient_nextLog
    (hnum : UniformChartTwoTerm numerator ...)
    (hden : UniformChartTwoTerm denominator ...)
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x => L N * (assembledRatio N x - ratioLead x))
      ratioCorrection atTop K
```

Two worthwhile specializations:

1. **Finite chart marks.** For continuous \(c_i(x)\),
   \[
   L_N\left(\sum_i c_i p_{i,N}-\sum_i c_i p_i\right)
   \to\sum_i c_i h_i.
   \]
2. **Existing posterior coefficient families:** assemble the energy numerator and finitely many fixed-\(s\) Laplace numerators, wherever their chartwise uniform hypotheses have already been proved.

**Inputs**

- Unit 398 applied to numerator families.
- Existing energy and fixed-\(s\) Laplace coefficient-family results.
- `DataTilt` for the physical Laplace identification.
- Uniform quotient machinery.

**Traps**

- Evidence asymptotics alone do **not** justify differentiating in temperature to obtain an energy numerator.
- Do not recover numerator expansions by dividing by each chart’s \(F_i\). That would unnecessarily exclude charts with vanishing leading coefficient.
- Fixed-\(s\) Laplace assembly is not local uniformity in \(s\).

---

## Unit 401 — One joint random assembled law

Bundle the genuinely useful outputs into one finite-dimensional statistic:
\[
\mathsf T_N(x)=
\left(
 L_N(G_N-A),\
 -L_N(\log G_N-\log A),\
 (L_N(p_{i,N}-p_i))_i,\
 (L_N(R_{k,N}-R_k))_k
\right).
\]
Its limit is
\[
\mathsf T(x)=
\left(
 D_1,\
 -D_1/A,\
 (h_i)_i,\
 (H_k)_k
\right).
\]

**Main target, schematically**
```lean
theorem randomAssembledMixed_graphLaw_tendsto
    (hμ : μₙ ⟶w μ) :
    graphLaw μₙ (assembledMixedStat · n)
      ⟶w graphLaw μ assembledMixedLimit
```

Here the measures live on the Polish admissible domain \(D_+\), and the graph law retains the **entire common datum**.

Equivalent random-variable formulation:
\[
X_N\Rightarrow X
\quad\Longrightarrow\quad
(X_N,\mathsf T_N(X_N))
 \Rightarrow
(X,\mathsf T(X)).
\]

**Inputs**

- Units 398–400.
- C’s uniform logarithmic lemma.
- CII’s finite-product continuous-convergence machinery.
- Existing graph-law transfer.

**Traps**

- Marginal convergence of the chart data is insufficient: require joint convergence.
- Independence is neither required nor inferred.
- For an external statistic identified through a sampling identity, retain that identity as an explicit hypothesis.
- CIII gives expectation corollaries only with the corresponding UI assumptions. Distributional convergence alone does not.

I would **not spend a sixth unit merely applying CIII again**. Add those corollaries inside this unit if needed.

---

# Why not the other branches now?

### (b): audit first, theorem block later

The required deterministic theorem is genuinely stronger:
\[
\sup_{t\in[\beta,\beta+S],\,x\in K}
\left|L_N(E_{t,N}(x)-F_t(x))-B_t(x)\right|\to0.
\]

Before scheduling it, check whether every temperature-dependent remainder bound admits a uniform bound for \(t\in[\beta,\beta+S]\). Staying away from zero is helpful, but continuity of one displayed `cutoffBound` is not enough if other thresholds or tail bounds also depend on temperature.

**If the existing proof factors through uniformly bounded constants, this could avoid new Taylor-tree mathematics.** Otherwise it is a real analytic extension. Fixed-\(s\) convergence plus continuity does not establish the needed uniform next-order convergence.

The `C([0,S])`-valued graph law is the payoff *after* that theorem, not a shortcut to it.

### (c): good small theorem, limited new infrastructure

The map
\[
x\mapsto B(x)-B(\operatorname{faceRestrict}x)
\]
is a natural continuous statistic. Its graph-law transfer and an a.s. sign corollary are worthwhile if transverse dependence is central. But distinguish this coefficient-level statistic from a new finite-\(N\) sensitivity theorem.

### (d): substantially less automatic than it looks

For \(m=1\), \(B=0\) establishes no particular next polynomial rate. Before a random refinement, verify:

- the actual next nonzero exponent;
- the possible logarithmic multiplicity at that exponent;
- a **uniform** remainder at the sharper scale.

Continuity of \(C_{\lambda+1/Q,j}(x)\) supplies continuity of a proposed limit, not convergence to it. A surviving log polynomial may also prevent the proposed unadjusted normalization from having a finite limit.

---

## Stop rule

**Choose either consolidation now, or these five units followed by consolidation.** Both are mathematically honest endpoints.

After the assembly block, the non-claims should still explicitly include:

- no resolution/geometric bridge;
- no convergence theorem for the phase field itself;
- no stable convergence without the required sampling structure;
- no original-space posterior theorem;
- no total-face-coefficient cancellation regime;
- no variable-temperature or sharper lattice-order expansion unless separately proved.

Update the theorem map and mirror at that endpoint; keep the Overleaf push behind the existing user-authorisation gate.
