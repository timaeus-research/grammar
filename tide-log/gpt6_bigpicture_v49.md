**Yes: (A) + (B) is the right next block.** The missing input is now principally uniform bookkeeping, not new asymptotic analysis. I would use **five units**, with the coefficient-family topology throughout.

Ranking:

1. **(A), including coefficient-topology continuity of \(F,B\).**
2. **(B), jointly with the random data and for a finite vector of statistics.**
3. **The easy part of (C): sup-norm continuity of \(F\)**, only if needed elsewhere.
4. **(D)** as supporting cleanup, not a headline.
5. **(E)** after the theorem block.

Do **not** pursue general sup-norm continuity of \(B\).

## Fix the domain and conventions first

Fix the geometry, \(\beta>0\), and **one coefficient radius \(b>0\)**. Let
\[
D=\mathrm{DataSpace}(n+1)\times\mathrm{DataSpace}(n+1)
\]
or the equivalent existing bundled phase/amplitude data space. Its norm must control the weighted masses used by `TaylorTreeConclusion`.

Write
\[
p=m-1,\qquad t_N=\log N,\qquad
d_N=N^{-\lambda}t_N^p.
\]
All asymptotic identities below are eventually restricted to \(N\ge e\).

Use **canonical coefficients in powers of \(\log N\)**:
\[
F(x),\qquad
B(x)=
\begin{cases}
\text{coefficient at }(\lambda,m-2),&m\ge2,\\
0,&m=1.
\end{cases}
\]
Identify them with the explicit spatial face/finite-part expressions afterward.

This convention matters when \(b\ne1\): a coefficient of \(\log(Nb^{2|k|})\) is not automatically the corresponding coefficient of \(\log N\).

---

## Unit 1 — Uniform spatial next-log expansion on coefficient balls

### Targets

For every finite \(R\),
```lean
theorem tendstoUniformlyOn_spatialNextLog_closedBall :
  TendstoUniformlyOn
    (fun N x =>
      Real.log N * (Z N x / leadingScale N - F x))
    B atTop (Metric.closedBall 0 R)
```

Together with:
```lean
theorem continuous_spatialLeadingCoeff : Continuous F
theorem continuous_spatialNextLogCoeff : Continuous B
```

Then derive the compact-set version by boundedness of compact sets.

**No positivity assumption belongs in this unit.** These are unnormalised integral expansions, valid for signed amplitude data as well.

### Minimal proof from the existing ordered remainders

For \(m\ge2\), first check whether the existing ordered remainder at
\[
(\lambda,m-2)
\]
is, after simplification, exactly
\[
t_N\left(\frac{Z_N(x)}{d_N}-F(x)\right).
\]

It should be: all preceding coefficients vanish except the coefficient at \((\lambda,m-1)\). Thus the required work is:

1. universal coefficient-vanishing lemmas for exponents below \(\lambda\);
2. vanishing at \(\lambda\) above degree \(m-1\);
3. identification of the surviving leading coefficient with \(F\);
4. identification of the target coefficient with \(B\);
5. an exact algebraic rewrite of the ordered remainder.

If that matches the existing normalization, **the uniform theorem is already present in substance**. Use the existing uniform ordered-remainder result rather than reprove the analytic estimates.

The first ordered remainder at \((\lambda,m-1)\) is useful for the leading coefficient identification, but need not be a separate analytic step if that identification is already available.

### Direct fallback from `TaylorTreeConclusion`

Choose a fixed cutoff exponent \(\tau>\lambda\). After converting to powers of \(\log N\), the finite expansion has:

- no terms with exponent below \(\lambda\);
- at exponent \(\lambda\), degree at most \(p\);
- finitely many terms with exponent \(\mu>\lambda\);
- a remainder of order \(N^{-\tau}(1+\log N)^n\), uniformly on the data ball.

On that ball:

- finitely many coefficients are uniformly bounded by coefficient continuity/Lipschitz bounds;
- the explicit `cutoffBound` has a uniform envelope from the bounded constant term and weighted masses.

After subtracting \(F\) and \(B\), every remaining exponent-\(\lambda\) term contributes
\[
C_{\lambda,j}(x)t_N^{j-p+1},\qquad j\le p-2,
\]
hence is uniformly \(O(1/t_N)\).

Every higher-exponent term contributes
\[
C_{\mu,j}(x)N^{-(\mu-\lambda)}t_N^{j-p+1},
\]
hence tends uniformly to zero. There is a positive gap because this is a **fixed finite lattice truncation**. The normalized cutoff remainder tends uniformly to zero for the same reason.

One convenient coarse bound is
\[
\sup_{\|x\|\le R}
\left|t_N\left(Z_N(x)/d_N-F(x)\right)-B(x)\right|
\le
\frac{C_R}{t_N}
+C_RN^{-\gamma}(1+t_N)^{n+1},
\]
for some fixed \(\gamma>0\).

There is no need to optimize this estimate.

### Scaling trap

If the raw expansion uses an outer factor \(b^a\), the variable \(Nb^d\), and raw coefficients \(C_{\lambda,j}\), where \(d=2|k|\), then
\[
F=b^{a-d\lambda}C_{\lambda,p},
\]
and, for \(p\ge1\),
\[
B=b^{a-d\lambda}
\left(C_{\lambda,p-1}
+p\log(b^d)\,C_{\lambda,p}\right).
\]
Use this conversion unless `dataBoxCoeff` already incorporates it.

### The \(m=1\) branch

Do not write a universal definition using natural-number subtraction `m - 2`: at \(m=1\) it becomes zero and selects the **leading** coefficient.

Instead prove separately:
\[
t_N\bigl(N^\lambda Z_N(x)-F(x)\bigr)\longrightarrow0
\]
uniformly on coefficient balls, and define \(B=0\).

This follows directly from the positive exponent gap and cutoff remainder. An ordinary leading \(o(1)\) theorem alone would **not** imply this log-amplified statement.

**Inputs:** ordered uniform remainders; quantitative Taylor-tree cutoff; universal spectral vanishings; coefficient Lipschitz/continuity; existing spatial coefficient identifications.

---

## Unit 2 — Uniform next-log quotient theorem, with a positivity floor

State this generically for normalized numerator and denominator families.

Suppose, uniformly on \(S\),
\[
t_N(a_N-A)\to B_A,\qquad
t_N(z_N-F)\to B_Z,
\]
with the four limiting functions bounded on \(S\), and
\[
F(x)\ge\delta>0\quad(x\in S).
\]
Then
\[
t_N\left(\frac{a_N}{z_N}-\frac{A}{F}\right)
\longrightarrow
\frac{B_AF-AB_Z}{F^2}
\]
uniformly on \(S\).

Lean-level shape:
```lean
theorem TendstoUniformlyOn.nextLog_div
    (hA : TendstoUniformlyOn
      (fun N x => log N * (a N x - A x)) BA atTop S)
    (hZ : TendstoUniformlyOn
      (fun N x => log N * (z N x - F x)) BZ atTop S)
    ...
    (hfloor : ∀ x ∈ S, δ ≤ F x)
    (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun N x => log N * (a N x / z N x - A x / F x))
      (fun x => (BA x * F x - A x * BZ x) / (F x)^2)
      atTop S
```

Also obtain eventual uniform positivity \(z_N\ge\delta/2\).

For applications, take either:

- a coefficient ball intersected with `{x | δ ≤ F x}`; or
- a compact \(K\) on which \(F>0\), extracting \(\delta\) by continuity.

**Strict pointwise positivity is sufficient on compact sets. A fixed global floor is not needed for the eventual random theorem.**

Instantiate this with the existing coefficient-family numerator/denominator expansions for the LXXXVII dictionary. Keep the theorem modular enough to handle a finite vector.

**Inputs:** Unit 1; `quotient_second_order` as an algebraic guide; existing observable coefficient identities.

---

## Unit 3 — Compact-uniform-to-graph-law transfer

Add the precise generic bridge needed here:
```lean
theorem continuouslyConverges_of_uniformOn_compacts
    [PseudoMetricSpace D] [PseudoMetricSpace E]
    (hT : ∀ K, IsCompact K →
      TendstoUniformlyOn T B atTop K)
    (hB : Continuous B) :
    ContinuouslyConverges T B
```
Adjust hypotheses and the index type to the existing definition.

The sequential proof uses only the compact set
\[
\{x\}\cup\{x_j:j\in\mathbb N\}
\]
for a convergent sequence \(x_j\to x\).

Then package a graph-law consequence, if not already a direct specialization:
\[
\mu_j\Rightarrow\mu
\quad\Longrightarrow\quad
(\mathrm{id},T_j)_*\mu_j
\Rightarrow
(\mathrm{id},B)_*\mu.
\]

### Two important qualifications

1. Call the hypothesis **uniform convergence on compact sets**, not unqualified “locally uniform convergence.” In an infinite-dimensional coefficient space, convergence uniformly on compact sets need not mean convergence uniformly on a fixed neighborhood of every point.

2. `DataSpace` being normed does not by itself establish the hypotheses of the Polish graph-law theorem. Verify completeness and separability, or state the transfer with explicit typeclass assumptions until those are discharged. A countably indexed weighted-\(\ell^1\) realization should supply them, but this is a real obligation.

For finite-\(N\) functions, also verify the measurability required by `graphLaw`; continuity is a convenient sufficient condition.

**Inputs:** existing `ContinuouslyConverges` and graph-law machinery; metric compactness of a convergent sequence and its limit.

---

## Unit 4 — Random next-log evidence, jointly with its data

For external random data laws \(\mu_j\Rightarrow\mu_0\) on \(D\), and \(N_j\to\infty\), prove
\[
\left(
X_j,\;
\log N_j\left(\frac{Z_{N_j}(X_j)}{d_{N_j}}-F(X_j)\right)
\right)
\Rightarrow
\left(X,\;B(X)\right).
\]

Prefer the law-level theorem first:
```lean
tendsto_graphLaw_spatialNextLog
```
and then the random-variable formulation if useful.

This theorem needs:

- **no positivity floor**;
- no common probability space;
- no almost-sure coupling;
- no phase-field CLT.

It includes \(m=1\), with limit second coordinate zero.

A useful finite-dimensional extension is to allow several amplitude families driven by the same data and obtain their next-log coefficients jointly. That prevents later applications from proving only marginal convergence.

**Inputs:** Units 1 and 3; continuity of the finite-\(N\) phase integrals or a separate measurability lemma.

---

## Unit 5 — Random next-log posterior statistics

Work on an admissible data domain \(U\) where the denominator face coefficient is strictly positive and the coefficient-family statistic is defined. For each statistic \(r\), write
\[
M_r(x)=\frac{A_r(x)}{F(x)},\qquad
C_r(x)=\frac{B_r(x)F(x)-A_r(x)B_Z(x)}{F(x)^2}.
\]

For a fixed finite collection, prove jointly:
\[
\left(
X_j,\;
\left[\log N_j\bigl(S_{r,N_j}(X_j)-M_r(X_j)\bigr)\right]_r
\right)
\Rightarrow
\left(X,\;[C_r(X)]_r\right).
\]

Prioritize these instantiations:

1. **Energy mean**, using the existing LXXXI/LXXXVII normalization:
   \[
   \log N_j\left(\mathbb E_{Q_{N_j}(X_j)}[N_jK]-\mu(X_j)\right)
   \Rightarrow c_2(X).
   \]
2. A fixed finite list of Laplace-transform parameters.
3. Evidence ratios already represented by coefficient families.

The energy case deserves an explicit audit: its numerator is typically \(N Z_N[K\eta]\), not simply \(Z_N[\eta']\) with an unchanged leading scale. Use the appropriate shifted spectral indices and prove the corresponding uniform expansion. Do not obtain it merely by naming it an ordinary amplitude quotient.

### Domain choice

A clean formulation takes \(\mu_j,\mu_0\) as laws on \(U\). If \(U=\{F>0\}\), it is open by Unit 1; with a Polish ambient space it admits the needed Polish structure. Additional physical constraints on amplitudes must be handled explicitly.

On each compact subset of \(U\), positivity supplies the floor needed by Unit 2. Consequently the random theorem does **not** require a common deterministic \(\delta\) for all possible data.

Discharge actual finite-\(N\) normalizer positivity with `origPhaseIntegral_pos` wherever its hypotheses apply. That is supporting cleanup, not another headline.

**Inputs:** Units 1–3; observable coefficient-family realizations and shifted expansions; existing quotient coefficient identifications; positivity on the physical domain.

---

## Why not sup-norm continuity of the finite-part coefficient?

Coefficient-topology continuity of \(B\) is already available through its spectral-coefficient representation. Use it.

A general finite-part functional is not controlled by the sup norm alone. For example,
\[
h_j(t)=\frac{1-(1-t)^j}{\log(j+1)}
\]
is polynomial and tends uniformly to zero on \([0,1]\), while
\[
\int_0^1\frac{h_j(t)-h_j(0)}t\,dt
=\frac{H_j}{\log(j+1)}
\longrightarrow1.
\]
Thus even analyticity of each individual input does not make this functional sup-norm continuous on unrestricted analytic families.

This does not prove discontinuity of every particular spatial \(B\), where cancellations can occur. It does rule out the proposed general continuity argument. A controlled coefficient norm—or suitable transverse Hölder/derivative control—is the right setting.

Sup-norm continuity of \(F\) remains a cheap, valid separate result, but is not needed to unlock this block.

## Explicit non-claims

This block should not claim:

- next-log corrections for arbitrary continuous observables;
- a functional limit theorem over all Laplace parameters;
- convergence in law of the phase field itself;
- stable convergence relative to an environment without the requisite sampling identity;
- random **draw-level** corrections merely from corrections to posterior expectations;
- convergence of expectations of random next-log statistics without uniform integrability;
- higher-order behavior after cancellation of \(F\);
- a nonzero \(1/\log N\) coefficient when \(m=1\).

**Bottom line:** prove the coefficient-ball theorem once, preferably by rewriting the existing second ordered remainder; branch explicitly at \(m=1\); then use compact positivity and the existing graph-law machinery. The principal genuinely new payload is the **joint random next-log dictionary**, not another pointwise asymptotic theorem.
