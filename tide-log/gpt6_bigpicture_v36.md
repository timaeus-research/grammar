## Recommendation

**Freeze the mathematical release and hand it off. Do not start another substantive programme on auto.**

On the status you supplied, §4 now has a complete and useful **conditional analytic–probabilistic core**:

- §4.1: fluctuation functions and ladder algebra;
- §4.2: the positive-dimensional Taylor-tree expansion under the declared analytic hypotheses;
- §4.3: continuous coefficient functionals, finite-cutoff stochastic expansions through tangential integration and finite chart assembly, and the leading posterior quotient.

That is not the same as an unconditional formalisation of every assertion in §4.3. The remaining gap is principally **upstream model construction and statement repair**, not another missing Taylor-tree estimate.

I would mark the seabed **“COMPLETE — conditional §4 release”**, not “the paper completely formalised.” Prepare the three hand-off reports, ensuring that the stochastic report includes A4-L and its qualifications.

A closing tranche of at most two units is defensible, but **not required for completion**. My default instruction to the autonomous formaliser is: **prepare the hand-off, not another theorem programme**.

## 1. What remains, ranked

Here is the ranking I would use *if the authors request a small additional deliverable*. Estimates are ceilings for thin corollaries, not invitations to develop new infrastructure.

| Rank | Candidate | Estimate | Gate / verdict |
|---|---|---:|---|
| 1 | **Different leading scales in the posterior quotient** | 1 unit | Genuine interpretation gain, using existing A4-L almost verbatim. GO only as a thin corollary with joint convergence and a.e. nonzero limiting denominator. |
| 2 | **Conditional deterministic normal-form expansion, `ξ = 0`** | 1–2 units | Useful bridge back to the population discussion. Use the existing deterministic assembly theorem directly. Must not be labelled the obsolete §3 theorem. |
| 3 | **Finitely many observables jointly, one denominator** | 1–2 units **if the probability route already exists** | Useful posterior API. Marginal quotient convergence does not establish joint convergence. Stop if this requires a new multivariate probability development. |
| 4 | **Monomial amplitude absorption, `h ↦ h+l`** | 1 unit for the identity; up to 2 for its Taylor-tree specialisation | Good local bridge, but “shifted expansion” and “identified leading exponent” are different claims. No automatic leading-coefficient nonvanishing. |
| 5 | **Paper-language dictionary for finite cutoffs and asymptotic notation** | 0–1 unit | Primarily documentation. Add Lean only for an exact translation with downstream use; do not invent a parallel asymptotics framework. |
| — | Limiting denominator nonvanishing from finite-sample positivity | **NO-GO** | Positivity at every finite sample does not prevent convergence to zero. |
| — | Gaussian identification from Hypothesis I | **NO-GO as a closing tranche** | Requires a genuine empirical-process/topology bridge, not coefficient continuity alone. |
| — | Hypothesis I / greybook standard-form / resolution-atlas bridge | **No bounded estimate without a statement audit** | Nothing in the supplied status supports treating this as cheap. |
| — | All-orders posterior division; obsolete §3 expansion | **NO-GO** | Retain the existing statement gates. |

### Important distinctions

**The absent `prop:convergence` and `lemma:AsymInt` need not hold this release hostage.** You have already supplied rigorous replacements in explicit topologies and with explicit uniform estimates. The authors need to decide whether those are the statements they want in the paper. Their missing labels are not, by themselves, reasons to keep proving things.

**Gaussian input is not Gaussian output.** If the limiting data have a specified Gaussian law, the existing theorem already identifies the coefficient law as its pushforward under the coefficient map. Identifying that input law from the empirical model—or obtaining a more explicit distribution for nonlinear coefficient functionals—is another project.

**There is some value in the paper’s `∼` language, but little value in a notation-only programme.** The useful dictionary is:

\[
Z(N)-S_L(N)=O\!\left(N^{-L}(1+\log N)^D\right),
\]

and, for an ordered target,

\[
Z(N)-S_{\prec(\mu,j)}(N)
 =c_{\mu,j}N^{-\mu}(\log N)^j
   +o\!\left(N^{-\mu}(\log N)^j\right).
\]

Only when \(c_{\mu,j}\ne0\) should this become an asymptotic equivalence to \(c_{\mu,j}N^{-\mu}(\log N)^j\). When the coefficient is zero, the meaningful conclusion is the little‑\(o\) statement, not an equivalence to zero. For random source data, retain the source-dependent coefficient and the in-probability remainder statement; do not disguise convergence in law as deterministic `IsEquivalent`.

### The vanishing-order candidate

The safe chart-level identity is simply

\[
Z_{h,k}(N;\xi,u^l\eta)=Z_{h+l,k}(N;\xi,\eta),
\]

provided the chart conventions and amplitude representation make multiplication by \(u^l\) legitimate.

The Taylor-tree theorem can then be applied with \(h+l\). But

\[
\mu_I(\varphi)
 =\min_{i:k_i>0}\frac{h_i+l_i+1}{2k_i}
\]

is an **actual leading exponent only after a noncancellation/nonvanishing argument**. A factorisation of the amplitude alone does not establish that conclusion; signed observables and chart assembly can cancel leading coefficients. Exclude the non-decaying case with no positive \(k_i\).

I would call the cheap result **“monomial absorption and shifted normal-form expansion,”** not “wall-crossing.”

Likewise, `E[K] ∼ λ/n` is not an immediate stochastic corollary. Even in the deterministic normal form it needs the leading coefficient ratio, the identification of \(K\), and the temperature convention—typically a \(\beta\) factor matters. In the stochastic setting, the quotient coefficient can remain random. Do not bundle that example into a two-unit promise.

## 2. Optional closing tranche: exact first two units

If you want a final, explicitly bounded mathematical tranche rather than stopping now, I recommend **different scales followed by the deterministic bridge**. This avoids reopening probability infrastructure.

### Unit 1 — Different-scale leading posterior quotient

First export the generic statement.

Let \(U_\ell,V_\ell\) be measurable real random variables and let \(a_\ell,b_\ell\) be deterministic real sequences, nonzero at every index. Assume

\[
\left(\frac{U_\ell}{a_\ell},\frac{V_\ell}{b_\ell}\right)
 \Rightarrow (A,B),
 \qquad \mathbb P(B=0)=0.
\]

Then

\[
\boxed{\quad
\frac{b_\ell}{a_\ell}\frac{U_\ell}{V_\ell}
 \Rightarrow \frac AB .
\quad}
\]

This uses the existing quotient theorem and the identity

\[
\frac{U_\ell/a_\ell}{V_\ell/b_\ell}
 =\frac{b_\ell}{a_\ell}\frac{U_\ell}{V_\ell}.
\]

No finite-sample nonvanishing of \(V_\ell\) is required under totalised division.

The paper-facing specialisation takes

\[
a_\ell=N_\ell^{-\mu_\varphi}(\log N_\ell)^{j_\varphi},
\qquad
b_\ell=N_\ell^{-\mu_1}(\log N_\ell)^{j_1},
\]

with \(N_\ell>1\), giving

\[
\boxed{
N_\ell^{\mu_\varphi-\mu_1}
(\log N_\ell)^{j_1-j_\varphi}
\frac{Z_\ell^0[\varphi]}{Z_\ell^0[1]}
\Rightarrow
\frac{C^\varphi_{\mu_\varphi,j_\varphi}(Y)}
     {C^1_{\mu_1,j_1}(X)} .
}
\]

Here the log exponent difference is an integer or real difference, **not truncated natural subtraction**.

For the assembly wrapper, require:

- joint numerator/denominator data convergence;
- negligible external residuals at their **respective** scales;
- source predecessor sums vanishing at their **respective** targets;
- a.e. nonzero limiting denominator coefficient.

The joint convergence of the two normalised integrals must be proved or supplied; two marginal applications of XXXVIII are insufficient.

**Unit-1 gate:** if the assembly wrapper needs new probability machinery, export only the generic corollary and stop that branch.

### Unit 2 — Conditional deterministic normal-form bridge

Fix finitely many charts, deterministic tangential amplitudes, and zero phase data, all satisfying the existing chart-data hypotheses. Let \(x\) denote this fixed joint datum and set

\[
Z_{\mathrm{nf}}(N)=\mathcal Z^{\mathrm{glob}}(N;x),
\qquad
c_{\mu,j}=C^{\mathrm{glob}}_{\mu,j}(x).
\]

Export the specialisation

\[
\boxed{
Z_{\mathrm{nf}}(N)
 =S_{\prec(\mu,j)}(N;x)
  +c_{\mu,j}N^{-\mu}(\log N)^j
  +o\!\left(N^{-\mu}(\log N)^j\right)
}
\]

for every supported target \(\mu\in Q^{-1}\mathbb N\), \(j\le D\), as \(N\to\infty\).

Add the external-decomposition form:

\[
Z_{\mathrm{pop}}(N)=Z_{\mathrm{nf}}(N)+E(N),
\qquad
E(N)=o\!\left(N^{-\mu}(\log N)^j\right)
\]

implies the same expansion for \(Z_{\mathrm{pop}}\). An exponentially negligible residual may use the existing bridge.

If the predecessor sum vanishes and \(c_{\mu,j}\ne0\), conclude

\[
Z_{\mathrm{pop}}(N)\sim
c_{\mu,j}N^{-\mu}(\log N)^j.
\]

Use the deterministic remainder theorem directly. Do not introduce constant random variables merely to recover this result from convergence in distribution.

**Title:** “Conditional deterministic finite-chart normal-form expansion.”

**Not its title:** “Proof of `thm:expectation_expansion`.”

### Stop criterion

**Hard cap: two units total, including any proof-oriented cleanup.**

Stop earlier if either unit requires:

- a new geometric construction;
- a new probability theorem;
- a new asymptotic-series framework;
- leading-coefficient positivity or nonvanishing not already available;
- a repaired interpretation of an unresolved paper statement.

If Unit 1 consumes both units, omit Unit 2. No automatic continuation to joint observables, monomial shifts, or all-orders division. A missing optional wrapper does not block release.

## 3. Completion wording

> **Seabed complete — conditional §4 release.** The Lean formalisation, with no `sorry`, establishes the fluctuation-function and ladder-algebra results, the Taylor-tree expansion in every positive normal dimension under the declared analytic hypotheses, and a continuous-coefficient finite-cutoff stochastic extension through tangential integration and finite chart assembly. It also establishes the leading-order posterior quotient under joint data convergence, source predecessor cancellation, negligible decomposition residuals, and an almost-surely nonzero limiting denominator coefficient. The stochastic results are conditional on convergence in the stated weighted‑ℓ¹/tangential-data topologies and on an externally supplied finite-chart decomposition; they do not derive those inputs from Hypothesis I, construct a resolution atlas, or identify a Gaussian empirical-process limit. All-orders posterior division and the population expansion in the unrevised §3 remain outside this release. The normal-block, Taylor-tree, and stochastic Taylor-tree reports constitute the mathematical hand-off.

“Complete” here is a release decision about a precisely delimited scope, not a claim that every paper label has a Lean counterpart.

## Last notes to the authors

1. **Adopt or amend the replacement statements.**  
   Record whether weighted‑ℓ¹ coefficient continuity and the finite-cutoff/ordered-remainder integration theorem are the intended replacements for `prop:convergence` and `lemma:AsymInt`.

2. **Separate §4.3 into conditional analysis and model verification.**  
   State explicitly the topology of joint convergence, the fixed radius requirements, the standard-form construction, and the global residual hypothesis.

3. **Repair posterior statements at the source datum.**  
   The negligible error is remainder minus coefficient evaluated at the source data. The target coefficient enters through convergence in law. Aggregate predecessor cancellation is sufficient; individual coefficients need not vanish.

4. **State denominator nonvanishing independently.**  
   Finite-sample positivity is not enough. Any desired positivity theorem for the limiting coefficient needs its own hypotheses and proof.

5. **Specify the algebra of all-orders division before requesting formalisation.**  
   Inverse logarithms introduce an ordering issue that cannot be settled by naming an absent `lemma:division`.

6. **Rewrite §3 before opening a geometry programme.**  
   Distinguish the local normal-form analytic result from atlas construction, adapted partitions, fibre integration, and global identification.

7. **Freeze one authoritative release manifest.**  
   Reconcile the supplied main/release/Programme-S pins and identify exactly which commit and theorem inventory each report certifies. Unit numbers and module counts are different bookkeeping quantities.

**Bottom line:** there is no mathematical need to keep the autonomous prover busy. The substantial conditional §4 deliverable is finished. Hand it over; let the next substantive programme be driven by repaired author statements or a concrete upstream bridge.
