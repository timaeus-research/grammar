## Recommendation

Make **the joint law with a posterior draw** the main result of the next block. It is reachable from the present inventory, without tensor-product approximation and without a new asymptotic estimate.

My priority order is:

1. **(c): full random-field/posterior-draw convergence**;
2. **(a): the a.e. product-form iff**;
3. **a genuine quenched-to-stable corollary**, with the conditioning hypotheses stated explicitly;
4. **(b): temperature scaling, corrected for phase rescaling**;
5. **(d): random next-log statistics, later**.

I recommend the following **six units**. Units 1–3 deliver (c); units 4–6 are independent, bounded additions. No theorem-map or positivity-cleanup unit.

---

## Unit 1 — Upgrade continuous convergence from observable vectors to posterior laws

Write
```lean
abbrev Z := ℝ × (Fin d → ℝ)

posteriorMap (N : ℝ) :
    C(K, ℝ) → ProbabilityMeasure Z

limitPosteriorMap :
    C(K, ℝ) → ProbabilityMeasure Z
```
for the existing phase joint law and spatial joint face law, using `extPhase`.

### Targets

```lean
theorem continuous_limitPosteriorMap :
    Continuous limitPosteriorMap

theorem continuouslyConverges_posteriorMap
    (hN : Tendsto N atTop atTop) :
    ContinuouslyConverges
      (fun m p => posteriorMap (N m) p)
      limitPosteriorMap
```

If existing definitions or theorem interfaces require `1 < N m`, retain that hypothesis initially, then remove it by an eventual-tail argument if convenient.

### Inputs

- `movingPhaseJointLaw_tendsto`;
- `spatialJointFaceLaw_tendsto_of_uniform`;
- the sup-norm control supplied by `extPhase`;
- `continuouslyConverges_of_seq`;
- fixed-\(N\) continuity and unconditional positivity.

The sequential bridge requires convergence along **arbitrary index sequences tending to infinity**, not merely the sequence \(m \mapsto (m,p_m)\). LXXXVIII already has exactly the flexibility needed.

### Why this unit matters

It replaces “every fixed finite vector of observables” by convergence of the entire conditional posterior law. XC then becomes a consequence of a more informative theorem.

### Trap

Do not make this depend on proving `PolishSpace (ProbabilityMeasure Z)` on the pin. For the graph-law application, the Polish/tightness requirement belongs to the **phase space**. A compatible metrizable weak topology on the law-valued codomain is enough for this route, subject to the existing graph theorem’s precise signature.

---

## Unit 2 — A continuous marked-mixture operator

This is the abstract theorem that closes the kernel gap.

For \(P\) and \(Z\) Polish metric spaces, define
\[
\operatorname{sampleLift}(\Lambda)
  := \int_{P\times\mathcal P(Z)}
       (\delta_p\otimes q)\,\Lambda(d p,d q).
\]
Its output is a probability measure on \(P\times Z\).

### Targets

Lean-level schematic shape:

```lean
def sampleLift
    (Λ : ProbabilityMeasure (P × ProbabilityMeasure Z)) :
    ProbabilityMeasure (P × Z)

theorem integral_sampleLift
    (f : (P × Z) →ᵇ ℝ) :
    ∫ x, f x ∂(sampleLift Λ : Measure (P × Z))
      =
    ∫ pq, ∫ z, f (pq.1, z) ∂(pq.2 : Measure Z)
      ∂(Λ : Measure (P × ProbabilityMeasure Z))

theorem continuous_sampleLift :
    Continuous (sampleLift : _ → ProbabilityMeasure (P × Z))
```

Then define the marked mixture
\[
\operatorname{jointKernelLaw}(\mu,Q)
  = \int_P(\delta_p\otimes Q(p))\,\mu(dp)
\]
and prove
```lean
jointKernelLaw μ Q = sampleLift (graphLaw μ hQ)
```
with the appropriate measurable-map argument.

### Yes: this is reachable with `Measure.bind`

Use `Measure.bind` with
\[
(p,q)\longmapsto q.\mathrm{map}(z\mapsto(p,z)).
\]
Prove measurability and mass one, then wrap the resulting measure as a `ProbabilityMeasure`. A `Kernel` wrapper is useful API, but **not mathematically necessary** for this block.

The central analytical lemma is:

```lean
theorem continuous_integral_marked
    (f : (P × Z) →ᵇ ℝ) :
    Continuous
      (fun pq : P × ProbabilityMeasure Z =>
        ∫ z, f (pq.1, z) ∂(pq.2 : Measure Z))
```

For \(p_n\to p\), \(q_n\Rightarrow q\), split
\[
\int f(p_n,z)\,dq_n-\int f(p,z)\,dq
\]
into a moving-\(p\) term and a weak-convergence term. Tightness of the \(q_n\), plus uniform continuity on
\[
(\{p\}\cup\{p_n:n\in\mathbb N\})\times C,
\]
controls the first term.

After this lemma, continuity of `sampleLift` follows directly by testing weak convergence.

### Traps

- A bounded continuous \(f(p,z)\) need not be uniformly continuous on the whole product. The compact/tightness argument is essential.
- Do not try to prove convergence for arbitrary bounded **measurable** \(f\).
- No Stone–Weierstrass argument is needed.
- Avoid repeatedly commuting `toReal` through integrals. Keep the real integral formula separate from the ENNReal mass-one proof.

---

## Unit 3 — Random field jointly with one posterior draw

This should be the headline theorem of the block.

Let
\[
Q_m(p)=Q_{N_m}^{\operatorname{ext}p},
\qquad
Q(p)=\widetilde Q^{\operatorname{ext}p}.
\]

### Target

```lean
theorem randomField_posteriorDraw_tendsto
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (hN : Tendsto N atTop atTop) :
    Tendsto
      (fun m => jointKernelLaw (μ m) (posteriorMap (N m)))
      atTop
      (𝓝 (jointKernelLaw μ₀ limitPosteriorMap))
```

Thus
\[
\mu_m(dp)\,Q_m(p,dz)
   \Rightarrow
\mu_0(dp)\,Q(p,dz)
\quad\text{on }C(K,\mathbb R)\times Z.
\]

### Proof

1. Unit 1 gives law-valued continuous convergence.
2. `tendsto_graphLaw_of_polish` gives convergence on
   \(P\times\mathcal P(Z)\).
3. Apply `continuous_sampleLift`.

Also export the posterior-draw marginal:
\[
\int Q_m(p,\cdot)\,\mu_m(dp)
   \Rightarrow
\int Q(p,\cdot)\,\mu_0(dp).
\]

### Best primary statement

Use the **measure-level statement above**, not a statement requiring construction of random variables on an extension.

A random-variable corollary can say: if \((X_m,Z_m)\) has joint law
\(\mu_m(dp)Q_m(p,dz)\), then
\[
(X_m,Z_m)\Rightarrow \mu_0(dp)Q(p,dz).
\]
This covers the intended conditional-posterior interpretation without forcing a regular-conditional-distribution development.

### Non-claims

- This is the standard-form chart posterior, not the original-space posterior.
- It is not stable convergence relative to an external sigma-algebra merely from \(\mu_m\Rightarrow\mu_0\).
- It does not establish convergence in law of the phase field; that remains an input.

---

## Unit 4 — Close the a.e. product-form iff

Let \(\nu^\xi\) be the actual spatial marginal of \(\widetilde Q^\xi\), and let \(a(u)=\xi(P_Ju)\).

### Targets

First the missing direction:
\[
a(u)=a_0\quad\nu^\xi\text{-a.e.}
\quad\Longrightarrow\quad
\widetilde Q^\xi=\rho_{a_0}\otimes\nu^\xi.
\]

Then the clean fixed-parameter equivalence:
\[
\boxed{
\widetilde Q^\xi=\rho_{a_0}\otimes\nu^\xi
\iff
\xi\circ P_J=a_0\quad\nu^\xi\text{-a.e.}
}
\]

Finally, combine with LXXXV/LXXXVI to state independence iff essential face constancy.

### Inputs

- LXXXII disintegration;
- existing converse and strict identifiability of \(\rho_a\);
- integral congruence under a.e. equality.

### Important measure distinction

Define the base weighted face measure explicitly. If
\[
\nu^\xi(du)
 = c^{-1}J_\lambda(\xi(P_Ju))\,\sigma(du),
\]
then positivity and finiteness of \(J_\lambda\) give
\[
\nu^\xi\sim\sigma.
\]
Export that mutual absolute continuity, then transfer the a.e. condition.

But if the proposed `μ_P` **does not include \(\eta\)**, equivalence can fail where \(\eta=0\). Constancy `μ_P`-a.e. is sufficient, but need not be necessary. The iff belongs to the weighted face measure—or directly to \(\nu^\xi\).

This is a small, genuinely complete mathematical closure.

---

## Unit 5 — Quenched weak convergence and a properly stated stable transfer

The pathwise theorem alone is cheap. Pair it with the stable-kernel consequence to make this a worthwhile unit.

### Quenched target

On a probability space, assume
\[
X_m(\omega)\to X(\omega)
\quad\text{in }C(K,\mathbb R)
\quad\text{a.s.}
\]
Then
\[
Q_m(X_m(\omega))
   \Rightarrow Q(X(\omega))
\quad\text{a.s.}
\]

Prove this as an a.e. statement about convergence in `ProbabilityMeasure Z`, using Unit 1. This avoids separate exceptional sets for separate observables.

### Stable target

Let \(\mathcal G\) be an environment sigma-algebra; let \(X_m,X\) be \(\mathcal G\)-measurable. Suppose posterior draws satisfy
\[
\mathbb E[g(Z_m)\mid\mathcal G]
   =\int g\,dQ_m(X_m)
\]
for bounded continuous \(g\).

Then, for every bounded \(\mathcal G\)-measurable real \(H\),
\[
\mathbb E[H g(Z_m)]
 \longrightarrow
\mathbb E\!\left[H\int g\,dQ(X)\right].
\]

This is stable convergence to the random kernel \(Q(X)\), in the standard test-function formulation.

### Implementation boundary

It is acceptable—and probably preferable—to take the displayed conditional-law identity in its **integrated test form**, rather than build new conditional-expectation infrastructure. The proof is pathwise weak convergence followed by dominated convergence.

### Critical trap

Knowing the conditional law given **\(X_m\)** does not automatically give the displayed identity conditional on a larger \(\mathcal G\). State the full-environment conditional sampling hypothesis. Without it, do not claim \(\mathcal G\)-stable convergence.

---

## Unit 6 — Temperature scaling, with the missing phase rescaling

Candidate (b) needs correction for nonzero phase.

For the kernel convention
\[
e^{-\beta NK+\beta\sqrt N\,\xi\sqrt K},
\]
the exact identity is
\[
\boxed{
\mathcal Z_N^\beta[\eta;\xi]
 =\mathcal Z_{\beta N}^{1}[\eta;\sqrt\beta\,\xi].
}
\]
It is **not** generally \(\mathcal Z_{\beta N}^{1}[\eta;\xi]\).

### Targets in the single-log, \(\lambda=\tfrac12\) case

Using the convention
\[
\mathcal Z_N^\beta
 =N^{-1/2}\bigl(F_\beta\log N+B_\beta+o(1)\bigr),
\]
prove
\[
F_\beta[\eta;\xi]
 =\beta^{-1/2}F_1[\eta;\sqrt\beta\,\xi],
\]
\[
B_\beta[\eta;\xi]
 =\beta^{-1/2}
   \left(
     B_1[\eta;\sqrt\beta\,\xi]
     +F_1[\eta;\sqrt\beta\,\xi]\log\beta
   \right).
\]

At \(\xi=0\), these reduce to the proposed formulas.

If the theorem is already naturally parameterized by exponent \(\lambda\) and leading log degree \(q\), the corresponding formulas are
\[
F_\beta=\beta^{-\lambda}F_1(\sqrt\beta\,\xi),\qquad
B_\beta=\beta^{-\lambda}
 \bigl(B_1(\sqrt\beta\,\xi)+qF_1(\sqrt\beta\,\xi)\log\beta\bigr).
\]
Do not generalize just for this unit.

### Inputs and proof choice

- Exact kernel identity;
- LXXVII–LXXIX coefficients;
- two-term expansion and uniqueness of its coefficients.

Coefficient uniqueness is an attractive proof: it checks the expansion’s normalization without reproducing the finite-part calculation. Retain \(\beta>0\).

---

## Why defer (d)?

**After (a)/(b), and after the posterior-draw theorem.**

The missing issue is not randomization; it is the deterministic uniform second-order theorem in the **correct topology**.

Before attempting the random theorem, one needs a result of the form
\[
\sup_{p\in C}
\left|
\log N\left(A_N(p)-\frac{F_g(p)}{F(p)}\right)
-\frac{F(p)B_g(p)-F_g(p)B(p)}{F(p)^2}
\right|\to0
\]
on compact subsets \(C\) of a specified coefficient-family parameter space, together with continuity of the limiting correction.

Two substantive traps:

1. Uniform Taylor-tree remainder on data balls is not automatically uniform remainder after spatial assembly, finite-part extraction, and division by the normalizer.
2. Pointwise positivity of \(F\) does not provide a uniform lower bound on arbitrary bounded coefficient balls. Compactness plus continuity does; a ball may require an explicit nondegeneracy assumption.

Once that deterministic theorem exists, the random result should be another application of the continuous-convergence/graph-law machinery. Do not spend this block trying to infer it from scalar continuity of \(B\).

---

## Positivity: exactly what can disappear now

For every theorem whose phases are continuous and whose other hypotheses match `origPhaseIntegral_pos`:

- delete explicit hypotheses
  ```lean
  hZ : ∀ m, 0 < origPhaseIntegral ...
  ```
- delete separate fixed-\(N\) normalizer nonvanishing assumptions;
- delete phase-smallness or large-\(N\) assumptions **when their sole role was proving positivity**;
- do this for constant phases, `extPhase p`, continuous coefficient-family phases, and continuous moving phases.

Retain:

- nonnegative continuous \(\eta\) and positive face weight;
- the standing geometric/kernel assumptions;
- temperature positivity where required;
- large-\(N\) assumptions used by asymptotic estimates rather than normalization.

For LXXXVIII’s **merely measurable** moving phases, the continuous-phase positivity theorem does not directly remove all-\(m\) positivity. Use `origPhaseIntegral_eventually_pos` and work on a tail. Removing the all-\(m\) hypothesis from a globally defined probability-law sequence may additionally require a harmless totalized definition for the finitely many exceptional indices.

Fold these changes into the relevant theorem edits; they should not consume a headline.

**Bottom line:** six units give a full posterior-draw transfer, an a.e. independence characterization, a genuine stable-kernel consequence, and a corrected second-order temperature regression—without reopening the deferred geometric bridge or gambling on unproved uniform next-log control.
