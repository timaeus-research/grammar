## Recommendation

The next campaign should close the **remaining conditional analytic/probabilistic interfaces**, rather than attempt another large geometric existence theorem.

I would fund **seven units**, in this order:

| Rank | Unit | Main deliverable |
|---|---|---|
| 1 | Exact-core adapter | Certified box data become the actual pulled-back core integral |
| 2 | Expected remainder | A correct expectation-level bridge, preferably from a pointwise exponential-moment bound |
| 3 | Compact base I | Mass-preserving atomic approximation and partition-independent bounds |
| 4 | Compact base II | Gaussian identities and interpolation on a compact base |
| 5 | Strict moment thresholds | Sharp strict inequalities for scalar and finite-mixture moments |
| 6 | Conditional empirical assembly | Distributional/expectation conclusions with the correct random coefficient |
| 7 | Bilocal boundary | Complete the critical-line classification, if the existing integral is exactly the model below |

Units 1–2 are the paper-facing priority. Units 3–5 are a coherent, worthwhile extension. Unit 6 should be predominantly assembly, not new machinery. Unit 7 is the expendable unit.

Throughout, theorem signatures below are **schematic**: existing project definitions should be reused. I cannot inspect the pinned Mathlib checkout here, so I distinguish reliable API names from proposed project declarations.

---

## 1. Exact-core adapter: close the representation gap without removing units

### Target

Introduce a small certificate expressing that an existing pulled-back core integral is **already** in the exact coordinates required by the box theorem.

For a direct box core, its fields should include:

- equality of the restricted integration measures, or equality of domains up to null sets;
- the exact phase identity;
- the exact amplitude identity;
- the relevant measurability/integrability hypotheses;
- the existing coefficient/TanCertificate data.

Schematically:

```lean
theorem chartCoreIntegral_eq_boxIntegralFin
    (hdom : μ.restrict core = volume.restrict box)
    (hphase : phase N ξ =ᵐ[volume.restrict box] standardPhase N ξ)
    (hamp : amplitude =ᵐ[volume.restrict box] standardAmplitude)
    ... :
    chartCoreIntegral ... = boxIntegralFin ...
```

For a second adapted-coordinate map, require its **proved change-of-variables identity** as input. Do not make this adapter reprove a general substitution theorem.

Then obtain:

```lean
theorem assembled_core_expansion_of_exactBoxCertificates
    (cover : ResolutionCover ...)
    (cert : ∀ i, ExactBoxCoreCertificate ...)
    ... :
    -- existing assembled expansion, now for the actual core integrals
```

The substantive gain is that the Taylor-tree output is no longer attached to a separately defined model integral.

### Positive units: the honest boundary

If
\[
K\circ\Phi(u)=a(u)u^{2k},
\]
then \(a\) cannot simply be absorbed into a fixed observable:
\[
e^{-\beta N a(u)u^{2k}}
=
e^{-\beta N u^{2k}}\,
e^{-\beta N(a(u)-1)u^{2k}}.
\]
The second factor is \(N\)-dependent. An existing theorem for a fixed coefficient family does not thereby apply uniformly in \(N\).

Likewise, saying “absorb it into the phase” means **generalising the phase theorem**, not instantiating the existing exact-monomial theorem.

What is provable now:

1. the exact-monomial adapter;
2. a unit-bearing adapter **given a certified substitution** that produces the exact phase and an admissible transformed domain/amplitude;
3. population comparison estimates from \(0<a_0\le a\le a_1\), where the integrand is nonnegative.

The comparison estimates give orders, not the exact leading coefficient or empirical expansion.

The proposed substitution
\[
v_j=u_j a(u)^{1/(2k_j)}
\]
requires \(k_j>0\), positivity and suitable regularity of \(a\), local invertibility, and control of the image domain. Even when locally valid, it generally sends a box to a non-box. The fluctuation datum must also transform correctly.

**Stop rule:** land the exact adapter. Do not open analytic unit removal or compatible analytic localisation during this unit.

**Inputs:** existing cover/substitution results, `MeasureTheory.integral_congr_ae`, and the project’s box expansion. No new Hironaka declaration is needed.

---

## 2. Expected remainder: use exponential moments, not a bare bad-event probability

The proposed estimate
\[
E|\mathrm{Rem}_n|
\le e^{-\beta n\kappa/2}\int g+\|F\|P(\mathrm{bad})
\]
is generally false without a deterministic bound for the integrand on the bad event. The empirical exponential may be very large precisely there.

### First deliverable: a generic good/bad theorem

If
\[
|R_n|\mathbf1_{\mathrm{good}}\le A e^{-an},
\qquad
|R_n|\mathbf1_{\mathrm{bad}}\le B_n\mathbf1_{\mathrm{bad}},
\]
then
\[
E|R_n|\le A e^{-an}+B_nP(\mathrm{bad}).
\]

Also provide the Hölder version, for \(q>1\):
\[
E|R_n|
\le A e^{-an}
+\|R_n\|_{L^q}P(\mathrm{bad})^{1-1/q}.
\]

These make the missing hypothesis explicit. If \(B_n\) grows exponentially, the tail exponent must beat that growth.

### Preferred deliverable: pointwise annealed control

On a gap \(S\), suppose \(K=\phi^2\ge\kappa\), \(|a|\le g\), and, for almost every \(y\),
\[
E\exp\!\bigl(\beta\sqrt n\,\phi(y)\xi_n(y)\bigr)
\le
\exp\!\bigl(\theta\beta nK(y)\bigr),
\qquad 0\le\theta<1.
\]
Then
\[
E\left|
\int_S a(y)e^{-\beta nK(y)+\beta\sqrt n\phi(y)\xi_n(y)}\,dy
\right|
\le
e^{-(1-\theta)\beta n\kappa}\int_S g.
\]

This avoids both a supremum tail and the exceptional-dataset problem. Prove the nonnegative/enorm bound first; obtain Bochner integrability as a consequence when appropriate.

A useful specialisation is the explicit pointwise sub-Gaussian hypothesis
\[
E e^{t\xi_n(y)}\le e^{\sigma^2t^2/2}.
\]
It gives \(\theta=\beta\sigma^2/2\), hence exponential decay when
\[
\beta\sigma^2<2.
\]

For independent bounded centered observations, the pointwise hypothesis can be supplied by scalar Hoeffding bounds. Notice that **pointwise** bounds suffice here; they do not establish a tail bound for \(\sup_y|\xi_n(y)|\).

### Mathlib caution

I would not certify the exact signature or availability of  
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` in your pinned checkout without checking it. The initial audit should search the actual source for:

```text
measure_sum_ge
iIndepFun
HasSubgaussianMGF
Hoeffding
```

The main unit should depend only on an explicit exponential-moment inequality, Tonelli/Fubini, and the norm-of-integral bound. This insulates it from concentration-API details.

**Stop rule:** one generic annealed theorem and one bounded-observation specialisation. No chaining, covering-number theory, or generic empirical-process supremum inequality.

---

## 3. Compact base I: atomic approximation and deterministic bounds

**Yes, this is worth doing now.** It removes the artificial finite-base restriction without depending on the unresolved geometry.

Assume:

- \(K\) compact metric;
- \(\rho\) a finite Borel measure;
- \(M=\rho(K)>0\);
- \(\lambda,\beta>0\).

### Build a reusable finite quantisation theorem

For any \(\varepsilon>0\), construct a measurable finite-range map \(q_\varepsilon:K\to K\) with
\[
d(x,q_\varepsilon(x))<\varepsilon.
\]
Set
\[
\rho_\varepsilon=(q_\varepsilon)_*\rho.
\]

This is automatically atomic and mass-preserving. A finite ball cover and a first-hit Borel partition suffice; representatives need not belong to their partition cells.

A clean project declaration is:

```lean
theorem exists_measurable_finiteRange_approx
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : K → K,
      Measurable q ∧
      (Set.range q).Finite ∧
      ∀ x, dist x (q x) < ε
```

For \(\varepsilon_n\to0\), prove
\[
\int f\,d\rho_n\longrightarrow\int f\,d\rho
\quad(f\in C(K,\mathbb R)),
\qquad
\rho_n(K)=M.
\]

I would **build this small lemma unless a checkout search reveals an exact match**. A theorem saying finitely supported measures are dense may not provide the required explicit mass-preserving construction.

Reliable ingredients include `Measure.map`, `Measure.dirac`, `MeasureTheory.integral_map`, compactness/uniform continuity, and dominated convergence.

### Deterministic package

Define directly
\[
D_\rho(g)=\int_K S_\lambda(g(x))\,d\rho(x).
\]
Prove positivity, finiteness, and the proposed bound
\[
|\log D_\rho(g)|
\le |\log M|+C_{\lambda,\beta}
+\frac{\beta}{2}\|g\|_\infty^2+2\lambda\|g\|_\infty.
\]

For a continuous positive-semidefinite covariance kernel \(C\), with \(C(x,x)\le c\), prove the compact analogue
\[
0\le V_\rho(g)\le c\left(\frac{2\lambda}{\beta}
+\frac{\|g\|_\infty^2}{4}\right).
\]

Use the finite theorem’s exact normalisation of \(V\).

Finally prove convergence of \(D,\log D,H,V\) under the constructed atomic approximations, for each fixed \(g\).

**Trap:** convergence is not uniform over the entire sup-norm ball of \(C(K)\). Such a ball is not generally equicontinuous.

**Stop rule:** no general weak-convergence framework and no arbitrary-base extension beyond compact metric spaces.

---

## 4. Compact base II: finite-dimensional Gaussian laws and identities

### The clean law statement

Let
```lean
G : Ω → C(K, ℝ)
```
be measurable, and require explicitly
\[
\int \|G(\omega)\|_\infty^2\,dP(\omega)<\infty.
\]

For finite-dimensional Gaussianity, use evaluation pushforwards:

```lean
∀ (m : ℕ) (x : Fin m → K),
  P.map (fun ω => fun i => G ω (x i)) = gaussianLawFor x
```

Here `gaussianLawFor x` is the measure induced by your **existing axiom-clean `gaussianVector` construction**, with covariance matrix
\[
B_x(i,j)=C(x_i,x_j).
\]

If the existing Gaussian object is a random variable \(Y_x\) on a source measure \(\nu_x\), write the right side as `νx.map Yx`, or use `ProbabilityTheory.IdentDistrib`.

This is preferable to requiring a single common Gaussian source space. Allow repeated evaluation points and singular covariance matrices. No independence between evaluations is intended.

A small record packaging \(C\), its continuity, the finite-vector witnesses, and these map equalities is reasonable. Do not redefine “Gaussian vector” via a new unrelated predicate.

### Identities

To make the normalisation explicit, consider the posterior on \(K\times(0,\infty)\) proportional to
\[
r^{\lambda-1}e^{-\beta r+\beta g(x)\sqrt r}\,\rho(dx)\,dr.
\]
With
\[
H(g)=\langle g(x)\sqrt r\rangle,
\]
and
\[
V(g)=
\langle rC(x,x)\rangle
-\langle\sqrt{rs}\,C(x,y)\rangle_{\text{two replicas}},
\]
the targets are
\[
EH(G)=\beta EV(G),
\qquad
E\log D(G)\ge\log D(0).
\]

For \(\Psi(t)=E\log D(\sqrt t\,G)\), prove the integrated interpolation identity
\[
\Psi(1)-\Psi(0)
=
\frac{\beta^2}{2}\int_0^1 EV(\sqrt t\,G)\,dt.
\]
Translate these formulas to the existing finite definitions if their conventions differ.

Transfer from atomic approximations using the bounds from Unit 3 and
\[
|H(g)|\le C(1+\|g\|_\infty^2).
\]
Use the **integrated** identity first; do not require a pointwise derivative theorem at \(t=0\).

**Non-claims:** no construction of the Gaussian process, no Fernique theorem, and no assertion that finite-dimensional Gaussianity alone supplies the explicit moment hypothesis by already available infrastructure.

**Stop rule:** finish by dominated convergence from finite identities. Do not formalise abstract Gaussian measures on Banach spaces.

---

## 5. Strict \(p\)-moment thresholds

For
\[
S_\lambda(a)=\int_0^\infty
t^{\lambda-1}e^{-\beta t+\beta a\sqrt t}\,dt,
\]
prove the advertised upper bound for \(0<\eta<1\):
\[
S_\lambda(a)\le
\Gamma(\lambda)(\beta\eta)^{-\lambda}
\exp\!\left(\frac{\beta a_+^2}{4(1-\eta)}\right).
\]

Prove a quantified lower bound: there are \(A,C>0\) such that
\[
a\ge A\implies
S_\lambda(a)\ge
Ca^{2\lambda-1}e^{\beta a^2/4}.
\]

For \(X\sim N(0,v)\), \(v>0\), and \(p>1\), conclude:
\[
p\beta v<2\implies E[S_\lambda(X)^p]<\infty,
\]
\[
p\beta v>2\implies E_+[S_\lambda(X)^p]=\infty.
\]

For a finite nonnegative mixture
\[
D(G)=\sum_i\rho_iS_\lambda(G_i),
\]
put
\[
c_*=\max_{\rho_i>0}B_{ii}.
\]
Then the same strict threshold holds with \(v=c_*\). Correlations do not affect this argument.

Also obtain compact-base **sufficiency** when \(C(x,x)\le c\), using
\[
\left(\int S\,d\rho\right)^p
\le M^{p-1}\int S^p\,d\rho
\]
and Tonelli. Do not infer compact-base necessity merely from infinite pointwise \(p\)-moments; that inference is invalid.

### Boundary policy

At \(p\beta v=2\), the scalar polynomial factor matters:
\[
p(2\lambda-1)<-1
\]
is the predicted finite side. Leave equality out of the headline unless matching estimates have actually been proved.

Most importantly:

> A finite \(p\)-moment of the limiting \(D(G)\) does not establish a uniform \(p\)-moment bound for the empirical approximants.

This unit identifies plausible UI regimes; it does not discharge empirical UI.

**Stop rule:** strict thresholds first. Boundary classification is optional and must not delay Unit 6.

---

## 6. Conditional empirical assembly—and the correct Hironaka connection

There is a useful conditional theorem here, but **not** generally convergence to the population coefficient.

Let
\[
A_n=\frac{n^\lambda}{(\log n)^{m-1}},
\qquad n\ge2,
\]
and suppose the certified empirical core theorem gives
\[
A_n Z_n^{\mathrm{core}}\Rightarrow L,
\]
where \(L\) is the assembled Gaussian coefficient.

With the appropriate scaled remainder convergence, conclude
\[
A_nZ_n\Rightarrow L.
\]

If the normalised core sequence is UI and
\[
E|A_n\mathrm{Rem}_n|\to0,
\]
then
\[
E[A_nZ_n]\to EL.
\]

Unit 2 makes the latter remainder condition automatic for polynomial-logarithmic \(A_n\). Use the already-landed law-level UI bridge rather than proving another one.

### Exponents

If \(0<L<\infty\) almost surely and \(Z_n>0\), derive
\[
\frac{\log Z_n}{\log n}\longrightarrow-\lambda
\quad\text{in probability}.
\]
The finite initial segment \(n<2\) should be handled by arbitrary harmless definitions.

If additionally \(0<EL<\infty\) and expectation convergence holds, derive
\[
E Z_n\sim EL\,n^{-\lambda}(\log n)^{m-1}.
\]

These are the right places to connect to
`laplaceTheta_of_analyticOnNhd_nonneg_of_Q`, keeping `Q n` explicit:

- it supplies a population exponent statement;
- the certified empirical presentation must separately supply a compatible exponent pair;
- an existing uniqueness-of-orders lemma can identify the pairs.

Do not pretend that the population exponent theorem itself supplies the empirical presentation or phase-field CLT.

### Essential correction

In general,
\[
EL\ne C_{\mathrm{population}}.
\]
Even your landed denominator formula already exhibits the Gaussian inflation of the expectation relative to \(D(0)\). Thus the proposed phrase

> “UI implies convergence to the population Laplace coefficient”

must become

> “UI implies convergence to the expectation of the limiting empirical coefficient.”

Equality with the population coefficient needs an additional theorem.

**Stop rule:** an assembly wrapper with all geometric and CLT assumptions visible. No new geometric existence claim.

---

## 7. Bilocal boundary: a small closure unit

If the existing bilocal integral is exactly
\[
I_\lambda(a,b,h)=
\int_0^\infty\!\!\int_0^\infty
t^{\lambda-1}s^{\lambda-1}
e^{-at-bs+h\sqrt{ts}}\,dt\,ds,
\qquad\lambda>0,
\]
then complete its classification:

- \(a,b>0,\ h<2\sqrt{ab}\): finite;
- \(a,b>0,\ h>2\sqrt{ab}\): infinite;
- \(a,b>0,\ h=2\sqrt{ab}\): finite iff \(\lambda<1/4\);
- \(a\le0\) or \(b\le0\): infinite.

The last assertion includes the non-obvious case \(a=0,b>0,h<0\): integrating in \(t\) produces an \(s^{-\lambda}\) factor, leaving an \(s^{-1}\) divergence at zero.

At the critical line, \(t=x^2,s=y^2\) gives a Gaussian transverse to
\[
\sqrt a\,x=\sqrt b\,y,
\]
with longitudinal power \(r^{4\lambda-2}\).

These conclusions depend on the displayed equal-power model. Unequal powers require a different classification.

**Stop rule:** drop this unit if it requires a general polar-coordinate or cone-integration library. Strip estimates and elementary substitutions should suffice.

---

## Text and mirror corrections

I would make the following edits now, before the new proofs land.

1. **Repair the expected-remainder paragraph.**  
   Distinguish pathwise good-event bounds, bounds with bad-event amplitude control, and direct annealed exponential-moment bounds.

2. **Separate “core represented by a box” from “core estimated by a box theorem.”**  
   CXXXVIII supplies the former integral only as a pulled-back core. Unit 1 supplies the exact representation under a certificate; it does not construct that certificate.

3. **State explicitly that a positive phase unit is not a fixed observable factor.**  
   Avoid wording suggesting that the coefficient-family interface already removes \(a(u)\).

4. **Correct “population coefficient” to “expected limiting empirical coefficient.”**

5. **Keep moment and UI claims distinct.**  
   Integrability of the Gaussian limit—even a strict \(p\)-moment margin—is not uniform integrability of the empirical sequence.

6. **After Units 3–4, advertise the compact-base result conditionally:**  
   “for a measurable \(C(K)\)-valued centered Gaussian field with finite second sup-norm moment.” Do not abbreviate this to “for every Gaussian field.”

7. **Reduce, rather than further densify, the mirror remarks.**  
   Add one short interface table:
   - proved analytic transformation;
   - supplied presentation certificate;
   - supplied probabilistic convergence/tail hypothesis.  
   Refer remarks to that table.

## Campaign-wide stop rule

Stop once the paper can honestly say:

> Given an exact certified empirical presentation and the stated field-limit and moment hypotheses, the chart cores assemble into the global limiting law; an explicit annealed hypothesis controls the expected remainder; UI transfers the limit to expectations.

Do **not** expand this campaign into analytic partition-of-unity existence, positive-unit removal with compatible boxes, a phase-field CLT, or a claim that Hironaka alone closes those interfaces. Those remain genuine subsequent campaigns.
