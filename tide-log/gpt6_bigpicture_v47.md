## Recommendation

**Take R1, but make the main theorem about finite families of arbitrary bounded continuous observables.** Prove the moving-phase joint weak convergence first, so there is a useful new theorem even if the abstract transfer overruns.

Two adjustments make R1 substantially cleaner:

1. Express continuous convergence using a **product filter**, rather than only a diagonal sequence condition.
2. Prove uniform convergence on compact sets by a **finite-cover argument**. You need neither an extended CMT already in Mathlib nor a product-measure convergence theorem.

I would not use R2: it replaces one missing lemma with extra topology on the index space. R3 is the right stopping point, but not the preferred final deliverable.

---

## 1. The deterministic theorem should use the full joint law

Write, schematically,
\[
Q_N(p)=\operatorname{Law}_{Q_N^{\operatorname{ext}p}}(NK,u),
\qquad
Q_\infty(p)=\widetilde Q^{\operatorname{ext}p},
\]
where \(p\in C(K,\mathbb R)\). Keep the existing model/admissibility hypotheses explicit.

The first target is:

```lean
-- Schematic names for the existing joint probability measures.
theorem jointLaw_tendsto_of_phase_tendsto
    (hN : Tendsto N atTop atTop)
    (hp : Tendsto p atTop (𝓝 p₀))
    -- positivity/admissibility hypotheses required by Q
    :
    Tendsto (fun m => Q (N m) (p m)) atTop (𝓝 (Qinf p₀))
```

This follows directly from LXXVI and LXXXII. For each
`g : (ℝ × (Fin d → ℝ)) →ᵇ ℝ`, decompose
\[
Q_{N_m}(p_m)(g)-Q_\infty(p_0)(g)
=
[Q_{N_m}(p_m)(g)-Q_{N_m}(p_0)(g)]
+
[Q_{N_m}(p_0)(g)-Q_\infty(p_0)(g)].
\]

For LXXVI, the varying observable on the original integration domain is
\[
u\longmapsto g(N_mK(u),u).
\]
Its bound is uniformly \(\|g\|_\infty\); its dependence on \(m\) is explicitly allowed.

**Thus there is no reason to restrict this theorem to the generators.** The generators have already done their job in proving LXXXII.

For a finite family `g : Fin r → E →ᵇ ℝ`, define
```lean
def observableVector (q : ProbabilityMeasure E) : Fin r → ℝ :=
  fun i => ∫ z, g i z ∂(q : Measure E)
```
and set
\[
T_m(p)=\bigl(Q_{N_m}(p)(g_i)\bigr)_i,\qquad
T(p)=\bigl(Q_\infty(p)(g_i)\bigr)_i.
\]

Then moving-phase convergence gives the required convergence of these vectors coordinatewise.

---

## 2. Use this exact form of continuous convergence

For the abstract theorem, use:

```lean
def ContinuouslyConverges
    (Tn : ℕ → P → V) (T : P → V) : Prop :=
  ∀ p : P,
    Tendsto
      (fun q : ℕ × P => Tn q.1 q.2)
      (atTop ×ˢ 𝓝 p)
      (𝓝 (T p))
```

In metric language, this says:

> For every \(p\) and every \(\varepsilon>0\), there are \(n_0\) and a neighborhood \(U\) of \(p\) such that  
> \(n\ge n_0,\ q\in U \Longrightarrow d(T_n(q),T(p))<\varepsilon.\)

This is the convenient form for the abstract proof.

### Sequential form for the deterministic application

The moving-phase theorem naturally supplies:

```lean
∀ (p : P) (k : ℕ → ℕ) (x : ℕ → P),
  Tendsto k atTop atTop →
  Tendsto x atTop (𝓝 p) →
  Tendsto (fun j => Tn (k j) (x j)) atTop (𝓝 (T p))
```

Use this rather than only
```lean
∀ p x, Tendsto x atTop (𝓝 p) →
  Tendsto (fun n => Tn n (x n)) atTop (𝓝 (T p))
```
in the intermediate API. The latter is sufficient in this setting, but subsequence filling is needless Lean work.

For metrizable \(P\), the arbitrary-index sequential formulation implies the product-filter formulation. If the first-countable filter API is awkward on the pin, the contradiction proof is short: failure gives \(k_j\ge j\) and \(d(x_j,p)<1/(j+1)\) violating a fixed output neighborhood.

### Compact-uniform lemma

Prove:

```lean
theorem ContinuouslyConverges.tendstoUniformlyOn
    (hcc : ContinuouslyConverges Tn T)
    (hT : Continuous T)
    (hC : IsCompact C) :
    TendstoUniformlyOn Tn T atTop C
```

For each \(p\in C\), combine:

- eventual closeness of \(T_n(q)\) to \(T(p)\) on a neighborhood of \(p\);
- continuity of \(T\), making \(T(q)\) close to \(T(p)\).

Take a finite subcover and a common index threshold.

**This avoids the sequential-compactness machinery entirely.**

It is also worth packaging the small metric-space fact that continuous convergence implies continuity of \(T\). Indeed, the local eventual bound passes to the pointwise limit at each fixed \(q\). This lets the deterministic theorem establish limit continuity without reopening the limiting density’s dominated-convergence proof.

---

## 3. The abstract random transfer target

Use probability laws as the primary API, not random variables on a common sample space.

Let \(P\) be Polish and metrizable, and \(V=\mathrm{Fin}\ r\to\mathbb R\). Assume:

```lean
hμ  : Tendsto μ atTop (𝓝 μ₀)
hTm : ∀ n, Measurable (Tn n)
hT  : Continuous T
hcc : ContinuouslyConverges Tn T
```

The conclusion is
\[
(\mathrm{id},T_n)_\#\mu_n
\ \Longrightarrow\
(\mathrm{id},T)_\#\mu_0.
\]

For a pin-independent statement layout, introduce a tiny local `push` wrapper around `ProbabilityMeasure.map`, accepting a measurable map. Then the target reads:

```lean
theorem tendsto_graphLaw_of_continuouslyConverges
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (hTm : ∀ n, Measurable (Tn n))
    (hT : Continuous T)
    (hcc : ContinuouslyConverges Tn T) :
    Tendsto
      (fun n =>
        push (μ n) (fun p => (p, Tn n p))
          (measurable_id.prodMk (hTm n)))
      atTop
      (𝓝
        (push μ₀ (fun p => (p, T p))
          (measurable_id.prodMk hT.measurable)))
```

Here `push` is only an API wrapper, not an additional theorem assumption. I would not guess the exact argument order of `ProbabilityMeasure.map` on your pin.

### Proof using precisely your inventory

1. The convergent sequence of input laws, together with its limit, is compact.
2. Hence it is uniformly tight on Polish \(P\).
3. Fixed-map CMT handles \(p\mapsto(p,T(p))\).
4. For a bounded continuous test \(f\) on \(P\times V\), put
   \[
   f_n(p)=f(p,T_n(p)),\qquad f_\infty(p)=f(p,T(p)).
   \]
   These have continuous convergence, hence uniform convergence on any compact \(C\).
5. Compare their integrals under the **same** \(\mu_n\):
   \[
   \left|\int f_n\,d\mu_n-\int f_\infty\,d\mu_n\right|
   \le
   \sup_C|f_n-f_\infty|
   +2\|f\|_\infty\,\mu_n(C^c).
   \]

This last formulation is important: it avoids claiming that a bounded continuous \(f\) is uniformly continuous on the whole product, and avoids proving tightness of the output laws first.

You can prove the engine with an explicit uniform-tightness hypothesis, then discharge that hypothesis in the Polish corollary.

---

## 4. What the instantiated random theorem actually says

For random phases \(X_m\Rightarrow X\) in \(C(K,\mathbb R)\), and any fixed finite family \(g_i\in\mathrm{BCF}(E,\mathbb R)\),
\[
\left(X_m,\,
 \bigl[Q_{N_m}(X_m)(g_i)\bigr]_{i<r}\right)
\Rightarrow
\left(X,\,
 \bigl[Q_\infty(X)(g_i)\bigr]_{i<r}\right).
\]

This is a substantial random-environment theorem: **joint convergence of the environment and finitely many conditional observables**.

Use general bounded continuous \(g_i\) in the headline. Add generator specializations as short corollaries.

One useful additional corollary is the mixed annealed identity
\[
\int h(p)\,Q_{N_m}(p)(g)\,d\mu_m(p)
\longrightarrow
\int h(p)\,Q_\infty(p)(g)\,d\mu(p)
\]
for bounded continuous \(h\).

To derive it from the graph-law theorem, clip the output coordinate outside \([-\|g\|,\|g\|]\). The naive product test \((p,v)\mapsto h(p)v_i\) is not globally bounded.

### Do not overstate the result

This is not automatically:

- almost-sure quenched convergence;
- stable convergence relative to an arbitrary underlying sigma-algebra;
- a full theorem about the jointly sampled environment and posterior draw.

The last is a reasonable later extension, but needs kernel measurability and a further joint-law argument. No independence assumption is needed for the finite-observable theorem.

---

## 5. Phase space and measurability traps

### Use \(C(K,\mathbb R)\), not global bounded continuous functions

Take
\[
K=\{u:\mathrm{Fin}\ d\to\mathbb R:\forall i,\ 0\le u_i\le1\}.
\]

Install the compactness instance for the subtype, then check:

```lean
#synth NormedAddCommGroup C(K, ℝ)
#synth CompleteSpace C(K, ℝ)
#synth SecondCountableTopology C(K, ℝ)
#synth PolishSpace C(K, ℝ)
```

The first three are the substantive ingredients. If the fourth does not synthesize, bridge complete metrizability and second countability locally using the actual theorem on the pin. **Do not turn this into a global compact-open function-space project.**

Extend phases by coordinatewise clamping:
\[
r(x)_i=\max(0,\min(1,x_i)),\qquad \operatorname{ext}(p)=p\circ r.
\]
This is continuous, agrees with \(p\) on \(K\), and
\[
|\operatorname{ext}(p)(x)-\operatorname{ext}(q)(x)|
\le \|p-q\|_\infty.
\]

### Prove fixed-\(N\) continuity, not merely measurability

A good companion theorem is:

```lean
theorem continuous_jointLaw_fixed_N :
  Continuous (fun p : C(K, ℝ) => Q N p)
```

It implies measurability of all \(T_m\), and also of the probability-law-valued map if later needed.

For fixed \(N\), the energy coordinate is bounded on the integration box. Consequently the phase-dependent exponential weight has locally uniform domination in \(p\). The normalization is positive. This is an ordinary fixed-\(N\) normalized-integral continuity argument.

Alternatively, a fixed-\(N\) density-ratio estimate gives continuity in a stronger metric. Its constants may grow with \(N\); that is harmless here.

**Do not use those growing constants for the asymptotic moving-phase theorem.**

### The exponential-moment issue

A bound involving
\[
e^{\beta\|p_m-p\|_\infty\sqrt y}
\]
cannot be integrated merely because the energy laws are tight. Tightness does not supply exponential moments.

For the moving-phase theorem, invoke LXXVI as the black box that already handles this. For a new direct domination argument, use an explicit Gaussian-tail envelope, for example
\[
-\beta y+\beta M\sqrt y
\le -\tfrac{\beta}{2}y+\tfrac{\beta M^2}{2},
\]
with \(\beta>0\), along with the relevant polynomial weight. Uniformity must be over a **bounded phase ball**.

### Generator boundedness

On energy space \(\mathbb R\), \(e^{-sy}\) is not bounded for \(s>0\). Use your existing
\[
e^{-(sy^++ty^-)}F(u)
\]
generators, or \(e^{-sy^+}F(u)\) when exploiting nonnegative support. Do not accidentally bundle \(e^{-sy}\) as a bounded continuous function on all of \(\mathbb R\).

---

## 6. A five-unit cap

| Unit | Deliverable |
|---|---|
| **1** | Compact phase-space infrastructure and **moving-phase joint weak convergence** for arbitrary bounded continuous tests. |
| **2** | Fixed-\(N\) phase continuity/measurability; finite-observable maps and arbitrary-index continuous convergence. |
| **3** | Product-filter continuous convergence: compact-uniform lemma, sequential bridge, and limit continuity. |
| **4** | Abstract tight-input graph-law transfer, then its Polish corollary. |
| **5** | Random-field finite-observable theorem, generator specializations, and mixed annealed corollary. |

If a unit must be cut, stop after the deterministic core and its continuity companions. Do not substitute an unproved “extended CMT assumption” and present that as the random-field result.

The a.e. product-form iff is a good independent next theorem, but I would not let it displace this transfer once units 1–4 are in place.

---

## 7. Independent check for LXXXIV

**The Euler-constant value is correct under the stated normalization**, but I would not spend a unit formalizing it unless the half-argument gamma-derivative identity is already nearby.

A more independent and less special-function-heavy check is the exact finite-\(N\), zero-phase reduction. For \(\beta,N>0\),
\[
\mathcal Z_N[1;0]
=\int_0^1(-\log t)e^{-\beta Nt^2}\,dt
\]
and hence
\[
\mathcal Z_N[1;0]
=
\frac1{4\sqrt N}
\left[
\log N\int_0^N y^{-1/2}e^{-\beta y}\,dy
-\int_0^N(\log y)y^{-1/2}e^{-\beta y}\,dy
\right].
\]

This checks independently:

- the \(1/4\);
- the sign of the logarithmic moment;
- the normalization by \(\log N\), rather than \(\log(\beta N)\);
- both coefficients through explicit incomplete integrals.

Taking the limits gives
\[
F_\beta(0,1)=\frac{\sqrt\pi}{4\sqrt\beta},
\qquad
B_\beta(0,1)
=\frac{\sqrt\pi}{4\sqrt\beta}
 \bigl(\log\beta+\gamma_E+2\log2\bigr),
\]
using \(\psi(1/2)=-\gamma_E-2\log2\).

An even cheaper formal regression is the temperature-scaling dictionary:
\[
F_\beta=\beta^{-1/2}F_1,\qquad
B_\beta=\beta^{-1/2}(B_1+F_1\log\beta),
\]
from the exact identity \(\mathcal Z_N^\beta=\mathcal Z_{\beta N}^{1}\).

**Priority:** exact reduction or scaling check as a small addition; no dedicated Euler-constant unit ahead of the random transfer.
