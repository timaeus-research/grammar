**Verdict: A–C close the fixed-index deterministic continuity item**, based on the supplied statements and proof descriptions. This is a statement-level audit, not an independent inspection of the commit or of #144.

## 1. Closure audit

### (i) Order: correct, and sufficient rather than claimed optimal

The required order is
```lean
pieceOrder p μ :=
  ∑ i, depthOf (hA p) (kA p) (cutoffOf (hA p) μ) i
```
because the rectangular derivative requirements have coordinatewise depth `depthOf …`, and total Fréchet derivatives through their sum control those mixed derivatives.

Two qualifications:

- In the paper, write
  \[
  R_p(\mu)=\sum_i p_{p,i}(\mu),\qquad
  p_{p,i}(\mu)=2k_{p,i}L_{p,\mu}-h_{p,i}.
  \]
  The cutoff is **piece-dependent**. If Lean uses natural subtraction, the identification with this integer expression uses the canonical-cutoff depth inequalities.
- This is the order used by the canonical construction at \(\mu\), **not a minimal regularity theorem**.

Bounding the fixed amplitude \(\eta=\mathrm{amp}_s\) through the same order is correct: Leibniz requires its derivatives through \(R_p\). Those bounds are auxiliary constants, uniform in \(s\) by compactness and smoothness of the fixed resolved data. They are not additional convergence assumptions.

The composition estimate may use outer derivatives through \(R_p+1\) to obtain Lipschitz control of the outer \(R_p\)-jet. That is harmless: the outer function is fixed and smooth; it does **not** increase the convergence order required of the branch fields.

### (ii) Compact chart images: correct

Your hypothesis controls ambient derivatives on
```lean
chartImage p = { Tm p s v | s ∈ Base, v ∈ closedBox da a }
```
and hence controls the \(v\)-jets after pullback **uniformly in \(s\)**. This is exactly sufficient for the parameter integral. No derivatives in \(s\), and no wall matching, are needed.

It is potentially **stronger** than necessary: only derivatives in the directions of `affineLin` enter the cube coefficient. Ambient jet control is nevertheless a clean, natural theorem.

For an arbitrary compact set \(K\), define “uniform \(C^R\) convergence on \(K\)” explicitly as convergence of the **ambient jets restricted to \(K\)**. Avoid suggesting an intrinsic \(C^R(K)\) construction.

### (iii) Nonnegative error sequence: harmless

Yes. Replacing an error bound by its absolute value preserves convergence to zero and weakens the bound appropriately. A wrapper theorem could hide this normalization; it is not mathematically significant.

### (iv) What is still missing?

Nothing essential for the stated deterministic theorem. For the **probability interface**, record:

1. a fixed-\(\mu\) topology on the branch-jet data;
2. continuity of the coefficient map in that topology;
3. Borel measurability as a consequence.

“Joint measurability” is not an additional property of the deterministic map that must be proved separately. For random fields, one must establish that the random branch data are measurable **as random elements of the chosen jet space**; pointwise measurability alone should not silently substitute for this.

Also: convergence of a vector of coefficients requires **joint** convergence of the relevant branch data. Coordinatewise convergence in distribution does not suffice.

## 2. Yes: expose the local Lipschitz theorem

Define the fixed-index jet pseudodistance
\[
d_\mu(\xi_1,\xi_2)=
\max_p\max_{0\le r\le R_p(\mu)}
\sup_{x\in K_p}\|D^rL_{\xi_1,p}(x)-D^rL_{\xi_2,p}(x)\|.
\]

The most immediately extractable Lean theorem needs no supremum machinery:

```lean
-- Schematic; retain the resolved-data / vanishing hypotheses.
theorem exists_resolvedCoeff_top_bound
    (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ξ₁ ξ₂ : SmoothRootField,
        (∀ p, JetBoundOn (pieceOrder p μ) (chartImage p)
          (ξ₂.Lψ p) B) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        (∀ p, JetClose (pieceOrder p μ) (chartImage p)
          (ξ₁.Lψ p) (ξ₂.Lψ p) ε) →
        |ξ₁.resolvedCoeff μ (c - 1) -
          ξ₂.resolvedCoeff μ (c - 1)| ≤ K * ε
```

Here `K` depends on the fixed resolved data, observable, `μ`, `c`, and `B`, but not on `ξ₁`, `ξ₂`, or `ε`. Piecewise bounds `B p` are a useful refinement, not a prerequisite.

The proof should expose the constants already present:
\[
K=\sum_p \operatorname{vol}(\mathrm{Base}_p)\,
       K_{c,p}\,C_p,
\]
including any fixed prefactors in the actual definition.

Call this **local Lipschitz control on jet-bounded data**, not unrestricted global Lipschitz continuity. The `ε ≤ 1` condition matters.

And correct the probability slogan: **convergence in distribution plus continuity** gives the continuous-mapping conclusion. Tightness alone gives only subsequential opportunities, not identification of the limit.

## 3. Ranked direction

### 1. **(d) Extract Lipschitz + the topology/measurability interface, then (c) consolidate**

This is a small, high-value completion of work already done—not another analytic campaign.

Suggested sequence:

**A. Extract the uniform bound above.** Derive the existing sequential theorem from it.

**B. Package the branch jets.** Schematically, with `E p` the ambient chart space and `V p` the branch codomain:
```lean
abbrev BranchJetSpace (μ : ℝ) :=
  ∀ p, ∀ r : Fin (pieceOrder p μ + 1),
    C[chartImage p,
      ContinuousMultilinearMap ℝ (fun _ : Fin r.val => E p) (V p)]

def branchJet (μ : ℝ) (ξ : SmoothRootField) : BranchJetSpace μ := ...
```
Install compactness on each chart-image subtype. The finite product carries its usual sup-norm topology.

**C. Prefer the realizable jet image to installing a new global topology on `SmoothRootField`.**
```lean
def RealizableJets (μ : ℝ) :=
  Set.range (branchJet μ)

def coeffOnJets :
    RealizableJets μ → ℝ := ...

theorem continuous_coeffOnJets :
    Continuous (coeffOnJets ...)

theorem measurable_coeffOnJets :
    Measurable (coeffOnJets ...) :=
  continuous_coeffOnJets.measurable
```
Well-definedness follows from the bound with `ε = 0`: identical restricted jets imply identical coefficients.

Relevant infrastructure: compact-set boundedness of continuous jets, the normed structure on `ContinuousMap`, finite products, and `Continuous.measurable`. For the integral estimate, reuse your existing `norm_integral_le_of_norm_le_const` proof rather than introducing new integration machinery.

**Pitfalls:**

- Raw smooth fields carry a **pseudometric** from these jets: different fields may have distance zero.
- The topology depends on `μ`; do not silently install one instance intended to serve every index.
- Do not claim extension to all arbitrary jet tuples or to the closure of the realizable image without proving it.
- For finitely many indices, use piecewise maximum orders and obtain a continuous coefficient-vector map.

Then consolidate the modules and paper.

### 2. **(a) Lower-log Mellin weights**

This supplies genuinely new explicit formulas, whereas a conditional continuous-mapping corollary is largely infrastructure.

But first audit the normalization. Your proposed identity cannot be certified without the definitions of `mellinMom` and \(S_\nu\):

- a kernel \(\tau^{2\nu-1}\) produces \(2^\ell(\log\tau)^\ell\);
- a kernel \(\tau^{-2\nu-1}\) produces \((-2)^\ell(\log\tau)^\ell\);
- using \(\log(\tau^2)\) changes the displayed normalization.

The shift \(\mu+r/2\), sign, and powers of \(2\) must all be derived from the actual kernel. First prove a one-derivative integral identity with a locally uniform integrable dominator, then iterate. Avoid starting with an `iteratedDeriv` theorem whose normalization is only guessed.

### 3. **(b) Conditional random-field subleading theorem**

Do this after the topology package, preferably using the same convergence-in-law abstraction already used by `EmpiricalFieldLimit`. I would not choose a Mathlib theorem name without checking the repository’s pinned version.

The mathematical statement is:
```lean
-- Schematic
Xₙ ⇒ X in RealizableJets μ
  ⟹ coeffOnJets Xₙ ⇒ coeffOnJets X
```
The substantial probabilistic task remains proving convergence in that jet topology for the intended empirical branch fields—not applying continuous mapping.

## 4. Concrete paper edits

Replace the order explanation by:

> Put \(K_p=\{T_p(s,v):s\in\mathrm{Base}_p,\ v\in\overline{\Box}_p\}\) and \(R_p(\mu)=\sum_i\mathrm{depth}_{p,i}(\mu)\), using the canonical cutoff on piece \(p\). Uniform \(C^{R_p(\mu)}\) convergence means uniform convergence on \(K_p\) of all ambient Fréchet derivatives through that order.

Replace:

> no single order serves the whole expansion

by the safer:

> the required order depends on the coefficient index; the theorem asserts no uniform finite order for the full expansion.

Add, once the bound is named:

> More precisely, the coefficient map is locally Lipschitz for these restricted jet seminorms, with constants controlled by the fixed resolved data and bounds on the branch jets.

Finally:

> This is the deterministic continuity input for a continuous-mapping theorem, provided the random branch representatives converge in distribution in the corresponding jet topology.

Keep the non-claims. Also verify once that `deepZeroFibre c` corresponds exactly to the paper’s \(D_{c+1}\); the supplied signatures alone do not settle that indexing convention.