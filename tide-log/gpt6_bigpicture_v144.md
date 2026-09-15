## Verdict

**Close priorities 2a and 2b.** The supplied statements and proofs implement the intended design. The `DeepVanishing` change is a sound strengthening of the API: weaker input hypotheses, with exactly the boundary-jet conclusion needed downstream.

This is a source-level audit of the supplied code; I have not independently checked the repository or the population indexing definitions.

### 1. Audit of 2a/2b

**(i) Depth and dimension.**

- `hc : 1 ≤ c` is correct and necessary: without it, truncated subtraction would make `c = 0` incorrectly select log degree zero as the “top” degree.
- No upper bound `c ≤ d` is needed in Lean.
- The `c - 1 > d - 1` branch correctly makes both sides zero.
- In the resolved formula, use the **active piece dimension** `da p`, not the ambient dimension, for this check. Pieces with `da p < c` contribute zero; their size-`c` face sum is empty. Reusing `smoothCoeff_eq_faceSum_top` handles this without another case split.
- The upper-degree vanishing theorems legitimately allow `c = 0`.

**(ii) Normalisation. Correct.**

The piece replacement is precisely
```lean
smoothCoeff
  (fun v => amp v * fluctuation 1 μ (ζ v) / Real.Gamma μ)
  hA kA 1 a μ (c - 1)
```
with the **same** `hA`, `kA`, and cube radius `a`.

There is no additional dilation factor to insert: `smoothCoeff_eq_scaleCoeff_dilation` supplies the same
```text
A_b · B_b^(−μ)
```
as the empirical scaling after higher-log terms vanish.

At the face-formula level, `Γ(μ)` is constant in the face variables, so
```text
Γ(μ) · ∂^α[amp · S_μ(ζ) / Γ(μ)]
    = ∂^α[amp · S_μ(ζ)].
```
Here `μ > 0` ensures the intended Gamma normalisation and fluctuation smoothness. Setting population `β = 1` is essential and correct.

**(iii) Indexing. No mismatch in the theorem actually proved.**

The proof passes directly through
```lean
pieceCoeff
→ base integral of smoothCoeff
→ smoothCoeff_eq_faceSum_top
```
using the same `p`, `s`, `hA`, `kA`, radius, and `piecePresentation Y p`. Thus it does **not** depend on identifying the population decomposition’s chart indexing.

One wording qualification: without inspecting the population definition, I would call `empPieceStratumSum`

> “the same population face-sum expression, evaluated on `replacedAmp`”

rather than claim literal definitional equality with a named `pieceStratumSum`.

A reindexing lemma through `en I` is needed only if you want an explicit equality with a sum written using `(Ξ.decomp Y).chart I`. It is **not a closure blocker**.

### 2. `DeepVanishing`: accept the weakening

For `b > 0`, the new condition says that the zero set of `η` contains a relative neighbourhood of every deep point in `closedBox d b`. This is the correct extension-independent condition.

The proof chain is sound:
```text
F vanishes near deepZeroFibre
→ Gloc vanishes near the corresponding chart point
→ pull back along continuous facePt
→ use G_eq only for points inside the box
→ DeepVanishing amp
→ one-sided boundary-jet vanishing.
```

In particular, the argument never illegitimately uses `G_eq` outside its domain.

Also correct:

- `DeepVanishing.diag` needs only the forward deep-set map and preservation of the closed box.
- Multiplication by the fluctuation factor preserves relative vanishing.
- Smoothness plus the one-sided lemma gives the **full ambient jets**, not merely tangential derivatives. Positivity of the box radius matters here.

**Use the weaker hypothesis in the paper**, not merely in Lean notes. Suggested wording:

> “Assume that \(\eta\) vanishes on a neighbourhood of the deep set relative to the closed box \([0,b]^d\).”

This is more precise than “within the box,” which could be misread as referring only to \((0,b]^d\).

Keep the stronger-hypothesis wrapper via `DeepVanishing.of_eventually` for compatibility.

## 3. Ranked next units

### 1. Fixed-coefficient continuity under finite-order branch convergence

**Highest-value mathematical addition.** It supplies a deterministic stability theorem for the new formula and the missing bridge toward random-field limits. Scope it to fixed `μ, q`; do not promise a single finite derivative order for the entire expansion.

A useful sequence is:

#### A. Population coefficient finite-order bound

Introduce a compact-box jet seminorm, for example
```lean
-- Proposed API; boxJetNorm uses derivatives of orders ≤ r on closedBox.
theorem smoothCoeff_finiteOrderBound
    (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (μ : ℝ) (q : ℕ) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ A, ContDiff ℝ ∞ A →
        |smoothCoeff A h k β b μ q| ≤ C * boxJetNorm r b A
```

Also expose linearity, if not already available:
```lean
smoothCoeff_add
smoothCoeff_smul
```
Uniqueness of cutoff expansions is the natural route to linearity, including the usual off-lattice/out-of-degree cases.

**Important:** coefficient uniqueness alone does **not** establish continuity. The finite-order bound must come from the explicit smooth/face engine, with a Taylor cutoff chosen beyond the fixed exponent.

#### B. Cube replacement continuity

For fixed smooth `η`, prove
```lean
∃ r, ∀ (ζn : ℕ → ((Fin d → ℝ) → ℝ)) ζ,
  (∀ n, ContDiff ℝ ∞ (ζn n)) →
  ContDiff ℝ ∞ ζ →
  Tendsto (fun n => boxJetNorm r b (ζn n - ζ)) atTop (𝓝 0) →
  Tendsto
    (fun n => empCoeffRect η (ζn n) h k (fun _ => b) μ (c - 1))
    atTop
    (𝓝 (empCoeffRect η ζ h k (fun _ => b) μ (c - 1)))
```
with the existing hypotheses `hη`, `hk`, `hb`, `hμ`, `hc`, `hdeep`.

Reuse:
```lean
empCoeffRect_top_eq_smoothCoeff
contDiff_mul_fluctuation
smoothCoeff_eq_scaleCoeff_dilation
```
and finite-order continuity of multiplication and smooth composition on a common compact value interval.

#### C. Resolved continuity

Keep `Ξ`, `Y`, and therefore the geometry and observable, fixed:
```lean
-- Schematic: BranchJetConverges is a proposed compact-uniform C^r condition.
∃ r, ∀ ξn : ℕ → Ξ.SmoothRootField Y,
  BranchJetConverges r ξn ξ →
  Tendsto
    (fun n => (ξn n).resolvedCoeff μ (c - 1))
    atTop
    (𝓝 (ξ.resolvedCoeff μ (c - 1)))
```

Require convergence uniformly over the relevant compact branch-coordinate sets, including the base parameter after pullback. Take a finite maximum of the derivative orders required by the pieces.

**Pitfalls:**

- `faceCoeffInt` is not automatically bounded by just the displayed normal jet order. Its remaining coefficient operation can require additional derivatives.
- Pointwise convergence in `s` does not justify convergence of base integrals. Obtain a uniform coefficient bound and use the existing base-measure finiteness/integrability infrastructure.
- Do not impose wall agreement on the branches.
- Work on closed boxes, including boundary jets.
- Start with smooth approximants converging in a finite-order topology; extending coefficient definitions to merely `C^r` inputs is a separate project.

### 2. Declare the current §20 formalisation closed and consolidate

**The current theorem package already warrants closure.** Do this now as a milestone, even if continuity becomes the next project. Continuity is an extension, not unfinished 2a/2b work.

High-value consolidation: a short dependency map, the relative-neighbourhood hypothesis, and the exact branchwise/non-global scope.

### 3. Lower-log Mellin-weight identification

Useful for explicit subleading formulas, but less structural than continuity. State it first as an `iteratedDeriv` identity in the Mellin order, on the open region where the shifted order is positive. Prove local uniform domination before differentiating under the integral.

Check the sign and powers against the **actual definition of `mellinMom`**; they cannot be audited from the definitions supplied here.

### 4. Random-field limits of subleading coefficients

Defer until deterministic continuity and the required topology are settled. This additionally needs a genuine tightness/convergence statement in that topology; pointwise or `C⁰` field convergence is generally insufficient.

## 4. Short paper edits

1. **Box hypothesis**
   > “vanishes on a neighbourhood of the deep set relative to the closed box.”

2. **Population comparison**
   > “the population cube coefficient, with \(\beta=1\), the same exponents and cube radius, and the replaced amplitude.”

3. **Replacement-rule sentence**
   Replace “on the resolved manifold” by
   > “piece by piece in the resolved presentation.”

   Your following non-global disclaimer is good; this change removes the initial suggestion of descent.

4. **Exactly resonant faces**
   For closest correspondence to the Lean sum:
   > “the size-\(c\) faces, with the resonance weights of Theorem E; nonresonant terms vanish.”

5. **Associated-graded language**
   The new theorem proves a formula on \(\mathcal I_{c+1}\). To say it defines a functional on \(\mathcal I_{c+1}/\mathcal I_c\), explicitly cite annihilation on \(\mathcal I_c\): depth vanishing with parameter `c - 1` handles `c ≥ 2`; `c = 1` needs the existing away-from-zero-fibre result.

**Bottom line:** accept both priorities and the hypothesis change; close the milestone. The next substantive unit should be fixed-coefficient finite-order continuity, not stochastic subleading limits.