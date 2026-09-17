# Big-picture consult #164: closing the posterior-expectation programme

You are Astra, design consultant for the Lean 4 (Mathlib) formalisation of the grammar paper (repo `timaeus-research/grammar`,
namespace `Grammar`, 895 modules, axiom-clean). Rank, decide, give Lean-typable statements. No process advice.

## Landed since #163 (main = DLX)

* DLVI–DLVII (candidate I): finite-atom and compact-base covariance interpolation,
  ★★★ `GaussianField.integral_compactAvg_eq : E⟨f⟩_G = ρ(f)/ρ(K) + ∫₀¹ E H_f(√sG) ds`, `H_f` in moment form with the quadratic
  domination `|H_f(g)| ≤ 5β²‖f‖c(2λ/β + 1/4)(1 + ‖g‖²)`.
* DLVIII–DLIX (candidate II): `gibbsJoint` = μ_g on `K × ℝ` (withDensity of ρ ⊗ dt|_(0,∞)), probability, reductions
  (`∫φ dμ = ⟨φ⟩`, `∫φ√t = ⟨φ⟩^{½}`, `∫φt = T`, `∬h√t₁√t₂ = B`), ★★★ two-replica Stein
  `E[G(x₀)⟨f⟩_G] = βE∬f(x₁)(√t₁𝒞(x₀,x₁) − √t₂𝒞(x₀,x₂))dμ_G dμ_G`, ★★★ three-replica response
  `H_f(g) = (β²/2)E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁𝒞(x₁,x₁) − 2√t₁√t₃𝒞(x₁,x₃))]`.
* DLX (candidate V): `hasFDerivAt_weightedFunctional` (`g ↦ ∫φS_ν(g)dρ` Fréchet differentiable on `C(K,ℝ)`),
  `hasFDerivAt_compactAvg` (`D⟨f⟩_g[h] = β(⟨fh⟩^{½} − ⟨f⟩⟨h⟩^{½})`), ★★★ Banach-form Stein
  `E[G(x₀)F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]`.
* Earlier (this programme): DL source cumulants (`κ₂ = varianceBlocks` over quotient blocks), DLI ★★★ `emp_variance_isBigO`
  (posterior variance to all orders, fixed sample), DLII inverse-evidence moments, DLIII anchored quenched source
  (`Ψ'(0) = E⟨f⟩_G`, `Ψ''(0) = E Var_G f`), DLV Stein on the compact base.
* Bridge inventory for (VI): the greybook bridge has convergence in distribution of the normalised evidence and
  `tendstoZeroInProb_posteriorMean_sub_retainedQuotient` (posterior mean − retained quotient → 0 in probability), the joint law of
  the retained coefficients as continuous functionals of a JET-TUPLE limit; it does NOT identify the limit posterior mean with
  `compactAvg` of a `GaussianField` on a compact base (the limit is built from cube jets, not from a `C(K,ℝ)`-valued field), and
  there is no `C(K,ℝ)`-valued convergence of the field. So (VI) requires a new identification layer (jet-tuple limit ↔ compact-base
  Gaussian field with kernel 𝒞) before uniform integrability arguments — a project, not a unit.

## Remaining candidates

(III) Convergent source expansion `Ψ(ε) = Σ_{r≥1} (ε^r/r!) E κ_r^{μ_G}(f)` on `|ε| < log 2/M` (analytic log of the entire function
      `ε ↦ ⟨e^{εf}⟩_g`, coefficient identification with iterated derivatives, interchange with `E` by geometric domination).
(IV) Higher posterior cumulants for a fixed sample: a two-scale PRODUCT lemma (`P₁P₂ − Σ_{j<J}(Σ_{i≤j}R₁ i R₂ (j−i))x^j = O(x^J g^{2J+2})`
      generalising the variance case), hence expansions of every polynomial in the moment quotients, and the κ_r blocks by the
      moment–cumulant recurrence (`κ₃ = m₃ − 3m₂m₁ + 2m₁³` etc.).
(VII) The derivative identity at the compact level: `A'(s) = E H_f(√sG)` for `A(s) = E⟨f⟩_{√sG}` on `(0,1)` (Astra #163: reasonable
      once continuity of the averaged response is packaged) — and/or the second-order interpolation (iterate once: the response of
      the response, five replicas?) with exact remainder.
(VIII) Write-up: the mirror `grammar_lean_2.tex` has §10 (empirical expansion); the posterior programme is only in the grammar2 notes.
      A theorem-style §10.5 "posterior expectations" in the mirror (fixed sample: quotient blocks, κ₂; averaged: Stein, interpolation,
      replicas) would put the landed results next to the empirical ones. (Presentation, not new mathematics.)
(IX) Anything you consider missing for the narrative "the right way to study E[Z_n[f]/Z_n[1]]": e.g. a theorem that the averaged
      posterior mean at leading order EQUALS the interpolation formula's value in a checkable special case (constant kernel? one-point
      base?) as a sanity anchor; or the sign/monotonicity of the response for positive kernels (is `E⟨f⟩_G ≥ ρ(f)/ρ(K)` for f ≥ 0? no —
      but is there a clean inequality?).

## Questions
1. Rank (III), (IV), (VII), (VIII), (IX) for the paper's narrative; which ONE next and what to stop at? Is the programme "closed" at the
   theorem level after DLX in the sense of consult #162's plan, so that write-up should now take priority?
2. For (IX): is there a genuinely informative closed-form check (one-point base `K = {pt}`, ρ = δ, kernel c: then ⟨f⟩_g = f(pt) trivially —
   useless; two-point base with f = indicator? the response then involves S_λ, S_{λ+1/2}, S_{λ+1} at two Gaussian values; is
   `E⟨f⟩_G − ρ(f)/ρ(K)` computable in closed form there, or at least its sign?). Give the statement if one exists.
3. Any errors or misleading names in the landed statements to fix before the write-up (e.g. `compactHalfAvg`, `compactFirstMoment`
   are weighted integrals, already flagged; `gibbsJoint` is supported on t > 0 but lives on `K × ℝ`).
