You are Astra, consulted for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, Mathlib) of the paper "Grammar (Expectations and the Exceptional Divisor)" (Gerraty–Murfet). Consult #147: DESIGN of the stochastic jet programme (your #146 item 3), or a reasoned decision to close the arc instead.

## Landed since #146 (main 69002f8, 827 modules, axiom-clean)
- Your item 1: `EmpiricalClosedJets` — `coeffOnJets'` (ambient, junk off the realizable jets), `exists_coeffOnJets'_dist_le` (bounded-ball Lipschitz), `ClosedRealizableJets μ := closure (range (branchJet μ))`, `coeffOnClosedJets := limUnder (𝓝[range] z) coeffOnJets'` (Cauchy along realizable jets by the Lipschitz bound ⇒ limit in ℝ), `tendsto_coeffOnClosedJets` (unique characterisation), `coeffOnClosedJets_closedRealizableJet`, `continuous_coeffOnClosedJets`, `measurable_coeffOnClosedJets`, `tendstoInDistribution_resolvedCoeff_top_closed` (limits in the closed realizable jets).
- Your item 2: `empOneDimCoeff_two`, `empOneDimCoeff_three` (closed forms; no logs in d = 1, as you predicted).
- Hand-off note (module inventory, scope 1–6, non-claims) in the SRI staging directory; papers updated with your wording.

## What the repo already has on the stochastic side (leading term, rank 4–5a)
- `RootField` (ψ measurable on U, bounded, continuous branch representatives `loc p : Base × box → ℝ`), `BranchTuple` = the tuple of continuous branch representatives, Borel σ-algebra; random root fields `ξ : ℕ → Ω → RootField`.
- `tendstoInDistribution_empZ_div`: if `ξ̂_n ⇒ G` in `BranchTuple` (C^0, compact-uniform) with tight laws and `O_p(1)` global bounds, then `Z^emp_n/(n^{−λ}(log n)^{m−1}) ⇒ T(G)` (Slutsky for the tail; `tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts`).
- Rank 5a′: Gaussian expectation of the leading limit for a Gaussian `G` (not annealed).
- The root field is an ABSTRACT input: nothing in the development constructs ψ from data (no empirical process, no CLT). The paper's ψ is the normalised fluctuation `√n (K_n − K)/√K`-type field on the resolved manifold, with Gaussian limit.

## What the new deterministic package gives
- For the TOP coefficient at `(μ, c−1)` on `𝓘_{c+1}`: continuity + local Lipschitz in the branch jets of order `R_p(μ) = Σ_i (2k_{p,i} L_{p,μ} − h_{p,i})` on compact chart images; the coefficient is a continuous Borel function on the closed realizable jets; conditional continuous-mapping theorem.
- Missing: convergence in distribution of the random branch jets `branchJet μ (ξ_n ω)` in `BranchJetSpace μ = ∀ p, ∀ r ≤ R_p, C(K_p, CMM_r)`.

## Questions
1. Is a Lean formalisation of the stochastic jet programme sensible at this point, given that the development has NO data model for ψ? Options I see: (a) an abstract "jet-level Donsker" hypothesis package: define `JetLaw`-type structures (random smooth root fields with pathwise C^{R+1} regularity and square-integrable derivative envelopes) and prove TIGHTNESS of the branch jets in `BranchJetSpace μ` from an equicontinuity criterion (Arzelà–Ascoli / Kolmogorov-type moment bound on increments of the R-th derivatives) — pure functional analysis + probability, no data model; then convergence in distribution follows from fd convergence + tightness (Prokhorov) — does Mathlib have Prokhorov / tightness ⇒ relative compactness in distribution for Polish spaces at this pin? (b) a concrete data model: iid samples, `K_n` the empirical loss, ψ_n the normalised fluctuation; derive the jet regularity from the smoothness of the per-sample losses and prove the jet CLT via fd CLT + tightness — very large. (c) Close the arc: declare the empirical programme complete as "deterministic + conditional", record the stochastic hypotheses as the interface, and stop.
2. If (a): concrete Lean design — what is the minimal, clean tightness theorem to aim for? Statement shape, e.g.
   `theorem isTightMeasureSet_branchJet (ξ : ℕ → Ω → SmoothRootField) (hmeas) (hmom : ∀ p, ∀ r ≤ R_p + 1, ∃ C, ∀ n, ∫ sup_{x ∈ K_p} ‖D^r Lψ_n p x‖^2 ≤ C) : IsTightMeasureSet (range (fun n => P.map (fun ω => branchJet μ (ξ n ω))))`
   — is the Arzelà–Ascoli route (`BoundedContinuousFunction.arzela_ascoli`, `ContinuousMap` compactness) available in Mathlib for `C(K, CMM_r)` with `K` compact, and is a moment envelope on `D^{r+1}` enough (Lipschitz in x ⇒ equicontinuity on compacts with probability ≥ 1 − ε)? Pitfalls?
3. If (c): what exactly should the paper's final scope paragraph say about the random-field side (one or two sentences), and is there any remaining DETERMINISTIC item you would still add (e.g. a d = 2 example with a log, exhibiting a `∂_ν S_ν` weight concretely — which cutoff/exponent configuration produces a nonzero log order there)?
4. Rank (a)/(b)/(c) with reasons; for the top pick give statement shapes, Mathlib lemmas to reuse, and pitfalls.

Be concrete and terse.
