# Direction consult #40 — after the #39 stretch: what next for the grammar paper's Lean seabed?

Same setting as #39 (Lean 4 + Mathlib, repo `timaeus-research/grammar`, zero `sorry`/`axiom`; resolution/geometric bridge DEFERRED by the user; user wants NEW THEOREMS over process). Your #39 plan is now complete, including both items I had deferred, plus extras. Grammar main `6b55f24`.

## Delivered since #39 (Headlines XLIV–LVI; all built)
- **XLIV** assembled first log energy correction `N log N (𝒵_K/𝒵 − μ*/(βN)) → −(m*−1)/β` (each chart shifting its own `h_I`); abstract isolated remainders with any log weight.
- **XLV/XLVI** second-order expectation quotient for general observables: chart (`population_second_order_chart`, `_observable` for `φ∘π = u^s ψ`), assembled, with `secondCoeff`/`assembledSecondCoeff` = coefficient of `N^{-λ}L^{m−2}`.
- **Wall-crossing** local constancy (`first_nonzero_locally_constant`, `population_first_nonzero_locally_constant`).
- **XLVII** free energy `−log 𝒵 = λ log N − (m−1) log log N − log A − (B/A)/log N + o(1/log N)` (your unit 11).
- **XLVIII** energy hierarchy: iterated transport, `N^r 𝒵_{K^r}/𝒵 → (μ*)_r/β^r` with correction `−(m*−1)∂(μ*)_r/β^r`, posterior variance of `NK` → `μ*/β²` with correction `−(m*−1)/β²` (chart and assembled) (your units 4–5).
- **XLIX** Gamma Laplace limit `𝒵_{β+t}/𝒵_β → (β/(β+t))^λ` via exact rescaling (your unit 6).
- **L** stochastic second-order posterior quotient centred at the current `A'_ℓ/A_ℓ` (your units 1–3), and **LIII** the multiplicity-one case via uniform log-weighted isolated remainders on norm balls + an abstract four-statistics lemma with deterministic normalisers (`tendstoInDistribution_secondOrder_of_stats`).
- **LI** noncancellation from face witnesses (your units 7–8): `chartFace_pos` (measure charging open sets), `assembledFace_pos`, `population_assembled_isEquivalent_of_witness`.
- **LII** phase-dressed moment recurrence `J_{ν+1,i}(a) = (νJ_{ν,i} − iJ_{ν,i−1})/β + (a/2)J_{ν+1/2,i}` and `∂_a J_{ν,i} = βJ_{ν+1/2,i}` (your unit 9).
- **LIV/LV/LVI** (your unit 10, completed): constant phase `ξ ≡ a`: `C(μ,j;a) = K_k ∑_γ cη_γ S(μ,j;γ;a)` with phase-dressed moments; transport `C_K(μ+1,j;a) = (μC − (j+1)C(μ,j+1) + (a/2)∂_aC)/β` with `∂_a` proved through the monomial sum (Mathlib `hasDerivAt_tsum_of_isPreconnected`, half kernels dominated by the moment at phase `|a₀|+1`); constant-phase leading coefficient `A(a) = 2^{-(m−1)}/((m−1)!∏_J k_i)∫η(P_J u)J_{2λ}(a)∏u^{h−2kλ}` (Headline XIX in the variable `√N`, polynomial uniqueness) and **`N 𝒵_N[K∘π η; a]/𝒵_N[η; a] → λ/β + (a/2β) ∂_a log A(a)`** for `A(a) ≠ 0`.

Interfaces beyond #39: `phaseFace`, `constFamily`, `kernelSHalf`/`kernelFunctionalHalf`, `poch`/`pochD`/`iterTransport`, `secondCoeff`, `tendstoInDistribution_secondOrder_of_stats`, `gInt_isolated_bound`, `cutoffExpansion_isolated_remainder_mul`, `neg_log_twoTerm`, `quotient_second_order`, `energy_laplace_chart`, `origPhaseIntegral_beta_rescale`.

## Remaining declared gaps (mirror)
External by instruction: resolution, charts, partitions of unity, empirical-process CLT, standard-form identity. NO-GO: all-orders inverse-log division. Not done: next-log correction WITH constant phase (would need constant-phase two-term data: the constant-phase Taylor tree's remainders at the next-log scale — the isolated-remainder lemmas already work for any `cξ`, so this may be cheap); spatially varying `ξ` transport (needs `∂` along the phase family, i.e. the derivative of the full coefficient functional in the direction of `ξ`); assembled Laplace limit (residual must respect the rescaling); weak convergence of the law of `NK` (Laplace continuity theorem); the `E[φ]` second-order theorem in distribution at mixed multiplicities (one side multiplicity one) — the four-statistics lemma makes this routine.

## Candidate directions (rank, cut, replace)
(a) **Constant-phase next-log correction**: `N log N (𝒵_K/𝒵 − c₁(a)/N) → c₂(a)` with `c₁ = λ/β + (a/2β)∂_a log A`, via two-term constant-phase data + transport at `(λ, m−2)` (needs `∂_a` of the second coefficient too — available from the same derivative theorem).
(b) **Random constant phase**: if the fluctuation is a random constant `a ~ P` (e.g. the Gaussian `ξ(0) = X` already used in `rem:pop_vs_emp`), the posterior expectation of `NK` converges in distribution to `λ/β + (X/2β) ∂_a log A(X)`; combine LVI with the leading-quotient-in-distribution machinery (XXXVIII) — a genuinely stochastic energy statement.
(c) **Spatially varying phase, first order**: directional derivative of `C(μ,j;·)` at `ξ = 0` in direction `ζ` (the `p = 1` term of the coefficient series is already `β kernelFunctional … 1 μ j (cη * fluct cζ)`); a "linear response" of the leading coefficient to the fluctuation; the energy correction to first order in `ξ`.
(d) **Weak convergence of `NK`** to `Gamma(λ, β)` from the Laplace transform limit (needs a Laplace continuity theorem — check Mathlib; if absent, NO-GO).
(e) **Mixed-multiplicity stochastic second order** (one side `m = 1`): routine with the four-statistics lemma; low value?
(f) **Assembled Laplace limit** with residual hypotheses respecting the rescaling.
(g) Something you consider more valuable for the authors.

## Ask
A ranked bounded plan (≤ 10 units) with precise target statements, external inputs, non-claims and traps (remainder scales, divisions, where `A ≠ 0` a.s. is needed, where differentiating an expansion would be illegitimate). Say which of (a)–(f) you drop. Under ~2000 words.
