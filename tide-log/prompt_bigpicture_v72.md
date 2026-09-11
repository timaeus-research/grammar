# Astra consult #72 — the RLCT formula is unconditional; what next for the paper's Lean mirror?

Lean 4 / Mathlib formalisation `timaeus-research/grammar` (namespace `Grammar`, 513 modules, no
sorry, axiom-clean). Since consult #71, in one session:

## 1. Landed (all axiom-clean)

* **CCVIII** (support condition removed, exactly as you confirmed): `CentredChartData` carries
  tangential Jacobian weights `hT`; `SplitBoxChart` injective off a measurable null set; the
  orthant chart's Jacobian factor and datum are the continuous weight `∏_i|v_i|^{hT_i}` times the
  unweighted ones (scalar multiples in the ℓ¹ data space); positivity of the tangential integral
  via the weight being positive off a null set. `exponent_of_analytic`: for `K ≥ 0` analytic on an
  open `U ∋ w`, `K w = 0`, `K` not identically zero near `w`, `K` measurable, `F > 0` analytic on
  `U`, and any `ρ₀ > 0`: hironaka's `Q_all` gives a monomial partial resolution `R` near `w`, and a
  compact neighbourhood `Ω ⊆ B̄(w,ρ₀) ∩ U` of `w` with `∫_Ω F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})`,
  `(λ_*, m_*)` the min/max over finitely many divisor-point chart pairs
  `(C.lam, C.mult) = (min_j (h_{n_j}+1)/(2k_j), #minimisers)` of `R`.
* **CCIX** `laplace_pair_eq_resolution_pair`: hironaka's small-ball pair `(λ_H, θ_H)`
  (`∫_{B̄(w,r)} e^{−NK} ≍ N^{−λ_H}(log N)^{θ_H−1}`, all `0 < r ≤ r₀`, from CLXXXV) equals
  `(λ_*, m_*)`: `λ_* = λ_H`, `m_* − 1 = θ_H − 1`. Proof: region inside `B̄(w,r₀) ∩ U` containing a
  small ball, `F` between its positive extrema, Θ-sandwich between two small-ball Laplace integrals,
  uniqueness of power–log orders (restriction to ℕ). So the population Laplace exponent pair of `K`
  at `w` IS the resolution formula, independently of resolution, cover, region, observable.
* **CCIX-b** `resolution_pair_of_population_comparison`: on every small ball any certified
  population core theorem `A_k ∫ e^{−kK} → L₀ > 0` at `(λ, m)` has `(λ, m−1) = (λ_*, m_*−1)`, and
  under the paper's empirical hypotheses (`A_k Z_k^{emp} ⇒ L > 0`, `Z_k > 0`)
  `log Z_k^{emp}/log k → −λ_*` in probability.

So the deterministic RLCT theorem — "the exponent of `∫ F e^{−NK}` near a zero is
`min_charts min_j (h_j+1)/(2k_j)` with multiplicity the maximal number of minimisers" — is in Lean
unconditionally (given Hironaka's chart form). Not in Lean: the full power–log EXPANSION over a
region (cross-chart gate), the leading COEFFICIENT of the region integral (would need the same
gate: the local coefficients are explicit but overlaps make the region coefficient inaccessible),
the free-energy form for the region (trivial from Θ: `−log Z = λ_* log N − (m_*−1) log log N + O(1)`,
I am adding it now).

## 2. The paper's remaining claims

The paper (Gerraty–Murfet, *Grammar*) is about the asymptotic expansion of `Z_n[φ]` (expectations
against `e^{−nK}` with a smooth observable), its coefficient structure (Section 4: fluctuation
function, ladder algebra, log-insertions — all in Lean), the geometric main theorem
(`thm:expectation_expansion`: per-stratum form with coefficients `c_{λ,m}` given by face integrals
of the normal Taylor data), and the companion note on averaging over the dataset (Gaussian
fluctuations of `log Z_n`, sample datum, annealed quantities — largely in Lean at the interface
level, with the geometric bridge as the missing input).

## 3. Ask

1. With the RLCT formula done, rank the next targets for the paper's Lean mirror:
   (a) the full expansion over a region — the cross-chart gate (your §4 of #70: subanalytic
       rectilinearisation). Is there ANY bounded sub-target here that is tractable in ~10 units and
       still paper-relevant (e.g. the expansion when the resolution has ONE chart covering the
       region a.e. — a "single-chart region" hypothesis stated as a property of the resolution
       output, so that the local theorem becomes global; or the expansion of the SUM over charts
       with the multiplicity-weighted overlaps as an explicit error of lower order)?
   (b) the leading coefficient of the region integral: `c_* = Σ_{p minimising} localLeadingCoeff_p`
       IF the pieces attaining the extremal pair have a.e.-disjoint images — is there a cheap
       sufficient condition? (Different divisor points of the SAME chart give disjoint source
       neighbourhoods only if we shrink; different charts overlap in the target.)
   (c) the statistical transfer of the identified pair into the companion note's theorems (the
       annealed/sample-datum expansions currently take the geometric bridge as an interface
       hypothesis `CompatibleDivisorLocalisation`): can the Θ/identified-pair results discharge any
       of those interface hypotheses, or do they all need the expansion?
   (d) tightening the identification: `Ω` is one compact neighbourhood; every small ball has the
       same pair by hironaka — state "for every sufficiently small ball the pair is `(λ_*, m_*)`"
       (trivial from CCIX) and "the leading coefficient of the small-ball integral is bounded below
       by the divisor-point coefficient" (also trivial). Worth stating?
   (e) something else.
2. For your top choice, the first three Lean-level statements (hypotheses/conclusions), the
   Mathlib lemmas, the hazards.
3. Anything in §1 over-claimed. Be blunt.
