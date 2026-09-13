# G0 — signature-and-composition audit for the companion note (consult #106, Rank 0)

Pin `32cdbf6`. For each endpoint: the complete explicit hypotheses (section variables + binders), and which
certificates are CONSTRUCTED (appear under `∃`) versus CONSUMED (hypotheses).

| Declaration | Consumed | Constructed | Notes |
|---|---|---|---|
| `L1SeqCLT.clt_l1` | `[Countable ι]`, i.i.d. `Y : ℕ → Ω → L1Seq ι` (`hY : ∀ j, MemLp (Y 0 · j) 2`, `hindep`, `hident`, `hYm`), summable coordinate `L²` (`SummableCoordL2`-type hypothesis) | `∃ ν : ProbabilityMeasure (L1Seq ι)`: (i) the centred normalised empirical sums converge in distribution to `ν`; (ii) every finite coordinate vector has the centred Gaussian law with the observation covariance (`gaussianTarget`); (iii) the truncation tail bound `∫⁻ ‖x − truncate F x‖ₑ dν ≤ sigmaTail` | the ℓ¹ CLT constructs the law from the coordinate certificate; no functional-CLT input |
| `SampleDatumLimit.tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum` | `hk`, `hβ`, `hb`, coefficient family `c : 𝓧 → CoeffFamily` with `hc` (certified chart data), `hcm`, `hXm`, `hXind`, `hXid`, `hc2 : ∀ γ, MemLp (c (X 0 ·) γ) 2`, `hsum : Summable (b^{|γ|} √E c²)`, zero-phase datum `A` | `∃ ν`: marginals + `A_n · dataBoxIntegral(sampleDatum) ⇒ dataBoxCoeff(x + A)` at the leading pair | law CONSTRUCTED (via `clt_l1`); consumed: the model-to-chart coefficient family `c` (the "certified chart data") |
| `JointSampleLimit.tendstoInDistribution_scaled_coreSum_sampleDatum` | as above per chart `I : Fin J` (`bJ`, `c I`, `hc2`, `hsum`), common scale `(lam, mult)` dominating every chart pair (`hdom`), stacked data `A : Fin J → DataSpace` | `∃ ν` on the STACKED ℓ¹ space: stacked marginals + joint scaled core-sum limit `jointLeadingCoeff` | one stacked law for finitely many charts read from the same sample (no independence across charts) |
| `ClosureEndpoint.tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail` | same as `SampleDatumLimit` | `∃ ν`: marginals + TAIL bound + scaled core limit | the tail certificate is constructed, not consumed — §6.10 row "Distributional assembly / Not supplied: CLT/tail certificates" is STALE |
| `ClosureEndpoint.annealed_sampleDatum_single_identified` | as above + `hp : 1 < p`, `hpc : p β κ < 2`, `hκ : UniformSubgaussianPhase b hb c hc P X κ`, `hA : xiCoord A = 0`, `hAM : mass (etaCoord A) ≤ M` (BOUNDED AMPLITUDE of the deterministic datum, not of the sample datum), remainder `R` with `hRint`, `hrem : ∫ |A_n R_n| → 0` (= hypothesis E) | `∃ ν`: marginals + tail + `Integrable (dataBoxCoeff (· + A)) ν` + `∫ A_n (Z_n^core + R_n) dP → ∫ dataBoxCoeff dν` + the covariance-modified face-integral identification | one law supplies expectation convergence and identification; `_effectiveTemperature`, `_of_lt_two` are wrappers |
| `ScaledAssembly.tendsto_integral_scaled_assembly` | `hcore` (scaled core weak limit), `hp : 1 < p`, uniform `p`-moment bound `hM` of the scaled core, `hRint`, `hrem : ∫ |A_n R_n| → 0` (E) | `Integrable L μ' ∧ ∫ A_n (Zc + R) → ∫ L` | E is REQUIRED (not merely `o_P(1)`): note's scaled-assembly item (2) must state it |
| `ExponentComparison.exponentPair_eq_of_population_comparison` | `hΘ : LaplaceTheta μ f lamH qH` (population order), `hL : 0 < L₀`, `hconv : A_n ∫ e^{−nf} → L₀` (same integral, same measure) | `lam = lamH ∧ m − 1 = qH` | comparison for the SAME integral |
| `ExponentComparison.tendstoInMeasure_log_div_log_of_population_comparison` | `hcmp : lam = lamH`, scaled weak limit `hdist`, `hZpos`, `hL : L > 0 a.e.` | `log Z_n / log n → −lamH` in measure | empirical transport needs the positive distributional limit |
| `HironakaUnconditional.exists_exponentPair` | `IsOpen U`, `AnalyticOnNhd ℝ K U`, `K w = 0`, `K` not eventually `0`, `K ≥ 0` eventually | `∃ lamH thetaH r₀`, uniqueness of any power–log rate on small balls | population EXISTENCE only |
| `BoxMomentBound.moment_scaled_dataBoxIntegral_le` | `hp : 1 ≤ p`, `hc : p β c < 2`, amplitude mass bound `hxM : ∀ ω, mass (etaCoord (x ω)) ≤ M` (bounded AMPLITUDE of the datum, ω-wise), full-box MGF `hmgf` | `p`-moment bound by the reduced-temperature population mass | bounded amplitude, not bounded full sample datum |

## Reconciliation of §6.10

* "Distributional assembly — Not supplied: CLT/tail certificates and certified chart data": the CLT and tail
  certificates are CONSTRUCTED from the coordinate certificate (`hc2`, `hsum`, i.i.d.); what remains consumed is
  the certified chart data (the model-to-chart coefficient family `c`, `hc`) and the zero-phase amplitude datum.
* "Annealed assembly": requires `𝔼|A_n Rem_n| → 0` (E) and, for the asymptotic equivalence, `𝔼L > 0`.
* "Uniform moments": the amplitude bound is on the deterministic datum's amplitude mass (`mass (etaCoord A) ≤ M`),
  not on the full sample datum.
* No pathwise/annealed-gap declarations are dotted in the note's inventory (the gap results live in the paper's
  mirror).
