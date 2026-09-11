# Closure certificate — fidelity pass of the Lean annotations (2026-09-11)

Astra consult #66 recommended, before any further construction, an independent review of every
`\leanrefL` claim in the main-paper mirror `grammar_lean.tex` and the companion note
`averaging_dataset.tex`, and a publication-facing statement of what is formalised under which
external inputs. This directory records that pass.

## Scope frozen

* Lean library: `timaeus-research/grammar` at `fd37665` (488 modules, axiom-clean, zero sorries;
  StrucDual pinned at `4f317b3`). Addendum: at `2024ead` hironaka is bumped to `eb9b6ca` and the
  resolution hypothesis `Q n` is discharged (CLXXXV, 489 modules).
* Mirror: 633 dots; companion note: 211 dots; total 844 (`dot_inventory.md`).
* Every dot was inspected by one of six independent reviewers (general-purpose agents with read
  access to the Lean sources) against the checklist: silently supplied hypotheses, smooth vs
  analytic, map vs embedding, kernel field vs tangent bundle, conditional theorem vs existence claim,
  coordinate/linear model vs general geometry, wrong theorem linked, normalisation and sign,
  conclusion stronger than the Lean statement.

## Outcome

| chunk | dots | faithful | flagged | genuine mislinks |
|---|---|---|---|---|
| 1 (mirror L654–L1095: §4 geometry, Programmes P/Q headlines) | 141 | 121 | 20 | `weightComponent_eq` (deleted), `corner_evaluation_fails` (relinked to `MixedCounterexample.tendsto`/`amplitudeCoeff_eq`) |
| 2 (mirror L1095–L1198: coordinate stratum, population theorems, bridge, energy hierarchy) | 141 | 119 | 22 | `foot_tubeMap` (text reordered so it certifies the retraction), `isEquivalent_first_nonzero_of_cutoffExpansion` (existence relinked to `existsUnique_first_nonzero_isEquivalent`), `phaseLaw_cov_pos` (derivative dot added) |
| 3 (mirror L1198: spatial/random programme) | 141 | 126 | 15 | none |
| 4 (mirror L1198–L2300: allocations, §4 lemma headers, Taylor tree, CLT) | 141 | 117 | 24 | `tendstoUniformlyOn_scalar_mul_zero_of_bounded` (relinked to `tendstoUniformlyOn_chart_global`) |
| 5 (mirror L2300–L2453 and note L67–L287) | 141 | 121 | 20 | `polyBoundedPi_quartetW` (relinked to `quartetW_nonneg`/`quartetW_le`) |
| 6 (note L374–L434) | 139 | 127 | 12 | `compactQ_nonneg`/`compactQnum_le` (attribution of the two `V_ρ` bounds inverted; fixed), `spatialPhase_tendsto` (posterior-law claims relinked to `spatialEnergyLaw_tendsto`/`phasePosterior_tendsto_faceLocation`) |

All 113 flagged items were resolved in the documents (Overleaf clone commit after `aa2e6d0`):
qualifiers added to the claim sentence, dots moved from headers to the clause they certify, or dots
relinked to the declaration that proves the stated claim. Both documents compile; every dot audits
against the frozen Lean sources (mirror now 644 dots, note 221).

### Systematic patterns found

1. **Header dots certifying more than the Lean statement.** Lemma/theorem headers in §4 (ladder
   algebra, extended ladder, number operator, QHO), the Taylor-tree headline dots (`d = 2` wrappers
   where the general-`d` theorem `thm_TaylorTree_taylor` exists), `thm:strataempiricalexpansion`
   (chart level, conditional on data convergence), and `cor:empirical_expectation` (moved into its
   scope remark).
2. **Geometry: pointwise/linear-frame/additive-family Lean under general-manifold prose** (§4
   conormal splitting, symmetric powers, tubular-neighbourhood definition, coordinate stratum).
   Qualifiers now say so at each dot; the abstract tubular equivalence is conditional on a lifted foot.
3. **Hypothesis leakage in the empirical chain**: zero-phase amplitude datum, `pβM₀² < 2` (or
   `pβκ < 2`) with `p > 1`, bounded amplitude mass, Bochner integrability of the observation,
   `A ≠ 0`/`A > 0` at every phase, finite measures and nonnegative observables in the Laplace-exponent
   material, unit box radii `b = 1` in several stochastic modules.
4. **Printed displays that the Lean corrects** (`eq:lambda_I_f`, `eq:thm_leading_coeff`, the `1/r!`
   in `eq:per_stratum_expansion_coordfree`, the `(log n)^q` vs `(log n)^{q-1}` convention): the dots
   now sit on the corrected statement or carry an explicit qualifier.
5. **Two-sided vs one-sided**: "if and only if" or "exactly when" where Lean has sufficiency
   (bilocal finiteness in `A,B ≤ 0`, annealed remainder threshold, variance `= σ²` vs `≤ σ²`).

## Coverage statement (for the paper)

At revision `fd37665`, the Lean development formalises the statements of §§3–4 of the paper marked
by blue dots, in the versions given by the cited declarations and their hypotheses. The geometric
results use the certified chart, frame and tubular data specified at each dot (chosen normal
families; frame–coframe atlases; a StrucDual tube; a smooth lifted foot); construction of those data
from the paper's geometric setting is included only where explicitly indicated (the coordinate
stratum, StrucDual's compact-set tube). The sampling and annealed conclusions additionally require
the listed coefficient, distributional and remainder hypotheses. The formalisation does not
construct the full resolved geometric setting, does not prove the model-specific remainder
estimates, and does not identify the abstract coefficient family with a model's Taylor coefficients.

## External-hypothesis register

| Input or missing step | Classification | What closure requires |
|---|---|---|
| Hironaka's chart form (Bierstone–Milman Thm 3.2, `Q n`) | **discharged** (CLXXXV; hironaka `eb9b6ca`, `Q_all` axiom-clean) | — |
| Certified resolution charts and their relation to the original model | substantive geometry; bridge unfinished | exact chart identities and domains |
| Analytic units, compatible localisation, passage to the resolved setting | unfinished | a compatibility theorem or an explicit external package |
| Level-set manifold and tangent-image identification (`GeometricIdentification`) | unfinished under suitable regularity | IFT/regular-level-set construction or externally supplied manifold data |
| Certified normal tube (`NormalTubularChart`) | supplied unless constructed (StrucDual: compact set + compatible analytic LCI atlas) | separate existence/compatibility result for the paper's strata |
| Smooth lifted foot (`LiftedFoot`) | unfinished; not implied by an injective smooth map | strong enough embedding hypotheses and the construction |
| Loss factorisation `f = v^k a`, coefficient evaluation `hca`, population mean `hφ` | model-specific | verification for the chosen model and chart |
| Measurability, independence, identical distribution, chart moment certificate | genuine probabilistic assumptions | model verification |
| Uniform full-box sub-Gaussian proxy `κ` | genuine sufficient assumption on the sampling law | verification, or a different tail theorem |
| Scaled `L¹` remainder decay `E|A_n Rem_n| → 0` | substantive model/localisation estimate | proof for the actual remainder |
| A.e. constant face variance (effective-temperature corollary) | additional structural assumption | model verification |
| Common sub-Gaussian proxy across finitely many charts | scope restriction | chart-specific proxies (not opened) |
| Banach `L²` from the coordinate certificate | **discharged** (CLXXXIV) | — |
| Tail certificate reaching the first-moment theorem | **discharged** (CLXXXIV) | — |

## Not done in this pass

Astra #66 unit 5's release-check module beyond the single-chart endpoint (`ClosureEndpoint`); a
theorem for the one-chart triviality of the labelled normal bundle; a Lean lemma for the
`λ + Q/2 = 1/2` case of the number operator; a `Sneg`-independent characterisation of `D_{−ν}`.
