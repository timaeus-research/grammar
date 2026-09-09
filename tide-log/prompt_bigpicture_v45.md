# Direction consult #45 — the arbitrary-continuous-phase programme is done at leading order; what next?

Same setting (Lean 4 + Mathlib, repo `timaeus-research/grammar`, zero `sorry`/`axiom`; resolution/geometric bridge DEFERRED by the user; user wants NEW THEOREMS over process). Grammar main `de397fa`; 76 headlines. Your #44 units 1–5 are done (unit 6, random spatial fields conditional on a `C(box)`-valued CLT, and the joint weak convergence on the product were not attempted).

## Delivered since #44 (Headlines LXXII–LXXVI)
Conventions: box `B = (0,1]^{d}` chart, `P_J` the face projection (coordinates in the minimiser set `J` set to `0`), `w(u) = ∏_{i∉J} u_i^{h_i−2k_iλ}`, face weight `η(P_J u) w(u)`, `M_β(p;a) = ∫₀^∞ s^{p−1}e^{−βs²+βas}ds`, `J_ν(a) = 2M_β(2ν;a)`, `ρ_a ∝ y^{λ−1}e^{−βy+βa√y}`.
- **LXXII**: for continuous `ξ, η`: `𝒵_N[η;ξ]/(N^{−λ}L^{m−1}) → F(ξ,η) = c ∫ η(P_J u) M_β(2λ; ξ(P_J u)) w(u) du` (Headline XIX already allowed a continuous phase); only the face restriction of `ξ` survives; energy tilt = temperature change with pointwise rescaled phase; evidence ratio; weighted energy Laplace limit `E_{Q_N^ξ}[e^{−tNK} g(u)] → r^{−λ}∫ gη(P_J u) M(2λ; ξ(P_J u)/√r) w / ∫ η(P_J u) M(2λ; ξ(P_J u)) w`.
- **LXXIII**: the joint law `Q^ξ ∝ η(P_J u) w(u) y^{λ−1}e^{−βy+βξ(P_J u)√y} dy du` on `(0,∞)×B` as a probability measure; energy marginal = evidence-weighted face mixture of the `ρ_{ξ(P_J u)}` (Laplace transform by Fubini); **weak convergence of the posterior law of `NK` under a fixed continuous phase to it**.
- **LXXIV**: **posterior concentration on the dominant face**: the law of the chart coordinate → `(P_J)_# Q^ξ`, carried by `{u_i = 0, i ∈ J}`, face density `∝ η w J_λ(ξ(v))`.
- **LXXV**: mixed moments `E[(NK)^r g(u)] → ∫ η w g(P_J u) J_{λ+r}(ξ(P_J u))/Z_ξ`; posterior mean = evidence-weighted face average of the tilted means `μ(ξ(v))`.
- **LXXVI**: tilt bound around any continuous base phase; continuity of the face functional under constant shifts; positivity from a positive face weight; `‖ξ_m − ξ₀‖_∞ → 0 ⇒` bounded expectations merge and the posterior law of `NK` converges to `ρ^{ξ₀}`.

Interfaces: `spatialFace`, `spatialPhase_tendsto`, `spatialLaplace_tendsto`, `spatialJointLaw`/`spatialEnergyLimit`/`faceLocationLimit` with integral formulas, `spatialMoment_tendsto`, `phase_observable_bound_base`, `movingPhaseEnergyLaw_tendsto`, plus everything from the constant-phase layer (LIV–LXXI) and the §4 stochastic machinery (four-statistics interface, convergence in distribution of posterior quotients, tightness lemmas, `tendsto_of_laplace`).

## Standing gaps
External by instruction: resolution, charts, partitions of unity, empirical-process CLT (in particular any `C(B)`-valued CLT for the fluctuation field), standard-form identity. NO-GO: all-orders inverse-log division. Not done: next-log corrections with a spatial phase (would need the two-term data of Headline LVII for a spatial phase — the constant-phase two-term theorem came from the Taylor-tree coefficient at `(λ, m−2)` for the constant family; for a general `ξ` the second coefficient involves the phase's Taylor data at the face — is this reachable from the existing `familySpectralCoeff`/`TaylorTreeConclusion` machinery for an analytic `ξ`?); joint weak convergence on `(0,∞)×B`; random spatial fields.

## Candidate directions (rank, cut, replace)
(a) **Spatial-phase next-log correction**: `L(𝒵_N[η;ξ]/(N^{−λ}L^{m−1}) − F(ξ,η)) → B(ξ,η)` for `ξ` given by an analytic family (the fluctuation `ξ` in §4 IS given as a coefficient family `cξ` on the box), and the resulting `c₂(ξ)` for the energy — the §4 machinery (`TaylorTreeConclusion` with data `cξ`, `familySpectralCoeff n h k β cξ cη λ j`) already produces the coefficients at `(λ, j)` for a general family; what is missing is the identification of `C(λ, m−1; cξ)` with `F(ξ,η)` (only done for constant `cξ` in LVI) and of `C(λ,m−2;cξ)`, plus the two-term remainder statement (isolated-remainder lemmas work for any `cξ`). This would upgrade all of LXXII–LXXVI to next-log order for analytic phases.
(b) **Random spatial fields** (your #44 unit 6) conditional on an external `C(B)`-valued CLT: measurability of `ξ ↦ Q_N^ξ`, `Measure.bind`, the random-measure statement — packaging, heavy.
(c) **Joint weak convergence on `(0,∞)×B`**: a product determining-class lemma (energy Laplace functions × continuous location functions) — moderate; makes LXXIII+LXXIV a single joint statement including asymptotic independence of energy and face location.
(d) **Face-restricted phases vs full phases at next order**: is the dependence on the transverse part of the phase at order `1/L`? A clean statement would separate "face" and "transverse" effects.
(e) **Assembly with spatial phases**: chart mixture with different charts' face laws (LXVII generalised) — likely routine.
(f) **A hand-off report** (PDF) for the authors on LIV–LXXVI: process; the user said theorems first, but after 23 headlines beyond the paper a consolidated statement may now be the most useful thing for the authors. Your view?
(g) Something you consider more valuable.

## Ask
A ranked bounded plan (≤ 8 units) with precise target statements, external inputs, non-claims and traps; in particular assess (a): is the next-log spatial correction reachable from the existing Taylor-tree coefficient machinery for an analytic phase family, and what is the correct formula for `B(ξ,η)`? Under ~1800 words.
