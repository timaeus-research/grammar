# Consult #99 — audit of phase 3 (the analytic-neighbourhood bridge) and the direction after it

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 633 modules, zero sorry/axiom; every theorem below checks
`#print axioms = [propext, Classical.choice, Quot.sound]`), companion to *Grammar (Expectations and the
Exceptional Divisor)* (Gerraty–Murfet 2026). Consult #98 designed phase 3; its five units P1–P5 (plus the
small-level selection P0 from #97) have landed as CCCXXVII–CCCXXXII. This consult asks for (A) an independent
AUDIT of what was actually proved against what you designed and against the paper's intent, and (B) the
recommended direction after phase 3, with a unit plan for whatever you recommend.

The user's standing goal: the full asymptotic expansion of `∫_W φ ϕ e^{−nK}` stated coordinate-free (strata of
the exceptional divisor, conormal derivatives, moment tensors, stratum densities), with the certificates
PRODUCED rather than assumed. Phases 1–3 are closed. The remaining assumed pieces, per the plan file: the
certified resolved geometry with a compatible monomial atlas beyond the coordinate model (general SNC
geometry: a.e.-disjoint or multiplicity-corrected change of variables, exact core transport, tail gap, the
analytic unit); complexification of a real-analytic ϕ, φ (the holomorphic extensions are hypotheses);
and the previously deferred items E (projector blow-up model as an instance), J (observable-independent
coefficient functionals), G (two-sided interval / signed coordinates rather than the positive box).

## A. Audit questions

1. Fidelity: does `HolomorphicBoxExtension` (CCCXXX) match the packet you specified — in particular `eqϕ` on
   the REAL SLICE of `Ω` — and does CCCXXXII's conclusion state precisely "for some collar level `δ`, the
   coordinate-free expansion with the certificates constructed"? Is anything in the ∃-statement of
   CCCXXXII weaker than it should be (e.g. `δ` chosen after `A`, so not uniform in the data; the log degree
   `d − 1` rather than the exact one; the lattice `commonQ`)?
2. Hypothesis hygiene: `hϕm : Measurable ϕ`, `hφm : Measurable φ`, `hφint : Integrable φ (ϕ·Leb|_W)` remain
   global hypotheses although ϕ, φ are continuous on the box (real parts of holomorphic functions). Should
   the final theorem discharge them (continuity on a compact box ⇒ measurability/integrability of the
   restriction, with ϕ, φ arbitrary off the box)? Is that a cheap follow-up unit?
3. Any soundness/vacuity risk: e.g. could `HolomorphicBoxExtension` be unsatisfiable for natural inputs,
   or satisfiable only trivially? Is the `ofRealNhd` wrapper (agreement on a real open neighbourhood of the
   box, then restrict Ω) the right public form? Is the box-only agreement theorem worth adding as a
   separately named "chosen-extension" statement, or should it be left as a documented non-claim?
4. The mirror sentence added to `grammar_lean.tex` (reproduced below) — is it accurate and appropriately
   hedged? Suggest a correction if not.
5. Anything in the six files that a fidelity reviewer would flag (names, docstrings overclaiming, dead
   hypotheses, redundant fields)?

## B. Direction

Rank the candidates and give a unit plan (statement sketches, Mathlib routes, pitfalls, size) for the top
one; state a stopping gate:
  (i) complexification: from real-analyticity of ϕ, φ on a neighbourhood of the box (Mathlib
      `AnalyticOnNhd ℝ`) to a `HolomorphicBoxExtension` — is there a Mathlib route (e.g. `AnalyticAt` →
      `HasFPowerSeriesOnBall` → complex extension of the power series via `FormalMultilinearSeries` over ℂ,
      uniqueness of analytic continuation for gluing)? Honest size estimate.
  (ii) discharging the measurability/integrability hypotheses (A2).
  (iii) G: signed coordinates `[−a,a]^d` (both sides of each divisor), via a reflection cover with 2^d boxes
      or an even/odd decomposition; how does `posPart` interact?
  (iv) E: the projector blow-up model as an instance of the certified compact-box producer (a first
      non-coordinate geometry on which the whole chain is a theorem).
  (v) J: observable-independent coefficient functionals (distributions on the strata).
  (vi) general SNC geometry with a compatible monomial atlas (the big one): what is the minimal
      certificate interface such that the coordinate-box producer becomes the local model and the global
      statement follows by a partition of unity / a.e.-disjoint charts?
Also say explicitly whether the programme should STOP here as far as the paper is concerned, and what the
paper should claim.

## C. Material

### The mirror sentence (grammar_lean.tex, Lean paragraph)
"Finally the local normal series themselves are produced from analytic data: for a prior and an observable
that are the real parts of holomorphic functions on a complex neighbourhood of the embedded box, agreeing
with them on its real slice (or on a real neighbourhood of the box), the real Cauchy coefficients of the
recentred normal functions z ↦ H(s + Σ_i z_i e_{σi}) at the closed faces form uniform series families at a
common radius — one uniform complex buffer around the compact box, one bound on the compact tube, Cauchy
estimates with a strict radius shrink — and the collar level is then chosen small enough to fit these
radii, so that the original integral ∫_{[0,a]^d} φ ϕ e^{−nK} dw has the coordinate-free expansion with
stratum-integral coefficients for some collar level, with the certificates constructed from the
extensions." Non-claim: "the holomorphic extensions on a complex neighbourhood of the box are hypotheses,
and their construction from real analyticity is not included".

### HEADLINES rows CCCXXVII–CCCXXXII
| **CCCXXXII** | ★★★ **THE COORDINATE-FREE EXPANSION FROM HOLOMORPHIC DATA NEAR THE BOX (u650; phase 3 unit P5, consult #98 §7 — PHASE 3 STOPPING GATE)**: composing the bridge (CCCXXVIII–CCCXXXI) with the compact-box producer (CCCXXIV–CCCXXVII): for the coordinate monomial phase on `[0,a]^d`, a prior and an observable that are the real parts of holomorphic functions on a complex neighbourhood of the embedded box (`HolomorphicBoxExtension`; the wrapper `HolomorphicBoxExtension.ofRealNhd` accepts agreement on an open REAL neighbourhood of the box, via `Ω ∩ {Re z ∈ V}`), with the producer's measurability, nonnegativity and integrability assumptions, the original integral `∫_{[0,a]^d} φϕe^{−nK}` has the coordinate-free expansion FOR SOME collar level `δ` (exhibited with `δ^{1/d} < a^{2k_i}`, `2δ^{1/(2k_i d)} < A.radius`), with the stratum measures and the coefficient field of the certificates constructed from the extension's face series: ★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension` (globally nonnegative prior) and ★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on` (prior nonnegative on the box; certificate of `ϕ⁺`). Spectrum `{(α,j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ d−1}` with `Q` the cores' common lattice. Non-claims: the holomorphic extensions are hypotheses (complexification from real analyticity is not included); the observable identity is used on the full open normal balls; global measurability retained; general SNC geometry untouched. Axiom-clean | AnalyticCoordinateBoxExpansion.lean |
| **CCCXXXI** | ★★ **FACE SERIES FROM A HOLOMORPHIC BOX EXTENSION (u649; phase 3 unit P4, consult #98 §4)**: for a `HolomorphicBoxExtension a ϕ φ` with buffer radius `R` and tube bound `M`, the RECENTRED normal family `G_s(z) = H(complexify s + complexInsert I z)` over the closed face `X_I` satisfies containment (`recentred_mem`), holomorphicity in `z` on the open polydisc of radius `R` (`differentiableOn_recentred`), joint continuity on `X_I × closedPolydisc (R/2)` (`continuousOn_recentred`) and the uniform bound `M` (`norm_recentred_le`); hence `analyticUniformSeries` at `ρ = R/4 < R/2 < R` gives `HolomorphicBoxExtension.uniformSeries`, and reconstruction + `complexify_originalNormalMap` + the real-slice identity give `evalF_uniformSeries : evalF = Re H (complexify Ψ_I(s,u))` for `‖u‖ < ρ`. Result: ★★ `HolomorphicBoxExtension.faceSeries A I : OriginalFaceSeries a ϕ φ I` at the COMMON radius `A.radius = R/4` (`faceSeries_ρ`), and ★★ `exists_originalFaceSeries_of_holomorphicBoxExtension : ∃ ρ > 0, ∃ O, ∀ I, (O I).ρ = ρ`. No differentiation in the face parameter, no compatibility across faces; the strict radius shrinks `ρ < r < R` are the Cauchy-estimate obligations. Axiom-clean | HolomorphicOriginalFaceSeries.lean |
| **CCCXXX** | ★ **HOLOMORPHIC EXTENSIONS NEAR THE BOX: THE UNIFORM BUFFER (u648; phase 3 unit P3, consult #98 §1.1, §3.3–3.4)**: the primary analytic hypothesis packet `HolomorphicBoxExtension a ϕ φ` (open `Ω ⊆ ℂ^d` containing the complexified box, holomorphic `Hϕ Hφ` on `Ω`, and agreement `ϕ w = Re Hϕ (complexify w)` on the REAL SLICE of `Ω` — the normal form of agreement on a real neighbourhood; box-only agreement is a different theorem); `isCompact_complexify_box`; ★ `exists_uniform_complex_box_buffer : ∃ R > 0, ∀ w ∈ [0,a]^d, ∀ z, ‖z‖ ≤ R → complexify w + z ∈ Ω` (closed thickening of the compact embedded box, `IsCompact.exists_cthickening_subset_open`); the compact tube `tube a R` (`isCompact_tube`, `mem_tube`, `tube_subset`) and ★ `exists_bound_on_tube` (uniform bound of a holomorphic function on the tube); `HolomorphicBoxExtension.exists_buffer/exists_bounds` — ONE radius and ONE bound for all faces. Axiom-clean | HolomorphicBoxBuffer.lean |
| **CCCXXIX** | ★ **COMPLEXIFICATION AND THE COMPLEX NORMAL INSERTION (u647; phase 3 unit P2, consult #98 §3.1–3.2)**: `complexify w = (w_j : ℂ)_j`, the insertion CLM `complexInsert I : ℂ^{|I|} →L[ℂ] ℂ^d` (coordinates `z_{σ⁻¹j}` on `I`, `0` off `I`; `complexInsert_apply`), the sup-norm bound `norm_complexInsert_le : ‖complexInsert I z‖ ≤ ‖z‖` (no dimensional constant), the compatibility `complexify_originalNormalMap : complexify (Ψ_I(s,u)) = complexify s + complexInsert I (complexify u)`, and `isCompact_faceSet` (the closed face is the compact box cut by finitely many closed coordinate conditions). Axiom-clean | ComplexNormalInsertion.lean |
| **CCCXXVIII** | ★ **ARBITRARY-RADIUS ANALYTIC UNIFORM SERIES (u646; phase 3 unit P1, consult #98 §2)**: for a family `F : X → (Fin m → ℂ) → ℂ` jointly continuous and bounded by `M` on the closed polydisc of radius `r`, the real Cauchy coefficients at radius `r` form a `UniformSeriesFamily X m ρ` for every `0 < ρ < r` (★ `analyticUniformSeries`: continuity from `continuous_polyRealCoeff_param`, the majorant `M r^{-|γ|}` from `norm_polyCoeff_le`, and its `ρ`-summability `summable_cauchyMajorant_weight` from the multivariate geometric series `summable_prodGeom` — the strict radius shrink `ρ < r` is the whole obligation); for `F x` holomorphic on the open polydisc of radius `R > r` the series represents `Re (F x)` on the real ball of radius `r` (`evalF_analyticUniformSeries`, from `evalF_polyRealCoeff_of_lt`). Unlike `analyticDatum` (scale 1, radius `> 1`) this works at every radius in the ORIGINAL normal variables. Axiom-clean | AnalyticUniformSeries.lean |
| **CCCXXVII** | ★ **SMALL-LEVEL SELECTION FOR THE COLLAR (u645; consult #97 §3.2)**: for every radius `ρ > 0` there is a collar level `δ > 0` with `δ^{1/d} < a^{2k_i}` and `2δ^{1/(2k_i d)} < ρ` for all `i` (`exists_delta`: each `δ ↦ δ^c`, `c > 0`, tends to `0` at `0⁺`, finitely many constraints, `Filter.eventually_all` on `𝓝[>] 0`). Hence ★★★ `hasCoordFreeExpansion_collar_of_face_exists`: from original-variable face series at any radii (a common lower radius over the finitely many faces is taken), the compact-box expansion holds for SOME collar level, with the certificate and the coefficient field exhibited for the chosen `δ` — no smallness hypothesis is left to the user. The collar level is chosen AFTER the analytic data, as the bridge design requires. Axiom-clean | CollarDeltaSelection.lean |

### Plan file, section 5c (phase 3 table) and section 6 (what remains a hypothesis)
## 5c. Phase 3 — the complex analytic-neighbourhood bridge (consult #98, 2026-09-12)

Goal: from holomorphic extensions of the prior and the observable on a complex neighbourhood of the
embedded compact box, agreeing with them on its real slice (`HolomorphicBoxExtension`), produce the
closed-face normal series `OriginalFaceSeries` at a COMMON radius `ρ`, then choose the collar level
(CCCXXVII) and feed CCCXXV. Interfaces stay unchanged (per-face `ρ` kept downstream). Box-only agreement
gives a different theorem (about chosen extensions) and is optional; complexification from real
analyticity is NOT part of this phase.

| unit | module | content | status |
|---|---|---|---|
| P0 | `CollarDeltaSelection` (CCCXXVII) | small-level selection `exists_delta`; `hasCoordFreeExpansion_collar_of_face_exists` | done |
| P1 | `AnalyticUniformSeries` (CCCXXVIII) | radius-parametric Cauchy → `UniformSeriesFamily X m ρ` for `0 < ρ < r < R` (`polyRealCoeff m r`, majorant `M r^{-|γ|}`, weighted geometric summability, reconstruction `evalF = Re F` on the real ball of radius `r`) | done |
| P2 | `ComplexNormalInsertion` (CCCXXIX) | `complexify`, insertion CLM `L_I : ℂ^m →L ℂ^d`, `‖L_I z‖ ≤ ‖z‖`, compatibility with `originalNormalMap`, `isCompact_faceSet` | done |
| P3 | `HolomorphicBoxBuffer` (CCCXXX) | `HolomorphicBoxExtension` packet; uniform buffer `∃ R > 0, ∀ w ∈ W, ∀ z, ‖z‖ ≤ R → complexify w + z ∈ Ω` (closed thickening), compact tube, uniform bounds | done |
| P4 | `HolomorphicOriginalFaceSeries` (CCCXXXI) | recentred family `G s z = H(complexify s + L_I z)`; containment, holomorphicity, joint continuity, bounds; common-radius `OriginalFaceSeries` producer (`exists_originalFaceSeries_of_holomorphicBoxExtension`) | done |
| P5 | `AnalyticCoordinateBoxExpansion` (CCCXXXII) | composition: holomorphic box extension ⇒ coordinate-free expansion for some collar level (★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension`, `_nonneg_on`); real-neighbourhood wrapper `ofRealNhd` | done |

Status: main `41fc8bf`, 633 modules; PHASE 3 STOPPING GATE MET (complex neighbourhood → unchanged closed-face interface → existing certificates and expansion). Not included: complexification from real analyticity; box-only agreement (chosen extensions); optimal (lcm) spectral lattice; general SNC geometry.

## 6. Hypotheses that remain at the end

Certified resolved geometry with a compatible monomial atlas (a.e.-disjoint or multiplicity-corrected
change of variables, exact core transport, tail gap, unit handling), analytic admissibility of `φ`
(radii, majorants), uniform integrable bounds for the base integrals. Everything else — the strata,
the normal differentials, the moment coefficients, the densities, the expansion — is a theorem.


### Full source of the six phase-3 files (733 lines)

#### Grammar/CollarDeltaSelection.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxInputs

/-!
# Small-level selection for the collar (CCCXXVII)

Consult #97 §3.2: the collar level `δ` should be chosen AFTER the face series, so that the collar
fits their radii. For every radius `ρ > 0` there is `δ > 0` with `δ^{1/d} < a^{2k_i}` (the collar
lies in the box) and `2 δ^{1/(2k_i d)} < ρ` (the rescaled normal ball lies in the series ball) for
every `i` (`exists_delta`: every `δ ↦ δ^c`, `c > 0`, tends to `0` at `0⁺`, and there are finitely
many constraints). Hence the compact-box expansion from original-variable face series holds for
SOME collar level, with no smallness hypothesis left to the user
(`hasCoordFreeExpansion_collar_of_face_exists`): the certificate and its coefficient field are
exhibited for the chosen `δ`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a : ℝ)

omit k hk a in
/-- `δ ↦ δ^c` tends to `0` at `0` for `c > 0`. -/
theorem tendsto_rpow_const_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => δ ^ c) (𝓝 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto
  rwa [Real.zero_rpow hc.ne'] at h

include hk in
/-- ★ **Small-level selection**: for every radius `ρ > 0` there is a collar level `δ > 0` with
`δ^{1/d} < a^{2k_i}` and `2 δ^{1/(2k_i d)} < ρ` for every `i`. -/
theorem exists_delta (hd : 0 < d) (ha : 0 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      ∀ i, 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ := by
  have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hd)
  have h1 : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i) :=
    Filter.eventually_all.2 fun i =>
      (tendsto_rpow_const_zero hdpos).eventually_lt_const (pow_pos ha _)
  have h2 : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ / 2 :=
    Filter.eventually_all.2 fun i => by
      have hc : 0 < (d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹ := by
        have := hk i
        positivity
      exact (tendsto_rpow_const_zero hc).eventually_lt_const (by linarith)
  have h3 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, h1δ, h2δ⟩ :=
    (h3.and ((h1.and h2).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨δ, hδ, h1δ, fun i => by linarith [h2δ i]⟩

variable (ϕ φ : (Fin d → ℝ) → ℝ)

/-- ★★★ **The compact-box expansion from original-variable face series, for some collar level**:
no smallness hypothesis is left to the user; the certificate and the coefficient field are
exhibited for the chosen `δ`. -/
theorem hasCoordFreeExpansion_collar_of_face_exists (hd : 0 < d) (ha : 0 < a)
    (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
    (hφint : Integrable φ
      ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
    (O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
        (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
        (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  -- the common lower radius over the finitely many faces
  have hne : Nonempty (NonemptyIdx d) :=
    ⟨⟨Finset.univ, ⟨⟨0, hd⟩, Finset.mem_univ _⟩⟩⟩
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_min_image Finset.univ (fun I : NonemptyIdx d => (O I).ρ)
    Finset.univ_nonempty
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta k hk a hd ha (O I₀).hρ
  have hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ := fun I i =>
    (hsm (σI I i).1).trans_le (hI₀ I (Finset.mem_univ _))
  exact ⟨δ, hδ, hδa, hsmall,
    hasCoordFreeExpansion_collar_of_face k hk a δ hϕm hφm hφint hδ hd ha hδa hϕ0 O hsmall⟩

end WaterFilling

end Grammar
```

#### Grammar/AnalyticUniformSeries.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticFamilyData
import Grammar.ParameterisedSeriesDatum

/-!
# Arbitrary-radius analytic uniform series (CCCXXVIII; phase 3, unit P1)

Consult #98 §2. For a family `F : X → (Fin m → ℂ) → ℂ` of holomorphic functions on the open polydisc
of radius `R`, jointly continuous and uniformly bounded by `M` on the closed polydisc of radius
`r < R`, the real Cauchy coefficients at radius `r` form a `UniformSeriesFamily X m ρ` for every
`0 < ρ < r` (`analyticUniformSeries`): the coefficients are continuous in the parameter
(`continuous_polyRealCoeff_param`), dominated by `M r^{-|γ|}` (`norm_polyCoeff_le`), and the
majorant is `ρ`-summable because `Σ_γ M (ρ/r)^{|γ|} = Σ_γ M ∏_i (ρ/r)^{γ_i}` converges
(`summable_cauchyMajorant_weight`, the multivariate geometric series `summable_prodGeom`).
The represented function is the real part of `F x` on the real ball of radius `r`
(`evalF_analyticUniformSeries`, from `evalF_polyRealCoeff_of_lt`). Unlike `analyticDatum` (scale 1)
this works at every radius in the ORIGINAL normal variables. Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

open CoeffFamily

/-- The Cauchy majorant `M r^{-|γ|}` is summable against the weight `ρ^{|γ|}` for `0 ≤ ρ < r`. -/
theorem summable_cauchyMajorant_weight (m : ℕ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) (M : ℝ) :
    Summable fun γ : Fin m → ℕ => |M * r⁻¹ ^ (∑ i, γ i)| * ρ ^ (∑ i, γ i) := by
  have hr : 0 < r := hρ.trans_lt hρr
  have hq0 : 0 ≤ ρ / r := div_nonneg hρ hr.le
  have hq1 : ρ / r < 1 := (div_lt_one hr).2 hρr
  refine ((summable_prodGeom m (q := fun _ => ρ / r) (fun _ => hq0) fun _ => hq1).mul_left
    |M|).congr fun γ => ?_
  rw [Finset.prod_pow_eq_pow_sum, abs_mul, abs_pow, abs_inv, abs_of_pos hr, div_pow, mul_assoc,
    inv_pow, ← div_eq_inv_mul, mul_div_assoc']

variable {X : Type*} [TopologicalSpace X] {m : ℕ} {ρ r R M : ℝ}

/-- ★ **Analytic uniform series at an arbitrary radius**: the real Cauchy coefficients at radius `r`
of a holomorphic family, jointly continuous and bounded by `M` on the closed polydisc of radius `r`,
form a `ρ`-summable uniform series family for every `ρ < r`. -/
noncomputable def analyticUniformSeries (hρ : 0 < ρ) (hρr : ρ < r) (F : X → (Fin m → ℂ) → ℂ)
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) : UniformSeriesFamily X m ρ where
  f x := polyRealCoeff m r (F x)
  M γ := M * r⁻¹ ^ (∑ i, γ i)
  continuous_coeff γ := continuous_polyRealCoeff_param (hρ.trans hρr) hcont γ
  abs_le x γ := by
    refine (Complex.abs_re_le_norm _).trans (norm_polyCoeff_le (hρ.trans hρr) ?_ γ)
    exact fun w hw => hbound x w (torusSet_subset_closedPolydisc m r hw)
  M_abs := summable_cauchyMajorant_weight m hρ.le hρr M

theorem analyticUniformSeries_f (hρ : 0 < ρ) (hρr : ρ < r) (F : X → (Fin m → ℂ) → ℂ)
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) :
    (analyticUniformSeries hρ hρr F hcont hbound).f x = polyRealCoeff m r (F x) := rfl

/-- Reconstruction on the real ball of radius `r`: the series represents `Re (F x)`. -/
theorem evalF_analyticUniformSeries (hρ : 0 < ρ) (hρr : ρ < r) (hrR : r < R)
    (F : X → (Fin m → ℂ) → ℂ) (hhol : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc m R))
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) {u : Fin m → ℝ}
    (hu : ‖u‖ < r) :
    evalF ((analyticUniformSeries hρ hρr F hcont hbound).f x) u = (F x fun i => (u i : ℂ)).re := by
  rw [analyticUniformSeries_f]
  refine evalF_polyRealCoeff_of_lt (hρ.trans hρr) hrR (hhol x) fun i => ?_
  rw [Complex.norm_real]
  exact (norm_le_pi_norm u i).trans_lt hu

/-- Reconstruction on the series ball `‖u‖ < ρ`. -/
theorem evalF_analyticUniformSeries_of_lt (hρ : 0 < ρ) (hρr : ρ < r) (hrR : r < R)
    (F : X → (Fin m → ℂ) → ℂ) (hhol : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc m R))
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) {u : Fin m → ℝ}
    (hu : ‖u‖ < ρ) :
    evalF ((analyticUniformSeries hρ hρr F hcont hbound).f x) u = (F x fun i => (u i : ℂ)).re :=
  evalF_analyticUniformSeries hρ hρr hrR F hhol hcont hbound x (hu.trans hρr)

end Grammar
```

#### Grammar/ComplexNormalInsertion.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxInputs

/-!
# Complexification and the complex normal insertion (CCCXXIX; phase 3, unit P2)

Consult #98 §3.1–3.2. `complexify w = (w_j : ℂ)_j` embeds `ℝ^d` into `ℂ^d` (sup norms); for a
nonempty coordinate set `I` the complex normal insertion `complexInsert I : ℂ^{|I|} →L[ℂ] ℂ^d` puts
`z_{σ⁻¹ j}` in the coordinates `j ∈ I` and `0` elsewhere; it is norm-nonincreasing (sup norm — no
dimensional constant) and compatible with the real insertion:
`complexify (originalNormalMap I s u) = complexify s + complexInsert I (complexify u)`. The closed
faces `X_I` are compact. Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

variable {d : ℕ}

/-- Coordinatewise complexification `ℝ^d → ℂ^d`. -/
def complexify (w : Fin d → ℝ) : Fin d → ℂ := fun j => (w j : ℂ)

theorem complexify_apply (w : Fin d → ℝ) (j : Fin d) : complexify w j = (w j : ℂ) := rfl

theorem continuous_complexify : Continuous (complexify (d := d)) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

theorem complexify_add (w v : Fin d → ℝ) : complexify (w + v) = complexify w + complexify v := by
  funext j
  simp [complexify]

/-- The complex normal insertion `z ↦ Σ_i z_i e_{σ i}` as a continuous linear map. -/
noncomputable def complexInsert (I : NonemptyIdx d) :
    (Fin (nI I + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun j : Fin d =>
    if h : j ∈ I.1 then ContinuousLinearMap.proj ((σI I).symm ⟨j, h⟩) else 0

theorem complexInsert_apply (I : NonemptyIdx d) (z : Fin (nI I + 1) → ℂ) (j : Fin d) :
    complexInsert I z j = if h : j ∈ I.1 then z ((σI I).symm ⟨j, h⟩) else 0 := by
  rw [complexInsert, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- The insertion is norm-nonincreasing for the sup norms. -/
theorem norm_complexInsert_le (I : NonemptyIdx d) (z : Fin (nI I + 1) → ℂ) :
    ‖complexInsert I z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  rw [complexInsert_apply]
  split_ifs
  · exact norm_le_pi_norm z _
  · rw [norm_zero]
    exact norm_nonneg z

/-- Compatibility with the real insertion:
`complexify (Ψ_I(s, u)) = complexify s + complexInsert I (complexify u)`. -/
theorem complexify_originalNormalMap (I : NonemptyIdx d) (s : Fin d → ℝ)
    (u : Fin (nI I + 1) → ℝ) :
    complexify (originalNormalMap I s u) = complexify s + complexInsert I (complexify u) := by
  funext j
  rw [Pi.add_apply, complexInsert_apply, complexify_apply, complexify_apply, originalNormalMap]
  by_cases hj : j ∈ I.1
  · rw [dif_pos hj, dif_pos hj, Complex.ofReal_add]
    rfl
  · rw [dif_neg hj, dif_neg hj, add_zero]

variable (a : ℝ)

/-- The closed faces are compact. -/
theorem isCompact_faceSet (I : Finset (Fin d)) : IsCompact (faceSet a I) := by
  have hbox : IsCompact (piBox d (Icc 0 a)) := isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ fun w hw => hw.1
  have : faceSet a I = piBox d (Icc 0 a) ∩ ⋂ i ∈ I, {w : Fin d → ℝ | w i = 0} := by
    ext w
    simp only [faceSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [this]
  refine (isClosed_set_pi fun _ _ => isClosed_Icc).inter (isClosed_biInter fun i _ => ?_)
  exact isClosed_eq (continuous_apply i) continuous_const

/-- Points of the closed face lie in the box. -/
theorem mem_piBox_of_mem_faceSet {I : Finset (Fin d)} {w : Fin d → ℝ} (hw : w ∈ faceSet a I) :
    w ∈ piBox d (Icc 0 a) := hw.1

end WaterFilling

end Grammar
```

#### Grammar/HolomorphicBoxBuffer.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ComplexNormalInsertion

/-!
# Holomorphic extensions near the box: the uniform buffer (CCCXXX; phase 3, unit P3)

Consult #98 §1.1, §3.3–3.4. The primary analytic hypothesis of the bridge is the packet
`HolomorphicBoxExtension a ϕ φ`: an open `Ω ⊆ ℂ^d` containing the complexified box `[0,a]^d`,
holomorphic `Hϕ Hφ` on `Ω`, and agreement `ϕ w = Re Hϕ (complexify w)` on the REAL SLICE of `Ω`
(the normal form of "agreement on a real neighbourhood of the box"; agreement only on the box would
be a different theorem, about chosen extensions).

Compactness of the embedded box gives a UNIFORM buffer `R > 0` with `complexify w + z ∈ Ω` for all
`w ∈ [0,a]^d` and `‖z‖ ≤ R` (`exists_uniform_complex_box_buffer`, from the closed thickening
`IsCompact.exists_cthickening_subset_open`), the compact tube `tube a R = {complexify w + z}`
lies in `Ω` (`isCompact_tube`, `tube_subset`), and a holomorphic function on `Ω` is uniformly
bounded on it (`exists_bound_on_tube`). One radius and one bound serve all faces.
Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

variable {d : ℕ} (a : ℝ)

/-- **Holomorphic box extension**: holomorphic extensions of the prior and the observable on a
complex neighbourhood of the box, agreeing with them on its real slice. -/
structure HolomorphicBoxExtension (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the complex neighbourhood -/
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω
  /-- the holomorphic extensions -/
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re

theorem isCompact_complexify_box : IsCompact (complexify '' piBox d (Icc 0 a)) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).image continuous_complexify

/-- ★ **The uniform complex buffer**: an open set containing the complexified box contains all
`complexify w + z` with `w` in the box and `‖z‖ ≤ R`, for some `R > 0`. -/
theorem exists_uniform_complex_box_buffer {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω)
    (hWΩ : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω) :
    ∃ R : ℝ, 0 < R ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      complexify w + z ∈ Ω := by
  obtain ⟨R, hR, hsub⟩ := (isCompact_complexify_box a).exists_cthickening_subset_open hΩ (by
    rintro _ ⟨w, hw, rfl⟩
    exact hWΩ w hw)
  refine ⟨R, hR, fun w hw z hz => hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ ⟨w, hw, rfl⟩ ?_)⟩
  rw [dist_eq_norm, add_sub_cancel_left]
  exact hz

/-- The compact tube `{complexify w + z : w ∈ [0,a]^d, ‖z‖ ≤ R}` around the embedded box. -/
def tube (R : ℝ) : Set (Fin d → ℂ) :=
  (fun p : (Fin d → ℝ) × (Fin d → ℂ) => complexify p.1 + p.2) ''
    (piBox d (Icc 0 a) ×ˢ Metric.closedBall 0 R)

theorem isCompact_tube (R : ℝ) : IsCompact (tube (d := d) a R) := by
  have hK : IsCompact (piBox d (Icc 0 a)) := isCompact_univ_pi fun _ => isCompact_Icc
  exact (hK.prod (isCompact_closedBall 0 R)).image
    (show Continuous fun p : (Fin d → ℝ) × (Fin d → ℂ) => complexify p.1 + p.2 from
      (continuous_complexify.comp continuous_fst).add continuous_snd)

theorem mem_tube {R : ℝ} {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 a)) {z : Fin d → ℂ}
    (hz : ‖z‖ ≤ R) : complexify w + z ∈ tube a R :=
  ⟨(w, z), ⟨hw, mem_closedBall_zero_iff.2 hz⟩, rfl⟩

theorem tube_subset {Ω : Set (Fin d → ℂ)} {R : ℝ}
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω) :
    tube a R ⊆ Ω := by
  rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact hbuf w hw z (mem_closedBall_zero_iff.1 hz)

/-- ★ **Uniform bound on the tube**: a holomorphic function on `Ω` is bounded on the compact
tube. -/
theorem exists_bound_on_tube {Ω : Set (Fin d → ℂ)} {R : ℝ} {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω)
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      ‖H (complexify w + z)‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_tube a R).exists_bound_of_continuousOn
    (hH.continuousOn.mono (tube_subset a hbuf))
  exact ⟨max C 0, le_max_right _ _, fun w hw z hz =>
    (hC _ (mem_tube a hw hz)).trans (le_max_left _ _)⟩

namespace HolomorphicBoxExtension

variable {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)

/-- The buffer radius of the extension. -/
theorem exists_buffer : ∃ R : ℝ, 0 < R ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
    complexify w + z ∈ A.Ω :=
  exists_uniform_complex_box_buffer a A.isOpen_Ω A.box_subset

/-- Uniform bounds for both extensions on a common tube. -/
theorem exists_bounds {R : ℝ}
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ A.Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      ‖A.Hϕ (complexify w + z)‖ ≤ M) ∧
      ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → ‖A.Hφ (complexify w + z)‖ ≤ M := by
  obtain ⟨M₁, hM₁, h₁⟩ := exists_bound_on_tube a A.holϕ hbuf
  obtain ⟨M₂, hM₂, h₂⟩ := exists_bound_on_tube a A.holφ hbuf
  exact ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _),
    fun w hw z hz => (h₁ w hw z hz).trans (le_max_left _ _),
    fun w hw z hz => (h₂ w hw z hz).trans (le_max_right _ _)⟩

end HolomorphicBoxExtension

end WaterFilling

end Grammar
```

#### Grammar/HolomorphicOriginalFaceSeries.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.HolomorphicBoxBuffer
import Grammar.AnalyticUniformSeries

/-!
# Face series from a holomorphic box extension (CCCXXXI; phase 3, unit P4)

Consult #98 §4. For a holomorphic box extension `A` (CCCXXX) with uniform buffer radius `R` and
uniform bound `M` on the tube, and a nonempty coordinate set `I`, the RECENTRED normal family
`G_s(z) = H (complexify s + complexInsert I z)` over the closed face `X_I` satisfies, in order:

* A. containment: `complexify s + complexInsert I z ∈ Ω` for `‖z‖ ≤ R` (the insertion is
  norm-nonincreasing; `recentred_mem`);
* B. holomorphicity in `z` on the open polydisc of radius `R` (`differentiableOn_recentred`);
* C. joint continuity on `X_I × closedPolydisc (R/2)` (`continuousOn_recentred`);
* D. the uniform bound `M` on the closed polydisc of radius `R/2` (`norm_recentred_le`);
* E. the uniform series family at radius `ρ = R/4` (`analyticUniformSeries`, CCCXXVIII);
* F. the evaluation identity for the ORIGINAL real functions on the real ball of radius `ρ`
  (reconstruction + `complexify_originalNormalMap` + the real-slice identity of `A`).

Hence ★★ `HolomorphicBoxExtension.faceSeries A I : OriginalFaceSeries a ϕ φ I` at the COMMON radius
`A.radius = R/4` (`faceSeries_ρ`), and ★★ `exists_originalFaceSeries_of_holomorphicBoxExtension`.
No differentiation in the face parameter and no compatibility across faces is needed.
Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoeffFamily

variable {d : ℕ} (a : ℝ)

/-- The recentred normal family `G_s(z) = H (complexify s + complexInsert I z)` over the closed
face. -/
noncomputable def recentred (H : (Fin d → ℂ) → ℂ) (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    (z : Fin (nI I + 1) → ℂ) : ℂ :=
  H (complexify s.1 + complexInsert I z)

theorem norm_le_of_mem_closedPolydisc {m : ℕ} {r : ℝ} (hr : 0 ≤ r) {z : Fin m → ℂ}
    (hz : z ∈ closedPolydisc m r) : ‖z‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 (mem_closedPolydisc.1 hz)

theorem norm_lt_of_mem_openPolydisc {m : ℕ} {r : ℝ} (hr : 0 < r) {z : Fin m → ℂ}
    (hz : z ∈ openPolydisc m r) : ‖z‖ < r :=
  (pi_norm_lt_iff hr).2 (mem_openPolydisc.1 hz)

theorem norm_complexify_le (u : Fin d → ℝ) : ‖complexify u‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i => by
    rw [complexify_apply, Complex.norm_real]
    exact norm_le_pi_norm u i

section Recentred

variable {Ω : Set (Fin d → ℂ)} {R : ℝ}
  (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω)
  (I : NonemptyIdx d)

include hbuf in
/-- A. Containment of the recentred polydisc in `Ω`. -/
theorem recentred_mem (s : ↥(faceSet a I.1)) {z : Fin (nI I + 1) → ℂ} (hz : ‖z‖ ≤ R) :
    complexify s.1 + complexInsert I z ∈ Ω :=
  hbuf s.1 (mem_piBox_of_mem_faceSet a s.2) _ ((norm_complexInsert_le I z).trans hz)

include hbuf in
/-- B. Holomorphicity of the recentred family in the normal variable. -/
theorem differentiableOn_recentred (hR : 0 < R) {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω) (s : ↥(faceSet a I.1)) :
    DifferentiableOn ℂ (recentred a H I s) (openPolydisc (nI I + 1) R) := by
  refine hH.comp ((differentiable_const _).add (complexInsert I).differentiable).differentiableOn
    fun z hz => ?_
  exact recentred_mem a hbuf I s (norm_lt_of_mem_openPolydisc hR hz).le

include hbuf in
/-- C. Joint continuity of the recentred family on the face times the closed polydisc. -/
theorem continuousOn_recentred {r : ℝ} (hrR : r ≤ R) {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω) :
    ContinuousOn (fun p : ↥(faceSet a I.1) × (Fin (nI I + 1) → ℂ) => recentred a H I p.1 p.2)
      (univ ×ˢ closedPolydisc (nI I + 1) r) := by
  have hin : Continuous fun p : ↥(faceSet a I.1) × (Fin (nI I + 1) → ℂ) =>
      complexify p.1.1 + complexInsert I p.2 :=
    (continuous_complexify.comp (continuous_subtype_val.comp continuous_fst)).add
      ((complexInsert I).continuous.comp continuous_snd)
  refine hH.continuousOn.comp hin.continuousOn fun p hp => ?_
  have hr0 : 0 ≤ r := by
    rcases (mem_closedPolydisc.1 hp.2) with h
    by_cases hm : Nonempty (Fin (nI I + 1))
    · obtain ⟨i⟩ := hm
      exact (norm_nonneg _).trans (h i)
    · exact absurd ⟨0⟩ hm
  exact recentred_mem a hbuf I p.1 ((norm_le_of_mem_closedPolydisc hr0 hp.2).trans hrR)

omit hbuf in
/-- D. The uniform bound of the recentred family on the closed polydisc. -/
theorem norm_recentred_le {r M : ℝ} (hrR : r ≤ R) {H : (Fin d → ℂ) → ℂ}
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → ‖H (complexify w + z)‖ ≤ M)
    (s : ↥(faceSet a I.1)) {z : Fin (nI I + 1) → ℂ} (hz : ‖z‖ ≤ r) :
    ‖recentred a H I s z‖ ≤ M :=
  hM s.1 (mem_piBox_of_mem_faceSet a s.2) _ ((norm_complexInsert_le I z).trans (hz.trans hrR))

end Recentred

namespace HolomorphicBoxExtension

variable {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)

/-- The buffer radius of the extension. -/
noncomputable def bufferRadius : ℝ := (A.exists_buffer a).choose

theorem bufferRadius_pos : 0 < A.bufferRadius a := (A.exists_buffer a).choose_spec.1

theorem buffer_mem : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    complexify w + z ∈ A.Ω :=
  (A.exists_buffer a).choose_spec.2

/-- The common normal radius of the face series: a quarter of the buffer radius. -/
noncomputable def radius : ℝ := A.bufferRadius a / 4

theorem radius_pos : 0 < A.radius a := by
  have := A.bufferRadius_pos a
  unfold radius
  positivity

/-- The uniform bound of both extensions on the tube. -/
noncomputable def bound : ℝ := (A.exists_bounds a (A.buffer_mem a)).choose

theorem bound_ϕ : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    ‖A.Hϕ (complexify w + z)‖ ≤ A.bound a :=
  (A.exists_bounds a (A.buffer_mem a)).choose_spec.2.1

theorem bound_φ : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    ‖A.Hφ (complexify w + z)‖ ≤ A.bound a :=
  (A.exists_bounds a (A.buffer_mem a)).choose_spec.2.2

theorem radius_lt_half : A.radius a < A.bufferRadius a / 2 := by
  have := A.bufferRadius_pos a
  unfold radius
  linarith

theorem half_lt_buffer : A.bufferRadius a / 2 < A.bufferRadius a := by
  have := A.bufferRadius_pos a
  linarith

/-- E. The uniform series family of an extension over the face `I` at the common radius. -/
noncomputable def uniformSeries (H : (Fin d → ℂ) → ℂ) (hH : DifferentiableOn ℂ H A.Ω)
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
      ‖H (complexify w + z)‖ ≤ A.bound a) (I : NonemptyIdx d) :
    UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) (A.radius a) :=
  analyticUniformSeries (A.radius_pos a) (A.radius_lt_half a) (recentred a H I)
    (continuousOn_recentred a (A.buffer_mem a) I (by linarith [A.bufferRadius_pos a]) hH)
    fun s _ hz => norm_recentred_le a I (by linarith [A.bufferRadius_pos a]) hM s
      (norm_le_of_mem_closedPolydisc (by linarith [A.bufferRadius_pos a]) hz)

/-- F. The evaluation identity for the original real function on the real ball of radius
`A.radius`. -/
theorem evalF_uniformSeries (H : (Fin d → ℂ) → ℂ) (hH : DifferentiableOn ℂ H A.Ω)
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
      ‖H (complexify w + z)‖ ≤ A.bound a) (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    {u : Fin (nI I + 1) → ℝ} (hu : ‖u‖ < A.radius a) :
    evalF ((A.uniformSeries a H hH hM I).f s) u =
      (H (complexify (originalNormalMap I s.1 u))).re := by
  rw [complexify_originalNormalMap]
  change evalF (polyRealCoeff (nI I + 1) (A.bufferRadius a / 2) (recentred a H I s)) u = _
  refine evalF_polyRealCoeff_of_lt (by linarith [A.bufferRadius_pos a]) (A.half_lt_buffer a)
    (differentiableOn_recentred a (A.buffer_mem a) I (A.bufferRadius_pos a) hH s) fun i => ?_
  rw [Complex.norm_real]
  exact (norm_le_pi_norm u i).trans_lt (hu.trans (A.radius_lt_half a))

theorem complexify_originalNormalMap_mem (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    {u : Fin (nI I + 1) → ℝ} (hu : ‖u‖ < A.radius a) :
    complexify (originalNormalMap I s.1 u) ∈ A.Ω := by
  rw [complexify_originalNormalMap]
  refine recentred_mem a (A.buffer_mem a) I s ((norm_complexify_le u).trans ?_)
  have := A.bufferRadius_pos a
  unfold radius at hu
  linarith

/-- ★★ **The original face series of a holomorphic box extension** at the common radius
`A.radius`. -/
noncomputable def faceSeries (I : NonemptyIdx d) : OriginalFaceSeries a ϕ φ I where
  ρ := A.radius a
  hρ := A.radius_pos a
  Fϕ := A.uniformSeries a A.Hϕ A.holϕ (A.bound_ϕ a) I
  Fφ := A.uniformSeries a A.Hφ A.holφ (A.bound_φ a) I
  hϕ_eq := fun s _ hz =>
    (A.eqϕ _ (A.complexify_originalNormalMap_mem a I s hz)).trans
      (A.evalF_uniformSeries a A.Hϕ A.holϕ (A.bound_ϕ a) I s hz).symm
  hφ_eq := fun s _ hz =>
    (A.eqφ _ (A.complexify_originalNormalMap_mem a I s hz)).trans
      (A.evalF_uniformSeries a A.Hφ A.holφ (A.bound_φ a) I s hz).symm

theorem faceSeries_ρ (I : NonemptyIdx d) : (A.faceSeries a I).ρ = A.radius a := rfl

end HolomorphicBoxExtension

/-- ★★ **The bridge**: a holomorphic box extension yields original-variable face series at a
common positive radius for every nonempty coordinate set. -/
theorem exists_originalFaceSeries_of_holomorphicBoxExtension {ϕ φ : (Fin d → ℝ) → ℝ}
    (A : HolomorphicBoxExtension a ϕ φ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I, ∀ I, (O I).ρ = ρ :=
  ⟨A.radius a, A.radius_pos a, A.faceSeries a, fun _ => rfl⟩

end WaterFilling

end Grammar
```

#### Grammar/AnalyticCoordinateBoxExpansion.lean
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.HolomorphicOriginalFaceSeries
import Grammar.CollarDeltaSelection

/-!
# The coordinate-free expansion from holomorphic data near the box (CCCXXXII; phase 3, unit P5)

Consult #98 §7. Composition of the bridge (CCCXXVIII–CCCXXXI) with the compact-box producer
(CCCXXIV–CCCXXVII): for the coordinate monomial phase on `[0,a]^d`, a prior and an observable that
are the real parts of holomorphic functions on a complex neighbourhood of the embedded box
(`HolomorphicBoxExtension`; the wrapper `HolomorphicBoxExtension.ofRealNhd` accepts agreement on a
real neighbourhood of the box instead of the real slice), together with the measurability,
nonnegativity and integrability assumptions of the producer, the original integral
`∫_{[0,a]^d} φ ϕ e^{−nK}` has the coordinate-free expansion for some collar level `δ`, with the
stratum measures and the coefficient field of the certificates constructed from these extensions
(★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension`; box-local nonnegativity:
★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on`, with the certificate of `ϕ⁺`).

Non-claims: the holomorphic extensions are hypotheses (constructing them from real analyticity
is not part of this phase); the observable identity is used on the full open normal balls
(two-sided germs); global measurability of the functions is retained. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} (a : ℝ)

/-- The real parts of the coordinates `ℂ^d → ℝ^d`. -/
def realParts (z : Fin d → ℂ) : Fin d → ℝ := fun j => (z j).re

theorem continuous_realParts : Continuous (realParts (d := d)) :=
  continuous_pi fun j => Complex.continuous_re.comp (continuous_apply j)

theorem realParts_complexify (w : Fin d → ℝ) : realParts (complexify w) = w := by
  funext j
  simp [realParts, complexify]

/-- **Agreement on a real neighbourhood suffices**: holomorphic extensions on an open `Ω ⊇` box
agreeing with `ϕ, φ` on an open real neighbourhood `V ⊇` box give a holomorphic box extension
(on `Ω ∩ {z : Re z ∈ V}`). -/
noncomputable def HolomorphicBoxExtension.ofRealNhd {ϕ φ : (Fin d → ℝ) → ℝ}
    {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) (hWΩ : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω)
    {Hϕ Hφ : (Fin d → ℂ) → ℂ} (hHϕ : DifferentiableOn ℂ Hϕ Ω) (hHφ : DifferentiableOn ℂ Hφ Ω)
    {V : Set (Fin d → ℝ)} (hV : IsOpen V) (hWV : piBox d (Icc 0 a) ⊆ V)
    (heqϕ : ∀ w ∈ V, ϕ w = (Hϕ (complexify w)).re) (heqφ : ∀ w ∈ V, φ w = (Hφ (complexify w)).re) :
    HolomorphicBoxExtension a ϕ φ where
  Ω := Ω ∩ realParts ⁻¹' V
  isOpen_Ω := hΩ.inter (hV.preimage continuous_realParts)
  box_subset := fun w hw => ⟨hWΩ w hw, by
    rw [mem_preimage, realParts_complexify]
    exact hWV hw⟩
  Hϕ := Hϕ
  Hφ := Hφ
  holϕ := hHϕ.mono inter_subset_left
  holφ := hHφ.mono inter_subset_left
  eqϕ := fun w hw => heqϕ w (by
    have := hw.2
    rwa [mem_preimage, realParts_complexify] at this)
  eqφ := fun w hw => heqφ w (by
    have := hw.2
    rwa [mem_preimage, realParts_complexify] at this)

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (ϕ φ : (Fin d → ℝ) → ℝ)
  (A : HolomorphicBoxExtension a ϕ φ) (hd : 0 < d) (ha : 0 < a) (hϕm : Measurable ϕ)
  (hφm : Measurable φ)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))

include hφm in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box** (globally nonnegative
prior): for some collar level `δ`, with the certificates built from the face series of the
extension. -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension (hϕ0 : ∀ w, 0 ≤ ϕ w) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
        (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
        (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=
  hasCoordFreeExpansion_collar_of_face_exists k hk a ϕ φ hd ha hϕm hϕ0 hφm hφint (A.faceSeries a)

include hφm in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box** (prior nonnegative on
the box): for some collar level `δ`, with the certificates of the positive part `ϕ⁺` built from the
face series of the extension. -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on
    (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
          ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).stratumMeasure
        (coeffCertificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
          ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).field
        (spectrumLe (commonQ (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
          (posPart_nonneg ϕ) ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta k hk a hd ha (A.radius_pos a)
  have hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ :=
    fun I i => hsm (σI I i).1
  exact ⟨δ, hδ, hδa, hsmall, hasCoordFreeExpansion_collar_of_nonneg_on k hk a δ hϕm hφm hφint hδ
    hd ha hδa hϕ0W fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)⟩

end WaterFilling

end Grammar
```

### Key upstream statements (CCCXXV interface consumed by phase 3)
```lean
77-/-- Uniform normal-series families for the prior and the observable over the closed face, in the
78-original normal variables, at a radius `ρ`. -/
79:structure OriginalFaceSeries (I : NonemptyIdx d) where
80-  /-- the normal radius -/
81-  ρ : ℝ
82-  hρ : 0 < ρ
83-  Fϕ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
84-  Fφ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
85-  hϕ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
86-    ϕ (originalNormalMap I s.1 z) = evalF (Fϕ.f s) z
87-  hφ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
88-    φ (originalNormalMap I s.1 z) = evalF (Fφ.f s) z
89-
90-/-- A collar base point lies on the closed face. -/
91-theorem mem_faceSet_of_KI (ha : 0 < a) (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
--
224-/-- ★★★ **The compact-box expansion from original-variable face series** (globally nonnegative
225-prior): with radii `ρ_I` and `2 δ^{1/(2k_i d)} < ρ_I`. -/
226:theorem hasCoordFreeExpansion_collar_of_face (hϕ0 : ∀ w, 0 ≤ ϕ w)
227-    (O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I)
228-    (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
229-      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ) :
230-    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
231-      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
232-        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
233-      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
234-        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
235-      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
236-        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
237-      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=
238-  hasCoordFreeExpansion_collar' k hk a δ hδ ϕ φ hϕm hϕ0 hφm hφint hd ha hδa _
--
292-`∫_{[0,a]^d} φ ϕ e^{−nK}` holds with the certificate and coefficient field of the positive part
293-`ϕ⁺`, which agrees with `ϕ` on the box. -/
294:theorem hasCoordFreeExpansion_collar_of_nonneg_on (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
295-    (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I) :
296-    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
297-      (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
298-        ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
299-        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).stratumMeasure
300-      (coeffCertificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
301-        ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
302-        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).field
303-      (spectrumLe (commonQ (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
304-        (posPart_nonneg ϕ) ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa
305-        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).cores.k) (d - 1))
306-      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
```
