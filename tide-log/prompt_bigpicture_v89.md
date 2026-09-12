# Consult #89 — a GLOBAL main theorem over W with strata integrals in the coefficient

You are Astra, advising the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, Mathlib v4.33.1, 590 modules, no sorry/axioms; hironaka pinned as a lake dependency, consumed only through axiom-clean declarations) of the grammar paper (Gerraty–Murfet). After consult #88 the user (Daniel Murfet) asked for a new programme, verbatim:

> "I want to have a version of the main theorem that addresses the actual original integrals over $W$ and makes use of strata integrals in the coefficients, i.e. move past these local coordinate versions."

Design the programme. Be concrete: exact Lean-level statements, the route against Mathlib and the existing library, obstacles, and what is infeasible with the current upstream interface.

## The paper's target (thm:expectation_expansion, leading part)
For `K ≥ 0` analytic (the population KL), a real analytic observable φ and a prior density, with a resolution `π : U → W` whose exceptional divisor has components `E_i` (data `(k_i, h_i)`) and strata `S_I = ⋂_{i∈I} E_i \ ⋃_{j∉I} E_j`:
`𝒵_n[φ] = ∫_W φ e^{−nK} ϕ dw = Σ_I 𝒵_n[φ; I] + O(e^{−nε})`, `𝒵_n[φ; I] ~ Σ_k Σ_j C_{I,k,j}(φ) n^{−λ_{I,k}} (log n)^{j−1}`, `λ_{I,1} = min_{i∈I} (h_i + l_i + 1)/(2k_i)`, and when all `l_i = 0`:
`C_{I,1,m}(φ) = Γ(λ_I)/(m−1)! · a_I · ∫_{S_I} (φ∘π)|_{S_I} c_0 |dv|`, with `c_0(v) = b(v,0) (ϕ∘π)(v,0)` the smooth density factor and `a_I` from the zeta residue (`a_{−m} = ∏_{i∈J} 1/(2k_i) · ∏_{i∈I∖J} b^{h_i+1−2k_iλ}/(h_i+1−2k_iλ)`). The paper's proof: (1) pull back along π, (2) localise to a tubular neighbourhood of E, (3) an adapted smooth partition of unity `{ρ_I}` on the resolved space, fibre-saturated and constant in normal directions (lem:adapted_pou), (4) tubular-neighbourhood fibre integration and the normal moment asymptotics. The mirror already records (Lean paragraph): "the Lean coefficient is the face functional" — in mixed-ratio cases the corner evaluation `∫_{S_I} … c_0` is replaced by the face functional `∫ η(P_J u) ∏_{i∉J} u_i^{h_i − 2k_iλ} du`.

## What the library has (all unconditional unless stated)
* ★★★ `laplace_pair_eq_resolution_pair` / `exponent_of_analytic`: for `K ≥ 0` analytic near a zero `w`, `F > 0` analytic, hironaka's `Q_all` gives a monomial partial resolution `R` of a compact neighbourhood `N ∋ w`, and some compact neighbourhood `Ω ⊆ U` of `w` has `∫_Ω F e^{−NK} = Θ(N^{−λ*} log^{m*−1} N)` with `(λ*, m*)` the extremal pair over divisor-point chart pairs. This is Θ, not `~`, and Ω is a small compact neighbourhood, NOT the user's region `W`. The Θ-route avoided the overlap problem (upper bound by summing charts, lower bound from one chart).
* `IsMonomialChart.local_leading_term` (CCV): on a single monomial chart at a divisor point, `∫_Ω F e^{−NK} ~ c N^{−λ} log^{m−1}`, `c > 0` explicit (chart coordinates).
* Source decompositions (CCLXXIII–CCLXXX): `sourceChartIntegral`, `SourceDecomposition` (Z = Σ_i chart integrals + exponentially small remainder), assembled coefficient `sourceDecompCoeff = Σ_{tied charts} sourceCoeff_i` where `sourceCoeff_i` is a chart-face functional (integral over the dominant face `sourceDominantFace` of amplitude × |Jacobian unit| × tangential monomial weight × prior); `CompactSourceLocalization`: for a continuous nonnegative amplitude of compact support inside the monomial neighbourhood of ONE chart, a plateau partition of unity on the chart domain gives a `SourceLocalization` (finite boxes at divisor points, exponentially small remainder) — this is the analogue of lem:adapted_pou on ONE chart's source.
* `AEDisjointSourceAssembly` (CCLXXVIII): for a `ResolutionCover` whose chart images are pairwise a.e.-disjoint (`AEDisjointImages : ∀ i j, i ≠ j → volume (image i ∩ image j) = 0`), `targetIntegral Rg F K p := ∫_{Rg} F p e^{−NK}` for a target region `Rg` a.e. equal to `⋃ image i` satisfies `targetIntegral ~ aeDisjointCoeff · N^{−λ*} log^{k*}` with `aeDisjointCoeff = Σ_{tied} face functionals` (positive under a dominant-face positivity hypothesis) — `targetIntegral_isEquivalent_of_aeDisjoint`; `targetIntegral_isEquivalent_ofPartialResolution` is the same for hironaka's `PartialResolution` UNDER THE SUPPLIED HYPOTHESIS `hdisj : (ofPartialResolution R).AEDisjointImages` and supplied one-chart product packages `Ps`.
* Derived certificates (CCLXXXI–CCLXXXIV): whole boxes, `BoxFamily` (finitely many divisor-point boxes with a.e.-disjoint images by `IsMonomialChart.volume_image_inter_eq_zero`), and the blow-up cube of the origin in every dimension (`∫_{[−1,1]^d} e^{−N|x|²} ~ π^{d/2} N^{−d/2}`), coefficient locality (regions differing on `{K ≥ κ}` share the leading term), separable-ball regression.
* The mirror's honest non-claim: "certificate production for an arbitrary compact chart domain from a resolution alone (continuous target partitions subordinate to resolution-chart images need not exist, a centred box at a divisor point need not lie in the chart domain, and the exposed resolution interface carries no common resolved space)".

## The upstream interface (hironaka), verbatim
```lean
structure PartialResolution (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (K : Set (Fin n → ℝ)) where
  /-- The set being resolved is compact. -/
  K_compact : IsCompact K
  /-- The chart index. -/
  ι : Type
  /-- The chart family is finite. -/
  [fin : Fintype ι]
  /-- The chart domains ("boxes" in the blow-up instances). -/
  dom : ι → Set (Fin n → ℝ)
  dom_compact : ∀ i, IsCompact (dom i)
  /-- The chart maps. -/
  φ : ι → (Fin n → ℝ) → (Fin n → ℝ)
  /-- Each chart is smooth on an open neighborhood of its domain. -/
  smooth : ∀ i, ∃ U, IsOpen U ∧ dom i ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (φ i) U
  /-- Chart images lie in `K` (Definition 8's "images in a fixed compact
  neighborhood", in box-relative form; composition needs it). -/
  mapsTo : ∀ i, MapsTo (φ i) (dom i) K
  /-- The chart images cover `K` up to a set of measure zero. -/
  cover : volume (K \ ⋃ i, φ i '' dom i) = 0
  /-- The per-chart exceptional sets. -/
  E : ι → Set (Fin n → ℝ)
  /-- Each exceptional set is carried by its chart. -/
  E_subset : ∀ i, E i ⊆ dom i
  E_closed : ∀ i, IsClosed (E i)
  E_null : ∀ i, volume (E i) = 0
  /-- Each chart is injective off its exceptional set. -/
  inj : ∀ i, InjOn (φ i) (dom i \ E i)
  /-- Each chart has nonvanishing Jacobian off its exceptional set. -/
  jac_ne_zero : ∀ i, ∀ x ∈ dom i \ E i, (fderiv ℝ (φ i) x).det ≠ 0
  /-- The multiplicity bound of the family. -/
  mult : ℕ
  /-- The null set off which the multiplicity bound holds. -/
  multN : Set (Fin n → ℝ)
  multN_null : volume multN = 0
  /-- Off the null set, every point of `K` has at most `mult` preimages across
  the whole chart family. -/
  mult_bound : ∀ y ∈ K \ multN,
    {p : ι × (Fin n → ℝ) | p.2 ∈ dom p.1 ∧ φ p.1 p.2 = y}.encard ≤ mult

attribute [instance] PartialResolution.fin

namespace PartialResolution

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}


variable {n : ℕ}

/-- Atom 9.2.4.e: a terminal (monomial) chart for `F`: an open `W ⊇ dom` on which `φ` is analytic,
injective where the Jacobian monomial `y^h` does not vanish, with `F ∘ φ = u · y^e` and
`det Dφ = v · y^h` for continuous nonvanishing `u, v` on `W`. Source: BM88 Def 4.3 p.23 plus the
Jacobian clause of the analytic note Sect. 2.5(d); G5 note Section 5 (the open `W`). -/
structure IsMonomialChart (F : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (dom : Set (Fin n → ℝ)) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen W
  subset : dom ⊆ W
  analyticOnNhd : AnalyticOnNhd ℝ φ W
  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
  exists_unit : ∃ u : (Fin n → ℝ) → ℝ, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧
    ∀ y ∈ W, F (φ y) = u y * monomialEval y e
  exists_jacUnit : ∃ v : (Fin n → ℝ) → ℝ, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
    ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h

/-- A per-chart predicate: a property of the chart map, its domain and its exceptional set. -/
abbrev ChartPred (n : ℕ) : Type :=
  ((Fin n → ℝ) → (Fin n → ℝ)) → Set (Fin n → ℝ) → Set (Fin n → ℝ) → Prop

/-- Atom 9.2.4.e (auxiliary): a chart predicate stable under shrinking the chart domain (with the
exceptional set cut down to the new domain, as `restrict` does). Source: [derived]. -/
def ChartPredStable (P : ChartPred n) : Prop :=
  ∀ (φ : (Fin n → ℝ) → (Fin n → ℝ)) (dom E dom' : Set (Fin n → ℝ)),
    dom' ⊆ dom → P φ dom E → P φ dom' (E ∩ dom')

namespace PartialResolution

variable {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}

/-- Atom 9.2.4.e (auxiliary): every chart of `R` satisfies the chart predicate `P`. Source:
[derived]. -/
def ForallChart (R : PartialResolution n F K) (P : ChartPred n) : Prop :=
  ∀ i, P (R.φ i) (R.dom i) (R.E i)

/-- Atom 9.2.4.e: a monomial resolution — every chart is terminal (for some exponents and some

79:def IsMonomial (R : PartialResolution n F K) : Prop :=
80-  ∀ i, ∃ (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)), IsMonomialChart F (R.φ i) (R.dom i) e h W
81-
82-end PartialResolution

theorem exists_monomialResolution_at (hQ : Q n) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U)
    (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ N : Set (Fin n → ℝ), IsCompact N ∧ N ∈ 𝓝 w ∧
      ∃ R : PartialResolution n K N, R.IsMonomial := by
```

Key facts about this interface: chart images lie in the compact set `K` and cover it up to a null set, but they may OVERLAP (finite multiplicity `mult`, only a bound); each chart is injective with nonvanishing Jacobian off a closed null exceptional set; there is NO common resolved space `U`, NO transition maps between charts, NO global exceptional divisor and NO strata as geometric objects — the divisor is seen only chart-by-chart as the zero set of the monomial `y^e`. hironaka's blow-up constructions do produce a.e.-disjoint wedge images within one blow-up (`blowUpChartBox_cover`), but the exposed `PartialResolution` does not record a.e.-disjointness and its initial covers of a compact set by neighbourhoods overlap. Changing hironaka is possible in principle (same organisation) but is a separate repo and a separate programme; the grammar library consumes only axiom-clean hironaka declarations and must not use hironaka's `E6`.

## Questions
1. **The global statement.** What is the strongest honest theorem of the form "for the ORIGINAL integral `∫_W φ(w) ϕ(w) e^{−nK(w)} dw` over a region `W` (compact, or a compact neighbourhood of the zero set, or all of a bounded open set), `𝒵_n[φ] ~ C n^{−λ} (log n)^{m−1}` with `C` expressed as a sum over strata of integrals over the strata" that can be proved from the current interface? Give the exact statement (hypotheses on `W`, `K`, `φ`, `ϕ`; the region; the sign of φ), and say precisely which part is unconditional.
2. **Overlaps.** The blocking issue is that hironaka's chart images overlap with finite multiplicity, so `∫_W = Σ_i ∫_{chart i}` fails and the a.e.-disjoint assembly does not apply. Options considered: (A) a measurable ownership partition of `W` (`A_i = image_i \ ⋃_{j<i} image_j`), which turns each chart integral into an integral over a measurable region `D_i ⊆ dom_i` of the chart domain — then one needs a leading-term theorem for `∫_{D} G |det| e^{−nK∘φ}` over a measurable (semi-analytic) region `D`, whose coefficient is a face integral weighted by the normal density of `D` at the face (the blow-up wedge computations `π/2` per wedge are instances); (B) multiplicity weights `1/#{i : x ∈ image_i}` (measurable, not continuous — the chart theorems need continuous amplitudes); (C) a continuous partition of unity on `W` subordinate to the interiors of the images (interiors need not cover); (D) request an a.e.-disjoint (`mult = 1`) or transition-map-carrying refinement upstream in hironaka. Which route is right, and what exactly must be proved? If (A): state the region leading-term theorem and the density hypothesis on `D` you would use (Lebesgue density along normal fibres? tangent cones of semi-analytic sets? a "fibre-saturated" ownership partition built in chart coordinates near each face?).
3. **Strata integrals without a resolved space.** How should "∫_{S_I} (φ∘π) c_0 |dv|" be DEFINED in Lean given only charts? Candidates: (i) define the stratum measure on each chart face and prove the face functionals of two charts agree on the overlap of their images of the face via the Jacobian identity (needs transition maps we do not have — but maybe recoverable as `φ_j⁻¹ ∘ φ_i` on the overlap where both are injective?); (ii) define the intrinsic object as the pushforward measure on `W` itself: the coefficient as `∫_W (φ ϕ) dσ_I` for a finite Borel measure `σ_I` on `W` supported on `π(S_I)` (the image of the stratum, a subset of the zero set `W_0`), built as the sum over charts of the pushforwards of the face densities under `φ_i`, with an ownership partition making it well defined — this expresses the coefficient as an integral over `W` against a canonical "stratum measure" and is chart-independent by construction if the ownership partition is; (iii) something else. Which definition is (a) honest to the paper, (b) provable, (c) chart-independent in a provable sense? Note `π(S_I) ⊆ W_0` may be lower-dimensional or a point; the measure `σ_I` on `W` is the honest global object.
4. **Unit plan.** Give an ordered plan (≤ 8 units, each ≤ ~400 lines) with exact statements, Mathlib/library tools, sizes, and the gate for each; name the first unit precisely. Say what remains a hypothesis at the end (e.g. a.e.-disjointness, the face density of the ownership regions, analyticity of φ) and whether the plan needs an upstream hironaka change. If the honest answer is that the strata-integral coefficient cannot be made chart-independent from this interface, say so and give the best global theorem that CAN be proved (e.g. `∫_W … ~ C n^{−λ} log^{m−1}` with `C = ∫_W (φ ϕ) dσ` for a canonical finite measure `σ` on `W_0` constructed from the resolution, plus the Θ-theorem for an arbitrary region).
