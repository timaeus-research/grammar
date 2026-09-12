# Consult #92 — a coordinate-free FINAL statement: conormal derivatives, strata, no charts

You are Astra, advising the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, Mathlib v4.33.1, 597 modules, no sorry/axioms) of the grammar paper (Gerraty–Murfet). Consult #91 designed a chart-face programme for the full expansion (finite-part functionals on chart faces, pushed to `W`). The user (Daniel Murfet) has now stated the requirement precisely:

> "I just want the ultimate final formula to not have coordinates involved in it at all, just conormal derivatives and other quantities that make reference to the stratification of the exceptional divisor but which are not otherwise involving local coordinate charts."

So the TARGET is the paper's coordinate-free statement `thm:expectation_expansion` / `eq:thm_coordfree`:
`𝒵_n[φ; I] ~ Σ_{r≥0} (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩ τ_*|μ_I|`, with `D^r_⊥(φ∘π) ∈ Γ(S_I, Sym^r N^*S_I)` the normal `r`-th differential w.r.t. a tubular neighbourhood `Φ_I : NS_I → U` (`defn:normal_diff`), `M_{I,r}(n) ∈ Γ(S_I, Sym^r NS_I)` the moment tensor (the `n`-dependence of the normal fibre moments, a finite power–log sum in `n` — `eq:moment_tensor_defn`), `τ_*|μ_I|` the pushed-forward density on the stratum, and the per-stratum decomposition via the adapted partition of unity `{ρ_I}` (`lem:adapted_pou`: `ρ_I` constant in normal directions, `V_I ∩ E_j = ∅` for `j ∉ I` — which is exactly what makes each per-stratum integral converge where a stratum closes onto a tied deeper stratum; the split is `ρ`-dependent, the total canonical). Charts may appear in HYPOTHESES (as the certificate that the geometry is resolved) and in PROOFS, but not in the statement of the final formula.

## The interface problem
hironaka exposes `PartialResolution` (finitely many compact chart domains `dom_i ⊆ ℝ^d`, maps `φ_i : ℝ^d → ℝ^d` analytic near `dom_i`, images covering a compact `N ⊆ W` a.e. with finite multiplicity, injective off a null exceptional set, `IsMonomialChart`: `K∘φ_i = u y^e`, `det Dφ_i = v y^h`). There is NO common resolved space `U`, NO map `π : U → W`, NO transition maps, NO divisor components `E_i ⊆ U`, NO strata. The library's "coordinate-free" normal machinery is formalised relative to a chosen NORMAL FAMILY (normal spaces `N_s ⊆ E` and fibre maps `Φ_s`, germ at 0; `NormalTaylorForm`, `IsGlobalNormalSection`, `conormalSplitting`, `LabelledNormalBundle` giving a `C^∞` bundle with diagonal transitions from labelled defining equations on an open cover), and the resolved-space expansion `coverIntegral_eq_sum_pieceContraction` is still a sum over chart–stratum pieces. The leading measure (CCXC–CCXCVI) lives on `W` and is canonical but chart-defined.

## Questions
1. **What is the right abstract geometric structure to state the theorem on**, given that it cannot be produced from hironaka now? Propose a Lean structure `ResolvedSpace` (or a chain of structures) carrying exactly the data the coordinate-free formula refers to: a space `U` (what regularity/typeclass: a `C^∞`/analytic manifold via Mathlib's `Manifold` API on `EuclideanSpace`/a model space? or just a measurable space with a measure `|μ_U|` and a proper measurable `π : U → W`?), the exceptional divisor components `E_i ⊆ U` (closed), strata `S_I`, normal bundle data along each `S_I` — the conormal splitting `N^*S_I ≅ ⊕ L_i` — a tubular neighbourhood `Φ_I`, the pushed-forward densities `τ_*|μ_I|`, and the numerical data `(k_i, h_i)`. Which of these can reuse the library's existing objects (`NormalTaylorForm` relative to a normal family; `LabelledNormalBundle`; `TubularFibreIntegration`; `condContractionSeries`), and which must be new? What is the minimal set of axioms on this structure that make the expansion theorem PROVABLE from the chart-level results (i.e. the structure must also carry, as a certificate, an atlas of monomial charts compatible with the strata, normal bundles and densities — how should compatibility be phrased so that it is checkable in the examples we have: blow-up of the origin in `ℝ^d`, the cube, the normal-crossing model)?
2. **The coordinate-free objects.** Give precise Lean-level definitions of: (a) `D^r_⊥(φ∘π)` as a section over `S_I` of symmetric `r`-forms on the normal spaces, from the tubular neighbourhood — can it be defined as `fun s => normalTaylorForm r (φ∘π∘Φ_I) s` using the existing normal-family machinery, with the "global section" property `IsGlobalNormalSection`? (b) the moment tensor `M_{I,r}(n)` — its definition as the `n`-dependent fibre moment of the normal coordinates against `e^{−nK}` (a section of `Sym^r NS_I`); the paper says it is a finite power–log sum in `n` — is that exact or asymptotic, and how should Lean state it (exact fibre moments are NOT finite power–log sums in general; the paper's `M_{I,r}(n)` presumably means the asymptotic truncation)? (c) the density `τ_*|μ_I|` on `S_I` — as a measure on `S_I` (pushforward of the fibre-integrated Lebesgue density with the Jacobian), and its relation to the leading measure of CCXC; (d) the pairing `⟨D^r_⊥, M_{I,r}⟩` and the stratum integral, including the regularisation where `S_I` closes onto a tied deeper stratum (via `ρ_I`, or as a finite part — which is more honest for the STATEMENT?).
3. **The theorem.** State the final coordinate-free theorem as you would want it to read in Lean (statement only): hypotheses = the resolved-space structure with its compatibility certificate, `φ` analytic (or `C^∞`? the paper says analytic) on `W`, prior `ϕ`; conclusion = the full cutoff expansion of `∫_W φ ϕ e^{−nK}` with coefficients written as strata integrals of pairings of conormal derivatives with moment-tensor coefficients against `τ_*|μ_I|`, plus the leading-term corollary (which should recover the leading measure of CCXC as `Σ_{tied I} Γ(λ)/(m−1)! a_I (τ_*|μ_I|)|_{c₀}` pushed to `W`). Be explicit about what is canonical and what depends on `Φ_I`, `ρ_I`.
4. **Route.** How much of the chart-face programme of #91 (finite parts, Laurent algebra) is still needed as the PROOF engine under this coordinate-free statement, and what is the shortest path from the existing chart-level theorems to the coordinate-free theorem? Give an ordered unit plan (≤ 12 units, ≤ ~400 lines each) with exact statements, the first unit named precisely, and the sizes/gates; say which examples should instantiate the structure (blow-up of the origin as the first instance: `U` = the blow-up realised how? as a submanifold of `ℝ^d × P^{d−1}`, or as the disjoint union of the `d` blow-up charts glued? — Mathlib has no blow-ups; what is the cheapest honest model of `U` that still has strata and a global `π`?).
5. **Upstream.** State precisely what hironaka would have to expose (a common resolved space with a proper analytic `π`, charts as an atlas of `U`, divisor components as closed analytic hypersurfaces meeting normally) for the structure in (1) to be produced automatically from `K`, and whether that is realistic given hironaka's construction (iterated blow-ups with box charts, BM89 readout); if the conditional theorem on the abstract structure is the honest endpoint for now, say so.

## Existing coordinate-free machinery (verbatim headers)
```lean
Grammar/ConormalSplitting.lean:107:noncomputable def conormalSplitting [Finite ι] (h : LinearIndependent ℝ ℓ) :
Grammar/ConormalSplitting.lean-108-    (⨁ i, conormalLine ℓ i) ≃ₗ[ℝ] conormalOf ℓ :=
Grammar/ConormalSplitting.lean-109-  (LinearEquiv.ofInjective _ (coeLinearMap_conormalLine_injective ℓ h)).trans
Grammar/ConormalSplitting.lean-110-    (LinearEquiv.ofEq _ _ (by rw [DirectSum.range_coeLinearMap, conormalOf_eq_iSup_conormalLine]))
Grammar/ConormalSplitting.lean-111-
Grammar/ConormalSplitting.lean-112-theorem conormalSplitting_apply [Finite ι] (h : LinearIndependent ℝ ℓ)
Grammar/ConormalSplitting.lean-113-    (x : ⨁ i, conormalLine ℓ i) :
Grammar/NormalTaylorForm.lean:45:noncomputable def rawNormalJet (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
Grammar/NormalTaylorForm.lean-46-    (r : ℕ) : JetForm (N s) r :=
Grammar/NormalTaylorForm.lean-47-  iteratedFDeriv ℝ r (fun n : N s => F (Φ s n)) 0
Grammar/NormalTaylorForm.lean-48-
Grammar/NormalTaylorForm.lean-49-/-- **The normal Taylor form** `T_r(F)(s) = J_r(F)(s) / r!` (the paper's `D^r_⊥ F`). -/
Grammar/NormalTaylorForm.lean:50:noncomputable def normalTaylorForm (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ)
Grammar/NormalTaylorForm.lean-51-    (s : S) (r : ℕ) : JetForm (N s) r :=
Grammar/NormalTaylorForm.lean-52-  (r.factorial : ℝ)⁻¹ • rawNormalJet N Φ F s r
Grammar/NormalTaylorForm.lean-53-
Grammar/NormalTaylorForm.lean-54-variable (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
Grammar/NormalTaylorForm.lean-55-
Grammar/NormalTaylorForm.lean-56-theorem rawNormalJet_eq_normalJet (r : ℕ) :
Grammar/LabelledNormalBundle.lean:79:structure LabelledDefiningEquations (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
Grammar/LabelledNormalBundle.lean-80-    [ChartedSpace HB B] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)
Grammar/LabelledNormalBundle.lean-81-    (ι : Type*) where
Grammar/LabelledNormalBundle.lean-82-  emb : B → E
Grammar/LabelledNormalBundle.lean-83-  contMDiff_emb : ContMDiff IB 𝓘(ℝ, E) ∞ emb
Grammar/LabelledNormalBundle.lean-84-  baseSet : ι → Set B
Grammar/LabelledNormalBundle.lean-85-  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
Grammar/ConormalSplitting.lean:107:noncomputable def conormalSplitting [Finite ι] (h : LinearIndependent ℝ ℓ) :
Grammar/ConormalSplitting.lean-108-    (⨁ i, conormalLine ℓ i) ≃ₗ[ℝ] conormalOf ℓ :=
Grammar/ConormalSplitting.lean-109-  (LinearEquiv.ofInjective _ (coeLinearMap_conormalLine_injective ℓ h)).trans
Grammar/ConormalSplitting.lean-110-    (LinearEquiv.ofEq _ _ (by rw [DirectSum.range_coeLinearMap, conormalOf_eq_iSup_conormalLine]))
Grammar/ConormalSplitting.lean-111-
Grammar/ConormalSplitting.lean-112-theorem conormalSplitting_apply [Finite ι] (h : LinearIndependent ℝ ℓ)
Grammar/ConormalSplitting.lean-113-    (x : ⨁ i, conormalLine ℓ i) :
Grammar/ChartNormalFamily.lean:211:noncomputable def fibreMeasures (I : Fin M) (N : ℝ) : K I → Measure (Fin (n I + 1) → ℝ) :=
Grammar/ChartNormalFamily.lean-212-  fun v => (A.chart I).fibreMeasure v N
Grammar/ChartNormalFamily.lean-213-
Grammar/ChartNormalFamily.lean-214-/-- **The resolved population integral as the finite sum over the trivialised cover of base
Grammar/ChartNormalFamily.lean-215-integrals of the coordinate-free contraction series**, `Z(N) = ∑_I ∫_{K_I} ∑_r ⟨D^r_⊥F, 𝖬_{I,r}(N)⟩
Grammar/ChartNormalFamily.lean-216-dν_I + tail(N)`, for the chart normal families of the certified presentation. -/
Grammar/ChartNormalFamily.lean-217-theorem Z_eq_tsum_normalContraction (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β)
Grammar/GeometricMainTheorem.lean:117:noncomputable def fibreMeasure (v : K) (N : ℝ) : Measure (Fin (n + 1) → ℝ) :=
Grammar/GeometricMainTheorem.lean-118-  (dressedMeasure n C.h C.k β N C.b).withDensity fun u => ENNReal.ofReal (C.c (v, u))
Grammar/GeometricMainTheorem.lean-119-
Grammar/GeometricMainTheorem.lean-120-theorem fibreMeasure_ac (v : K) (N : ℝ) :
Grammar/GeometricMainTheorem.lean-121-    C.fibreMeasure v N ≪ dressedMeasure n C.h C.k β N C.b :=
Grammar/GeometricMainTheorem.lean-122-  withDensity_absolutelyContinuous _ _
Grammar/GeometricMainTheorem.lean-123-
Grammar/LabelledNormalBundle.lean:79:structure LabelledDefiningEquations (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
Grammar/LabelledNormalBundle.lean-80-    [ChartedSpace HB B] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)
Grammar/LabelledNormalBundle.lean-81-    (ι : Type*) where
Grammar/LabelledNormalBundle.lean-82-  emb : B → E
Grammar/LabelledNormalBundle.lean-83-  contMDiff_emb : ContMDiff IB 𝓘(ℝ, E) ∞ emb
Grammar/LabelledNormalBundle.lean-84-  baseSet : ι → Set B
Grammar/LabelledNormalBundle.lean-85-  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
Grammar/NormalTaylorForm.lean:45:noncomputable def rawNormalJet (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
Grammar/NormalTaylorForm.lean-46-    (r : ℕ) : JetForm (N s) r :=
Grammar/NormalTaylorForm.lean-47-  iteratedFDeriv ℝ r (fun n : N s => F (Φ s n)) 0
Grammar/NormalTaylorForm.lean-48-
Grammar/NormalTaylorForm.lean-49-/-- **The normal Taylor form** `T_r(F)(s) = J_r(F)(s) / r!` (the paper's `D^r_⊥ F`). -/
Grammar/NormalTaylorForm.lean:50:noncomputable def normalTaylorForm (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ)
Grammar/NormalTaylorForm.lean-51-    (s : S) (r : ℕ) : JetForm (N s) r :=
Grammar/NormalTaylorForm.lean-52-  (r.factorial : ℝ)⁻¹ • rawNormalJet N Φ F s r
Grammar/NormalTaylorForm.lean-53-
Grammar/NormalTaylorForm.lean-54-variable (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
Grammar/NormalTaylorForm.lean-55-
Grammar/NormalTaylorForm.lean-56-theorem rawNormalJet_eq_normalJet (r : ℕ) :
Grammar/TubularFibreIntegration.lean:112:noncomputable def tubeDensity (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
Grammar/TubularFibreIntegration.lean-113-    (wt : TubeWeight d) : (Fin (d - r) → ℝ) × (Fin r → ℝ) → ℝ :=
Grammar/TubularFibreIntegration.lean-114-  (tubeChartDom T C).indicator fun p => tubeJac C p * wt.w (tubeChartM T C p)
Grammar/TubularFibreIntegration.lean-115-
Grammar/TubularFibreIntegration.lean-116-variable (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) (wt : TubeWeight d)
Grammar/TubularFibreIntegration.lean-117-
Grammar/TubularFibreIntegration.lean-118-theorem tubeDensity_of_mem {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T C) :
Grammar/TubularPushforward.lean:139:noncomputable def condContractionSeries (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
Grammar/TubularPushforward.lean-140-  ∑' k, normalContraction A.normal (condTubeNormalMeasure T C wt)
Grammar/TubularPushforward.lean-141-    (integrable_norm_pow_condTubeNormalMeasure T C wt k) (additiveFamily A.normal) F x
Grammar/TubularPushforward.lean-142-
Grammar/TubularPushforward.lean-143-end Cond
Grammar/TubularPushforward.lean-144-
Grammar/TubularPushforward.lean-145-section Pushforward
Grammar/WeightedFibreIntegration.lean:82:noncomputable def fibreMeasure (c : V × E → ℝ) (v : V) : Measure E :=
Grammar/WeightedFibreIntegration.lean-83-  vol.withDensity fun u => ENNReal.ofReal (c (v, u))
Grammar/WeightedFibreIntegration.lean-84-
Grammar/WeightedFibreIntegration.lean-85-variable {c : V × E → ℝ}
Grammar/WeightedFibreIntegration.lean-86-
Grammar/WeightedFibreIntegration.lean-87-theorem integral_fibreMeasure [MeasurableSpace V] (hc : Measurable c) (hc0 : ∀ p, 0 ≤ c p) (v : V)
Grammar/WeightedFibreIntegration.lean-88-    (H : E → ℝ) :
```
