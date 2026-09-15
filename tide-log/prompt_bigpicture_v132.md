# Consult #132 — DESIGN of the residue programme, items 2–3: the stratum measure as an object, and the Poincaré residue as an object

User direction (2026-09-15, verbatim): "I think the phrasing in terms of Poincaré residues is beautiful and should be centered going forward." After I explained what is implicit vs. absent, the user said "Proceed with 1-3" for: (1) [LANDED, CDLIII] pole orders + `d log`-normalised residue weight + `coeff_eq_residueSum`; (2) the stratum measure `ν^μ_c` as an intrinsic object with `𝒯^U_{μ,c−1}[F] = ∫ F dν` for `F ∈ 𝓘_{c+1}`, made a genuine Radon measure on `U ∖ D_{c+1}` via Riesz; (3) an intrinsic Poincaré residue for densities with simple poles along a normal-crossings divisor on the analytic manifold `U`, with the theorem that the chart weight is its coordinate expression. Please fix the design, hypotheses and unit list with S/M/L costs, and tell us plainly if (3) in the log-form sense is the wrong target.

## 1. State (grammar main `754691d`, 767 modules)
```
-- CDLIII SmoothResolvedResidue (namespace Grammar.SmoothEngine[.ResolvedData])
noncomputable def poleOrder (k h : ℕ) (μ : ℝ) : ℝ := 2 * k * μ - h        -- (K∘π)^{−μ}μ_U ~ u^{−poleOrder} along a wall
theorem resonates_iff_poleOrder : Resonates μ p ↔ ∃ n : ℕ, poleOrder p.1 p.2 μ = n + 1
theorem exactCount_eq_card_simplePole : exactCount k e μ = #{i | poleOrder (k i) (e i) μ = 1}
noncomputable def residueWeight (h k : ι → ℕ) (μ) (w) : ℝ := mono h w * mono (2k) w ^ (−μ)      -- ∏ w_i^{h_i} (∏ w_i^{2k_i})^{−μ}
noncomputable def dlogResidueInt (k h) (μ b) (J) (A) : ℝ := (∏_{j∈J} (2k_j)⁻¹) * ∫_{(0,b]^{Jᶜ}} A (glue J 0 w) * residueWeight (h|Jᶜ) (k|Jᶜ) μ w
noncomputable def residueConst (μ) (c) : ℝ := Γ(μ) / (c−1)!
theorem faceTerm_eq_residue_of_simple (hsimple : ∀ j ∈ J, 2 k_j μ = h_j + 1) : faceW·faceCoef·faceCoeffInt = residueConst μ c * β^{−μ} * dlogResidueInt k h μ b J A
noncomputable def residueSum (μ c) : ℝ := residueConst μ c * ∑_I ∫_s ∑_{J ∈ simpleFaces} dlogResidueInt … ((Ξ.amp Y (en I)).amp s) ∂ν_I
theorem coeff_eq_residueSum (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) : Ξ.coeff Y μ (c−1) = Ξ.residueSum Y μ c
-- from Theorems D/E: coeff_nonneg_of_deep (F ≥ 0 ⇒ 0 ≤ 𝒯), coeff_eq_of_eqOn_exactStratum (values on S^μ_c only), coeff_eq_of_transports, coeff_add/coeff_smul (linearity in F), tendsto_normalised_Z_of_extremalData (𝒯 as a Laplace limit at λ*), integrableOn_pieceStratum_integrand
```
## 2. Infrastructure available
- `R.U : AnalyticManifold ℝ (Fin d → ℝ)`: `T2Space`, `SecondCountableTopology`, `IsManifold 𝓘(ℝ, Fin d → ℝ) ω`, Borel `MeasurableSpace`; hironaka proves `LocallyCompactSpace`/`SigmaCompactSpace` from the charted structure. `U ∖ D_{c+1}` is an open subset (D_{c+1} compact).
- Mathlib: Riesz–Markov–Kakutani for `Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ` on locally compact T2 `X`: `RealRMK.rieszMeasure Λ`, `integral_rieszMeasure`, regularity, uniqueness `Measure.ext_of_integral_eq_on_compactlySupported` (regular measures agreeing on `C_c(X, ℝ)` are equal). Smooth partitions of unity on σ-compact T2 manifolds: `SmoothPartitionOfUnity.exists_isSubordinate`, `exists_contMDiffMap_zero_one_of_isClosed`, `exists_contMDiffMap_one_nhds_of_subset_interior`, and the local-to-global gluing `exists_contMDiffMap_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x)) (Hloc : ∀ x, ∃ c, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g smooth, ∀ x, g x ∈ t x` — which gives uniform approximation of a continuous function by a smooth one (t x := (g x − ε, g x + ε)). NO Poincaré residue, NO log forms, NO densities-with-poles on manifolds in Mathlib; no meromorphic continuation of ζ_F(s) = ∫ F (K∘π)^s μ_U in the library.

## 3. Proposal for item 2 (the stratum measure)
Fix `μ, c` with `ZeroOrder μ c` (or `μ = λ*`). Let `X := U ∖ D_{c+1}` (open, locally compact T2). 
(2a) Extension (M): every smooth `F` with compact support in `X` lies in `𝓘_{c+1}`; the functional `T F := 𝒯^U_{μ,c−1}[F]` is linear and positive there, hence monotone; for compact `K ⊆ X` pick a smooth `χ_K ≥ 1_K` with compact support in `X` (bump), so `|T F| ≤ T χ_K · sup|F|` for `F` supported in `K`; extend `T` to `C_c(X, ℝ)` by uniform approximation with smooth compactly supported functions (via the convex-gluing theorem plus a cutoff), well-defined by the bound, linear and positive.
(2b) Riesz (S): `ν^μ_c := RealRMK.rieszMeasure (extension)`, a regular measure on `X` with `∫ f dν = T f` for `f ∈ C_c(X)`, in particular `𝒯^U_{μ,c−1}[F] = ∫ F dν` for smooth compactly supported `F` in `X`; unique among regular measures with this property.
(2c) Chart formula (S): on such `F`, `∫ F dν = residueSum` (CDLIII), i.e. `ν` is represented in every chart by `residueConst · dlogResidueInt`: "the stratum measure is the Poincaré residue in coordinates".
(2d) Support/locality (S): `ν` is supported on `S^μ_c ∩ X`... (from values-only dependence: `∫ F dν = 0` when `F = 0` on `S^μ_c`).
Questions: is `X = U ∖ D_{c+1}` the right space, or should the measure live on the exact stratum `S^μ_c` (a locally closed submanifold, itself a locally compact T2 space) — i.e. take `X := S^μ_c` with the functional `F|_S ↦ 𝒯[F]` (values-only makes this well defined; needs every `C_c(S)` function to extend to a smooth `F` on `U` compactly supported in `U ∖ D_{c+1}`: extension of smooth functions from a closed submanifold of `X` — do we have that? `S^μ_c` is closed in `X`). Which is cheaper and which is the right object for the paper? Is (2a) the standard route or is there a shortcut (e.g. define `ν` directly as the chart pushforward measure `∑_I ∫_s (divPt)_*(residue weight measure)` via `Measure.bind`/`Measure.map`, prove `∫ F dν = residueSum` for smooth `F`, then chart-independence by uniqueness on `C_c` after smooth approximation)?

## 4. Proposal for item 3 (the Poincaré residue as an object)
We see three options.
(3A) Log-form calculus on `U`: define densities with poles along a normal-crossings divisor, define the iterated residue along an intersection of components, prove chart independence (Poincaré residue of a log form is intrinsic), and prove `Res_S[(K∘π)^{−μ}μ_U] = residueWeight` in charts. Genuinely new infrastructure (L, maybe XL); Mathlib has none of it.
(3B) Define the residue MEASURE intrinsically as the Laplace-asymptotic object: `Res^μ_c := ν^μ_c` from item 2 (the Riesz measure of `F ↦ 𝒯^U_{μ,c−1}[F]`, equivalently of `F ↦ lim N^μ (log N)^{−(c−1)} ∫ F e^{−NK∘π} μ_U` at the leading index) — this is coordinate-free by construction and CDLIII is then the theorem "in every normal-crossings chart the residue measure is `Γ(μ)/(c−1)! · (∏ (2k_j)^{−1}) · residueWeight · dw` on the face", which is the classical Poincaré-residue formula. The name "Poincaré residue" is then a theorem about `ν`, not a separate definition.
(3C) Define the residue via the zeta function `ζ_F(s) = ∫ F (K∘π)^s μ_U` (leading Laurent coefficient at `s = −μ`): intrinsic, classical, but needs meromorphic continuation (M–L) that the library lacks.
Our inclination: (3B) as the definition, with (3A) recorded as the non-formalised identification unless you think the log-form residue should exist independently of the expansion. Please rule.

## 5. Questions
(A) Is the paper-facing statement "`ν^μ_c` is a positive Radon measure on `U ∖ D_{c+1}` supported on `S^μ_c`, with `𝒯^U_{μ,c−1}[F] = ∫ F dν^μ_c` for `F ∈ 𝓘_{c+1}` compactly supported away from `D_{c+1}`, given in normal-crossings coordinates by `Γ(μ)/(c−1)! ∏_{j∈J}(2k_j)^{−1} ∏_{i∉J} w_i^{h_i}(∏ w_i^{2k_i})^{−μ} dw`, i.e. `Γ(μ)/(c−1)! · Res_{S^μ_c}[(K∘π)^{−μ}μ_U]` with residues against `d log(u_j^{2k_j})`" correct as stated, and does it need `F` compactly supported in `X` (vs. merely vanishing near `D_{c+1}`; `F ∈ 𝓘_{c+1}` need not have compact support in `X`, e.g. `F = 1` when `D_{c+1} = ∅` — but `Z₀` is compact, does that save it)?
(B) Route for (2a): approximation via `exists_contMDiffMap_forall_mem_convex_of_local_const` + cutoff, or another?
(C) Rule on (3A)/(3B)/(3C). If (3B): exact statements to prove, and the wording for the paper ("the stratum measure is the Poincaré residue of the twisted prior density" vs. "is given by the residue formula in coordinates").
(D) Unit list with costs and order; any hidden difficulty (e.g. `X` not compact, `ν` locally finite but infinite total mass near `D_{c+1}`; the Riesz measure is on `X`, not on `U`; measurability of `S^μ_c`).
