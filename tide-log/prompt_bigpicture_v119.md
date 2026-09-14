# Consult #119 — NEW PROJECT: a smooth weighted normalised atlas from resolution data (design)

You are advising a Lean 4 (Mathlib) formalisation of the grammar paper (Gerraty–Murfet). Your audit #118 closed the smooth-amplitude route as a CONDITIONAL theorem: `SmoothSheetInputs.hasSmoothCoordFreeExpansion` gives the coordinate-free power–log expansion of `∫_W prior·obs·e^{−NK}` from a smooth weighted domain atlas. You recommended a separately named next project: "constructing a smooth weighted normalised atlas from resolution data", starting with the resolution-space → weighted-transport bridge. The user has approved that project. This consult asks you to DESIGN it, given exactly what the resolution library (`hironaka`, fork branch `sector-atlas`) exports today. Everything quoted below is verbatim Lean, axiom-clean unless marked.

## 1. What hironaka exports (verbatim)

### 1.1 Watanabe's modification (exact chart form; `Monomialize/Transport/AnalyticResolutionExports.lean`)
```
structure WatanabeModificationOn (f : (Fin d → ℝ) → ℝ) (W : Opens (Fin d → ℝ)) where
  U : AnalyticManifold.{0} ℝ (Fin d → ℝ)                    -- the resolved analytic manifold (hironaka's own structure, not Mathlib's IsManifold)
  g : AnalyticMap U ((AnalyticManifold.model ℝ (Fin d → ℝ)).restrict W)
  proper : IsProperMap g                                     -- proper INTO W
  surjective : Function.Surjective g
  isoOff : AnalyticMap.IsAnalyticIsoOver g {x | f (inclusion W x) ≠ 0}   -- IsLocalDiffeomorphOn ω on g⁻¹U ∧ BijOn g (g⁻¹ U) U
  chartAt : ∀ P : U, f (inclusion W (g P)) = 0 → WatanabeChartAt f g P

def WatanabeChartAt f g P : Prop :=
  ∃ (φ : OpenPartialHomeomorph U (Fin d → ℝ)) (k h : Fin d → ℕ) (S : ℝ) (b : (Fin d → ℝ) → ℝ),
    φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω U ∧ P ∈ φ.source ∧ φ P = 0 ∧ (S = 1 ∨ S = -1) ∧
    AnalyticOnNhd ℝ b φ.target ∧ (∀ u ∈ φ.target, b u ≠ 0) ∧
    (∀ u ∈ φ.target, f (watanabeRep g φ u) = S * ∏ i, u i ^ k i) ∧
    ∀ u ∈ φ.target, (fderiv ℝ (watanabeRep g φ) u).det = b u * ∏ i, u i ^ h i
-- watanabeRep g φ := fun u => inclusion W (g (φ.symm u)) : (Fin d → ℝ) → (Fin d → ℝ)   (the chart map into ℝ^d)
-- WatanabeEvenChartAt: same with S = 1 and exponents 2 * k i; theorem WatanabeChartAt.even_of_nonneg (hf0 : ∀ x ∈ W, 0 ≤ f x)
theorem exists_watanabeModificationOn (hU₀ : IsOpen U₀) (hf : AnalyticOnNhd ℝ f U₀) (h0 : f 0 = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, f x = 0) (W : Opens _) (hW : IsConnected (W : Set _)) (h0W : 0 ∈ W) (hWU : ↑W ⊆ U₀) :
    Nonempty (WatanabeModificationOn f W)
```
NOTE: the phase unit is the CONSTANT `S` (`= 1` for `f ≥ 0`), valid on the WHOLE `φ.target`; the Jacobian unit `b` is analytic and nonvanishing (not necessarily positive) on the whole `φ.target`. So the paper's unit normalisation is already performed inside hironaka: `hu_tan` is free. There is NO measure-theoretic statement about `g` itself in hironaka (no `∫_W f = ∫_U f∘g |det Dg|`); a descent `logResolutionData_of_watanabe` exists but exposes only two-sided monomial bounds and an existential null set — not the exact units.

### 1.2 The finite chart interface with exact weighted transport (`Monomialize/VolumeScaling`, `Monomialize/Transport`)
```
structure PartialResolution (n : ℕ) (F : (Fin n → ℝ) → ℝ) (K : Set (Fin n → ℝ)) where
  K_compact : IsCompact K ; ι : Type ; [fin : Fintype ι]
  dom : ι → Set (Fin n → ℝ) ; dom_compact : ∀ i, IsCompact (dom i)
  φ : ι → (Fin n → ℝ) → (Fin n → ℝ)
  smooth : ∀ i, ∃ U, IsOpen U ∧ dom i ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (φ i) U
  mapsTo : ∀ i, MapsTo (φ i) (dom i) K
  cover : volume (K \ ⋃ i, φ i '' dom i) = 0
  E : ι → Set (Fin n → ℝ) ; E_subset : ∀ i, E i ⊆ dom i ; E_closed : ∀ i, IsClosed (E i) ; E_null : ∀ i, volume (E i) = 0
  inj : ∀ i, InjOn (φ i) (dom i \ E i)
  jac_ne_zero : ∀ i, ∀ x ∈ dom i \ E i, (fderiv ℝ (φ i) x).det ≠ 0
  mult : ℕ ; multN : Set (Fin n → ℝ) ; multN_null : volume multN = 0
  mult_bound : ∀ y ∈ K \ multN, {p : ι × (Fin n → ℝ) | p.2 ∈ dom p.1 ∧ φ p.1 p.2 = y}.encard ≤ mult

def HasWeightedTransport (R : PartialResolution n F K) (ω : R.ι → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ g : (Fin n → ℝ) → ℝ≥0∞, Measurable g →
    ∫⁻ y in K, g y = ∑ i, ∫⁻ x in R.dom i, g (R.φ i x) * R.jacDensity i x * ENNReal.ofReal (ω i x)

theorem hasWeightedTransport_of_partition (R : PartialResolution n F K) (χ : R.ι → (Fin n → ℝ) → ℝ)
    (hχm : ∀ i, Measurable (χ i)) (hχ0 : ∀ i y, 0 ≤ χ i y)
    (hsum : ∀ᵐ y ∂(volume.restrict K), ∑ i, (R.φ i '' R.dom i).indicator (χ i) y = 1) :
    R.HasWeightedTransport fun i x => χ i (R.φ i x)                 -- χ lives on the TARGET; the weights are its pull-backs

structure ProductChartAtlas n F Ω extends PartialResolution n F Ω where
  lo hi : ι → Fin n → ℝ ; lo_lt_hi ; dom_eq : ∀ i, dom i = Set.univ.pi fun j => Icc (lo i j) (hi i j)
  V : ι → Set _ ; V_open ; dom_subset_V ; φ_analytic : ∀ i, AnalyticOnNhd ℝ (φ i) (V i)
  k : ι → Fin n → ℕ ; phaseUnit : ι → (Fin n → ℝ) → ℝ ; phaseUnit_analytic ; phaseUnit_pos : ∀ i, ∀ y ∈ V i, 0 < phaseUnit i y
  phase_eq : ∀ i, ∀ y ∈ V i, F (φ i y) = phaseUnit i y * ∏ j, y j ^ (2 * k i j)
  h : ι → Fin n → ℕ ; jacUnit ; jacUnit_analytic ; jacUnit_ne_zero : ∀ i, ∀ y ∈ V i, jacUnit i y ≠ 0
  jac_eq : ∀ i, ∀ y ∈ V i, (fderiv ℝ (φ i) y).det = jacUnit i y * ∏ j, y j ^ h i j
structure WeightedSectorAtlas n F Ω extends ProductChartAtlas n F Ω where
  ω : ι → (Fin n → ℝ) → ℝ ; ω_measurable ; ω_nonneg ; ω_le_one ; transport : toPartialResolution.HasWeightedTransport ω
structure WeightedDomainAtlas n F Ω extends WeightedSectorAtlas n F Ω where
  W : Set _ ; measurableSet_W ; W_subset : W ⊆ Ω ; signs : ι → Finset (CoordSign n)
  domain_ae : ∀ i, (dom i ∩ φ i ⁻¹' W) =ᵐ[volume] (dom i ∩ selectedOrthants (signs i))
theorem WeightedDomainAtlas.weightedDomainTransport (ha : Measurable a) :
    ∑ i, (A.sectorMeasure a i).map (A.φ i) = (volume.restrict A.W).withDensity a
-- also: ProductSectorAtlas.rescale / DomainSectorAtlas.rescale (box normalisation to [−a,a]^n), DomainSectorAtlas.ofAll (W := Ω, all orthants), ofBoundaryMonomials
-- worked model: shiftedAtlasOf τ … : WeightedDomainAtlas … built by feeding a measurable partition τ into hasWeightedTransport_of_partition (CD regression)
theorem exists_smooth_partition {ι} [Fintype ι] {s : Set (Fin n → ℝ)} (hs : IsClosed s) (U : ι → Set _) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ χ : ι → (Fin n → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧ (∀ i, ∀ x, x ∉ U i → χ i x = 0) ∧ ∀ x ∈ s, ∑ i, χ i x = 1
-- (ℝ^n only; proved from Mathlib SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Fin n → ℝ)))
theorem volume_preimage_null_of_contDiffAt (hsm : ∀ x ∈ s, ContDiffAt ℝ 1 f x) (hjac : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) (ht : volume t = 0) : volume (s ∩ f ⁻¹' t) = 0
```
Mathlib available: `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, `integral_image_eq_integral_abs_det_fderiv_smul` (ℝ^d, InjOn), `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, `SmoothPartitionOfUnity.exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s) (U) (ho) (hU)` on a Mathlib manifold `IsManifold I ∞ M`, `exists_contMDiffMap_zero_one_of_isClosed`.

### 1.3 The consumer (grammar; consult #118)
```
structure SmoothSheetInputs (d : ℕ) where
  K ; K_m : Measurable K ; Ω ; A : WeightedDomainAtlas d K Ω ; a ; ha : 0 < a ; lo_eq : ∀ i j, A.lo i j = -a ; hi_eq : ∀ i j, A.hi i j = a
  K_nonneg : ∀ w ∈ A.W, 0 ≤ K w
  prior obs : (Fin d → ℝ) → ℝ ; prior_nonneg : ∀ w, 0 ≤ prior w ; prior_smooth : ContDiff ℝ ∞ prior ; obs_smooth : ContDiff ℝ ∞ obs
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  φ_smooth : ∀ i, ContDiff ℝ ∞ (A.φ i) ; ω_smooth : ∀ i, ContDiff ℝ ∞ (A.ω i) ; jacAbs_smooth : ∀ i, ContDiff ℝ ∞ fun y => |A.jacUnit i y|
  hu_tan : ∀ i (w w'), (∀ j, ¬ 0 < A.k i j → w j = w' j) → A.phaseUnit i w = A.phaseUnit i w'
theorem SmoothSheetInputs.hasSmoothCoordFreeExpansion : HasSmoothCoordFreeExpansion (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) X.decomp.coeff X.decomp.commonQ X.decomp.commonD
-- decomp : SmoothCoreDecomposition with tail := 0 (the atlas pieces exhaust vol|_W). SmoothCoreDecomposition itself ALLOWS a tail measure with a phase gap δ₀ (gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z).
-- also available: exists_contDiff_eqOn_of_contDiffOn (smooth extension from an open nbhd of a closed set, CCCXCVIII), SmoothSheetNhdsInputs (prior/obs smooth on a nbhd of the closed W only).
```

## 2. A candidate design (please audit, correct, and turn into units)

**Target A (first, boundary-free).** `K : ℝ^d → ℝ` analytic on an open `U₀`, `K ≥ 0` on a connected open `W ∋ 0` with `K(0) = 0`, `K` not identically zero near `0`; `prior ∈ C_c^∞` with `tsupport prior ⊆ W` (compact support INSIDE the open W), `prior ≥ 0`; `obs : ℝ^d → ℝ` smooth. Conclusion: `HasSmoothCoordFreeExpansion (fun N => ∫ prior·obs·e^{−NK}) c Q D` for SOME `(c, Q, D)` (intrinsic by the certificate). This removes domain rectification entirely (the paper's compact semianalytic `W` becomes Target B later, via a joint resolution of `K` and the boundary functions — hironaka has `AnalyticQChartPacket (Δ : BMData n s)` with `s` auxiliary functions but its phase clause is a disjunction, so B is not free).

**Bridge plan for A.**
1. `Nonempty (WatanabeModificationOn K W)`; `C := g⁻¹(tsupport prior)` is compact in `U` (properness into `W`); `Z := K⁻¹(0) ∩ W` is `volume`-null (analytic, not identically zero on connected `W` — is this in Mathlib/hironaka? needs `AnalyticOnNhd` zero-set null lemma) and `g⁻¹(Z)` is covered by the chart clause.
2. Charts: at each `P ∈ C ∩ g⁻¹(Z)` an even Watanabe chart `φ_P` (`S = 1`, `K∘watanabeRep = ∏ u^{2k}`, `det = b·u^h` on ALL of `φ_P.target`); at each `P ∈ C ∖ g⁻¹(Z)` any chart of the atlas (there `K∘g > 0`). Choose closed boxes `B_P ⊂ B'_P ⊂ φ_P.target` (concentric, `B_P` in the interior of `B'_P`); compactness of `C` gives finitely many `P_1..P_m` with `C ⊆ ⋃ φ_{P_i}⁻¹(int B_{P_i})`. Set `dom_i := B'_{P_i}` (then rescale to `[−a,a]^d` by `DomainSectorAtlas.rescale`-type constructors — the Watanabe boxes are centred at `φ P = 0`, so symmetric boxes are natural), `φ_i := watanabeRep g φ_{P_i}` (analytic on the open `φ.target ⊇ B'`), `k_i, h_i, jacUnit_i := b_i, phaseUnit_i := 1`.
3. Partition of unity ON `U`: `ρ_i` smooth on `U`, `supp ρ_i ⊆ φ_i⁻¹(int B'_i)`, `∑ ρ_i = 1` on the closed set `⋃_i φ_i⁻¹(B_i) ⊇ C`. Requires Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` on `U` — hironaka's `AnalyticManifold` is its own structure: is there (or can there cheaply be) an `IsManifold 𝓘(ℝ, ℝ^d) ∞ U`, `T2Space U`, `SigmaCompactSpace U` instance? (Risk 1.) Alternative avoiding manifold PoU: build the partition in ℝ^d chart by chart? (A partition on the target side `W ∖ Z` is NOT acceptable: the pulled-back weights must be smooth ACROSS the walls `{y_j = 0}` of the boxes, and a target-side partition on the open set `W∖Z` has no control there.)
4. Target-side weights: `χ_i(y) := ρ_i(g⁻¹ y)` for `y ∈ W ∖ Z` (via `isoOff`: `g` is a bijection `g⁻¹(W∖Z) → W∖Z` and a local diffeo), `χ_i := 0` on `Z`. Measurable (continuous on the open `W∖Z`). Pull-backs `ω_i(x) := χ_i(φ_i x) = ρ_i(φ_i.symm x)` for `x ∈ B'_i ∖ walls`, `= ρ_i(φ_{P_i}.symm x)` everywhere on `φ.target` by continuity/smoothness — smooth on `φ.target` (Risk 2: showing `ω_i = ρ_i ∘ φ.symm` a.e. on the box and that THIS is the smooth representative; `HasWeightedTransport.congr_ae` exists).
5. `PartialResolution d K W_dom` with `W_dom := ⋃_i φ_i(B_i)` (compact, `⊇ tsupport prior`, `⊆ W`): `cover` trivial; `E_i := walls ∩ B'_i` (closed null; `= φ_i⁻¹(Z) ∩ dom` since `K∘φ_i = ∏ u^{2k}`; for the off-zero charts `E_i := ∅`); `inj` off `E_i` from `BijOn g` + injectivity of `φ.symm`; `jac_ne_zero` from `b ≠ 0`; `mult ≤ m`, `multN := Z`. Then `hasWeightedTransport_of_partition` with `hsum`: for `y ∈ W_dom ∖ Z`, `g⁻¹y ∈ ⋃ φ_i⁻¹(B_i)` so `∑ ρ_i(g⁻¹y) = 1`, and `χ_i(y) ≠ 0 ⇒ g⁻¹ y ∈ φ_i⁻¹(int B'_i) ⇒ y ∈ φ_i(dom_i)`, so the indicators are invisible. `WeightedDomainAtlas` with `W := W_dom`, `Ω := W_dom`, `signs := univ` (`domain_ae` trivial since `φ_i(dom_i) ⊆ … `— careful: `dom_i ∩ φ_i⁻¹ W_dom = dom_i` needs `φ_i(B'_i) ⊆ W_dom`; fix by choosing `W_dom := ⋃_i φ_i(B'_i)` and the partition summing to one on `⋃ φ_i⁻¹(B'_i)`? then the subordination must be to a still larger open set: use THREE nested boxes `B ⊂ B' ⊂ B''`, `dom := B''`? Please settle the box bookkeeping).
6. Off-zero charts: `K∘φ_i > 0` on the compact `dom_i`, so those pieces are a TAIL with gap `δ₀ := min_i min_{dom_i} K∘φ_i > 0` — they are not monomial cores. So the consumer should be `SmoothCoreDecomposition` with `tail := ∑_{off-zero i} (piece measures)`, i.e. a `SmoothSheetInputs` generalisation where the atlas covers `W_dom` but only the charts with `k_i ≠ 0`... Alternatively keep every chart as a core with `k_i := 0`?? — then `phase_eq` forces `K∘φ_i = phaseUnit_i` (a positive analytic unit, NOT tangential in general). Which is cleaner: (a) a `WeightedDomainAtlas`-plus-tail structure (`WeightedDomainAtlasWithTail`: charts + one measurable tail region `T ⊆ W` with `K ≥ δ₀` on `T`, transport `∑ pieces + vol|_T·a = vol|_W·a`), or (b) shrink `W_dom` to a small neighbourhood of `Z ∩ tsupport prior` and treat `tsupport prior ∖ W_dom` (where `K ≥ δ₀`) as the tail directly in `SmoothCoreDecomposition` (measure `(vol|_{supp∖W_dom})·prior`, `gap` from compactness)? Option (b) needs no new hironaka structure: the atlas only has to cover the compact `W_dom := g(⋃ φ_i⁻¹(B_i))` for zero-charts only, and `∫_{ℝ^d} prior·obs·e^{−NK} = ∫_{W_dom} … + ∫_{supp∖W_dom} …`; the second is `O(e^{−δ₀N})`. But then `W_dom`'s complement in `supp prior` must have `K ≥ δ₀`: `tsupport prior ∖ int(W_dom)` compact and disjoint from `Z`? Only if `g⁻¹(tsupport prior) ∩ g⁻¹(Z) ⊆ ⋃ φ_i⁻¹(int B_i)` (true by construction) AND `g(int)` open... `g` is not open near `Z`. Please resolve.
7. Global smoothness of chart data: `φ_i`, `b_i`, `ω_i` are smooth only on `φ.target ⊇ dom_i`; `SmoothSheetInputs` demands global `ContDiff`. Cheapest fix: a grammar-side wrapper `SmoothSheetInputs.ofLocal` taking `ContDiffOn` on an open `V_i ⊇ dom_i` and extending each of `φ_i`, `|b_i|`, `ω_i` by CCCXCVIII's `exists_contDiff_eqOn_of_contDiffOn` — the producer only evaluates them on the boxes (`piecePresentation` uses `T s v ∈ box`), but the atlas STRUCTURE fields (`phase_eq`, `jac_eq` on `V`, `transport`) refer to the original `φ_i`; the extension changes `φ_i` off `dom_i` so a new atlas record must be rebuilt with `V_i := int(dom_i)`-ish. Is it cleaner to weaken `SmoothSheetInputs` to `ContDiffOn … (A.V i)` and extend INSIDE the producer (the amplitude family `ofAffine` needs a globally smooth `G`; extend `G := ω·|b|·prior∘φ·obs∘φ` on `V_i` as ONE function agreeing on the closed box)? Please choose.
8. Analytic prerequisites to check: (i) `Z` null (`AnalyticOnNhd`, connected, not identically zero ⇒ zero set null — Mathlib? there is `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`; measure-zero of the zero set of a non-trivial analytic function on ℝ^d needs a separate lemma; hironaka may have one — otherwise the a.e. statements can avoid it: `hsum` needs `∑ = 1` a.e. on `W_dom`; points of `Z` are where `χ_i = 0`, so `Z ∩ W_dom` must be null anyway); (ii) `g⁻¹(Z)` in chart `i` = walls (null) — automatic from the monomial form; (iii) `isoOff` gives `BijOn g (g⁻¹(W∖Z)) (W∖Z)`.

## 3. Questions
1. **Audit the plan.** Wrong steps? Hidden gaps (measurability of `χ_i`, the a.e. identification of `ω_i` with the smooth `ρ_i∘φ.symm`, the box bookkeeping in 5, the tail in 6, `Z` null)? Is the `PartialResolution` + `hasWeightedTransport_of_partition` route the right bridge, or should the bridge be a direct chart-by-chart identity `∫_{W_dom} f = ∑_i ∫_{B'_i} f(φ_i x)·|b_i(x)|·|x^{h_i}|·ω_i(x) dx` proved from `integral_image_eq_integral_abs_det_fderiv_smul` on `B'_i ∖ walls` and the partition — bypassing `PartialResolution`'s `mult` fields?
2. **Risk 1 (manifold PoU).** hironaka's `AnalyticManifold.{0} ℝ (Fin d → ℝ)` — we will check what instances it carries; if it is not a Mathlib `IsManifold`, what is the cheapest way to get a smooth partition of unity on `U` subordinate to finitely many chart sources and summing to one on a compact set? (E.g. build bumps in charts: `ρ_i := (β_i ∘ φ_i)` extended by zero outside `φ_i.source`, with `β_i` a smooth bump in ℝ^d supported in `int B'_i` and `= 1` on `B_i` — then `∑_i ρ_i ≥ 1` on `⋃ φ_i⁻¹(B_i)` and normalise: `ρ_i / ∑_j ρ_j` near the set. Smoothness of `β_i ∘ φ_i` on `U` needs only that `φ_i` is a chart of the maximal atlas and the zero-extension is smooth (support inside the open source). This needs no Mathlib PoU at all and stays in ℝ^d for all analysis except "chart transition maps are smooth", which is exactly the atlas compatibility. Is this the way? Then the target-side `χ_i = ρ_i∘g⁻¹` and the pull-back to chart `i` is `ρ_i∘φ_i.symm = (∑_j β_j∘φ_j∘φ_i.symm)⁻¹·β_i` — smooth on `φ_i(source_i ∩ ⋃…)` via transition maps.)
3. **Tail handling (6) and Target choice.** Confirm Target A (compactly supported prior inside the open `W`) as the first unconditional theorem; decide between the tail options; state the final theorem in Lean-ready form. Then outline Target B (compact semianalytic `W`) and what hironaka would need (joint monomialisation of `K` and the boundary functions — `AnalyticQChartPacket`'s disjunction, or a new export).
4. **Units.** Give an ordered list of units (hironaka-side vs grammar-side), each with: statement (Lean-ready), inputs, estimated size, risk. Identify the FIRST unit to land and any regression to run first (e.g. `d = 1`, `K = x²` on `W = (−1,1)`, `prior` a bump: the Watanabe modification is the identity; the bridge should reproduce the CD-style certificate).
5. **Acceptance criterion** for the project (what theorem, with what hypotheses, counts as "the atlas exists"), and a non-claims list.
