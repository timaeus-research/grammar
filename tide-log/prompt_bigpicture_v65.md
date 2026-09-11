# Astra consult #65 — review of the bundle layer (units 8–15) and next direction

You are Astra, direction-setting consultant for the Lean 4 (Mathlib v4.33.1) formalisation of Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*, repo `timaeus-research/grammar`. Your consult #64 designed the bundle programme (units 8–15). Everything except the *general* unit 14 is landed (grammar main `eb7ac7d`, 480 modules, axiom-clean, zero sorries). `timaeus-research/strucdual` was bumped to Mathlib v4.33.1 (master `4f317b3`) and is a lake dependency.

## Headline rows landed

| **CLXXVIII** | **the normal bundle of a coordinate stratum and its tubular equivalence (u489; Astra #64 units 14–15, coordinate case)**: in the adapted chart `ℝ^{m+k} = ℝ^m × ℝ^k` the stratum `{u = 0}` with the last `k` coordinate functionals as labelled defining equations is a `LabelledDefiningEquations` instance (`stratumEquations`; independence of the coordinate functionals `linearIndependent_uCoord`), its gradient frame is the constant coordinate frame `c ↦ (0,c)` (`frame_eq`, via `rieszCLM_proj`: the Riesz gradient of a coordinate functional is the coordinate vector) and its normal field the last `k` coordinate directions (`normal_eq`), so the normal bundle is the trivial `C^∞` bundle (`contMDiffVectorBundle`); **the tubular equivalence**: `(v, n) ↦ v + n` is a diffeomorphism from the total space of the normal bundle onto the ambient chart with inverse `y ↦ (foot y, normal coordinate y)` (`tubeDiffeomorph`, `tubeInv_tubeMap`, `tubeMap_tubeInv`, `contMDiff_tubeMap`, `contMDiff_tubeInv` via `Trivialization.contMDiff_iff`), restricting to the embedding on the zero section with the foot as retraction (`tubeMap_zero`, `foot_tubeMap`) — the coordinate-stratum tube at infinite radius, StrucDual's `stratum_tube` supplying the finite-radius analytic tubes; the invariant contraction through this normal bundle is CLXXII's chart contraction with `Φ₀ v c = G(v,c)` (`normalContraction_eq_chart`). Non-claims: no cross-chart gluing of the resolved space; general unit 14 (tubular diffeomorphism of an abstract normal bundle) remains open | CoordinateStratumBundle.lean |
| **CLXXVII** | **global normal sections — the "global section" clauses of `defn:normal_diff` and `lem:normal_deriv` (u488; Astra #64 unit 13)**: for a frame atlas of the normal field, a family of symmetric fibre forms `σ x : JetForm (N x) r` is a **global normal section** when its frame coordinates `pullForm i x (σ x) = σ x ∘ (frame i x,…)` are `C^n` on every frame domain (`IsGlobalNormalSection`); the frame coordinates transform by the transition functions (`pullForm_eq_comp_coordChange`, from `frameToN_eq`), composition with a smooth family of linear maps is smooth (`contMDiffOn_compCLM_family`, via Mathlib's `analyticAt_uncurry_compContinuousLinearMap`), so smoothness in one frame gives smoothness in every frame on the overlap (`contMDiffOn_pullForm_of_frame`) and the predicate can be checked in covering frames (`IsGlobalNormalSection.of_cover`); symmetry is frame independent (`isSymmForm_pullForm`), degree zero is the restriction of `F` (`pullForm_normalTaylorForm_zero`); the frame coordinates of the normal Taylor form are the Taylor forms of the frame realisation, unconditionally (`pullForm_normalTaylorForm`, via `frameEquiv` and CLXXII's `normalTaylorForm_comp_equiv`); **the global Taylor-section theorem**: over a base modelled on a normed space, jointly `C^∞` frame realisations `G_i(x,v) = F(Φ_x(frame i x v))` and fibre maps analytic at `0` make `x ↦ D^r_⊥F(x)` a global normal section (`isGlobalNormalSection_normalTaylorForm`, via CLXVI `contDiff_normalTaylorCoeff` and CLXVIII `isSymmForm_normalJet`). Non-claims: no `Sym^r` bundle functor or multilinear-map bundle; no independence from the chosen fibre maps `Φ` (nonlinear reparametrisations change higher jets) | GlobalNormalSections.lean |
| **CLXXVI** | **the normal bundle of labelled defining equations — `eq:decomp_nx` at bundle level (u487; Astra #64 units 11–12)**: over an embedded base (a manifold `B` with a smooth map `emb : B → E` into a finite-dimensional inner product space) with labelled equations `u i l : E → ℝ` on an open cover whose differentials along `emb` are independent and related on overlaps by nonzero scalars (`LabelledDefiningEquations`; the differential law from `u' = g·u` on the zero set, `fderiv_unit_mul_eq_smul`), the **tangent field** `T x = ⋂ ker du_l` is chart independent (`tangent_eq`, via CLXVII `tangentOf_smul`), the **normal field** is `N x = (T x)ᗮ`, the **Riesz gradient frames** `c ↦ ∑ c_l ∇u_l(emb x)` are smooth, injective, with range `N x` (`range_frame`, via CLXVII `orthogonal_tangentOf_toDual`; `rieszCLM` the real Riesz CLM), so with the Moore–Penrose coframes of CLXXV they form a `NormalFrameAtlas` and hence a **`C^∞` normal bundle with fibre `ℝ^k`** (`normalAtlas`, `contMDiffVectorBundle`); **the labelled lines are canonical**: the transition functions are diagonal in the labels, `coordChange i j x c = (a_l⁻¹ c_l)_l` where `du^j_l = a_l du^i_l` (`coordChange_diagonal`), so every coordinate line `ℝ e_l` is preserved (`coordChange_single`) — the normal bundle is the direct sum of the labelled line bundles and its dual splits the conormal bundle as in `eq:decomp_nx`. Non-claims: the base manifold and embedding are inputs (no implicit-function construction of a level-set manifold); normal bundle realised as `(TX)ᗮ` through the metric; no quotient bundle | LabelledNormalBundle.lean |
| **CLXXV** | **frame atlases from frames and coframes (u486; Astra #64 unit 10)**: the transition functions of a `NormalFrameAtlas` are determined by the frames once each frame has a `C^n` left inverse — `FrameCoframeData` (frames onto `N x` with coframes `coframe i x ∘ frame i x = 1`) yields the atlas with `coordChange i j x = coframe j x ∘ frame i x` (`FrameCoframeData.toAtlas`; the frame identity because `frame i x v ∈ N x = range (frame j x)`, `frame_coframe_of_mem_range`); over inner product spaces **frames alone suffice**: the Moore–Penrose left inverse `pinv f = (f†f)⁻¹ f†` inverts any injective `f` (`gram_injective`, `gramEquiv`, `pinv_apply`) and is `C^n` in a smooth injective frame family (`contMDiffOn_pinv`: the adjoint as a real CLM on operators `adjointCLM`, `contDiffAt_map_inverse` on the Gram automorphism), giving `frameCoframeDataOfFrames`. Non-claims: any manifold base, frames are data (Jacobian frames `Jᵀ` with coframes `(JJᵀ)⁻¹J` and dual frames of differentials are the intended instances) | FrameAtlasOfCoframes.lean |
| **CLXXIV** | **the normal bundle from local frames (u485; Astra #64 unit 9)**: a `NormalFrameAtlas` — subspaces `N x ⊆ E` over a manifold `B` covered by local frames `frame i x : V →L E` (injective, range `N x`, `C^n` in `x`) with `C^n` transition functions `coordChange i j x` characterised by `frame j x (coordChange i j x v) = frame i x v` — satisfies the cocycle laws automatically (`coordChange_self`, `coordChange_comp`) and defines a `VectorBundleCore` (`toCore`) with the `IsContMDiff` mixin, so its total space is a **`C^n` vector bundle** by Mathlib's core construction (`contMDiffVectorBundle`); the **ambient realisation** `realise ⟨x,v⟩ = frame (indexAt x) x v` agrees with every frame on its domain through the local trivialisations (`realise_eq_frame`), lands in `N x`, is injective on fibres and identifies `Fiber x ≃ₗ N x` (`realise_mem`, `realise_injective_fibre`, `fibreEquiv`), and is **`C^n` on the total space** (`contMDiff_realise`: the fibre inclusion `NX ↪ B × E` as a smooth fibrewise-linear bundle map); sections are `C^n` iff their frame coordinates are (`contMDiffAt_section_iff_coord`). Non-claims: no subbundle/quotient-bundle framework — bundles of subspaces of a fixed `E` only; frames and smooth transitions are construction data (supplied by units 10–11) | NormalBundleOfFrames.lean |
| **CLXXIII** | **the StrucDual realisation of the chosen normal family (u484; Astra #64 unit 8; strucdual bumped to Mathlib v4.33.1 and made a lake dependency)**: the additive family `Φ_s n = s + n` on a normal field (`additiveFamily`) is inverted on the certified domain of a StrucDual `NormalTubularChart` — `proj (s+n) = s`, `ncoord (s+n) = n`, `s + n ∈ U`, every tube point decomposes, injectivity (`proj_additiveFamily`, `ncoord_additiveFamily`, `additiveFamily_mem_tube`, `additiveFamily_decomp`, `additiveFamily_injective`); its chosen-normal jet is the restricted ambient jet and its contraction the restricted ambient pairing (`rawNormalJet_additiveFamily`, `normalContraction_additiveFamily`); **existence**: a compact `S ⊆ ℝ^d` with a compatible analytic LCI atlas carries an analytic tube for the additive family on `A.normal` (`exists_analyticTube_of_atlas` = StrucDual `exists_analyticNormalTubularChart_of_atlas`), and a coordinate stratum `{u = 0}` of an ambient chart carries one at every radius (`stratum_tube`); **the chart-local coefficient bridge**: StrucDual's mixed normal derivative `normalCoeff F γ v = ∂^γ_u F(v,0)` (a fixed-order fold of directional derivatives) is an iterated directional derivative along the accumulated label list (`normalDeriv_eq_iterD`, via `fderiv_iteratedFDeriv_apply_dir`), whose weight is `γ` (`weightOf_foldLabels`, `card_filter_get_eq_count`), hence for analytic `F` it is the weight component `∂^γ` of CLXVIII of the fibre jet `D^{|γ|}(F(v,·))(0)` (`normalCoeff_eq_weightComponent`), and StrucDual's analyticity of the normal coefficients transfers to the fibre weight components in the tangential variable (`analyticAt_weightComponent_fibre`: the chart-local content of `rem:analytic_tubular`). Non-claims: no inverse function theorem reproved, StrucDual's hypotheses kept verbatim, no bundle topology, no statement on the paper's resolved `U` | StrucDualNormalFamily.lean |


## Key statements (verbatim Lean)

### NormalFrameAtlas (CLXXIV)
```lean
structure NormalFrameAtlas (n : ℕ∞ω) (N : B → Submodule ℝ E) (ι : Type*) where
  /-- the frame domains -/
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  /-- a chosen frame at every point -/
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  /-- the frames -/
  frame : ι → B → V →L[ℝ] E
  frame_injective : ∀ i, ∀ x ∈ baseSet i, Function.Injective (frame i x)
  range_frame : ∀ i, ∀ x ∈ baseSet i, LinearMap.range (frame i x : V →ₗ[ℝ] E) = N x
  contMDiffOn_frame : ∀ i, ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n (frame i) (baseSet i)
  /-- the transition functions `(frame j x)⁻¹ ∘ frame i x` (frame-`i` to frame-`j` coordinates) -/
  coordChange : ι → ι → B → V →L[ℝ] V
  frame_coordChange : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∀ v,
    frame j x (coordChange i j x v) = frame i x v
  contMDiffOn_coordChange : ∀ i j,
    ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] V) n (coordChange i j) (baseSet i ∩ baseSet j)

namespace NormalFrameAtlas

variable {IB V} {n : ℕ∞ω} {N : B → Submodule ℝ E} {ι : Type*} (A : NormalFrameAtlas IB V n N ι)
```

### FrameCoframeData / pinv (CLXXV)
```lean
structure FrameCoframeData (n : ℕ∞ω) (N : B → Submodule ℝ E) (ι : Type*) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  frame : ι → B → V →L[ℝ] E
  range_frame : ∀ i, ∀ x ∈ baseSet i, LinearMap.range (frame i x : V →ₗ[ℝ] E) = N x
  contMDiffOn_frame : ∀ i, ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n (frame i) (baseSet i)
  coframe : ι → B → E →L[ℝ] V
  coframe_frame : ∀ i, ∀ x ∈ baseSet i, ∀ v, coframe i x (frame i x v) = v
  contMDiffOn_coframe : ∀ i, ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (coframe i) (baseSet i)

namespace FrameCoframeData
...
theorem contMDiffOn_pinv {f : B → V →L[ℝ] E} {s : Set B}
    (hf : ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n f s) (hinj : ∀ x ∈ s, Injective (f x)) :
    ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (fun x => pinv (f x)) s := by
  have hadj : ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (fun x => ContinuousLinearMap.adjoint (f x)) s :=
```

### LabelledDefiningEquations (CLXXVI)
```lean
structure LabelledDefiningEquations (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
    [ChartedSpace HB B] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)
    (ι : Type*) where
  emb : B → E
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, E) ∞ emb
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  u : ι → Fin k → E → ℝ
  contDiff_u : ∀ i l, ContDiff ℝ ∞ (u i l)
  indep : ∀ i, ∀ x ∈ baseSet i, LinearIndependent ℝ fun l => fderiv ℝ (u i l) (emb x)
  unit : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∀ l,
    ∃ a : ℝ, a ≠ 0 ∧ fderiv ℝ (u j l) (emb x) = a • fderiv ℝ (u i l) (emb x)

/-- The differential form of a unit change of defining equation: on the zero set of `u`,
`d(g·u) = g · du`. -/
...
theorem coordChange_diagonal (i j : ι) {x : B} (hx : x ∈ D.baseSet i ∩ D.baseSet j) :
    ∃ a : Fin k → ℝ, (∀ l, a l ≠ 0) ∧ ∀ c : EuclideanSpace ℝ (Fin k),
      D.normalAtlas.coordChange i j x c = WithLp.toLp 2 fun l => (a l)⁻¹ * c l := by
  choose a ha using D.unit i j x hx
```

### IsGlobalNormalSection (CLXXVII)
```lean
structure IsGlobalNormalSection (r : ℕ) (σ : ∀ x, JetForm (N x) r) : Prop where
  symm : ∀ x, IsSymmForm (σ x)
  smooth : ∀ i, ContMDiffOn IB 𝓘(ℝ, JetForm V r) n (fun x => A.pullForm i x (σ x)) (A.baseSet i)

/-- **The predicate can be checked in covering frames**: symmetric fibre forms whose coordinates in
...
theorem isGlobalNormalSection_normalTaylorForm
    (hG : ∀ i, ContDiff ℝ ∞ fun p : EB × V => F (Φ p.1 (A.frameToN i p.1 p.2)))
    (hΦ : ∀ x, ContDiffAt ℝ ω (fun n : N x => F (Φ x n)) 0) (r : ℕ) :
    A.IsGlobalNormalSection r fun x => normalTaylorForm N Φ F x r where
  symm := fun x => by
```

### Coordinate stratum (CLXXVIII)
```lean
noncomputable def tubeDiffeomorph :
    Diffeomorph (𝓘(ℝ, ℝᵐ).prod 𝓘(ℝ, ℝᵏ)) 𝓘(ℝ, ℝᵐᵏ) (NB m k) ℝᵐᵏ ∞ where
  toFun := tubeMap m k
  invFun := tubeInv m k
  left_inv := tubeInv_tubeMap m k
  right_inv := tubeMap_tubeInv m k
  contMDiff_toFun := contMDiff_tubeMap m k
  contMDiff_invFun := contMDiff_tubeInv m k

...
theorem normalContraction_eq_chart (G : ℝᵐᵏ → ℝ) {r : ℕ}
    (η : ∀ v : ℝᵐ, MeasureTheory.Measure ((stratumEquations m k).normal v))
    (hr : ∀ v, MeasureTheory.Integrable (fun ξ : (stratumEquations m k).normal v => ‖ξ‖ ^ r) (η v))
    (v : ℝᵐ) :
    normalContraction (stratumEquations m k).normal η hr
        (fun v n => emb m k v + (n : ℝᵐᵏ)) G v =
      momentFunctional
        ((η v).map (((stratumEquations m k).normalAtlas.frameEquiv () (mem_univ v)).symm :
          (stratumEquations m k).normal v →L[ℝ] ℝᵏ))
        (integrable_norm_pow_map' _ (hr v))
        ((r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun c : ℝᵏ => G (emb m k v + nrm m k c)) 0) := by
  rw [normalContraction_frame' _ _ _ _ η hr ((stratumEquations m k).normalAtlas.frameEquiv ()
    (mem_univ v))]
  have h : ∀ c : ℝᵏ, (((stratumEquations m k).normalAtlas.frameEquiv () (mem_univ v)) c : ℝᵐᵏ) =
```

### StrucDual adapter (CLXXIII)
```lean
theorem normalCoeff_eq_weightComponent (hF : ∀ p, AnalyticAt ℝ F p) (γ : Fin k →₀ ℕ)
    (v : Fin m → ℝ) {r : ℕ} (hr : r = ∑ j, γ j) :
    normalCoeff F γ v =
      weightComponent (normalJet (fun u : Fin k → ℝ => F (v, u)) r) (fun j => γ j) := by
  have hF' : ContDiff ℝ ∞ F := contDiff_iff_contDiffAt.2 fun p => (hF p).contDiffAt
```

## What is NOT done
* **General unit 14**: a tubular diffeomorphism from the total space of an abstract normal bundle (over a manifold base `B` with `emb : B → ℝ^d`) onto a StrucDual tube. The forward map `(x, n) ↦ emb x + realise (x, n)` is smooth and injective on the certified domain; the inverse needs `emb⁻¹ ∘ T.proj` smooth on the tube, i.e. a smooth left inverse of the embedding along the tube, which the abstract interface does not supply. The coordinate case is done (CLXXVIII).
* No manifold structure on a level set from the implicit function theorem (Astra #64 unit 11A); the base manifold is an input.
* Nothing on the paper's resolved `U` (hironaka gives charts only) — as agreed.
* The companion note's Astra #62 programme (sampling-identity gate, sub-Gaussian observations, effective-temperature corollary, paper closure) is still pending.

## Questions
1. **Fidelity review.** Do the landed statements say what the paper needs? In particular: (a) is `LabelledDefiningEquations` (scalar law on differentials along `emb`, base a manifold with a smooth map into `E`) an honest model of "labelled defining equations of a stratum related by units on overlaps", and is the diagonal-transition theorem the right formal content of `eq:decomp_nx` at bundle level? (b) Is `IsGlobalNormalSection` (smooth frame coordinates in every atlas frame, with `of_cover`) an acceptable formal reading of "defines a global section of `Sym^r(N^*X)`"? (c) Any statement you would call over-claimed in the headline rows or in the mirror dots (we dotted `defn:normal_diff`'s `Γ(X, Sym^r N^*X)` with `IsGlobalNormalSection` + `pullForm_normalTaylorForm`, `lem:normal_deriv`'s global-section clause with `isGlobalNormalSection_normalTaylorForm` + `coordChange_single`, the tubular-neighbourhood definition sentence with `additiveFamily_decomp/injective` + `proj_additiveFamily`, and the adapted-coordinates sentence of the main proof with `stratumEquations`, `tubeDiffeomorph`, `normalContraction_eq_chart`)?
2. **General unit 14.** Should we (i) state it conditionally with the hypothesis "`emb` has a smooth left inverse on a neighbourhood of `emb(B)` in the tube", (ii) restrict to bases that are open subsets of `ℝ^m` embedded as graphs/coordinate slices (covering the adapted charts), or (iii) leave it and record the coordinate case as the honest endpoint? Give the recommended statement.
3. **Next direction.** Options: (A) return to the companion note (Astra #62 programme), (B) unit 11A (manifold structure on an LCI level set via the implicit function theorem, making CLXXVI apply to StrucDual's atlases with `B := S`), (C) the exact geometric bridge (analytic units / compatible localisation for hironaka's chart form), (D) a reviewing pass (independent fidelity review of the whole coordinate-free + bundle layer). Recommend one with a unit list (≤ 6 units) and stop rules.

Answer in Markdown; be blunt about over-claims.
