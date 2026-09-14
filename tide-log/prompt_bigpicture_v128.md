# Consult #128 — AUDIT of Theorem D level (2) as landed (D5–D6, D8a) and DIRECTION: what remains worth doing on the resolved manifold, and what to say in the paper

Since #127 (this morning) the following LANDED in grammar (main `d820762`, 749 modules, all axiom-clean) and hironaka (fork `dmurfet/hironaka@sector-atlas` rev `5a310bdba`). Please (A) audit the statements below against your #127 design and flag over-claims; (B) decide what is worth doing next among the remaining items (D3b continuity on U, D7 kernels, D8b Riesz/Z₀-sup bound, x²y² regression, resolution-independence) or whether level (2) should be CLOSED; (C) give a paper paragraph for level (2) (8–10 sentences, mirror style, naming the Lean theorems in prose) and list the non-claims.

## 1. hironaka additions since #127
```
-- ResolvedJacobian.lean
theorem isLocalDiffeomorphAt_gv {P : R.U} (hP : K (R.gv P) ≠ 0) : IsLocalDiffeomorphAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω R.gv P
theorem EvenChartBox.det_fderiv_rep_ne_zero (E) {u} (hu : u ∈ E.φ.target) (hK : K (watanabeRep R.g E.φ u) ≠ 0) : (fderiv ℝ (watanabeRep R.g E.φ) u).det ≠ 0
theorem EvenChartBox.h_eq_zero_of_k_eq_zero (E) {j} (hj : E.k j = 0) : E.h j = 0        -- inactive Jacobian exponents vanish
-- ResolvedCoreTransport.lean addendum
field phaseConst_eq_one : ∀ i, T.phaseConst i = 1 ;  def evenChartBox (i : X.T.ι) : EvenChartBox R   -- each resolution chart of the transport is an even chart box (radii a/2 < a)
```
## 2. grammar level (2), verbatim signatures (namespace `Grammar.NormalCrossing` unless stated; `R : WatanabeModificationOn K W`, `hK0 : ∀ x ∈ W, 0 ≤ K x`, `hKc : ContinuousOn K W`)
```
-- ResolvedDepth.lean (CDXXX). EvenChartBoxDepth: active E := univ.filter (0 < E.k ·) ; pairData E : Multiset (ℕ×ℕ) := (active E).val.map (fun j => (E.k j, E.h j)) ; monomialForm E : MonomialForm d (unit 1)
theorem EvenChartBoxDepth.pairData_eq_of_centered (E E') (hP : P ∈ E.φ.source) (hP0 : E.φ P = 0) (hP' : P ∈ E'.φ.source) (hP0' : E'.φ P = 0) : pairData E = pairData E'
  -- transition H = φ'∘φ⁻¹ analytic near 0 with analytic inverse (maximal atlas), phases agree, Jacobian chain rule, inactive exponents removed, CDXXVII multiset_pairs_eq_of_phase_eq
def divisor R : Set R.U := {P | K (R.gv P) = 0}
noncomputable def pairs R hK0 (P : R.U) : Multiset (ℕ × ℕ)     -- pairData of a chosen centred box (exists_evenChartBox), 0 off the divisor
theorem pairs_eq_pairData (E) (hP : P ∈ E.φ.source) (hP0 : E.φ P = 0) : pairs R hK0 P = pairData E
noncomputable def depth R hK0 P : ℕ := (pairs R hK0 P).card ;  def Resonates (μ : ℝ) (p : ℕ × ℕ) : Prop := ∃ m : ℕ, 2 * p.1 * μ = p.2 + 1 + m
noncomputable def resonanceCount R hK0 μ P : ℕ := ((pairs R hK0 P).filter (Resonates μ)).card
theorems depth_eq_card_active, depth_le_dim, resonanceCount_le_depth, fst_pos_of_mem_pairs, depth_pos_iff : 0 < depth ↔ P ∈ divisor, resonanceCount_eq_zero_of_nonpos
-- ResolvedDepthLocal.lean (CDXXXI). wallsAt E u₀ := (active E).filter (u₀ · = 0) ; translatedForm E u₀ : MonomialForm (unit ∏_{u₀_j≠0}(v_j+u₀_j)^{2k_j})
theorem pairs_eq_of_mem_source (E) (hQ : Q ∈ E.φ.source) : pairs R hK0 Q = (wallsAt E (E.φ Q)).val.map (fun j => (E.k j, E.h j))   -- ANY even chart box, ANY point of its source
theorem pairs_le_of_mem_source (E) (hP hP0) (hQ : Q ∈ E.φ.source) : pairs R hK0 Q ≤ pairs R hK0 P ; depth_le_of_mem_source ; resonanceCount_le_of_mem_source
def depthGE c := {P | c ≤ depth} ; resonanceGE μ c ; shallowOpen c := (depthGE (c+1))ᶜ ; depthStratum c
theorem isClosed_depthGE (hKc) (c) ; isClosed_resonanceGE (hKc) (μ c) ; isOpen_shallowOpen (hKc) ; depthGE_one : depthGE 1 = divisor ; depthGE_succ_dim : depthGE (d+1) = ∅ ; depthGE_antitone ; resonanceGE_subset_depthGE
theorem mem_depthGE_iff_of_centered (E) (hP hP0) (hQ : Q ∈ E.φ.source) : Q ∈ depthGE (depth P) ↔ ∀ j ∈ active E, E.φ Q j = 0 ; not_mem_depthGE_succ_of_mem_source
-- SmoothResonantSupport.lean (CDXXXIII, engine; namespace Grammar.SmoothEngine)
def resonantCount (k e : ι → ℕ) (μ) : ℕ := #{i | ∃ m : ℕ, 2 k_i μ = e_i + 1 + m}
theorem faceCoef_eq_zero_of_resonantCount_le (k β b J e) (hk hβ hb) (hj : resonantCount (k|J) (e|J) μ ≤ j) : faceCoef k β b J e μ j = 0   -- pole-multiplicity bound threaded from stateDensityRep_coeffAt_eq_zero_of_le
theorem smoothCoeff_eq_zero_of_resonant (hF : ContDiff ℝ ∞ F) (h k) (hk hβ hb) (μ q)
  (hres : ∀ J, q + 1 ≤ resonantCount (k|J) (h|J) μ → ∀ v ∈ closedBox d b, (∀ i ∈ J, v i = 0) → ∀ α, pdMulti α (finRange d) F v = 0) : smoothCoeff F h k β b μ q = 0
-- SmoothResolvedResonant.lean + SmoothResolvedResonantSupport.lean (CDXXXV; namespace Grammar.SmoothEngine.ResolvedData; Ξ : ResolvedData d, Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
def resonantZeroFibre μ q : Set Ξ.R.U := Ξ.zeroFibre ∩ resonanceGE Ξ.R Ξ.hK0 μ (q + 1)      -- compact
theorem faceResonant_le_resonanceCount (p s J) (hv : v ∈ closedBox) (hvJ : ∀ i ∈ J, v i = 0) (μ) : faceResonant p J μ ≤ resonanceCount Ξ.R Ξ.hK0 μ (divPt p s v)
theorem Gloc_eventually_zero (hF : ∀ᶠ P in 𝓝ˢ (resonantZeroFibre μ q), Ξ.F P = 0) … : ∀ᶠ u in 𝓝 (facePt p s v), Gloc p.1 u = 0     -- F vanishes near the divisor point, OR the point is off supp prior
theorem pdMulti_eq_zero_of_eqOn_inter_closedBox (hF : ContDiff) (hb) (hO : IsOpen O) (h0 : ∀ v ∈ O ∩ closedBox d b, F v = 0) (hv₀ : v₀ ∈ O ∩ closedBox d b) (α) : pdMulti α (finRange d) F v₀ = 0
theorem coeff_eq_zero_of_eventually_zero_resonant (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) : Ξ.coeff Y μ q = 0
theorem coeff_congr_of_eventuallyEq_resonant (h : G =ᶠ[𝓝ˢ (Ξ.resonantZeroFibre μ q)] G') : (Ξ.withF G).coeff Y μ q = (Ξ.withF G').coeff Y μ q
theorem coeff_eq_zero_of_eventually_zero_depth (hF : ∀ᶠ P in 𝓝ˢ (Ξ.zeroFibre ∩ depthGE (q+1)), Ξ.F P = 0) : Ξ.coeff Y μ q = 0
theorem coeff_eq_zero_of_tsupport_subset_shallowOpen (hsupp : tsupport Ξ.F ⊆ shallowOpen Ξ.R Ξ.hK0 c) (hq : c ≤ q) : Ξ.coeff Y μ q = 0
-- SmoothLeadingTerm / SmoothResolvedLeading / SmoothResolvedLeadingOne (CDXXXII, CDXXXIV)
def Precedes ν p μ₀ q₀ : Prop := ν < μ₀ ∨ (ν = μ₀ ∧ q₀ < p) ; normalised μ₀ q₀ Z N := N^μ₀ / (log N)^q₀ * Z N
theorem tendsto_normalised_of_leading (hQ) (h : HasSmoothCoordFreeExpansion Z c Q D) (hsupp) (hlead : ∀ ν p, Precedes ν p μ₀ q₀ → c ν p = 0) : Tendsto (normalised μ₀ q₀ Z) atTop (𝓝 (c μ₀ q₀))
def IsLeadingIndex Ξ Y μ₀ q₀ := ∀ ν p, Precedes ν p μ₀ q₀ → ∀ G hG, (Ξ.withF G hG).coeff Y ν p = 0
theorem coeff_nonneg_of_leading (hlead) (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) : 0 ≤ (Ξ.withF G hG).coeff Y μ₀ q₀ ; abs_coeff_le_of_leading (hM : ∀ P, π P ∈ supp prior → |G P| ≤ M) : |𝒯[G]| ≤ M·𝒯[1]
def IsLeadingIndexOne Ξ Y μ₀ q₀ := (∀ ν p, Precedes ν p μ₀ q₀ → 𝒯_{ν,p}[1] = 0) ∧ 𝒯_{μ₀,q₀}[1] ≠ 0
theorem abs_Z_le_mul_Z_one (hM) (N) : |Z^U_N[G]| ≤ M * Z^U_N[1]
theorem isLeadingIndex_of_one (h : IsLeadingIndexOne Ξ Y μ₀ q₀) : IsLeadingIndex Ξ Y μ₀ q₀   -- first nonzero preceding index of G from the finite spectrum; dominated normalised limit → 0 contradiction
theorem coeff_one_pos_of_leading_one (h) : 0 < 𝒯_{μ₀,q₀}[1] ; coeff_nonneg_of_leading_one ; abs_coeff_le_of_leading_one
```
## 3. Questions
(A) Audit: (i) Is `pairs_eq_of_mem_source` + `isClosed_depthGE` + `mem_depthGE_iff_of_centered` an adequate formal content for "the depth stratification is intrinsic and closed, with coordinate-subspace strata in centred charts", given no bundled submanifold? (ii) The resonant support theorem is stated with the hypothesis "F vanishes on a NEIGHBOURHOOD of the compact resonant zero fibre" — is the germ-locality corollary the right paper statement for `supp 𝒯_{μ,q} ⊆ Z₀ ∩ {r_μ ≥ q+1}`, or should we also state the contrapositive "if 𝒯_{μ,q}[F] ≠ 0 then some point of Z₀ ∩ {r_μ ≥ q+1} lies in the closure of {F ≠ 0}"? (iii) `Resonates μ (k,h) ↔ 2kμ ∈ h+1+ℕ` — confirm this is the right resonance relation for the Jacobian exponent convention `det Dπ = b ∏ u^{h}` (the engine's monomial box integral is `∫ ∏ u^{h+m} e^{−N∏u^{2k}}` with the Taylor indices m ≥ 0 shifting h). (iv) Anything over-claimed in the HEADLINES-style summaries above?
(B) Direction. Candidates: D3b (chart-wise jet bound ⇒ continuity of 𝒯^U in F; M–L, mostly re-plumbing Theorem C's `abs_observableCoeff_le` with `F∘φ⁻¹` in place of `f∘ψ`); D7 kernels (normal-jet presentation on `U_c` — you said defer); D8b (sup over Z₀ instead of L, and Riesz on the compact zero fibre); the regression x²y² (needs a hand-built `WatanabeModificationOn` for K = x²y² with charts at all zero points, M); resolution-independence (comparison of two modifications through a common refinement — XL, probably out of scope); "leading index = RLCT" identification (needs the nonvanishing of the leading coefficient of Z_N[1], which we cannot prove in general — but for POSITIVE prior at some zero point? Is there a cheap sufficient condition for `IsLeadingIndexOne` at the first lattice point, e.g. via positivity of the engine's leading face coefficients when the prior is positive on the zero fibre? That would connect 𝒯 to the RLCT for real). Which of these has the best value/cost, and is there anything I have missed that the user's request ("express this in terms of resolution data and the stratification") still demands?
(C) Paper paragraph for level (2) as landed, and the non-claims list.
