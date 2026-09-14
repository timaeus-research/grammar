# Consult #129 — AUDIT of the RLCT identification on the resolved manifold (CDXXXVII–CDXLII) and CLOSURE of Theorem D

Since #128 (a few hours ago) the following LANDED in grammar (main `97072af`, 756 modules, all axiom-clean; hironaka pin unchanged `5a310bdba`). Your #128 ranked follow-ups (1) sup bound [landed CDXXXVI], (2) D3b, (3) modification independence, (5) RLCT nonvanishing; we did (2), (3), (5) and a realisation theorem. Please (A) audit the statements below for over-claims and for the correct mathematical reading, (B) tell us what the paper should now SAY about Theorem D (one paragraph), and (C) whether Theorem D should be CLOSED or what single further unit is worth doing. Be direct; we can take "close it".

## 1. Verbatim signatures (namespace `Grammar.SmoothEngine.ResolvedData`; `Ξ : ResolvedData d` = (K, W, R : WatanabeModificationOn K W, hKc, hK0, K_m, prior smooth ≥ 0 compactly supported in W, F : R.U → ℝ smooth); `Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior`; `Ξ.coeff Y μ q` = 𝒯^U_{μ,q}[F]; `Ξ.withF G hG` replaces the observable; `Ξ.zeroFibre := π⁻¹(tsupport prior) ∩ {K∘π = 0}` compact; `pairs R hK0 P : Multiset (ℕ×ℕ)` the intrinsic wall data (k,h) at P (CDXXX); `resonanceCount R hK0 μ P := ((pairs P).filter (fun (k,h) => ∃ m:ℕ, 2kμ = h+1+m)).card`)
```
-- SmoothResolvedJetBound.lean (CDXXXVII, D3b)
def ChartJetBound (R : ℕ) (M : ℝ) : Prop := ∀ i : Y.T.ι, JetBound R (centeredBox d (Y.T.a i)) (fun u => Ξ.F (Y.chartInv i u)) M
   -- JetBound R S f M := ∀ r ≤ R, ∀ x ∈ S, ‖iteratedFDeriv ℝ r f x‖ ≤ M ; Y.chartInv i = φ_i⁻¹ on the chart target
noncomputable def jetConstU (μ : ℝ) (q : ℕ) : ℝ   -- Σ_pieces pieceConst · densityBound · baseMeasure.real univ (depends on Y)
theorem abs_coeff_le_of_chartJetBound (μ q) (hJ : Ξ.ChartJetBound Y ((Ξ.X Y).engineOrder μ) M) : |Ξ.coeff Y μ q| ≤ Ξ.jetConstU Y μ q * M
-- SmoothResolvedModificationIndependence.lean (CDXXXVIII)
theorem coeff_eq_of_Z_eventuallyEq (Ξ Ξ' Y Y') (h : Ξ.Z =ᶠ[atTop] Ξ'.Z) (μ q) : Ξ.coeff Y μ q = Ξ'.coeff Y' μ q
theorem coeff_comp_gv_eq_of_modifications (hK : Ξ.K = Ξ'.K) (hp : Ξ.prior = Ξ'.prior) (hf : ContDiff ℝ ∞ f) (μ q) :
  (Ξ.withF (fun P => f (Ξ.R.gv P)) _).coeff Y μ q = (Ξ'.withF (fun P => f (Ξ'.R.gv P)) _).coeff Y' μ q     -- W, W' may differ
theorem coeff_one_eq_of_modifications (hK hp μ q) ; theorem isLeadingIndexOne_iff_of_modifications (hK hp μ₀ q₀) : Ξ.IsLeadingIndexOne Y μ₀ q₀ ↔ Ξ'.IsLeadingIndexOne Y' μ₀ q₀
-- SmoothResolvedRLCTIndex.lean (CDXXXIX)
def IsExtremalData (lam : ℝ) (m : ℕ) : Prop :=
  (∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, 2 * (p.1 : ℝ) * lam ≤ (p.2 : ℝ) + 1) ∧ ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m
theorem isExtremalData_zero : Ξ.IsExtremalData 0 0
theorem resonantZeroFibre_eq_empty_of_precedes (h : IsExtremalData lam m) (hp : Precedes ν p lam (m - 1)) : Ξ.resonantZeroFibre ν p = ∅   -- Precedes ν p μ₀ q₀ := ν < μ₀ ∨ (ν = μ₀ ∧ q₀ < p)
theorem coeff_eq_zero_of_precedes (h) (hp : Precedes ν p lam (m - 1)) : Ξ.coeff Y ν p = 0          -- EVERY observable F
theorem isLeadingIndex_of_extremalData (h) : Ξ.IsLeadingIndex Y lam (m - 1)                        -- unconditional
theorem tendsto_normalised_Z_of_extremalData (h) (hG) : Tendsto (normalised lam (m-1) (Ξ.withF G hG).Z) atTop (𝓝 ((Ξ.withF G hG).coeff Y lam (m-1)))
theorem coeff_nonneg_of_extremalData (h) (hG) (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) : 0 ≤ (Ξ.withF G hG).coeff Y lam (m-1) ; coeff_one_nonneg_of_extremalData
-- MonomialBoxLowerBound.lean (CDXL; namespace Grammar)
noncomputable def monoBoxIntegral (k h : Fin d → ℕ) (ε N : ℝ) : ℝ := ∫ u in pi univ (fun _ => Ioc 0 ε), (∏ j, u j ^ h j) * exp (-N * ∏ j, u j ^ (2 * k j))
theorem exists_tendsto_monoBoxIntegral (k h) (hh0 : ∀ j, k j = 0 → h j = 0) (hε : 0 < ε) (hlam : ∀ j, 0 < k j → 2 * k j * lam ≤ h j + 1)
  (hm : (univ.filter fun j => 0 < k j ∧ 2 * k j * lam = h j + 1).card = m) (hm1 : 1 ≤ m) :
  ∃ C, 0 < C ∧ Tendsto (fun N => N ^ lam / log N ^ (m - 1) * monoBoxIntegral k h ε N) atTop (𝓝 C)
  -- Fubini along piEquivPiSubtypeProd for inactive coords, relabel to Fin n, then boxIntegralGen_isEquivalent_general (state-density programme)
-- SmoothResolvedRLCTPositive.lean (CDXLI)
theorem integral_image_orthant (E : EvenChartBox Ξ.R) (hε : ε ≤ E.r) (g) :
  ∫ y in watanabeRep Ξ.R.g E.φ '' orthant d ε, g y = ∫ u in orthant d ε, |E.b u| * (∏ j, u j ^ E.h j) * g (watanabeRep Ξ.R.g E.φ u)
  -- orthant d ε := (0,ε]^d ; injectivity from injOn_offZero (phase ≠ 0 on the open orthant); Mathlib integral_image_eq_integral_abs_det_fderiv_smul
theorem Z_one_ge_mul_monoBoxIntegral (E) (hε) (hc0 : 0 ≤ c) (hc : ∀ u ∈ orthant d ε, c ≤ |E.b u| * Ξ.prior (watanabeRep Ξ.R.g E.φ u)) (hN : 0 ≤ N) :
  c * monoBoxIntegral E.k E.h ε N ≤ (Ξ.withF 1).Z N
theorem exists_orthant_bound (E) (hP : P₀ ∈ E.φ.source) (hP0 : E.φ P₀ = 0) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀)) : ∃ ε c, 0 < ε ∧ ε ≤ E.r ∧ 0 < c ∧ ∀ u ∈ orthant d ε, c ≤ |E.b u| * Ξ.prior (rep u)
theorem resonanceCount_eq_card_of_centered (E) (hP hP0) (hlam : ∀ j, 0 < E.k j → 2 * E.k j * lam ≤ E.h j + 1) :
  (univ.filter fun j => 0 < E.k j ∧ 2 * E.k j * lam = E.h j + 1).card = resonanceCount Ξ.R Ξ.hK0 lam P₀
theorem coeff_one_pos_of_realised (h : Ξ.IsExtremalData lam m) (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
  (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) : 0 < (Ξ.withF (fun _ => 1) contMDiff_const).coeff Y lam (m - 1)
theorem isLeadingIndexOne_of_realised (h hP₀ hprior hres hm1) : Ξ.IsLeadingIndexOne Y lam (m - 1)
-- SmoothResolvedExtremalRealised.lean (CDXLII)
theorem exists_finset_pairs_subset : ∃ S : Finset (ℕ × ℕ), ∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, p ∈ S   -- finite even chart cover (exists_finite_evenChartBoxes) + pairs_le_of_mem_source
theorem exists_realised_extremalData (hne : Ξ.zeroFibre.Nonempty) :
  ∃ lam m P₀, Ξ.IsExtremalData lam m ∧ P₀ ∈ Ξ.zeroFibre ∧ resonanceCount Ξ.R Ξ.hK0 lam P₀ = m ∧ 1 ≤ m
  -- lam := min wallRatio over the finite set of walls occurring on Z₀ (Finset.exists_min_image); m := Nat.find of the least bound on resonance counts; attained by minimality
theorem exists_isLeadingIndexOne (hne) (hpos : ∀ P ∈ Ξ.zeroFibre, 0 < Ξ.prior (Ξ.R.gv P)) : ∃ lam m, 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧ Ξ.IsLeadingIndexOne Y lam (m - 1)
theorem exists_isLeadingIndexOne_of_pos_on_zeroSet (hne) (hpos : ∀ y ∈ tsupport Ξ.prior, Ξ.K y = 0 → 0 < Ξ.prior y) : same conclusion
theorem coeff_eq_zero_of_zeroFibre_eq_empty (h : Ξ.zeroFibre = ∅) (μ q) : Ξ.coeff Y μ q = 0
```
Recall from before: `Z_one : (Ξ.withF 1).Z N = ∫ prior · e^{−NK}` (Euclidean partition function), and CDXXXIV: `IsLeadingIndexOne` ⇒ `IsLeadingIndex` (leading for ALL observables), positivity `0 ≤ 𝒯[G]` for `G ≥ 0`, `|𝒯[G]| ≤ sup|G|·𝒯[1]`; CDXXXVI sup over the resonant zero fibre.

## 2. Our reading (please correct)
(a) CDXXXIX + CDXLI + CDXLII = "the RLCT identification on the resolved manifold": for a nonempty zero fibre and a prior positive on {K = 0} ∩ supp prior, `Z_N[1] = ∫ prior e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`, c > 0, where λ* = min over walls through Z₀ of (h+1)/(2k) and m* = max number of walls with ratio λ* through a point of Z₀ — i.e. Watanabe's (λ, m) read off the intrinsic wall data of the modification, with the chart-independence of CDXXX making it a statement about the pair (K, prior) via CDXXXVIII. Is it fair to call λ* "the RLCT of (K, prior)" in the paper, or should we say "the extremal exponent of the resolution data (which equals the RLCT)" since the identification of λ* with the largest pole of the zeta function is not formalised?
(b) The positivity hypothesis: `∀ y ∈ tsupport prior, K y = 0 → 0 < prior y` — is this the right hypothesis to state (it excludes priors vanishing at a zero of K on the boundary of their support, where a smaller wall ratio with a vanishing prior would genuinely alter the asymptotics)? Or should we generalise to "positive at one realising point" (already `coeff_one_pos_of_realised`) as the primary statement?
(c) The resonance convention: `resonanceCount λ* P` counts walls with 2kλ* = h+1+n for n ∈ ℕ; under extremality only n = 0 occurs, so it is the number of walls through P with ratio exactly λ*. Correct multiplicity for the log power m*−1?
(d) Non-claims we intend to state: no formula for c; the coefficient functionals are distributions of finite order only chart-wise (CDXXXVII; no test-function topology on U); no comparison between modifications on non-pull-back observables (D7 deferred); no Riesz representation.

## 3. Questions
(A) Audit the six modules' statements for over-claims / misreadings; in particular the proof route of CDXLI (Euclidean partition function ≥ image of the orthant box under π∘φ⁻¹, change of variables, continuity lower bound, monomial asymptotics via the state-density theorem) — is anything missing, e.g. is the orthant `(0,ε]^d` sufficient (we only need a lower bound, so one orthant suffices)?
(B) What should the paper say about Theorem D now (one paragraph, precise wording; you corrected us last time to "closed superlevel sets", "chart-independent on a fixed modification", "conditional leading-index results" — the last is no longer conditional)?
(C) CLOSE Theorem D here, or is there ONE more unit that materially improves the paper-facing statement (candidates: Riesz representation of the leading functional on C(S); x²y² local regression; identification of λ* with the zeta-function pole; the kernels/common-refinement D7)? Rank with S/M/L cost and say which, if any, you would do before closing.
