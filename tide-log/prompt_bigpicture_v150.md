# Consult #150 — Stage B of the jet route: one smooth representative of the analytic Lˢ kernel, in Lean

Context: grammar ↔ greybook bridge (your consults #148, #149). Stage A is DONE in the bridge (`Bridge/AnalyticKernel.lean`, axiom-clean):
```lean
structure AnalyticChartKernel (A : ChartedAtlas ι d νχ K) {s : ℝ≥0∞} [Fact (1 ≤ s)] (F : (Fin d → ℝ) → Lp ℝ s μ) where
  S : ι → Set (Fin d → ℝ);  isOpen_S : ∀ α, IsOpen (S α);  box_subset_S : ∀ α, GreyBook.box d (A.b α) ⊆ S α
  analytic_g : ∀ α, AnalyticOnNhd ℝ (A.g α) (S α);  a : ι → (Fin d → ℝ) → Lp ℝ s μ;  analytic : ∀ α, AnalyticOnNhd ℝ (a α) (S α)
  factor : ∀ α, ∀ u ∈ S α, F (A.g α u) = (∏ i, u i ^ A.k α i) • a α u;  mean : ∀ α, ∀ u ∈ S α, ∫ x, a α u x ∂μ = ∏ i, u i ^ A.k α i
theorem exists_analyticChartKernel (hs : 2 ≤ s) (hd : 0 < d) (hF : IsLpValuedAnalytic F U₀) (hnormF) (hKF : ∀ w ∈ U₀, K w = ∫ x, F w x ∂μ)
    (A) (hAt : A.HasChartTargets U₀) : Nonempty (AnalyticChartKernel A F)     -- via greybook's Lˢ monomial quotient theorem
noncomputable def derivKernel Q α n (v : Fin n → (Fin d → ℝ)) : (Fin d → ℝ) → Lp ℝ s μ := fun u => iteratedFDeriv ℝ n (Q.a α) u v
theorem isLpValuedAnalytic_derivKernel : IsLpValuedAnalytic (Q.derivKernel α n v) (Q.S α)
theorem exists_law_derivKernel … : ∃ f m, (∀ x, ContinuousOn (f x) (box)) ∧ … (∀ w ∈ box, (fun x => f x w) =ᵐ[μ] derivKernelL2 w) ∧
    ∃ ψ : ℕ → Ω → C(box, ℝ), (∀ n ω w, ψ n ω w = preEmpiricalProcess X f m n ω w) ∧ ∃ μlim, laws → μlim ∧ Gaussian fidis   -- greybook Thm 5.9
```
So every finite-order derivative kernel of the standard-form quotient is a Definition 5.3 datum and has its own C(box) law. What is missing for the joint jet law of the empirical field `ξ_n(u) = (1/√n) Σ_i (a(X_i,u) − u^k)` (sign aside) is STAGE B: a representative family `f : E → ℝ^d → ℝ` of `a α` that is, for a.e. `x` (one full-measure set), `C^{R}` (ideally analytic) in `u` on a neighbourhood of the box, with `iteratedFDeriv ℝ k (f x) u v` a representative of `derivKernel α k v u` for ALL `u` simultaneously, and `L^s` envelopes `sup_{u ∈ box, k ≤ R} ‖D^k f(x,u)‖ ≤ B(x)`. Then the order-`k` empirical process of the derivative kernel IS `D^k ξ_n` pathwise on the good event, `chartProcessCM_law` on the index type `ι × JetIdx` gives the joint law, and grammar's closed-branch-jet theorem consumes it.

## What the grey book has (exact declarations; survey of the repo)

Definition 5.3: `IsLpValuedAnalytic F W := IsOpen W ∧ AnalyticOnNhd ℝ F W` (F : ℝ^d → Lp ℝ s μ).

Monomial expansion of a Banach-valued power series (Ch5/MonomialExpansion.lean:80):
```lean
theorem hasSum_monomial_expansion [CompleteSpace G] {F : (Fin d → ℝ) → G} {p : FormalMultilinearSeries ℝ (Fin d → ℝ) G} {w₀} {R}
    (hF : HasFPowerSeriesOnBall F p w₀ R) (hd : 0 < d) {r : ℝ≥0} (hr : (((d : ℝ≥0) * r : ℝ≥0) : ℝ≥0∞) < R) :
    (∀ w, ‖w - w₀‖ ≤ r → HasSum (fun α : MonoIdx d => monomial w₀ α w • monoCoeff p α) (F w)) ∧
    Summable fun α : MonoIdx d => (r : ℝ) ^ α.1 * ‖monoCoeff p α‖
```
(`MonoIdx d` = monomial multi-indices with their degree `α.1`; `monomial w₀ α w = ∏ (w − w₀)_j^{α_j}`; `monoCoeff p α ∈ G`.) The converse (monomial HasSum with summable majorant ⇒ HasFPowerSeriesOnBall / analyticity) is NOT in the repo.

Pointwise expansion of an Lˢ-valued power series (Ch5/LpPointwise.lean:24), reindexed by ℕ:
```lean
theorem exists_pointwise_expansion (hqt : q ≠ ∞) {F : (Fin d → ℝ) → Lp ℝ q μ} {p} {w₀} {R} (hF : HasFPowerSeriesOnBall F p w₀ R) (hd : 0 < d)
    {r : ℝ≥0} (hr : (((d : ℝ≥0) * r : ℝ≥0) : ℝ≥0∞) < R) :
    ∃ (Alp : ℕ → Lp ℝ q μ) (A : ℕ → E → ℝ) (C : ℕ → (Fin d → ℝ) → ℝ) (Rr : ℕ → ℝ),
      (∀ i, Measurable (A i)) ∧ (∀ i, A i =ᵐ[μ] Alp i) ∧ (∀ i, 0 ≤ Rr i) ∧ (∀ i, ∀ w ∈ closedBall w₀ r, |C i w| ≤ Rr i) ∧
      (Summable fun i => Rr i * (eLpNorm (A i) q μ).toReal) ∧ (∀ x, Summable fun i => Rr i * |A i x|) ∧
      (∀ w ∈ closedBall w₀ r, HasSum (fun i => C i w • Alp i) (F w)) ∧ ∀ i, Continuous (C i)
```
(`C i` are the monomials `monomial w₀ α w`; the representative is then `f x w := ∑' i, C i w * A i x`, and — crucially — `∀ x, Summable (Rr i * |A i x|)` holds for EVERY x, not just a.e., because A i are chosen as a.e.-representatives and the majorant is arranged pointwise.) The first-derivative version (Ch5/LpCoeffExpansionDeriv.lean:34) `exists_coeffExpansion_deriv_of_hasFPowerSeriesOnBall` produces `f, Df, m, Dm` on `closedBall w₀ (2r)` with `HasFDerivAt (f x) (Df x w) w` for all x and w in the open ball, `ContinuousOn (Df x)`, a.e. identification with `F w`, and `CoeffExpansion` data for `f` and each `Df · · v` (with `∑ Rr_i |A_i x| < ∞` this is termwise differentiation of the monomial series, once). Compact gluing (Ch6/SamplewiseKernelsDeriv.lean:35) `exists_compact_representative_deriv (hF : IsLpValuedAnalytic F U₀) (hK : IsCompact K₀) (hKU) (hKne) (hd)`: finite cover of `K₀` by balls, representatives on each ball, a σ-selection `f x w = fj (σ w) x w`, agreement on overlaps for x in a full-measure set (countable dense + continuity), then redefinition of `f x := f x₀` off that set, giving `ContinuousOn (f x) K₀`, `HasFDerivWithinAt (f x) (Df x w) K₀ w`, `ContinuousOn (Df x) K₀`, a.e. identification, and `CoeffExpansion` data (used by Theorem 5.9 via `chartProcessCM_law`, whose inputs are `hfc : ContinuousOn (fa α x) box`, `hmc`, `hfam`, `hmam`, `hae : (fun x => fa α x u) =ᵐ a α u`, `hexp : CoeffExpansion X P (fa α) (ma α) box 6` with continuous coefficient functions).

## Questions (design to Lean statement level; be concrete about which Mathlib/greybook declarations to use)

1. **Smoothness route.** From `∑ Rr_i |A_i x| < ∞` and the monomials `C i` on a ball of radius `r`, the cheapest Lean route to `ContDiffOn ℝ R (f x) (ball w₀ r')` for `r' < r` with `iteratedFDeriv ℝ k (f x) w = ∑' i, iteratedFDeriv ℝ k (C i) w * A i x`: (a) Mathlib's `contDiff_tsum`/`iteratedFDeriv_tsum` (Analysis/Calculus/SmoothSeries) — but these need GLOBAL summable bounds `‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ u k i` for all x; monomials are unbounded on ℝ^d — is there a `contDiffOn`/local variant, or should one compose with a fixed smooth cutoff equal to 1 on the ball (`ContDiffBump`), or reparametrise? (b) Build `HasFPowerSeriesOnBall (f x) (pointwise series) w₀ r` from the scalar monomial coefficients `A_i x` — requires the missing converse theorem (a `FormalMultilinearSeries` from monomial coefficients): how hard, and does Mathlib have `FormalMultilinearSeries` ↔ monomial-coefficient correspondence for `Fin d → ℝ` (e.g. via `ContinuousMultilinearMap.mkPiAlgebra`/`ofSubsingleton`/`FormalMultilinearSeries.ofScalars`)? (c) Something else (e.g. prove analyticity of `f x` via Cauchy–Hadamard in each variable and Hartogs — not in Mathlib).
2. **Representing the Lp derivatives.** With route (a), `iteratedFDeriv ℝ k (f x) w v = ∑' i, D^k(C i)(w)[v] * A i x` for every x in the good set; the Lp-valued derivative `iteratedFDeriv ℝ k F w v = ∑ D^k(C i)(w)[v] • Alp i` (termwise differentiation in Lp, from `HasFPowerSeriesOnBall.iteratedFDeriv`? or from `AnalyticOnNhd.iteratedFDeriv` + uniqueness) — the a.e. identification of an Lp-convergent series with a pointwise-convergent series of representatives: which Mathlib lemma (`Lp` limits vs a.e. limits: `MeasureTheory.Lp.tendsto…`, `tendsto_ae_of_tendsto_Lp`? / `Summable.of_norm` in Lp + `ae_tendsto_of_tendsto_in_measure`?) — give the exact route to `(fun x => iteratedFDeriv ℝ k (f x) w v) =ᵐ[μ] iteratedFDeriv ℝ k F w v` for all `w` (uncountably many w, but the exceptional set comes from `∑ Rr_i |A_i x| = ∞` and the finitely many... — is it really w-uniform? note `Alp i` representatives are fixed once).
3. **Envelopes.** `sup_{w ∈ closedBall w₀ r', k ≤ R} ‖D^k f(x,w)‖ ≤ ∑ (majorant) |A i x| =: B x` with `B ∈ Lˢ` (from `Summable (Rr i * eLpNorm (A i))`) — the right Lean packaging (a `MemLp B s μ` statement) and whether `eLpNorm` summability gives `MemLp` of the tsum (Minkowski in Lp: `eLpNorm_tsum_le`? exists?).
4. **Gluing over the compact box.** Greybook's σ-selection gives a function that is locally one ball representative for x in the good set N — so smoothness on N is inherited locally; is that enough for `ContDiffOn ℝ R (f x) (interior)` for x ∈ N, and how to state "one good event": `∃ N, μ Nᶜ = 0 ∧ ∀ x ∈ N, ContDiffOn … ∧ ∀ k ≤ R, ∀ w ∈ K₀, (iteratedFDeriv …) …`? Should the bridge redo the gluing (copying `exists_compact_representative_deriv`'s structure with higher order) or can it reuse `exists_pointwise_expansion` per ball + its own gluing?
5. **Joint law.** `chartProcessCM_law` is hard-wired to `Lp ℝ 6 μ` and `CoeffExpansion … 6`; for the derivative kernels at s = 6 we need `CoeffExpansion X P (fun x u => D^k f x u v) (fun u => D^k m u v) box 6` — is that produced by termwise differentiation (as greybook does at order 1: `hexp` for `Df · · v`), i.e. generalise `exists_coeffExpansion_deriv_of_hasFPowerSeriesOnBall` to order R? What is `CoeffExpansion` exactly (fields), and what is the cheapest way to obtain one for a series `∑ C_i(w) A_i(x)` with `Summable (Rr_i eLpNorm(A_i))`?
6. **Alternative that avoids Stage B?** Grammar's conditional theorem needs random `SmoothRootField`s (branch representatives smooth) and their `branchJet`s. If instead one DEFINES the random jet element as `(empirical process of the derivative kernels)_{k ≤ R}` (well-defined, law converges by Stage C), one still needs it to be the jet of an actual smooth field for the closed-realizable-jets support. Is there a cheaper way to get "a.e. ω the jet element lies in the closure of realizable jets" (e.g. closure is closed, so it suffices that the jet element is an a.e.-limit of realizable jets — of smooth approximations obtained by mollifying the C⁰ field? but the empirical jets need not be jets of mollified fields)? Or should we accept Stage B as necessary and go?

Please give: a ranked route for 1, the exact Lean statement of the Stage B output (`ChartKernelRep`-like structure) and of the 2–3 intermediate lemmas, and the greybook/Mathlib declarations to consume for each. Flag anything above you think is wrong.
