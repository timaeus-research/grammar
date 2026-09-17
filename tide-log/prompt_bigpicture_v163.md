# Big-picture consult #163: after the Stein identity — what next for posterior expectations

You are Astra, design consultant for the Lean 4 (Mathlib) formalisation of the grammar paper (repo `timaeus-research/grammar`,
namespace `Grammar`, 890 modules, axiom-clean). Answer as a mathematician-engineer: rank, decide, give Lean-typable statements.

## Landed since consult #162 (main 89287cc)

* `SourceLog`: `U (log U)' = U'` for `PowerSeries.logOf`; `κ₁ = B⁻¹A`, `κ₂ = B⁻¹C − (B⁻¹A)²`; block level
  `κ₂(j) = quotientBlocks c b j − Σ_{i≤j} quotientBlocks a b i · quotientBlocks a b (j−i)` (`varianceBlocks`).
* `PosteriorVarianceExpansion`: ★★★ `emp_variance_isBigO` — the posterior variance of a smooth observable to all orders for a fixed
  sample: `Z₃/Z₂ − (Z₁/Z₂)² − Σ_{j<J} κ₂,j(log N) N^{−j/Q} = O(N^{−J/Q}(1+log N)^{D(2J+2)})`.
* `InverseEvidence`: `D_ρ(g)⁻¹ ≤ λe^{2β}ρ(K)⁻¹(1+‖g‖)^{2λ}`; all inverse moments for a Gaussian Borel law on `C(K,ℝ)`;
  radial moments `⟨t^p⟩_g ≤ Π_{i<p}(2(λ+i)/β + ‖g‖²/4)`.
* `QuenchedSource`: `log⟨e^{εf}⟩_g` with `|·| ≤ |ε|M`; `∂_ε = ⟨f⟩_{g,ε}`; `Ψ(ε) = E log⟨e^{εf}⟩_G`, `Ψ'(0) = E⟨f⟩_G`,
  `Ψ''(0) = E[⟨f²⟩_G − ⟨f⟩_G²]` (finite `P`, jointly measurable field, bounded measurable `f`).
* `PosteriorWeightStein` + `CompactBaseStein`: finite-atom `∂_j⟨f⟩_g = β W_j(g)(f_j − ⟨f⟩_g)` (`W_j = ρ_j S_{λ+1/2}(g_j)/D`), and
  ★★★ `GaussianField.integral_eval_mul_compactAvg`:
  `E[G(x₀)⟨f⟩_G] = β E[⟨f 𝒞(x₀,·)⟩^{½}_G − ⟨f⟩_G ⟨𝒞(x₀,·)⟩^{½}_G]`, `⟨φ⟩^{½}_g = ∫ φ S_{λ+1/2}(g) dρ / D_ρ(g)`,
  for every `GaussianField 𝒞 P` (structure: `G : Ω → C(K,ℝ)`, measurable evaluations, `∫‖G‖² < ∞`, fidi laws `gaussianVector A`
  with `AAᵀ = kernelMatrix`) and continuous `f`. Proof: quantised bases via `GaussianField.law` on `(G(x₀), atoms)` + dominated
  convergence along a quantisation sequence.
* Existing (older): `hasDerivAt_interpL`/`integral_log_quartetD_eq(_gen)` — covariance interpolation for `E log D(√s G)` on finite
  atoms (derivative `(β²/2) E[Σ b_jj R_j − Σ b_ij W_i W_j]`, via chain rule in `s`, Stein, poly-bounded domination), and its compact-base
  form `integral_log_compactD_eq` by quantisation. Tools: `PolyBoundedPi` algebra, `integrable_gaussianVector_of_polyBoundedPi`,
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `exists_quantisation_seq`, `tendsto_integral_comp_quantise`.

## Candidates

(I) Three-replica covariance interpolation for the averaged posterior mean: `A(s) = E⟨f⟩_{√s G}`,
    `A'(s) = (β²/2) E[Σ_j b_jj R_j(f_j − ⟨f⟩) − 2 Σ_ij b_ij W_i W_j (f_j − ⟨f⟩)]` at `√s G` on finite atoms (from
    `∂_i∂_j⟨f⟩ = β²[δ_ij R_j(f_j − ⟨f⟩) − W_iW_j(f_j − ⟨f⟩) − W_iW_j(f_i − ⟨f⟩)]`), then `A(1) = ρ(f)/ρ(K) + ∫_0^1 A'(s) ds`, then the
    compact base by quantisation (new compact-base terms: `⟨φ t⟩_g = ∫ φ S_{λ+1}(g)dρ/D`, and the bilocal
    `∫∫ 𝒞(x,y) φ(x) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ / D²`, cf. `compactQ`/`bilocalC`). Big (est. 500–700 lines).
(II) The two-replica REWRITING of the Stein identity as an integral over the product Gibbs measure (define the joint Gibbs measure
    `μ_g` on `K × (0,∞)` as a `Measure`, prove `⟨φ⟩^{½}_g = ∫ φ(x)√t dμ_g`, and state `E[G(x₀)⟨f⟩_G] = β E ∫∫ f(x₁)(√t₁𝒞(x₀,x₁) − √t₂𝒞(x₀,x₂)) dμ_g dμ_g`).
    Presentation infrastructure; moderate.
(III) The convergent source expansion: `Ψ(ε) = Σ_{r≥1} (ε^r/r!) E κ_r^{μ_G}(f)` for `|ε| < log 2/M` — needs the formal cumulant/moment
    algebra of `logTilt` at all orders (Mathlib `PowerSeries.logOf` + analytic identification). Moderate–big.
(IV) Higher cumulants for a fixed sample: instantiate `κ_r` blocks (r ≥ 3) via the recurrence and prove the all-orders expansion of the
    r-th posterior cumulant (generalising `emp_variance_isBigO`). Moderate; mostly bookkeeping of products of truncated expansions.
(V) The Fréchet derivative of `g ↦ ⟨f⟩_g` on `C(K,ℝ)` with the sup norm (`HasFDerivAt` with witness `C(K,ℝ) →L[ℝ] ℝ`), giving the
    Stein identity in Astra's Banach form `E[G(x₀)F(G)] = E[DF(G)[𝒞(x₀,·)]]` as a corollary of the landed identity. Moderate.
(VI) Anything connecting back to the EMPIRICAL side: e.g. the leading term of the averaged posterior mean `E E_N[f] → E⟨f⟩_G` is landed
    (`tendsto_integral_expectation`, bounded observables); is there a cheap statement combining it with Stein (e.g. the limit of
    `E[Z_N-normalised field × E_N[f]]`)? Or is that the averaging-of-remainders problem in disguise?

## Questions
1. Rank (I)–(VI) by value per Lean effort for the paper's narrative (posterior expectations via Gibbs-measure replica calculus). Which
   ONE to do next, and what to stop at?
2. For (I): confirm the second-derivative formula and the resulting finite-atom derivative of `A(s)`; specify the compact-base statement
   (which new averaged quantities to define) and whether to present it as `A(1) − A(0) = ∫_0^1 …` or as a derivative identity only.
   Any simplification (e.g. proving the interpolation identity for `E⟨f⟩_{√sG}` directly from the landed Stein identity applied to the
   field `√s G` plus a chain rule, avoiding second derivatives)?
3. Is there a cleaner formulation of the joint Gibbs measure for Lean (product measure `ρ ⊗ Lebesgue` with density) that would make
   (II) essentially free and (I)'s new terms uniform? Or should we stay with the `S_ν` moments (`ν = λ, λ+1/2, λ+1`) as now?
4. Anything in the landed statements that is misleading or should be renamed/restated before it is cited in the notes?
