# Big-picture consult #162: posterior expectations Z_n[f]/Z_n[1] beyond the leading term

You are Astra, design consultant for the Lean 4 (Mathlib) formalisation of the grammar paper
(Gerraty--Murfet, "Expectations and the Exceptional Divisor"), repo `timaeus-research/grammar`
(namespace `Grammar`, 884 modules, axiom-clean). Answer as a mathematician-engineer: rank, decide,
and give statements precise enough to be typed into Lean. No process advice.

## What is landed (main 52c0490)

Empirical partition function with observable insertion, in a normal-crossing chart on the unit cube:
`Z_N[eta,zeta](N) = ∫_box eta(v) e^{√N mono_k(v) zeta(v)} mono_h(v) e^{-N mono_{2k}(v)} dv`.

* `emp_cutoffExpansion`: for every C^∞ eta, zeta, `Z_N ~ Σ_{μ ∈ (1/Q)ℕ} N^{-μ} Σ_{j ≤ d-1} C_{μ,j}[eta,zeta] log^j N`
  (CutoffExpansion: for each L, error O(N^{-L}(1+log N)^{d-1}); coefficients unique, cutoff-independent).
* `empCoeff_unique`; `boxLeading_shift`; `empCoeff_eq_zero_of_boxLeading_lt/deg`.
* Fluctuation zeta function = Mellin transform of the frozen evidence with the intrinsic coefficients as
  unique polar data, with all analytic hypotheses derived (bridge `FluctuationZetaStrip`).
* Gaussian averaging: the Wick series `E C_{μ,q}[eta,zeta] = Σ_r (1/r!) E C_{μ+r/2,q}[eta (mono_k zeta)^r, 0]`
  with every integrability hypothesis DISCHARGED from `IsGaussianProcess` values on an open set containing
  the closed cube plus an exponential moment `E exp(δ ‖J_R zeta‖²) < ∞`, δ > 1/4
  (`integral_empCoeff_gaussian_wick_of_exp_moment`, modules GaussianJetLaw, MonomialShift, WickEnvelope).
  Key engine: the monomial shift identity `C_{μ+1,q}[u^{2k} eta] = μ C_{μ,q}[eta] − (q+1) C_{μ,q+1}[eta]`
  (proved via d/dN of Z_N, not Mellin).
* Posterior quotient for a FIXED sample to all orders: `quotientBlocks A B` (formal quotient of two
  CutoffExpansions, `quotientBlocks_zero/succ`), deterministic + in-probability posterior mean to all orders
  at the diagonal (bridge `boundedInProbSeq_posteriorMean_allOrders`).
* Gaussian posterior algebra already present (from the averaging_dataset note programme, now closed):
  `gaussianReal_stein`, `stdGaussianPi_stein (k) (hH : ∀ z, HasFDerivAt H (H' z) z) (hH'm) (hHb : PolyBoundedPi H) (hH'b) :
   ∫ z, z k * H z ∂stdGaussianPi (n+1) = ∫ z, H' z (Pi.single k 1) ∂stdGaussianPi (n+1)`,
  `gaussianVector_stein (A : Matrix (Fin m) (Fin (n+1)) ℝ) (i) … : ∫ g, g i * F g ∂gaussianVector A = Σ_j (A Aᵀ) i j * ∫ g, F' g (single j 1)`,
  `PolyBoundedPi`, the quartet theorem `integral_quartetH_eq : E H = β E V` (finite-atom posterior: D = Σ ρ_i S_λ(g_i),
  M2 = second-moment ratio, H = M2/D-type quantity, V the quadratic covariance-weighted form), covariance interpolation
  `integral_log_quartetD_eq : E log D = log(β^{-λ}Γ(λ)|ρ|) + ∫_0^1 (β²/2) E V(√s G) ds`, and the compact-base versions on a
  compact metric space K with a PSD kernel 𝒞 and a Gaussian field `GaussianField 𝒞 P` (structure: G : Ω → C(K,ℝ), finite-dim
  marginals `P.map (G · (x i)) = gaussianVector A` with `A Aᵀ = kernelMatrix x`):
  `compactD β lam ρ g = ∫ S_λ(β; g x) dρ(x)` (S_λ(a) = fluctuation = ∫_0^∞ t^{λ-1} e^{-βt + βa√t} dt),
  `GaussianField.integral_compactH_eq : E H_ρ(G) = β E V_ρ(G)`, `integral_log_compactD_eq`, `log_compactD_zero_le_integral`;
  `GibbsJointRatio`: `expectation π Kh n φ = numerator/normaliser`, `tendstoInDistribution_expectation`,
  `tendsto_integral_expectation` (bounded φ, convergence in distribution of the Hamiltonian ⇒ convergence of E[posterior mean]).

## The question (from the author)

"Return to the actual expectation values against the posterior, i.e. Z_n[f]/Z_n[1]. It's not clear what the right,
beautiful way is to study the asymptotic expansions of these. The leading term is easy. There were ideas about turning
the ratio into products of Gaussian random variables so we get Feynman diagrams from Wick/Isserlis. Is this anything more
than the usual formula for a ratio of asymptotic expansions? Surely this situation comes up elsewhere."

My assessment so far (to be checked):
1. Fixed sample: E_n[f] = Z_n[f]/Z_n[1] is exactly the formal quotient (`quotientBlocks`); the clean organisation is
   the source/log form E_n[f] = ∂_ε log Z_n[e^{εf}]|_0, so the quotient coefficients are the connected (cumulant-like)
   coefficients of the two-variable expansion in (N^{-1/Q}, log N, ε). Everything here is deterministic algebra over the
   already-landed expansions.
2. Averaged over the sample: E[Z[f]/Z[1]] is NOT accessible by a term-by-term Wick expansion of the ratio: expanding
   1/Z[1] = 1/(B_0 + …) around the Gaussian-free part and applying Wick term by term gives exactly the moment/quotient
   formula, and it is ill-founded because E[1/B_0-type] blocks have E D = ∞ past the Gaussian threshold (W ≥ 2; same
   threshold as the envelope). Even where it converges the "Feynman diagrams" are just quotient bookkeeping.
3. The right exact object is the limit Gibbs measure: the leading coefficient is the fluctuation integral
   D(G) = ∫ S_λ(G(x)) dρ(x) over the exceptional divisor/compact base with G the limit Gaussian field; the posterior
   average of f is ⟨f⟩_G = ∫ f S_λ-weights/ D; and the exact tool is Gaussian integration by parts (Stein) on the field:
   E[G(x) F(G)] = ∫ C(x,x') E[δF/δG(x')] dx'. Applied to F = ⟨φ⟩_G this produces replica identities
   δ⟨φ⟩/δG(x') = β(⟨φ · T_{x'}⟩ − ⟨φ⟩⟨T_{x'}⟩) (T = the √t-type tilt observable), and iterating gives the expansion of
   E⟨φ⟩ in covariance lines between replicas — this IS the Feynman-diagram structure, but on the Gibbs measure, not on
   the ratio. Covariance interpolation C_s = sC gives the derivative in s as E of a two-replica covariance and hence exact
   integral formulas (quartet theorem is the first instance: E H = β E V). Analogies: spin glasses (Gaussian IBP + replicas,
   Guerra interpolation, GREM), Schwinger–Dyson equations, Tierney–Kadane (ratio via two Laplace expansions, cancellation
   of leading errors), Watanabe's four formulas.

## Concrete units I am considering (rank these; propose better ones; give Lean-typable statements)

(A) Connected coefficients: define the source expansion Z_N[eta e^{εf}, zeta] as a CutoffExpansion in N with coefficients
    polynomial in ε (finite ε-order truncation), and prove
    `quotientBlocks (C[eta f]) (C[eta]) = d/dε log-coefficients`; i.e. a formal identity `quotientBlocks A B j =
    (∂_ε of the log-series)` phrased over `ℕ → K` for a field K. Plus the second-order version (posterior variance =
    second connected coefficient). Purely algebraic.
(B) Banach-space Gaussian IBP for the compact-base posterior average: for the Gaussian field G with kernel C on K and a
    C¹ functional F : C(K,ℝ) → ℝ with polynomial growth, E[G(x) F(G)] = E[DF(G)(C(x,·))]. Existing: finite-dimensional
    `gaussianVector_stein`; compact-base quantities are limits of finite-atom quantities (`exists_quantisation_seq`,
    `tendsto_compactD_map`). Then the replica identity for posterior averages
    E[G(x) ⟨φ⟩] = β ∫ C(x,x') E[⟨φ T_{x'}⟩ − ⟨φ⟩⟨T_{x'}⟩] dρ(x'), with T the tilt observable, giving e.g. the exact
    formula for E⟨G(x)⟩-type first moments and a second-order "one covariance line" formula.
(C) Finite-N transfer: E_N[f] → ⟨f⟩_G in distribution and E E_N[f] → E⟨f⟩_G for bounded f (exists in bounded case via
    `tendsto_integral_expectation`); extend to the 1/√N correction term? (probably out of reach / low value).
(D) Sanity theorem: E[1/Z-type] = ∞ past the threshold (E D^{-1}? no — E D = ∞ for W ≥ 2 via `lintegral_gaussMomentJ_lt_top_iff`),
    formalising why a Wick expansion of the ratio cannot be justified past the threshold. Cheap; do we want it?

Questions:
1. Is my assessment (1)–(3) right? Anything misleading? Is there a genuinely better "beautiful" framework (e.g. the
   fixed-N ratio as a Gaussian expectation via Z[1]^{-1} = ∫_0^∞ e^{-tZ[1]} dt, or a replica/sourced-log trick) that gives
   expansions of E[Z[f]/Z[1]] in the sample distribution with convergent, Lean-checkable coefficients?
2. Rank (A)–(D) (and alternatives) by value per Lean effort; specify the exact statement of the top unit and its proof plan
   in the existing infrastructure (name the lemmas to reuse). For (B), state precisely what "DF" should be in Lean
   (Fréchet derivative on C(K,ℝ) with the sup norm? or a Gateaux derivative along C(x,·)?) and how to pass from
   `gaussianVector_stein` on atoms to the compact base.
3. For the notes: what is the standard name/literature for "expectation of a Gibbs average via Gaussian integration by parts
   and covariance interpolation" so the notes cite correctly (Guerra–Toninelli interpolation, Talagrand's Gaussian IBP
   lemma, Nourdin–Peccati, Schwinger–Dyson)? Keep this to a short list.
