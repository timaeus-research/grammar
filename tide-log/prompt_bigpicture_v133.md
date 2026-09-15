# Consult #133 — CLOSURE AUDIT of the residue programme: the stratum measure ν^μ_c, the weighted residue measure ℛ^μ_c, and the leading asymptotic with insertion

Context: consult #132 designed items 2–3 of the residue programme (adopt (3B): the residue is a MEASURE defined from the coefficient functional; build ν on X = U ∖ D_{c+1} via smooth tests → fixed-support approximation → positive linear extension → Riesz; define ℛ := ((c−1)!/Γ(μ))·ν; defer log-form calculus and zeta continuation). All ten units are now landed, plus one extra unit (the extremal/leading-index characterisation you listed under unit 9 "where available"). Grammar main `47eef56`, 771 modules, zero sorry/axiom, hironaka pin unchanged. As before: this is a mathematical audit of the SIGNATURES below (the proofs compile); please check that the statements say what I claim, that the paper wording is faithful, and whether to CLOSE.

## 1. Landed signatures (namespace Grammar.SmoothEngine.ResolvedData unless noted; `Ξ : ResolvedData d` bundles K, prior, the modification R with U := R.U, the observable F; `Y` = resolved core transport; `Ξ.withF G hG` replaces the observable; `Ξ.coeff Y μ q` = 𝒯^U_{μ,q}[F]; `Ξ.zeroFibre` = Z₀ = π⁻¹(supp prior) ∩ {K∘π = 0} (compact); `Ξ.deepZeroFibre c` = D_{c+1} = Z₀ ∩ {depth ≥ c+1}; `Ξ.exactStratum μ c` = S^μ_c = Z₀ ∩ {depth = c} ∩ {r_μ = c}; `Ξ.ZeroOrder μ c` = every wall through S^μ_c has 2kμ = h+1; `Ξ.stratumOpen c` = X = (D_{c+1})ᶜ; `Ξ.IsTest c G` = HasCompactSupport G ∧ tsupport G ⊆ X; `Ξ.T Y μ c G hG := (Ξ.withF G hG).coeff Y μ (c−1)`; `Ξ.Λ Y hc hzero : C_c(X, ℝ) →ₚ[ℝ] ℝ` the positive extension (CDLV, consult #132 units 1–3); `residueSum`, `dlogResidueInt`, `residueConst μ c = Γ(μ)/(c−1)!`, `pieceResidueSum` from CDLIII.)

### CDLVI SmoothStratumMeasure (units 4–10)
```
instance (c : ℕ) : LocallyCompactSpace (Ξ.stratumOpen c)
theorem stratumOpen_inter_exactStratum (μ : ℝ) (c : ℕ) :
    Ξ.stratumOpen c ∩ Ξ.exactStratum μ c =
      Ξ.stratumOpen c ∩ (Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 c ∩ resonanceGE Ξ.R Ξ.hK0 μ c)
theorem isClosed_zeroFibre : IsClosed Ξ.zeroFibre := Ξ.isCompact_zeroFibre.isClosed
theorem isOpen_stratumOpen_diff_exactStratum (μ : ℝ) (c : ℕ) :
    IsOpen (Ξ.stratumOpen c \ Ξ.exactStratum μ c)
theorem exists_cutoff_subset (c : ℕ) {K V : Set Ξ.R.U} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVX : V ⊆ Ξ.stratumOpen c) :
    ∃ χ : Ξ.R.U → ℝ, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ ∧ Ξ.IsTest c χ ∧ tsupport χ ⊆ V ∧
      (∀ P ∈ K, χ P = 1) ∧ ∀ P, χ P ∈ Icc (0 : ℝ) 1
noncomputable def stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c)
instance {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    (Ξ.stratumMeasure Y hc hzero).Regular
theorem integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f : C_c(Ξ.stratumOpen c, ℝ)) :
    ∫ x, f x ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.Λ Y hc hzero f
theorem integral_stratumMeasure_test {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.T Y μ c G hG
theorem stratumMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0
theorem coeff_withF_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero)
theorem coeff_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) :
    Ξ.coeff Y μ (c - 1) = ∫ x, Ξ.F x.1 ∂(Ξ.stratumMeasure Y hc hzero)
theorem observableCoeff_eq_integral_stratumMeasure {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0) :
    (Ξ.X Y).observableCoeff μ (c - 1) f hf =
      ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.stratumMeasure Y hc hzero)
theorem integral_stratumMeasure_eq_residueSum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = (Ξ.withF G hG).residueSum Y μ c
noncomputable def residueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c)
theorem residueMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.residueMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0
theorem integral_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) (g : Ξ.stratumOpen c → ℝ) :
    ∫ x, g x ∂(Ξ.residueMeasure Y hc hzero) =
      ((c - 1).factorial / Real.Gamma μ) * ∫ x, g x ∂(Ξ.stratumMeasure Y hc hzero)
theorem integral_residueMeasure_eq {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∫ x, G x.1 ∂(Ξ.residueMeasure Y hc hzero) =
      ∑ I, ∫ s, (Ξ.withF G hG).pieceResidueSum Y I s μ c
        ∂(((Ξ.withF G hG).decomp Y).chart I).ν
theorem Λ₀_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) (μ : ℝ) (c : ℕ)
    (f : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.Λ₀ Y μ c f = Ξ.Λ₀ Y' μ c f
theorem stratumMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) {μ : ℝ}
    {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero = Ξ.stratumMeasure Y' hc hzero
theorem isCompact_preimage_val {c : ℕ} {L : Set Ξ.R.U} (hL : IsCompact L)
    (hLX : L ⊆ Ξ.stratumOpen c) : IsCompact (Subtype.val ⁻¹' L : Set (Ξ.stratumOpen c))
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero
```
Proof notes. `stratumMeasure_compl_exactStratum`: within X the exact stratum equals Z₀ ∩ depthGE c ∩ resonanceGE μ c (both filtrations closed, `isClosed_depthGE`/`isClosed_resonanceGE`; uses r_μ ≤ depth), so X ∖ S^μ_c is open in U; inner regularity of the Riesz measure (`Regular.innerRegular.measure_eq_iSup`) reduces to compact K ⊆ X ∖ S^μ_c; a cutoff χ ∈ [0,1], = 1 on K, supported in X ∖ S^μ_c has T[χ] = 0 by locality (`T_eq_zero_of_eqOn_zero`, i.e. values-only dependence on S^μ_c), and ν.real K ≤ ∫ χ dν = T[χ] = 0. `coeff_withF_eq_integral_stratumMeasure`: from the neighbourhood-vanishing hypothesis get an open O ⊇ D_{c+1} with G = 0 on O; K₀ := Z₀ ∖ O is compact and ⊆ X; a cutoff χ = 1 on K₀ makes Gχ a test agreeing with G on S^μ_c ⊆ Z₀; values-only dependence gives coeff G = coeff (Gχ) = T[Gχ] = ∫ Gχ dν, and Gχ = G ν-a.e. by the support theorem. `eq_stratumMeasure_of_tests`: `Measure.ext_of_integral_eq_on_compactlySupported`; for f ∈ C_c(X) the chosen approximants G_n (|G_n − f| ≤ 1/(n+1), supports in one compact L) give ∫ G_n dν' → ∫ f dν' by ‖∫_{L'}(G_n − f)‖ ≤ ν'.real(L')/(n+1), while T[G_n] → Λ f = ∫ f dν.

### CDLVII SmoothStratumMeasureExtremal (extra unit)
```
noncomputable def extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure (Ξ.stratumOpen m)
theorem tendsto_normalised_Z_extremal {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), G P = 0) :
    Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
      (𝓝 (∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm)))
theorem tendsto_normalised_partitionObs_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)))
theorem partitionObs_isEquivalent_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0)
    (hne : ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) ≠ 0) :
    (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
      fun N => (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)) *
        (N ^ (-lam) * Real.log N ^ (m - 1))
```
(`IsExtremalData lam m` := 2kλ ≤ h+1 for all walls at Z₀ ∧ r_λ ≤ m on Z₀; `normalised lam q Z N := N^lam / (log N)^q * Z N`; `partitionObs K prior f N = ∫ prior·f·e^{−NK}`; `Z_withF_comp_gv : (Ξ.withF (f∘π)).Z N = partitionObs K prior f N`.)

## 2. Mirror paragraph (grammar_lean.tex, appended after the Theorem E paragraph; [name] = leanref dot; pin to be bumped to 47eef56)
> \smallskip\noindent\textbf{The stratum measure and the weighted residue (formalised).} Under the zero-order condition on $S^\mu_c$ (every wall through the exact stratum has ratio exactly $\mu$) the coefficient functional $\mathcal T^U_{\mu,c-1}$ restricted to $\mathcal I_{c+1}$ determines an intrinsic positive Radon measure $\nu^\mu_c$ on $U\setminus D_{c+1}$, carried by the exact stratum. It is obtained from the Riesz--Markov--Kakutani theorem applied to the positive linear functional $\Lambda$ on $C_c(U\setminus D_{c+1})$ which extends $\mathcal T^U_{\mu,c-1}$ from smooth compactly supported tests (the extension exists and is unique because $|\mathcal T^U_{\mu,c-1}[G]|\le\|G\|_\infty\,\mathcal T^U_{\mu,c-1}[\chi_L]$ for tests $G$ supported in a compact $L$ with cutoff $\chi_L$) [SmoothEngine.ResolvedData.abs\_T\_le] [SmoothEngine.ResolvedData.stratumMeasure]. The measure integrates every smooth test to its coefficient [SmoothEngine.ResolvedData.integral\_stratumMeasure\_test], the complement of $S^\mu_c$ in $U\setminus D_{c+1}$ is a null set [SmoothEngine.ResolvedData.stratumMeasure\_compl\_exactStratum], and every $F\in\mathcal I_{c+1}$, compactly supported in $U\setminus D_{c+1}$ or not, satisfies $\mathcal T^U_{\mu,c-1}[F]=\int F\,d\nu^\mu_c$ [SmoothEngine.ResolvedData.coeff\_withF\_eq\_integral\_stratumMeasure]; in particular $C_{\mu,c-1}(f)=\int f\circ\pi\,d\nu^\mu_c$ whenever $f\circ\pi\in\mathcal I_{c+1}$ [SmoothEngine.ResolvedData.observableCoeff\_eq\_integral\_stratumMeasure]. The measure does not depend on the transport data [SmoothEngine.ResolvedData.stratumMeasure\_eq\_of\_transports] and is the unique regular Borel measure integrating smooth tests to the coefficient functional [SmoothEngine.ResolvedData.eq\_stratumMeasure\_of\_tests]. In normal-crossings coordinates the twisted density $(K\circ\pi)^{-\mu}\mu_U$ has pole order $2k_j\mu-h_j$ along the $j$-th wall, and the fully resonant faces of the exact stratum are exactly those along which every wall is a simple pole [SmoothEngine.exactCount\_eq\_card\_simplePole]; there $\nu^\mu_c$ is $\Gamma(\mu)/(c-1)!$ times the multiplicity-weighted logarithmic residue of the twisted prior density, normalised against $d\log(u_j^{2k_j})$: $\int F\,d\nu^\mu_c$ is $\Gamma(\mu)/(c-1)!$ times the sum over simple faces $J$ of the face integrals $\prod_{j\in J}(2k_j)^{-1}\int_{u_J=0}(F\cdot\text{amplitude})\prod_{i\notin J}u_i^{h_i}(\prod_{i\notin J}u_i^{2k_i})^{-\mu}$ [SmoothEngine.dlogResidueInt] [SmoothEngine.ResolvedData.integral\_stratumMeasure\_eq\_residueSum]. The weighted residue measure $\mathscr R^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\nu^\mu_c$ [SmoothEngine.ResolvedData.residueMeasure] integrates $F$ to this bare residue sum [SmoothEngine.ResolvedData.integral\_residueMeasure\_eq]. Here ``residue'' means the unsigned, multiplicity-weighted residue of a density, which is a positive measure on the stratum; it is not the classical alternating-form Poincar\'e residue of a logarithmic form, and no logarithmic-form calculus is set up. Not asserted: a log-form calculus, the identification of $\mathscr R^\mu_c$ with the coefficient of $(s+\mu)^{-c}$ in a meromorphic continuation of the zeta function, or any extension of $\nu^\mu_c$ across $D_{c+1}$.

Intended addition for CDLVII: "At the extremal data $(\lambda^*,m^*)$ of the RLCT identification the zero-order condition holds on every stratum, and for $f\circ\pi\in\mathcal I_{m^*+1}$ the normalised partition function with insertion converges, $N^{\lambda^*}(\log N)^{-(m^*-1)}\int\varphi f e^{-NK}\to\int f\circ\pi\,d\nu^{\lambda^*}_{m^*}$ [tendsto_normalised_partitionObs_extremal]: the leading coefficient of the partition function with insertion of any observable vanishing near the deeper zero fibre is the weighted logarithmic residue of the twisted prior density integrated against the observable."

## 3. Questions
(a) Audit each ★★★ statement for what it does and does not say. In particular: is `stratumMeasure_compl_exactStratum` the right formalisation of "carried by the exact stratum" (S^μ_c is NOT closed in U, only relatively closed in X; is "carried by" better than "supported on"? should the paper say `supp ν ⊆ closure_X(S^μ_c)`?); is `eq_stratumMeasure_of_tests` a genuine uniqueness statement (regular measures on X determined by smooth compactly supported tests); is `coeff_withF_eq_integral_stratumMeasure` correctly described as the representation of the functional on 𝓘_{c+1} with NO compact-support-in-X requirement (F may be nonzero near D_{c+1}ᶜ ∩ ∂… i.e. anywhere off a neighbourhood of D_{c+1}; note F ∈ 𝓘_{c+1} need not be integrable w.r.t. ν a priori — the theorem asserts the Bochner integral equals the coefficient, which is fine if F∘val is ν-integrable; is it? F∘val = (Fχ)∘val ν-a.e. and the latter is integrable, so yes, but should I state integrability separately?).
(b) The weighted residue measure ℛ^μ_c = ((c−1)!/Γ(μ))·ν: with `integral_residueMeasure_eq` the bare sum ∑_I ∫ ∑_{J simple} ∏(2k_j)⁻¹ ∫ A ∏w^h (∏w^{2k})^{−μ}. Is the sentence "ℛ is the multiplicity-weighted logarithmic residue of the twisted prior density, normalised against d log(u_j^{2k_j})" now JUSTIFIED by the landed chart identity, or does it still need a (deferred) log-density residue calculus to be more than a definition? How should the paper phrase the relation between ℛ and the classical Poincaré residue (unsigned/density vs alternating form; where the twisted density is (K∘π)^{−μ}μ_U with μ_U a positive density)? Give the recommended sentence(s).
(c) CDLVII: is "the leading coefficient of the partition function with insertion IS the stratum-measure integral" correctly hedged (only f∘π ∈ 𝓘_{m*+1}; unit observable excluded unless D_{m*+1} = ∅; total mass not identified with c)? Is there a cheap way to say something about the unit observable / total mass (e.g. ν(X) = ∞ or finite? — ν is finite on compacts of X; is ν(X) finite when D_{m*+1} ≠ ∅? I suspect it can be infinite: the residue weight near the deeper stratum need not be integrable). Should I state `ν.real X` anything, or leave it?
(d) CLOSE the residue programme? If yes, give the final paragraph wording (replace mine if needed). If no, what is the ONE missing unit? Then rank optional follow-ups (measure on the subtype S^μ_c; explicit chart-pushforward measure equal to ν; positivity ∫ f∘π dν > 0 for f ≥ 0 positive at a stratum point where the prior is positive — is that true and cheap via the CDXL orthant lower bound?; x²y² regression; zeta continuation) by value/cost.
(e) Anything in the memory/plan wording to correct: I have been saying "intrinsic positive Radon measure on U ∖ D_{c+1}, carried by the exact stratum" — fine?
