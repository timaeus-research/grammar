# Astra consult #37 — rewriting §3 of the grammar paper (the population theorem) and formalising it

Context: Lean 4 / Mathlib formalisation of the grammar paper (Gerraty–Murfet, "Grammar (Expectations and the Exceptional Divisor)") in `timaeus-research/grammar` (main `99fbdd8`, release pin `f1c0138`; 280 modules, no `sorry`, no added `axiom`). Per your #36 the seabed was marked **COMPLETE — conditional §4 release** (Headlines I–XXXVIII, units 1–289, reviews v1–v31). Your hand-off item 6 was "Rewrite §3 before opening a geometry programme", and your #33/#35 said NO-GO on `thm:expectation_expansion` (the §3 population theorem) "before the authors' rewrite", because the authors themselves flag it in red: *"The theorem is now out of date, and needs to be rewritten with the progress on fluctuations etc."*

**The user (an author) has now instructed:** "consult Astra as to the correct path forward for Section 3 based on what you think we are trying to do, and attempt to formalise that." So the authors' rewrite is being delegated to this process: I am to propose (in a staging note for the authors — never editing the paper itself) what the rewritten §3 theorem should say, and then formalise that statement in Lean. I need your design: the target statement(s), the programme, caps and gates.

## 1. What §3 currently says (verbatim extracts; paper `paper_grammar.tex`)

§3 "Expectation via resolution" (`sec:expect_via_res`) computes the asymptotic expansion of the **population** partition function with observable
```
𝒵_n[φ] = ∫_W φ(w) e^{-nK(w)} ϕ(w) dw,        E_n[φ] = 𝒵_n[φ]/𝒵_n[1]
```
(φ real analytic observable, K the KL divergence, ϕ the prior, W compact, real analytic boundary). Its architecture:

* §3.1 `lem:normal_deriv`/`defn:normal_diff`: on a transverse intersection X = ⋂ Y_i of divisors the conormal bundle splits canonically N*X ≅ ⊕ L_i; for F̃ smooth on the normal bundle NX with linear fibre coordinates u_i, `D_b(F̃) = (1/b!) ∂^{|b|}F̃/∂u^b |_{u=0} (du_1)^{⊗b_1}⊗…` is independent of the linear fibre frame (a frame change is u'_i = g_i(x) u_i with g_i nonvanishing depending only on the base point; the factors g_i^{±b_i} cancel). Normal derivatives of an observable F on M are defined via a tubular neighbourhood Φ : NX → M as D_b(F∘Φ). "The regularity of Φ is load-bearing."
* §3.2 tubular neighbourhoods and pushforward of densities; `eq:pushforward_local` (integrate out the normal variables). Application: in adapted coordinates (v,u) near a stratum S_I, K∘π = ∏_{i∈I} u_i^{2k_i}, |det Dπ| = b(v,u)∏|u_i|^{h_i}, b>0 smooth; the observable φ∘π is an arbitrary analytic function of (v,u), NOT monomialised ("we wish to treat all observables simultaneously using a single resolution adapted to K"). Normal Taylor expansion `(φ∘π)(v,u) = Σ_{|γ|≤N} (1/γ!) D^γ_⊥(φ∘π)(v) u^γ + R_N`; density factor c(v,u) = b(v,u)(ϕ∘π)(v,u) = Σ_δ c_δ(v)/δ! u^δ with c_0 > 0. **Dressed normal moment** `M̃_γ(v,n) = ∫_{D_v} u^γ |u|^{h_I} e^{-n u^{2k_I}} c(v,u) du = Σ_δ c_δ(v)/δ! M_{γ+δ}(n)`, bare normal moment `M_α(n) = ∫ u^α |u|^{h_I} e^{-n u^{2k_I}} du`. Per-stratum expansion
```
𝒵_n[φ; I] ∼ Σ_γ (1/γ!) ∫_{S_I} D^γ_⊥(φ∘π)(v) M̃_γ(v,n) |dv|          (eq:tubular_expansion)
```
"the justification that the Taylor remainder is asymptotically negligible is given in the proof of thm:TaylorTree". `rem:parity`: interior components are integrated over (−ε,ε) and odd h_i+γ_i moments vanish; boundary components over [0,ε).
* §3.3 moment tensors `M_{I,r}(n) ∈ Γ(S_I, Sym^r(NS_I))`, `⟨α, M_{I,r}(n)(v)⟩ = ∫_{D_v} α(ξ^{⊗r}) |u|^{h_I} e^{-nK_I(ξ)} |μ_I|_v(ξ)`; coordinate-free per-stratum expansion `𝒵_n[φ;I] ∼ Σ_r (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩ τ_*|μ_I|` (eq:per_stratum_expansion_coordfree), which in adapted frames reduces to the dressed-moment expansion. `rem:reduce_to_box`: the fibre pairing may be computed over a fixed box ∏ I_i with a cutoff κ; "Taylor expanding the smooth factor κ(u)g(v,u) in u reduces these fibre integrals to finite linear combinations (to any fixed asymptotic order) of the model moments on a box".
* §3.4 standard form: zeta function `ζ(z) = ∏_i b^{2k_i z+h_i+γ_i+1}/(2k_i z+h_i+γ_i+1)`, λ_i(γ) = (h_i+γ_i+1)/(2k_i), λ(γ) = min, J the minimisers, m = |J|, Laurent leading coefficient `a_{-m} = ∏_{J} 1/(2k_i) · ∏_{I∖J} b^{h_i+γ_i+1−2k_iλ}/(h_i+γ_i+1−2k_iλ)` (eq:a_minus_m_explicit). `rem:cutoff_correct`: changing the normal cutoff b changes coefficients but not the candidate exponents or pole orders; localisation in the phase K∘π ≥ ε gives O(e^{-nε}).
* §3.5 per-stratum decomposition, Steps 1–4: (1) pull back to the resolution (`eq:pullback_integral`, change of variables valid since π is injective off the exceptional divisor E); (2) localise to U_ε = {K∘π < ε}, remainder O(e^{-nε}); (3) `lem:adapted_pou`: open V_I ⊆ U_ε with V_I ∩ E_I = S_I, V_I ∩ E_j = ∅ for j ∉ I, covering U_ε, fibre-saturated, and a smooth partition of unity ρ_I constant in normal directions (ρ_I(v,u) = ρ_I(v)); `𝒵_n[φ] = Σ_I 𝒵_n[φ;I] + O(e^{-nε})` with `𝒵_n[φ;I] = ∫_{S_I} ρ_I(v) ∫_{D_v} (φ∘π)(v,u) |u|^{h_I} e^{-n u^{2k_I}} c(v,u) du dv` (eq:per_stratum_form); (4) the normal Taylor expansion above.
* "Asymptotic expansion" paragraph: if (φ∘π)(v,0) ≢ 0 on the stratum the leading exponent is `λ_I = min_i (h_i+1)/(2k_i)`, multiplicity m_I; if φ∘π vanishes to generic order l_i along E_i then D^γ_⊥(φ∘π) ≡ 0 for γ_i < l_i, so only γ ≥ l contribute, and if D^l_⊥(φ∘π)|_{S_I} ≢ 0 the leading exponent is `μ_I(φ) = min_i (h_i+l_i+1)/(2k_i)` (eq:lambda_I_f), "otherwise larger, determined by the first nonzero γ ≥ l". `𝒵_n[φ;I] ∼ Σ_k Σ_{j=1}^{m_{I,k}} C_{I,k,j}(φ) n^{-λ_{I,k}}(log n)^{j-1}` (eq:zn_starting_point), leading coefficient ∝ ∫_{S_I} (φ∘π)(v,0) c_0(v) |dv| (eq:leading_coefficient).

**The flagged theorem** (`thm:expectation_expansion`, preceded by the red note):
> Let φ: W → ℝ be a real analytic observable, and write l_i = ord_{E_i}(φ∘π) ≥ 0 for the generic vanishing order of φ∘π along E_i (well-defined and constant on a dense open subset of E_i by analyticity). Then `𝒵_n[φ] = Σ_I 𝒵_n[φ; I] + O(e^{-nε})` where the sum is over all strata of E. Each contribution admits the asymptotic expansion `𝒵_n[φ; I] ∼ Σ_{k≥1} Σ_{j=1}^{m_{I,k}} C_{I,k,j}(φ) n^{-λ_{I,k}} (log n)^{j-1}`. Writing l = (l_i)_{i∈I}, if D^l_⊥(φ∘π)|_{S_I} ≢ 0 then the leading exponent is `λ_{I,1} = min_{i∈I} (h_i+l_i+1)/(2k_i)` with multiplicity m_{I,1} = |{i : (h_i+l_i+1)/(2k_i) = λ_{I,1}}|; otherwise λ_{I,1} is strictly larger, determined by the first γ ≥ l for which D^γ_⊥(φ∘π)|_{S_I} ≢ 0. The expansion admits the coordinate-free expression `𝒵_n[φ;I] ∼ Σ_{r≥0} (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩ τ_*|μ_I|`. In particular, if l_i = 0 for all i ∈ I, the leading coefficient is `C_{I,1,m_{I,1}}(φ) = Γ(λ_{I,1})/(m_{I,1}−1)! · a_I · ∫_{S_I} (φ∘π)|_{S_I} c_0 |dv|` where c_0(v) = b(v,0)(ϕ∘π)(v,0) > 0 and a_I > 0 depends only on (k_i,h_i)_{i∈I} via eq:a_minus_m_explicit. When some l_i > 0 the leading coefficient instead involves D^l_⊥(φ∘π)|_{S_I} contracted against M_{I,|l|}(n).

Proof: "Steps 1–4 above establish each part … the leading coefficient is computed by combining the moment asymptotics with the dressed moment expansion at γ = 0, δ = 0."

* §3.6 general expectation values: μ_I(φ) = min_i (h_i+l_i+1)/(2k_i) (eq:mu_I_phi); global μ_1(φ) = min over strata; `E_n[φ] ∼ (C'/C) n^{-(μ_1−λ_1)} (log n)^{m̃_1−m_1}` (eq:expectation_leading) where C > 0 "being the integral of a positive density over the leading stratum"; three cases: **generic** (μ_1 = λ_1, m̃_1 = m_1: E_n[φ] → C'/C), **partially vanishing** (μ_1 = λ_1, m̃_1 < m_1: E_n[φ] ∼ D (log n)^{-(m_1−m̃_1)}, D ≠ 0), **fully vanishing** (μ_1 > λ_1: power-law decay). **Wall-crossing**: for φ_τ varying continuously, μ_1(τ) is piecewise constant with jumps where vanishing orders change. `ex:phi_equals_K`: φ = K gives l_i = 2k_i, μ_I(K) = λ_I + 1 uniformly, `E[K] ∼ λ/n`, and directly 𝒵_n[K] = −𝒵_n'(n) so `E[K] = −(d/dn) log 𝒵_n = λ/n − (m−1)/(n log n) + …`. (The all-orders `cor:expectation_expansion` via `lemma:division` is commented out.)
* `rem:pop_vs_emp` (§4.3): "After resolution and applying the standard form, the empirical partition function on each chart takes the form Z(β,n;ξ_n,η) where ξ_n is the empirical process; **the population version is the specialisation ξ = 0**. (i) Exponents are shared … the per-stratum organisation (thm:expectation_expansion), the shifted exponent μ_I(φ) from the vanishing orders, and the wall-crossing mechanism all apply equally to the empirical case. (ii) Coefficients differ …"

Candidate exponent set (§4.2, `eq:candidateexponents`): `Λ(h,k) = ⋃_i ((h_i+1)/(2k_i) + ℕ/(2k_i))`. `thm:TaylorTree`: for ξ, η real analytic on [0,b]^d extending holomorphically to the polydisc D_R, R > b, `Z(β,n;ξ,η) = ∫_{[0,b]^d} u^h e^{-βn u^{2k} + β√n u^k ξ(u)} η(u) du ∼ Σ_{μ∈Λ*} n^{-μ} P_μ(β,ξ,η,log n)`, P_μ polynomial of degree ≤ d−1 with absolutely convergent coefficient series. Remark after it: "The theorem makes no sign assumption on η. Without η > 0, the leading coefficient could vanish identically and the true leading exponent could be larger … u^h η(u) incorporates both the Jacobian and (depending on the setup) normal derivatives of the observable φ; the prior ϕ > 0 contributes positivity, but φ can have any sign." `rem:n_dependence`: "For the population partition function (ξ = 0), the coefficients remain genuine constants."

Asymptotic expansion convention (§2.4): `f(n) ∼ Σ_{a∈𝒜} Σ_{b∈ℬ} C_{a,b} n^{-a}(log n)^{b-1}` means for every (a',b'): `f(n) = Σ_{(a,b)<(a',b')} C_{a,b} n^{-a}(log n)^{b-1} + O(n^{-a'}(log n)^{b'-1})`, with `(a,b) < (a',b') ⟺ a < a' ∨ (a = a' ∧ b > b')`. `defn:comparable`: f ≍ g if c_1 g ≤ f ≤ c_2 g; comparable functions monomialised by the same π have the same exponents; coefficients differ.

## 2. What the Lean seabed already has that bears on §3

Conventions: Lean `n` = dimension index (d = n+1 normal coordinates), Lean `N` = paper's sample size n, log degree j = m−1, boxes `(0,b]^d` (boundary type; the symmetric/parity variants exist only in d = 2, Headlines XI/XIX), lattice `latticeQ k = 2∏k_i`, `candidateExp h k μ` = μ ∈ Λ(h,k), `ratioExp h k i = (h_i+1)/(2k_i)`, `multCount`.

**Bare and dressed normal moments (normal-block programme):**
```lean
theorem headline_normal_moment_mixed (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    (fun N => ∫ x in unitBox (m + 1),
        (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) ~[atTop]
      fun N => (Real.Gamma l * β ^ (-l) /
          (((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1).factorial : ℝ) *
        ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 / (2 * (k i : ℝ))
          else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l)) *
        N ^ (-l) * Real.log N ^ ((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1)
-- = Γ(λ) β^{-λ} a_{-m}/(m−1)! · N^{-λ}(log N)^{m−1}  (Headline VII; eq:a_minus_m_explicit at b = 1)

theorem headline_normal_moment_amplitude (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : …) (hatt : …)
    (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in unitBox (m + 1), η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ (multiplicity − 1))) atTop
      (𝓝 (Γ(l) β^{-l}/(mult−1)! ∏_{J} 1/(2k_i) * ∫ u in unitBox (m + 1), η (P_J u) * ∏_{i∉J} u i ^ (h i − 2 k_i l)))
-- Headline VIII: face-supported leading functional (P_J zeroes the minimal coordinates). In the
-- equal-ratio case (J = everything) this is η(0) × the bare constant (`headline_normal_moment_amplitude_equal`).
```
Also `shiftedMoment_tendsto_of_face` (monomial dressing u^γ with γ|_J = 0 keeps (λ,m); `shiftedMoment_tendsto_zero` when γ_j > 0 for some j ∈ J the shifted moment is o of the undressed scale), the tangential version Headline IX (`headline_tangential_normal_moment_equal`: integration against a compact parameter set), Headline XXI (`MellinCoefficient.lean`: real-axis Abelian limit of the zeta leading coefficient, `η = 1` gives a_{-m}; Γ-dictionary with VIII), `LeadingCoeffNonzero.lean`: `blockCoeff_pos_of_nonneg_ne_zero` (η(0,·) ≥ 0 on the face and ≠ 0 somewhere ⇒ leading coefficient > 0) and `blockStateIntegral_isEquivalent_of_ne_zero`; `LeadingCoeffPositive.lean` (d = 2 posterior denominator positivity). Deterministic assembly Headline XV (`HeadlineAssembly.lean`, min exponent / max log multiplicity over charts, abstract `ChartAssembly.lean`) and posterior quotients XIV.

**Taylor tree (deterministic, every positive dimension, Headline XXXIII):**
```lean
theorem thm_TaylorTree_taylor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (taylorFamily (n + 1) Fξ) (taylorFamily (n + 1) Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b (taylorFamily (n + 1) Fξ)
        (taylorFamily (n + 1) Fη) = origPhaseIntegral n h k β N b ξ η
-- origPhaseIntegral n h k β N b ξ η = ∫_{(0,b]^{n+1}} η u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du
-- taylorFamily F γ = Re(∂^γ F(0)/γ!)

structure TaylorTreeConclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ) : Prop where
  coeff_eq : ∀ μ j, C μ j = familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ j
  vanish : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0
  summable : ∀ μ, 0 < μ → ∀ j, Summable fun p => |familyCoeffTerm n h k β (scale cξ b) (scale cη b) μ j p|
  series : ∀ μ j, C μ j = familyCoeffSeries n h k β (scale cξ b) (scale cη b) μ j
  remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N →
    |familyPhaseIntegralBox n h k β N b cξ cη - b ^ (∑ i, h i + (n + 1)) *
        ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) *
          ∑ j ∈ Finset.range (n + 1), C μ j * (Real.log (boxScale k b N)) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) * cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)
  isBigO : ∀ L, 0 < L → (fun N => familyPhaseIntegralBox … - boxSpectralSum n h k β L b cξ cη N) =O[atTop] fun N => N ^ (-L) * (1 + Real.log N) ^ n
  dictionary : …   -- β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)
```
The coefficient series (Headline XXIX): `A_{μ,j}(cξ,cη) = Σ_p β^p/p! T_p(cη * J^{*p})`, `J = fluctFamily cξ` (cξ with the constant term removed), `T_p(f) = K_k Σ_γ f_γ S_p(μ,j;γ)` a kernel functional built from the lattice-supported state densities of `u^{h+γ}` and the fluctuation moments `fluctMoment β a p μ i = ∫₀^∞ t^{μ−1}(−log t)^i (√t)^p e^{−βt+β√t a} dt`, `a = ξ(0)`. **At ξ = 0** (population): J = 0, only p = 0 survives: `A_{μ,j}(0,cη) = K_k Σ_γ cη_γ S_0(μ,j;γ)` where `S_0(μ,j;γ) = Σ_{q≥j} coeffAt(ρ_{h+γ}, μ, q) C(q,j) fluctMoment β 0 0 μ (q−j)` and `fluctMoment β 0 0 μ i = ∫₀^∞ t^{μ−1}(−log t)^i e^{−βt} dt` (Γ-function derivatives: i = 0 gives Γ(μ)β^{−μ}). So the population per-chart coefficients are explicit finite-in-`q` sums over the amplitude Taylor coefficients — the paper's dressed-moment expansion `Σ_γ (η_γ/γ!)·[coefficient of N^{-μ}(log N)^j in M_{h+γ}(N)]` — but this specialisation has NOT been written down as a theorem.

**Stochastic data / assembly layer (Programme S)** — the objects that a deterministic §3 assembly would reuse with deterministic data:
```lean
-- DataSpace d = ℓ¹((Fin d → ℕ) ⊕ (Fin d → ℕ)) (weighted-ℓ¹ coefficient pairs (cξ, cη)); dataBoxIntegral n h k β N b x = the box integral; dataBoxCoeff = its canonical coefficient of N^{-μ}(log N)^j
-- TangentialData K d = C(K, DataSpace d) (K compact); tanIntegral ν … x = ∫_K dataBoxIntegral (x v) dν, tanCoeff = ∫_K dataBoxCoeff (x v) dν
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop, |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)
noncomputable def absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j
noncomputable def absPredSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := ∑ p ∈ predSet D Q μ j, absTerm c N p
-- CutoffExpansion.add/sum/refine (Q ∣ Q')/pad; abs_abstractRemainder_sub_le; tendsto_abstractRemainder
theorem cutoffExpansion_tan … (x : TangentialData K (n + 1)) : CutoffExpansion (latticeQ k) n (fun N => tanIntegral ν n h k β N b x) (tanCoeff ν n h k β b x)
-- JointData K n = ∀ I : Fin M, TangentialData (K I) (n I + 1); commonQ k = ∏ latticeQ (k I); commonD n = sup n
noncomputable def gInt (x : JointData K n) (N : ℝ) : ℝ := ∑ I, tanIntegral (ν I) (n I) (h I) (k I) β N (b I) (x.chart I)
noncomputable def gCoeff (x : JointData K n) (μ : ℝ) (j : ℕ) : ℝ := ∑ I, tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j
theorem tendstoUniformlyOn_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => gRemainder ν h k β b x μ j N) (fun x => gCoeff ν h k β b x μ j) atTop (Metric.closedBall 0 R)
-- closing corollary u289 (deterministic, fixed joint datum x):
theorem tendsto_normalForm_pop … (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0)) :
    Tendsto (fun N => (Zpop N - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b x) μ₀ j N) / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 (gCoeff ν h k β b x μ₀ j))
theorem isEquivalent_normalForm_pop … (hpred : ∀ N, absPredSum … = 0) (hc : gCoeff ν h k β b x μ₀ j ≠ 0) :
    Zpop ~[atTop] fun N => gCoeff ν h k β b x μ₀ j * (N ^ (-μ₀) * Real.log N ^ j)
```
Support theorems: `dataBoxCoeff_eq_zero_of_lt` (j > n), `_of_not_candidate` (μ ∉ Λ(h,k)), `_of_not_lattice`. Quotients: `tendstoInDistribution_div`, and deterministic posterior quotients in XIV.

**Not in Lean at all:** anything about manifolds, resolutions, tubular neighbourhoods, partitions of unity, normal bundles, densities on manifolds, vanishing orders along divisors, or the change of variables through π. (Mathlib has `SmoothPartitionOfUnity`, smooth manifolds with corners, and vector bundles; no tubular neighbourhood theorem.) The mirror has ~6 §3 dots into a separate differential-geometry repo (`timaeus-research/strucdual`, tubular-neighbourhood definitions) and the §3.4 normal-moment dots above.

## 3. My reading of "what we are trying to do" in §3 (for you to correct)

1. **§3 is the population instance of the §4 machinery.** By `rem:pop_vs_emp` the per-chart population integral is the standard integral at ξ = 0: `𝒵_n[φ;I] = ∫_{S_I} ρ_I(v) Z(1, n; 0, η_v) dv` with `η_v(u) = (φ∘π)(v,u) c(v,u)` in the adapted chart (β = 1, or β general for the tempered case). The per-stratum expansion eq:tubular_expansion IS `thm:TaylorTree` at ξ = 0 integrated in v (`lemma:AsymInt`), and the "dressed moment" formula is the p = 0 coefficient series. So the rewritten §3 theorem should be stated as a **corollary of thm:TaylorTree + tangential integration + finite assembly**, not proved by a separate hand-wave through Steps 1–4.
2. **The genuinely §3-specific content is (a) the exponent shift by vanishing orders and (b) the explicit leading coefficient.** (a): if η_v(u) = u^l η'_v(u) (φ∘π vanishes to order l_i along E_i, so the amplitude Taylor coefficients vanish for γ ≱ l), then the coefficient of N^{-μ}(log N)^j vanishes unless μ ∈ Λ(h+l, k) — a support theorem — and the first candidate is μ_I(φ) = min (h_i+l_i+1)/(2k_i). (b): the leading coefficient is the face-supported functional of Headline VIII applied to u^h·(u^l η'): `Γ(μ)/(m−1)! ∏_J 1/(2k_i) ∫ (u^l η')(P_J u) ∏_{∉J} u^{h_i−2k_iμ}`, which for l = 0 and equal ratios reduces to `Γ(λ)/(m−1)! a_I · η(0)` = eq:thm_leading_coeff at chart level (the stratum integral ∫_{S_I} (φ∘π)(v,0)c_0(v)dv after tangential integration). Note the paper's "if D^l_⊥(φ∘π)|_{S_I} ≢ 0 then the leading exponent is μ_I(φ)" is only correct with a sign/nonvanishing condition (the face integral of a signed function can vanish — your v-review point "candidate exponents versus genuinely nonzero leading terms"); the honest statement is: the expansion is supported on Λ(h+l,k), and the coefficient at the first candidate is the explicit face functional, which is nonzero under (η' ≥ 0 on the face and ≠ 0 somewhere) or when the face functional is assumed ≠ 0.
3. **The global statement should be conditional on the geometric decomposition** (as XXXVII′/`tendsto_normalForm_pop`): given `𝒵_n[φ] = Σ_I 𝒵_n[φ;I] + O(e^{-nε})` (external: resolution + localisation + adapted partition of unity), the global expansion exists on the common lattice with coefficients Σ_I, leading exponent min_I μ_I(φ) with the max multiplicity among the minimisers *provided the summed leading coefficient is nonzero* (signed cancellation across strata is possible for general φ; for φ = 1 with ϕ > 0 it is positive).
4. **§3.6's three cases and wall-crossing** then follow from two expansions (numerator φ, denominator 1) by the leading-term quotient (deterministic version of XXXVIII / division at leading order): `E_n[φ] ∼ (C'/C) n^{-(μ_1−λ_1)}(log n)^{m̃_1−m_1}`, with C > 0 from positivity (Headline VIII face functional with η ≥ 0, ≠ 0). Wall-crossing = the leading exponent is a function of the vanishing-order vector only, hence piecewise constant in τ; probably only a remark.
5. **The coordinate-free packaging (§3.1–3.3)** — normal bundle splitting, moment tensors — is presentation, not needed for the theorem's truth; `lem:normal_deriv` is a one-line chain rule (`∂_u^b F(g(x)u)|_{u=0} = g(x)^b ∂_u^b F|_{u=0}`), formalisable cheaply in coordinates, but I would not attempt tubular neighbourhoods / adapted partitions of unity in Lean.
6. **ex:phi_equals_K**: `𝒵_n[K] = −𝒵_n'(n)` is exact (differentiation under the integral); `E[K] ∼ λ/n` needs the derivative's asymptotics, which do NOT follow from the asymptotics of 𝒵_n alone. In the chart model with ξ = 0 the amplitude for φ = K∘π is `u^{2k} c`, i.e. h ↦ h + 2k, so μ = λ + 1 with the same multiplicity is a direct instance of the support/shift theorem with the leading coefficient `Γ(λ+1)/(m−1)! a'` vs `Γ(λ)/(m−1)! a` — ratio λ (since a' = a when the shift is 2k_i on every coordinate: (h_i+2k_i+1−2k_i(λ+1)) = (h_i+1−2k_iλ)). So E[K] → λ/n at chart level is a clean corollary without differentiating.

## 4. Questions

1. **The rewritten §3 theorem.** Given the above, write the statement you would put in the paper in place of `thm:expectation_expansion` (and §3.6's leading-order claims), in the paper's notation, honest about (i) conditionality on the decomposition `𝒵_n[φ] = Σ_I 𝒵_n[φ;I] + O(e^{-nε})` (or do you think Steps 1–3 can be stated as a lemma with a real proof rather than a hypothesis?), (ii) the distinction candidate exponent vs. actual leading exponent (nonvanishing conditions; signed cancellation), (iii) what "vanishing order l_i" should mean in the chart model (amplitude divisible by u^l in the normal-form chart? `D^γ_⊥ ≡ 0` for γ ≱ l?), (iv) the role of the parity remark (interior components; our Lean boxes are one-sided). Please also say what should be *removed* or demoted to remarks (moment tensors, coordinate-free form) and what the relation to §4 should be (corollary of thm:TaylorTree at ξ = 0? or the other way round?).
2. **Formalisation programme.** Which parts of that statement are formalisable now in this seabed with the existing machinery, at what cost? My candidate list (rank / cap / gate it, or replace it):
   - P1 **population Taylor tree** (ξ = 0 specialisation of XXXIII): the per-chart coefficient formula collapses to `C_{μ,j} = K_k Σ_γ cη_γ S_0(μ,j;γ)` with `fluctMoment β 0 0 μ i` = Γ-derivative moments; identify `fluctMoment β 0 0 μ 0 = Γ(μ)β^{-μ}` and the leading `(μ,j) = (λ, m−1)` coefficient with Headline VIII's face functional (this is the "dressed moment expansion" `eq:tubular_expansion` and `eq:thm_leading_coeff` at chart level).
   - P2 **vanishing-order support and exponent shift**: for `cη` supported on γ ≥ l (η = u^l η'), `C_{μ,j} = 0` unless `μ ∈ Λ(h+l,k)`; leading candidate `μ_I(φ) = min (h_i+l_i+1)/(2k_i)`; leading coefficient = face functional of `u^l η'`; positivity/nonvanishing criterion (η' ≥ 0 on the face, ≠ 0) via `blockCoeff_pos_of_nonneg_ne_zero`-style lemma in general d (does that exist in general d? Headline VIII is general d; the positivity lemma is for the d₀+1 / d' block split — check).
   - P3 **deterministic tangential integration + finite assembly with exponential residual** (reuse `TangentialData`/`gInt`/`CutoffExpansion`; deterministic versions of XXXVII′ giving the §2.4-style asymptotic expansion `∀ (a',b')` of `𝒵_n[φ]` on the common lattice, plus the leading exponent/multiplicity = min/max over strata with the nonvanishing proviso — Headline XV/ChartAssembly may already cover the min/max bookkeeping).
   - P4 **§3.6 leading-order quotient and the three cases** (`E_n[φ] ∼ (C'/C) n^{-(μ₁−λ₁)}(log n)^{m̃₁−m₁}`) with the denominator positivity from a nonnegative amplitude; wall-crossing as a corollary/remark.
   - P5 **ex:phi_equals_K at chart level** (`E[K∘π] → λ/n`-type statement via the 2k shift; and/or the exact identity 𝒵_n[K] = −𝒵_n'(n)).
   - P6 **`lem:normal_deriv` in coordinates** (frame-change invariance of normalised normal derivatives) — cheap, but is it worth a dot?
   - NO-GO candidates: tubular neighbourhoods, `lem:adapted_pou`, change of variables through π, real analytic vanishing orders on a dense open set, the coordinate-free moment tensors, interior/parity components in d ≥ 3.
   For the GO items give exact Lean-level statements for the first three units (hypotheses in our conventions: `origPhaseIntegral`, `TaylorTreeConclusion`, `familyCoeffSeries`, `fluctMoment`, `amplitudeCoeff`/`faceProj`/`residualWeight`, `CutoffExpansion`, `gInt/gCoeff`, one-sided boxes `(0,b]^d`, Lean `N` = paper `n`, `j = m−1`), the unit budget/cap, the review cadence, and the stop criterion.
3. **Staging note for the authors.** What should the accompanying note say (a) about why the current theorem is out of date and what the corrected statement is, (b) about what the Lean formalisation of the corrected statement does and does not establish, and (c) about the pieces that remain genuinely geometric (Steps 1–3) and must stay as hypotheses? Include any errata you see in §3 as it stands (e.g. eq:lambda_I_f's "if D^l_⊥ ≢ 0 then the leading exponent is μ_I(φ)"; the claim that the denominator coefficient is positive "being the integral of a positive density over the leading stratum" when the leading stratum group may have mixed ratios; b-dependence of coefficients vs the b-independent a_{-m} in eq:thm_leading_coeff; the parity remark vs the one-sided boxes of §4).

Please be concrete and decisive: statement text, unit list with statements, caps, gates, non-claims. Lean pin for reference: `f1c0138` (statements above are current on main `99fbdd8`). The statement extracts above were produced by an awk extractor that cuts at `:= by`; it can truncate long hypotheses — treat elisions marked `…` as such.
