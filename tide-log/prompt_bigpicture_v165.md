# Big-picture consult #165: readable closed form for the first correction of Z_n[f] in dimension d ≥ 2

You are Astra, design consultant for the Lean 4 (Mathlib) formalisation of the grammar paper (repo `timaeus-research/grammar`,
namespace `Grammar`, 896 modules). Decide the route and give Lean-typable statements. No process advice.

## The object and what exists

`Z_N[η,ζ] = ∫_{[0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`, η, ζ ∈ C^∞ on the closed cube, k_i > 0.
Ratios λ_i = (h_i+1)/(2k_i); λ = min λ_i; J₀ = argmin (multiplicity m = |J₀|); Q = 2∏k_i.

Proved: ★★★ `emp_cutoffExpansion`: `Z_N ~ Σ_{μ∈(1/Q)ℕ} N^{−μ} Σ_{q≤d−1} c(μ,q) log^q N` with `c = empCoeff η ζ h k` unique and cutoff
independent (`empCoeff_unique`: any other CutoffExpansion has the same coefficients on the lattice, degree ≤ d−1). The coefficients
are DEFINED by the smooth engine's finite face formula `empCoeffAtDepth` = Σ over faces J ⊆ [d] and normal multi-indices m (bounded by
the depth) of `faceW J m` (∏ 1/m_i!) × Σ_j C(j,q) × `faceCoef` (Laurent data of the J-face monomial integral
`∫_{[0,1]^J} u^{m+h} e^{−βt u^{2k}} du` at the exponent μ, log power j) × `faceCoeffInt` (the integral over the complementary face
`[0,1]^L` of the FLAT face amplitude `faceAmp` = the m-th normal derivative of the amplitude at u_J = 0, with its Taylor terms in the
L-directions up to the depth SUBTRACTED (inclusion–exclusion `remList`), against `w^{h_L}` and the L-monomial's power-log weights at
μ, `j − q`). This is exact but unreadable. Explicit closed forms exist only for d = 1 (`empOneDimCoeff_zero/one/two/three`:
`C_j = ∂_u^j[η(u) S_{μ_j}(ξ(u))]|_{u=0}/(j!·2k)`, `μ_j = (h+j+1)/(2k)`, obtained from a SEPARATE direct 1D expansion `empOneDim_expansion`
by scaling `u = N^{−1/2k}x` and Taylor-expanding at fixed x) and for the leading term in general d (`tendsto_empBoxIntegral_div_boxFaceLimit`:
`Z_N/(N^{−λ} log^{m−1} N) → faceFunctional`, an integral over the leading face of `η S_λ(ζ)` with the face weight, via a dilation/dominated-
convergence argument `spatialPhase_box_tendsto`; identified with `empCoeff` at (λ, m−1) by `empCoeff_eq_zero_of_boxLeading_lt/_deg` +
uniqueness).

## The task (user): a READABLE formula for the first correction in d ≥ 2

My analysis. Substituting t = N v^{2k} in the resonant coordinate i₀ (single leading coordinate, m = 1): each Taylor order α in v_{i₀}
contributes at exponent (h_{i₀}+α+1)/(2k_{i₀}) with the face integral over v_L = (v_l)_{l≠i₀} carrying the weight `v_L^{h_L − 2k_L μ}`
(exponents > −1 iff λ_l > μ), and the field's Taylor derivatives in the normal direction produce `√t` factors, i.e. `S_{μ+1/2}`. So in
the GENERIC case — J₀ = {i₀}, and μ₁ := λ + 1/(2k_{i₀}) < λ' := min_{l≠i₀} λ_l — I expect:

  C_λ     = (1/2k_{i₀}) ∫_{[0,1]^{L}} v_L^{h_L − 2k_L λ}  η(0,v_L) S_λ(ζ(0,v_L)) dv_L
  C_{μ₁}  = (1/2k_{i₀}) ∫_{[0,1]^{L}} v_L^{h_L − 2k_L μ₁} [ ∂_{i₀}η(0,v_L) S_{μ₁}(ζ(0,v_L)) + η(0,v_L) ∂_{i₀}ζ(0,v_L) S_{μ₁+1/2}(ζ(0,v_L)) ] dv_L

with no log terms at λ or μ₁ and zero coefficients at the lattice points strictly between (β = 1, `S_ν(a) = ∫_0^∞ t^{ν−1}e^{−t+a√t}dt`).
When μ₁ ≥ λ' the picture changes (another coordinate becomes resonant at μ₁; if a coordinate l has λ_l < μ but μ ∉ its progression the
face integral diverges and the flat-amplitude subtraction is what regularises it). When m ≥ 2 there are logs at λ.

Two proof routes:
(R1) LIMIT + UNIQUENESS: prove `N^{μ₁}(Z_N − C_λ N^{−λ}) → C_{μ₁}` directly (inner 1D expansion in v_{i₀} with parameter v_L and
     T = N v_L^{2k_L}, uniform constants from jet bounds; split T ≥ 1 / T < 1; the region {∏ v_l^{2k_l} < 1/N} has weighted volume
     ~ N^{−(λ'−μ₁)} (up to logs) → 0), then a "reading-off" lemma: a CutoffExpansion whose partial normalised sums converge forces the
     coefficients (c(λ,0) = C_λ, c(λ,q≥1) = 0, c(ν,·) = 0 for λ < ν < μ₁, c(μ₁,0) = C_{μ₁}, c(μ₁,q≥1) = 0).
(R2) UNWIND `empCoeffAtDepth` at μ₁: identify the contributing faces (J ∋ i₀ with m_{i₀} = 1 …) and show the inclusion–exclusion pieces
     recombine into the unregularised face integral; needs the Laurent data of multi-coordinate face monomials.

## Questions
1. Is the generic formula above right (signs, factors 1/(2k), the S_{μ₁+1/2} term, the face weight v_L^{h_L − 2k_L μ})? Anything missing
   (e.g. a contribution from Taylor order α = 0 with the L-directions' Taylor terms; the exponentially small tails)?
2. Which route, R1 or R2, and what are the pitfalls? For R1: is the two-region estimate for {∏_l v_l^{2k_l} < 1/N} of ∏ v_l^{a_l}
   (a_l > −1) available cheaply (a lemma of the form ∫_{∏ v_l^{2k_l} ≤ ε} ∏ v_l^{a_l} dv ≤ C ε^{min (a_l+1)/(2k_l)} (1+|log ε|)^{d−1})?
   For the reading-off lemma: is there a slicker argument via `empCoeff_unique` applied to a manufactured second CutoffExpansion
   (e.g. `Z_N − C_λN^{−λ} − C_{μ₁}N^{−μ₁} = O(N^{−μ₁−ε})` is NOT a full CutoffExpansion — how to close)?
3. Beyond the generic case, what is the right general READABLE statement for the coefficient at an exponent μ with resonant set
   J(μ) = {i : μ ∈ λ_i + (1/2k_i)ℕ} (Taylor orders α_i = 2k_iμ − h_i − 1), in terms of face integrals with the Hadamard-regularised
   weight for the coordinates l with λ_l < μ, μ ∉ progression? Give the formula for the no-log case (|J(μ)| = 1) as the target
   theorem after the generic first correction, and say whether the log case (|J(μ)| ≥ 2) has a comparably clean form
   (derivatives ∂_ν S_ν and the Laurent coefficients of ∏_{i∈J} 1/(2k_i(s+μ))).
4. Anything in my reading of the paper's Taylor-tree coefficient formula (eq:ExpansionCoefficient: absolutely convergent Taylor series
   with Laurent coefficients c_{μ,j} and (−∂_μ)^{j−m}∂^p S_μ(ξ(0))) that contradicts the face-integral form? The face form keeps the
   L-directions unexpanded; the paper expands everything at the origin — they must agree termwise after integrating the L-Taylor series.
