You are Astra, the design consultant for the Lean 4 formalisation of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor", Section 4: fluctuations / the empirical partition function). Repo timaeus-research/grammar (namespace `Grammar`, 841 modules, axiom-clean), plus a glue workspace `grammar-greybook-bridge` combining grammar with the Lean formalisation of the grey book (Murfet's SLT text: empirical process ξ_n, Theorem 5.9 C(K) CLT, Theorem 6.7 evidence asymptotics with tail/central/non-essential splits, `AtlasData`, `TailData`).

## What consult #152 asked for, and what landed (all axiom-clean)

Deliverable 1 — `FieldJetUniform`: a jet bound on ζ gives a jet bound on η e^{−ζ} with constant 2^{|p|}|p|! B_η (1+B)^{|p|}.
Deliverable 2 — `RectRemainderUniform`: `empRect_remainder_uniform_on_jetBall`: ∃ K N₀, for every smooth ζ with `JetBoundOn (Σᵢ depthOf h k (max ⌈U⌉₊ (L₀ h)) i) (closedBox d b) ζ B`, ∀ N ≥ N₀, |empIntegralRect η ζ h k b N − absSpectralSum (Qamb k) (d−1) (empCoeffRect η ζ h k b) U N| ≤ K N^{−U} (1+log N)^{d−1}.
Deliverable 3 — `TightNormTail`: tight laws ⇒ uniform norm tails.
Deliverable 4 — `CubeRemainderProbability`: `requiredOrder h k U := Σᵢ depthOf h k (max ⌈U⌉₊ (L₀ h)) i`; `tendstoInMeasure_cubeRemainder_of_tendsto`: random smooth fields ζ n w with jets Y n measurable, tight, a.s. = `cubeJet R b (ζ n w)`, `requiredOrder ≤ R`, normaliser s n with s n · n^{−U}(1+log n)^{d−1} → 0 ⇒ `TendstoInMeasure P (fun n w => s n · (empIntegralRect η (ζ n w) h k b n − absSpectralSum … U n)) atTop 0`; instance `tendstoInMeasure_cubeRemainder_rpow` with s n = n^A, A < U.
Deliverable 5 — bridge `Bridge/EvidenceExpansion`: cube jets are Polish (FiniteDimensional instance on ContinuousMultilinearMap); `tendstoInMeasure_chartRemainder` (Y n := −chartJetReconstruct (Zₙ), measurable, tight because convergent in distribution, a.s. the cube jets of −globalField); `tendstoZeroInProb_rpow_mul_tail` (grey book `tail_evidence_tendsto_zero_inProb`, m := 1); ★★ `tendstoZeroInProb_evidence_expansion`: for A < min_α U_α and R ≥ requiredOrder (h α) (k α) (U α) for all α,
  n^A · (∫ e^{−n Kₙ} dν − Σ_α absSpectralSum (Qamb k_α) (d−1) (empCoeffRect (unitWt α) (−globalField α n ω) h_α k_α b_α) U_α n) → 0 in probability (grey book `TendstoZeroInProb (fun _ => P)`),
under the M6b hypotheses (β = 1, νχ = ν.withDensity χ∘K, g_α(box) ⊆ K₀, 0 < k α i, smooth unit weights, i.i.d. sample with law μ).

Earlier: `chartTopCoeffLaw` / `jointChartTopCoeffLaw` (top-order coefficient laws, limit concentrated on closed realizable cube jets), `ae_totalEvidence_eq`.

## Open items I know of

(a) Leading-constant identification: grammar's `boxFaceLimit (boxExt G)` vs the grey book's `boxGamma · limitY` (the grey book proves the leading law from the process itself, `theorem_6_7_of_process`). Both are functionals of the C(box) limit field.
(b) Lattice alignment: `empCoeffRect` is defined for every real μ; off the lattice Λ(h,k) it is not known to vanish; across charts the lattices differ, so the total expansion is not yet a single sum over a common index set with identified coefficients. `absSpectralSum (Qamb k) (d−1) c U n` sums over the ambient lattice with Q = Qamb k.
(c) Lower coefficients: laws of `empCoeffRect … μ q` for (μ,q) below the top are not proved (continuity of the coefficient in jets at lower orders is an open deterministic item; the top coefficient is Lipschitz on jet balls).
(d) Explicit chart hypotheses: `0 < k α i`, `ContDiff ⊤ (unitWt α)`, `DeepVanishing (unitWt α) (rb α) c` (for the coefficient law), `g_α(box) ⊆ K₀` are not supplied by the grey book's `AtlasData`.
(e) The remainder is o_P below the cutoff and only O_P at it; the cutoff U is arbitrary, so the expansion is "at every polynomial rate", not an asymptotic series with identified error constants.
(f) The paper's expansion also covers the posterior expectation / observable insertion `∫ f e^{−nKₙ}`; the bridge only does the evidence (f = 1 via the unit weight).

## Question

Which of these (or what else) is the highest-value NEXT theorem programme, given the standing priority "new theorems over process"? Please give: (1) a ranked list with the mathematical content of each headline; (2) for the top item, a concrete staged Lean plan (statements, hypothesis structures, which Mathlib/grey-book/grammar results carry it), with the traps you foresee; (3) any correction to the way I have described the landed results (over-claims, wrong framing). Be concrete about Lean statements; I will grep Mathlib for names you propose.
